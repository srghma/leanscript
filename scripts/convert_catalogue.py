#!/usr/bin/env python3
"""One-shot conversion of the extern catalogue to signature-indexed families.

Old entry:  | lean_nat_add : Nat → Nat → PreludeExtern nat -- Nat.add
New entry:  | lean_nat_add : PreludeExtern [nat, nat] nat -- Nat.add

The arguments of an entry become the list of the types of its arguments (the values are
the arguments of the extern call in a term); proofs are dropped (the evaluator decides
them); type arguments `(αt : MyTy)` stay fields of the entry.

Also writes `LeanScript/Extern/Eval<Theme>.lean`, the evaluator of every family at the
instantiation of the catalogue to `Ty`.
"""
import re, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAT = os.path.join(ROOT, 'LeanScript', 'LeanInitPureExterns')
THEMES = ['Core', 'FixedWidth', 'String', 'Float']

PRIM = {
    'Nat': ('nat', 'Nat'), 'Int': ('int', 'Int'), 'String': ('string', 'String'),
    'Float': ('float', 'Float'), 'Float32': ('float32', 'Float32'),
    'String.Pos.Raw': ('stringPosRaw', 'String.Pos.Raw'),
    'UInt8': ('uint8', 'UInt8'), 'UInt16': ('uint16', 'UInt16'),
    'UInt32': ('uint32', 'UInt32'), 'UInt64': ('uint64', 'UInt64'),
    'Int8': ('int8', 'Int8'), 'Int16': ('int16', 'Int16'), 'Int32': ('int32', 'Int32'),
    'Int64': ('int64', 'Int64'), 'Bool': ('LeanPrimTy.bool', 'Bool'),
    'Substring.Raw': ('substringRaw', 'Substring.Raw'), 'Char': ('char', 'Char'),
    'String.Slice': ('stringSlice', 'String.Slice'),
    'Float.Model': ('floatModel', 'Float.Model'), 'Float32.Model': ('float32Model', 'Float32.Model'),
    'BitVec 8': ('(bitvec 8)', 'BitVec 8'), 'BitVec 16': ('(bitvec 16)', 'BitVec 16'),
    'BitVec 32': ('(bitvec 32)', 'BitVec 32'), 'BitVec 64': ('(bitvec 64)', 'BitVec 64'),
    'Array (denote αt)': ('(array αt)', 'Array (Ty.den E αt)'),
    'denote αt': ('αt', 'Ty.den E αt'),
    '(Char → Bool)': ('(fn1 char LeanPrimTy.bool)', 'Char → Bool'),
    '(String → Char → String)': ('(fn2 string char string)', 'String → Char → String'),
    's.Pos': ('(LeanPrimTy.stringPos s h_len)', 'String.Pos s'),
    '(denote (lazy αt))': ('(lazy αt)', 'Ty.den E αt'),
    'Thunk (denote αt)': ('(thunk αt)', 'Ty.den E αt'),
}
# not in the grammar of types: the entry is commented out
UNSUPPORTED = ['List ', 'leanName', '(list ']
# proof-taking entries whose result is a value of an arbitrary type: when the proof (which
# the language erases) does not hold, the evaluator has no value to answer
NO_DEFAULT = {'lean_array_fget', 'lean_array_fget_borrowed'}


def split_arrows(ty):
    parts, depth, cur, i = [], 0, '', 0
    while i < len(ty):
        ch = ty[i]
        if ch in '([{':
            depth += 1
        if ch in ')]}':
            depth -= 1
        if depth == 0 and ty.startswith(' → ', i):
            parts.append(cur.strip()); cur = ''; i += 3; continue
        cur += ch; i += 1
    parts.append(cur.strip())
    return parts


def is_prop(t):
    return any(s in t for s in [' < ', ' ≤ ', ' ≠ ', ' ∣ ', '¬', 'isValidChar', '= Bool.true'])


def res_lean(res):
    """The Lean type of the value of a result type, and how to convert a call to it."""
    r = res.strip()
    m = {
        'nat': 'Nat', 'int': 'Int', 'string': 'String', 'char': 'Char',
        'stringPosRaw': 'String.Pos.Raw',
        'substringRaw': 'Substring.Raw', 'uint8': 'UInt8', 'uint16': 'UInt16',
        'uint32': 'UInt32', 'uint64': 'UInt64', 'int8': 'Int8', 'int16': 'Int16',
        'int32': 'Int32', 'int64': 'Int64', 'floatModel': 'Float.Model',
        'float32Model': 'Float32.Model', 'αt': 'Ty.den E αt',
        '(array αt)': 'Array (Ty.den E αt)', '(option char)': 'Option Char',
        '(bitvec 8)': 'BitVec 8', '(bitvec 16)': 'BitVec 16', '(bitvec 32)': 'BitVec 32',
        '(bitvec 64)': 'BitVec 64', '(LeanPrimTy.stringPos s h_len)': 'String.Pos s',
    }
    if r in m:
        T = m[r]
        return (T, lambda c: f'({c} : {T})')
    if r == 'LeanPrimTy.bool':
        return ('Bool', lambda c: f'ExternBool.toBool ({c})')
    if r == 'float':
        return ('HashableFloat', lambda c: f'HashableFloat.normalize ({c})')
    if r == 'float32':
        return ('HashableFloat32', lambda c: f'HashableFloat32.normalize ({c})')
    if r == 'ordering':
        return ('Fin 3', lambda c: f'orderingToFin ({c})')
    if r == '(prod float int)':
        return ('HashableFloat × Int', lambda c: f'(let r := {c}; (HashableFloat.normalize r.1, r.2))')
    if r == '(prod float32 int)':
        return ('HashableFloat32 × Int', lambda c: f'(let r := {c}; (HashableFloat32.normalize r.1, r.2))')
    lm = re.match(r'^\(lazy (.*)\)$', r)
    if lm:
        T, inner = res_lean(lm.group(1))
        return (T, lambda c: inner(f'{c} ()'))
    return None


def convert_entry(line):
    """Returns (new_line, eval_case or None, fam, name)."""
    m = re.match(r'^(\s*)\| (\S+) : (.*?) -- (.*)$', line)
    ind, name, ty, fn = m.groups()
    parts = split_arrows(ty)
    resm = re.match(r'^(\w+Extern) (.*)$', parts[-1])
    fam, res = resm.group(1), resm.group(2)
    if any(u in ty for u in UNSUPPORTED):
        return (f'{ind}-- | {name} : {ty} -- {fn} -- (lists and names are not types of the '
                f'grammar: a Lean `List`/`Lean.Name` is a declared datatype)', None, fam, name)
    if name in NO_DEFAULT:
        return (f'{ind}-- | {name} : {ty} -- {fn} -- (takes a proof, and answers a value of '
                f'an arbitrary type: when the erased proof does not hold there is no value to '
                f'answer; `a[i]` is `lean_array_get` with the `Inhabited` default)', None, fam, name)
    fields = []    # new fields of the entry (type arguments)
    argtys = []    # the types of the arguments
    binds = []     # (varname, leanType, conv) for the evaluator
    props = []     # (hname, prop)
    call_args = []  # arguments of the Lean function, in order
    dropped = []
    k = 0
    implicit_s = False
    for p in parts[:-1]:
        nm = None
        t = p
        bm = re.match(r'^\((\w+) : (.*?)( := by get_elem_tactic)?\)$', p)
        if bm:
            nm, t = bm.group(1), bm.group(2)
        if p == '{s : String}':
            implicit_s = True
            fields.append('(s : String)')
            continue
        if t == 'MyTy':
            fields.append(f'({nm} : MyTy)')
            continue
        if nm == 'h_len':
            fields.append('(h_len : 2 ≤ s.length)')
            continue
        if is_prop(t):
            h = nm if nm and not any(q[0] == nm for q in props) else f'h{len(props)}'
            props.append((h, t))
            call_args.append(h)
            dropped.append(t)
            continue
        if t not in PRIM:
            raise Exception(f'unknown type {t!r} in {name}')
        mt, lt = PRIM[t]
        k += 1
        v = nm if nm else f'x{k}'
        argtys.append(mt)
        binds.append((v, lt))
        call_args.append(v)
    if implicit_s and not any(f.startswith('(h_len') for f in fields):
        fields.append('(h_len : 2 ≤ s.length)')
    fieldstr = ''.join(f + ' → ' for f in fields)
    note = ''
    if dropped:
        note = ' (decides ' + ', '.join(f'`{d}`' for d in dropped) + ')'
    new = f'{ind}| {name} : {fieldstr}{fam} [{", ".join(argtys)}] {res} -- {fn}{note}'
    # evaluator case
    rl = res_lean(res)
    if rl is None:
        return (new, f'  -- TODO {name}', fam, name)
    resT, conv = rl
    fieldpats = ' '.join('_' if not f.startswith('(αt') and not f.startswith('(s ') else
                         f[1:].split(' ')[0] for f in fields)
    vs = [b[0] for b in binds]
    if len(vs) == 0:
        pat = '_'
    elif len(vs) == 1:
        pat = vs[0]
    else:
        pat = '(' + ', '.join(vs) + ')'
    lets = []
    for v, lt in binds:
        if lt == 'Float':
            lets.append(f'let {v} : Float := HashableFloat.toFloat {v}')
        elif lt == 'Float32':
            lets.append(f'let {v} : Float32 := HashableFloat32.toFloat32 {v}')
        else:
            lets.append(f'let {v} : {lt} := {v}')
    fnname = fn.split(' ')[0]
    call = fnname + ''.join(' ' + a for a in call_args)
    body = conv(call)
    if props:
        dflt = f'(default : {resT})'
        if res.strip() == '(array αt)':
            arr = [b[0] for b in binds if b[1].startswith('Array')]
            dflt = arr[0]
        for h, pr in reversed(props):
            body = f'if {h} : {pr} then {body} else {dflt}'

    ctor = f'.{name}' + (' ' + fieldpats if fieldpats else '')
    if fieldpats:
        ctor = f'({ctor})'
    lines = [f'  | _, _, {ctor}, {pat} =>']
    for l in lets:
        lines.append(f'    {l}')
    lines.append(f'    {body}')
    return (new, '\n'.join(lines), fam, name)


def main():
    evals = {}
    for th in THEMES:
        path = os.path.join(CAT, th + '.lean')
        src = open(path).read().split('\n')
        out = []
        fam_cases = {}
        order = []
        for line in src:
            if re.match(r'^\s*\| \S+ : .* -- ', line):
                new, case, fam, name = convert_entry(line)
                out.append(new)
                if fam not in fam_cases:
                    fam_cases[fam] = []; order.append(fam)
                if case:
                    fam_cases[fam].append(case)
            else:
                line = re.sub(r'^inductive (\w+Extern) : MyTy → Type where',
                              r'inductive \1 : List MyTy → MyTy → Type where', line)
                out.append(line)
        open(path, 'w').write('\n'.join(out))
        evals[th] = (order, fam_cases)
    import json
    json.dump({th: [o, c] for th, (o, c) in evals.items()}, open('/tmp/evals.json', 'w'))


if __name__ == '__main__':
    main()
