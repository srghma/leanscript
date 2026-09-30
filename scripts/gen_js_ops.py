#!/usr/bin/env python3
"""Generate the typed operations of `JsTerm` from the catalogue of externs.

    python3 scripts/gen_js_ops.py            # regenerate the generated modules of JsTerm/Ops/
    python3 scripts/gen_js_ops.py --report   # list the operations with no implementation

Every extern of the catalogue (`LeanScript/LeanInitPureExterns/*.lean`) is split by the
JavaScript representation of its arguments and its result: `lean_nat_div : [nat, nat] -> nat`
becomes `bigint_nat__lean_nat_div : [bigint_nat, bigint_nat] -> bigint_nat` and
`uint53__lean_nat_div : [uint53, uint53] -> uint53`.  The name of an operation is its *type
prefix* and the name of the extern, joined by `__`; the prefix is the list of the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` with `n > 53`), in order of first appearance and without repetitions, or,
when the signature has none, the first leaf of the signature (`uint32__lean_uint32_add`), or
the family of the polymorphic ones (`array__lean_array_push_immutable`, `thunk__lean_mk_thunk`).

An operation is either

* **inlined** (`JsOpInlinable`): a single JavaScript operator, conversion or call of a global
  (`bigint_nat__lean_nat_land` is `a & b`, `float__sin` is `Math.sin(a)`), written by
  `JsInline`; or
* **imported** (`JsOpImported`): a function of the same name exported by `runtime.js`, which
  the generated module imports.

Every operation carries its effects: `effectful` for the `_mutable` array updates (the only
ones that change an argument), `pure` otherwise; `mayThrow` when its function in `runtime.js`
contains a `throw` or refers to a function that may throw (found by a fixpoint over the
declarations of `runtime.js`), `doesntThrow` otherwise.  An alias in `runtime.js`
(`export const a = b;`) of an operation at the same signature is not an operation of its own:
its extern is looked up to `b` (`lean_array_get_borrowed` is `lean_array_get`).  The array
updates (`UPDATES`) come as an `_immutable` and a `_mutable` operation, both functions of
`runtime.js` at the same signature, which `JsOpImported.toMutable?` pairs; the script fails when
the `_mutable` function of one is missing.

Every extern must have an operation at every representation: the script fails (listing them)
when one has neither an inline form nor a function in `runtime.js`.
"""
import os, re, sys, itertools, json

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import js_ops_array_std as array_std

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAT = os.path.join(ROOT, 'LeanScript', 'LeanInitPureExterns')
RUNTIME = os.path.join(ROOT, 'runtime.js')

# --------------------------------------------------------------------------- catalogue

def tokenize(s):
    return re.findall(r'\(|\)|\[|\]|,|[^\s()\[\],]+', s)

def parse_ty(toks, i):
    """A Lean type of the catalogue, as a tuple."""
    t = toks[i]
    if t == '(':
        head = toks[i + 1]
        j = i + 2
        args = []
        while toks[j] != ')':
            if toks[j] == '(':
                a, j = parse_ty(toks, j)
                args.append(a)
            else:
                args.append(('atom', toks[j]))
                j += 1
        return (head, args), j + 1
    return ('atom', t), i + 1

def norm(ty):
    """Normalise a parsed type to ('prim', p) / ('bitvec', n) / (former, [args]) / ('var',)."""
    kind, v = ty
    if kind == 'atom':
        p = v.replace('LeanPrimTy.', '')
        if p == 'αt':
            return ('var',)
        if p in ('ordering', 'leanName'):
            return (p,)
        return ('prim', p)
    head, args = kind, v
    head = head.replace('LeanPrimTy.', '')
    if head == 'bitvec':
        return ('bitvec', int(args[0][1]))
    if head == 'stringPos':
        return ('prim', 'stringPosRaw')
    return (head, [norm(a) for a in args])

def parse_sig(s):
    toks = tokenize(s)
    assert toks[0] == '['
    i = 1
    args = []
    while toks[i] != ']':
        if toks[i] == ',':
            i += 1
            continue
        a, i = parse_ty(toks, i)
        args.append(norm(a))
    i += 1
    res, i = parse_ty(toks, i)
    return args, norm(res)

def catalogue():
    out = []
    for th in ['Core', 'FixedWidth', 'String', 'Float']:
        for line in open(os.path.join(CAT, th + '.lean')):
            m = re.match(r'^  \| (\S+) : (.*?)(?: -- (.*))?$', line)
            if not m:
                continue
            name, rest, lean = m.groups()
            poly = '(αt : MyTy)' in rest
            sig = re.sub(r'^.*?Extern ', '', rest)
            args, res = parse_sig(sig)
            if 'LeanPrimTy.stringPos ' in sig:
                # a `String.Pos s` is a byte offset into the string `s`, a parameter of the
                # extern known at compile time: the operation takes `s` as its first argument
                args = [('prim', 'string')] + args
            out.append(dict(name=name, args=args, res=res, poly=poly, lean=(lean or '').strip(), group=th))
    return out

# ---------------------------------------------------------------------- representations

KNOBS = ['nat', 'int', 'uint64', 'int64', 'bitvec']

def leaf(p, cfg):
    """The leaf (`JsTerminalTy`) of a Lean leaf type at a configuration; `None` for a type
    variable."""
    if p[0] == 'bitvec':
        n = p[1]
        if n <= 53:
            return ('bitvec_small', n)
        return ('bigint_bitvec_big', n) if cfg['bitvec'] == 'big' else ('int53_bitvec_big', n)
    q = p[1]
    return {
        'bool': 'bool',
        'nat': 'bigint_nat' if cfg['nat'] == 'big' else 'uint53',
        'int': 'bigint_int' if cfg['int'] == 'big' else 'int53',
        'uint64': 'bigint_nat' if cfg['uint64'] == 'big' else 'uint53',
        'int64': 'bigint_int' if cfg['int64'] == 'big' else 'int53',
        'uint8': 'uint8', 'uint16': 'uint16', 'uint32': 'uint32',
        'int8': 'int8', 'int16': 'int16', 'int32': 'int32',
        'float': 'float', 'float32': 'float32', 'floatModel': 'float', 'float32Model': 'float32',
        'char': 'string', 'string': 'string', 'stringPosRaw': 'uint53',
        'substringRaw': 'substring', 'stringSlice': 'stringSlice',
    }[q]

def knob_of(p):
    if p[0] == 'bitvec':
        return 'bitvec' if p[1] > 53 else None
    if p[0] == 'prim' and p[1] in ('nat', 'int', 'uint64', 'int64'):
        return p[1]
    return None

def knobs_in(ty, acc):
    if ty[0] in ('prim', 'bitvec'):
        k = knob_of(ty)
        if k and k not in acc:
            acc.append(k)
    elif len(ty) == 2 and isinstance(ty[1], list):
        for a in ty[1]:
            knobs_in(a, acc)
    return acc

def leaf_name(l):
    if isinstance(l, tuple):
        k, n = l
        return {'bitvec_small': f'bitvec{n}', 'bigint_bitvec_big': f'bigint_bitvec{n}',
                'int53_bitvec_big': f'int53_bitvec{n}'}[k]
    return l

def leaf_lean(l):
    if isinstance(l, tuple):
        k, n = l
        if k == 'bitvec_small':
            return f'(.bitvec_small {n} (by decide) (by decide))'
        return f'(.{k} {n} (by decide))'
    return '.' + l

def is_big(l):
    if isinstance(l, tuple):
        return l[0] == 'bigint_bitvec_big'
    return l in ('bigint_nat', 'bigint_int')

def js_ty(ty, cfg):
    """The `JsTy` of a Lean type of the catalogue: a tuple, `('leaf', l)`, … ; `('var',)`
    stays a variable."""
    k = ty[0]
    if k in ('prim', 'bitvec'):
        return ('leaf', leaf(ty, cfg))
    if k == 'var':
        return ('var',)
    if k == 'ordering':
        return ('enum', 3, -1)
    if k == 'leanName':
        return ('leanName',)
    args = [js_ty(a, cfg) for a in ty[1]]
    if k == 'array':
        return ('array', args[0])
    if k == 'list':
        return ('list', args[0])
    if k == 'thunk':
        return ('thunk', args[0])
    if k == 'lazy':
        return ('fn', [], args[0])
    if k == 'option':
        return ('union', [[], [args[0]]])
    if k == 'prod':
        return ('record', args)
    if k == 'fn1':
        return ('fn', [args[0]], args[1])
    if k == 'fn2':
        return ('fn', [args[0], args[1]], args[2])
    raise ValueError(ty)

def lean_of(t, var='α'):
    """A `JsTy` as Lean source."""
    k = t[0]
    if k == 'leaf':
        return f'(.terminal {leaf_lean(t[1])})'
    if k == 'var':
        return var
    if k == 'enum':
        return f'(.enum {t[1]} ({t[2]}))'
    if k in ('array', 'list', 'thunk'):
        return f'(.{k} {lean_of(t[1], var)})'
    lst = lambda ts: '[' + ', '.join(lean_of(a, var) for a in ts) + ']'
    if k == 'union':
        cs = t[1]
        ar = ', '.join(str(len(c)) for c in cs)
        return f'(.obj (.union [{ar}] .cells) ' + lst([a for c in cs for a in c]) + ')'
    if k == 'record':
        fs = t[1]
        return f'(.obj (.record {len(fs)}) {lst(fs)})'
    if k == 'fn':
        return f'(.fn {lst(t[1])} {lean_of(t[2], var)})'
    raise ValueError(t)

def leaves(t, acc):
    if t[0] == 'leaf':
        acc.append(t[1])
    elif t[0] in ('array', 'list', 'thunk'):
        leaves(t[1], acc)
    elif t[0] == 'union':
        for c in t[1]:
            for a in c:
                leaves(a, acc)
    elif t[0] == 'record':
        for a in t[1]:
            leaves(a, acc)
    elif t[0] == 'fn':
        for a in t[1]:
            leaves(a, acc)
        leaves(t[2], acc)
    return acc

def configurable_leaves(ty, cfg, acc):
    if ty[0] in ('prim', 'bitvec'):
        if knob_of(ty):
            acc.append(leaf(ty, cfg))
    elif len(ty) == 2 and isinstance(ty[1], list):
        for a in ty[1]:
            configurable_leaves(a, cfg, acc)
    return acc

def prefix(e, cfg):
    acc = []
    for a in e['args'] + [e['res']]:
        configurable_leaves(a, cfg, acc)
    ded = []
    for l in acc:
        if l not in ded:
            ded.append(l)
    if ded:
        return '__'.join(leaf_name(l) for l in ded)
    ls = []
    for a in e['args'] + [e['res']]:
        leaves(js_ty(a, cfg), ls)
    if ls:
        return leaf_name(ls[0])
    fam = [a[0] for a in e['args'] + [e['res']]]
    for f in ('array', 'thunk', 'list', 'lazy'):
        if f in fam:
            return f
    return 'any'


DECL_RE = re.compile(r'^(export )?(const|let|function) ([A-Za-z_$][\w$]*)')

def parse_decls(text):
    """The top-level declarations of a module: a list of dicts (name, exported, doc, code)."""
    lines = text.split('\n')
    decls = []
    i = 0
    pending_doc = []
    while i < len(lines):
        line = lines[i]
        m = DECL_RE.match(line)
        if m:
            start = i
            depth = 0
            j = i
            while True:
                l = lines[j]
                s = re.sub(r'"(\\.|[^"\\])*"|`[^`]*`|\'(\\.|[^\'\\])*\'', '""', l)
                s = re.sub(r'//.*$', '', s)
                depth += s.count('(') + s.count('{') + s.count('[') - s.count(')') - s.count('}') - s.count(']')
                if depth <= 0 and (s.rstrip().endswith(';') or (m.group(2) == 'function' and s.rstrip().endswith('}'))):
                    break
                j += 1
            code = '\n'.join(lines[start:j + 1])
            decls.append(dict(name=m.group(3), exported=bool(m.group(1)), doc='\n'.join(pending_doc),
                              code=code))
            pending_doc = []
            i = j + 1
            continue
        if line.startswith('/**') or line.startswith('/*'):
            doc = [line]
            while not lines[i].rstrip().endswith('*/'):
                i += 1
                doc.append(lines[i])
            if line.startswith('/* ---') or line.startswith('/* ==='):
                pending_doc = []
            else:
                pending_doc = doc
            i += 1
            continue
        if line.strip() == '' or line.startswith('//'):
            if line.strip() == '':
                pending_doc = pending_doc  # keep
            i += 1
            continue
        i += 1
    return decls

def ident_re(name):
    return re.compile(r'(?<![\w$])' + re.escape(name) + r'(?![\w$])')

# The characters of a Lean identifier that a JavaScript one cannot have, and how the name of a
# function of `runtime.js` writes them (`jsSafeName` in `JsTerm/Ops/Basic.lean`).
JS_ESCAPES = {'?': '$3F', '!': '$21', "'": '$27'}

def js_name(name):
    return ''.join(JS_ESCAPES.get(c, c) for c in name)


VALUE_CONVERSIONS = set("""lean_float32_to_float lean_int16_to_float lean_int16_to_float32 lean_int16_to_int
lean_int16_to_int32 lean_int16_to_int64 lean_int32_to_float lean_int32_to_float32
lean_int32_to_int lean_int32_to_int64 lean_int64_to_float lean_int64_to_int_sint
lean_int8_to_float lean_int8_to_float32 lean_int8_to_int lean_int8_to_int16
lean_int8_to_int32 lean_int8_to_int64 lean_nat_to_int lean_uint16_of_nat_mk
lean_uint16_to_float lean_uint16_to_float32 lean_uint16_to_nat__UInt16_toBitVec
lean_uint16_to_nat__UInt16_toNat lean_uint16_to_uint32 lean_uint16_to_uint64
lean_uint32_of_nat_mk lean_uint32_to_float lean_uint32_to_float32
lean_uint32_to_nat__UInt32_toBitVec lean_uint32_to_nat__UInt32_toNat
lean_uint32_to_uint64 lean_uint64_of_nat_mk lean_uint64_to_float
lean_uint64_to_nat__UInt64_toBitVec lean_uint64_to_nat__UInt64_toNat
lean_uint8_of_nat_mk lean_uint8_to_float lean_uint8_to_float32
lean_uint8_to_nat__UInt8_toBitVec lean_uint8_to_nat__UInt8_toNat lean_uint8_to_uint16
lean_uint8_to_uint32 lean_uint8_to_uint64""".split())

MODEL_CONVERSIONS = {"lean_float_to_bits__Float_toModel", "lean_float_of_bits__Float_ofModel",
                     "lean_float32_to_bits__Float32_toModel", "lean_float32_of_bits__Float32_ofModel"}

POLY_RESULT = {"lean_array_get", "lean_array_get_borrowed", "lean_thunk_get_own"}

def A(i):
    return ('arg', i)

def B(op, a, b):
    return ('bin', op, a, b)

def fixed_cmp(sym):
    m = re.match(r'^lean_(u?int)(8|16|32|64)_(dec_eq|dec_lt|dec_le)$', sym)
    return m.group(3) if m else None

def leaf_of(t):
    return t[1] if t and t[0] == 'leaf' else None

def conv_value(src, dst):
    """`convValue?`: the conversion of a value between two layouts, when it needs no check."""
    s, d = leaf_of(src), leaf_of(dst)
    sb = s is not None and is_big(s)
    db = d is not None and is_big(d)
    if d == 'float':
        # `Number` of a `BigInt` rounds once, to nearest (ties to even), as the C cast does;
        # every integer `number` source is already that double exactly.
        return ('call', 'Number', [A(0)]) if sb else A(0)
    if d == 'float32':
        # A `float32` is a `number` rounded by `Math.fround`.  The integers of at most 24 bits
        # (and a `float32` itself) are already `float32`s; a wider integer `number` (exact in a
        # double) must be rounded once, by `Math.fround`.  A `BigInt` cannot be written inline:
        # `Math.fround(Number(x))` would round twice (`runtime.js` has `$bigToF32`).
        if sb:
            return None
        return A(0) if s in F32_EXACT_LEAVES else ('call', 'Math.fround', [A(0)])
    if sb == db:
        return A(0)
    if db:
        return ('call', 'BigInt', [A(0)])
    return None

# The leaves whose every value is exactly a `float32`.
F32_EXACT_LEAVES = {'uint8', 'uint16', 'int8', 'int16', 'float32'}

def old_inline(name, arg_tys, res_ty):
    """The inline expression the old backend used for an extern (on non-array layouts)."""
    sym = name.split('__')[0]
    t0 = arg_tys[0] if arg_tys else ('leaf', 'bool')
    big = leaf_of(t0) is not None and is_big(leaf_of(t0))
    n = len(arg_tys)
    bin2 = (lambda op: B(op, A(0), A(1))) if n == 2 else (lambda op: None)
    if name in MODEL_CONVERSIONS:
        return A(0)
    if name in VALUE_CONVERSIONS:
        c = conv_value(t0, res_ty)
        if c is not None:
            return c
        return None
    if sym in ('lean_nat_add', 'lean_int_add'):
        return bin2('+') if big else None
    if sym in ('lean_nat_mul', 'lean_int_mul'):
        return bin2('*') if big else None
    if sym == 'lean_int_sub':
        return bin2('-') if big else None
    if sym in ('lean_nat_pow', 'lean_int_pow'):
        # `a ** b` (the exponent is a `Nat`, so it is never negative); a `number` exponent of a
        # `BigInt` base is made a `BigInt` first
        if not big:
            return None
        e = arg_tys[1]
        return B('**', A(0), A(1) if is_big(leaf_of(e)) else ('call', 'BigInt', [A(1)]))
    if sym in ('lean_nat_repr', 'lean_int_repr'):
        # the decimal digits, with a `-` when negative: `String` of a `number` or a `BigInt`
        return ('call', 'String', [A(0)])
    if sym in ('lean_nat_dec_eq', 'lean_int_dec_eq', 'lean_string_dec_eq', 'lean_float_beq'):
        return bin2('===')
    if sym in ('lean_nat_dec_lt', 'lean_int_dec_lt', 'lean_float_decLt'):
        return bin2('<')
    if sym in ('lean_nat_dec_le', 'lean_int_dec_le', 'lean_float_decLe'):
        return bin2('<=')
    if sym == 'lean_int_dec_nonneg':
        return B('>=', A(0), ('big', 0) if big else ('num', 0))
    if sym == 'lean_strict_and':
        return bin2('&&')
    if sym == 'lean_strict_or':
        return bin2('||')
    if sym in ('lean_string_push', 'lean_string_append'):
        return bin2('+')
    if sym == 'lean_float_add':
        return bin2('+')
    if sym == 'lean_float_sub':
        return bin2('-')
    if sym == 'lean_float_mul':
        return bin2('*')
    if sym == 'lean_float_div':
        return bin2('/')
    fc = fixed_cmp(sym)
    if fc == 'dec_eq':
        return bin2('===')
    if fc == 'dec_lt':
        return bin2('<')
    if fc == 'dec_le':
        return bin2('<=')
    return None


def tmpl_js(t, names='abcdefg'):
    k = t[0]
    if k == 'arg':
        return names[t[1]]
    if k == 'bin':
        return f'{tmpl_js(t[2])} {t[1]} {tmpl_js(t[3])}'
    if k == 'un':
        return f'{t[1]}{tmpl_js(t[2])}'
    if k == 'call':
        return f'{t[1]}(' + ', '.join(tmpl_js(a) for a in t[2]) + ')'
    if k == 'num':
        return str(t[1])
    if k == 'big':
        return f'{t[1]}n'
    if k == 'emptyArray':
        return '[]'
    if k == 'member':
        return f'{tmpl_js(t[1])}.{t[2]}'
    if k == 'newTyped':
        return 'new C(' + ', '.join(tmpl_js(a) for a in t[1]) + ')'
    if k == 'typedFrom':
        return 'C.from(' + ', '.join(tmpl_js(a) for a in t[1]) + ')'
    raise ValueError(t)


# ------------------------------------------------------------- inline float math

# `Math` functions that are the C function of a float extern (`float__sin` is `Math.sin(a)`);
# the `Float32` ones round the double result with `Math.fround`.
MATH_1 = {'sin': 'sin', 'cos': 'cos', 'tan': 'tan', 'asin': 'asin', 'acos': 'acos', 'atan': 'atan',
          'sinh': 'sinh', 'cosh': 'cosh', 'tanh': 'tanh', 'asinh': 'asinh', 'acosh': 'acosh',
          'atanh': 'atanh', 'exp': 'exp', 'log': 'log', 'log2': 'log2', 'log10': 'log10',
          'sqrt': 'sqrt', 'cbrt': 'cbrt', 'ceil': 'ceil', 'floor': 'floor', 'fabs': 'abs'}
MATH_2 = {'atan2': 'atan2', 'pow': 'pow'}
# exact in double precision, so no `Math.fround` is needed for `Float32`
MATH_EXACT = {'ceil', 'floor', 'fabs'}

def math_template(name):
    """The template of a float math extern (`sin`, `sinf`, …), if it is one."""
    f32 = name.endswith('f') and name[:-1] in list(MATH_1) + list(MATH_2) + ['exp2']
    base = name[:-1] if f32 else name
    if base in MATH_1:
        t = ('call', 'Math.' + MATH_1[base], [A(0)])
    elif base in MATH_2:
        t = ('call', 'Math.' + MATH_2[base], [A(0), A(1)])
    elif base == 'exp2':
        t = ('call', 'Math.pow', [('num', 2), A(0)])
    else:
        return None
    if f32 and base not in MATH_EXACT:
        t = ('call', 'Math.fround', [t])
    return t

# ---------------------------------------------------------------------- the runtime

def runtime_decls():
    """The top-level declarations of `runtime.js`."""
    try:
        return parse_decls(open(RUNTIME).read())
    except FileNotFoundError:
        return []

ALIAS_RE = re.compile(r'^export const ([\w$]+) = ([\w$]+);$')

def runtime_info():
    """The exported names of the runtime, its aliases (`export const a = b;`: `a -> b`), and
    the names whose evaluation may throw (a `throw`, or a reference to a name that may)."""
    decls = runtime_decls()
    exports = {d['name'] for d in decls if d['exported']}
    aliases = {}
    for d in decls:
        m = ALIAS_RE.match(d['code'].strip())
        if m and d['exported']:
            aliases[m.group(1)] = m.group(2)
    names = [d['name'] for d in decls]
    body = {}
    for d in decls:
        code = d['code']
        code = re.sub(r'//.*$', '', code, flags=re.M)
        code = re.sub(r'/\*.*?\*/', '', code, flags=re.S)
        body[d['name']] = code.split('=', 1)[1] if '=' in code else code
    throws = {n for n in names if re.search(r'\bthrow\b', body[n])}
    changed = True
    while changed:
        changed = False
        for n in names:
            if n in throws:
                continue
            if any(ident_re(t).search(body[n]) for t in throws):
                throws.add(n)
                changed = True
    # back to the names of the operations (`…get$3F` is the operation `…get?`)
    def lean(n):
        for c, e in JS_ESCAPES.items():
            n = n.replace(e, c)
        return n
    return ({lean(n) for n in exports}, {lean(a): lean(b) for a, b in aliases.items()},
            {lean(n) for n in throws})

def ident_re(name):
    return re.compile(r'(?<![\w$])' + re.escape(name) + r'(?![\w$])')

# ---------------------------------------------------------------------------- the ops

def all_cfgs(knobs):
    for vals in itertools.product(['big', 'num'], repeat=len(knobs)):
        cfg = {k: 'big' for k in KNOBS}
        cfg.update(dict(zip(knobs, vals)))
        yield cfg

# The polymorphic array/thunk externs, by hand: 'layout' (one op over every array layout),
# 'split' (a generic and a typed op), 'thunk' / 'any' (over the delayed type).
POLY = {
    'lean_array_get_borrowed': 'layout', 'lean_array_get': 'layout', 'lean_array_push': 'split',
    'lean_array_get_size': 'layout', 'lean_array_set': 'layout', 'lean_array_fset': 'layout',
    'lean_array_fswap': 'layout', 'lean_array_swap': 'layout', 'lean_array_pop': 'split',
    'lean_array_to_list': 'split', 'lean_mk_array': 'split',
    'lean_mk_empty_array_with_capacity__Array_emptyWithCapacity': 'split',
    'lean_mk_empty_array_with_capacity__Array_mkEmpty': 'split',
    'lean_array_mk': 'split',
    'lean_thunk_pure': 'thunk', 'lean_mk_thunk': 'thunk', 'lean_thunk_get_own': 'thunk',
    'lean_dbg_trace_if_shared': 'any', 'lean_panic_fn': 'any',
}

# The array updates that return a copy of their array argument: an `_immutable` operation
# (the extern) and a `_mutable` one (which updates the array in place, when nothing else
# refers to it), at the same signature.  `push` and `pop` change the length, so they are split
# into a generic and a typed operation, and only the generic one has a `_mutable` version (a
# typed array cannot grow or shrink).  `fset` / `fswap` are `set` / `swap` with the bounds
# proved (so their functions do not check them).
UPDATES = {'lean_array_push': 'generic', 'lean_array_pop': 'generic',
           'lean_array_set': 'layout', 'lean_array_swap': 'layout',
           'lean_array_fset': 'layout', 'lean_array_fswap': 'layout'}

LAYOUT_PARAMS = '{A E : JsTy} (l : JsArrayLayout A E)'

def op_name(pre, name):
    base = f'{pre}__{name}'
    return base + '_immutable' if name in UPDATES else base

def mk_op(name, extern, e, args, res, impl, params='', poly=None, group=None, **kw):
    return dict(name=name, extern=extern, lean=e['lean'] if e else '', params=params, args=args,
                res=res, impl=impl, poly=poly, group=group or (e['group'] if e else 'Core'), **kw)

def build_ops(rt):
    """The operations: a list of dicts; and the operations missing from the runtime."""
    exports, aliases, throws = rt
    cat = catalogue()
    ops, missing, seen = [], [], set()
    for e in cat:
        name = e['name']
        knobs = []
        for a in e['args'] + [e['res']]:
            knobs_in(a, knobs)
        for cfg in all_cfgs(knobs):
            arg_tys = [js_ty(a, cfg) for a in e['args']]
            res_ty = js_ty(e['res'], cfg)
            if any(t[0] == 'leanName' for t in arg_tys + [res_ty]):
                continue
            pre = prefix(e, cfg)
            if e['poly'] or name in POLY:
                ops.extend(poly_ops(e, pre, arg_tys, res_ty, seen, exports, missing))
                continue
            opname = op_name(pre, name)
            if opname in seen:
                continue
            seen.add(opname)
            tmpl = old_inline(name, arg_tys, res_ty)
            if tmpl is None:
                tmpl = math_template(name)
            if tmpl is None and opname in INLINE_TABLE:
                tmpl = INLINE_TABLE[opname]
            if tmpl is not None:
                impl = ('inline', tmpl)
            elif opname in exports:
                impl = ('import',)
            else:
                missing.append(opname)
                continue
            ops.append(mk_op(opname, name, e, [lean_of(t) for t in arg_tys], lean_of(res_ty), impl))
    # the mutable updates
    for base, kind in UPDATES.items():
        e = next(x for x in cat if x['name'] == base)
        for o in [o for o in ops if o['extern'] == base and o['poly'] == kind]:
            mname = o['name'].replace('_immutable', '_mutable')
            if mname not in exports:
                missing.append(mname)
                continue
            if kind == 'generic':
                ops.append(mk_op(mname, None, e, o['args'], o['res'], ('import',), params='(α : JsTy)',
                                 poly='generic', mutableOf=o['name']))
            else:
                ops.append(mk_op(mname, None, e, o['args'], o['res'], ('import',),
                                 params=LAYOUT_PARAMS, poly='layout', mutableOf=o['name']))
    # the array functions written in Lean (`ArrayStdExtern`), listed by hand
    # (`scripts/js_ops_array_std.py`)
    for d in array_std.ops():
        if d['name'] not in exports:
            missing.append(d['name'])
            continue
        ops.append(dict(d, impl=('import',), poly='std', group='ArrayStd',
                        ctorArg=d.get('ctorArg'), mutableOf=d.get('mutableOf')))
    # effects and throws
    for o in ops:
        o['eff'] = 'effectful' if o['name'].endswith('_mutable') else 'pure'
        o['throw'] = 'mayThrow' if o['impl'][0] == 'import' and o['name'] in throws else 'doesntThrow'
    # an alias of the runtime at the same signature is the same operation
    byname = {o['name']: o for o in ops}
    merged = {}
    for a, b in aliases.items():
        if a in byname and b in byname:
            oa, ob = byname[a], byname[b]
            if (oa['args'], oa['res'], oa['params'], oa['poly']) == (ob['args'], ob['res'], ob['params'], ob['poly']):
                merged[a] = b
    for o in ops:
        o['sameAs'] = merged.get(o['name'])
    return ops, missing

def poly_ops(e, pre, arg_tys, res_ty, seen, exports, missing):
    name = e['name']
    kind = POLY.get(name)
    def has(opname):
        if opname in exports:
            return True
        missing.append(opname)
        return False
    def sig(var_arr, var_elem):
        def sub(t):
            k = t[0]
            if k == 'var':
                return var_elem
            if k == 'array' and t[1][0] == 'var':
                return var_arr
            return lean_of(t)
        return [sub(t) for t in arg_tys], sub(res_ty)
    if kind == 'layout':
        opname = op_name(pre, name)
        if opname in seen:
            return []
        seen.add(opname)
        args, res = sig('A', 'E')
        if name == 'lean_array_get_size':
            # `a.length`, a `number` (converted to a `BigInt` for a `bigint_nat`)
            length = ('member', A(0), 'length')
            tmpl = length if pre == 'uint53' else ('call', 'BigInt', [length])
            return [mk_op(opname, name, e, args, res, ('inline', tmpl), LAYOUT_PARAMS, 'layout')]
        if not has(opname):
            return []
        return [mk_op(opname, name, e, args, res, ('import',), LAYOUT_PARAMS, 'layout')]
    if kind in ('thunk', 'any'):
        opname = f'{pre}__{name}'
        if opname in seen or not has(opname):
            return []
        seen.add(opname)
        args, res = [lean_of(t, 'α') for t in arg_tys], lean_of(res_ty, 'α')
        # 'any': the result is the type itself (`dbgTraceIfShared msg a`, `panicCore d msg`)
        elem = '(elemOf? (σs ++ [τ]))' if kind == 'thunk' else 'τ'
        return [mk_op(opname, name, e, args, res, ('import',), '(α : JsTy)', 'elem', elemArg=elem)]
    # split: a generic and a typed op
    gname = op_name(pre, name)
    tname = 'typedArray__' + (gname if pre != 'array' else gname[len('array__'):])
    if gname in seen:
        return []
    seen.add(gname)
    sym = name.split('__')[0]
    gargs, gres = sig('(.array α)', 'α')
    targs, tres = sig('(.typedArray t)', '(.terminal t.leaf)')
    TP = '(t : JsTypedElem)'
    res = []
    if sym == 'lean_array_to_list':
        # a list and a generic array are both JavaScript arrays
        res.append(mk_op(gname, name, e, gargs, gres, ('inline', A(0)), '(α : JsTy)', 'generic'))
        if has(tname):
            res.append(mk_op(tname, name, e, targs, '(.list (.terminal t.leaf))', ('import',), TP, 'typed'))
    elif sym in ('lean_array_push', 'lean_array_pop'):
        if has(gname):
            res.append(mk_op(gname, name, e, gargs, gres, ('import',), '(α : JsTy)', 'generic'))
        if has(tname):
            res.append(mk_op(tname, name, e, targs, tres, ('import',), TP, 'typed'))
    elif sym == 'lean_mk_array':
        if has(gname):
            res.append(mk_op(gname, name, e, gargs, gres, ('import',), '(α : JsTy)', 'generic'))
            res.append(mk_op(tname, name, e, targs, tres, ('import',), TP, 'typed', ctorArg=True))
    elif sym == 'lean_mk_empty_array_with_capacity':
        res.append(mk_op(gname, name, e, gargs, gres, ('inline', ('emptyArray',)), '(α : JsTy)', 'generic'))
        res.append(mk_op(tname, name, e, targs, tres, ('inline', ('newTyped', [('num', 0)])), TP, 'typed'))
    elif sym == 'lean_array_mk':
        res.append(mk_op(gname, name, e, gargs, gres, ('inline', A(0)), '(α : JsTy)', 'generic'))
        res.append(mk_op(tname, name, e, ['(.list (.terminal t.leaf))'], tres,
                         ('inline', ('typedFrom', [A(0)])), TP, 'typed'))
    return res

# ------------------------------------------------------------------------ Lean output

def tmpl_lean(t):
    k = t[0]
    if k == 'arg':
        return f'.arg {t[1]}'
    if k == 'bin':
        return f'.bin "{t[1]}" ({tmpl_lean(t[2])}) ({tmpl_lean(t[3])})'
    if k == 'un':
        return f'.un "{t[1]}" ({tmpl_lean(t[2])})'
    if k == 'call':
        return f'.call "{t[1]}" [' + ', '.join(tmpl_lean(a) for a in t[2]) + ']'
    if k == 'num':
        return f'.num {t[1]}'
    if k == 'big':
        return f'.big {t[1]}'
    if k == 'emptyArray':
        return '.emptyArray'
    if k == 'member':
        return f'.member ({tmpl_lean(t[1])}) "{t[2]}"'
    if k == 'newTyped':
        return '.new t.kind.ctorName [' + ', '.join(tmpl_lean(a) for a in t[1]) + ']'
    if k == 'typedFrom':
        return '.call (t.kind.ctorName ++ ".from") [' + ', '.join(tmpl_lean(a) for a in t[1]) + ']'
    raise ValueError(t)

def param_names(o):
    """The explicit parameters of a constructor."""
    return {'layout': ['l'], 'generic': ['α'], 'elem': ['α'], 'typed': ['t']}.get(o['poly'], [])

def ctor_line(op, fam):
    params = op['params'] + ' → ' if op['params'] else ''
    params = params.replace(') (', ') → (').replace('} (', '} → (')
    sig = f".{op['eff']} .{op['throw']} [" + ', '.join(op['args']) + '] ' + op['res']
    if op['impl'][0] == 'inline':
        doc = f'  /-- `{tmpl_js(op["impl"][1])}` ({op["lean"]}) -/\n'
    elif op.get('mutableOf'):
        doc = f'  /-- `{op["mutableOf"]}`, updating the array in place ({op["lean"]}) -/\n'
    else:
        doc = f'  /-- {op["lean"]} -/\n' if op['lean'] else ''
    return f'{doc}  | {op["name"]} : {params}{fam} {sig}\n'

OPS_DIR = os.path.join(ROOT, 'JsTerm', 'Ops')

def lean_file(imports, title, doc, body, namespaces=('MoreJs',)):
    """A generated module: its imports, its doc (after the title and the generated notice), and
    its body, in the namespaces."""
    s = 'module\n\n'
    s += ''.join(f'public import {m}\n' for m in imports)
    s += '\n@[expose] public section\n\nset_option autoImplicit false\n\n'
    s += f'/-!\n# {title}\n\n**Generated** by `scripts/gen_js_ops.py`; do not edit.\n\n{doc}-/\n\n'
    s += ''.join(f'namespace {n}\n\n' for n in namespaces)
    s += body.rstrip('\n') + '\n\n'
    s += ''.join(f'end {n}\n\n' for n in reversed(namespaces))
    s += 'end\n'
    return s

def write_ops_file(rel, s):
    path = os.path.join(OPS_DIR, *rel.split('/'))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, 'w').write(s)

SIG_ARGS = '{e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}'

def write_lean(ops):
    # the constructors with parameters first: the compiled code represents a constructor with
    # fields as an object whose tag must stay small (at most 244), the others as scalars
    by_params = lambda o: (0 if o['params'] else 1)
    live = [o for o in ops if not o['sameAs']]
    imp = sorted([o for o in live if o['impl'][0] == 'import'], key=by_params)
    inl = sorted([o for o in live if o['impl'][0] == 'inline'], key=by_params)
    # the ordering above is only enough while at most 244 constructors have fields (the
    # compiled code refuses to build one of index > 243 that has fields, "tag too big"); past
    # that the inductive must be split into families (as `LeanInitPureExtern` is)
    for kind, lst in (('JsOpImported', imp), ('JsOpInlinable', inl)):
        with_fields = sum(1 for o in lst if o['params'])
        if with_fields > 244:
            sys.exit(f'{kind}: {with_fields} constructors with fields, more than the 244 the '
                     'compiled code can build; split it into families')

    # JsTerm/Ops/Imported.lean
    s = '/-- The operations implemented by the function of `runtime.js` named as the constructor,\n'
    s += '    indexed by their effects, the types of their arguments and the type of their result. -/\n'
    s += 'inductive JsOpImported : Effectfulness → MayThrow → List JsTy → JsTy → Type where\n'
    for o in imp:
        s += ctor_line(o, 'JsOpImported')
    s += f'''
namespace JsOpImported

/-- The names of the constructors of `JsOpImported`, in order. -/
def names : Array String := ctor_names% JsOpImported

/-- The name of the operation (the name of its constructor). -/
def name {SIG_ARGS}
    (op : JsOpImported e t σs τ) : String :=
  JsOpImported.names[op.ctorIdx]!

/-- The name of the function of `runtime.js` that implements the operation: the name of its
    constructor, made a JavaScript identifier (`jsSafeName`). -/
def runtimeName {SIG_ARGS}
    (op : JsOpImported e t σs τ) : String :=
  jsSafeName op.name

'''
    s += '/-- The globals passed before the arguments (the constructor of a typed array). -/\n'
    s += f'def extraArgs {SIG_ARGS} :\n'
    s += '    JsOpImported e t σs τ → List String\n'
    for o in imp:
        if o.get('ctorArg'):
            # the explicit parameters before the typed element `t` (the layouts of the
            # arguments, for the operations of `ArrayStdExtern`)
            before = ''.join('_ ' for _ in re.findall(r'\((l|l₁|l₂) :', o['params']))
            s += f'  | .{o["name"]} {before}t => [t.kind.ctorName]\n'
    s += '  | _ => []\n\n'
    s += '/-- The version of an array update that updates the array in place, if it has one. -/\n'
    s += f'def toMutable? {SIG_ARGS} :\n'
    s += '    JsOpImported e t σs τ → Option (Σ t\' : MayThrow, JsOpImported .effectful t\' σs τ)\n'
    for o in imp:
        m = o.get('mutableOf')
        if not m:
            continue
        if o['poly'] == 'generic':
            s += f'  | .{m} α => some ⟨_, .{o["name"]} α⟩\n'
        else:
            s += f'  | .{m} l => some ⟨_, .{o["name"]} l⟩\n'
    s += '  | _ => none\n\n'
    s += 'end JsOpImported\n'
    write_ops_file('Imported.lean', lean_file(
        ['JsTerm.Ty.Basic', 'JsTerm.Ops.Basic', 'LeanScript.Term.Extern.NameElab'],
        'The operations of `JsTerm` implemented by `runtime.js`',
        '''`JsOpImported`: the operations that call the function of `runtime.js` named as their
constructor (`JsOpImported.runtimeName`, read off the constructors by `ctor_names%`), which the
generated module imports; the families, their names and their effects are explained in
`JsTerm.Ops.Basic`.  The array updates come in two versions, `…_immutable` (the extern: a copy
of the array) and `…_mutable` (the same update in place), which `JsOpImported.toMutable?`
pairs.
''', s))

    # JsTerm/Ops/Inlinable.lean
    s = '/-- The operations written inline, indexed by their effects, the types of their arguments\n'
    s += '    and the type of their result. -/\n'
    s += 'inductive JsOpInlinable : Effectfulness → MayThrow → List JsTy → JsTy → Type where\n'
    for o in inl:
        s += ctor_line(o, 'JsOpInlinable')
    s += f'''
namespace JsOpInlinable

/-- The names of the constructors of `JsOpInlinable`, in order. -/
def names : Array String := ctor_names% JsOpInlinable

/-- The name of the operation (the name of its constructor). -/
def name {SIG_ARGS}
    (op : JsOpInlinable e t σs τ) : String :=
  JsOpInlinable.names[op.ctorIdx]!

'''
    s += 'end JsOpInlinable\n'
    write_ops_file('Inlinable.lean', lean_file(
        ['JsTerm.Ty.Basic', 'JsTerm.Ops.Basic', 'LeanScript.Term.Extern.NameElab'],
        'The operations of `JsTerm` written inline',
        '''`JsOpInlinable`: the operations written in place of their call as a JavaScript operator,
conversion or literal over their arguments (`JsOpInlinable.template`, in `JsTerm.Ops.Template`);
they never throw.  The families, their names and their effects are explained in
`JsTerm.Ops.Basic`.
''', s))

    # JsTerm/Ops/Template.lean
    s = 'namespace JsOpInlinable\n\n'
    s += '/-- The JavaScript of an inlined operation, over its arguments. -/\n'
    s += f'def template {SIG_ARGS} :\n'
    s += '    JsOpInlinable e t σs τ → JsInline\n'
    for o in inl:
        ps = param_names(o)
        pat = ''.join(' ' + (p if p == 't' else '_') for p in ps)
        s += f'  | .{o["name"]}{pat} => {tmpl_lean(o["impl"][1])}\n'
    s += '\nend JsOpInlinable\n'
    write_ops_file('Template.lean', lean_file(
        ['JsTerm.Ops.Inlinable'],
        'The JavaScript of the operations of `JsTerm` written inline',
        '''`JsOpInlinable.template`: the JavaScript operator, conversion or literal (a `JsInline`, in
`JsTerm.Ops.Basic`) written in place of a call of each operation of `JsOpInlinable`
(`JsTerm.Ops.Inlinable`), over its arguments.
''', s))
    write_lookup(ops)

def cand(o):
    """The candidate expression of a monomorphic operation, in the lookup."""
    wrap = 'imported' if o['impl'][0] == 'import' else 'inlined'
    return f'⟨_, _, _, _, .{wrap} .{o["name"]}⟩'

def poly_cands(os_):
    """The candidates of the polymorphic operations of an extern, as one expression over `σs`
    and `τ`: the layout of the array among the types is found once (`layoutOf?`), and each
    operation is instantiated from it (or from the delayed type, `elemOf?`)."""
    def item(o, arg):
        wrap = 'imported' if o['impl'][0] == 'import' else 'inlined'
        return f'⟨_, _, _, _, .{wrap} (.{o["name"]} {arg})⟩'
    by = {k: [o for o in os_ if o['poly'] == k] for k in ('layout', 'generic', 'typed', 'elem')}
    unknown = [o for o in os_ if o['poly'] not in by]
    if unknown:
        raise ValueError(unknown)
    parts = []
    if by['elem']:
        parts.append('[' + ', '.join(item(o, o.get('elemArg', '(elemOf? (σs ++ [τ]))')) for o in by['elem']) + ']')
    if by['layout'] or by['generic'] or by['typed']:
        inner = []
        if by['layout']:
            inner.append('[' + ', '.join(item(o, 'l') for o in by['layout']) + ']')
        if by['generic'] or by['typed']:
            g = '[' + ', '.join(item(o, 'α') for o in by['generic']) + ']'
            t = '[' + ', '.join(item(o, 't') for o in by['typed']) + ']'
            ga = 'α' if by['generic'] else '_'
            ta = 't' if by['typed'] else '_'
            inner.append(f'(match l with | .generic {ga} => {g} | .typed {ta} => {t})')
        parts.append('(match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => '
                     + ' ++ '.join(inner) + ' | none => [])')
    return parts

def check_unique_sigs(ext, targets):
    """No two operations of an extern at the same signature: the lookup must find at most one
    candidate for a call (`OpsSpec.LookupUnique` proves it of the generated modules)."""
    seen = {}
    for o in targets:
        key = (repr(o['args']), repr(o['res']), o['params'], o['poly'])
        if key in seen:
            sys.exit(f'the extern {ext} has two operations at the same signature: '
                     f'{seen[key]} and {o["name"]}')
        seen[key] = o['name']

# The groups of externs of the lookup, one module `JsTerm/Ops/Cands/<name>.lean` each, in the
# order the lookup tries them (the groups are disjoint, so the order does not matter).
CAND_GROUPS = [
    ('Nat', '`Nat` and `Int`', '`lean_nat_*`, `lean_int_*`'),
    ('UInt', 'the unsigned fixed-width integers', '`lean_uint8_*`, …, `lean_uint64_*`, `lean_usize_*`'),
    ('SInt', 'the signed fixed-width integers', '`lean_int8_*`, …, `lean_int64_*`, `lean_isize_*`'),
    ('Float', 'the floating-point numbers',
     '`lean_float_*`, `lean_float32_*` and the C functions of `math.h`: `sin`, `sinf`, …'),
    ('String', 'the strings', '`lean_string_*`, `lean_substring_*`, `lean_slice_*`, `lean_char_*`'),
    ('Misc', 'the other externs', 'arrays, thunks, `Bool` conversions, version and platform'),
    ('ArrayStd', 'the array functions written in Lean',
     '`ArrayStdExtern`: `lean_array_append`, `lean_array_map`, …, `lean_list_append`; listed by '
     'hand in `scripts/js_ops_array_std.py`'),
]

def cand_group(ext):
    """The group of an extern (the name of its module in `JsTerm/Ops/Cands/`)."""
    if ext in array_std.CANDS:
        return 'ArrayStd'
    if not ext.startswith('lean_') or ext.startswith('lean_float'):
        return 'Float'
    if re.match(r'lean_(nat|int)_', ext):
        return 'Nat'
    if re.match(r'lean_(uint\d+|usize)_', ext):
        return 'UInt'
    if re.match(r'lean_(int\d+|isize)_', ext):
        return 'SInt'
    if re.match(r'lean_(string|substring|slice|char)_', ext):
        return 'String'
    return 'Misc'

def write_lookup(ops):
    byname = {o['name']: o for o in ops}
    by_ext = {}
    for o in ops:
        if o['extern']:
            target = byname[o['sameAs']] if o['sameAs'] else o
            # an alias is the operation it names: list it once
            if target not in by_ext.setdefault(o['extern'], []):
                by_ext[o['extern']].append(target)
    names = sorted(by_ext)
    group_sig = {}
    for group, what, which in CAND_GROUPS:
        s = ''
        mine = [ext for ext in names if cand_group(ext) == group]
        uses_sig = {}
        if group == 'ArrayStd':
            s += array_std.HELPERS
        for ext in mine:
            check_unique_sigs(ext, by_ext[ext])
            if group == 'ArrayStd':
                uses_sig[ext] = True
                s += f'/-- The operations of `{ext}`. -/\n'
                body = array_std.CANDS[ext]
                ps = '(σs : List JsTy)' if 'σs' in body else '(_ : List JsTy)'
                pt = '(τ : JsTy)' if 'τ' in body else '(_ : JsTy)'
                s += f'def «cands_{ext}» {ps} {pt} : List Cand :=\n'
                s += '  ' + body + '\n\n'
                continue
            mono = [cand(o) for o in by_ext[ext] if o['poly'] is None]
            rest = poly_cands([o for o in by_ext[ext] if o['poly'] is not None])
            uses_sig[ext] = bool(rest)
            expr = ' ++ '.join((['[' + ', '.join(mono) + ']'] if mono else []) + rest)
            s += f'/-- The operations of `{ext}`. -/\n'
            if rest:
                s += f'def «cands_{ext}» (σs : List JsTy) (τ : JsTy) : List Cand :=\n'
            else:
                s += f'def «cands_{ext}» : List Cand :=\n'
            s += '  ' + expr + '\n\n'
        group_sig[group] = any(uses_sig.values())
        s += f'/-- The candidates of the extern `name`, when it is one of {what}. -/\n'
        sig = ' (σs : List JsTy) (τ : JsTy)' if group_sig[group] else ''
        s += f'def cands{group}? (name : String){sig} : Option (List Cand) :=\n'
        s += '  match name with\n'
        for ext in mine:
            s += (f'  | "{ext}" => some («cands_{ext}» σs τ)\n' if uses_sig[ext]
                  else f'  | "{ext}" => some «cands_{ext}»\n')
        s += '  | _ => none\n'
        write_ops_file(f'Cands/{group}.lean', lean_file(
            ['JsTerm.Ops.Op'],
            f'The operations of the externs of {what}',
            f'''The candidates (`JsOp.Cand`) of every extern of {what} ({which}): its
operations at their signatures, for the lookup (`JsOp.lookup`, `JsTerm.Ops.Lookup`).
''', s, ('MoreJs', 'JsOp')))
    s = ('/-- The candidates of the extern `name` (none if it is not an extern of the catalogue): its\n'
         '    operations, one per representation of its configurable types, at most one of them at\n'
         '    any signature (`OpsSpec.LookupUnique`). -/\n')
    s += 'def cands (name : String) (σs : List JsTy) (τ : JsTy) : List Cand :=\n'
    s += '  (' + ' <|>\n    '.join(f'cands{g}? name' + (' σs τ' if group_sig[g] else '')
                                  for g, _, _ in CAND_GROUPS)
    s += ').getD []\n\n'
    s += ('/-- The operation of the extern `name` at the signature `σs → τ`, if there is one: the\n'
          '    candidate at this signature (there is at most one, `OpsSpec.LookupUnique`). -/\n')
    s += 'def lookup (name : String) (σs : List JsTy) (τ : JsTy) : Option (JsSomeOp σs τ) :=\n'
    s += '  firstOf σs τ (cands name σs τ)\n'
    write_ops_file('Lookup.lean', lean_file(
        [f'JsTerm.Ops.Cands.{g}' for g, _, _ in CAND_GROUPS],
        'Finding the operation of an extern call',
        '''`JsOp.lookup name σs τ` is the operation of the extern `name` (as the catalogue spells it,
`lean_nat_div`) at the argument types `σs` and the result type `τ`, if there is one: the
constructor of `JsOpImported` or `JsOpInlinable` whose signature is exactly `σs → τ` (a
polymorphic one instantiated from the types), with its effects.  The candidates of the externs
are in `JsTerm/Ops/Cands/`, by group of externs.
''', s, ('MoreJs', 'JsOp')))

# ------------------------------------------------------------------------------ main

# The operations whose runtime function was one operator, kept as templates.
INLINE_JSON = os.path.join(ROOT, 'scripts', 'js_ops_inline.json')
INLINE_TABLE = {}

def decode(v):
    if isinstance(v, list):
        if v and v[0] == '__list__':
            return [decode(x) for x in v[1:]]
        return tuple(decode(x) for x in v)
    return v

def load_inline():
    if os.path.exists(INLINE_JSON):
        for k, v in json.load(open(INLINE_JSON)).items():
            INLINE_TABLE[k] = decode(v)

def main():
    load_inline()
    rt = runtime_info()
    ops, missing = build_ops(rt)
    if len(sys.argv) >= 2 and sys.argv[1] == '--report':
        for r in missing:
            print(r)
        used = {o['name'] for o in ops if o['impl'][0] == 'import'}
        unused = sorted(n for n in rt[0] if n not in used and n not in rt[1])
        if unused:
            print('# exported by runtime.js but not an operation:', ' '.join(unused))
        return
    if missing:
        print('error: no implementation (in runtime.js or inline) for:', file=sys.stderr)
        for r in missing:
            print('  ' + r, file=sys.stderr)
        sys.exit(1)
    write_lean(ops)
    live = [o for o in ops if not o['sameAs']]
    print(f'{len([o for o in live if o["impl"][0] == "import"])} imported, '
          f'{len([o for o in live if o["impl"][0] == "inline"])} inlined, '
          f'{len([o for o in ops if o["sameAs"]])} merged into the operation they alias')

if __name__ == '__main__':
    main()
