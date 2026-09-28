#!/usr/bin/env python3
"""Generate the typed operations of `JsTerm` from the catalogue of externs.

    python3 scripts/gen_js_ops.py                       # regenerate the Lean files
    python3 scripts/gen_js_ops.py --migrate-runtime OLD # (once) also rewrite runtime.js

Every extern of the catalogue (`LeanScript/LeanInitPureExterns/*.lean`) is split by the
JavaScript representation of its arguments and its result: `lean_nat_div : [nat, nat] -> nat`
becomes `bigint_nat__lean_nat_div : [bigint_nat, bigint_nat] -> bigint_nat` and
`uint53__lean_nat_div : [uint53, uint53] -> uint53`.  The name of an operation is its *type
prefix* and the name of the extern, joined by `__`; the prefix is the list of the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` with `n > 53`), in order of first appearance and without repetitions, or,
when the signature has none, the first leaf of the signature (`uint32__lean_uint32_add`), or
the family of the polymorphic ones (`array__lean_array_push`, `thunk__lean_mk_thunk`).

An operation is either

* **inlined** (`JsTerm/OpsInlined.lean`): a single JavaScript operator, conversion or literal
  over its arguments (`bigint_nat__lean_nat_land` is `a & b`), written by `JsInline`; or
* **imported** (`JsTerm/OpsImported.lean`): a function of the same name exported by
  `runtime.js`, which the generated module imports.

An extern that is neither for some representation has no operation there: a call of it is
converted to a call that throws (`JsExpr.unimplemented`).  `JsTerm/OpsLookup.lean` finds the
operation of an extern call from the name of the extern and the types of its arguments and
result.
"""
import os, re, sys, itertools, subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAT = os.path.join(ROOT, 'LeanScript', 'LeanInitPureExterns')
RUNTIME = os.environ.get('LEANSCRIPT_RUNTIME_OUT', os.path.join(ROOT, 'runtime.js'))

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
            out.append(dict(name=name, args=args, res=res, poly=poly, lean=(lean or '').strip()))
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
    if k in ('thunk', 'lazy'):
        return (k, args[0])
    if k == 'option':
        return ('union', [[], [args[0]]])
    if k == 'prod':
        return ('record', args)
    if k == 'fn1':
        return ('fn', args[0], args[1])
    if k == 'fn2':
        return ('fn', args[0], ('fn', args[1], args[2]))
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
    if k in ('array', 'list', 'thunk', 'lazy'):
        return f'(.{k} {lean_of(t[1], var)})'
    if k == 'union':
        return '(.union [' + ', '.join('[' + ', '.join(lean_of(a, var) for a in c) + ']' for c in t[1]) + '])'
    if k == 'record':
        return '(.record [' + ', '.join(lean_of(a, var) for a in t[1]) + '])'
    if k == 'fn':
        return f'(.fn {lean_of(t[1], var)} {lean_of(t[2], var)})'
    raise ValueError(t)

def leaves(t, acc):
    if t[0] == 'leaf':
        acc.append(t[1])
    elif t[0] in ('array', 'list', 'thunk', 'lazy'):
        leaves(t[1], acc)
    elif t[0] == 'union':
        for c in t[1]:
            for a in c:
                leaves(a, acc)
    elif t[0] == 'record':
        for a in t[1]:
            leaves(a, acc)
    elif t[0] == 'fn':
        leaves(t[1], acc)
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

# ------------------------------------------------------------ the old runtime, parsed

def split_sections(src):
    """The sections of the merged runtime: `(file name, text)`."""
    out = []
    cur, lines = None, []
    for line in src.split('\n'):
        m = re.match(r'^==== FILE: runtime/(\S+) ====$', line)
        if m:
            if cur:
                out.append((cur, '\n'.join(lines)))
            cur, lines = m.group(1), []
        else:
            lines.append(line)
    if cur:
        out.append((cur, '\n'.join(lines)))
    return out

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

# ------------------------------------------------------------------ old lowering rules

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
    if d in ('float', 'float32'):
        return ('call', 'Number', [A(0)]) if sb else A(0)
    if sb == db:
        return A(0)
    if db:
        return ('call', 'BigInt', [A(0)])
    return None

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

def rt_name(name):
    if name == 'lean_uint32_of_nat__Char_ofNatAux':
        return 'Char_ofNatAux'
    if name == 'lean_uint64_to_nat__UInt64_toBitVec':
        return 'UInt64_toBitVec'
    return '$' + name.split('__')[0]

def rt_section(e, res_ty, cfg):
    sym = e['name'].split('__')[0]
    if sym in POLY_RESULT:
        return 'lean_runtime_non_configurable.mjs'
    k = knob_of(e['res']) if e['res'][0] in ('prim', 'bitvec') else None
    if k is None:
        return 'lean_runtime_non_configurable.mjs'
    l = leaf_of(res_ty)
    big = l is not None and is_big(l)
    return f"lean_runtime_{k}_{'bigint' if big else 'num'}.mjs"

# Simple bodies of old runtime functions that become inline operations.
SIMPLE_BIN = ['===', '!==', '<=', '>=', '<<', '>>>', '>>', '&&', '||', '+', '-', '*', '/', '%',
              '&', '|', '^', '<', '>']

def simple_template(code):
    """The template of a runtime function whose body is one operator on its parameters."""
    m = re.match(r'^export const [\w$]+ = \(([\w, ]*)\) => (.*);$', code.strip())
    if not m or '\n' in code.strip():
        return None
    params = [p.strip() for p in m.group(1).split(',') if p.strip()]
    body = m.group(2).strip()
    idx = {p: i for i, p in enumerate(params)}
    if body in idx:
        return A(idx[body])
    mm = re.match(r'^(BigInt|Number)\((\w+)\)$', body)
    if mm and mm.group(2) in idx:
        return ('call', mm.group(1), [A(idx[mm.group(2)])])
    mm = re.match(r'^([-~!])(\w+)$', body)
    if mm and mm.group(2) in idx:
        return ('un', mm.group(1), A(idx[mm.group(2)]))
    for op in SIMPLE_BIN:
        parts = body.split(' ' + op + ' ')
        if len(parts) == 2 and parts[0] in idx and parts[1] in idx:
            return B(op, A(idx[parts[0]]), A(idx[parts[1]]))
    return None

# ---------------------------------------------------------------------------- the ops

def all_cfgs(knobs):
    for vals in itertools.product(['big', 'num'], repeat=len(knobs)):
        cfg = {k: 'big' for k in KNOBS}
        cfg.update(dict(zip(knobs, vals)))
        yield cfg

# The polymorphic array/thunk externs, by hand.  Each entry:
#   kind: 'layout' (one op over every array layout), 'split' (a generic and a typed op),
#   impl for generic / typed: ('import', runtime function) / ('inline', template).
POLY = {
    'lean_array_get_borrowed': 'layout', 'lean_array_get': 'layout', 'lean_array_push': 'layout',
    'lean_array_get_size': 'layout', 'lean_array_set': 'layout', 'lean_array_fset': 'layout',
    'lean_array_fswap': 'layout', 'lean_array_swap': 'layout', 'lean_array_pop': 'layout',
    'lean_array_to_list': 'split', 'lean_mk_array': 'split',
    'lean_mk_empty_array_with_capacity__Array_emptyWithCapacity': 'split',
    'lean_mk_empty_array_with_capacity__Array_mkEmpty': 'split',
    'lean_array_mk': 'split',
    'lean_thunk_pure': 'thunk', 'lean_mk_thunk': 'thunk', 'lean_thunk_get_own': 'thunk',
    'lean_dbg_trace_if_shared': 'any',
}

# The runtime functions of the in-place array updates (not externs).
INPLACE = [('lean_array_push_inplace', 'lean_array_push'),
           ('lean_array_set_inplace', 'lean_array_set'),
           ('lean_array_swap_inplace', 'lean_array_swap'),
           ('lean_array_pop_inplace', 'lean_array_pop')]

def build_ops(runtime_exports, old_sections=None):
    """The ops: a list of dicts (name, extern, cfg-independent signature strings, impl)."""
    cat = catalogue()
    ops = []
    seen = set()
    migrate = []  # (op name, section, function name, specialisation) for the runtime
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
                ops.extend(poly_ops(e, cfg, pre, arg_tys, res_ty, seen, runtime_exports,
                                    old_sections, migrate))
                continue
            opname = f'{pre}__{name}'
            if opname in seen:
                continue
            seen.add(opname)
            tmpl = old_inline(name, arg_tys, res_ty)
            impl = None
            if tmpl is not None:
                impl = ('inline', tmpl)
            else:
                fn = rt_name(name)
                sec = rt_section(e, res_ty, cfg)
                if old_sections is not None:
                    d = old_sections.get(sec, {}).get(fn)
                    if d is not None and d['exported']:
                        st = simple_template(d['code'])
                        if st is not None and opname != 'uint53__lean_nat_land':
                            impl = ('inline', st)
                            INLINE_TABLE[opname] = st
                        else:
                            impl = ('import', None)
                            migrate.append((opname, sec, fn, pre))
                elif opname in INLINE_TABLE:
                    impl = ('inline', INLINE_TABLE[opname])
                elif opname in runtime_exports:
                    impl = ('import', None)
            if impl is None:
                if REPORT is not None:
                    REPORT.append(opname)
                continue
            ops.append(dict(name=opname, extern=name, lean=e['lean'], params='',
                            args=[lean_of(t) for t in arg_tys], res=lean_of(res_ty), impl=impl,
                            poly=None))
    # the in-place updates
    for (ip, base) in INPLACE:
        for pre in (['bigint_nat', 'uint53'] if base in ('lean_array_set', 'lean_array_swap') else ['array']):
            opname = f'{pre}__{ip}'
            nat = f'(.terminal .{pre})'
            if base == 'lean_array_push':
                args, res = ['A', 'E'], 'A'
            elif base == 'lean_array_set':
                args, res = ['A', nat, 'E'], 'A'
            elif base == 'lean_array_swap':
                args, res = ['A', nat, nat], 'A'
            else:
                args, res = ['A'], 'A'
            if old_sections is not None:
                migrate.append((opname, 'lean_runtime_non_configurable.mjs', '$' + ip, pre))
            elif opname not in runtime_exports:
                continue
            ops.append(dict(name=opname, extern=None, lean=f'(in place: `{base}` on an array nothing else refers to)',
                            params='{A E : JsTy} (l : JsArrayLayout A E)', args=args, res=res,
                            impl=('import', None), poly='layout'))
    return ops, migrate

def poly_ops(e, cfg, pre, arg_tys, res_ty, seen, runtime_exports, old_sections, migrate):
    name = e['name']
    kind = POLY.get(name)
    out = []
    fn = rt_name(name)
    def has(opname):
        if old_sections is not None:
            d = old_sections['lean_runtime_non_configurable.mjs'].get(fn)
            return d is not None and d['exported']
        return opname in runtime_exports
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
        opname = f'{pre}__{name}'
        if name == 'lean_array_get_size' and opname not in seen:
            # `a.length`, a `number` (converted to a `BigInt` for a `bigint_nat`)
            seen.add(opname)
            length = ('member', A(0), 'length')
            tmpl = length if pre == 'uint53' else ('call', 'BigInt', [length])
            args, res = sig('A', 'E')
            return [dict(name=opname, extern=name, lean=e['lean'],
                         params='{A E : JsTy} (l : JsArrayLayout A E)',
                         args=args, res=res, impl=('inline', tmpl), poly='layout')]
        if opname in seen or not has(opname):
            return []
        seen.add(opname)
        args, res = sig('A', 'E')
        if old_sections is not None:
            migrate.append((opname, 'lean_runtime_non_configurable.mjs', fn, pre))
        return [dict(name=opname, extern=name, lean=e['lean'], params='{A E : JsTy} (l : JsArrayLayout A E)',
                     args=args, res=res, impl=('import', None), poly='layout')]
    if kind == 'thunk' or kind == 'any':
        opname = f'{pre}__{name}'
        if opname in seen or not has(opname):
            return []
        seen.add(opname)
        args, res = [lean_of(t, 'α') for t in arg_tys], lean_of(res_ty, 'α')
        if old_sections is not None:
            migrate.append((opname, 'lean_runtime_non_configurable.mjs', fn, pre))
        return [dict(name=opname, extern=name, lean=e['lean'], params='(α : JsTy)', args=args, res=res,
                     impl=('import', None), poly='elem')]
    # split: a generic and a typed op
    gname = f'{pre}__{name}'
    tname = f'typedArray__{pre}__{name}' if pre != 'array' else f'typedArray__{name}'
    if gname in seen:
        return []
    seen.add(gname)
    sym = name.split('__')[0]
    gargs, gres = sig('(.array α)', 'α')
    targs, tres = sig('(.typedArray k e)', '(.terminal e)')
    res = []
    if sym == 'lean_array_to_list':
        # a list and a generic array are both JavaScript arrays
        res.append(dict(name=gname, extern=name, lean=e['lean'], params='(α : JsTy)', args=gargs, res=gres,
                        impl=('inline', A(0)), poly='generic'))
        tres = '(.list (.terminal e))'
        if has(tname):
            if old_sections is not None:
                migrate.append((tname, 'lean_runtime_non_configurable.mjs', fn, pre))
            res.append(dict(name=tname, extern=name, lean=e['lean'], params='(k : JsTypedArray) (e : JsTerminalTy)',
                            args=targs, res=tres, impl=('import', None), poly='typed'))
    elif sym == 'lean_mk_array':
        if has(gname):
            if old_sections is not None:
                migrate.append((gname, 'lean_runtime_non_configurable.mjs', fn, pre))
                migrate.append((tname, 'lean_runtime_non_configurable.mjs', '$lean_mk_typed_array', pre))
            res.append(dict(name=gname, extern=name, lean=e['lean'], params='(α : JsTy)', args=gargs, res=gres,
                            impl=('import', None), poly='generic'))
            res.append(dict(name=tname, extern=name, lean=e['lean'], params='(k : JsTypedArray) (e : JsTerminalTy)',
                            args=targs, res=tres, impl=('import', None), poly='typed', ctorArg=True))
    elif sym == 'lean_mk_empty_array_with_capacity':
        res.append(dict(name=gname, extern=name, lean=e['lean'], params='(α : JsTy)', args=gargs, res=gres,
                        impl=('inline', ('emptyArray',)), poly='generic'))
        res.append(dict(name=tname, extern=name, lean=e['lean'], params='(k : JsTypedArray) (e : JsTerminalTy)',
                        args=targs, res=tres, impl=('inline', ('newTyped', [('num', 0)])), poly='typed'))
    elif sym == 'lean_array_mk':
        res.append(dict(name=gname, extern=name, lean=e['lean'], params='(α : JsTy)', args=gargs, res=gres,
                        impl=('inline', A(0)), poly='generic'))
        targs = ['(.list (.terminal e))']
        res.append(dict(name=tname, extern=name, lean=e['lean'], params='(k : JsTypedArray) (e : JsTerminalTy)',
                        args=targs, res=tres, impl=('inline', ('typedFrom', [A(0)])), poly='typed'))
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
        return '.new k.ctorName [' + ', '.join(tmpl_lean(a) for a in t[1]) + ']'
    if k == 'typedFrom':
        return '.call (k.ctorName ++ ".from") [' + ', '.join(tmpl_lean(a) for a in t[1]) + ']'
    raise ValueError(t)

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

def ctor_line(op, fam):
    params = op['params'] + ' → ' if op['params'] else ''
    params = params.replace(') (', ') → (').replace('} (', '} → (')
    sig = '[' + ', '.join(op['args']) + '] ' + op['res']
    doc = ''
    if op['impl'][0] == 'inline':
        doc = f'  /-- `{tmpl_js(op["impl"][1])}` ({op["lean"]}) -/\n'
    else:
        doc = f'  /-- {op["lean"]} -/\n' if op['lean'] else ''
    return f'{doc}  | {op["name"]} : {params}{fam} {sig}\n'

HEADER_IMPORTED = '''module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm` that call the runtime

**Generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`) and the exports of `runtime.js`; do not edit.

Every extern of the catalogue is split by the JavaScript representation of its arguments and
its result (`lean_nat_div : [nat, nat] → nat` is `bigint_nat__lean_nat_div : [bigint_nat,
bigint_nat] → bigint_nat` and `uint53__lean_nat_div : [uint53, uint53] → uint53`).  The
operations here are the ones implemented by a function of `runtime.js` of the **same name**,
which the generated module imports; the ones written as a JavaScript operator or conversion
are in `JsTerm.OpsInlined`.

The name of an operation is its *type prefix* and the name of the extern, joined by `__`: the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` for `n > 53`) in order of first appearance and without repetitions, or,
when there is none, the first leaf of the signature (`uint32__lean_uint32_add`), or the family
of a polymorphic operation (`array__lean_array_push`, `thunk__lean_mk_thunk`).  A polymorphic
array operation works on every layout of an array (`JsArrayLayout`: a generic array or a typed
array).
-/

namespace MoreJs

/-- The operations implemented by a function of `runtime.js` of the same name, indexed by
    the types of their arguments and of their result. -/
inductive JsOpImported : List JsTy → JsTy → Type where
'''

HEADER_INLINED = '''module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm` written inline

**Generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`); do not edit.

The operations whose JavaScript is one operator, conversion or literal over their arguments
(`bigint_nat__lean_nat_land` is `a & b`, `uint8__lean_uint8_to_nat__UInt8_toNat` at
`bigint_nat` is `BigInt(a)`): each is printed in place of its call, as its template
(`JsOpInlined.template`, a `JsInline` over the arguments).  The naming is the one of
`JsTerm.OpsImported`.
-/

namespace MoreJs

/-- How an inlined operation is written in JavaScript, over its arguments. -/
inductive JsInline where
  /-- The argument of position `i` (from `0`). -/
  | arg (i : Nat)
  /-- `a op b`, for the JavaScript binary operator `op` (`+`, `&`, `===`, …). -/
  | bin (op : String) (a b : JsInline)
  /-- `op a`, for the JavaScript prefix operator `op` (`-`, `~`, `!`). -/
  | un (op : String) (a : JsInline)
  /-- `f(args)`, `f` a global function (`BigInt`, `Number`, `Uint8Array.from`). -/
  | call (f : String) (args : List JsInline)
  /-- `new C(args)`. -/
  | new (ctor : String) (args : List JsInline)
  /-- An integer `number` literal. -/
  | num (n : Int)
  /-- A `BigInt` literal. -/
  | big (n : Int)
  /-- `[]`. -/
  | emptyArray
  /-- `a.field` (`a.length`). -/
  | member (a : JsInline) (field : String)
  deriving Inhabited, Repr

/-- The operations written inline, indexed by the types of their arguments and of their
    result. -/
inductive JsOpInlined : List JsTy → JsTy → Type where
'''

def write_lean(ops):
    # the constructors with parameters first: the compiled code represents a constructor with
    # fields as an object whose tag must stay small (at most 244), the others as scalars
    by_params = lambda o: 0 if o['params'] else 1
    imp = sorted([o for o in ops if o['impl'][0] == 'import'], key=by_params)
    inl = sorted([o for o in ops if o['impl'][0] == 'inline'], key=by_params)
    # --- imported
    s = HEADER_IMPORTED
    for o in imp:
        s += ctor_line(o, 'JsOpImported')
    s += '\nnamespace JsOpImported\n\n'
    s += '/-- The name of the operation: the name of its function in `runtime.js`. -/\n'
    s += 'def name {σs : List JsTy} {τ : JsTy} : JsOpImported σs τ → String\n'
    for o in imp:
        s += f'  | .{o["name"]} {" ".join("_" for _ in param_names(o))} => "{o["name"]}"\n'.replace('  _ =>', ' =>').replace('  =>', ' =>')
    s += '\n/-- The globals passed before the arguments (the constructor of a typed array). -/\n'
    s += 'def extraArgs {σs : List JsTy} {τ : JsTy} : JsOpImported σs τ → List String\n'
    for o in imp:
        if o.get('ctorArg'):
            s += f'  | .{o["name"]} k _ => [k.ctorName]\n'
    s += '  | _ => []\n'
    s += '\n/-- The name of every operation (for the tests: `runtime.js` exports each). -/\n'
    s += 'def allNames : List String := [\n' + ',\n'.join(f'  "{o["name"]}"' for o in imp) + ']\n'
    s += '\nend JsOpImported\n\nend MoreJs\n\nend\n'
    open(os.path.join(ROOT, 'JsTerm', 'OpsImported.lean'), 'w').write(s)
    # --- inlined
    s = HEADER_INLINED
    for o in inl:
        s += ctor_line(o, 'JsOpInlined')
    s += '\nnamespace JsOpInlined\n\n'
    s += '/-- The name of the operation. -/\n'
    s += 'def name {σs : List JsTy} {τ : JsTy} : JsOpInlined σs τ → String\n'
    for o in inl:
        s += f'  | .{o["name"]}{"".join(" _" for _ in param_names(o))} => "{o["name"]}"\n'
    s += '\n/-- The JavaScript of the operation, over its arguments. -/\n'
    s += 'def template {σs : List JsTy} {τ : JsTy} : JsOpInlined σs τ → JsInline\n'
    for o in inl:
        ps = param_names(o)
        pat = ''.join(' ' + (p if p == 'k' else '_') for p in ps)
        s += f'  | .{o["name"]}{pat} => {tmpl_lean(o["impl"][1])}\n'
    s += '\nend JsOpInlined\n\nend MoreJs\n\nend\n'
    open(os.path.join(ROOT, 'JsTerm', 'OpsInlined.lean'), 'w').write(s)
    write_lookup(ops)

def param_names(o):
    """The explicit parameters of a constructor."""
    if o['poly'] == 'layout':
        return ['l']
    if o['poly'] in ('generic', 'elem'):
        return ['α']
    if o['poly'] == 'typed':
        return ['k', 'e']
    return []

def write_lookup(ops):
    by_ext = {}
    for o in ops:
        if o['extern']:
            by_ext.setdefault(o['extern'], []).append(o)
    s = '''module

public import JsTerm.OpsImported
public import JsTerm.OpsInlined

@[expose] public section

set_option autoImplicit false

/-!
# Finding the operation of an extern call

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOp.lookup name σs τ` is the operation of the extern `name` (as the catalogue spells it,
`lean_nat_div`) at the argument types `σs` and the result type `τ`, if there is one: the
constructor of `JsOpImported` or `JsOpInlined` whose signature is exactly `σs → τ` (a
polymorphic one instantiated from the types).
-/

namespace MoreJs

/-- An operation: one that calls the runtime, or one written inline. -/
inductive JsOp : List JsTy → JsTy → Type where
  | imported {σs : List JsTy} {τ : JsTy} (op : JsOpImported σs τ) : JsOp σs τ
  | inlined {σs : List JsTy} {τ : JsTy} (op : JsOpInlined σs τ) : JsOp σs τ

namespace JsOp

/-- The name of the operation. -/
def name {σs : List JsTy} {τ : JsTy} : JsOp σs τ → String
  | .imported op => op.name
  | .inlined op => op.name

/-- The operation at the signature `σs → τ`, if it is its own. -/
def ofSig {σs' : List JsTy} {τ' : JsTy} (op : JsOp σs' τ') (σs : List JsTy) (τ : JsTy) :
    Option (JsOp σs τ) :=
  if h : σs' = σs ∧ τ' = τ then some (h.1 ▸ h.2 ▸ op) else none

/-- The first operation of a list of candidates that has the signature `σs → τ`. -/
def firstOf (σs : List JsTy) (τ : JsTy) : List (Σ σs' τ', JsOp σs' τ') → Option (JsOp σs τ)
  | [] => none
  | ⟨_, _, op⟩ :: rest => (op.ofSig σs τ).orElse fun _ => firstOf σs τ rest

/-- The layout of the array among the argument types (the first one that is an array). -/
def layoutOf? : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => layoutOf? ts

'''
    names = sorted(by_ext)
    uses_sig = {}
    for ext in names:
        s += f'/-- The operations of `{ext}`. -/\n'
        items = []
        for o in by_ext[ext]:
            wrap = 'imported' if o['impl'][0] == 'import' else 'inlined'
            if o['poly'] is None:
                items.append(f'⟨_, _, .{wrap} .{o["name"]}⟩')
            elif o['poly'] == 'layout':
                items.append(f'(match layoutOf? (σs ++ [τ]) with | some ⟨_, _, l⟩ => [⟨_, _, .{wrap} (.{o["name"]} l)⟩] | none => [])')
            elif o['poly'] == 'elem':
                items.append(f'[⟨_, _, .{wrap} (.{o["name"]} (elemOf? (σs ++ [τ])))⟩]')
            elif o['poly'] == 'generic':
                items.append(f'(match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .generic α⟩ => [⟨_, _, .{wrap} (.{o["name"]} α)⟩] | _ => [])')
            elif o['poly'] == 'typed':
                items.append(f'(match layoutOf? (σs ++ [τ]) with | some ⟨_, _, .typed k e⟩ => [⟨_, _, .{wrap} (.{o["name"]} k e)⟩] | _ => [])')
        mono = [x for x in items if x.startswith('⟨')]
        rest = [x for x in items if not x.startswith('⟨')]
        uses_sig[ext] = bool(rest)
        expr = ' ++ '.join((['[' + ', '.join(mono) + ']'] if mono else []) + rest)
        if rest:
            s += f'def «cands_{ext}» (σs : List JsTy) (τ : JsTy) : List (Σ σs\' τ\', JsOp σs\' τ\') :=\n'
        else:
            s += f'def «cands_{ext}» : List (Σ σs\' τ\', JsOp σs\' τ\') :=\n'
        s += '  ' + expr + '\n\n'
    s += '''/-- The operation of the extern `name` at the signature `σs → τ`, if there is one. -/
def lookup (name : String) (σs : List JsTy) (τ : JsTy) : Option (JsOp σs τ) :=
  firstOf σs τ (match name with
'''
    for ext in names:
        s += f'    | "{ext}" => «cands_{ext}»' + (' σs τ' if uses_sig[ext] else '') + '\n'
    s += '''    | _ => [])

end JsOp

end MoreJs

end
'''
    # the element type of a thunk operation
    s = s.replace("def layoutOf?", '''def elemOf? : List JsTy → JsTy
  | [] => .terminal .bool
  | .thunk t :: _ => t
  | .lazy t :: _ => t
  | _ :: ts => elemOf? ts

/-- The layout of the array among the argument types (the first one that is an array). -/
def layoutOf?''', 1).replace("/-- The layout of the array among the argument types (the first one that is an array). -/\ndef elemOf?", "/-- The type a thunk operation delays (the first delay among the types). -/\ndef elemOf?", 1)
    open(os.path.join(ROOT, 'JsTerm', 'OpsLookup.lean'), 'w').write(s)

# --------------------------------------------------------------------- runtime output

def migrate_runtime(old_src, migrate):
    """Rewrite the merged runtime as one module exporting the imported operations."""
    sections = split_sections(old_src)
    parsed = {f: parse_decls(t) for f, t in sections}
    # which (section, function) each op uses
    wanted = {}
    for (opname, sec, fn, pre) in migrate:
        wanted.setdefault((sec, fn, spec_of(sec, pre)), []).append(opname)
    out = [RUNTIME_HEADER]
    helper_defs = {}   # name -> code (deduplicated)
    order = ['lean_runtime_non_configurable.mjs',
             'lean_runtime_nat_bigint.mjs', 'lean_runtime_nat_num.mjs',
             'lean_runtime_int_bigint.mjs', 'lean_runtime_int_num.mjs',
             'lean_runtime_uint64_bigint.mjs', 'lean_runtime_uint64_num.mjs',
             'lean_runtime_int64_bigint.mjs', 'lean_runtime_int64_num.mjs',
             'lean_runtime_bitvec_bigint.mjs', 'lean_runtime_bitvec_num.mjs']
    tag = lambda sec: sec.replace('lean_runtime_', '').replace('.mjs', '')
    body_parts = []
    for sec in order:
        decls = parsed[sec]
        byname = {}
        for d in decls:
            byname.setdefault(d['name'], d)
        # the renaming of this section: helpers keep their names unless another section
        # defines them differently; exported functions become the ops that use them
        rename = {}
        for d in decls:
            if not d['exported']:
                code = d['code']
                nm = d['name']
                if nm in helper_defs and helper_defs[nm] != code:
                    rename[nm] = f'{nm}_{tag(sec)}'
                    helper_defs[rename[nm]] = code
                else:
                    helper_defs[nm] = code
        emitted = []
        needed_private = set()
        for (s2, fn, spec), opnames in wanted.items():
            if s2 != sec:
                continue
            emitted.append((fn, spec, opnames))
        # exported functions referenced by emitted functions but not emitted themselves
        emitted_fns = {(fn, spec) for fn, spec, _ in emitted}
        def refs(code):
            return {d2['name'] for d2 in decls if d2['exported'] and ident_re(d2['name']).search(code.split('=', 1)[1] if '=' in code else code)}
        # the name each exported function is emitted under (the first op, unspecialised)
        main_name = {}
        for fn, spec, opnames in emitted:
            main_name.setdefault(fn, sorted(opnames)[0] if spec == 'plain' else None)
        private = {}
        todo = []
        for fn, spec, opnames in emitted:
            d = byname[fn]
            todo.extend(refs(d['code']) - {fn})
        while todo:
            r = todo.pop()
            if r in private or (main_name.get(r)):
                continue
            private[r] = f'{tag(sec)}{r}' if not r.startswith('$') else f'{tag(sec)}_{r[1:]}'
            todo.extend(refs(byname[r]['code']) - {r})
        def rewrite(code, own_name):
            # rename the declaration and the references in it
            for nm, new in list(rename.items()):
                code = ident_re(nm).sub(new, code)
            head, _, rest = code.partition('=')
            for fn2, new in list(private.items()):
                rest = ident_re(fn2).sub(new, rest)
            for fn2, new in main_name.items():
                if new:
                    rest = ident_re(fn2).sub(new, rest)
            m = DECL_RE.match(head)
            head = f'export const {own_name} ' if own_name else head
            return head + '=' + rest
        part = [f'/* {"-" * 60} {tag(sec)} */', '']
        for r, new in sorted(private.items()):
            d = byname[r]
            code = rewrite(d['code'], None)
            code = re.sub(r'^export const [\w$]+ ', f'const {new} ', code)
            if d['doc']:
                part.append(d['doc'])
            part.append(code)
            part.append('')
        for fn, spec, opnames in sorted(emitted, key=lambda x: sorted(x[2])[0]):
            d = byname[fn]
            opnames = sorted(opnames)
            first = opnames[0]
            code = rewrite(d['code'], first)
            code = specialise(code, spec)
            if d['doc']:
                part.append(d['doc'])
            part.append(code)
            for other in opnames[1:]:
                part.append(f'export const {other} = {first};')
            part.append('')
        body_parts.append((sec, part))
    # helpers used anywhere
    all_text = '\n'.join('\n'.join(p) for _, p in body_parts)
    helpers = []
    for nm, code in helper_defs.items():
        pass
    # emit only the helpers referenced (transitively)
    used = set()
    changed = True
    texts = all_text
    while changed:
        changed = False
        for nm, code in helper_defs.items():
            if nm not in used and ident_re(nm).search(texts):
                used.add(nm)
                texts += '\n' + code
                changed = True
    for sec in order:
        for d in parsed[sec]:
            if not d['exported']:
                nm = d['name']
                code = d['code']
                # the helper, under its (possibly renamed) name
                for key, c in helper_defs.items():
                    if c == code and key in used and key not in [h[0] for h in helpers]:
                        c2 = re.sub(r'^const [\w$]+ ', f'const {key} ', c)
                        helpers.append((key, (d['doc'] + '\n' if d['doc'] else '') + c2))
    out.append('/* ' + '-' * 60 + ' private helpers */\n')
    for _, c in helpers:
        out.append(c + '\n')
    for sec, part in body_parts:
        out.append('\n'.join(part))
    out.append(EXTRA_RUNTIME)
    return '\n'.join(out)

def spec_of(sec, pre):
    """How a function of the non-configurable module is specialised to the representation of
    the index or count it takes: `uint53` reads it as it is, `bigint_nat` converts it."""
    if sec == 'lean_runtime_non_configurable.mjs' and pre in ('uint53', 'bigint_nat'):
        return pre
    return 'plain'

def specialise(code, spec):
    if spec == 'uint53':
        code = re.sub(r'\$idx\((\w+)\)', r'\1', code)
        code = re.sub(r'\$count\((\w+)\)', r'\1', code)
    return code

RUNTIME_HEADER = '''// The runtime of the JavaScript that LeanScript generates: one module.
//
// Every function exported here is an operation of `JsTerm/OpsImported.lean`, of the same
// name: the name of the extern it implements, behind the JavaScript representation of its
// arguments and result (`bigint_nat__lean_nat_div` on `BigInt`s, `uint53__lean_nat_div`
// on numbers below 2^53; see `scripts/gen_js_ops.py` for the naming).  A generated module
// imports the operations it calls.  The operations that are one JavaScript operator are
// not here: they are written inline (`JsTerm/OpsInlined.lean`).
//
// Every function is pure (it never mutates an argument), except the `_inplace` array
// updates, which the backend calls only on an array nothing else refers to.
'''

EXTRA_RUNTIME = '''
/* ------------------------------------------------------------ missing externs */

/** Called in place of an extern that has no JavaScript implementation yet. */
export const lean_extern_unimplemented = (name) => {
  throw new Error(`LeanScript: the extern ${name} has no JavaScript implementation yet`);
};
'''

# The operations whose old runtime function was one operator (found when the runtime was
# migrated, `--migrate-runtime`), kept in `scripts/js_ops_inline.json`.
INLINE_JSON = os.path.join(ROOT, 'scripts', 'js_ops_inline.json')
INLINE_TABLE = {}
REPORT = None

def load_inline():
    import json
    if os.path.exists(INLINE_JSON):
        for k, v in json.load(open(INLINE_JSON)).items():
            INLINE_TABLE[k] = decode(v)

def encode(t):
    if isinstance(t, tuple):
        return [encode(x) for x in t]
    if isinstance(t, list):
        return ['__list__'] + [encode(x) for x in t]
    return t

def decode(v):
    if isinstance(v, list):
        if v and v[0] == '__list__':
            return [decode(x) for x in v[1:]]
        return tuple(decode(x) for x in v)
    return v

def runtime_exports():
    try:
        src = open(RUNTIME).read()
    except FileNotFoundError:
        return set()
    return set(re.findall(r'^export const ([\w$]+)', src, re.M))

def main():
    if len(sys.argv) >= 3 and sys.argv[1] == '--migrate-runtime':
        old = open(sys.argv[2]).read()
        sections = {f: {d['name']: d for d in reversed(parse_decls(t))} for f, t in split_sections(old)}
        ops, migrate = build_ops(set(), sections)
        new = migrate_runtime(old, migrate)
        open(RUNTIME, 'w').write(new)
        import json
        json.dump({k: encode(v) for k, v in sorted(INLINE_TABLE.items())}, open(INLINE_JSON, 'w'), indent=0)
        return
    load_inline()
    if len(sys.argv) >= 2 and sys.argv[1] == '--report':
        global REPORT
        REPORT = []
        build_ops(runtime_exports())
        for r in REPORT:
            print(r)
        return
    ops, _ = build_ops(runtime_exports())
    write_lean(ops)
    print(f'{len([o for o in ops if o["impl"][0] == "import"])} imported, '
          f'{len([o for o in ops if o["impl"][0] == "inline"])} inlined')

if __name__ == '__main__':
    main()
