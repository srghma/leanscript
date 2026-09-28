#!/usr/bin/env python3
"""Write the types of the arguments and of the result of every operation of `runtime.js` in
the comment on top of it.

    python3 scripts/annotate_runtime.py           # rewrite runtime.js
    python3 scripts/annotate_runtime.py --check   # exit 1 (changing nothing) if it is not up to date

The types come from the signatures of the operations (`JsOpImported` in `JsTerm/Ops.lean`), as
`scripts/gen_js_ops.py` computes them from the catalogue of externs, so they are the types the
backend calls the function at.  Every exported function of `runtime.js` gets JSDoc tags after
its description:

    /** `Nat.div`.
     *  @param {bigint} a `bigint_nat`
     *  @param {bigint} b `bigint_nat`
     *  @returns {bigint} `bigint_nat` */

the JavaScript type of the value in braces, then its `JsTy` (the representation, which says
more than the JavaScript type: a `uint53` and an `int16` are both `number`s).  A polymorphic
operation gets a `@template` line for its type parameters (`α`, the array layout `A`/`E`, the
typed-array element `t`).  An alias (`export const a = b;`) gets the types of its own signature
and the parameter names of `b`.

The tags are the only lines the script writes: it removes the ones it wrote before, so it can
be run again after an edit of `runtime.js` or of the catalogue.  The private helpers (`$…`) have
no signature in `JsTerm/Ops.lean` and are left as they are.
"""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_js_ops as g  # noqa: E402

RUNTIME = g.RUNTIME

# ------------------------------------------------------------------ the `JsTy`s of Ops.lean

def tokenize(s):
    return re.findall(r'\(|\)|\[|\]|,|[^\s()\[\],]+', s)

def parse(s):
    """A `JsTy` written as in `JsTerm/Ops.lean` (`(.terminal .bigint_nat)`, `(.array α)`, `A`, …),
    as a tuple."""
    toks = tokenize(s)
    t, i = parse_at(toks, 0)
    assert i == len(toks), (s, toks[i:])
    return t

def parse_list(toks, i):
    assert toks[i] == '['
    i += 1
    out = []
    while toks[i] != ']':
        if toks[i] == ',':
            i += 1
            continue
        t, i = parse_at(toks, i)
        out.append(t)
    return out, i + 1

def parse_at(toks, i):
    tok = toks[i]
    if tok == '[':
        return parse_list(toks, i)
    if tok != '(':
        return ('var', tok), i + 1
    head = toks[i + 1]
    i += 2
    if head == '.terminal':
        if toks[i] == '(':
            # a leaf with parameters: `(.bitvec_small 8 (by decide) (by decide))`, …
            kind, n = toks[i + 1].lstrip('.'), toks[i + 2]
            depth, j = 0, i
            while True:
                depth += {'(': 1, ')': -1}.get(toks[j], 0)
                j += 1
                if depth == 0:
                    break
            leaf = g.leaf_name((kind, int(n)))
            i = j
        else:
            leaf = toks[i].lstrip('.')
            i += 1
        assert toks[i] == ')'
        return ('leaf', leaf), i + 1
    if head in ('.array', '.list', '.thunk'):
        a, i = parse_at(toks, i)
        assert toks[i] == ')'
        return (head[1:], a), i + 1
    if head == '.typedArray':
        v = toks[i]
        assert toks[i + 1] == ')'
        return ('typedArray', v), i + 2
    if head == '.fn':
        doms, i = parse_list(toks, i)
        cod, i = parse_at(toks, i)
        assert toks[i] == ')'
        return ('fn', doms, cod), i + 1
    if head == '.record':
        f1, i = parse_at(toks, i)
        f2, i = parse_at(toks, i)
        fs, i = parse_list(toks, i)
        assert toks[i] == ')'
        return ('record', [f1, f2] + fs), i + 1
    if head == '.union':
        c0, i = parse_list(toks, i)
        c1, i = parse_list(toks, i)
        cs, i = parse_list(toks, i)
        assert toks[i] == ')'
        return ('union', [c0, c1] + cs), i + 1
    if head == '.enum':
        n = toks[i]
        i += 1
        if toks[i] == '(':
            shift = toks[i + 1]
            i += 3
        else:
            shift = toks[i]
            i += 1
        assert toks[i] == ')'
        return ('enum', int(n), int(shift)), i + 1
    raise ValueError(f'unknown JsTy constructor {head}')

# ------------------------------------------------------------------------- rendering

NUMBER_LEAVES = {'uint53', 'int53', 'uint8', 'uint16', 'uint32', 'int8', 'int16', 'int32',
                 'float', 'float32'}

def js_leaf(l):
    """The JavaScript type of a leaf."""
    if l == 'bool':
        return 'boolean'
    if l == 'string':
        return 'string'
    if l in ('substring', 'stringSlice'):
        return '[string, number, number]'
    if l == 't.leaf':
        return 'number|bigint'
    if l.startswith('bigint_'):
        return 'bigint'
    if l in NUMBER_LEAVES or l.startswith('bitvec') or l.startswith('int53_bitvec'):
        return 'number'
    raise ValueError(f'unknown leaf {l}')

def js(t):
    """The JavaScript type of a `JsTy` (a JSDoc / Closure type expression)."""
    k = t[0]
    if k == 'leaf':
        return js_leaf(t[1])
    if k == 'var':
        return {'A': 'Array<E>|TypedArray'}.get(t[1], t[1])
    if k in ('array', 'list'):
        return f'Array<{js(t[1])}>'
    if k == 'typedArray':
        return 'TypedArray'
    if k == 'thunk':
        return f'Thunk<{js(t[1])}>'
    if k == 'fn':
        return f'function({", ".join(js(a) for a in t[1])}): {js(t[2])}'
    if k == 'record':
        return '{' + ', '.join(f'_{i + 1}: {js(f)}' for i, f in enumerate(t[1])) + '}'
    if k == 'union':
        alts = []
        for i, c in enumerate(t[1]):
            alts.append('{' + ', '.join([f'tag: {i}'] + [f'_{j + 1}: {js(f)}' for j, f in enumerate(c)]) + '}')
        return '(' + '|'.join(alts) + ')'
    if k == 'enum':
        return 'number'
    raise ValueError(t)

def rep(t, top=True):
    """A `JsTy` in the notation of `JsTerm/Ty.lean`, without the dots (`array bigint_nat`)."""
    k = t[0]
    if k in ('leaf', 'var'):
        return t[1]
    lst = lambda ts: '[' + ', '.join(rep(a) for a in ts) + ']'
    if k in ('array', 'list', 'thunk'):
        s = f'{k} {rep(t[1], False)}'
    elif k == 'typedArray':
        s = f'typedArray {t[1]}'
    elif k == 'fn':
        s = f'fn {lst(t[1])} {rep(t[2], False)}'
    elif k == 'record':
        s = f'record {rep(t[1][0], False)} {rep(t[1][1], False)} {lst(t[1][2:])}'
    elif k == 'union':
        s = f'union {lst(t[1][0])} {lst(t[1][1])} [' + ', '.join(lst(c) for c in t[1][2:]) + ']'
    elif k == 'enum':
        s = f'enum {t[1]} ({t[2]})' if t[2] < 0 else f'enum {t[1]} {t[2]}'
    else:
        raise ValueError(t)
    return s if top else f'({s})'

TEMPLATES = {
    'layout': '@template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or '
              '`typedArray t` with `E` = `terminal t.leaf`',
    'generic': '@template α the element type',
    'elem': '@template α the delayed type',
    'typed': '@template t the typed-array element (`JsTypedElem`); `TypedArray` is `t.kind`',
}

def tags(op, params):
    """The JSDoc lines of an operation whose JavaScript parameters are `params`."""
    args = [parse(a) for a in op['args']]
    res = parse(op['res'])
    out = []
    if op['poly'] in TEMPLATES:
        out.append(TEMPLATES[op['poly']])
    lead = []
    if op.get('ctorArg'):
        # the typed-array constructor, which the backend passes first (`new C(n)`)
        lead = [('function(new:TypedArray, number)', '`t.kind` (the typed-array constructor)')]
    shown = lead + [(js(a), f'`{rep(a)}`') for a in args]
    if len(shown) != len(params):
        raise ValueError(f'{op["name"]}: {len(params)} parameters in runtime.js, '
                         f'{len(shown)} in its signature')
    for p, (jt, r) in zip(params, shown):
        out.append(f'@param {{{jt}}} {p} {r}')
    out.append(f'@returns {{{js(res)}}} `{rep(res)}`')
    return out

# ---------------------------------------------------------------------------- runtime.js

EXPORT_RE = re.compile(r'^export const ([\w$]+) = (.*)$')
TAG_RE = re.compile(r'^ \*  @(param|returns|template) ')

def js_params(rhs):
    """The parameter names of an arrow function, from the text after `=`; `None` if it is
    not one."""
    m = re.match(r'\(([^()]*)\)\s*=>', rhs)
    if m:
        return [p.strip() for p in m.group(1).split(',') if p.strip()]
    m = re.match(r'([\w$]+)\s*=>', rhs)
    if m:
        return [m.group(1)]
    return None

def strip_tags(doc):
    """A doc comment (a list of lines) without the tags this script wrote."""
    lines = [l for l in doc if not TAG_RE.match(l)]
    last = lines[-1]
    if not last.rstrip().endswith('*/'):
        # the closing `*/` was on a tag line
        lines[-1] = last.rstrip() + ' */'
    return lines

def with_tags(doc, ts):
    """A doc comment with the tags `ts` at its end."""
    if not doc:
        return ['/**'] + [f' *  {t}' for t in ts[:-1]] + [f' *  {ts[-1]} */']
    body = doc[:-1] + [re.sub(r'\s*\*/\s*$', '', doc[-1])]
    if body[-1].strip() in ('', '*'):
        body = body[:-1]
    return body + [f' *  {t}' for t in ts[:-1]] + [f' *  {ts[-1]} */']

def annotate(text, ops):
    byname = {g.js_name(o['name']): o for o in ops if o['impl'][0] == 'import'}
    lines = text.split('\n')
    # the parameters of every exported function (an alias gets those of its target)
    params, alias = {}, {}
    for l in lines:
        m = EXPORT_RE.match(l)
        if m:
            p = js_params(m.group(2))
            if p is not None:
                params[m.group(1)] = p
            else:
                a = re.match(r'([\w$]+);$', m.group(2))
                if a:
                    alias[m.group(1)] = a.group(1)
    for a, b in alias.items():
        if b in params:
            params[a] = params[b]
    out = []
    done, skipped = 0, []
    i = 0
    while i < len(lines):
        l = lines[i]
        m = EXPORT_RE.match(l)
        if not m:
            out.append(l)
            i += 1
            continue
        name = m.group(1)
        # the doc comment right above, if any, already in `out`
        doc = []
        if out and out[-1].rstrip().endswith('*/'):
            j = len(out) - 1
            while not out[j].lstrip().startswith('/*'):
                j -= 1
            if out[j].startswith('/**'):
                doc = out[j:]
                del out[j:]
        if name in byname and name in params:
            doc = with_tags(strip_tags(doc) if doc else [], tags(byname[name], params[name]))
            done += 1
        else:
            skipped.append(name)
            if doc:
                doc = strip_tags(doc)
        out.extend(doc)
        out.append(l)
        i += 1
    return '\n'.join(out), done, skipped

def main():
    g.load_inline()
    ops, missing = g.build_ops(g.runtime_info())
    text = open(RUNTIME).read()
    new, done, skipped = annotate(text, ops)
    for s in skipped:
        print(f'warning: no signature for the exported {s}', file=sys.stderr)
    if len(sys.argv) >= 2 and sys.argv[1] == '--check':
        if new != text:
            print('runtime.js: the type comments are not up to date '
                  '(run python3 scripts/annotate_runtime.py)', file=sys.stderr)
            sys.exit(1)
        print(f'runtime.js: the type comments of {done} functions are up to date')
        return
    if new != text:
        open(RUNTIME, 'w').write(new)
    print(f'runtime.js: type comments on {done} functions')

if __name__ == '__main__':
    main()
