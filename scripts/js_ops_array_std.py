"""The operations of the externs of `ArrayStdExtern`, for `scripts/gen_js_ops.py`.

The family `ArrayStdExtern`
(`LeanScript/LeanInitPureExterns/ArrayStdFunctionsNonExternButBigEnoughToLoseInformation.lean`)
holds the array functions of `Init` written in Lean (`Array.append`, `Array.map`, …).  Their
signatures have several type variables (`Array.map : (α → β) → Array α → Array β`) and several
arrays, each of which may be a generic or a typed array (`JsArrayLayout`), so they do not fit
the one-variable scheme `gen_js_ops.py` derives from the catalogue; they are listed here by
hand, with their candidates for the lookup (`JsTerm/Ops/Cands/ArrayStd.lean`).

Every array *argument* is layout-polymorphic (a `JsArrayLayout` parameter: the function of
`runtime.js` reads generic and typed arrays alike).  An array *result* whose layout is not the
one of an argument (`Array.map`, `Array.flatMap`, `Array.flatten`, `Array.zipWith`) comes as a
generic operation (`array__…`, an element-type parameter) and a typed one (`typedArray__…`, a
`JsTypedElem` parameter), which takes the constructor of the typed array as its first argument
(`JsOpImported.extraArgs`).  An index or a count is a `Nat`, so those operations come in a
`bigint_nat__…` and a `uint53__…` version.

Each operation is `(name, extern, lean, params, args, res)`, plus `ctorArg=True` for the typed
results and `mutableOf=` for the in-place version of an update; `gen_js_ops.py` adds the effects
(`effectful` for `…_mutable`) and whether it may throw (read off `runtime.js`).
"""

L1 = '{A E : JsTy} → (l : JsArrayLayout A E)'
L2 = '{A E B F : JsTy} → (l₁ : JsArrayLayout A E) → (l₂ : JsArrayLayout B F)'
NATS = [('bigint_nat', '(.terminal .bigint_nat)'), ('uint53', '(.terminal .uint53)')]
BOOL = '(.terminal .bool)'


def opt(t):
    return f'(.obj (.union [0, 1] .cells) [{t}])'


def ops():
    """The operations, as dicts."""
    out = []

    def op(name, extern, lean, params, args, res, **kw):
        out.append(dict(name=name, extern=extern, lean=lean, params=params, args=args, res=res,
                        **kw))

    op('array__lean_array_append_immutable', 'lean_array_append', 'Array.append', L1,
       ['A', 'A'], 'A')
    op('array__lean_array_append_mutable', None, 'Array.append', L1, ['A', 'A'], 'A',
       mutableOf='array__lean_array_append_immutable')
    op('array__lean_array_map', 'lean_array_map', 'Array.map', L1 + ' → (β : JsTy)',
       ['(.fn [E] β)', 'A'], '(.array β)')
    op('typedArray__lean_array_map', 'lean_array_map', 'Array.map', L1 + ' → (t : JsTypedElem)',
       ['(.fn [E] (.terminal t.leaf))', 'A'], '(.typedArray t)', ctorArg='t')
    op('array__lean_array_flat_map', 'lean_array_flat_map', 'Array.flatMap', L1 + ' → (β : JsTy)',
       ['(.fn [E] (.array β))', 'A'], '(.array β)')
    op('typedArray__lean_array_flat_map', 'lean_array_flat_map', 'Array.flatMap',
       L1 + ' → (t : JsTypedElem)', ['(.fn [E] (.typedArray t))', 'A'], '(.typedArray t)',
       ctorArg='t')
    op('array__lean_array_flatten', 'lean_array_flatten', 'Array.flatten', '(β : JsTy)',
       ['(.array (.array β))'], '(.array β)')
    op('typedArray__lean_array_flatten', 'lean_array_flatten', 'Array.flatten', '(t : JsTypedElem)',
       ['(.array (.typedArray t))'], '(.typedArray t)', ctorArg='t')
    op('array__lean_array_reverse', 'lean_array_reverse', 'Array.reverse', L1, ['A'], 'A')
    op('array__lean_array_contains', 'lean_array_contains', 'Array.contains', L1,
       [f'(.fn [E, E] {BOOL})', 'A', 'E'], BOOL)
    op('array__lean_array_find_opt', 'lean_array_find_opt', 'Array.find?', L1,
       [f'(.fn [E] {BOOL})', 'A'], opt('E'))
    op('array__lean_array_zip_with', 'lean_array_zip_with', 'Array.zipWith', L2 + ' → (γ : JsTy)',
       ['(.fn [E, F] γ)', 'A', 'B'], '(.array γ)')
    op('typedArray__lean_array_zip_with', 'lean_array_zip_with', 'Array.zipWith',
       L2 + ' → (t : JsTypedElem)', ['(.fn [E, F] (.terminal t.leaf))', 'A', 'B'],
       '(.typedArray t)', ctorArg='t')
    op('array__lean_array_zip', 'lean_array_zip', 'Array.zip', L2, ['A', 'B'],
       '(.array (.obj (.record 2) [E, F]))')
    op('array__lean_array_back_opt', 'lean_array_back_opt', 'Array.back?', L1, ['A'], opt('E'))
    for pre, n in NATS:
        op(f'{pre}__lean_array_filter', 'lean_array_filter', 'Array.filter', L1,
           [f'(.fn [E] {BOOL})', 'A', n, n], 'A')
        op(f'{pre}__lean_array_extract', 'lean_array_extract', 'Array.extract', L1, ['A', n, n], 'A')
        op(f'{pre}__lean_array_any', 'lean_array_any', 'Array.any', L1,
           ['A', f'(.fn [E] {BOOL})', n, n], BOOL)
        op(f'{pre}__lean_array_all', 'lean_array_all', 'Array.all', L1,
           ['A', f'(.fn [E] {BOOL})', n, n], BOOL)
        op(f'{pre}__lean_array_find_idx_opt', 'lean_array_find_idx_opt', 'Array.findIdx?', L1,
           [f'(.fn [E] {BOOL})', 'A'], opt(n))
        op(f'{pre}__lean_array_idx_of_opt', 'lean_array_idx_of_opt', 'Array.idxOf?', L1,
           [f'(.fn [E, E] {BOOL})', 'A', 'E'], opt(n))
        op(f'{pre}__lean_array_erase_idx', 'lean_array_erase_idx', 'Array.eraseIdx!', L1,
           ['A', n], 'A')
        op(f'{pre}__lean_array_insert_idx', 'lean_array_insert_idx', 'Array.insertIdx!', L1,
           ['A', n, 'E'], 'A')
        op(f'{pre}__lean_array_erase_idx_if_in_bounds', 'lean_array_erase_idx_if_in_bounds',
           'Array.eraseIdxIfInBounds', L1, ['A', n], 'A')
        op(f'{pre}__lean_array_insert_idx_if_in_bounds', 'lean_array_insert_idx_if_in_bounds',
           'Array.insertIdxIfInBounds', L1, ['A', n, 'E'], 'A')
        op(f'{pre}__lean_array_qsort', 'lean_array_qsort', 'Array.qsort', L1,
           ['A', f'(.fn [E, E] {BOOL})', n, n], 'A')
        op(f'{pre}__lean_array_foldr', 'lean_array_foldr', 'Array.foldr', L1 + ' → (β : JsTy)',
           ['(.fn [E, β] β)', 'β', 'A', n, n], 'β')
        op(f'{pre}__lean_array_count_p', 'lean_array_count_p', 'Array.countP', L1,
           [f'(.fn [E] {BOOL})', 'A'], n)
    op('list__lean_list_append', 'lean_list_append', 'List.append', '(α : JsTy)',
       ['(.list α)', '(.list α)'], '(.list α)')
    op('consList__lean_list_append', 'lean_list_append', 'List.append', '(α : JsTy)',
       ['(.obj .consList [α])', '(.obj .consList [α])'], '(.obj .consList [α])')
    return out


def c(name, *args):
    """A candidate of the operation `name` applied to `args`."""
    a = ' '.join(args)
    return f'⟨_, _, _, _, .imported (.{name}{" " + a if a else ""})⟩'


def nat_pair(ext, *args):
    return '[' + ', '.join(c(f'{pre}__{ext}', *args) for pre, _ in NATS) + ']'


def at1(i, body):
    """The candidates, from the layout `l` of argument `i`."""
    return f'match layoutAt? σs {i} with\n  | some ⟨_, _, l⟩ => {body}\n  | none => []'


def split_res(i, gen, typ, extra=''):
    """The candidates of an operation whose array result may be generic or typed."""
    return (f'match layoutAt? σs {i}, layoutOf? [τ] with\n'
            f'  | some ⟨_, _, l⟩, some ⟨_, _, .generic β⟩ => [{c(gen, "l", extra, "β").replace("  ", " ")}]\n'
            f'  | some ⟨_, _, l⟩, some ⟨_, _, .typed t⟩ => [{c(typ, "l", extra, "t").replace("  ", " ")}]\n'
            f'  | _, _ => []')


# The Lean body of the candidates of every extern of the family, over `σs` and `τ`.
CANDS = {
    'lean_array_append': at1(0, '[' + c('array__lean_array_append_immutable', 'l') + ']'),
    'lean_array_map': split_res(1, 'array__lean_array_map', 'typedArray__lean_array_map'),
    'lean_array_filter': at1(1, nat_pair('lean_array_filter', 'l')),
    'lean_array_flat_map': split_res(1, 'array__lean_array_flat_map',
                                     'typedArray__lean_array_flat_map'),
    'lean_array_flatten': ('match layoutOf? [τ] with\n'
                           f'  | some ⟨_, _, .generic β⟩ => [{c("array__lean_array_flatten", "β")}]\n'
                           f'  | some ⟨_, _, .typed t⟩ => [{c("typedArray__lean_array_flatten", "t")}]\n'
                           '  | none => []'),
    'lean_array_reverse': at1(0, '[' + c('array__lean_array_reverse', 'l') + ']'),
    'lean_array_extract': at1(0, nat_pair('lean_array_extract', 'l')),
    'lean_array_any': at1(0, nat_pair('lean_array_any', 'l')),
    'lean_array_all': at1(0, nat_pair('lean_array_all', 'l')),
    'lean_array_contains': at1(1, '[' + c('array__lean_array_contains', 'l') + ']'),
    'lean_array_find_opt': at1(1, '[' + c('array__lean_array_find_opt', 'l') + ']'),
    'lean_array_find_idx_opt': at1(1, nat_pair('lean_array_find_idx_opt', 'l')),
    'lean_array_idx_of_opt': at1(1, nat_pair('lean_array_idx_of_opt', 'l')),
    'lean_array_erase_idx': at1(0, nat_pair('lean_array_erase_idx', 'l')),
    'lean_array_insert_idx': at1(0, nat_pair('lean_array_insert_idx', 'l')),
    'lean_array_erase_idx_if_in_bounds': at1(0, nat_pair('lean_array_erase_idx_if_in_bounds', 'l')),
    'lean_array_insert_idx_if_in_bounds': at1(0, nat_pair('lean_array_insert_idx_if_in_bounds', 'l')),
    'lean_array_qsort': at1(0, nat_pair('lean_array_qsort', 'l')),
    'lean_array_foldr': at1(2, nat_pair('lean_array_foldr', 'l', 'τ')),
    'lean_array_zip_with': ('match layoutAt? σs 1, layoutAt? σs 2, layoutOf? [τ] with\n'
                            '  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩, some ⟨_, _, .generic γ⟩ => ['
                            + c('array__lean_array_zip_with', 'l₁', 'l₂', 'γ') + ']\n'
                            '  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩, some ⟨_, _, .typed t⟩ => ['
                            + c('typedArray__lean_array_zip_with', 'l₁', 'l₂', 't') + ']\n'
                            '  | _, _, _ => []'),
    'lean_array_zip': ('match layoutAt? σs 0, layoutAt? σs 1 with\n'
                       '  | some ⟨_, _, l₁⟩, some ⟨_, _, l₂⟩ => ['
                       + c('array__lean_array_zip', 'l₁', 'l₂') + ']\n'
                       '  | _, _ => []'),
    'lean_array_back_opt': at1(0, '[' + c('array__lean_array_back_opt', 'l') + ']'),
    'lean_array_count_p': at1(1, nat_pair('lean_array_count_p', 'l')),
    'lean_list_append': ('match τ with\n'
                         f'  | .list α => [{c("list__lean_list_append", "α")}]\n'
                         f'  | .obj .consList [α] => [{c("consList__lean_list_append", "α")}]\n'
                         '  | _ => []'),
}

HELPERS = '''/-- The layout of argument `i` among the types `σs`, when it is an array. -/
def layoutAt? (σs : List JsTy) (i : Nat) : Option (Σ a e, JsArrayLayout a e) :=
  match σs[i]? with
  | some t => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => none
  | none => none

'''
