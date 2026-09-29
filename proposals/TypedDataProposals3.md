# Typing `JsTy.data`, part 3: nominal object types, parameters, canonical layouts

```lean
/-- A declared datatype, by name (`D<block>_<member>`). -/
| data (name : String)          -- JsTerm/Ty/Defs.lean
```

This is the third note on the question. Part 1 (`proposals/TypedDataProposals.md`) and part 2
(`proposals/TypedDataProposals2.md`) already cover: a checked global index, cast nodes with views,
a layout proof as a field, the signature as a parameter, an equi-recursive `μ` (rejected), types
of expressions in head form (part 2's B), self-contained blocks, instance-found layout proofs,
pass counters, and the `List` = `MyList` differential test. **This note only adds designs that are
not in those two.** Each section ends with what it keeps and what it costs.

The code for this note is a toy model, `proposals/TypedDataNodeToy.lean`, of Proposals P and Q
together. It is not part of the Lake build. It checks with
`lake env lean proposals/TypedDataNodeToy.lean` with no errors, no warnings and no `sorry`, and
its theorem `Expr.knownCtor_eval` depends only on `propext`. **Nothing in `JsTerm` was
changed.**

---

## 0. Facts from the current tree that these designs rely on

- `lowerTy` maps `Ty.data r` to `.data (refName r)`, where `refName` writes `D<depth>_<j>` from
  the **relative** de Bruijn depth of `r` (`JsTerm/Ty/Lower.lean`). The same datatype can get
  different names in different scopes, and different datatypes can get the same name.
- The Term-level datatypes (`LeanScript/Ty/Syntax/Ty.lean`) are **monomorphic**. A block has no
  type parameters, so a `List Nat` and a `List String` declared by the user become two unrelated
  blocks.
- **The passes never build an object type. They only match object types.** Searching
  `JsTerm/Passes` for `.union ` / `.record ` finds just one pattern in `Unbox.lean`
  (`letMut (τ := .union _ _ _) x (.union_mk ix args) rest`) and the two cases of `shareFree` in
  `InPlace/Linear.lean`. Object types are created only in `JsTerm/Ty/Lower.lean`,
  `JsTerm/Lower/Basic.lean`, `JsTerm/Lower/Extern.lean` and in five signatures of
  `JsTerm/Ops/Imported.lean`: `Option String` (a `.union [] [string] []`) and the four
  `frexp` pairs (`.record …`). This fact is what makes Proposal P cheap: changing the
  representation of object types does not touch pass logic, only the indices of the patterns.
- The four forms the optimisations look for are `union_mk`, `unionCases`, `record_mk` and
  `destructure`. Part 2 counted 114 matches on them in `JsTerm/Passes` and `JsTerm/Print`.
  Optimisations get lost when a datatype value stops looking like one of these four forms.

---

## Proposal P ★: every tagged-object type is a name (nominal object types)

Part 1 and part 2 both try to make `data` **look like** `union`. P goes the other way: it
removes the structural `union` / `record` from the types of expressions, so that **every** tagged
object is a name in the module's table:

```lean
inductive JsTy where
  | terminal (t : JsTerminalTy) | array (elem : JsTy) | typedArray (e : JsTypedElem)
  | list (elem : JsTy) | fn (doms : List JsTy) (cod : JsTy) | enum (n : Nat) (shift : Int)
  | thunk (t : JsTy)
  | obj (n : Nat) (args : List JsTy)   -- replaces `record`, `union`, `data` and `consList`

inductive JsDecl                       -- a row of the table; fields are `PTy` (see Q)
  | record (f₁ f₂ : PTy) (fs : List PTy)
  | union  (c₀ c₁ : List PTy) (cs : List (List PTy))
structure JsSig where decls : Array JsDecl    -- a *parameter* of `JsExpr` / `JsBlock`
```

A structural union from the source, such as `Nat ⊕ String`, becomes an **anonymous
non-recursive declaration**. A declared datatype becomes a declaration that may be recursive.
Both are built and matched by the same forms, and those forms share **one index**:

```lean
| union_mk (ix : JsMem (Σ.ctorsOf n args) fs) (args : JsArgs C M fs) : JsExpr C M (.obj n args)
| unionCases (e : JsExpr C M (.obj n args)) (arms : JsUnionArms C M J k (Σ.ctorsOf n args))
| record_mk (args : JsArgs C M (Σ.fieldsOf n args)) : JsExpr C M (.obj n args)
| destructure (e : JsExpr C M (.obj n args)) (sel : JsSel (Σ.fieldsOf n args) us) …
```

**Why no optimisation is lost.**

- A pattern such as `unionCases (union_mk ix args) arms` still has the same shape. The node and
  the arms are at the same `obj n args`, so the constructor list that `ix` points into **is** the
  list the arms are indexed by. The case-of-known-constructor rewrite needs no cast, no proof
  field and no `▸`. The toy writes it as `| .case (.mk ix as) arms => .lets as (arms.pick ix)`
  and proves `Expr.knownCtor_eval`.
- No value has two types. Part 2's B has to keep a "head form" discipline: every binder must
  unfold `data` one level, and a value still typed `data r` is rejected. In P a value of
  `List Nat` has exactly one type, `obj List [nat]`, both at the binder and inside the fields.
  Nothing is unfolded, so nothing can be forgotten.
- `Hoist` still sees `{ tag: 0 }` as a `union_mk` with no arguments. So `$tag0` sharing, and
  sharing of whole literals, work for every declaration, recursive ones included.
- The pass code does not change, because the passes never build object types (§0). A pass
  that rebuilds a node reuses `ix` and `args` without changing their indices.

**Why it is sound.**

- There is nothing to unfold and nothing to substitute under a binder. Type equality is
  syntactic: a `Nat` and a list of arguments. The hand-written `JsTerm/Ty/DecEq.lean` gets
  smaller, since three large cases (`record`, `union`, `data`) become one small case.
- A value of one declaration cannot be passed where another declaration is expected, even if
  the two have the same layout. That is the usual nominal discipline. When two layouts should
  be treated as one, Proposal R identifies them before the IR is built.
- **Semantics.** `Val` is an ordinary inductive family whose `ctor` stores
  `Vals (Σ.ctorsOf n args)[i]`, and evaluation is structural, with no fuel (see the toy).

**Costs.**

- `Σ` goes on the `variable` line of every pass (part 1, Proposal 4).
- `lowerTy` needs a table to add declarations to. It becomes `StateM JsSig`, or the table is
  collected once before lowering. The key for looking up a declaration is its layout, hashed,
  so equal structural unions get the same id.
- **Dependent pattern matching.** `JsMem (Σ.ctorsOf n args) fs` has an index that is a function
  application. Part 2's toy found the discipline that works: traverse `JsArgs` / `JsSel` without
  inspecting the index, and match only on `JsMem` / `JsUnionArms`. The one index pattern in
  `Unbox.lean` becomes `(τ := .obj _ _)`.
- **Printing.** The printer reads the layout from `Σ` instead of from the type. The printed
  object is the same (`{ tag: i, _1: … }`), so the snapshots do not change.
- `shareFree` needs `Σ`. For a recursive declaration it is a greatest fixpoint over the table,
  which is a small worklist computation.

---

## Proposal Q: declarations with parameters (orthogonal: works with P, with part 2's B or C)

Every design so far keeps declarations monomorphic, like the Term-level blocks. JavaScript
erases types, so **one declaration can serve every instance**:

```lean
inductive PTy | terminal … | param (i : Nat) | obj (n : Nat) (args : List PTy) | …
def PTy.inst (as : List JsTy) : PTy → JsTy      -- first order: no binder, no capture
def JsSig.ctorsOf (Σ) (n) (args) := (Σ.decls[n].ctors).map (·.map (PTy.inst args))
```

- **The built-in `List` is `obj List [α]`, and so is a user's `MyList α`** (or, after R, a user
  list of the same shape). `JsTy.consList`, `JsListOp.nil` and `JsListOp.cons`, and the roughly 40
  list-specific matches in the passes (part 2, §0), become ordinary `union_mk` /
  `unionCases`. The `List` = `MyList` differential test of part 2 then passes by construction,
  because the two are the same code path.
- **The extern catalogue gets a prelude.** Reserve ids for `Option α`, `Prod α β` and `List α`.
  The five object types in `JsTerm/Ops/Imported.lean` then become `obj Option [string]` and
  `obj Prod [float, int53]`, with no interning needed for the catalogue.
- **One helper per declaration, not per instance.** Structural equality, hashing, `toArray` and
  the `consList__append` family in `runtime.js` are emitted or written once for `List`, whatever
  the element type is. The equality or hash of an element is passed as an argument, as a
  dictionary would be. This keeps the output size flat as instances multiply.
- **Soundness.** `inst` substitutes closed types for `param i` in a first-order tree. The result
  is again an ordinary `JsTy`, and equality stays syntactic. This is the difference from `μ`
  (part 1, Proposal 5): no type ever contains a binder.
- **Where the parameters come from.** The Term level has none, so `FromTerm` recovers them by
  *anti-unification*: two blocks whose layouts differ only at the same leaf positions become one
  declaration with a parameter at those positions. This is optional. With no parameters
  recovered, Q degenerates to P, and the built-in `List` still gets its prelude declaration.
- **Costs.** `PTy` is a second small type, with its own `inst` lemmas. `JsTy` becomes a nested
  inductive through `List JsTy`. Lean's `deriving DecidableEq` refuses nested inductives, so the
  toy writes `Ty.decEq` by hand, which takes about 20 lines. `decide` still reduces it.

---

## Proposal R: canonical layouts, where the *id* is the layout (equi-recursive, decided once)

Part 1 rejected `μ` because type equality stops being syntactic. R keeps the **meaning** of `μ`,
where two types are equal when their layouts are equal as infinite trees, but it computes
equality **once**, when types are lowered, and not inside the typed IR.

- Before building `JsExpr`, `FromTerm` treats the whole table of declarations as an automaton.
  The states are declarations, and a state's label is its layout with the recursive positions
  as edges. `FromTerm` then **minimises** the automaton by partition refinement (Hopcroft's
  algorithm). Two declarations with the same layout as infinite trees end up in the same class.
  Each class gets one id.
- From then on the typed IR is P or Q, with syntactic `Nat` equality. But the ids are now
  **canonical**:
  - `MyList Nat`, the built-in `List Nat`, and a user type `Stack` with the same constructors all
    get one id. The JavaScript code for them is identical by construction, and so are the helpers.
  - A structural union and a declared datatype with the same layout also get one id.
- **Why this is right for JavaScript.** The layout is all that exists at run time, so
  identifying same-layout types loses nothing that the generated code could observe. The
  Lean-level names go into a side table from each id to its names, which is used for JSDoc
  comments and for readable helper names.
- **Proof obligation.** The claim "same class ⇒ same layout" is an ordinary lemma about a
  finite computation. Alternatively, a checker can verify, for the result, that every class is a
  bisimulation. That is a cheap decidable check, and it can run as a Spec test.
- **Costs.** One partition-refinement pass per module, which is near-linear. Printed type
  names become "one of the names", so a user sees `List` where they wrote `Stack` unless the
  side table is used.

---

## Proposal S: the representation is part of the declaration, instead of a global knob

`JsConfig.listRepr` is global today: every list is either cells or an array. With P, a
declaration's row can carry its **representation**:

```lean
inductive JsRepr | cells | array | nullable | smallIntNullary | padded
structure JsDecl where layout : JsLayout; repr : JsRepr
```

- **Types keep the choice consistent.** The same constructors can appear under two
  declarations, `List/cells` and `List/array`. They are different ids, so the Lean type checker
  rejects any place where one is used as the other. Every change of representation is an
  explicit, typed conversion (today's `listOp` conversions, generalised), and a pass cannot
  accidentally merge them.
- **The choice can be made per use instead of per module.** A value that is only built by
  `Array.toList` and only consumed by a left fold can be `List/array`, while a list that shares
  tails stays `List/cells`. The lowering picks the declaration and inserts the conversions, and
  the typed IR guarantees they are complete.
- **The global knob stays** as the default choice, so the `faithful` / `pbo` snapshots are
  unchanged until a per-use policy is switched on.

---

## Answer to "how to make it typed *while improving* optimisations?"

Parts 1 and 2 list the gains that typing enables: one code path for lists, type-directed
loops, known-constructor field reads, per-datatype layouts, reset/reuse, monomorphic object
shapes, `null` for options, and `shareFree` for datatypes. The gains below are the ones that
P, Q, R and S add.

1. **Identical code for identical layouts (R).** Two layouts that are equal as trees get the
   same helpers, the same `$tagN` constants and the same shapes for JavaScript engines, even if
   the user declared them separately.
2. **Nullary constructors as small integers (S, `smallIntNullary`).** A declaration whose
   nullary constructors are printed as `0`, `1`, … needs no `{ tag: 0 }` allocation and no
   `$tag0` constant. The tag test becomes `typeof x === "number" ? x : x.tag`, or just
   `x === 0` when there is one nullary constructor. This is decidable from the row. It
   generalises part 2's `null` for option-like types to any number of nullary constructors.
3. **Tag tests by pointer (S, with Hoist).** If the row says every nullary cell is the shared
   constant, which `Hoist` already makes true for literals, and `runtime.js` does the same, then
   `x.tag === 0` becomes `x === $tag0`. That saves one property load per test. It is sound only
   because the type says which constructors can reach `x`.
4. **Struct of arrays for arrays of numeric records.** For `Array (obj n [])`, where `n` is a
   non-recursive record whose fields are all numbers, the row can choose a representation with
   one typed array per field (`Float64Array`, `Int32Array`, …). Array reads become field reads
   at an index. The choice is only safe because every access goes through typed `record_mk` /
   `destructure` forms at that id.
5. **Constructor specialisation and fusion keyed by declaration.** The fold of a declaration is
   derived from its row. Two optimisations can then be written once for all declarations
   instead of for `List` only:
   - `toArray (map f (ofArray a))` compiles to one loop (fold/build fusion);
   - a recursive function that always matches its argument against a known constructor is
     specialised to that constructor (GHC calls this SpecConstr).
6. **Unboxing function parameters.** A parameter of record type `obj n args` that the body
   always destructures can be passed as separate fields (worker/wrapper). Today `Unbox` does
   this for local variables. With a table, the decision for a parameter is local to the
   function, because the layout is known from the id.
7. **Faster comparisons in the compiler and in the output.** Inside the compiler, type
   equality becomes a comparison of ids, and an `obj` case replaces three large `DecEq` cases.
   In the generated code, the structural equality helpers of immutable declarations can start
   with `a === b ||`, which is sound because no in-place update touches cells of a declaration
   (the `InPlace` pass updates arrays, never objects).

---

## Comparison with the earlier recommendations

| | Casts / proof fields | Pattern shape of the 4 forms | Values with 2 types | `List` special cases | Output sharing across instances |
| --- | --- | --- | --- | --- | --- |
| part 1, Prop. 3 (layout proof) | one proof field, `▸` per rewrite | + proof field | yes (`data r` vs. unfolding) | stay | no |
| part 2, B (head form) | none | same, binder indices `heads Σ` | yes (head vs. field) | removable | no |
| **P (nominal objects)** | **none** | **same, index `obj n args`** | **no** | removable | per declaration |
| **P + Q (parameters)** | none | same | no | **removed (prelude `List`)** | **per declaration, all instances** |
| P + Q + R (canonical ids) | none | same | no | removed | **per layout** |
| S (representation in the row) | none | same | no | removed | per layout and representation |

## Suggested order

1. **Stable ids first** (part 2's A, which is also the first step of P): `D<id>` names that do not
   depend on the scope.
2. **Pass counters** (part 2) before any change to the typing, so that a lost optimisation shows
   up as a failing test in `Tests/Main.lean`.
3. **P**, with `Σ` as a parameter. Start with `Unbox`, which has the most matches and the one
   index pattern, to confirm that dependent matching over `Σ.ctorsOf n args` stays as simple as
   in the toy. Then `FromTerm` can accept `data_in` / `data_out`. Both become no-ops, because the
   value already has type `obj n args`. It can also accept `data_rec`.
4. **Q with a prelude** (`List`, `Option`, `Prod`). This retires `consList` / `JsListOp.nil` /
   `cons`, and the `List` = `MyList` test becomes a regression guard.
5. **R** once recursive user datatypes are common enough for duplicate layouts to matter.
6. **S** and gains 2 to 6, one at a time, each measured by the counters and by the node
   snapshots.

## What the toy checks (`proposals/TypedDataNodeToy.lean`)

- `Ty = nat | obj n args`, `PTy` with `param i`, and `Sig.fieldsOf n args` built by first-order
  instantiation.
- `Val` / `Vals` form an inductive family, and `Expr.eval` is structural, with no fuel.
- `Expr.knownCtor` needs no cast, and `Expr.knownCtor_eval` proves that it preserves evaluation
  (depends only on `propext`).
- One declaration `List α` is used at `List Nat` and at `List (List Nat)`. An anonymous
  non-recursive union (`none | some Nat`) uses the same `mk` / `case`. The results are checked by
  `rfl`, before and after the rewrite.
- `DecidableEq Ty` is written by hand (nested inductive), and `decide` reduces it
  (`listTy .nat ≠ listTy (listTy .nat)`).
- **Not modelled:** the real passes, `JsSel`, join points, the interning in `lowerTy`, R's
  minimisation, and S's representations.
