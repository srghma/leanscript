# Typing `JsTy.data` without losing optimisations (and gaining some)

This is a design note. Apart from the toy model `proposals/TypedDataToy.lean`, which checks
with `lake env lean proposals/TypedDataToy.lean` and has no `sorry`, **nothing here is
implemented**. It picks up §3 of `JsTermReviewPlan.md` and §2.1 / step 5 of
`RecursiveDatatypesProposal.md`. Those two say *that* `data` should be typed. This note is
about *how* to type it without slowing down the passes of `JsTerm/Passes`.

```lean
/-- A declared datatype, by name (`D<block>_<member>`). -/
| data (name : String)
```

---

(In the Lean snippets, `Σ` stands for the signature; `Σ` is a keyword in Lean, so real code would name it `S` or `sig`, as the toy does.)

## 0. The problem

### What is wrong with the string

1. **Nothing ties the name to a declaration.** Two different datatypes with the same printed
   name are the same `JsTy`. `refName` computes the name from a *relative* de Bruijn depth
   (`D<depth>_<j>`), so the same datatype can get two names in two scopes, and two datatypes
   can get the same name.
2. **The layout is unknown.** A value of type `.data n` cannot be built (`union_mk`), matched
   (`unionCases`) or projected (`destructure`): all three are typed at the *structural*
   `JsTy.union c₀ c₁ cs` or `JsTy.record f₁ f₂ fs`. So `FromTerm` rejects every construct that
   touches a datatype (`data_in`, `data_out`, `data_rec`, `data_brec`) as `notYet`.

### What the fix must not break

The passes find their work by **pattern-matching on the syntax** of `JsExpr` / `JsBlock`.
Counting the matches on the four forms involved (`rg -c` over `JsTerm/Passes` and
`JsTerm/Print`):

| Form | Passes that match on it |
| --- | --- |
| `union_mk` | `Unbox`, `InPlace/Collect`, `Simplify`, `InlineConsts`, `Contify`, `Hoist`, `Cleanup`, printer |
| `unionCases` | `Unbox` (10 matches), `Cleanup`, `Contify`, `Tco`, `InPlace`, `Hoist`, `InlineConsts`, `Simplify`, printer |
| `record_mk` | `Unbox`, `InPlace`, `Simplify`, `Contify`, `Hoist`, `Cleanup`, `InlineConsts`, printer |
| `destructure` | `Unbox` (13 matches), `Tco`, `InlineConsts`, `Hoist`, `InPlace`, `Simplify`, `Contify`, `Cleanup`, printer |

The obvious fix (plan §3) adds two *cast nodes*, `data_in : JsExpr (Σ.unfold r) → JsExpr (.data r)`
and `data_out` going the other way. Both are the identity at run time. They are the danger:

- `unboxNode` looks for `let acc = { tag: i, … }` whose assignments are all `{ tag: i, … }`.
  With casts, it sees `acc = data_in({ tag: i, … })` and `unionCases (data_out acc)`, so it
  matches nothing.
- `Hoist` shares `{ tag: 0 }` as `$tag0`. It then sees `data_in($tag0)` and can no longer
  share the whole of `{ tag: 1, _1: 1, _2: { tag: 1, _1: 2, _2: $tag0 } }`, because the
  literal is interrupted by a cast at every level.
- Case-of-known-constructor, `InlineConsts`, `Contify`, and the in-place analysis of
  `InPlace/Collect` (a fresh object is one built by `union_mk`) all have the same problem.

Every pass would need an extra case for "look through the casts". That is roughly 40 edited
matches, and each one it forgets is an optimisation that silently stops firing: the snapshots
still pass, and only the output gets slower.

So the real design question is **where the equation `data r = Σ.unfold r` lives**, so that
the passes never see it as a node.

---

## Proposal 1 — Extrinsic: a checked index, a well-formedness predicate, no syntax change

```lean
| data (id : Nat)                                -- the position of the member in the module's table

structure JsModule where
  …
  datatypes : Array JsTy                         -- the unfolding of member `id`, a `union` / `record` / `enum`
```

- Construction and matching stay typed at the structural `union`. `FromTerm` emits
  `union_mk` / `unionCases` at `datatypes[id]` directly. In the syntax, a datatype value is a
  union value. `JsTy.data id` appears only where the *recursion* goes: a field of type
  `data id` inside `datatypes[id]`.
- To match such a field, `FromTerm` still needs the unfolding. It gets it with a single
  **untyped** coercion, `JsExpr.retype (e : JsExpr C M σ) (τ : JsTy)`. This is accepted when
  `σ` and `τ` unfold to the same type, and is checked by a separate
  `JsModule.WellFormed : Prop` (or a Boolean checker run in the snapshots).
- **Optimisations: all kept, and no pass changes.** `retype` appears only at the recursion
  points, where no pass looked before anyway.
- **Cost:** the static typing of `JsTerm` has a hole, closed only by the checker, and passes
  cannot rely on it in proofs. The name bug (item 1) goes away, because `id` is global to the
  module and not a relative depth.
- **When to choose it:** as the first step (step 1 of `RecursiveDatatypesProposal.md` §5),
  to unblock `FromTerm` in a small change.

## Proposal 2 — Intrinsic, with casts, and passes that see through them via views

This is plan §3 as written (`JsTy ks`, `data (r : Ref ks)`, `JsSig ks`, `data_in` /
`data_out` nodes), with the cost of the casts removed in one place.

- Add **smart constructors** that remove round trips: `dataIn (dataOut e) = e`, and
  `dataOut (dataIn e) = e`. This mirrors how `JsExpr.consListOf?` already removes
  `consList__to_array` / `consList__of_array` round trips (`JsTerm/Syntax/Basic.lean`).
- Add **views**, one function per form: `JsExpr.asUnionMk? : JsExpr C M τ → Option (UnionMkView …)`.
  A view returns the constructor, the arguments *and the chain of casts* around it. Each pass
  matches on the view instead of the raw constructor. The rewrite puts the casts back
  (`view.rebuild`).
- **Optimisations: kept, but every pass must be ported to the views** (the ~40 matches
  above). This change is mechanical, but it touches every pass.
- **Cost:** a lot of churn, and a view that is not used means a lost optimisation (only
  benchmarks show it). Keep this design only if the cast nodes are wanted for their own sake,
  for example to print `/* D0_1 */` annotations.

## Proposal 3 — Intrinsic, *without* cast nodes: the unfolding is carried by a proof ★ recommended

Put the equation in the **index** of the existing constructors, not in new nodes. `union_mk`,
`unionCases`, `record_mk` and `destructure` stop requiring their type to be *syntactically*
`.union c₀ c₁ cs`. Instead, they take a proof that their type **unfolds** to those
constructors:

```lean
/-- The constructors a type unfolds to, in the module's signature `Σ`. -/
def JsTy.ctors? (Σ : JsSig ks) : JsTy ks → Option (List (List (JsTy ks)))
  | .union c₀ c₁ cs => some (c₀ :: c₁ :: cs)
  | .data r         => (Σ.unfold r).ctors?          -- one step: `Σ.unfold r` is a union / record
  | _               => none

| union_mk   {τ} {cs fs} (h : τ.ctors? Σ = some cs) (ix : JsMem cs fs) (args : JsArgs C M fs) : JsExpr C M τ
| unionCases {τ} {cs}    (h : τ.ctors? Σ = some cs) (e : JsExpr C M τ) (arms : JsUnionArms C M J k cs) : JsBlock C M J k
-- likewise `record_mk` / `destructure` with `τ.fields? Σ = some (f₁ :: f₂ :: fs)`
```

- **There is only one form for "build a constructor" and one for "match".** A structural
  union and a declared datatype use the same `union_mk`. Every pass that matches
  `union_mk ix args` still matches, because `h` is just one more field it passes through
  unchanged. Porting a pass means adding `h` to the pattern, with no new cases.
- **Case of a known constructor works across both kinds of type.** Given `unionCases h
  (union_mk h' ix args) arms`, the two proofs say the lists of constructors are equal
  (`Option.some.inj (h'.symm.trans h)`), so the arm is selected with no dynamic check. The toy
  proves this rewrite correct once, for both kinds of type (`Expr.knownCtor_eval`, which uses
  only `propext`).
- **Recursive values need no fuel.** In the toy, `Val` is an ordinary inductive family
  (`ctor (h : τ.ctors? S = some cs) (ix : Mem cs fs) (vs : Vals S fs) : Val S τ`), and
  `Expr.eval` is structural. So this design also gives `JsTerm` a semantics that the passes
  can be proved against (today "`JsTerm` has no semantics", `Unbox.lean`).
- **Printing is unchanged.** `h` is a `Prop`, so it is erased, and `{ tag: i, _1: … }` is
  printed from `ix` as today.
- **Cost:**
  - `JsTy` gets the index `ks` (or a module parameter; see Proposal 4), and so do
    `JsExpr C M τ`, `JsBlock`, and the rest.
  - `h` must be produced. In `FromTerm` it is `rfl` for a structural union, and a lemma
    about `Σ` for `data r` (both are `decide`-able on closed signatures).
  - A pass that *changes* the type of a constructor (none does today; `Unbox` removes the
    constructor instead) would have to rebuild `h`.
- **Where the risk is:** a proof field inside the index can make dependent pattern matching
  harder (the `▸` in `Expr.eval` of the toy). The toy shows the pattern stays small: one
  `ctors_unique` lemma, and one `▸` per rewrite.

## Proposal 4 — The signature as a *parameter*, not an index

This variant applies to Proposals 2 and 3, and it minimises churn. Instead of `JsTy ks` and
`JsExpr ks C M τ` everywhere, fix the signature **per module**:

```lean
section
variable (Σ : JsSig)                   -- `JsSig := { n : Nat, unfold : Fin n → JsTy }`
inductive JsTy | … | data (r : Fin Σ.n)
```

or, more simply, keep `JsTy` unindexed with `data (r : Nat)` and make `Σ` a **parameter**
(not an index) of `JsExpr` / `JsBlock`. Lean then handles it uniformly and cheaply:

- Every pass is already written "for all `C M`". It becomes "for all `Σ`", and `Σ` is never
  inspected except by the rules for `data`, so `Σ` goes into each pass's `variable` line once.
- `DecidableEq JsTy` (the hand-written `JsTerm/Ty/DecEq.lean`) does not change at all. A
  derived equality is already fast, and `ks` indices would make it heavier.
- Scope-dependent names disappear: `r` is global to the module, so the printed name is
  `D<r>`, stable across scopes.

This fits well with Proposal 3: only `JsTy.ctors?` reads `Σ`.

## Proposal 5 — Equi-recursive `μ` in `JsTy` (assessed, not recommended)

`| mu (body : JsTy) | var (i : Nat)` makes `data` structural: `List α` would be
`mu (union [] [α, var 0])`, and `consList α` a plain abbreviation.

- **For:** no signature, and `consList` stops being a separate former.
- **Against:** unfolding needs substitution, so `JsTy` equality is no longer syntactic (two
  unfoldings of one type differ). The same problem is why `LeanScript.Ty` moved *away* from
  `μ` to declared datatypes (`NominalTyProposal.md`). It is also worse for the passes: casts
  come back as `fold` / `unfold`, which is Proposal 2's problem again.

---

## How typing *improves* the optimisations

Once the layout of `data r` is known to the typechecker, several optimisations that cannot be
expressed today become typed rewrites.

### A. One code path for lists and user datatypes

`JsListOp.nil` / `cons` (with `JsTy.consList`) is a special case of `union_mk` at the builtin
member `List α ≅ nil | cons α (List α)`. With Proposal 3:

- `consList α` becomes `data listRef` (for each monomorphic element type `α`, as with
  `LeanScript` blocks), and `listOp (.nil _)` / `listOp (.cons _)` become `union_mk`.
- Everything already written for unions then applies to lists: `$tag0` sharing,
  whole-literal hoisting, case-of-known-constructor, and `Unbox`. The reverse also holds: the
  **tail-sharing** logic written for `consList` (`JsParts` onto a tail) applies to *any*
  datatype with one recursive field (snoc lists, streams, expression spines).
- `Hoist` keeps its special case `listOp (.nil _) ↦ "$tag0"` only for the conversions
  (`ofArray`, `append`, …), which stay runtime calls.

### B. The type says which traversal is a loop

The loop shapes of `RecursiveDatatypesProposal.md` §3 (left fold, right fold with an explicit
stack, and tail-recursion-modulo-cons with `setTail`) are only valid for **linear** members:
one recursive field per constructor. With a typed `Σ` this is a **static property of the
signature**:

```lean
def JsSig.linear (Σ) (r) : Prop := ∀ c ∈ Σ.ctors r, (c.filter (· = .data r)).length ≤ 1
```

`Term.optimize` / `FromTerm` choose the loop construct by `decide`, not by guessing from the
shape of the code. `setTail` can be typed to accept only a cell *of a linear member*, which
excludes the case where writing the tail would be unsafe.

### C. Types that know the tag: fewer checks, direct field loads

Add a refinement `JsTy.ctor (r) (i : Fin (Σ.ctors r).length)`: "a value of `data r` built
with constructor `i`". It is erased when printed (it is the same object).

- `unionCases` gives the arm `i` its subject at the refined type `ctor r i` for free.
- `JsExpr.field (e : JsExpr C M (.ctor r i)) (j : Fin …)` prints `e._j` with **no tag test
  and no destructuring**. This is the `cur._1` / `cur._2` of the hand-written loops
  (`ofList`), and it is sound by typing, not by an analysis.
- `whileTag` (the loop over a cursor) types its body with the cursor at `ctor r i`.
- `Unbox` becomes a type-directed rewrite: an accumulator of type `ctor r i` whose
  constructor has one field *is* that field. Today `unboxNode` has to prove this by scanning
  every assignment. With the refinement, the check is done when the type is assigned.

### D. Per-datatype layouts, chosen once, used consistently

A typed signature is the right place for **representation choices per datatype**, the way
`JsConfig.listRepr` chooses one for `List`:

- `nullaryAsNull` (`null` for the single nullary constructor, as discussed in
  `RecursiveDatatypesProposal.md` §2);
- `Nat`-like unary types as numbers (open question 1 of that proposal);
- one-constructor members as records without a tag (already the rule, but now checked);
- only-nullary members as enums.

Because every `union_mk` / `unionCases` goes through `τ.ctors? Σ` (and a `Σ.layout r`), a
layout choice cannot be applied in one place and forgotten in another. A mismatch is a type
error, not a snapshot failure.

### E. Structural operations per datatype

With a typed `Σ`, the generator can emit, once per member, `eq_D3(a, b)`, `hash_D3(a)` and
`toArray_D3` / `ofArray_D3` (the `list` / `ofList` of the example in
`RecursiveDatatypesProposal.md`). Each is a loop when the member is linear (B). The externs
over lists then become instances (`consList__to_array` is `toArray_<List>`).

### F. Passes become provable

Proposal 3 gives `JsTerm` a structural semantics with recursive values. A pass such as
case-of-known-constructor can then carry an `eval` preservation proof, as `Term.optimize`
does, instead of relying only on snapshots. `TypedDataToy.lean` is a first instance
(`Expr.knownCtor_eval`).

---

## Summary and suggested order

| | Typed? | Pass churn | Optimisations | Enables A–F |
| --- | --- | --- | --- | --- |
| 1. Extrinsic index + checker | checked, not static | none | all kept | A, B, D, E partly |
| 2. Casts + views | static | every pass (views) | kept if every pass is ported | all, with more friction |
| **3. Unfolding as a proof in the index** | static | add `h` to patterns | **all kept, one rewrite for both kinds of type** | **all** |
| 4. `Σ` as a parameter (with 1 or 3) | static | minimal | all kept | same as the base proposal |
| 5. `μ` in `JsTy` | static | casts again | at risk | A only |

Suggested order:

1. Proposal 1 (`data (id : Nat)`, a table in `JsModule`, `FromTerm` emitting `union_mk` at
   the unfolding). This unblocks non-recursive matching on datatypes right away.
2. Move to Proposals 3 + 4: `Σ` as a parameter of `JsExpr` / `JsBlock`, and `h : τ.ctors? Σ = some cs`
   on `union_mk` / `unionCases` / `record_mk` / `destructure`. `retype` goes away.
3. Improvement A (`consList` as the builtin `List` member), then C (the `ctor r i`
   refinement, `field`, `whileTag`), then B / E (loops and per-datatype helpers), then D
   (layout knobs).
