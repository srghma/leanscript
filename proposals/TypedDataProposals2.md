# Typing `JsTy.data`, part 2: typed without losing optimisations, and typed to gain some

```lean
/-- A declared datatype, by name (`D<block>_<member>`). -/
| data (name : String)          -- JsTerm/Ty/Defs.lean
```

This note follows `proposals/TypedDataProposals.md` (part 1). Part 1 compared five designs
and recommended "the unfolding as a proof field in the index" (its Proposal 3). This note
adds **new designs** that part 1 did not consider, a way to **detect lost optimisations**
mechanically, and a list of optimisations that typing makes possible.

It is a design note. The only code is a toy model, `proposals/TypedDataHeadToy.lean`, of
Proposal B below. It is not part of the Lake build. It checks with
`lake env lean proposals/TypedDataHeadToy.lean` with no errors and no `sorry`, and its
theorem `Expr.knownCtor_eval` depends only on `propext`. **Nothing in `JsTerm` was
changed.**

---

## 0. Where things stand (checked against the current tree)

- `lowerTy` maps `Ty.data r` to `.data (refName r)`. `refName` writes `D<depth>_<j>` from the
  **relative** de Bruijn depth of `r` (`JsTerm/Ty/Lower.lean`). So the name depends on the
  scope, and two datatypes can print the same name.
- `FromTerm` refuses `data_in`, `data_out`, `data_rec` and `data_brec` with `notYet`
  (`JsTerm/Lower/FromTerm.lean`). So today no JavaScript expression ever has a type `.data _`.
- The four forms the optimisations look for are typed at *structural* types:
  - `union_mk ix args : JsExpr C M (.union c₀ c₁ cs)`
  - `unionCases (e : JsExpr C M (.union c₀ c₁ cs)) arms`
  - `record_mk`
  - `destructure`

  `rg -c '\.union_mk\b'` and the same for the other three, over `JsTerm/Passes` and
  `JsTerm/Print`, give 24, 31, 22 and 37 occurrences: 114 places that must keep matching.
- Lists are special. `JsTy.consList` and `JsListOp.nil` / `cons` duplicate `union_mk` for the
  one recursive type the backend supports, and the passes have extra cases for them
  (`rg -c 'listOp|consList'`: 20 in `Simplify`, 13 in `Hoist`, 3 in `InlineConsts`, 2 each in
  `Unbox`, `Cleanup` and `InPlace/Collect`).
- `JsTy.shareFree` (`JsTerm/Passes/InPlace/Linear.lean`) returns `false` for `.data _` and
  `.consList _`. So a value that contains a list never counts as fresh, and the in-place
  array updates are lost around it.

**Losing optimisations** means that one of those 114 matches stops matching because a
datatype value looks different from a union value. **Gaining optimisations** means that
knowing the layout makes new rewrites typable.

---

## Proposal A: a stable global index (a small step, needed by every other proposal)

```lean
| data (id : Nat)                  -- the datatype's position in the module's table
structure JsModule where …; datatypes : Array JsDataDecl
```

- `FromTerm` numbers the members of all blocks **once per module**, for example with a
  `HashMap (Ref ks) Nat` built when it enters a block. The printed name becomes `D<id>`, which
  does not depend on the scope. This fixes the name clash on its own.
- `DecidableEq JsTy` (`JsTerm/Ty/DecEq.lean`) keeps its shape. Only the `String` comparison
  becomes a `Nat` comparison, which is also faster.
- By itself this proposal is **not typed**. It is the naming layer that B, C and D build on.

---

## Proposal B ★: expression types in head form (no casts, no proofs)

**The rule: no expression ever has a type `data r`.** Wherever a value of type `t` is
*bound*, the binder's type is `t.head Σ`:

```lean
def JsTy.head (Σ : JsSig) : JsTy → JsTy
  | .data r => Σ.unfold r          -- a `union` / `record` / `enum`, never a `data` (see below)
  | t       => t
```

"Bound" covers a field bound by a case arm or by `destructure`, an argument of a
constructor, a parameter of `lam`, an argument of `app`, an array element read by `forOf`,
and a `join` / `letMut` variable. The name `data r` survives only **inside** the field lists of
`union` / `record` and in the domains of `fn`, which is exactly where the recursion is.

The indices change like this; nothing else changes:

```lean
| union_mk (ix : JsMem (c₀ :: c₁ :: cs) fs) (args : JsArgs C M (heads Σ fs))
    : JsExpr C M (.union c₀ c₁ cs)                                 -- same result type as today
| JsUnionArms.cons (sel : JsSel (heads Σ fs) us) (b : JsBlock (pushAll us C) M J k) …
| record_mk (args : JsArgs C M (heads Σ (f₁ :: f₂ :: fs))) : JsExpr C M (.record f₁ f₂ fs)
| destructure (e : JsExpr C M (.record f₁ f₂ fs)) (sel : JsSel (heads Σ (f₁ :: f₂ :: fs)) us) …
| lam (body : JsBlock (pushAll (heads Σ σs) C) M [] (.ret τ)) : JsExpr C M (.fn σs τ)
| app (f : JsExpr C M (.fn σs τ)) (args : JsArgs C M (heads Σ σs)) : JsExpr C M (τ.head Σ)
```

Here `heads Σ = List.map (JsTy.head Σ)`, and `Σ` is a **parameter** of the mutual block
`JsExpr` / `JsBlock` (part 1, Proposal 4), not an index.

**Why nothing is lost.**

- A value of `List Nat` has the type `.union [] [nat, data L]`, a plain `union`. It is built by
  the ordinary `union_mk` and matched by the ordinary `unionCases`. The 114 patterns keep the
  **same shape**: `union_mk ix args` still has the type `.union c₀ c₁ cs`. When a pass
  rebuilds a node, it passes `args` through with their index unchanged.
- There is no `data_in` / `data_out` node to look through, and no proof field to carry or
  rebuild. Part 1's Proposal 3 needs one `▸` per rewrite. Here the case-of-known-constructor
  rewrite has none. In the toy:

  ```lean
  def Expr.knownCtor : Expr S Γ τ → Expr S Γ τ
    | .case (.mk ix args) arms => .lets args (arms.pick ix)   -- typechecks as is
    | e => e
  theorem Expr.knownCtor_eval (ρ) (e : Expr S Γ τ) : e.knownCtor.eval ρ = e.eval ρ
  ```

  This works because the arguments of `mk` are at `heads S fs`, which is exactly the
  environment the arm binds.
- `Hoist` still sees `{ tag: 0 }` as a `union_mk` with no arguments, so `$tag0` sharing and
  whole-literal hoisting work unchanged for every datatype.

**Why it is sound.**

- `head` unfolds **one level** of a closed unfolding, so no substitution happens and type
  equality stays syntactic.
- A value whose type is still `data r` (for example a `global` written by hand) cannot be
  passed where the head form is expected. The mismatch is a Lean type error when the node is
  built, not a silent wrong program.
- A declared datatype and a structural union with the same constructors get the same head
  type. That is intended: they have the same JavaScript layout. Below the head, the
  recursive fields still keep their names.
- **The unfolding must not be a `data`.** Store the unfolding as a *layout*, not as a `JsTy`,
  so this holds by construction:

  ```lean
  inductive JsDataBody | union (c₀ c₁ : List JsTy) (cs : List (List JsTy))
                       | record (f₁ f₂ : JsTy) (fs : List JsTy) | enum (n : Nat) (shift : Int)
  structure JsSig where n : Nat; body : Fin n → JsDataBody
  ```

  Then `head` is idempotent (`Ty.head_head` in the toy).
- **Semantics.** `Val` is an ordinary inductive family whose `ctor` stores `Vals (heads S fs)`,
  and `Expr.eval` is structural with no fuel (`Expr.eval` in the toy). This gives `JsTerm` the
  semantics that `Unbox.lean` says it lacks.

**Costs and risks.**

- `Σ` goes on the `variable` line of each pass. `lowerTy` has to produce head forms at
  binders; that is one `JsTy.head` call wherever a binder is created in `FromTerm`.
- **Dependent pattern matching.** An index `heads Σ fs` is a function application, not a
  constructor. So `cases` on a `JsArgs C M (heads Σ fs)` whose `fs` is a variable cannot
  always solve the index equation. The toy shows the working discipline: traverse
  `JsArgs` / `JsSel` generically over *any* index, and match only on `JsMem` / `JsUnionArms`,
  whose indices are plain constructors. The existing passes already traverse `JsArgs`
  generically, so this is expected to be a small change, but it should be checked on
  `Unbox`, which has the most matches, before committing to the design.
- **JSDoc and printed type names.** A binder's type no longer says `D3`. When a name is
  wanted in a comment, the printer can take it from the unfolded field type (which still says
  `data 3`), or `FromTerm` can pass the Lean type as a hint, as it already does for variable
  names.

---

## Proposal C: self-contained blocks (no signature parameter at all)

Put the block **inside** the type, with recursive positions as slots, instead of passing a
signature `Σ`:

```lean
inductive JsSlot | ty (t : JsTy) | self (j : Nat)          -- nested in `JsTy`
structure JsDataBlock where
  id    : Nat                                             -- interned: equal ids ⇔ equal blocks
  ctors : List (List (List JsSlot))                       -- member j ↦ constructors ↦ fields
| data (blk : JsDataBlock) (j : Nat)
```

- Unfolding `data blk j` maps `self j' ↦ data blk j'`. The block is closed (JavaScript types
  are monomorphic), so there is no capture and no substitution into arbitrary types. This is
  what separates it from `μ` (part 1, Proposal 5): the result is again an ordinary
  `data blk j'`, so equality stays syntactic.
- **Combined with B, `head` needs no `Σ`:** `head (data blk j) = union (unfold blk j)`. The
  mutual block `JsExpr` / `JsBlock` and every pass keep their current parameters. Only the
  indices of the binders change.
- **Costs.**
  - `JsTy` becomes a nested inductive through `JsSlot`, so the hand-written
    `JsTerm/Ty/DecEq.lean` grows.
  - Equality should compare `blk.id` first, which is sound only if ids are interned by a smart
    constructor. The alternative is a structural comparison, which is slow on large blocks.
  - Types are bigger trees. In memory they are shared by pointer, but `decide` on types in
    proofs gets slower.
- Choose C over "B with a `Σ` parameter" if threading `Σ` through the passes turns out to be
  more churn than the bigger `DecEq`.

---

## Proposal D: the layout proof found by instance search (a lighter version of part 1's Proposal 3)

Keep part 1's design, where `union_mk` / `unionCases` take a proof that `τ` unfolds to `cs`, but
make the proof an **instance** argument:

```lean
class HasCtors (Σ : JsSig) (τ : JsTy) (cs : outParam (List (List JsTy))) : Prop
instance : HasCtors Σ (.union c₀ c₁ cs) (c₀ :: c₁ :: cs)
instance [h : Σ.IsUnion r cs] : HasCtors Σ (.data r) cs
| union_mk [HasCtors Σ τ cs] (ix : JsMem cs fs) (args : JsArgs C M fs) : JsExpr C M τ
```

- Passes write `.union_mk ix args` and the proof is found by instance search, or kept by an
  `_` pattern. It is a `Prop`, so it is erased when printed.
- Unlike B, a value keeps its nominal type (`JsExpr C M (.data r)`), which is useful if
  printed type names matter.
- The cost stays: every rewrite that changes `τ` must find the instance again, and matching
  a node from one type against an arm list from another still needs part 1's
  `ctors_unique` and one `▸`. B avoids both.

---

## Proposal E (considered, rejected): index expressions by the runtime shape

Index expressions by the runtime layout: "a tagged object with arities `[0, 2]`" instead of
the full type. `data r` and its unfolding would then coincide by definition. The drawback
is that the shape forgets the field types, so a field read would be untyped. That is less
typing than today, not more.

---

## Detecting a lost optimisation (for any of the designs)

Part 1 warned that a lost optimisation is silent: the snapshots still compute the right
answers. Two cheap checks make it loud:

1. **Pass counters.** Each pass returns, next to its result, a `PassStats` record: how many
   times case-of-known-constructor fired, how many `$tagN` constants were shared, how many
   variables `Unbox` removed, how many array updates became in-place. A Spec test in
   `Tests/Main.lean` checks these counts on fixed inputs. Any drop in a count is a test
   failure.
2. **Differential test "`List` = `MyList`".** Compile the same program twice: once with
   `List Nat`, and once with a user datatype `MyList` that has the same constructors (one
   already appears in `Tests/SnapshotsPBOPure/InlineReferenceOpIsTag.lean`). Under `list=tagged`, the two JavaScript outputs must be
   **identical up to renaming**. Any difference means some pass still special-cases the
   built-in list, and today there are several such passes. This test also checks the first
   gain below.

---

## Optimisations that typing *adds*

These go beyond part 1's list (A–F there), except where noted.

1. **One code path for every recursive type** (part 1, A). With B, `consList α` is
   `data (List α)`, and `JsListOp.nil` / `cons` become `union_mk`. The list special cases in the
   passes (about 40 lines, see §0) disappear, except for the array conversions. Recursive user datatypes, which `FromTerm` refuses today, get
   every union optimisation at once, including tail sharing.
2. **`shareFree` for datatypes, so more in-place array updates.** With a signature,
   `shareFree (data r)` is the greatest fixpoint of `shareFree` over `Σ.body r`. `List Nat`, a
   tree of strings, and similar types are share-free, so values holding them count as fresh
   again, and the array updates next to them become mutable (`InPlace`). Today
   `shareFree (.consList _) = false` blocks this.
3. **Reusing constructor cells (reset/reuse, as in Lean's own compiler IR).** When
   `unionCases x` matches a variable `x` that owns its value (the existing `InPlace`
   ownership analysis), and the arm builds a `union_mk` of the *same head type* with no more
   fields, the new cell can overwrite `x`'s object: `x.tag = 1; x._1 = h; x._2 = t`. Only the
   types say whether the two objects have the same layout. With B that check is a syntactic
   equality of head types. A `map` over a uniquely owned list then allocates nothing.
4. **Monomorphic object shapes.** JavaScript engines optimise object accesses by the object's
   shape (V8 calls it a hidden class). `{ tag: 0 }` and `{ tag: 1, _1, _2 }` have different
   shapes, so every `x.tag` in a traversal sees two shapes. A typed signature allows choosing
   a layout **per datatype**: pad every constructor to the largest arity
   (`{ tag: 0, _1: undefined, _2: undefined }`, shared as `$tag0`), or emit one class per
   datatype. The printer and every `union_mk` read the choice from `Σ.body r`, so a
   constructor built in one place cannot disagree with the pattern matched in another.
5. **A nullable layout for option-like types.** A datatype `none | some α`, where the layout
   of `α` can never be `null` (decidable from `JsTy`), can be printed as `null` / the payload.
   This removes one allocation per `some`. Choosing it is a property of `Σ.body r` and the
   field type, so it is type-directed rather than guessed.
6. **Loops chosen by type** (part 1, B). Linearity, meaning at most one recursive field per
   constructor, is decidable on `Σ`. Left folds, right folds with an explicit stack, and
   tail-recursion-modulo-cons with a `setTail` typed for linear datatypes only become safe
   choices, not guesses.
7. **Known constructor across join points** (part 1, C). A refinement type `ctor r i` for the
   subject of an arm gives direct field loads (`cur._1`) with no tag test. With B the
   refinement is just the head type plus the constructor index.
8. **Structural helpers per datatype** (part 1, E): `eq_D3`, `hash_D3`, `toArray_D3`, emitted
   once per member, as loops when the datatype is linear.

---

## Comparison

| | Typed? | Changes to the 114 patterns | Cast nodes / proof fields | New parameter | Keeps printed type names |
| --- | --- | --- | --- | --- | --- |
| A. global index | no (checked) | none | — | none | yes, and they are stable |
| **B. head-form expression types** | **static** | **none to the pattern shape; binder indices use `heads Σ`** | **none** | `Σ` on `JsExpr` / `JsBlock` | at the fields (hint for binders) |
| C. self-contained blocks (+B) | static | as B | none | **none** | yes |
| D. instance-found layout proof | static | an extra implicit or instance argument | one proof, one `▸` per rewrite | `Σ` | yes |
| E. shape index | weaker | many | none | none | no |
| part 1, Proposal 3 | static | one proof field per pattern | one proof, one `▸` per rewrite | `Σ` | yes |

## Suggested order

1. **A** (a global `id` per module, stable names, `JsModule.datatypes`). This is a small change.
2. Add the **pass counters** **before** changing the typing, so the migration is measured.
   The `List` = `MyList` differential test can only run once recursive user datatypes are
   accepted (step 3), and it guards step 4.
3. **B** with `Σ` as a parameter, and `JsSig.body : Fin n → JsDataBody`. Try it first on
   `Unbox` to confirm that dependent pattern matching over `heads Σ fs` stays simple, as it
   does in the toy. Then `FromTerm` can accept `data_in` / `data_out` (both become no-ops:
   the value already has the head type) and `data_rec`.
4. Gain 1 (retire `consList`), checked by the differential test. Then gain 2 (`shareFree`),
   gain 3 (reuse of cells) and gain 4 (layout per datatype). These are the gains that change
   the running time of the generated code.
5. Move to **C** only if threading `Σ` through the passes turns out to be more churn than
   the nested `DecEq`.
