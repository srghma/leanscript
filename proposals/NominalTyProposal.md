# Proposal: alternatives to `WTypeTyProposal.md` — declared datatypes (recommended), final coalgebras, and others

> **Status: proposal only.** Nothing in `LeanScript/`, `TyTests/` or `TermTests/` has changed.
>
> This note answers: *same properties as `proposals/WTypeTyProposal.md` (Part A, hardened),
> but a different design.* §1 surveys the candidates, including a final-coalgebra (`ν`) meaning.
> §2 describes the recommended alternative, **N: nominal (declared) datatypes**. §3 explains
> where a final coalgebra does and does not fit.
>
> Claims marked **(checked)** are compiled at toy scale in two self-contained files. Neither
> has imports or is part of the Lake build:
>
> ```
> lean proposals/NomTyToy.lean     # design N
> lean proposals/CoTyToy.lean      # final-coalgebra facts, and Unfold
> ```
>
> Both compile with no errors, no warnings and no `sorry`. The main results use only the
> axioms `propext` and `Quot.sound`. Any other Lean in this note is a sketch and has **not**
> been compiled.

---

## 0. What has to be kept

These are the qualities of `WTypeTyProposal.md` §H/§A. The second column says how A gets
each one, and the third how N does.

| quality | A (one `mu` binder in `Ty n g`) | N (declared datatypes) |
| :-- | :-- | :-- |
| scoping by typing, no `TyWf` / `Ty.Wf` / `ty_wf` | `Ty n g`, `var (i : Fin n)`; closed = `Ty 0 0` | `Ty ks` refers to datatypes with `Ref ks`, a typed de Bruijn name; bodies use `Fld ks n g` |
| strict positivity by typing | `fn : Ty 0 0 → Ty n g → Ty n g` | `Fld.fn : Ty ks → Fld ks n g → …`: the domain is an *older* closed type |
| no unit-like type | ≥ 2 fields, ≥ 2 constructors, no `unit`, nullary ctor ↦ `Option`/`Bool` | same containers (**checked**) |
| no empty-like type | grounding index `g` on every `Ty`, `Mems` in grounding order | the same grounding index, but **only on declaration bodies**. Closed types have none (**checked**) |
| two distinguishable values of every closed type | `Ty.twoDen : (t : Ty 0 0) → Two (Den t)` | `Ty.twoDen : (Δ : DSig ks) → (t : Ty ks) → Two (Ty.Den Δ t)` (**checked**) |
| no fuel, no measure, structural | `IW.build` on a `Nat` bound, `IW.fold` | same (**checked**) |
| three term formers instead of twelve | `mu_in`, `mu_out`, `mu_rec` (+ `mu_brec`) | `data_in`, `data_out`, `data_rec` (+ `data_brec`) (**checked**, except `data_brec`) |
| no casts, computes by `rfl` | yes | yes. Older types are read through structural transports `Ty.lift`/`Ty.lower`, which also compute (**checked**) |
| mutual families, a different answer type per member | `LitExprS` with `swap` | same, plus a member that uses an older block (**checked**) |
| nested containers (`Array X`, `Nat → X`) | yes | yes (**checked**) |
| `DecidableEq` (hence `BEq`, `ReflBEq`, `LawfulBEq`) | derived | derived for `Ty`, `Ref`, `Fld`, `Decl`, `Mems`, … (**checked**) |
| canonical forms (types match by `rfl` / `decide`) | smart constructor `Ty.fix` + a rule for `closed` | **free**: a recursive type is a name (**checked**: `weaken listNat = listNat₂` by `rfl`) |

---

## 1. Survey of alternative designs

| design | idea | verdict |
| :-- | :-- | :-- |
| **N. Nominal / declared datatypes** (§2) | Recursive types are declared once, Lean-kernel style, in a signature `Δ`. A `Ty` names them. | **Recommended alternative.** Keeps every quality in §0; trades `Ty.fix` and the two indices for a signature parameter |
| **F. Final coalgebra (`ν`, M-types)** (§3) | The meaning of a recursive type is the *greatest* fixed point | **Not a replacement** for inductive types: it adds infinite values and **loses folds** (`CoList.no_sum`, **checked**). Useful as an *extra* `codata` form, and for reading `Unfold` without an existential (§3.3, **checked**) |
| D. Descriptions / "levitation" (codes for indexed families) | One code `Desc I` per indexed family, so `LitExpr : Ty → Type` is a single datatype over *all* indices | Codes need function fields (`Den S → Desc I`) or index-equality constraints. That breaks `DecidableEq` and canonical forms, and grounding over an infinite index set is not structural. Rejected |
| U. Universal values + typing predicate | `Den t = {v : Val // Typed t v}` over one first-order `Val` | `Den` stops being the Lean type (every value is a subtype), and function values do not fit a first-order `Val` (positivity). Rejected |
| C. Church / Böhm–Berarducci encodings | `μF := ∀ X, (F X → X) → X` | Needs an impredicative `Type`. Lean's is predicative, so this lands in `Type 1`, and there is no induction principle. Rejected |
| S. Approximation chain (Adámek colimit) | `μF := Σ d, Fᵈ(∅)` | The same value appears at many depths, so equality needs a quotient and `rfl` computation is lost. Rejected |
| E. Equi-recursive `μ` | `Den (μ b) ≡ Den (unfold b)` definitionally | Not expressible: `Den` would have to be non-well-founded. Rejected |

A and N are the two sensible ways to give recursive types a *structural* meaning (an indexed
W-type), and they differ in one axis only: **structural vs nominal typing of datatypes**.
A writes a datatype *inside* the type (`mu k bs j`). N writes it *once, beside* the types, and
refers to it by name. F changes the *meaning* (greatest instead of least fixed point).

---

## 2. Design N: declared datatypes

### 2.1 Closed types: one index, no binder, no hole, no grounding (checked)

```lean
/-- A name of member `j` of one block; blocks newest first (de Bruijn). -/
inductive Ref : List Nat → Type where
  | here  {k ks} (j : Fin (k + 1)) : Ref (k :: ks)
  | there {k ks} : Ref ks → Ref (k :: ks)

mutual
inductive Ty : List Nat → Type where          -- `ks` = sizes of the declared blocks
  | prim   {ks} : LeanPrimTy → Ty ks          -- toy: `nat`, `bool`
  | fn     {ks} : Ty ks → Ty ks → Ty ks
  | array  {ks} : Ty ks → Ty ks
  | thunk  {ks} : Ty ks → Ty ks               -- (not in the toy; like `fn`'s codomain)
  | enum   {ks} : LeanEnumSchema → Ty ks      -- (not in the toy; a leaf with ≥ 3 values)
  | record {ks} : Ty ks → Fields ks → Ty ks   -- ≥ 2 fields
  | union  {ks} : Ctors ks → Ty ks            -- ≥ 2 constructors, **no base needed**
  | data   {ks} : Ref ks → Ty ks              -- a declared datatype, by name
inductive Fields : List Nat → Type  | one | cons          -- ≥ 1
inductive Ctor   : List Nat → Type  | nullary | fields    -- no `PUnit` payload
inductive Ctors  : List Nat → Type  | two | cons          -- ≥ 2
end
```

A closed type never contains a hole, so it needs no scope index `n` and no grounding index
`g`. A union is simply two or more constructors: every closed type already has values, so
every constructor is inhabited. Compared with A:

* contexts, terms and signatures speak about `Ty ks` for the program's fixed `ks`, instead of
  `Ty 0 0`;
* there is no `closed` constructor, so there is no canonicity rule for it;
* there is no `mu` inside a type, so there is no `Ty.fix` and no inlining rule.

### 2.2 Declarations: the only place with holes and grounding (checked)

A block of `k + 1` mutually recursive datatypes over the older signature `ks` is a list of
member declarations in grounding order. The grammar is **flat**: a member is one layer of
constructors, and its fields are types.

```lean
inductive Fld : List Nat → Nat → Nat → Type where     -- a field, in a block of n, g grounded
  | hole  {ks n g} (i : Fin n) : i.val < g → Fld ks n g   -- a member used directly: grounded
  | old   {ks n g} : Ty ks → Fld ks n g                   -- an older closed type
  | array {ks n g} : Fld ks n n → Fld ks n g              -- guarded
  | fn    {ks n g} : Ty ks → Fld ks n g → Fld ks n g      -- domain older: positivity
inductive Flds   ks n g | one | cons                 -- ≥ 1 field
inductive BCtor  ks n g | nullary | fields (Flds ks n g)
inductive BCtors ks n   | two (BCtor ks n n) (BCtor ks n n) | cons …    -- guarded
inductive Alts   ks n g | two₁ | two₂ | here | there                    -- one grounded base
inductive Decl   ks n g
  | wrap   (f : Fld ks n g)                  -- one ctor, one field (`Rose.node : Array Rose → Rose`)
  | record (f : Fld ks n g) (fs : Flds ks n g)   -- one ctor, ≥ 2 fields
  | union  (u : Alts ks n g)                     -- ≥ 2 ctors, a grounded base
inductive Mems   ks n g | nil : Mems ks n n | cons : Decl ks n g → Mems ks n (g+1) → Mems ks n g

inductive DSig : List Nat → Type where        -- the signature: blocks, newest first
  | nil  : DSig []
  | cons (Δ : DSig ks) (k : Nat) (bs : Mems ks (k + 1) 0) : DSig (k :: ks)
```

The grounding rules are A's, but they only apply here: `hole i h` needs `i < g`; `array` and
the non-base constructors are guarded (`Fld ks n n`); member `j` is a `Decl ks (k+1) j`.

*Why flat.* A field like `Option T`, where `T` is in the block, is itself a Lean type
instance on the cycle, so it becomes **its own member**, and it is referred to by name. This
is what Lean's elaborator does for nested inductives. Non-recursive structure inside a field
is an `old` closed type (`old (union …)`). So bodies need no anonymous records or unions, and
the body grammar is much smaller than A's `Ty n g`.

*Blocks and positivity.* A function domain in a body must be an **older** closed type
(`Fld.fn : Ty ks → …`). Blocks exist precisely so that a later datatype can have a field
`List Nat → T` or `List Nat` while `List` is not part of its cycle. A block cannot see itself
as a closed type: `old listNat` inside `listNat`'s own block is a type error (**checked**,
`#guard_msgs`).

### 2.3 Meaning (checked)

```lean
def Ty.den (E : Ref ks → Type) : Ty ks → Type            -- structural on the type
  | .data r => E r | .fn a b => den E a → den E b | .record t fs => den E t × … | …
def DSig.refDen : DSig ks → Ref ks → Type                 -- structural on the signature
  | .cons Δ _ bs, .here j  => IW (Mems.fam (DSig.refDen Δ) bs) j   -- indexed W-type
  | .cons Δ _ _,  .there r => DSig.refDen Δ r
abbrev Ty.Den (Δ : DSig ks) (t : Ty ks) : Type := Ty.den (DSig.refDen Δ) t
```

This is A's `IW`/`IPF` meaning with the recursion split in two: on the signature for the
datatypes, and on the type for closed types. A block's older fields mean what the older
signature says. `Ty.Den (.cons Δ k bs) (.data (.there r)) = Ty.Den Δ (.data r)` holds by `rfl`,
so **a value of an old datatype is a value in every extension of the signature, with no
conversion** (checked). Unions use `Option`/`Bool` for constructors without fields, as in A:
`Ty.Den .nil (.union (.two .nullary (.fields (.one .nat)))) = Option Nat` (checked).

### 2.4 No unit-like and no empty-like types (checked)

```lean
def   Ty.twoDen (Δ : DSig ks) (t : Ty ks) : Two (Ty.Den Δ t)
theorem Ty.den_nonempty          (Δ : DSig ks) (t : Ty ks) : Nonempty (Ty.Den Δ t)
theorem Ty.den_not_subsingleton  (Δ : DSig ks) (t : Ty ks) : ¬ ∀ x y : Ty.Den Δ t, x = y
theorem Ty.den_exists_ne         (Δ : DSig ks) (t : Ty ks) : ∃ x y : Ty.Den Δ t, x ≠ y
```

The proof comes in two layers, and both are data computed by structural recursion:

* `DSig.two Δ : ∀ r, Two (DSig.refDen Δ r)`, by recursion on the signature. Inside a block
  it works member by member with `IW.build` on a `Nat` bound, first with `inh` (grounded
  holes suffice), then with `two`. This is exactly A's argument, confined to bodies.
* `Ty.pick E TE : (t : Ty ks) → Two (Ty.den E t)`, by recursion on a closed type, given two
  values of every datatype. It needs **no grounding**: every closed type has values.

The two values picked for `List Nat` are `[]` and `[0]` (checked, by `rfl`).

Rejected by the type checker (checked with `#guard_msgs`):

```lean
.cons (.wrap (.hole 0 (by decide))) .nil                           -- μX. X
.cons (.record (.old .nat) (.one (.hole 0 (by decide)))) .nil      -- μX. Nat × X
(.union (.one .nullary) : Ty [])                                   -- a one-constructor union
.cons (.wrap (.old listNat)) .nil   -- in listNat's own block      -- a block cannot see itself
```

As in A, a Lean type with 0 or 1 values, or a recursive type with no grounding order, has
no declaration, and the front end reports an error.

### 2.5 Terms: three formers (checked, for the newest block)

```lean
abbrev Ty.unfold (bs : Mems ks (k+1) 0) (j : Fin (k+1)) : Ty (k :: ks) :=
  Mems.instMember .there (fun i => .data (.here i)) bs j _   -- holes ↦ names, older ↦ weakened

| data_in  (j) : Atom Γ (Ty.unfold bs j) → Comp Sg Γ (.data (.here j))
| data_out (j) : Atom Γ (.data (.here j)) → Comp Sg Γ (Ty.unfold bs j)
| data_rec (ρ : Fin (k+1) → Ty (k :: ks)) (v : Atom Γ (.data (.here j)))
    (branches : ∀ i, Term Sg (Mems.instMember .there (fun i' => pair (.data (.here i')) (ρ i')) bs i _ :: Γ) (ρ i))
    (d : Dest J (ρ j) τ) : Term Sg Γ τ J
```

In the toy these are `dataIn`, `dataOut` and `dataRec`. They are A's `muIn`/`muOut`/`muRec`
with `Ty.unfold` filling holes with **names** (`.data (.here i)`) instead of `mu`-trees. The
unfolded body is again a closed type, so `data_out` is followed by the ordinary
`record_casesOn`/`taggedUnion_casesOn`. All three are structural and compute:

* `List Nat`: `sum [1,2,3] = 6`, `head? [7] = some 7`, `head? [] = none`, all by `rfl`;
* block 2 (three members: `LitExprS (Nat × Bool)`, `LitExprS (Bool × Nat)`, and
  `Rose := node (List Nat) (Array Rose)`) is folded by **one** `data_rec` with answer types
  `Nat × Bool`, `Bool × Nat`, `Nat`. `eval (swap (lit (true, 3))) = (3, true)` holds by `rfl`,
  and so does the rose-tree sum (`31`), whose branch calls block 1's fold `sum'` on its
  `List Nat` field.

*Older fields.* An `old t` field of a body is weakened into the current signature
(`Ty.map .there t`). Roll and unroll transport its values with `Ty.lift`/`Ty.lower`. These
are structural functions, not `Eq` casts: they are the identity on datatype values
(`.data r ↦ x`) and rebuild only the anonymous structure around them. So they compute by
`rfl`, but they do cost a traversal of records, unions and arrays inside an old field. A
avoids this cost with its `closed` constructor, and pays for it with a canonicity rule.

*Folding an older block with answers in the current signature* needs `data_rec` at any
`Ref`, not just the newest block. The generalisation takes a position `p` in the signature
and composes the transports along `p` (sketch, not checked). The toy covers the common case:
an older fold whose answer type is also older (`sum'` inside block 2).

*`data_brec`* is A's `mu_brec` with `Ty.below` declared as one extra block, the history
family, generated next to the block it annotates (sketch, not checked).

### 2.6 Canonical forms without `Ty.fix` (checked)

A needs `Ty.fix` because the *same* datatype can be written as many trees: members can be
reordered, and non-cyclic members can be inlined or not. The field of `LitExpr (Nat × Bool)`'s
`pair` must be literally the same tree as a stand-alone `LitExpr Nat`.

Under N a recursive type is a leaf `data r`, so two occurrences are equal exactly when the
names are equal. The names come from a cache, as in `#leanscript_get_ty` (§A.8.2 of
`WTypeTyProposal.md`):

* **`#leanscript_get_ty T`** finds the strongly connected component (SCC) of Lean type
  instances reachable from `T`, using the reachable-indices walk of A.5 for index-varying
  families. If the SCC has a cycle, the cache declares it **once** as a block: it computes
  the grounding order and marks the first grounded constructor as the base (A.4's rules,
  applied once per declaration instead of on every tree). Otherwise `T` stays structural
  (`record`/`union`/leaf).
* The result is stored as a generated `def`, so every later use of `T` is the same
  `.data r`. Because weakening is `rfl` on concrete names, a type from an older block is
  literally the same tree in a newer signature (checked:
  `(Ty.weaken listNat : Ty [2, 0]) = listNat₂` by `rfl`, and
  `Ty.unfold block₂ 2 = .record listNat₂ (.one (.array rose))` by `rfl`).

Type equality in terms is therefore `decide` on `Ty ks`, which is derived.

### 2.7 `LitExpr` and `Unfold` under N

* **`LitExpr α`** at a closed index: the reachable indices are computed as in A.5.
  * Without `swap` there is no cycle, so no declaration is made and `LitExpr (Nat × Bool)` is
    a structural `union`, exactly as in A.
  * With `swap`, the two indices form one block of two members, and `eval` is one `data_rec`
    with a different answer type per member (checked, `eval₂`).
  * An index that grows without bound still needs a size cap.
* **`Unfold α`**: still not a datatype (its `State : Type` field is a Σ over `Type`). But see
  §3.3: its *behaviour* is exactly a `List α` (checked), so the existential can be avoided
  for consumers that only step it.

### 2.8 Costs of N compared with A

| | A | N |
| :-- | :-- | :-- |
| indices on `Ty` | two (`n`, `g`) everywhere; closed = `Ty 0 0` | one (`ks`) on closed types; `n`, `g` only on bodies |
| canonical form | `Ty.fix` + `closed` rule, re-run on every tree | by name; grounding order computed once per declaration |
| body grammar | the full `Ty n g` (records/unions nested anywhere) | flat: `hole`/`old`/`array`/`fn` fields in one layer of constructors |
| signature | none: a type is self-contained | **`Δ : DSig ks` threads through** `Den`, `Term` (for `Ty.unfold`) and `Eval` |
| modularity | a type can be copied anywhere | a type is only meaningful with its `Δ`. A module that extends a signature has to weaken earlier terms (`Term.map`, with an evaluation lemma, sketch). Or the translator emits one `Δ` per program and shares nothing between programs |
| older types inside a body | `closed t`, definitional | `old t` + weakening; values pass through `Ty.lift`/`Ty.lower` (structural, computes, costs a traversal) |
| reading a type | self-describing | needs the signature to print or unfold `data r` |

**When to prefer N:** if canonicity (`Ty.fix`, `closed`) and the double index are what hurt in
A, and the translator already centralises Lean types in a cache (B's `#leanscript_get_ty`).
**When to prefer A:** if terms and types must be moved freely between modules without a
shared signature.

### 2.9 Migration plan for N

Each step builds on its own and is checked by `lake build` together with an `rg sorry` sweep.

1. `LeanScript/Ty/Ty.lean`: the mutual `Ty`/`Fields`/`Ctor`/`Ctors` over `ks`, `Ref`, with
   `DecidableEq`, `BEq`, `ReflBEq`, `LawfulBEq`, `Repr`; `Ty.map`/`Ty.weaken`. Delete
   `Ty/Shape.lean` (`TyShape`).
2. `LeanScript/Ty/Decl.lean` (new): `Fld`, `Flds`, `BCtor`, `BCtors`, `Alts`, `Decl`, `Mems`,
   `DSig`; `Ty.unfold`.
3. `LeanScript/Den.lean`: `Ty.den`, `DSig.refDen`, `Ty.lift`/`Ty.lower`, roll/unroll. Port
   `Two`, `Ty.pick`, `DSig.two`, `Ty.twoDen` and the corollaries from the toy. `Den/Rec.lean`,
   `Den/Family.lean` and `Den/PFunctor.lean` collapse into this file.
4. Delete `Ty/Wf.lean`, `Ty/WfFacts.lean`, `Ty/WfTactic*`, `Ty/TyWf.lean`, `Ty/TyWfIn.lean`.
   `Ctx ks := List (Ty ks)`.
5. `Expr/Term.lean`: index terms by `Δ`; remove the twelve recursive formers and the
   `…FoldK…` families; add `data_in`, `data_out`, `data_rec` (and `data_brec`), with
   `data_rec` taking a `Ref` into any block (§2.5). `Eval.lean` gets these cases.
6. `CtorFn/*` and `Deriving/*` become the cache: `#leanscript_get_ty` (declares SCCs, returns
   `Ty ks`), `#leanscript_get_ctor` (returns `data_in` of the payload), and
   `#leanscript_get_cases` (returns `data_out` followed by `…casesOn`).
7. `ToTerm/*`: one code path through the cache and `data_*`; `brecOn` maps to `data_brec`.
8. Tests: the per-binder suites merge into one `DataTest`. Add a two-block test in which a
   later block stores an older type in a field (as block 2 of the toy does).

**Status of the implementation (in `LeanScript/Nominal/`, built next to the old stack, which is
untouched):**

- Steps 1–3: done in `Nominal/Ty.lean`, `Nominal/Decl.lean`, `Nominal/Container.lean`,
  `Nominal/Den.lean`, `Nominal/Two.lean`, `Nominal/DenFacts.lean` (including
  `DSig.dataOut_dataIn` and `DSig.dataIn_dataOut`). `Ty/Shape.lean` and `Den/*` are not deleted,
  because the old stack still uses them.
- Step 4: not done; `Ty/Wf*`, `TyWf` are still used by the old `Term`, `ToTerm` and `CtorFn`.
- Step 5: done as a new direct-style term language `Nominal/Term.lean` with `Nominal/Eval.lean`
  (`data_in`, `data_out`, `data_rec` at any block); `data_brec` is not implemented.
- Step 6: done as the command `leanscript_signature` (`Nominal/Signature.lean`), which declares
  the SCCs once in grounding order and generates the constructors as term functions.
- Step 7: not done (porting `ToTerm/*`).
- Step 8: `TyTests/NominalTest.lean` (two blocks, the later one storing an older type),
  `TyTests/NominalSignatureTest.lean`, `TermTests/NominalTermTest.lean`.

---

## 3. Final coalgebra (`ν`): what it would and would not give

### 3.1 As a *replacement* for inductive types: no

Giving a Lean `inductive` the meaning of the greatest fixed point adds values Lean does not
have: `νX. Option (Nat × X)` contains the infinite colist `ones = 1 :: ones`. Then:

* **Folds disappear.** No `sum : CoList Nat → Nat` satisfies `sum nil = 0` and
  `sum (x :: xs) = x + sum xs`. Applied to `ones` these give `sum ones = 1 + sum ones`
  (checked: `CoList.no_sum`). So `mu_rec`/`data_rec`, and every translation of structural
  recursion, would have no meaning.
* **The translation is no longer faithful.** `Den (List Nat)` would be strictly bigger than
  `List Nat`, so the correctness lemmas of the translator (`eval` agrees with the Lean
  function) could not even be stated for list-consuming functions.
* **Equality of values is bisimilarity**, which is undecidable. This does not affect
  `DecidableEq` on *types*, but it does affect every lemma that compares values.

### 3.2 As an *extra* `codata` form: possible, with a different hardening

A block could be marked `codata`: its meaning is an M-type, with formers `codata_out`
(observe one layer) and `codata_corec (seed : Atom Γ σ) (step : Term Sg (σ :: Γ) (unfold[σ]))`.
The seed's type `σ` is a closed `Ty` chosen at the term, so **no existential type is needed**:
the "state" is ordinary term-level data. The properties change as follows:

| quality | inductive (A / N) | `codata` |
| :-- | :-- | :-- |
| terminating elimination | `fold`, structural | only `out`. Productivity of `corec` is by typing (`step` returns exactly one layer) |
| no empty-like type | grounding index | **free**: every shape has a value, so `corec` from any value builds a tree. No grounding order is needed |
| no unit-like type | ≥ 2 values per layer + grounding | the grounding index must be **replaced**, not dropped: `νX. X` has one point (checked, `IdNu.subsingleton`), and so does `νX. X × X` (not checked). A sufficient typed rule: every cycle through a block passes a guard that has ≥ 2 shapes (a union, an `array`, or an `old` field). Sketch, not checked |
| construction in Lean without Mathlib | `IW`, one inductive | M-types are not primitive in Lean. Mathlib builds them from approximations with `cast`s. A cast-free representation exists per shape (colists as prefix-closed sequences, checked: `CoList.corec`/`dest` compute by `rfl`), but a general one for the whole `Ty` grammar is future work |
| source language | Lean `inductive` | Lean has no coinductive `Type`s to translate from. So `codata` would only serve LeanScript-native streams, or the behavioural reading of `Unfold` below |

### 3.3 `Unfold` without an existential: its behaviour is a list (checked)

The final-coalgebra view says what an `Unfold` *is* to an observer that only steps it: the
colist `CoList.corec u.step u.seed`. The `State` type is gone. Because of the erased
`decreasing` field, that colist is finite, and it is exactly a list computed without fuel:

```lean
def Unfold.behaviour (u : Unfold α) : CoList α := CoList.corec u.step u.seed
def Unfold.toList    (u : Unfold α) : List α   := go u (u.measure u.seed + 1) u.seed  -- Nat recursion
theorem Unfold.behaviour_finite    (u : Unfold α) : ∃ n, (behaviour u).1 n = none
theorem Unfold.behaviour_eq_toList (u : Unfold α) (n : Nat) : (behaviour u).1 n = (toList u)[n]?
example : toList countdown = [2, 1, 0] := rfl
```

So a consumer of `Unfold α` that only steps from the seed (`toList`, `take`, `fold`) can be
translated by first producing a `List α` (a declared datatype under N, a `mu` under A), with
**no existential type and no `Twin`/`Seal`**. This fits your decision not to support
existentially typed inductives. **Caveat:** a Lean function can observe more than the
behaviour, for example `u.measure u.seed`, or a `State` value it inspects directly. Such
consumers are not invariant under this reading and must still be refused, so the translator
would have to check syntactically that only `step` is used from `seed`. The theorem above is
what makes the check sufficient.

---

## 4. Decisions needed from you

1. **N or A?** They have the same guarantees (§0). N trades `Ty.fix` and the double index for a
   signature `Δ` threaded through `Den`, `Term` and `Eval`.
2. Under N: **one signature per program** (no weakening of terms, no sharing between
   programs), or **a growing signature per module** (sharing, plus `Term.map` and its
   evaluation lemma)?
3. Under N: `data_rec` at any `Ref` (general, §2.5), or only at the newest block, with the
   translator ordering declarations so that folds are always over the newest block?
4. Under N: keep `wrap` members (one constructor, one field, e.g. `Rose`), or require the front
   end to fold them into their use sites? Keeping them is simpler. Folding them makes
   declarations smaller, but needs a canonicity rule again.
5. Final coalgebra: skip it (recommended), or add `codata` blocks (§3.2) for LeanScript-native
   streams?
6. `Unfold`: adopt the behavioural reading (§3.3) for step-only consumers, or keep refusing
   `Unfold` entirely for now?
