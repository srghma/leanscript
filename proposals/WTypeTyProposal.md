# Proposal: W-types directly in `Ty`, with a cached constructor API

> **Status: proposal only.** Nothing in `LeanScript/`, `TyTests/` or `TermTests/` has changed.
>
> **Hardened revision.** `Ty` no longer admits unit-like or empty-like types: every closed
> type has at least two values, *by construction*, with no fuel, no measure and no
> well-formedness predicate. See §H and the rewritten §A.1–§A.4.
>
> **Revision 3.** The former *Proposal B* (no recursive types at all) is **withdrawn**: it
> cannot express recursive user types, which LeanScript must support. Its one idea worth
> keeping, a cached `#leanscript_get_ctor` (and `#leanscript_get_ty`), is now part of this
> proposal as §A.8. `Array`, `List` and "a length and a function on `Fin length`" are now
> three distinct `Ty` formers (`array`, `list`, `finFn`); a closed `array` means Lean's
> `Array`, and the rose trees `node : List Rose → Rose`, `node : Array Rose → Rose` and
> `node : (m : Nat) → (Fin m → Rose) → Rose` are three different, accepted types (§A.2,
> checked). §A.9 lists the Lean types that Lean accepts and that `Ty` still cannot represent.
>
> The claims in §H and §A.1–§A.5 marked **(checked)** are compiled at toy scale in
> `proposals/WTyToy.lean`. That file has no imports and is not part of the Lake build, so it
> is checked with the bare compiler:
>
> ```
> lean proposals/WTyToy.lean
> ```
>
> It compiles with no errors, no warnings and no `sorry`. All other Lean in this note is a
> sketch and has **not** been compiled.
>
> The two targets are the same as in `proposals/IndexedExistentialFamilyProposal.md`:
>
> ```lean
> inductive LitExpr : Type → Type 1 where
>   | lit  {α : Type} (x : α) : LitExpr α
>   | pair {α β : Type} (a : LitExpr α) (b : LitExpr β) : LitExpr (α × β)
>
> structure Unfold (α : Type) where
>   State      : Type
>   seed       : State
>   step       : State → Option (State × α)
>   measure    : State → Nat
>   decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x
> ```

The proposal has two parts:

* **One W-type binder (§A.1–§A.7).** `recTaggedUnion`, `recObject`, `recAlias` and
  `mutualRecursiveFamily` become a single constructor `Ty.mu`, an *indexed W-type*. The
  twelve recursive term formers become three (`mu_in`, `mu_out`, `mu_rec`), plus an optional
  fourth (`mu_brec`). Scoping is enforced by the type of `Ty`, so `TyWf` goes away.
* **A cached constructor API (§A.8).** `TyShape` is merged into `Ty`, and the class
  `LeanScriptTyWf` is replaced by two cached elaborators, `#leanscript_get_ty` and
  `#leanscript_get_ctor`. Every use of a Lean constructor goes through `#leanscript_get_ctor`,
  which caches the generated function (built from `mu_in` for recursive types).

§A.9 answers which Lean types still have no `Ty`, and §C summarises and lists the decisions I
need from you.

---

## H. Hardening: no unit-like and no empty-like types (checked)

The previous revision of this note let `Ty` describe types with one value or none. In the
toy, `.taggedUnion (.cons .nil .nil)` denoted `PUnit ⊕ PEmpty`, and `μX. X` denoted an empty
W-type. This revision rules both out **by the shape of `Ty` itself**:

| requirement | how it is enforced |
| :-- | :-- |
| no unit-like `Ty` | there is no unit type; a record has **≥ 2 fields**, a union **≥ 2 constructors** (the containers `Fields`, `Ctors`, `Alts` have no smaller form); every primitive has ≥ 2 values |
| no empty-like `Ty` | every scope index carries a **grounding** count `g`: `Ty n g` is a type in a scope of `n` recursive holes, of which the first `g` are known to have values. A hole may be used *directly* (`var i (h : i < g)`) only if grounded; any hole may be used under a **guard** (an `array` element, or a union constructor other than its *base* constructor). Member `j` of a `mu` is a `Ty (k+1) j`, so it can rely directly only on members `< j` |
| no unit-like or empty-like `Term` | a context, a term and a signature speak about `Ty 0 0` only, so every term has a type with ≥ 2 values. A constructor without fields denotes `Option _`/`Bool`, not `PUnit ⊕ _`, so building or matching it takes/binds **no payload**: there is no `PUnit.unit` term anywhere, nor a `PEmpty` branch |
| `Ty.Den` never returns a unit-like or empty-like type | **theorem** `Ty.twoDen : (t : Ty 0 0) → Two (Ty.Den t)`: two values and a Boolean test telling them apart, by structural recursion on `t`. Corollaries `Ty.den_nonempty`, `Ty.den_not_subsingleton`, `Ty.den_exists_ne` |
| no fuel, no measures | `Ty.twoDen`, `Ty.Den`, `muIn`, `muOut`, `muRec` are all structural. The one place that builds values member by member (`IW.build`, inside a `mu`) is structural recursion on a `Nat` bound equal to the member's index: member `j` is built from members `< j`, which is exactly what the grounding index promises |

What no longer typechecks (pinned in the toy with `#guard_msgs`):

```lean
.mu 0 [.var 0 _] 0                   -- μX. X          : `0 < 0` is false
.mu 0 [.record .nat [.var 0 _]] 0    -- μX. Nat × X    : a record field is a grounded position
.union (.one .nullary)               -- the old unitTy : there is no one-constructor union
```

What still typechecks, and what `Ty.Den` returns (all `rfl` in the toy):

| type | `Ty.Den` / unfolded body |
| :-- | :-- |
| two constructors without fields | `Bool` |
| `none \| some Nat` | `Option Nat` (not `PUnit ⊕ Nat ⊕ PEmpty`) |
| `List Nat` = `μX. nil \| cons Nat X` (`nil` is the base) | unfolds to `Option (Nat × List)` |
| rose tree `node : List Rose → Rose` = `μX. list X` (no base constructor, but `list` guards `X`) | unfolds to `List RoseL` |
| rose tree `node : Array Rose → Rose` = `μX. array X` | unfolds to `Array RoseA` |
| rose tree `node : (m : Nat) → (Fin m → Rose) → Rose` = `μX. finFn X` | unfolds to `(m : Nat) × (Fin m → RoseF)` |
| a closed `array nat` / `list nat` / `finFn nat` | `Array Nat` / `List Nat` / `(m : Nat) × (Fin m → Nat)` |
| `LitExprS` at `Nat × Bool` / `Bool × Nat` (two members, `lit` is each member's base) | `(Nat × Bool) ⊕ ((Nat × Bool) ⊕ member₁)` |

The two values the proof picks for `List Nat` are `[]` and `[0]` (checked by `rfl`). The
three rose trees are three different `Ty`s (checked by `decide`), each with a node count by
`mu_rec` that computes by `rfl`.

**Consequence for the translator.** A Lean type whose least fixed point is empty
(`inductive Bad | mk : Bad → Bad`) or has one point (`Unit`, `PUnit`, `True`-like structures)
has **no** `Ty`. Today's point counting (§A.8.1) already refuses 0 and 1 points and erases unit
fields; the difference is that this is now forced by the type of `Ty` instead of being a
convention of the front end. For recursive types the front end must find a grounding order
(§A.4); if there is none, the Lean type is empty and translation is refused with an error.

---

## 0. The current design, briefly

| piece | today |
| :-- | :-- |
| recursive binders in `Ty` | `recTaggedUnion`, `recObject`, `recAlias`, `mutualRecursiveFamily`, plus the leaves `self` and `familyMember i` |
| well-formedness | `Ty.Wf` (`LeanScript/Ty/Wf.lean`) checks scope, "really recursive", "every member mentioned", positivity and inhabitation. It is carried by `TyWf`, whose proof defaults to `by ty_wf` |
| scoped trees | `TyWfIn n`, used by 42 files |
| term formers for recursive types | `recTaggedUnion_{casesOn, casesOnWithDefault, rec, mk}`, `recObject_{casesOn, rec, mk}`, `recAlias_{casesOn, rec, mk}`, `mutualRecursiveFamily_{casesOn, casesOnWithDefault, rec, mk}`. Each fold has its own depth-`k` case tree (`TaggedUnionFoldKCases`, `FoldKBranch`, `FamilyFoldKCases`, `SelfField`, `OuterSelfField`, …) |
| denotation | already a W-type: `PFunctor.mu` (Mathlib's `WType`) for the three lone binders, and the project's own indexed W-type `FamW` for families (`LeanScript/Den.lean`, `LeanScript/Den/IPFunctor.lean`) |
| Lean type → tree | the class `LeanScriptTyWf` and `deriving LeanScriptTyWf` |
| constructors | `#leanscript_ctor I c` / `#leanscript_layout I c` (`LeanScript/CtorFn.lean`), already cached in an environment extension |

The denotation is already "one W-type per binder". Proposal A makes the *syntax* match the
denotation: one binder, whose meaning is one indexed W-type.

---

# Part A: one W-type binder

## A.1 The new `Ty` (hardened)

```lean
mutual
/-- A type in a scope with `n` recursive holes, the first `g` of which are *grounded*
    (known to have values).  A closed type is a `Ty 0 0`. -/
inductive Ty : Nat → Nat → Type where
  /-- A grounded hole: member `i` of the innermost `mu`, used directly.  Needs `i < g`. -/
  | var          {n g} (i : Fin n) : i.val < g → Ty n g
  /-- A closed type used inside a scope.  Weakening, as a constructor (§A.4). -/
  | closed       {n g} : Ty 0 0 → Ty n g
  -- the former `TyShape`, merged in (every primitive has ≥ 2 values; there is no `unit`):
  | prim         {n g} : LeanPrimTy → Ty n g
  /-- The domain is **closed** (strict positivity, by typing).  The codomain stays grounded:
      `Nat → X` has a value only if `X` has one. -/
  | fn           {n g} : Ty 0 0 → Ty n g → Ty n g
  /-- Lean's `Array`.  The element is **guarded**: `#[]` is always a value, so it may use
      every hole.  Compiled to a JS array. -/
  | array        {n g} : Ty n n → Ty n g
  /-- Lean's `List`, guarded like `array`.  Also compiled to a JS array. -/
  | list         {n g} : Ty n n → Ty n g
  /-- A length and a function on `Fin length`, `(m : Nat) × (Fin m → A)`, guarded like
      `array`.  What a constructor `node : (m : Nat) → (Fin m → T) → T` becomes (§A.2). -/
  | finFn        {n g} : Ty n n → Ty n g
  | thunk        {n g} : Ty n g → Ty n g
  | lazy         {n g} : Ty n g → Ty n g
  /-- At least three constructors without fields. -/
  | enum         {n g} : LeanEnumSchema → Ty n g
  /-- At least two fields, all grounded positions. -/
  | record       {n g} : Ty n g → Fields n g → Ty n g
  /-- At least two constructors; one of them, the *base*, is grounded, the others guarded. -/
  | union        {n g} : Alts n g → Ty n g
  /-- **The** recursive binder: an indexed W-type with `k + 1` members.  Member `j`'s body is a
      `Ty (k + 1) j`: it may use members `< j` directly and any member under a guard.  The
      bodies cannot see the enclosing scope. -/
  | mu           {n g} (k : Nat) (bodies : Mems (k + 1) 0) (sel : Fin (k + 1)) : Ty n g

/-- One or more fields. -/
inductive Fields : Nat → Nat → Type where
  | one  {n g} : Ty n g → Fields n g
  | cons {n g} : Ty n g → Fields n g → Fields n g
/-- A constructor: no fields, or one or more fields (there is no unit payload). -/
inductive Ctor : Nat → Nat → Type where
  | nullary {n g} : Ctor n g
  | fields  {n g} : Fields n g → Ctor n g
/-- Two or more guarded constructors. -/
inductive Ctors : Nat → Type where
  | two  {n} : Ctor n n → Ctor n n → Ctors n
  | cons {n} : Ctor n n → Ctors n → Ctors n
/-- Two or more constructors, exactly one of which is marked as the grounded base. -/
inductive Alts : Nat → Nat → Type where
  | two₁  {n g} : Ctor n g → Ctor n n → Alts n g      -- base first, of two
  | two₂  {n g} : Ctor n n → Ctor n g → Alts n g      -- base second, of two
  | here  {n g} : Ctor n g → Ctors n → Alts n g       -- base here, ≥ 2 more follow
  | there {n g} : Ctor n n → Alts n g → Alts n g      -- a guarded constructor before the base
/-- The bodies of members `g, g+1, …, n-1`; member `g`'s body is a `Ty n g`. -/
inductive Mems : Nat → Nat → Type where
  | nil  {n}   : Mems n n
  | cons {n g} : Ty n g → Mems n (g + 1) → Mems n g
end

/-- A closed type: what a context, a term and a signature speak about. -/
abbrev ClosedTy := Ty 0 0
```

The toy has exactly this shape, with `nat`/`bool` for `prim` and without `thunk`, `lazy` and
`enum` (they add nothing new: `thunk`/`lazy` are grounded like `fn`'s codomain, `enum` is a
leaf with ≥ 3 values).

**Why two indices, and why only arithmetic in proofs.** An earlier attempt indexed a body by
`(grounded, ungrounded)` counts, with scope `g + e`. The member list then needs the scopes
`g + (e+1)` and `(g+1) + e` to agree, which they do not definitionally, so `Fin` casts creep into
`Ty.Den`. With the scope `n` fixed and the grounding `g` counting up along `Mems`, every index
in a type is a plain variable or `n`; arithmetic only appears in proofs (`i < g`, `g + i < n`),
which are irrelevant, so nothing needs a cast (checked).

**What grounding means.** `Ty n g` is a type that has a value as soon as holes `0 … g-1` have
values, whatever holes `g … n-1` are. That is the invariant the constructors keep:

* `var i h` needs `i < g`;
* `fn`, `thunk`, `lazy`, `record` and a union's base constructor keep the same `g` for their
  parts — they have a value only if their parts do;
* `array`, `list`, `finFn` and the non-base constructors of a union switch to `Ty n n` — they
  have a value whatever their parts are (`#[]`; `[]`; length `0`; a different constructor);
* member `j` of a `mu` is a `Ty (k+1) j`.

So member `0` has a value outright, member `1` as soon as member `0` does, and so on: every
member of every `mu` has a value. Adding "at least two fields / constructors" gives two
distinct values (§A.2, `Ty.twoDen`).

**Weakening between groundings.** A `Ty n g` can be used where a `Ty n g'` with `g ≤ g'` is
expected (more holes known to have values). This is a structural function `Ty.ground` (sketch, not in the toy),
needed for example to put a grounded constructor in a guarded position. It is not a
constructor, so it adds no second tree for the same type.

**Why the containers must be mutual (checked).** The obvious definition nests the schemas
(`taggedUnion : LeanTaggedUnionSchema (Ty n) → Ty n`, or just `List (List (Ty n))`). The
kernel refuses that: *"invalid nested inductive datatype 'List', nested inductive datatypes
parameters cannot contain local variables"*. The index `n` is a local variable of the
constructor. So the schemas have to be restated as mutual inductives indexed by `n`. The
restatement is mechanical: same shapes, same "at least two" guarantees. With mutual
containers the kernel accepts the type, and `deriving DecidableEq` works for it (both are
checked in the toy). `BEq`, `ReflBEq` and `LawfulBEq` then follow from `DecidableEq` as
today.

The generic schemas `LeanRecordSchema α` and `LeanTaggedUnionSchema α` can stay for the
other things that use them (`Den`, catalogues). A pair of `toSchema`/`ofSchema` functions
connects the two forms.

*The unindexed fallback of the previous revision is withdrawn.* It kept `Ty` unindexed and
gave an out-of-scope `var` the junk meaning `PEmpty`. That is exactly an empty-like type, and
an unindexed `Ty` cannot express grounding, so it cannot rule out `μX. X` either. Hardening
needs the indices.

### What happens to each `Ty.Wf` condition

| `Ty.Wf` condition today | under A |
| :-- | :-- |
| **scope** (`self` / `familyMember i` only inside a binder, `i` in range) | by typing: `var (i : Fin n)`, and a closed type is `Ty 0 0` |
| **positivity** (no occurrence in a function domain) | by typing: `fn : Ty 0 0 → Ty n g → Ty n g` |
| **counts** (enum ≥ 3, record ≥ 2, union ≥ 2) | by the container types (`Fields` + one more field, `Alts`/`Ctors` have no one-constructor form). Unions whose constructors all lack fields are allowed (two of them denote `Bool`) |
| **really recursive** / **every member mentioned** | dropped as a typing condition. A `mu` whose body never mentions itself is a legal, if non-canonical, tree: `mu 0 [b] 0` denotes the same thing as `b`. Canonical form moves to the smart constructor `Ty.fix` (§A.4) |
| **inhabitation** (`μX. X` refused) | **by typing**, via the grounding index (§A.1): `μX. X`, `μX. Nat × X`, `μX. Nat → X` do not typecheck. Stronger than today: every closed type has **two** distinguishable values (`Ty.twoDen`, checked). Nothing is computed, so there is no fuel and no measure |

So `TyWf`, `TyWfIn`, `Ty.Wf`, `Ty.WfIn`, `ty_wf` and `LeanScript/Ty/WfTactic/*` all go away.
Contexts, terms and signatures are indexed by `Ty 0 0`. The only proofs left in a tree are the
`i < g` of each `var`, closed by `by decide` (or by the smart constructor).

### Old → new

| old | new |
| :-- | :-- |
| `Ty.self` | `var 0 _` inside a `mu 0 …`, in a guarded position (or in member `j > 0` directly) |
| `Ty.familyMember i` | `var i _` |
| `recTaggedUnion l` | `mu 0 [union l'] 0`, where `l'` marks a constructor that does not mention the type as the base |
| `recObject fs` | `mu 0 [record fs] 0`; every occurrence of the type must sit under an `array` or a guarded union (e.g. `children : Array Self`, `next : Option Self`), otherwise the type is empty and refused |
| `recAlias b` | `mu 0 [b] 0`, same condition on `b` |
| `mutualRecursiveFamily f` (member `j` of `k + 1`) | `mu k [body₀, …, body_k] j`, members in a grounding order (§A.4); a `.ctors` member is a `union`, a `.record` member a `record`, an `.alias` member its body |
| `LeanFamMemberSchema`, `LeanMutualRecFamily` | gone: member `j` is just a `Ty (k + 1) j` |
| `TyShape α` | gone: merged into `Ty` |

## A.2 Denotation: the indexed W-type, structurally (checked)

```lean
structure IPF (n : Nat) : Type 1 where            -- today's `IPFunctor`, with `tgt : … → Fin n`
  A : Type
  B : A → Type
  tgt : (a : A) → B a → Fin n

inductive IW {k} (P : Fin k → IPF k) : Fin k → Type where   -- today's `FamW`
  | mk (i : Fin k) (a : (P i).A) (f : (b : (P i).B a) → IW P ((P i).tgt a b)) : IW P i

-- a constructor without fields adds `Option`, never `PUnit ⊕ _`
def IPF.consC : Option (IPF n) → IPF n → IPF n     -- none, d ↦ opt d;  some c, d ↦ sum c d
def IPF.twoC  : Option (IPF n) → Option (IPF n) → IPF n
  -- none, none ↦ const Bool;  none, some d ↦ opt d;  some c, none ↦ opt c;  some c, some d ↦ sum c d

mutual
def Ty.toIPF : Ty n g → IPF n                      -- a hole is a position, a shape is a value
  | .var i _     => ⟨PUnit, fun _ => PUnit, fun _ _ => i⟩
  | .closed t    => .const (Ty.toIPF t).A
  | .fn a b      => .fn (Ty.toIPF a).A (Ty.toIPF b)
  | .array t     => .array (Ty.toIPF t)            -- shapes `Array A`
  | .list t      => .list (Ty.toIPF t)             -- shapes `List A`
  | .finFn t     => .finFn (Ty.toIPF t)            -- shapes `(m : Nat) × (Fin m → A)`
  | .record t fs => .prod (Ty.toIPF t) (Fields.toIPF fs)
  | .union u     => Alts.toIPF u
  | .mu _ bs s   => .const (IW bs.fam s)           -- bs.fam j := Mems.member bs j _
  …
def Fields.toIPF : Fields n g → IPF n              -- `one t ↦ toIPF t`: no trailing `PUnit`
def Ctor.toIPF   : Ctor n g → Option (IPF n)       -- `nullary ↦ none`
def Ctors.toIPF  : Ctors n → IPF n                 -- by `twoC` / `consC`
def Alts.toIPF   : Alts n g → IPF n                -- by `twoC` / `consC`
def Mems.member  : Mems n g → (i : Nat) → g + i < n → IPF n   -- body of member `g + i`
end

abbrev Ty.Den (t : Ty 0 0) : Type := (Ty.toIPF t).A
```

This is today's `Ty.toIPF` / `FamW`, with one simplification: every binder is a family, so
the three unary `PFunctor.mu` cases go away. For `k = 0`, `IW` over one sort is equivalent to
Mathlib's `WType` (`IW P 0 ≃ WType (P 0).B`). If you want Mathlib's `WType` itself to appear,
that equivalence is a lemma. It is not part of the definition, because two definitions would
break the definitional equations the evaluator relies on.

**No unit and no empty in the meaning.** `PUnit` occurs only as the shape of a hole inside a
container (a hole has one shape and one position), and `PEmpty` only as the position set of
a leaf; neither is ever the meaning of a closed type. A field list's meaning is `A₁ × … × Aₘ`
without a trailing `PUnit`, and a union's is built from `⊕`, `Option` and `Bool` without a
trailing `PEmpty`.

**`Mems.member` must be defined mutually** with `Ty.toIPF`. The more direct
`fun i => Ty.toIPF (bs.get i)` is not structural, because `bs.get i` is not a syntactic
subterm. Because of this, `mu_in` and `mu_out` go through `Mems.rollMember` /
`Mems.unrollMember`, which recurse on the family and the index together. The result is that
**no cast** is needed anywhere (checked).

### Containers: `array`, `list` and `finFn` are three types (checked)

A Lean constructor whose recursive occurrence sits in an `Array` or a `List` is accepted as
is, and the translator keeps the container: `node : Array Rose → Rose` is `μX. array X`,
`node : List Rose → Rose` is `μX. list X`. Both are compiled to a JS array (which may be
empty: that is the guard). A constructor `node : (m : Nat) → (Fin m → Rose) → Rose` is a
**different** type, `μX. finFn X`, and stays function-based: if a user wants a function-based
tree, they write that one. So the three formers are never identified (`array nat ≠ finFn nat`,
checked by `decide`).

Their meanings, as containers, are

```lean
def ListPos (c : IPF n) : List c.A → Type      -- positions of a list of shapes, in order
  | []      => PEmpty
  | a :: as => c.B a ⊕ ListPos c as

def IPF.list  (c : IPF n) : IPF n := ⟨List c.A,  ListPos c,                  ListPos.tgt c⟩
def IPF.array (c : IPF n) : IPF n := ⟨Array c.A, fun s => ListPos c s.toList, …⟩
def IPF.finFn (c : IPF n) : IPF n := ⟨(m : Nat) × (Fin m → c.A), fun s => (i : Fin s.1) × c.B (s.2 i), …⟩
```

so a closed `array nat` means `Array Nat`, `list nat` means `List Nat`, and `finFn nat` means
`(m : Nat) × (Fin m → Nat)` (all `rfl`). Positions are defined by structural recursion on the
list, so rolling and unrolling a list or an array (`listRoll`/`listUnroll`) needs no cast, and
`mu_out (node cs) = cs` holds for lists and arrays (checked).

**What the user sees is always the Lean container.** Unfolding `μX. array X` gives
`Ty.inst (array (var 0)) (fun _ => μX. array X) = array (μX. array X)`, whose meaning is
`Array Rose`. So `mu_in` takes an `Array Rose`, `mu_out` returns an `Array Rose`, and a
`mu_rec` branch receives an `Array (Rose × ρ)` (checked: `RoseA.size (node #[node #[], node
#[node #[]]]) = 4` by `rfl`; the same for `List` and for `finFn`).

**Inside, the node of a recursive tree still stores its children by position.** The meaning
of the `mu` itself is the indexed W-type `IW`, whose node holds a shape (`Array PUnit` for the
rose tree) and a function from positions to children. It cannot be a Lean nested inductive
with a real `Array` of children: Lean's kernel refuses nested occurrences under an index,
*"invalid nested inductive datatype 'Array', nested inductive datatypes parameters cannot
contain local variables"* (checked in
`proposals/UnrepresentableLeanTypes.lean`). This is a property of the Lean-side model only. `mu_in`/`mu_out` convert, the
evaluator never exposes it, and the JS backend is free to (and should) store children in a
JS array.

### Two values of every type (checked)

```lean
structure Two (α : Type) where
  x : α
  y : α
  d : α → Bool          -- a test that tells them apart
  dx : d x = true
  dy : d y = false

def Ty.twoDen (t : Ty 0 0) : Two (Ty.Den t)
theorem Ty.den_nonempty         (t : Ty 0 0) : Nonempty (Ty.Den t)
theorem Ty.den_not_subsingleton (t : Ty 0 0) : ¬ ∀ x y : Ty.Den t, x = y
theorem Ty.den_exists_ne        (t : Ty 0 0) : ∃ x y : Ty.Den t, x ≠ y
```

`Ty.twoDen` is **data**, computed by structural recursion on the type from two mutual
functions over open types (in the toy they use only `propext` and `Quot.sound`):

* `Ty.inh (t : Ty n g) X : (∀ i < g, X i) → (toIPF t).Obj X` — a value from values of the
  grounded holes. `array` gives `#[]`, a union its base constructor, and a hole outside `g` is
  never asked for.
* `Ty.two (t : Ty n g) X : (∀ i, X i) → (∀ i < g, Two (X i)) → Two ((toIPF t).Obj X)` — two
  values: a hole passes on its two values, `fn` two constant functions (the domain is closed,
  so it has a value), `array` `#[]` and `#[v]`, `list` `[]` and `[v]`, `finFn` lengths `0`
  and `1`, a record its first field's two values, a union two different tags.
* for a `mu`, `IW.build` makes a value of every member, member `j` from members `< j`
  (structural recursion on a `Nat` bound, which is exactly the grounding order), first with
  `Ty.inh`, then, with all members now known to have values, again with `Ty.two`.

The test `d` is what makes this compose without decidable equality on values: for a record
it looks at the first field, for a function it calls it at a fixed argument, for an array it
checks emptiness, for a union it checks the tag.

## A.3 Terms: three formers instead of twelve

Unfolding is instantiation of the holes by the members themselves:

```lean
def Ty.inst : Ty n g → (Fin n → Ty 0 0) → Ty 0 0  -- stops at `closed` and at a nested `mu`
abbrev Ty.unfold (bs : Mems (k+1) 0) (j : Fin (k+1)) : Ty 0 0 :=
  Mems.instMember bs j _ (fun i => .mu k bs i)
```

`Ty.inst` lands in `Ty 0 0`, so an unfolded body is again a type with two values. It is only ever used to put closed types into holes, so
`inst (closed t) σ = t` holds **by definition** (checked). This is why weakening is a
constructor and not a function (§A.4).

### The formers

```lean
-- Comp: the one introduction form of every recursive type
| mu_in  {Γ k} (bs : Mems (k+1) 0) (j : Fin (k+1)) :
    Atom Γ (Ty.unfold bs j) → Comp Sg Γ (.mu k bs j)
-- Comp: take one layer off
| mu_out {Γ k} {bs : Mems (k+1) 0} {j : Fin (k+1)} :
    Atom Γ (.mu k bs j) → Comp Sg Γ (Ty.unfold bs j)
-- Term: the one fold (a paramorphism), with one answer type per member
| mu_rec {Γ k τ} {J} {bs : Mems (k+1) 0} {j : Fin (k+1)}
    (ρ : Fin (k+1) → Ty 0 0)                                  -- answer type of each member
    (v : Atom Γ (.mu k bs j))
    (branches : MuBranches Sg Γ bs ρ)                          -- one per member, below
    (d : Dest J (ρ j) τ) : Term Sg Γ τ J

/-- Branch `i` binds member `i`'s body with every hole `i'` filled by the pair
    `(subvalue, answer at it)`, and answers `ρ i`. -/
inductive MuBranches (Sg) (Γ : Ctx) (bs : Mems (k+1) 0) (ρ : Fin (k+1) → Ty 0 0) : Type 1
  -- = for each i : Fin (k+1),
  --   Term Sg (Mems.instMember bs i _ (fun i' => pair (.mu k bs i') (ρ i')) :: Γ) (ρ i)
```

What each old former becomes:

| old | new |
| :-- | :-- |
| `recTaggedUnion_mk`, `recObject_mk`, `recAlias_mk`, `mutualRecursiveFamily_mk` | `mu_in` of a `taggedUnion_mk` / `record_mk` / the body itself |
| `recTaggedUnion_casesOn`, `mutualRecursiveFamily_casesOn` | `let u := mu_out v; taggedUnion_casesOn u …` |
| `…_casesOnWithDefault` | `mu_out`, then `taggedUnion_casesOnWithDefault` |
| `recObject_casesOn`, `recAlias_casesOn` | `mu_out`, then `record_casesOn`, or nothing for an alias |
| `recTaggedUnion_rec`, `recObject_rec`, `recAlias_rec`, `mutualRecursiveFamily_rec` at `k = 0` | `mu_rec` |
| the depth-`k` versions (`FoldKCases`, `FoldKBranch.deep/deepOuter`, `SelfField`, `OuterSelfField`, `recObjectRecBinders`, `recAliasAnswerTree`, `famAnswerBinders`, …) | `mu_brec` (below), or `mu_rec` with a tupled answer type |

So all the non-recursive eliminators are reused unchanged for recursive types. The
"unfolded schema" helpers (`recTaggedUnionUnfold`, `recObjectUnfold`, `recAliasUnfold`,
`TyWfIn.unfoldFam`) collapse into the single `Ty.unfold`.

Nested containers also stop being special. A member `Array (var 0 _)`, `List (var 0 _)` or (in
member `j ≥ 2`) `Nat → var 1 _` is just a body, and `mu_rec`'s branch receives an
`Array (pair (mu …) ρ)`, a `List (pair (mu …) ρ)` or a `Nat → pair (mu …) ρ`, because
instantiation goes through `array`, `list` and `fn` codomains. The separate
`famAnswerBinders` treatment is no longer needed.

### Termination and correctness by construction

* `Term.eval (mu_rec …)` is `IW.fold`: structural recursion on the W-tree of the value
  (checked). The branch is **given** the answer at each subvalue and never calls anything, so
  there is no fuel, and a term cannot diverge. The argument is the same as for today's
  `WType.memoFold`.
* `mu_in` and `mu_out` are `IW.mk` composed with `rollMember`, and a match on `IW.mk`
  composed with `unrollMember`. Both are structural, and both reduce by `rfl` on closed
  values (checked: `sum [1,2,3] = 6` and `head? [7] = some 7` hold by `rfl`).
* A term is well-typed by construction: `Term` is indexed by `Ty 0 0`, and `Ty 0 0` has no
  ill-scoped trees.
* **No unit-like or empty-like term.** Every `Atom`, `Comp` and `Term` has a type `τ : Ty 0 0`,
  and `Ty.twoDen τ` gives two distinguishable values, so no term lives in a one-point or empty
  type. The branch binders of `mu_rec`/`mu_brec` are instantiated bodies, again `Ty 0 0`. A
  constructor without fields is introduced by `taggedUnion_mk` **without** a payload atom and
  eliminated by a `casesOn` branch that binds **nothing** (its meaning is the `none` of an
  `Option` or a `Bool`, checked: `nil = muIn listBody 0 none`), so the old `PUnit.unit`
  payloads and `PEmpty` fall-through branches have no counterpart. Eliminators never need a
  default value, because no type is empty.

### Deeper look-back: `mu_brec` (optional; sketch, not checked)

Today's depth-`k` folds let a branch read answers `k + 1` layers down (`fib`). Lean's own
structural recursion (`brecOn`) gives **every** layer. Both are covered by one former whose
branch receives the whole *history*. The history is itself a `mu`: the same family with
every node annotated by its answer.

```lean
/-- Member `i` of the history family: the answer at the node, and the node.  The record keeps
    member `i`'s grounding (`closed` is grounded, the body is a `Ty (k+1) i`). -/
def Ty.below (bs : Mems (k+1) 0) (ρ : Fin (k+1) → Ty 0 0) : Mems (k+1) 0 :=
  bs.mapIdx fun i b => .record (.closed (ρ i)) (.one b)

| mu_brec {Γ k τ} {J} {bs} {j} (ρ : Fin (k+1) → Ty 0 0) (v : Atom Γ (.mu k bs j))
    (branches : ∀ i, Term Sg (Mems.instMember bs i _ (fun i' => .mu k (Ty.below bs ρ) i') :: Γ)
                             (ρ i))
    (d : Dest J (ρ j) τ) : Term Sg Γ τ J
```

A branch reads the answer at a child by `mu_out` and projecting field `0`, and reads the
answer at a grandchild by doing the same again. This is ordinary term code, so the three
case-tree families and their `k` bound disappear. `closed` is what makes `Ty.below`
definable without a cast. Evaluation is again one `IW.fold`, which builds the annotated tree
bottom-up.

The alternative is to drop `mu_brec` and have the translator tuple the answers
(`ρ := (fib n, fib (n-1))`). That is the smallest core, but it makes the translation of
`brecOn` harder.

## A.4 Canonical forms: `Ty.fix` and `closed`

Correctness does not need the old "every member is mentioned" rule. **Matching** does: the
field of `LitExpr (Nat × Bool)`'s `pair` must have literally the same `Ty` as a stand-alone
`LitExpr Nat`. So the translator never writes `Ty.mu` directly. It uses one computable smart
constructor:

```lean
/-- Canonical `mu`, built by the front end from *unordered, ungrounded* member bodies:
    keep only the members reachable from `sel`; inline every member that is not on a cycle
    (if `sel` itself is not on a cycle, the result is its body, with no `mu` at all); order
    the rest in **grounding order**, ties broken breadth-first from `sel`; in each union mark
    the **first** grounded constructor as the base.  Fails if some member can never be
    grounded: then that Lean type is empty, and translation is refused. -/
def Ty.fix (bodies : RawMembers) (sel : Nat) : Except String (Ty n g)
```

*Grounding order.* Stage `0` is the members whose body has a value with no member known;
stage `s + 1` is the members whose body has a value once the stages `≤ s` are known. Members
are listed stage by stage, so member `j` only relies directly on members `< j`, which is what
`Mems` demands. The stages are computed in at most `k + 1` rounds, each adding a member or
stopping, so this is structural recursion on the member count, not fuel. `sel` is then
whatever index the selected member got (it is no longer always `0`).

*Base constructor.* A union may have several grounded constructors (`Option (List α)`'s
`none` and `some`); the canonical tree marks the first one. So `Alts.there c u` is only used
when `c` is not grounded, and `Alts.two₂` only when the first constructor is not grounded.
This is a canonicity rule of `Ty.fix`, like the `closed` rule below; the typing of `Ty` does
not need it.

and `Ty.unfold` is stated with `Ty.fix` in the holes rather than raw `mu`. Then the children
of a canonical value are canonical. On closed trees everything reduces, so types still match
by `rfl` / `decide`.

This is the "families only on cycles" form from `IndexedExistentialFamilyProposal.md` §1.4,
now as a function instead of a well-formedness side condition.

`closed t` has one canonicity rule: the translator writes a closed subtree of a body as
`closed t` exactly when it is a *maximal* closed subtree that is not a leaf. The rule is
decidable, and `Ty.fix` enforces it. Alternatively, `Ty.fix` can normalise the other way (no
`closed` at all except where `Ty.below` needs it); either choice works as long as it is
fixed.

## A.5 `LitExpr` under A

`LitExpr α` is not one tree. It is a function of the **Lean** type `α`. So at a use site with
a closed index, the translator does the following (as in the earlier proposal):

1. **Reachable indices.** Start from the closed index. For every constructor, unify its
   result index with the current index (`isDefEq` with fresh metavariables for the
   constructor's arguments). If unification succeeds, the constructor exists at this index,
   and its recursive fields `LitExpr σ` add `σ` to the worklist. Indices are closed Lean
   `Expr`s, and they are memoised up to `isDefEq`.
2. **Bodies.** One member per reachable index. Its body is the schema of the constructors
   that survive there, **renumbered** in declaration order, with the usual point-counting
   (§A.8.1). A recursive field `LitExpr σ` becomes `var (index of σ)`.
3. **`Ty.fix`.** Canonicalise.

`LitExpr (Nat × Bool)`: reachable indices `Nat × Bool`, `Nat`, `Bool`. There is no cycle,
because the index only shrinks. So **there is no `mu` at all** (checked, `litExprNatBool`):

```
LitExpr Nat         = nat                 -- only `lit` survives; one ctor, one field ⇒ its field
LitExpr Bool        = bool
LitExpr (Nat × Bool) = taggedUnion [ [ record[nat, bool] ]     -- lit
                                   , [ nat, bool ] ]           -- pair (fields already inlined)
```

`eval : LitExpr α → α` specialised at `Nat × Bool` is then plain case analysis, with no
recursion (checked, `evalNB`).

**With a cycle.** Add `swap : LitExpr (β × α) → LitExpr (α × β)`. The indices `Nat × Bool`
and `Bool × Nat` now reach each other, so `Ty.fix` keeps both, as one `mu 1` with two members
(checked, `litSBody`). `eval` is one `mu_rec` whose answer type is **different per member**:
`ρ = [record[nat, bool], record[bool, nat]]`. Today this is the dependent-motive case that is
refused. In the toy, `eval (swap (lit (true, 3))) = (3, true)` holds by `rfl`.

**What stays refused:** an index that grows without bound, such as
`c : LitExpr (List α) → LitExpr α`. Here the reachable set is infinite, so a size cap is
needed, with a clear error when it is hit. A constructor argument that is not determined by
the result index and that data depends on is an existential, like `TExpr.fst`'s `β`, and is
handled as in §A.6.

## A.6 `Unfold` under A: not a W-type, deliberately

`Unfold α` is a Σ over `Type` (`State` is a field). A `Ty` constructor for it,
`Ty.exists (body : Ty 1 1)` with `Den = Σ t : Ty 0 0, Den (body.inst t)`, would **break
structural recursion**. `Den` would have to recurse on `body.inst t` for an *arbitrary* `t`,
which is not a subterm. Mathlib's `WType` does not help either: its shapes would be `Type`,
which lives in `Type 1`. And a "dynamic" `Ty.any` would break `Den`. So under A, as today:

* **A value** is built per `State`, with a layout that depends on the value.
  `#leanscript_get_ctor `Unfold.mk` is the function (the proof `decreasing` is erased):

  ```lean
  fun {Sg Γ} (α State : Ty 0 0)
      (seed    : Term Sg Γ State)
      (step    : Term Sg Γ (State ⇒ Option.ty (record[State, α])))
      (measure : Term Sg Γ (State ⇒ nat)) :
      Term Sg Γ (record[State, State ⇒ Option.ty (record[State, α]), State ⇒ nat])
  ```

  This is the "`fun a state => Term.record` with 3 fields" you expected. Where values with
  different `State`s meet, they are injected into a union (`TyWf.oneOf` today).
* **A function of an `Unfold`** is a *Lean* function `fun (State : Ty 0 0) => Term …`, which is
  universally quantified at the meta level, as today (`ToTerm/ExistentialArgs.lean`).
* **New with A: loops over an `Unfold` need no fuel.** The erased `decreasing` field implies
  that `step` fires at most `measure seed` times. So `Unfold.toList` / `take` translate to a
  `nat_rec` on `measure seed`, which is structural, instead of a `while_loop` with fuel. The
  proof of `decreasing` is used by the translation's correctness lemma, not by the term.

## A.7 Migration plan for A

Each step builds on its own and is checked by `lake build` together with an `rg sorry` sweep.

1. **New core type** `LeanScript/Ty/Ty.lean`: the mutual `Ty`/`Fields`/`Ctor`/`Ctors`/
   `Alts`/`Mems` of §A.1, with `DecidableEq`, `BEq`, `ReflBEq`, `LawfulBEq`, `Repr`,
   `Ty.ground`, and `toSchema`/`ofSchema`. Delete `Ty/Shape.lean` (`TyShape`). Port
   `Two`, `Ty.inh`, `Ty.two`, `Ty.twoDen` and its corollaries from the toy, next to `Ty.Den`.
2. **`Ty.inst`, `Ty.unfold`, `Ty.fix`**: replace `Ty/Unfold.lean`, `Ty/WfSubst.lean` and
   `Ty/Traversable.lean`.
3. **Denotation** `LeanScript/Den.lean`: `Ty.toIPF` over the new tree; `Den/Rec.lean` and
   `Den/Family.lean` become the single `rollMember`/`unrollMember` pair. `Den/PFunctor.lean`
   is only kept for the `k = 0` ↔ `WType` lemma.
4. **Delete** `Ty/Wf.lean`, `Ty/WfFacts.lean`, `Ty/WfTactic*`, `Ty/TyWf.lean` and
   `Ty/TyWfIn.lean`. `Ctx := List (Ty 0 0)`.
5. **`Term`** (`Expr/Term.lean`): remove the twelve recursive formers and the `…FoldK…`
   families; add `mu_in`, `mu_out`, `mu_rec` (and `mu_brec`). `Eval.lean` gets two cases.
   Delete `RecUnionRecFacts`, `RecObjectRecFacts`, `RecAliasRecFacts`,
   `FamilyRecFacts`/`FamilyNestedFacts`, `RecObjectAliasEvalFacts` and `SelfField`. Their
   content becomes one `mu_rec`/`mu_brec` evaluation lemma.
6. **Builders and translator** (`Expr/Build*`, `ToTerm/TransRec*`, `ToTerm/Brec.lean`,
   `ToTerm/TransBrec.lean`): one code path through `Ty.fix` and `mu_*`. `brecOn` maps to
   `mu_brec`.
7. **Class → cached elaborators** (§A.8): replace `LeanScript/Ty/Class.lean`,
   `Deriving/*` and `Instances.lean` by `#leanscript_get_ty`; rename `CtorFn/*` to
   `#leanscript_get_ctor`. The generated trees are `Ty.fix` trees; the only proofs in them are
   the `i < g` of each `var`, closed by `decide`. A Lean type with 0 or 1 values, or a
   recursive type with no grounding order, gets an error instead of a tree.
8. **Tests**: `…RecDepthTest` and `…ToTermTest` are re-expressed. The per-binder suites merge
   into one `MuTest`.

Rough size, from `rg` counts: `TyWfIn` appears in 42 files, `recTaggedUnion` in 78,
`recObject` in 69, `recAlias` in 62, `mutualRecursiveFamily` in 84, and `TyWf` in 162.
Steps 1–5 are the core. Steps 6–8 are mechanical, but they are most of the lines.

## A.8 Constructor API: cached `#leanscript_get_ty` and `#leanscript_get_ctor`

This section keeps the one idea of the withdrawn Proposal B, applied to the `Ty` of §A.1.
B's flat, non-recursive `Ty` is **not** kept: it could not express any recursive user type.

### A.8.1 Point counting

For a Lean inductive at a given (closed) instantiation, count the constructors that exist
there, in declaration order:

| constructors present | fields | tree |
| :-- | :-- | :-- |
| 0 | – | refused (no values) |
| 1 | 0 | refused (one point: the language has no unit; the value is erased where it occurs) |
| 1 | 1 | the field itself (newtype erasure) |
| 1 | ≥ 2 | `record` |
| 2 | none | a `union` of two constructors without fields, meaning `Bool` (or `prim .bool`, decision 3) |
| ≥ 3 | none | `enum`, numbered from `shift`: `0` by default; `Ordering` is `-1` (`lt, eq, gt ↦ -1, 0, 1`), a choice that today lives in `Instances.lean` and moves to the built-in table of §A.8.2 |
| ≥ 2 | some | `union`, with a base constructor chosen by `Ty.fix` (§A.4) |

Erased fields (proofs, instances, `Unit`, types) are dropped first. The constructor tag is
the position **among the constructors present**. For an index-varying family this can
differ from Lean's `ctorIdx` (see `LitExpr` below).

Fields are translated as follows:

| Lean field type | tree |
| :-- | :-- |
| an occurrence of a member of the block being translated | `var i _` (grounded or guarded as §A.1 requires; `Ty.fix` finds the order) |
| `Array T` / `List T` | `array t` / `list t` — **also** when `T` mentions the block (`node : List Rose → Rose`), compiled to a JS array |
| two adjacent fields `(m : Nat) (f : Fin m → T)`, where `m` occurs in no other field type, or a field `(m : Nat) × (Fin m → T)` | `finFn t` (`node : (m : Nat) → (Fin m → Rose) → Rose`) |
| `D → T` with `D` not mentioning the block | `fn d t` |
| `Option T`, `T × U`, other non-recursive inductives | inlined by point counting (their meaning is `Option`, `×`, …, as in §H) |
| a closed type that does not mention the block | its own tree (`closed` inside a body, §A.4) |
| anything else | an error naming the field (see §A.9) |

### A.8.2 Two cached elaborators replace the class

* `#leanscript_get_ty T` (a term elaborator; meta code): the `Ty 0 0` of a **closed Lean
  type** `T`. It works by structural recursion on the Lean `Expr`: a table of primitives
  (`Nat`, `Int`, `String`, `Char`, `Bool`, `UIntN`, `Float`, …), then `→`, `Array`, `List`,
  `Thunk`, a small **built-in table** of fixed choices (`Ordering`'s shift), and for an
  inductive application the point counting of §A.8.1 applied to its constructors'
  instantiated fields, followed by `Ty.fix` for the recursive members. The result is cached
  per `T` (up to `isDefEq`) in an environment extension, as `CtorFn/Cache.lean` does today,
  and stored as a generated `def`, so the same `T` always gives the same constant (this is
  also what makes two occurrences of the same Lean type literally the same `Ty`).
* `#leanscript_get_ctor c`: the constructor function (§A.8.3), cached the same way.

The translator (`#leanscript_to_term`) calls only these two. It never builds a
`taggedUnion_mk`/`record_mk`/`mu_in` for a Lean constructor inline: every Lean constructor in
the source becomes a call to its cached function. That is the "use it everywhere" rule.
The class `LeanScriptTyWf`, `deriving LeanScriptTyWf` and `Instances.lean` go away.

### A.8.3 `#leanscript_get_ctor`: specification

**Name.** A single `Lean.Name`: the last component is the constructor, and the prefix is the
inductive (`Option.some`, `List.nil`, `Lean.Syntax.node`, …). Resolution uses
`resolveGlobalConst`, so `open` namespaces work as usual. `#leanscript_get_ctor Prod` (an
inductive with one constructor) is accepted as shorthand for `Prod.mk`.

**Arguments of the returned function**, in the Lean constructor's order:

| Lean binder | becomes |
| :-- | :-- |
| a *uniform* type parameter (the layout is parametric in it: `Option`'s `α`) | an explicit `(α : Ty 0 0)` |
| a type that the **layout depends on** (an index-determining argument: `LitExpr`'s `α`, `β`) | fixed when the function is generated: named arguments of the elaborator, `#leanscript_get_ctor LitExpr.pair (α := Nat) (β := Bool)`. The cache key includes them |
| an existential type field (`Unfold.State`) | an explicit `(State : Ty 0 0)`; the layout depends on the value (§A.6) |
| a value field | `Term Sg Γ τ` with `τ` its translated type |
| the pair `(m : Nat) (f : Fin m → T)` of a `finFn` field | one argument `Term Sg Γ (finFn τ)` (decision 6) |
| a proof, instance, `Unit` | nothing (erased) |

**Result.** `Term Sg Γ (layout …)`, where the layout is an ordinary generated `def` on
`Ty 0 0` arguments (`Option.leanScriptLayout α`), shown by `#leanscript_get_ty`. For a
recursive type the body of the generated function is `mu_in` of the payload built with
`taggedUnion_mk` / `record_mk`, so the translator never sees `mu_in` directly.

### Examples (sketches, not compiled)

```lean
#leanscript_get_ctor Option.some
-- : {Sg : Sig} → {Γ : Ctx} → (α : Ty 0 0) → Term Sg Γ α → Term Sg Γ (Option.leanScriptLayout α)
-- where Option.leanScriptLayout α = .union (.two₁ .nullary (.fields (.one α)))  -- none | some α
-- (meaning `Option (Ty.Den α)`), and the body is `letE (.taggedUnion_mk _ 1 …) (.ret (.var 0))`.

#leanscript_get_ctor Option.none    -- : {Sg Γ} → (α : Ty 0 0) → Term Sg Γ (Option.leanScriptLayout α)
                                    --   no payload atom: `none` is a constructor without fields
#leanscript_get_ctor Prod.mk
-- : {Sg Γ} → (α β : Ty 0 0) → Term Sg Γ α → Term Sg Γ β → Term Sg Γ (.record α (.one β))
#leanscript_get_ctor Bool.true      -- : {Sg Γ} → Term Sg Γ (.prim .bool)
#leanscript_get_ctor Ordering.lt    -- : {Sg Γ} → Term Sg Γ (.enum ⟨0, -1⟩)   -- 0 extra ctors, shift -1
```

**`List.nil` / `List.cons`.** `List` is the built-in former `list` (decision 5):

```lean
#leanscript_get_ctor List.nil   -- : {Sg Γ} → (α : Ty 0 0) → Term Sg Γ (.list α)       -- `[]`
#leanscript_get_ctor List.cons  -- : {Sg Γ} → (α : Ty 0 0) → Term Sg Γ α → Term Sg Γ (.list α)
                                --     → Term Sg Γ (.list α)
```

Recursion over a list is `list_rec` (the list analogue of today's `array_rec`), and a JS array
is the runtime representation of both.

**Rose trees.** With `inductive RoseTree (α : Type) | node : α → List (RoseTree α) → RoseTree α`:

```lean
#leanscript_get_ty (RoseTree Nat)
-- = .mu 0 (.cons (.record (.closed .nat) (.one (.list (.var 0 _)))) .nil) 0
--   one member, one constructor, two fields; `list` guards the recursive occurrence
#leanscript_get_ctor RoseTree.node
-- : {Sg Γ} → (α : Ty 0 0) → Term Sg Γ α → Term Sg Γ (.list (RoseTree.leanScriptLayout α))
--     → Term Sg Γ (RoseTree.leanScriptLayout α)
--   body: `mu_in` of `record_mk` of the two arguments
```

With `Array` in place of `List`, the second argument is `Term Sg Γ (.array …)`. With
`node : α → (m : Nat) → (Fin m → RoseTree α) → RoseTree α` it is a
`Term Sg Γ (.finFn …)`: a third, different type.

**`LitExpr.lit` / `LitExpr.pair`.** The layout depends on the Lean index, so the indices are
fixed at generation time (§A.5):

```lean
#leanscript_get_ctor LitExpr.lit (α := Nat)
-- : {Sg Γ} → Term Sg Γ (.prim .nat) → Term Sg Γ (.prim .nat)
--   (only `lit` exists at `Nat`: one constructor, one field ⇒ the identity on its field)

#leanscript_get_ctor LitExpr.lit (α := Nat × Bool)
-- : {Sg Γ} → Term Sg Γ (.record nat (.one bool)) → Term Sg Γ LitExprNB
--   tag 0 of LitExprNB = #leanscript_get_ty (LitExpr (Nat × Bool))

#leanscript_get_ctor LitExpr.pair (α := Nat) (β := Bool)
-- : {Sg Γ} → Term Sg Γ (#leanscript_get_ty (LitExpr Nat))     -- = nat
--          → Term Sg Γ (#leanscript_get_ty (LitExpr Bool))    -- = bool
--          → Term Sg Γ LitExprNB                              -- tag 1
```

An index that cycles back (`swap`) is no longer a problem: the specialised tree is a `mu` with
one member per reachable index (§A.5), and `#leanscript_get_ctor LitExpr.swap (α := Nat)
(β := Bool)` is `mu_in` at member `0`.

Without the named index arguments, `#leanscript_get_ctor LitExpr.pair` fails with *"the
layout of `LitExpr` depends on its index; give `(α := …) (β := …)`"*. The expected type
cannot supply the indices, because it is a `Term` type and not a Lean type.

**`Unfold.mk`:** exactly as in §A.6 (the proof field is erased, `State` is an explicit `Ty`
argument, and the result is a `record` of three fields).

### Eliminators

The dual, `#leanscript_get_cases Option` (a function taking one branch per constructor
present and producing `taggedUnion_casesOn` / `record_casesOn` / `bool_casesOn` /
`enum_casesOn`, preceded by `mu_out` for a recursive type), follows the same rules and cache.
It is listed so that the translator never builds eliminators of Lean inductives inline
either. Its exact signature is left for the implementation.

## A.9 Lean types that Lean accepts but `Ty` cannot represent

Leaving out the types excluded on purpose (empty-like, unit-like, and existentially typed
ones such as `Unfold`), these are the Lean types that the kernel accepts and that have no
faithful `Ty`, both in this proposal (`proposals/WTyToy.lean`) and in the nominal
alternative (`proposals/NomTyToy.lean`, `proposals/NominalTyProposal.md`). The file
`proposals/UnrepresentableLeanTypes.lean` checks that Lean accepts every example below; it
does not (and cannot) check the "no `Ty`" column, which is an argument from the shape of the
two `Ty` definitions.

### Not representable at all

| kind | example | why there is no `Ty` (in both designs) |
| :-- | :-- | :-- |
| **dependent fields**, in general | `Tele.cons (n : Nat) (v : Fin (n + 2)) (rest : Tele)`; `WT.sup (a : α) (f : β a → WT α β)` | `Ty` has no dependent pairs or functions: a record field or a function codomain cannot mention a value. Only the `finFn` pattern `(m : Nat) (f : Fin m → T)` is built in (§A.2). Supporting the general case needs Σ/Π over `Ty`-indexed families, i.e. a dependent type theory inside `Ty` |
| **value-indexed families at a non-literal index** | `Matrix.cells : Vec (Vec Nat cols) rows`, or any `Vec α n` whose `n` is a variable or a field | at a *literal* index the reachable indices are finite and §A.5 applies (`Vec Nat 3` unfolds to 4 members, `Vec Nat 0` is unit-like and erased). At a variable index it is a dependent field again |
| **non-regular (polymorphic) recursion** | `Nest.cons : α → Nest (α × α) → Nest α` | the reachable instantiations `Nest Nat`, `Nest (Nat × Nat)`, … are infinite, so no finite `mu` (or finite nominal block) exists. §A.5's size cap refuses it with an error |
| **quotients** | `QT.node : Quot r → QT → QT`, `Multiset`, `Finset` | `Ty` has no quotient former. Representing `Quot r` by its carrier is fine at run time, but then `Ty.Den` has more values than the Lean type and `Quot.lift`'s respect proof has nowhere to go |

### Representable only with a caveat

| kind | example | caveat |
| :-- | :-- | :-- |
| **proof-carrying data** | `structure Pos where n : Nat; pos : n > 0`, `Subtype`, `Fin n` | proofs are erased, so the `Ty` is that of the data (`nat`), which has more values than the Lean type. Fine for compiling; the invariant is not tracked by `Ty` |
| **nested through a user-defined *recursive* container** | `Tree.node : Nat → MyList Tree → Tree` | a `mu` body cannot see the enclosing holes (§A.1), so `MyList Tree` cannot be a nested `mu`. It is flattened into an extra member (`mu 1 [Tree, MyList-of-Tree]`), exactly as Lean's kernel does for nested inductives. Then the field's type is that member, **not** `#leanscript_get_ty (MyList Tree)`, and passing a value made by generic `MyList` code needs a generated conversion (one traversal). Same in the nominal design (an extra member in the block). `List`, `Array`, `Option`, `Prod` and `Thunk` do **not** have this caveat: they are formers or are inlined |
| **polymorphic types** | `RoseTree (α : Type u)` itself | `Ty 0 0` has no type variables. A parametric Lean type becomes a meta-level function `RoseTree.leanScriptLayout : Ty 0 0 → Ty 0 0`, and a polymorphic Lean function is translated per instance, or as a Lean function over `Ty 0 0` (as for `Unfold`'s `State` in §A.6). Same in the nominal design |

### Differences between the two designs

| example | this proposal (`WTyToy`) | nominal (`NomTyToy`) |
| :-- | :-- | :-- |
| `node : List Rose → Rose` vs `node : Array Rose → Rose` vs `node : (m : Nat) → (Fin m → Rose) → Rose` | three different types, meaning `List`, `Array`, `(m : Nat) × (Fin m → _)` (checked) | **not yet**: `NomTyToy` has only `array`, which means `(m : Nat) × (Fin m → _)`, so all three collapse to one type, and a closed `Array Nat` does not mean `Array Nat`. Porting `list`/`finFn`/`ListPos` from `WTyToy` fixes it (for closed types it is even simpler there: `Ty.den (.array t) = Array (Ty.den t)` directly). Not done in this revision |
| structure inside a container element: `T5.node : Array (Option T5 × Nat) → T5` | direct: `array (record (union …) nat)` | a field is flat (`hole` / `old` / `array` / `fn`), so `Option T5 × Nat` needs an extra member in the block; its meaning is that member, not `Option T5 × Nat` |

Everything else that Lean accepts and that is neither empty- nor unit-like has a `Ty` under
this proposal. In particular the grounding check of §A.1 refuses **only** empty types: every
closed type has a value, so `D → X` has a value exactly when `X` does, and stage-by-stage
grounding (§A.4) finds an order for every member that has a value. (This last point is an
argument, not checked.)

---

# Part C: summary and decisions

* `Ty` = the former `TyShape` shapes **plus** a single `mu` (and `var`/`closed`), indexed by
  scope and grounding as in §A.1, with three distinct containers `array`, `list` and `finFn`.
  This replaces four binders and twelve term formers with three.
* No `TyWf`, no `LeanScriptTyWf`: correctness by typing (§A.1), canonical form by `Ty.fix`
  (§A.4).
* No unit-like and no empty-like types or terms, by construction (§H), with `Ty.twoDen` as the
  checked guarantee.
* `#leanscript_get_ty` / `#leanscript_get_ctor` / `#leanscript_get_cases`, cached, are the
  only way the translator touches Lean types and constructors (§A.8).
* `LitExpr` works at every closed index, including cyclic ones (§A.5). `Unfold` keeps
  value-dependent layouts with meta-level quantification, and gains fuel-free loops (§A.6).
* The Lean types still without a `Ty` are listed in §A.9.

Settled earlier: `Ty` is indexed (`Ty n g` with mutual containers), and inhabitation is
enforced by typing, not warned about. Proposal B is withdrawn.

**Decisions needed from you**

1. Keep `mu_brec` (full history, maps `brecOn` directly), or only `mu_rec` with tupled
   answers? (§A.3)
2. Index arguments of `#leanscript_get_ctor` for index-varying families: named arguments, as
   proposed, or a separate `#leanscript_get_ctor_at c (T)` form? (§A.8.3)
3. A union whose constructors all lack fields: keep it as a `union` (two of them denote
   `Bool`, as in the toy), or have `Ty.fix` turn it into `prim .bool` / `enum` so that each
   Lean type has exactly one tree? (Either way it has ≥ 2 values.)
4. Canonical base constructor: the **first** grounded one (proposed, §A.4), or always the
   first constructor of the Lean declaration when it is grounded and refuse otherwise
   (simpler, but refuses e.g. `inductive T | node : T → T → T | leaf`)?
5. `List`: its own former `list` (proposed: `mu_out` gives back a Lean `List`, and `List` and
   `Array` stay different types, as in Lean), or map `List` to `array` in `Ty` (one former
   fewer, but a Lean `List` value then needs a conversion)? Both compile to a JS array.
6. `finFn`: recognise only the two adjacent fields `(m : Nat) (f : Fin m → T)` with `m` used
   nowhere else, and the Σ-type `(m : Nat) × (Fin m → T)` (proposed), or more patterns? And
   does `#leanscript_get_ctor` take the two Lean arguments separately (closer to Lean) or one
   packed `finFn` term?
7. Nested user-defined recursive containers (§A.9): flatten into an extra member with a
   generated conversion (proposed, as Lean's kernel does), or refuse them?
8. If you prefer the nominal design instead: port `list`/`finFn` to it first (§A.9), since
   today it cannot tell the three rose trees apart.
