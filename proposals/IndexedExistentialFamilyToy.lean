module

public import LeanScript.Ty.TyWf

/-!
# Checks for `IndexedExistentialFamilyProposal.md`

Not part of the Lake build (like `ProofCarryingDiteToy.lean`).  Check it with

```
lake build LeanScript.Ty.TyWf && lake env lean proposals/IndexedExistentialFamilyToy.lean
```

Every tree below is written **by hand**: it is the tree the proposal says the deriving
handler / translator should produce.  `ty_wf` (the tactic behind `TyWf`'s default proof)
then says whether the *current* `Ty.Wf` accepts it.  Nothing here changes `Ty.Wf`.
-/

namespace LeanScript.Proposal.IndexedExistential

open LeanScript

/-- `Option t`, as `TyWf.option` builds it: `none` has no field, `some` has `t`. -/
abbrev opt (t : Ty) : Ty := .taggedUnion (.skip (.here ⟨t, []⟩ []))

/-- `α × β`. -/
abbrev pair (a b : Ty) : Ty := .record ⟨a, b, []⟩

/-! ## 1. `LitExpr (Nat × Bool)`, one member per reachable index

```
inductive LitExpr : Type → Type 1 where
  | lit  {α : Type} (x : α) : LitExpr α
  | pair {α β : Type} (a : LitExpr α) (b : LitExpr β) : LitExpr (α × β)
```

Reachable indices from `Nat × Bool`: `[Nat × Bool, Nat, Bool]` (member 0, 1, 2).

* member 0 (`Nat × Bool`): `lit (x : Nat × Bool) | pair (member 1) (member 2)`
* member 1 (`Nat`): only `lit` fits, so a newtype of `Nat`
* member 2 (`Bool`): only `lit` fits, so a newtype of `Bool`

The index only shrinks, so nothing mentions member 0, and the current `Ty.Wf` refuses the
family (`MembersOccur`). -/

/-- The three members of the monomorphised `LitExpr` at `Nat × Bool`. -/
abbrev litRoot : LeanFamMemberSchema Ty :=
  .ctors (.payloadFirst ⟨pair (.prim .nat) (.prim .bool), []⟩
    [.familyMember 1, .familyMember 2] [])

/-- error: ty_wf: nothing here mentions member 0 -/
#guard_msgs in
example : Ty.Wf (.mutualRecursiveFamily
    (.selectedThenMore [] litRoot (.alias (.prim .nat)) [.alias (.prim .bool)])) := by
  ty_wf

/-! ## 2. The same index, unrolled into non-recursive shapes

Because the index of `LitExpr` strictly shrinks, a closed index gives a finite tree with no
binder at all: a sum whose `pair` fields are the (erased-newtype) trees of the smaller
indices.  The current `Ty.Wf` accepts it. -/

/-- `LitExpr (Nat × Bool)`, unrolled. -/
example : TyWf where
  toTy := .taggedUnion (.payloadFirst ⟨pair (.prim .nat) (.prim .bool), []⟩
    [.prim .nat, .prim .bool] [])

/-- `LitExpr ((Nat × Bool) × Nat)`, unrolled: the inner product is itself a sum. -/
example : TyWf where
  toTy := .taggedUnion (.payloadFirst ⟨pair (pair (.prim .nat) (.prim .bool)) (.prim .nat), []⟩
    [.taggedUnion (.payloadFirst ⟨pair (.prim .nat) (.prim .bool), []⟩
      [.prim .nat, .prim .bool] []),
     .prim .nat] [])

/-! ## 3. A variant whose index graph has a cycle: a real family

```
inductive SwExpr : Type → Type 1 where
  | lit  {α : Type} (x : α) : SwExpr α
  | pair {α β : Type} (a : SwExpr α) (b : SwExpr β) : SwExpr (α × β)
  | swap {α β : Type} (p : SwExpr (β × α)) : SwExpr (α × β)
```

Reachable from `Nat × Bool`: `[Nat × Bool, Bool × Nat, Nat, Bool]`.  Member 0 and member 1
mention each other through `swap`, so every member is mentioned and the current `Ty.Wf`
accepts the family as it is. -/

/-- `SwExpr (Nat × Bool)`: the monomorphised family, selected at member 0. -/
abbrev swFamily (sel : Nat) : Ty :=
  let m0 : LeanFamMemberSchema Ty :=
    .ctors (.payloadFirst ⟨pair (.prim .nat) (.prim .bool), []⟩
      [.familyMember 2, .familyMember 3] [[.familyMember 1]])
  let m1 : LeanFamMemberSchema Ty :=
    .ctors (.payloadFirst ⟨pair (.prim .bool) (.prim .nat), []⟩
      [.familyMember 3, .familyMember 2] [[.familyMember 0]])
  match sel with
  | 0 => .mutualRecursiveFamily (.selectedThenMore [] m0 m1 [.alias (.prim .nat), .alias (.prim .bool)])
  | _ => .mutualRecursiveFamily (.selectedThenMore [m0] m1 (.alias (.prim .nat)) [.alias (.prim .bool)])

/-- The tree of `SwExpr (Nat × Bool)`. -/
example : TyWf where toTy := swFamily 0
/-- The tree of `SwExpr (Bool × Nat)`: the same family, another member selected. -/
example : TyWf where toTy := swFamily 1

/-! ## 4. `Unfold`, with the hidden state replaced by a closed-world state family

```
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x
```

Suppose the whole program builds `Unfold` values at these sites only:

| site | result | `State` |
| :-- | :-- | :-- |
| `countdown n` | `Unfold Nat` | `Nat` |
| `u.append v`  | `Unfold α`   | `u.State ⊕ v.State` |
| `u.map f`     | `Unfold β` (`u : Unfold α`) | `u.State` |

and uses `map` from `Nat` to `Bool` and from `Bool` to `Nat`.  Every `u.State` with
`u : Unfold α` is replaced by `H α`, the state family, whose constructors are the sites
whose result is `Unfold α`:

* member 0, `H Nat`: `countdown (n : Nat) | append (s : H Nat ⊕ H Nat) | map (s : H Bool)`
* member 1, `H Bool`: `map (s : H Nat)` — one constructor with one field, a newtype

`Unfold α` itself is then an ordinary closed record whose function fields take `H α`.  The
family stands to the left of an arrow, but as a *closed* type, which `Ty.Wf` allows; only an
occurrence `familyMember i` there would be refused. -/

/-- `H Nat` (`sel = 0`) and `H Bool` (`sel = 1`), the state family of `Unfold`. -/
abbrev stateFamily (sel : Nat) : Ty :=
  let h0 : LeanFamMemberSchema Ty :=
    .ctors (.payloadFirst ⟨.prim .nat, []⟩
      [.taggedUnion (.payloadFirst ⟨.familyMember 0, []⟩ [.familyMember 0] [])]
      [[.familyMember 1]])
  let h1 : LeanFamMemberSchema Ty := .alias (.familyMember 0)
  match sel with
  | 0 => .mutualRecursiveFamily (.selectedThenMore [] h0 h1 [])
  | _ => .mutualRecursiveFamily (.selectedLast h0 [] h1)

/-- The state family is a type of the language as it stands. -/
example : TyWf where toTy := stateFamily 0

/-- `Unfold Nat` = `{ seed : H Nat, step : H Nat ⇒ Option (H Nat × Nat), measure : H Nat ⇒ Nat }`
    (`decreasing` is a proof and is erased). -/
abbrev unfoldNat : TyWf where
  toTy := .record ⟨stateFamily 0,
    .fn (stateFamily 0) (opt (pair (stateFamily 0) (.prim .nat))),
    [.fn (stateFamily 0) (.prim .nat)]⟩

/-- `Unfold Bool`, over `H Bool`. -/
abbrev unfoldBool : TyWf where
  toTy := .record ⟨stateFamily 1,
    .fn (stateFamily 1) (opt (pair (stateFamily 1) (.prim .bool))),
    [.fn (stateFamily 1) (.prim .nat)]⟩

/-! What must stay refused: putting the `step` function *inside* the family, i.e. a member
whose field is `familyMember 0 ⇒ …`.  This is why the proposal keeps `Unfold α` outside the
state family. -/

/--
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs in
example : Ty.Wf (.mutualRecursiveFamily
    (.selectedThenMore []
      (.record ⟨.familyMember 1, .fn (.familyMember 1) (.prim .nat), []⟩)
      (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 1] [])) [])) := by
  ty_wf

end LeanScript.Proposal.IndexedExistential
