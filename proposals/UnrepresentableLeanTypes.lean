module

/-!
# The Lean types of `WTypeTyProposal.md` §A.9

Each is accepted by Lean, and has no faithful `Ty` in `WTyToy` / `NomTyToy`, or has one only
with a caveat (sections 4, 5, 7).

Self-contained (no imports, not part of the Lake build).  It only checks that Lean's kernel
**accepts** each declaration below; why each one has no `Ty` is explained in
`proposals/WTypeTyProposal.md`, §A.9.  Check it with:

```
lean proposals/UnrepresentableLeanTypes.lean
```
-/

@[expose] public section

namespace Unrep

/-! ## 1. Dependent fields: a later field's type mentions an earlier field's value -/

/-- `(n : Nat) × (Fin n → Nat)` spelled as a structure: read as `Nat × (Nat → Nat)` (and as
    `Nat × (Nat → Option T)` when `T` is on a recursive cycle); the general case of a
    dependent field is not supported. -/
structure Chunk where
  n : Nat
  data : Fin n → Nat

inductive Tele where
  | nil
  | cons (n : Nat) (v : Fin (n + 2)) (rest : Tele)

/-- Lean's own `Sigma`/W-type shape: the arity depends on the shape. -/
inductive WT (α : Type) (β : α → Type) where
  | sup (a : α) (f : β a → WT α β)

/-! ## 2. Families indexed by values, used at an index that is not a literal -/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

structure Matrix where
  rows : Nat
  cols : Nat
  cells : Vec (Vec Nat cols) rows

/-! ## 3. Non-regular (polymorphic) recursion: infinitely many members

(Now read with its type index erased through a generated element type, `Nest.Elem`: see
`TermTests/Datatypes/NestTest.lean`.) -/

inductive Nest : Type → Type 1 where
  | nil {α : Type} : Nest α
  | cons {α : Type} : α → Nest (α × α) → Nest α

/-! ## 4. Nested through a user-defined *recursive* container (representable only by
flattening into an extra member, so the field's meaning is not `MyList Tree`) -/

inductive MyList (α : Type) where
  | nil
  | cons : α → MyList α → MyList α

inductive Tree where
  | node : Nat → MyList Tree → Tree

/-! ## 5. Structure inside a container element (`WTyToy`: direct; `NomTyToy`: extra member)

(Supported with extra members: `T5`'s block is `T5`, `Option T5`, `Option T5 × Nat`, and the
array holds the third; see `TermTests/Datatypes/RoseVariantsTest.lean`.) -/

inductive T5 where
  | leaf : Nat → T5
  | node : Array (Option T5 × Nat) → T5

/-! ## 6. Quotients and proof-carrying data

Supported through erasure (`TermTests/Datatypes/QuotientTest.lean`): a quotient is read as its carrier
(`QT` is `leaf | node Nat QT`, a class is given by a representative, `Quot.lift f h q` is `f`
of the representative), and a proof field is dropped (`Pos` is `Nat`). -/

inductive QT where
  | leaf
  | node : Quot (fun (a b : Nat) => a % 2 = b % 2) → QT → QT

structure Pos where
  n : Nat
  pos : n > 0

/-! ## 7. A polymorphic type (a meta-level function `Ty 0 0 → Ty 0 0`, not one `Ty`)

(Each instance is its own datatype: `RoseTree Nat` with `List`, `Array` or `Fin m →` children
are three different datatypes — a linked-list member, a `Ty.array`, and a record of a `nat`
and a function to `Option`; see `TermTests/Datatypes/RoseVariantsTest.lean`.) -/

inductive RoseTree (α : Type u) where
  | node : α → List (RoseTree α) → RoseTree α

/-! ## Why the meaning of `Ty.mu` stores children by position, not in a real `Array`

A universe of values with a nested `Array` under an index is refused by the kernel, so the
meaning of a recursive `Ty` cannot be such an inductive (`WTypeTyProposal.md` §A.2). -/

inductive Code where
  | nat
  | arr : Code → Code

/--
error: (kernel) invalid nested inductive datatype 'Array', nested inductive datatypes parameters cannot contain local variables.
-/
#guard_msgs in
inductive V : Code → Type where
  | n : Nat → V .nat
  | arr {c : Code} : Array (V c) → V (.arr c)

end Unrep
end
