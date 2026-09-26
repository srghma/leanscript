module

public import LeanScript.Nominal.Ty

@[expose] public section

set_option autoImplicit false

/-!
# Declarations: the only place with holes and grounding

Step 2 of design **N** of `proposals/NominalTyProposal.md` (§2.2).

A block of `n = k + 1` mutually recursive datatypes over the older signature `ks` is a list
of member declarations **in grounding order** (`Mems`).  The grammar is flat: a member is
one layer of constructors and its fields are *field types* (`Fld`):

* `Fld.hole i h` — member `i` of the block being declared, used directly; it must be
  grounded (`i < g`: an earlier member, which is already known to have values);
* `Fld.old t` — an older closed type (it cannot mention the block being declared: the
  block is not in its own signature);
* `Fld.array f` — an array of a field; guarded (the empty array is a value), so its element
  may mention every member;
* `Fld.fn a f` — a function from an *older* closed type: strict positivity by typing.

A member is a wrapper of one field (`Decl.wrap`), a record of at least two fields
(`Decl.record`, all grounded) or a union of at least two constructors (`Decl.union`), of
which exactly one, the *base*, is grounded (`Alts`) and the others are guarded.

The grounding index `g` exists only here: closed types (`Ty ks`) have none.
-/

namespace LeanScript

namespace Nominal

/-- A field of a constructor of a declared datatype, in a block of `n` members of which the
    first `g` are grounded. -/
inductive Fld : List Nat → Nat → Nat → Type where
  /-- A member of the block being declared, used directly: must be grounded. -/
  | hole {ks : List Nat} {n g : Nat} (i : Fin n) : i.val < g → Fld ks n g
  /-- An older closed type (it cannot mention the block being declared). -/
  | old {ks : List Nat} {n g : Nat} : Ty ks → Fld ks n g
  /-- Guarded: the empty array is always a value. -/
  | array {ks : List Nat} {n g : Nat} : Fld ks n n → Fld ks n g
  /-- The domain is an older closed type (strict positivity, by typing). -/
  | fn {ks : List Nat} {n g : Nat} : Ty ks → Fld ks n g → Fld ks n g
  deriving DecidableEq, Repr

/-- One or more fields. -/
inductive Flds : List Nat → Nat → Nat → Type where
  | one {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g
  | cons {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g → Flds ks n g
  deriving DecidableEq, Repr

/-- A constructor: no fields, or one or more fields. -/
inductive BCtor : List Nat → Nat → Nat → Type where
  | nullary {ks : List Nat} {n g : Nat} : BCtor ks n g
  | fields {ks : List Nat} {n g : Nat} : Flds ks n g → BCtor ks n g
  deriving DecidableEq, Repr

/-- Two or more guarded constructors. -/
inductive BCtors : List Nat → Nat → Type where
  | two {ks : List Nat} {n : Nat} : BCtor ks n n → BCtor ks n n → BCtors ks n
  | cons {ks : List Nat} {n : Nat} : BCtor ks n n → BCtors ks n → BCtors ks n
  deriving DecidableEq, Repr

/-- Two or more constructors, exactly one of which (the base) is grounded. -/
inductive Alts : List Nat → Nat → Nat → Type where
  /-- Two constructors, the first is the base. -/
  | two₁ {ks : List Nat} {n g : Nat} : BCtor ks n g → BCtor ks n n → Alts ks n g
  /-- Two constructors, the second is the base. -/
  | two₂ {ks : List Nat} {n g : Nat} : BCtor ks n n → BCtor ks n g → Alts ks n g
  /-- The base, then at least two guarded constructors. -/
  | here {ks : List Nat} {n g : Nat} : BCtor ks n g → BCtors ks n → Alts ks n g
  /-- A guarded constructor, then the others (among which the base). -/
  | there {ks : List Nat} {n g : Nat} : BCtor ks n n → Alts ks n g → Alts ks n g
  deriving DecidableEq, Repr

/-- One member of a block. -/
inductive Decl : List Nat → Nat → Nat → Type where
  /-- One constructor with one field (e.g. `Rose.node : Array Rose → Rose`). -/
  | wrap {ks : List Nat} {n g : Nat} : Fld ks n g → Decl ks n g
  /-- One constructor with at least two fields, all grounded. -/
  | record {ks : List Nat} {n g : Nat} : Fld ks n g → Flds ks n g → Decl ks n g
  /-- At least two constructors, the base grounded. -/
  | union {ks : List Nat} {n g : Nat} : Alts ks n g → Decl ks n g
  deriving DecidableEq, Repr

/-- The members `g, g+1, …, n-1` of a block; member `g` may use members `< g` directly. -/
inductive Mems : List Nat → Nat → Nat → Type where
  | nil {ks : List Nat} {n : Nat} : Mems ks n n
  | cons {ks : List Nat} {n g : Nat} : Decl ks n g → Mems ks n (g + 1) → Mems ks n g
  deriving DecidableEq, Repr

/-- A datatype signature: blocks of mutually recursive datatypes, newest first.  Each block
    may use the older blocks as closed types. -/
inductive DSig : List Nat → Type where
  | nil : DSig []
  | cons {ks : List Nat} (Δ : DSig ks) (k : Nat) (bs : Mems ks (k + 1) 0) : DSig (k :: ks)
  deriving DecidableEq, Repr

section Instances
variable {ks : List Nat} {n g : Nat}
instance : BEq (Fld ks n g) := instBEqOfDecidableEq
instance : BEq (Flds ks n g) := instBEqOfDecidableEq
instance : BEq (BCtor ks n g) := instBEqOfDecidableEq
instance : BEq (BCtors ks n) := instBEqOfDecidableEq
instance : BEq (Alts ks n g) := instBEqOfDecidableEq
instance : BEq (Decl ks n g) := instBEqOfDecidableEq
instance : BEq (Mems ks n g) := instBEqOfDecidableEq
instance : BEq (DSig ks) := instBEqOfDecidableEq
end Instances

theorem Fin.zero_add_lt' {k : Nat} (j : Fin k) : 0 + j.val < k := by
  have := j.isLt; omega

/-! ## Instantiating a body: filling the holes with closed types

The older closed types of a body are renamed into the target signature by `w`. -/

section Inst
variable {ks K : List Nat} (w : Ref ks → Ref K)

/-- A field with its holes filled by `σ` and its older types renamed by `w`. -/
def Fld.inst {n g : Nat} (σ : Fin n → Ty K) : Fld ks n g → Ty K
  | .hole i _ => σ i
  | .old t => Ty.map w t
  | .array f => .array (Fld.inst σ f)
  | .fn a f => .fn (Ty.map w a) (Fld.inst σ f)
/-- `Fld.inst` on fields. -/
def Flds.inst {n g : Nat} (σ : Fin n → Ty K) : Flds ks n g → Fields K
  | .one f => .one (Fld.inst w σ f)
  | .cons f fs => .cons (Fld.inst w σ f) (Flds.inst σ fs)
/-- `Fld.inst` on a constructor. -/
def BCtor.inst {n g : Nat} (σ : Fin n → Ty K) : BCtor ks n g → Ctor K
  | .nullary => .nullary
  | .fields fs => .fields (Flds.inst w σ fs)
/-- `Fld.inst` on guarded constructors. -/
def BCtors.inst {n : Nat} (σ : Fin n → Ty K) : BCtors ks n → Ctors K
  | .two c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .cons c cs => .cons (BCtor.inst w σ c) (BCtors.inst σ cs)
/-- `Fld.inst` on the constructors of a union. -/
def Alts.inst {n g : Nat} (σ : Fin n → Ty K) : Alts ks n g → Ctors K
  | .two₁ c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .two₂ c d => .two (BCtor.inst w σ c) (BCtor.inst w σ d)
  | .here c cs => .cons (BCtor.inst w σ c) (BCtors.inst w σ cs)
  | .there c u => .cons (BCtor.inst w σ c) (Alts.inst σ u)
/-- A member, as a closed type. -/
def Decl.inst {n g : Nat} (σ : Fin n → Ty K) : Decl ks n g → Ty K
  | .wrap f => Fld.inst w σ f
  | .record f fs => .record (Fld.inst w σ f) (Flds.inst w σ fs)
  | .union u => .union (Alts.inst w σ u)
/-- Member `g + i` of a block, as a closed type. -/
def Mems.instMember {n g : Nat} (σ : Fin n → Ty K) : Mems ks n g → (i : Nat) → g + i < n → Ty K
  | .nil, _, h => absurd h (by omega)
  | .cons d _, 0, _ => Decl.inst w σ d
  | .cons _ bs, i + 1, h => Mems.instMember σ bs i (by omega)
/-- Member `j` of a whole block, as a closed type. -/
abbrev Mems.inst {k : Nat} (σ : Fin (k + 1) → Ty K) (bs : Mems ks (k + 1) 0) (j : Fin (k + 1)) :
    Ty K :=
  Mems.instMember w σ bs j.val (Fin.zero_add_lt' j)
end Inst

/-- The unfolded body of member `j` of the newest block: its holes are the members themselves
    (by name), its older types are weakened. -/
abbrev Ty.unfold {ks : List Nat} {k : Nat} (bs : Mems ks (k + 1) 0) (j : Fin (k + 1)) :
    Ty (k :: ks) :=
  Mems.inst .there (fun i => .data (.here i)) bs j

end Nominal

end LeanScript

end
