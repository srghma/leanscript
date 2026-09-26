module

public import LeanScript.LeanPrimTy
public import LeanScript.Ty.Schema.Sum

@[expose] public section

set_option autoImplicit false

/-!
# `Nominal.Ty`: closed types that name their recursive datatypes

This is step 1 of design **N** of `proposals/NominalTyProposal.md` (§2.1).

A closed type `Ty ks` has **no binder, no hole and no grounding index**.  A recursive type is
not written inside the type: it is *declared once*, in a datatype signature
(`LeanScript.Nominal.DSig`, in `LeanScript.Nominal.Decl`), and a type refers to it by its
name, `Ty.data r`, where `r : Ref ks` is a typed de Bruijn name.  `ks` lists the sizes of
the declared blocks, newest first: a block of `k + 1` mutually recursive datatypes
contributes `k` to `ks`.

Because a recursive type is a name, two occurrences of the same datatype are the same tree:
canonical forms are free, and equality of types is the derived `DecidableEq`.

What cannot be written:

* a union of fewer than two constructors (`Ctors` has at least two);
* a record of fewer than two fields (`Ty.record` takes a first field and at least one more);
* a constructor with an explicit `PUnit` payload (a constructor without fields is
  `Ctor.nullary`, and a union with one denotes `Option`/`Bool`, never `PUnit ⊕ _`);
* a leaf with fewer than two values: there is no `unit`, `BitVec 0` has no `LeanPrimTy`,
  and `String.Pos s` is only a leaf for a non-empty literal `s` (`LeanPrimTy.Nondeg`).
-/

namespace LeanScript

namespace LeanPrimTy

/-- A leaf with at least two values.  Every leaf has, except `String.Pos ""`, which has
    exactly one (the start of the empty string is its end). -/
def Nondeg : LeanPrimTy → Bool
  | .stringPos s => s != ""
  | _ => true

end LeanPrimTy

namespace Nominal

/-! ## Names of declared datatypes -/

/-- A reference to member `j` of one block of a signature whose block sizes are `ks`
    (newest block first, as de Bruijn indices).  A block of size `k` has `k + 1` members. -/
inductive Ref : List Nat → Type where
  /-- Member `j` of the newest block. -/
  | here {k : Nat} {ks : List Nat} (j : Fin (k + 1)) : Ref (k :: ks)
  /-- A datatype of an older block. -/
  | there {k : Nat} {ks : List Nat} : Ref ks → Ref (k :: ks)
  deriving DecidableEq, Repr

/-- A reference to a whole block of a signature (without choosing a member). -/
inductive BRef : List Nat → Type where
  /-- The newest block. -/
  | here {k : Nat} {ks : List Nat} : BRef (k :: ks)
  /-- An older block. -/
  | there {k : Nat} {ks : List Nat} : BRef ks → BRef (k :: ks)
  deriving DecidableEq, Repr

/-- The size `k` of a block (it has `k + 1` members). -/
def BRef.size : {ks : List Nat} → BRef ks → Nat
  | k :: _, .here => k
  | _ :: _, .there b => b.size

/-- Member `j` of a block, as a name. -/
def BRef.ref : {ks : List Nat} → (b : BRef ks) → Fin (b.size + 1) → Ref ks
  | _ :: _, .here, j => .here j
  | _ :: _, .there b, j => .there (b.ref j)

/-! ## Closed types -/

mutual
/-- A closed type over a signature with block sizes `ks`. -/
inductive Ty : List Nat → Type where
  /-- A leaf with at least two values. -/
  | prim {ks : List Nat} (p : LeanPrimTy) (h : p.Nondeg = true := by decide) : Ty ks
  /-- A function type. -/
  | fn {ks : List Nat} : Ty ks → Ty ks → Ty ks
  /-- A Lean `Array`. -/
  | array {ks : List Nat} : Ty ks → Ty ks
  /-- A memoised delay (it denotes the value it stands for; the wrapper only decides the
      code printed for it). -/
  | thunk {ks : List Nat} : Ty ks → Ty ks
  /-- An unmemoised delay (it denotes the value it stands for). -/
  | lazy {ks : List Nat} : Ty ks → Ty ks
  /-- A field-less sum of at least three constructors. -/
  | enum {ks : List Nat} : LeanEnumSchema → Ty ks
  /-- A record: a first field and at least one more. -/
  | record {ks : List Nat} : Ty ks → Fields ks → Ty ks
  /-- A union: at least two constructors. -/
  | union {ks : List Nat} : Ctors ks → Ty ks
  /-- A declared (recursive) datatype, by name. -/
  | data {ks : List Nat} : Ref ks → Ty ks
/-- One or more fields. -/
inductive Fields : List Nat → Type where
  | one {ks : List Nat} : Ty ks → Fields ks
  | cons {ks : List Nat} : Ty ks → Fields ks → Fields ks
/-- A constructor: no fields, or one or more fields. -/
inductive Ctor : List Nat → Type where
  | nullary {ks : List Nat} : Ctor ks
  | fields {ks : List Nat} : Fields ks → Ctor ks
/-- Two or more constructors. -/
inductive Ctors : List Nat → Type where
  | two {ks : List Nat} : Ctor ks → Ctor ks → Ctors ks
  | cons {ks : List Nat} : Ctor ks → Ctors ks → Ctors ks
end

deriving instance DecidableEq for Ty, Fields, Ctor, Ctors
deriving instance Repr for Ty, Fields, Ctor, Ctors

section Instances
variable {ks : List Nat}

instance : BEq (Ty ks) := instBEqOfDecidableEq
instance : BEq (Fields ks) := instBEqOfDecidableEq
instance : BEq (Ctor ks) := instBEqOfDecidableEq
instance : BEq (Ctors ks) := instBEqOfDecidableEq
instance : BEq (Ref ks) := instBEqOfDecidableEq
instance : BEq (BRef ks) := instBEqOfDecidableEq

example : LawfulBEq (Ty ks) := inferInstance
example : ReflBEq (Ctors ks) := inferInstance

end Instances

namespace Ty

/-- The pair type: a record of two fields. -/
abbrev pair {ks : List Nat} (a b : Ty ks) : Ty ks := .record a (.one b)

/-- `Bool`. -/
abbrev bool {ks : List Nat} : Ty ks := .prim .bool
/-- `Nat`. -/
abbrev nat {ks : List Nat} : Ty ks := .prim .nat
/-- `Int`. -/
abbrev int {ks : List Nat} : Ty ks := .prim .int
/-- `String`. -/
abbrev string {ks : List Nat} : Ty ks := .prim .string

/-- `Option t`: a union of a constructor without fields and one with the field `t`. -/
abbrev option {ks : List Nat} (t : Ty ks) : Ty ks := .union (.two .nullary (.fields (.one t)))

/-- `a ⊕ b`. -/
abbrev sum {ks : List Nat} (a b : Ty ks) : Ty ks := .union (.two (.fields (.one a)) (.fields (.one b)))

end Ty

/-! ## Renaming (weakening) -/

mutual
/-- Rename the declared datatypes a type mentions. -/
def Ty.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ty ks → Ty ks'
  | .prim p h => .prim p h
  | .fn a b => .fn (Ty.map f a) (Ty.map f b)
  | .array t => .array (Ty.map f t)
  | .thunk t => .thunk (Ty.map f t)
  | .lazy t => .lazy (Ty.map f t)
  | .enum s => .enum s
  | .record t fs => .record (Ty.map f t) (Fields.map f fs)
  | .union cs => .union (Ctors.map f cs)
  | .data r => .data (f r)
/-- `Ty.map` on fields. -/
def Fields.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Fields ks → Fields ks'
  | .one t => .one (Ty.map f t)
  | .cons t fs => .cons (Ty.map f t) (Fields.map f fs)
/-- `Ty.map` on a constructor. -/
def Ctor.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ctor ks → Ctor ks'
  | .nullary => .nullary
  | .fields fs => .fields (Fields.map f fs)
/-- `Ty.map` on constructors. -/
def Ctors.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Ctors ks → Ctors ks'
  | .two c d => .two (Ctor.map f c) (Ctor.map f d)
  | .cons c cs => .cons (Ctor.map f c) (Ctors.map f cs)
end

/-- Weakening a closed type into a signature with one more (newest) block. -/
abbrev Ty.weaken {k : Nat} {ks : List Nat} (t : Ty ks) : Ty (k :: ks) := Ty.map .there t

end Nominal

end LeanScript

end
