module

public import LeanScript.LeanPrimTy
public import LeanScript.EnumSchema

@[expose] public section

set_option autoImplicit false

/-!
# `Ty`: closed types that name their recursive datatypes

The one grammar of types of the language (designed in `proposals/NominalTyProposal.md`).

A closed type `Ty ks` has **no binder, no hole and no grounding index**.  A recursive type is
not written inside the type: it is *declared once*, in a datatype signature
(`LeanScript.DSig`, in `LeanScript.Decl`), and a type refers to it by its
name, `Ty.data r`, where `r : Ref ks` is a typed de Bruijn name.  `ks` lists the sizes of
the declared blocks, newest first: a block of `k + 1` mutually recursive datatypes
contributes `k` to `ks`.

Because a recursive type is a name, two occurrences of the same datatype are the same tree:
canonical forms are free, and equality of types is the derived `DecidableEq`.

What cannot be written:

* a union of fewer than two constructors (`Ctors` has at least two), or one none of whose
  constructors has fields (`UnionShape`: two points are only ever `bool`, three or more
  field-less constructors only ever an `enum`);
* a record of fewer than two fields (`Ty.record` takes a first field and at least one more);
* a constructor with an explicit `PUnit` payload (a constructor without fields is
  `Ctor.nullary`, and a union with one denotes `Option`/`Bool`, never `PUnit ⊕ _`);
* a leaf with fewer than two values: there is no `unit`, `BitVec 0` has no `LeanPrimTy`,
  and `String.Pos s` is only a leaf for a literal `s` of at least two characters
  (`LeanPrimTy.Nondeg`);
* a leaf with two values other than `bool` (`BitVec 1`, `String.Pos` of one character).
-/

namespace LeanScript

namespace LeanPrimTy

/-- `bool`, or a leaf with at least **three** values: two points are only ever `bool`, so the
    other leaves of two values are refused as well as the leaf of one value.  Every leaf other
    than `bool` has three or more, except `BitVec 1` (two values), `String.Pos ""` (one: the start of the empty string is its
    end) and `String.Pos s` for a one-character `s` (two: its start and its end). -/
def Nondeg : LeanPrimTy → Bool
  | .bitvec n _ => n != 1
  | .stringPos s => 2 ≤ s.length
  | _ => true

end LeanPrimTy



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

/-- The shape of a union: which of its constructors have fields.  A union must have at least
    one constructor with fields: a sum of field-less constructors is `bool` (two values) or an
    `enum` (three or more), never a union, so each finite set of points has exactly one type. -/
class UnionShape (bs : List Bool) : Prop where
  /-- Some constructor has fields. -/
  some_fields : bs.any id = true

instance UnionShape.here {bs : List Bool} : UnionShape (true :: bs) := ⟨rfl⟩
instance UnionShape.there {bs : List Bool} [h : UnionShape bs] : UnionShape (false :: bs) :=
  ⟨by simpa using h.some_fields⟩

mutual
/-- A closed type over a signature with block sizes `ks`. -/
inductive Ty : List Nat → Type where
  /-- A leaf with at least two values. -/
  | prim {ks : List Nat} (p : LeanPrimTy) (h : p.Nondeg = true := by decide) : Ty ks
  /-- A function type. -/
  | fn {ks : List Nat} : Ty ks → Ty ks → Ty ks
  /-- A Lean `Array`. -/
  | array {ks : List Nat} : Ty ks → Ty ks
  /-- A field-less sum of at least three constructors. -/
  | enum {ks : List Nat} : LeanEnumSchema → Ty ks
  /-- A record: a first field and at least one more. -/
  | record {ks : List Nat} : Ty ks → Fields ks → Ty ks
  /-- A union: at least two constructors, at least one of which has fields. -/
  | union {ks : List Nat} {bs : List Bool} (cs : Ctors ks bs) [h : UnionShape bs] : Ty ks
  /-- A declared (recursive) datatype, by name. -/
  | data {ks : List Nat} : Ref ks → Ty ks
/-- One or more fields. -/
inductive Fields : List Nat → Type where
  | one {ks : List Nat} : Ty ks → Fields ks
  | cons {ks : List Nat} : Ty ks → Fields ks → Fields ks
/-- A constructor: no fields (index `false`), or one or more fields (index `true`). -/
inductive Ctor : List Nat → Bool → Type where
  | nullary {ks : List Nat} : Ctor ks false
  | fields {ks : List Nat} : Fields ks → Ctor ks true
/-- Two or more constructors; the index lists which of them have fields. -/
inductive Ctors : List Nat → List Bool → Type where
  | two {ks : List Nat} {a b : Bool} : Ctor ks a → Ctor ks b → Ctors ks [a, b]
  | cons {ks : List Nat} {a : Bool} {bs : List Bool} : Ctor ks a → Ctors ks bs → Ctors ks (a :: bs)
end

deriving instance DecidableEq for Ty, Fields, Ctor, Ctors
deriving instance Repr for Ty, Fields, Ctor, Ctors

section Instances
variable {ks : List Nat}

instance : BEq (Ty ks) := instBEqOfDecidableEq
instance : BEq (Fields ks) := instBEqOfDecidableEq
instance {b : Bool} : BEq (Ctor ks b) := instBEqOfDecidableEq
instance {bs : List Bool} : BEq (Ctors ks bs) := instBEqOfDecidableEq
instance : BEq (Ref ks) := instBEqOfDecidableEq
instance : BEq (BRef ks) := instBEqOfDecidableEq

example : LawfulBEq (Ty ks) := inferInstance
example {bs : List Bool} : ReflBEq (Ctors ks bs) := inferInstance

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
  | .enum s => .enum s
  | .record t fs => .record (Ty.map f t) (Fields.map f fs)
  | .union cs (h := h) => .union (Ctors.map f cs) (h := h)
  | .data r => .data (f r)
/-- `Ty.map` on fields. -/
def Fields.map {ks ks' : List Nat} (f : Ref ks → Ref ks') : Fields ks → Fields ks'
  | .one t => .one (Ty.map f t)
  | .cons t fs => .cons (Ty.map f t) (Fields.map f fs)
/-- `Ty.map` on a constructor. -/
def Ctor.map {ks ks' : List Nat} {b : Bool} (f : Ref ks → Ref ks') : Ctor ks b → Ctor ks' b
  | .nullary => .nullary
  | .fields fs => .fields (Fields.map f fs)
/-- `Ty.map` on constructors. -/
def Ctors.map {ks ks' : List Nat} {bs : List Bool} (f : Ref ks → Ref ks') :
    Ctors ks bs → Ctors ks' bs
  | .two c d => .two (Ctor.map f c) (Ctor.map f d)
  | .cons c cs => .cons (Ctor.map f c) (Ctors.map f cs)
end

/-- Weakening a closed type into a signature with one more (newest) block. -/
abbrev Ty.weaken {k : Nat} {ks : List Nat} (t : Ty ks) : Ty (k :: ks) := Ty.map .there t

mutual
/-- Renaming by the identity is the identity. -/
theorem Ty.map_id {ks : List Nat} : (t : Ty ks) → Ty.map (fun r => r) t = t
  | .prim _ _ => rfl
  | .fn a b => by simp only [Ty.map, Ty.map_id a, Ty.map_id b]
  | .array t => by simp only [Ty.map, Ty.map_id t]
  | .enum _ => rfl
  | .record t fs => by simp only [Ty.map, Ty.map_id t, Fields.map_id fs]
  | .union cs (h := _) => by simp only [Ty.map, Ctors.map_id cs]
  | .data _ => rfl
theorem Fields.map_id {ks : List Nat} : (fs : Fields ks) → Fields.map (fun r => r) fs = fs
  | .one t => by simp only [Fields.map, Ty.map_id t]
  | .cons t fs => by simp only [Fields.map, Ty.map_id t, Fields.map_id fs]
theorem Ctor.map_id {ks : List Nat} {b : Bool} : (c : Ctor ks b) → Ctor.map (fun r => r) c = c
  | .nullary => rfl
  | .fields fs => by simp only [Ctor.map, Fields.map_id fs]
theorem Ctors.map_id {ks : List Nat} {bs : List Bool} :
    (cs : Ctors ks bs) → Ctors.map (fun r => r) cs = cs
  | .two c d => by simp only [Ctors.map, Ctor.map_id c, Ctor.map_id d]
  | .cons c cs => by simp only [Ctors.map, Ctor.map_id c, Ctors.map_id cs]
end

mutual
/-- Renaming twice is renaming by the composite. -/
theorem Ty.map_map {ks ks' ks'' : List Nat} (f : Ref ks → Ref ks') (g : Ref ks' → Ref ks'') :
    (t : Ty ks) → Ty.map g (Ty.map f t) = Ty.map (fun r => g (f r)) t
  | .prim _ _ => rfl
  | .fn a b => by simp only [Ty.map, Ty.map_map f g a, Ty.map_map f g b]
  | .array t => by simp only [Ty.map, Ty.map_map f g t]
  | .enum _ => rfl
  | .record t fs => by simp only [Ty.map, Ty.map_map f g t, Fields.map_map f g fs]
  | .union cs (h := _) => by simp only [Ty.map, Ctors.map_map f g cs]
  | .data _ => rfl
theorem Fields.map_map {ks ks' ks'' : List Nat} (f : Ref ks → Ref ks') (g : Ref ks' → Ref ks'') :
    (fs : Fields ks) → Fields.map g (Fields.map f fs) = Fields.map (fun r => g (f r)) fs
  | .one t => by simp only [Fields.map, Ty.map_map f g t]
  | .cons t fs => by simp only [Fields.map, Ty.map_map f g t, Fields.map_map f g fs]
theorem Ctor.map_map {ks ks' ks'' : List Nat} {b : Bool} (f : Ref ks → Ref ks')
    (g : Ref ks' → Ref ks'') :
    (c : Ctor ks b) → Ctor.map g (Ctor.map f c) = Ctor.map (fun r => g (f r)) c
  | .nullary => rfl
  | .fields fs => by simp only [Ctor.map, Fields.map_map f g fs]
theorem Ctors.map_map {ks ks' ks'' : List Nat} {bs : List Bool} (f : Ref ks → Ref ks')
    (g : Ref ks' → Ref ks'') :
    (cs : Ctors ks bs) → Ctors.map g (Ctors.map f cs) = Ctors.map (fun r => g (f r)) cs
  | .two c d => by simp only [Ctors.map, Ctor.map_map f g c, Ctor.map_map f g d]
  | .cons c cs => by simp only [Ctors.map, Ctor.map_map f g c, Ctors.map_map f g cs]
end



end LeanScript

end
