module

public import LeanScript.Eval
public meta import LeanScript.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Families indexed by a type: non-regular recursion (`Nest`)

`Nest α` recurses at `Nest (α × α)`, so its instances `Nest Nat`, `Nest (Nat × Nat)`,
`Nest ((Nat × Nat) × (Nat × Nat))`, … are infinitely many: they cannot each be a member of a
(finite) block.  As for the value index of `Vec α n` (`IndexedFamilyTest`), the type index is
**erased** (`LeanScript.Gen.canonIndex`), through a generated *element type* that holds a value
of every index reached from the base:

```
inductive Nest.Elem (α : Type) : Type where
  | leaf : α → Nest.Elem α
  | node : Nest.Elem α → Nest.Elem α → Nest.Elem α   -- the index `α × α`, flattened
```

* `Nest Nat` is the declared datatype `nil | cons (Nest.Elem Nat) Nest`: a list of trees, whose
  `k`-th element is (in Lean) a perfect tree of depth `k`.  `Nest.Elem Nat` is an older block.
* `Nest (Nat × Nat)` peels to the same base `Nat`: it is the **same** datatype.
* A value `(2, 3) : Nat × Nat` at depth 1 is `node (leaf 2) (leaf 3)`.
* A function generic in the index (`Nest.length`) is translated at the index the program
  declares the family at (or at the one given by name, `(α := Nat)`): its recursive call at
  `α × α` is a structural call on the tail.

As for `Vec`, the erased type has more values than the Lean one (a tree of any shape at any
depth); the encoding is injective (`NestProofs.nestEnc_injective`).
-/

namespace NestTest

open LeanScript

inductive Nest : Type → Type 1 where
  | nil {α : Type} : Nest α
  | cons {α : Type} : α → Nest (α × α) → Nest α

leanscript_signature Prog where
  nest := Nest Nat
  nest2 := Nest (Nat × Nat)

/-! ## The types -/

-- the generated element type
/--
info: inductive NestTest.Nest.Elem : Type → Type
number of parameters: 1
constructors:
NestTest.Nest.Elem.leaf : {α : Type} → α → Nest.Elem α
NestTest.Nest.Elem.node : {α : Type} → Nest.Elem α → Nest.Elem α → Nest.Elem α
-/
#guard_msgs in
#print Nest.Elem

-- two blocks: `Nest.Elem Nat` (older), then `Nest Nat`
example : Prog.ks = [0, 0] := rfl
example : Prog.nest = .data (.here 0) := rfl
-- `Nest (Nat × Nat)` is the same datatype
example : Prog.nest2 = Prog.nest := rfl
example : (#leanscript_get_ty (Nest ((Nat × Nat) × (Nat × Nat))) : Ty Prog.ks) = Prog.nest := rfl

-- `Nest.Elem Nat`: `leaf Nat` (the base) or `node Elem Elem`
example : Prog.block0 = .cons (.union (.two₁ (.fields (.one (.old .nat)))
    (.fields (.cons (.hole 0 (by decide)) (.one (.hole 0 (by decide))))))) .nil := rfl
-- `Nest Nat`: `nil` (the base) or `cons (Nest.Elem Nat) Nest`
example : Prog.block1 = .cons (.union (.two₁ .nullary
    (.fields (.cons (.old (.data (.here 0))) (.one (.hole 0 (by decide))))))) .nil := rfl

/-! ## Constructors and case analysis

The index of a type-indexed family is given by name; any index with the same base gives the
same function. -/

/--
info: NestTest.Prog.Nest.cons {Γ : Ctx Prog.ks} (x0 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there))
  (x1 : Term Prog.Δ Γ (Ty.data (Ref.here 0))) : Term Prog.Δ Γ (Ty.data (Ref.here 0))
-/
#guard_msgs in
#leanscript_get_ctor Nest.cons (α := Nat)

-- the same (cached) function
/--
info: NestTest.Prog.Nest.cons {Γ : Ctx Prog.ks} (x0 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there))
  (x1 : Term Prog.Δ Γ (Ty.data (Ref.here 0))) : Term Prog.Δ Γ (Ty.data (Ref.here 0))
-/
#guard_msgs in
#leanscript_get_ctor Nest.cons (α := Nat × Nat)

/--
info: NestTest.Prog.Nest.nil {Γ : Ctx Prog.ks} : Term Prog.Δ Γ (Ty.data (Ref.here 0))
-/
#guard_msgs in
#leanscript_get_ctor Nest.nil (α := Nat)

/--
info: NestTest.Prog.Elem.node {Γ : Ctx Prog.ks} (x0 x1 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there)) :
  Term Prog.Δ Γ (Ty.data (Ref.here 0).there)
-/
#guard_msgs in
#leanscript_get_ctor Nest.Elem.node (α := Nat)

/--
info: NestTest.Prog.Nest.cases {Γ : Ctx Prog.ks} {τ : Ty Prog.ks} (scrut : Term Prog.Δ Γ (Ty.data (Ref.here 0)))
  (on_nil : Term Prog.Δ Γ τ) (on_cons : Term Prog.Δ (Ty.data (Ref.here 0).there :: Ty.data (Ref.here 0) :: Γ) τ) :
  Term Prog.Δ Γ τ
-/
#guard_msgs in
#leanscript_get_cases Nest (α := Nat)

/--
error: LeanScript: `NestTest.Nest` is indexed by a type: give the index as `(α := …)`
-/
#guard_msgs in
#leanscript_get_ctor Nest.cons

/-! ## Values: the elements become trees -/

def n3 : Nest Nat := .cons 1 (.cons (2, 3) (.cons ((4, 5), (6, 7)) .nil))
def n3T := #leanscript_to_term n3

example : n3T = Prog.Nest.cons (Prog.Elem.leaf (.lit .nat 1))
    (Prog.Nest.cons (Prog.Elem.node (Prog.Elem.leaf (.lit .nat 2)) (Prog.Elem.leaf (.lit .nat 3)))
      (Prog.Nest.cons
        (Prog.Elem.node (Prog.Elem.node (Prog.Elem.leaf (.lit .nat 4)) (Prog.Elem.leaf (.lit .nat 5)))
          (Prog.Elem.node (Prog.Elem.leaf (.lit .nat 6)) (Prog.Elem.leaf (.lit .nat 7))))
        Prog.Nest.nil)) := rfl

-- a value of `Nest (Nat × Nat)`: its first element is already a pair
def m2 : Nest (Nat × Nat) := .cons (1, 2) .nil
def m2T := #leanscript_to_term m2
example : m2T = Prog.Nest.cons (Prog.Elem.node (Prog.Elem.leaf (.lit .nat 1))
    (Prog.Elem.leaf (.lit .nat 2))) Prog.Nest.nil := rfl

-- a pair that is not written out is taken apart by its projections
def pairs (p : Nat × Nat) : Nest Nat := .cons p.1 (.cons p .nil)
def pairsT := #leanscript_to_term pairs

/-! ## Functions generic in the index -/

def Nest.length : {α : Type} → Nest α → Nat
  | _, .nil => 0
  | _, .cons _ r => 1 + r.length

-- the index is erased: the translation takes the `Nest` only
/--
info: Nest.length : Term Prog.Δ [] ((Ty.data (Ref.here 0)).fn (Ty.prim LeanPrimTy.nat))
-/
#guard_msgs in
#leanscript_to_term Nest.length

def lengthT := #leanscript_to_term Nest.length
example : lengthT.run n3T.run = (3 : Nat) := rfl
example : lengthT.run m2T.run = (1 : Nat) := rfl
#guard n3.length == 3

def Nest.isNil : {α : Type} → Nest α → Bool
  | _, .nil => true
  | _, .cons _ _ => false

def isNilT := #leanscript_to_term Nest.isNil (α := Nat)
example : isNilT.run n3T.run = false := rfl
example : isNilT.run (Prog.Nest.nil (Γ := [])).run = true := rfl

example : lengthT.run (pairsT.run (show Ty.Den Prog.Δ (.pair .nat .nat) from ((8 : Nat), (9 : Nat)))) =
    (2 : Nat) := rfl

/-- Course-of-values recursion: the number of pairs of consecutive levels. -/
def Nest.pairsOfLevels : {α : Type} → Nest α → Nat
  | _, .nil => 0
  | _, .cons _ .nil => 0
  | _, .cons _ (.cons _ r) => 1 + r.pairsOfLevels

def pairsOfLevelsT := #leanscript_to_term Nest.pairsOfLevels
example : pairsOfLevelsT.run n3T.run = (1 : Nat) := rfl
#guard n3.pairsOfLevels == 1

/-! ## Refusals -/

/-- An element read at its Lean type: in the language it is an element of `Nest.Elem Nat`. -/
def headNat : Nest Nat → Option Nat
  | .nil => none
  | .cons a _ => some a

/--
error: LeanScript: the field `a` of `NestTest.Nest.cons` is used at the index
  Nat
of `NestTest.Nest`: the language reads the family at one index, where the field is an element of
  Nest.Elem Nat
so it can only be used by a function generic in the index
-/
#guard_msgs in
#leanscript_to_term headNat

-- `Unit` and `Empty` elements stay refused (a unit-like or an empty field)
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature ProgUnit where
  u := Nest Unit

/--
error: LeanScript: the type
  Empty
has no constructor (it has no value)
-/
#guard_msgs in
leanscript_signature ProgEmpty where
  e := Nest Empty

/-- One field-less constructor: one value. -/
inductive OnePt : Type → Type 1 where
  | a {α : Type} : OnePt α

/--
error: LeanScript: the type
  OnePt Nat
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_get_ty (OnePt Nat)

/-- A constructor at a fixed index (a GADT) is refused. -/
inductive G : Type → Type 1 where
  | nat : Nat → G Nat
  | any {α : Type} : α → G (α × α) → G α

/--
error: LeanScript: the constructor `NestTest.G.nat` of the type-indexed family `NestTest.G` builds a value at the index
  Nat
which is not a variable: only families whose constructors are generic in the index are supported
-/
#guard_msgs in
#leanscript_get_ty (G Nat)

/-- Recursion at an index in which the index is not positive: no element type. -/
inductive Neg : Type → Type 1 where
  | nil {α : Type} : Neg α
  | cons {α : Type} : α → Neg (α → Nat) → Neg α

/--
error: LeanScript: the element type `NestTest.Neg.Elem` of the type-indexed family `NestTest.Neg` is not a valid inductive type: (kernel) arg #2 of 'NestTest.Neg.Elem.node' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
#leanscript_get_ty (Neg Nat)

end NestTest
