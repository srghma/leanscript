module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Inductive families: their indices are erased

The language has no dependent types, so an inductive family is read with its **indices
erased** (`LeanScript.Gen.normType`): `Vec α n` is the datatype `Vec α` of vectors of every
length.  A constructor field that only names an index (`n` in `Vec.cons {n} a v`, the length
of `v`) is erased too (`LeanScript.Gen.erasedFields`): it is recovered from the other fields.

* `Vec α` is a declared recursive datatype `nil | cons α (Vec α)`: a linked list (not
  `Ty.array`: Lean's `Vec` is built like `List`).  Lean's own `Vector α n` is a wrapper of an
  `Array`, so it stays `Ty.array`.
* `Matrix` is a record of `rows : Nat`, `cols : Nat` and `cells`, a list of lists: `Vec (Vec
  Nat cols) rows` is `Vec (Vec Nat)`, a declared datatype whose `cons` holds a `Vec Nat`.
  `rows` and `cols` are fields of a structure, not indices, so they stay.

At **closed** indices a family can have no value, one, or two (`Vec Nat 0` has one): it is
refused as a declared type (field, parameter, result, signature entry) like every other such
type.  Two points are only ever `Bool`.  As the type of a subterm (`Vec.nil` inside
`Vec.cons 2 Vec.nil`) it is just the datatype the value belongs to.
-/

namespace IndexedFamilyTest

open LeanScript

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} : α → Vec α n → Vec α (n + 1)

structure Matrix where
  rows : Nat
  cols : Nat
  cells : Vec (Vec Nat cols) rows

leanscript_signature Prog where
  vec := Vec Nat 5
  mat := Matrix

/-! ## `Vec Nat`: a linked list -/

-- [SKIPPED BY PROFILE_LAKE] example : ∃ r, Prog.vec = .data r := ⟨_, rfl⟩
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Vec Nat 3) : Ty Prog.ks) = Prog.vec := rfl

/--
info: IndexedFamilyTest.Prog.Vec.cons {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o1) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor Vec.cons (α := Nat)

/--
info: IndexedFamilyTest.Prog.Vec.nil {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) none
-/
#guard_msgs in
#leanscript_get_ctor Vec.nil (α := Nat)

/--
info: IndexedFamilyTest.Prog.Vec.cases {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {d : Nat} {τ : Ty Prog.ks} {js : JCtx Prog.ks}
  {ℓ : Nat} {o0 o1 : Lvl} (scrut : Neu Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) ℓ)
  (on_nil : Term Prog.Δ d Φ (UCtx.annot d [] [] ++ Γ) τ js o0)
  (on_cons : Term Prog.Δ d Φ (UCtx.annot d [Ty.prim LeanPrimTy.nat, Ty.data (Ref.here 0).there] [] ++ Γ) τ js o1) :
  Term Prog.Δ d Φ Γ τ js (some (Lvl.meetL ℓ (o0.meet o1)))
-/
#guard_msgs in
#leanscript_get_cases Vec (α := Nat)

def v2 : Vec Nat 2 := .cons 1 (.cons 2 .nil)
def v2T := #leanscript_to_term v2

def Vec.sum {n : Nat} : Vec Nat n → Nat
  | .nil => 0
  | .cons a v => a + v.sum

-- The index `n` is erased: the translation takes the vector only.
/--
info: Vec.sum : Term Prog.Δ 0 [] [] ((Ty.data (Ref.here 0).there).fn (Ty.prim LeanPrimTy.nat)) [] none
-/
#guard_msgs in
#leanscript_to_term Vec.sum

def vecSumT := #leanscript_to_term Vec.sum
-- [SKIPPED BY PROFILE_LAKE] example : vecSumT.run v2T.run = (3 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard v2.sum == 3

def Vec.double {n : Nat} : Vec Nat n → Vec Nat n
  | .nil => .nil
  | .cons a v => .cons (2 * a) v.double

def vecDoubleT := #leanscript_to_term Vec.double
-- [SKIPPED BY PROFILE_LAKE] example : vecSumT.run (vecDoubleT.run v2T.run) = (6 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard v2.double.sum == 6

/-! ## `Matrix`: two numbers and a list of lists -/

-- [SKIPPED BY PROFILE_LAKE] example : ∃ r, Prog.mat = .record .nat (.cons .nat (.one (.data r))) := ⟨_, rfl⟩

/--
info: IndexedFamilyTest.Prog.Matrix.mk {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 o2 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o1)
  (x2 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0)) o2) :
  PExpr Prog.Δ Φ Γ
    ((Ty.prim LeanPrimTy.nat).record (Fields.cons (Ty.prim LeanPrimTy.nat) (Fields.one (Ty.data (Ref.here 0)))))
    (o0.meet (o1.meet (o2.meet none)))
-/
#guard_msgs in
#leanscript_get_ctor Matrix.mk

-- The cells hold `Vec Nat`, the older datatype.
/--
info: IndexedFamilyTest.Prog.Vec.cons_1 {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0)) o1) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0)) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor Vec.cons (α := Vec Nat 2)

def m : Matrix := ⟨2, 2, .cons (.cons 1 (.cons 2 .nil)) (.cons (.cons 3 (.cons 4 .nil)) .nil)⟩
def mT := #leanscript_to_term m

def Matrix.size (m : Matrix) : Nat := m.rows * m.cols
def matSizeT := #leanscript_to_term Matrix.size
-- [SKIPPED BY PROFILE_LAKE] example : matSizeT.run mT.run = (4 : Nat) := rfl

/-- The sum of every cell, by recursion on the rows (a list of lists). -/
def Vec.sumRows {r c : Nat} : Vec (Vec Nat c) r → Nat
  | .nil => 0
  | .cons row rest =>
    (match row with
     | .nil => 0
     | .cons a _ => a) + rest.sumRows

def sumRowsT := #leanscript_to_term Vec.sumRows
def Matrix.firstColumnSum (m : Matrix) : Nat := m.cells.sumRows
-- [SKIPPED BY PROFILE_LAKE] example : sumRowsT.run (mT.run.2.2) = (4 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard m.firstColumnSum == 4

/-! ## Lean's `Vector` stays an array -/

-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Vector Nat 3) : Ty []) = .array .nat := rfl

/-! ## Refusals -/

/--
error: LeanScript: the type
  Vec Nat 0
has one value (only `IndexedFamilyTest.Vec.nil` builds a value at these indices, and it has no field)
-/
#guard_msgs in
#leanscript_get_ty (Vec Nat 0)

def empty : Vec Nat 0 := .nil
/--
error: LeanScript: the type
  Vec Nat 0
has one value (only `IndexedFamilyTest.Vec.nil` builds a value at these indices, and it has no field)
-/
#guard_msgs in
#leanscript_to_term empty

structure WithEmpty where
  x : Nat
  v : Vec Nat 0

/--
error: LeanScript: the type
  Vec Nat 0
has one value (only `IndexedFamilyTest.Vec.nil` builds a value at these indices, and it has no field)
-/
#guard_msgs in
#leanscript_get_ty WithEmpty

/-- At index `0` only two field-less constructors build a value. -/
inductive Two : Nat → Type where
  | a : Two 0
  | b : Two 0
  | c : Nat → Two 1

/--
error: LeanScript: the type
  Two 0
has two values (only field-less constructors build a value at these indices): two points are only ever `Bool`
-/
#guard_msgs in
#leanscript_get_ty (Two 0)

-- No constructor builds a value at index `2`.
/--
error: LeanScript: the type
  Two 2
has no value (no constructor builds a value at these indices)
-/
#guard_msgs in
#leanscript_get_ty (Two 2)

/-- The index is erased, so it has no value in the language. -/
def Vec.len {n : Nat} (_ : Vec Nat n) : Nat := n

/--
error: LeanScript: the local `n` has no value in the language (a proof, an instance or an erased field)
-/
#guard_msgs in
#leanscript_to_term Vec.len

/-- The `nil` branch is unreachable in Lean, but reachable once the index is erased. -/
def Vec.head {n : Nat} : Vec Nat (n + 1) → Nat
  | .cons a _ => a

/--
error: LeanScript: a branch that Lean proves unreachable
  False.elim ⋯ ⋯
is not supported: the language has no term for it (and once the indices of an inductive family are erased, as `Vec α (n + 1)` is `Vec α`, a list, such a branch is reachable)
-/
#guard_msgs in
#leanscript_to_term Vec.head

/-! ## Caveats: only what closed indices show is checked -/

/-- `Idx n` has one value for every `n`; with the index erased it is a unary number. -/
inductive Idx : Nat → Type where
  | z : Idx 0
  | s {n : Nat} : Idx n → Idx (n + 1)

-- `Vec Bool 1` has two values in Lean, but its index is erased: it is a list of `Bool`.
leanscript_signature Prog2 where
  vecBool := Vec Bool 1
  idx := Idx 3

/--
info: IndexedFamilyTest.Prog2.Vec.cons {Φ : KCtx Prog2.ks} {Γ : UCtx Prog2.ks} {o0 o1 : Lvl}
  (x0 : PExpr Prog2.Δ Φ Γ (Ty.prim LeanPrimTy.bool) o0) (x1 : PExpr Prog2.Δ Φ Γ (Ty.data (Ref.here 0).there) o1) :
  PExpr Prog2.Δ Φ Γ (Ty.data (Ref.here 0).there) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor Vec.cons (α := Bool)

/--
info: IndexedFamilyTest.Prog2.Idx.s {Φ : KCtx Prog2.ks} {Γ : UCtx Prog2.ks} {o0 : Lvl}
  (x0 : PExpr Prog2.Δ Φ Γ (Ty.data (Ref.here 0)) o0) : PExpr Prog2.Δ Φ Γ (Ty.data (Ref.here 0)) (o0.meet none)
-/
#guard_msgs in
#leanscript_get_ctor Idx.s

end IndexedFamilyTest
