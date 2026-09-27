module

public import TermTests.IndexedFamilyTest

@[expose] public section

set_option autoImplicit false

/-!
# Proofs about the translation of `Vec` and `Matrix`

`TermTests/IndexedFamilyTest.lean` checks the translation of the inductive family `Vec` and of
`Matrix` on sample values.  This file proves, for **every** input:

* the translated `Vec.sum`, `Vec.double` (`#leanscript_to_term`) and `Vec.sumRows` compute
  what the Lean functions compute (`vecSumT_correct`, `vecDoubleT_correct`,
  `sumRowsT_correct`), and so does `Matrix.size` (`matSizeT_correct`);
* erasing the index loses nothing: two vectors with the same value in the language are the
  same vector of the same length (`vecEnc_injective`), and the vectors of every length are the
  lists (`Vec.sigma_equiv_list`, `vecEnc_eq_listEnc`);
* the instances refused at closed indices have no, one or two values (`vec_zero_subsingleton`,
  `two_zero_two_values`, `two_two_empty`), and the two caveats are real
  (`vecBool_one_two_values`, `idx_subsingleton`).

A value is encoded with the constructors the generator builds (`Prog.Vec.cons`, …), so the
encoding is the one the translated programs see.  The fold equation used throughout is the new
general `LeanScript.DSig.dataRec_dataIn`.
-/

namespace IndexedFamilyTest
open LeanScript

/-- The value of `Vec Nat` a Lean vector translates to, built with the generated
    constructors. -/
def vecEnc : {n : Nat} → Vec Nat n → Ty.Den Prog.Δ Prog.vec
  | _, .nil => (Prog.Vec.nil (Γ := [])).run
  | _, .cons a v =>
    (Prog.Vec.cons (Γ := [.nat, Prog.vec]) (.var .head) (.var (.tail .head))).eval (a, vecEnc v, ())

/-- A value of `nat` is a `Nat`. -/
def natOf {ks : List Nat} {Δ : DSig ks} (x : Ty.Den Δ .nat) : Nat := x

/-- The block of `Vec Nat` in `Prog`. -/
abbrev VB := Prog.Δ.block BRef.here.there

/-- A fold over `Vec Nat` whose branch sees the value `W` of the enclosing `fun`. -/
def foldVec {τ : Ty Prog.ks}
    (brs : (i : Fin (VB.k + 1)) → Term Prog.Δ (VB.recBody (fun _ => τ) i :: [Prog.vec]) τ [])
    (W c : Ty.Den Prog.Δ Prog.vec) : Ty.Den Prog.Δ τ :=
  Prog.Δ.dataRec BRef.here.there (fun _ => τ) (fun i x => (brs i).eval (x, W, ()) ()) 0 c

/-- The translated `Vec.sum` is a fold, with one step per constructor. -/
theorem sum_facts : ∃ brs : (i : Fin (VB.k + 1)) → Term Prog.Δ (VB.recBody (fun _ => .nat) i :: [Prog.vec]) .nat [],
    (∀ c, vecSumT.run c = foldVec brs c c) ∧
    (∀ W (a : Nat) {n : Nat} (v : Vec Nat n),
      natOf (foldVec brs W (vecEnc (.cons a v))) = a + natOf (foldVec brs W (vecEnc v))) ∧
    (∀ W, natOf (foldVec brs W (vecEnc (Vec.nil (α := Nat)))) = 0) := by
  refine ⟨_, fun c => rfl, ?_, fun W => rfl⟩
  intro W a n v
  unfold natOf foldVec
  refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
  rfl

/-- **`Vec.sum` is translated correctly**: on every vector, the translated program returns the
    sum of its elements. -/
theorem vecSumT_correct {n : Nat} (v : Vec Nat n) : natOf (vecSumT.run (vecEnc v)) = v.sum := by
  obtain ⟨brs, hrun, hcons, hnil⟩ := sum_facts
  have key : ∀ W, natOf (foldVec brs W (vecEnc v)) = v.sum := by
    intro W
    induction v with
    | nil => exact hnil W
    | cons a v ih => rw [hcons, ih]; rfl
  exact (congrArg natOf (hrun (vecEnc v))).trans (key _)

/-- The value `Vec.cons a c` of the language, for an element `a` and a tail `c`. -/
def consEnc (a : Nat) (c : Ty.Den Prog.Δ Prog.vec) : Ty.Den Prog.Δ Prog.vec :=
  (Prog.Vec.cons (Γ := [.nat, Prog.vec]) (.var .head) (.var (.tail .head))).eval (a, c, ())

/-- The translated `Vec.double` is a fold, with one step per constructor. -/
theorem double_facts :
    ∃ brs : (i : Fin (VB.k + 1)) → Term Prog.Δ (VB.recBody (fun _ => Prog.vec) i :: [Prog.vec]) Prog.vec [],
    (∀ c, vecDoubleT.run c = foldVec brs c c) ∧
    (∀ W (a : Nat) {n : Nat} (v : Vec Nat n),
      foldVec brs W (vecEnc (.cons a v)) = consEnc (2 * a) (foldVec brs W (vecEnc v))) ∧
    (∀ W, foldVec brs W (vecEnc (Vec.nil (α := Nat))) = vecEnc (Vec.nil (α := Nat))) := by
  refine ⟨_, fun c => rfl, ?_, fun W => rfl⟩
  intro W a n v
  unfold foldVec
  refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
  rfl

/-- **`Vec.double` is translated correctly**: on every vector, the translated program returns
    the encoding of the doubled vector. -/
theorem vecDoubleT_correct {n : Nat} (v : Vec Nat n) :
    vecDoubleT.run (vecEnc v) = vecEnc v.double := by
  obtain ⟨brs, hrun, hcons, hnil⟩ := double_facts
  have key : ∀ W, foldVec brs W (vecEnc v) = vecEnc v.double := by
    intro W
    induction v with
    | nil => exact hnil W
    | cons a v ih => rw [hcons, ih]; rfl
  exact (hrun (vecEnc v)).trans (key _)

/-- The two translations compose: summing the doubled vector. -/
theorem vecSumT_vecDoubleT {n : Nat} (v : Vec Nat n) :
    natOf (vecSumT.run (vecDoubleT.run (vecEnc v))) = 2 * v.sum := by
  rw [vecDoubleT_correct, vecSumT_correct]
  induction v with
  | nil => rfl
  | cons a v ih => simp only [Vec.double, Vec.sum, ih]; omega

/-! ## The encoding forgets nothing: the length is recovered -/

/-- One layer out of a value of `Vec Nat`: `none` for `nil`, the head and tail for `cons`. -/
def vecOut (c : Ty.Den Prog.Δ Prog.vec) : Option (Nat × Ty.Den Prog.Δ Prog.vec) :=
  Prog.Δ.dataOut BRef.here.there 0 c

theorem vecOut_nil : vecOut (vecEnc (Vec.nil (α := Nat))) = none :=
  DSig.dataOut_dataIn _ _ _ _

theorem vecOut_cons {n : Nat} (a : Nat) (v : Vec Nat n) :
    vecOut (vecEnc (.cons a v)) = some (a, vecEnc v) :=
  DSig.dataOut_dataIn _ _ _ _

/-- **Erasing the index loses nothing**: two vectors (of any lengths) with the same value in
    the language are the same vector, of the same length. -/
theorem vecEnc_injective {n m : Nat} (v : Vec Nat n) (w : Vec Nat m) (h : vecEnc v = vecEnc w) :
    (⟨n, v⟩ : (k : Nat) × Vec Nat k) = ⟨m, w⟩ := by
  induction v generalizing m with
  | nil =>
    cases w with
    | nil => rfl
    | cons b w =>
      have h' := congrArg vecOut h
      rw [vecOut_nil, vecOut_cons] at h'
      cases h'
  | cons a v ih =>
    cases w with
    | nil =>
      have h' := congrArg vecOut h
      rw [vecOut_nil, vecOut_cons] at h'
      cases h'
    | cons b w =>
      have h' := congrArg vecOut h
      rw [vecOut_cons, vecOut_cons] at h'
      have h2 := Option.some.inj h'
      have hab : a = b := congrArg Prod.fst h2
      have hvw : vecEnc v = vecEnc w := congrArg Prod.snd h2
      subst hab
      cases ih w hvw
      rfl

/-! ## `Matrix` -/

/-- The declared datatype `Vec (Vec Nat)`: the rows of a matrix. -/
abbrev rowsTy : Ty Prog.ks := .data (.here 0)

/-- The value of `Vec (Vec Nat)` the rows of a matrix translate to. -/
def rowsEnc {c : Nat} : {r : Nat} → Vec (Vec Nat c) r → Ty.Den Prog.Δ rowsTy
  | _, .nil => (Prog.Vec.nil_1 (Γ := [])).run
  | _, .cons row rest =>
    (Prog.Vec.cons_1 (Γ := [Prog.vec, rowsTy]) (.var .head) (.var (.tail .head))).eval
      (vecEnc row, rowsEnc rest, ())

/-- The value a matrix translates to: two numbers and its rows. -/
def matEnc (m : Matrix) : Ty.Den Prog.Δ Prog.mat := (m.rows, m.cols, rowsEnc m.cells)

/-- **`Matrix.size` is translated correctly**, on every matrix. -/
theorem matSizeT_correct (m : Matrix) : natOf (matSizeT.run (matEnc m)) = m.size := rfl

/-- The encodings agree with the values the translator builds for the sample vector and
    matrix of the tests. -/
theorem v2T_run : v2T.run = vecEnc v2 := rfl
theorem mT_run : mT.run = matEnc m := rfl

/-- The block of `Vec (Vec Nat)` in `Prog`. -/
abbrev RB := Prog.Δ.block BRef.here

/-- A fold over the rows `Vec (Vec Nat)` whose branch sees the value `W` of the enclosing
    `fun`. -/
def foldRows {τ : Ty Prog.ks}
    (brs : (i : Fin (RB.k + 1)) → Term Prog.Δ (RB.recBody (fun _ => τ) i :: [rowsTy]) τ [])
    (W c : Ty.Den Prog.Δ rowsTy) : Ty.Den Prog.Δ τ :=
  Prog.Δ.dataRec BRef.here (fun _ => τ) (fun i x => (brs i).eval (x, W, ()) ()) 0 c

/-- The first element of a vector, or `0`. -/
def headOr0 {n : Nat} : Vec Nat n → Nat
  | .nil => 0
  | .cons a _ => a

/-- The translated `Vec.sumRows` is a fold, with one step per constructor. -/
theorem sumRows_facts :
    ∃ brs : (i : Fin (RB.k + 1)) → Term Prog.Δ (RB.recBody (fun _ => .nat) i :: [rowsTy]) .nat [],
    (∀ c, sumRowsT.run c = foldRows brs c c) ∧
    (∀ W {c r : Nat} (row : Vec Nat c) (rest : Vec (Vec Nat c) r),
      natOf (foldRows brs W (rowsEnc (.cons row rest))) =
        headOr0 row + natOf (foldRows brs W (rowsEnc rest))) ∧
    (∀ W {c : Nat}, natOf (foldRows brs W (rowsEnc (Vec.nil (α := Vec Nat c)))) = 0) := by
  refine ⟨_, fun c => rfl, ?_, fun W => rfl⟩
  intro W c r row rest
  unfold natOf foldRows
  refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
  cases row <;> rfl

/-- **`Vec.sumRows` is translated correctly**: on the rows of every matrix, the translated
    program returns the sum of the first column. -/
theorem sumRowsT_correct {c r : Nat} (cells : Vec (Vec Nat c) r) :
    natOf (sumRowsT.run (rowsEnc cells)) = cells.sumRows := by
  obtain ⟨brs, hrun, hcons, hnil⟩ := sumRows_facts
  have key : ∀ W, natOf (foldRows brs W (rowsEnc cells)) = cells.sumRows := by
    intro W
    induction cells with
    | nil => exact hnil W
    | cons row rest ih =>
      rw [hcons, ih]
      cases row <;> rfl
  exact (congrArg natOf (hrun (rowsEnc cells))).trans (key _)

/-- On a whole matrix: the sum of its first column. -/
theorem firstColumnSum_correct (m : Matrix) :
    natOf (sumRowsT.run (matEnc m).2.2) = m.firstColumnSum :=
  sumRowsT_correct m.cells

/-! ## Erasing the index: `Vec α` is a linked list -/

/-- The elements of a vector. -/
def Vec.toList {α : Type} : {n : Nat} → Vec α n → List α
  | _, .nil => []
  | _, .cons a v => a :: v.toList

/-- The vector of a list, at its length. -/
def Vec.ofList {α : Type} : (l : List α) → Vec α l.length
  | [] => .nil
  | a :: l => .cons a (Vec.ofList l)

theorem Vec.length_toList {α : Type} {n : Nat} (v : Vec α n) : v.toList.length = n := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [Vec.toList, ih]

theorem Vec.toList_ofList {α : Type} (l : List α) : (Vec.ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Vec.ofList, Vec.toList, ih]

theorem Vec.ofList_toList {α : Type} {n : Nat} (v : Vec α n) :
    (⟨v.toList.length, Vec.ofList v.toList⟩ : (k : Nat) × Vec α k) = ⟨n, v⟩ := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [Vec.toList, Vec.ofList, List.length_cons]
    revert ih
    generalize v.toList = l
    intro ih
    cases ih
    rfl

/-- **The vectors of every length are the lists**: `(n : Nat) × Vec α n` and `List α` are
    in bijection (`toList`, and `ofList` at the length), so erasing the index of `Vec α n`
    gives a linked list, and the length is recovered as the length of the list. -/
theorem Vec.sigma_equiv_list (α : Type) :
    (∀ l : List α, (Vec.ofList l).toList = l) ∧
    (∀ (s : (k : Nat) × Vec α k), (⟨s.2.toList.length, Vec.ofList s.2.toList⟩ : (k : Nat) × Vec α k) = s) :=
  ⟨Vec.toList_ofList, fun ⟨_, v⟩ => Vec.ofList_toList v⟩

/-- The value of a vector depends only on its elements: it is the linked list of them. -/
def listEnc : List Nat → Ty.Den Prog.Δ Prog.vec
  | [] => vecEnc (Vec.nil (α := Nat))
  | a :: l => consEnc a (listEnc l)

theorem vecEnc_eq_listEnc {n : Nat} (v : Vec Nat n) : vecEnc v = listEnc v.toList := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [Vec.toList, listEnc, ← ih]; rfl

/-! ## Why closed indices are checked: the refused instances have 0, 1 or 2 values -/

/-- `Vec α 0` has one value (so it is refused, like `Unit`). -/
theorem vec_zero_subsingleton {α : Type} (v w : Vec α 0) : v = w := by
  cases v; cases w; rfl

/-- `Two 0` has exactly two values (so it is refused: two points are only ever `Bool`). -/
theorem two_zero_two_values : (∀ t : Two 0, t = .a ∨ t = .b) ∧ Two.a ≠ Two.b :=
  ⟨fun t => by cases t <;> simp, fun h => by cases h⟩

/-- `Two 2` has no value. -/
theorem two_two_empty (t : Two 2) : False := by
  cases t

/-- A caveat: `Vec Bool 1` has exactly two values in Lean, yet it is accepted (as a list of
    `Bool`), since only the constructors that fit the index are checked, one level deep. -/
theorem vecBool_one_two_values :
    (∀ v : Vec Bool 1, v = .cons true .nil ∨ v = .cons false .nil) ∧
      (Vec.cons true .nil : Vec Bool 1) ≠ .cons false .nil := by
  refine ⟨fun v => ?_, fun h => ?_⟩
  · match v with
    | .cons true .nil => exact .inl rfl
    | .cons false .nil => exact .inr rfl
  · cases h

/-- A caveat: `Idx n` has one value at every index, yet it is accepted (as a unary number),
    since nothing is checked at an index that is a variable. -/
theorem idx_subsingleton {n : Nat} (x y : Idx n) : x = y := by
  induction x with
  | z => cases y; rfl
  | s x ih =>
    cases y with
    | s y => rw [ih y]

end IndexedFamilyTest
