module

public import LeanScript.Term.Optimize.IntUnit

@[expose] public section

set_option autoImplicit false

/-!
# An addition of a negative literal, written as a subtraction

The optimiser writes `x - k` as `x + (-k)` (`Neu.intNeg?`, `LeanScript.Term.Optimize.IntUnit`),
so that its sums (`Term.arithWalk`) fold the literal with the ones around it.  What is left is
an addition of a literal that is often negative, as an integer of its type: `x + -1` at `Int8`,
`x + 255` at `UInt8`.  The conversion to JavaScript writes such an addition back as the
subtraction it reads as (`Neu.addLitAsSub`): `x - 1` in both cases (`((x - 1) << 24) >> 24`,
`(x - 1) & 255`), for `UInt8`–`UInt64`, `Int8`–`Int64` and `Int`.

It is not done by the optimiser: the subtraction would be written as an addition again.
Proved: the value is unchanged (`Neu.addLitAsSub_eval`).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

namespace IntUnit

theorem uint8_add_lit (a b : UInt8) : UInt8.sub a (-b) = UInt8.add a b := by
  show a - -b = a + b; rw [UInt8.sub_eq_add_neg, UInt8.neg_neg]
theorem uint16_add_lit (a b : UInt16) : UInt16.sub a (-b) = UInt16.add a b := by
  show a - -b = a + b; rw [UInt16.sub_eq_add_neg, UInt16.neg_neg]
theorem uint32_add_lit (a b : UInt32) : UInt32.sub a (-b) = UInt32.add a b := by
  show a - -b = a + b; rw [UInt32.sub_eq_add_neg, UInt32.neg_neg]
theorem uint64_add_lit (a b : UInt64) : UInt64.sub a (-b) = UInt64.add a b := by
  show a - -b = a + b; rw [UInt64.sub_eq_add_neg, UInt64.neg_neg]
theorem int8_add_lit (a b : Int8) : Int8.sub a (-b) = Int8.add a b := by
  show a - -b = a + b; rw [Int8.sub_eq_add_neg, Int8.neg_neg]
theorem int16_add_lit (a b : Int16) : Int16.sub a (-b) = Int16.add a b := by
  show a - -b = a + b; rw [Int16.sub_eq_add_neg, Int16.neg_neg]
theorem int32_add_lit (a b : Int32) : Int32.sub a (-b) = Int32.add a b := by
  show a - -b = a + b; rw [Int32.sub_eq_add_neg, Int32.neg_neg]
theorem int64_add_lit (a b : Int64) : Int64.sub a (-b) = Int64.add a b := by
  show a - -b = a + b; rw [Int64.sub_eq_add_neg, Int64.neg_neg]
theorem int_add_lit (a b : Int) : Int.sub a (-b) = Int.add a b := by
  show a - -b = a + b; rw [Int.sub_eq_add_neg, Int.neg_neg]

end IntUnit

/-- Is the literal `k` of an addition better written as the subtraction of `-k`: is `-k` a
    smaller positive number (`x + 255` at `UInt8` is `x - 1`, `x + -3` at `Int8` is `x - 3`)? -/
def negLitSmaller : (p : LeanPrimTy) → p.denote → Bool
  | .uint8, k => decide ((-k).toNat < k.toNat)
  | .uint16, k => decide ((-k).toNat < k.toNat)
  | .uint32, k => decide ((-k).toNat < k.toNat)
  | .uint64, k => decide ((-k).toNat < k.toNat)
  | .int8, k => decide (k < 0) && decide (0 < -k)
  | .int16, k => decide (k < 0) && decide (0 < -k)
  | .int32, k => decide (k < 0) && decide (0 < -k)
  | .int64, k => decide (k < 0) && decide (0 < -k)
  | .int, k => decide (k < 0)
  | _, _ => false

/-- **An addition of a literal written as a subtraction** when the literal is a negative number,
    as an integer of its type (`negLitSmaller`): `x + -3` is `x - 3`, `x + 255` at `UInt8` is
    `x - 1`.  Applied by the conversion to JavaScript (the optimiser keeps the additions, which
    its sums fold). -/
def Neu.addLitAsSub? {ℓ : Nat} : (p : LeanPrimTy) → (n : Neu Δ Φ Γ (.prim p) ℓ) →
    Option {m : Neu Δ Φ Γ (.prim p) ℓ // ∀ κ ρ, m.eval κ ρ = n.eval κ ρ}
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .uint8 v then
        some ⟨.extern (.uint8BasicExtern .lean_uint8_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt8.sub (x.eval κ ρ) (-v) = UInt8.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.uint8_add_lit _ _⟩
      else none
    | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .uint16 v then
        some ⟨.extern (.uint16BasicExtern .lean_uint16_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt16.sub (x.eval κ ρ) (-v) = UInt16.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.uint16_add_lit _ _⟩
      else none
    | none => none
  | .uint32, .extern (.uintBasicAuxExtern .lean_uint32_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .uint32 v then
        some ⟨.extern (.uintBasicAuxExtern .lean_uint32_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt32.sub (x.eval κ ρ) (-v) = UInt32.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.uint32_add_lit _ _⟩
      else none
    | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .uint64 v then
        some ⟨.extern (.uint64BasicExtern .lean_uint64_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt64.sub (x.eval κ ρ) (-v) = UInt64.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.uint64_add_lit _ _⟩
      else none
    | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .int8 v then
        some ⟨.extern (.int8BasicExtern .lean_int8_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int8.sub (x.eval κ ρ) (-v) = Int8.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.int8_add_lit _ _⟩
      else none
    | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .int16 v then
        some ⟨.extern (.int16BasicExtern .lean_int16_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int16.sub (x.eval κ ρ) (-v) = Int16.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.int16_add_lit _ _⟩
      else none
    | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .int32 v then
        some ⟨.extern (.int32BasicExtern .lean_int32_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int32.sub (x.eval κ ρ) (-v) = Int32.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.int32_add_lit _ _⟩
      else none
    | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .int64 v then
        some ⟨.extern (.int64BasicExtern .lean_int64_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int64.sub (x.eval κ ρ) (-v) = Int64.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.int64_add_lit _ _⟩
      else none
    | none => none
  | .int, .extern (.intBasicExtern .lean_int_add) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if negLitSmaller .int v then
        some ⟨.extern (.intBasicExtern .lean_int_sub) (.cons x (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int.sub (x.eval κ ρ) (-v) = Int.add (x.eval κ ρ) (y.eval κ ρ)
            rw [hy]; exact IntUnit.int_add_lit _ _⟩
      else none
    | none => none
  | _, _ => none

/-- `Neu.addLitAsSub?` on a neutral expression of any type. -/
def Neu.addLitAsSub : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Option (Neu Δ Φ Γ τ ℓ)
  | .prim p, _, n => (Neu.addLitAsSub? p n).map (·.1)
  | _, _, _ => none

theorem Neu.addLitAsSub_eval {τ : Ty ks} {ℓ : Nat} (n m : Neu Δ Φ Γ τ ℓ)
    (h : n.addLitAsSub = some m) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : m.eval κ ρ = n.eval κ ρ := by
  cases τ with
  | prim p =>
    have h' : (Neu.addLitAsSub? p n).map (·.1) = some m := h
    cases hr : Neu.addLitAsSub? p n with
    | none => rw [hr] at h'; cases h'
    | some r => rw [hr] at h'; cases h'; exact r.2 κ ρ
  | _ => cases h

end LeanScript

end
