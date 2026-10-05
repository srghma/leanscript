module

public import LeanScript.Term.Optimize.BitVecConv

@[expose] public section

set_option autoImplicit false

/-!
# Units and negations of integer operations

An integer operation with a unit operand is that operand, and a double negation is the
operand:

| call | becomes |
|---|---|
| `x - 0`, `x / 1` | `x` |
| `-(-x)` | `x` |

for `UInt8`–`UInt64`, `Int8`–`Int64`, `Int` (`-(-x)`, `x - 0`, and `x / 1` for both `Int.ediv`
and the truncating `Int.tdiv`) and `Nat` (`x - 0`, `x / 1`).  A product by `-1` and a subtraction
from `0` are written as the negation they are:

| call | becomes |
|---|---|
| `x * -1` (`x * 255` at `UInt8`, …) | `-x` |
| `0 - x` | `-x` |

for the fixed-width integers and `Int` (in JavaScript a negation is `-x & 255`, `-x | 0`,
`0 - x` …, cheaper than a product: `Math.imul`, or a call that checks for overflow).

These hold for every value (the fixed-width operations are modulo `2ⁿ`).  The sums and products
of `Term.arithWalk` put a literal operand last, so `x * -1` is the form a chain leaves
(`intValues (fun a b => a * c < b)` at `b = -1` gives `c * -1`).

`Neu.intUnit` is applied by `Term.arithWalk` at every neutral expression of a leaf type
(`Neu.normArithPrim`), bottom-up, after the sums and products are normalised.  Proved: the
value is unchanged (`Neu.intUnit_eval`).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

/-- The value of an operand that is a literal, with the facts that it is closed and has that
    value. -/
def PExpr.primLit? {p : LeanPrimTy} : {o : Lvl} → (e : PExpr Δ Φ Γ (.prim p) o) →
    Option {v : p.denote // o = none ∧ ∀ κ ρ, e.eval κ ρ = v}
  | _, .lit _ v => some ⟨v, rfl, fun _ _ => rfl⟩
  | _, _ => none

namespace IntUnit

theorem uint8_sub_zero (a : UInt8) : a = UInt8.sub a 0 := (UInt8.sub_zero a).symm
theorem uint8_div_one (a : UInt8) : a = UInt8.div a 1 := UInt8.div_one.symm
theorem uint8_neg_neg (a : UInt8) : a = UInt8.neg (UInt8.neg a) := UInt8.neg_neg.symm
theorem uint8_mul_neg_one (a : UInt8) : UInt8.neg a = UInt8.mul a (-1) := by
  show -a = a * -1; rw [UInt8.mul_neg, UInt8.mul_one]
theorem uint8_zero_sub (a : UInt8) : UInt8.neg a = UInt8.sub 0 a := (UInt8.zero_sub a).symm
theorem uint8_sub_lit (a b : UInt8) : UInt8.add a (-b) = UInt8.sub a b := (UInt8.sub_eq_add_neg a b).symm
theorem uint16_sub_zero (a : UInt16) : a = UInt16.sub a 0 := (UInt16.sub_zero a).symm
theorem uint16_div_one (a : UInt16) : a = UInt16.div a 1 := UInt16.div_one.symm
theorem uint16_neg_neg (a : UInt16) : a = UInt16.neg (UInt16.neg a) := UInt16.neg_neg.symm
theorem uint16_mul_neg_one (a : UInt16) : UInt16.neg a = UInt16.mul a (-1) := by
  show -a = a * -1; rw [UInt16.mul_neg, UInt16.mul_one]
theorem uint16_zero_sub (a : UInt16) : UInt16.neg a = UInt16.sub 0 a := (UInt16.zero_sub a).symm
theorem uint16_sub_lit (a b : UInt16) : UInt16.add a (-b) = UInt16.sub a b := (UInt16.sub_eq_add_neg a b).symm
theorem uint32_sub_zero (a : UInt32) : a = UInt32.sub a 0 := (UInt32.sub_zero a).symm
theorem uint32_div_one (a : UInt32) : a = UInt32.div a 1 := UInt32.div_one.symm
theorem uint32_neg_neg (a : UInt32) : a = UInt32.neg (UInt32.neg a) := UInt32.neg_neg.symm
theorem uint32_mul_neg_one (a : UInt32) : UInt32.neg a = UInt32.mul a (-1) := by
  show -a = a * -1; rw [UInt32.mul_neg, UInt32.mul_one]
theorem uint32_zero_sub (a : UInt32) : UInt32.neg a = UInt32.sub 0 a := (UInt32.zero_sub a).symm
theorem uint32_sub_lit (a b : UInt32) : UInt32.add a (-b) = UInt32.sub a b := (UInt32.sub_eq_add_neg a b).symm
theorem uint64_sub_zero (a : UInt64) : a = UInt64.sub a 0 := (UInt64.sub_zero a).symm
theorem uint64_div_one (a : UInt64) : a = UInt64.div a 1 := UInt64.div_one.symm
theorem uint64_neg_neg (a : UInt64) : a = UInt64.neg (UInt64.neg a) := UInt64.neg_neg.symm
theorem uint64_mul_neg_one (a : UInt64) : UInt64.neg a = UInt64.mul a (-1) := by
  show -a = a * -1; rw [UInt64.mul_neg, UInt64.mul_one]
theorem uint64_zero_sub (a : UInt64) : UInt64.neg a = UInt64.sub 0 a := (UInt64.zero_sub a).symm
theorem uint64_sub_lit (a b : UInt64) : UInt64.add a (-b) = UInt64.sub a b := (UInt64.sub_eq_add_neg a b).symm
theorem int8_sub_zero (a : Int8) : a = Int8.sub a 0 := (Int8.sub_zero a).symm
theorem int8_div_one (a : Int8) : a = Int8.div a 1 := Int8.div_one.symm
theorem int8_neg_neg (a : Int8) : a = Int8.neg (Int8.neg a) := Int8.neg_neg.symm
theorem int8_mul_neg_one (a : Int8) : Int8.neg a = Int8.mul a (-1) := by
  show -a = a * -1; rw [Int8.mul_neg, Int8.mul_one]
theorem int8_zero_sub (a : Int8) : Int8.neg a = Int8.sub 0 a := (Int8.zero_sub a).symm
theorem int8_sub_lit (a b : Int8) : Int8.add a (-b) = Int8.sub a b := (Int8.sub_eq_add_neg a b).symm
theorem int16_sub_zero (a : Int16) : a = Int16.sub a 0 := (Int16.sub_zero a).symm
theorem int16_div_one (a : Int16) : a = Int16.div a 1 := Int16.div_one.symm
theorem int16_neg_neg (a : Int16) : a = Int16.neg (Int16.neg a) := Int16.neg_neg.symm
theorem int16_mul_neg_one (a : Int16) : Int16.neg a = Int16.mul a (-1) := by
  show -a = a * -1; rw [Int16.mul_neg, Int16.mul_one]
theorem int16_zero_sub (a : Int16) : Int16.neg a = Int16.sub 0 a := (Int16.zero_sub a).symm
theorem int16_sub_lit (a b : Int16) : Int16.add a (-b) = Int16.sub a b := (Int16.sub_eq_add_neg a b).symm
theorem int32_sub_zero (a : Int32) : a = Int32.sub a 0 := (Int32.sub_zero a).symm
theorem int32_div_one (a : Int32) : a = Int32.div a 1 := Int32.div_one.symm
theorem int32_neg_neg (a : Int32) : a = Int32.neg (Int32.neg a) := Int32.neg_neg.symm
theorem int32_mul_neg_one (a : Int32) : Int32.neg a = Int32.mul a (-1) := by
  show -a = a * -1; rw [Int32.mul_neg, Int32.mul_one]
theorem int32_zero_sub (a : Int32) : Int32.neg a = Int32.sub 0 a := (Int32.zero_sub a).symm
theorem int32_sub_lit (a b : Int32) : Int32.add a (-b) = Int32.sub a b := (Int32.sub_eq_add_neg a b).symm
theorem int64_sub_zero (a : Int64) : a = Int64.sub a 0 := (Int64.sub_zero a).symm
theorem int64_div_one (a : Int64) : a = Int64.div a 1 := Int64.div_one.symm
theorem int64_neg_neg (a : Int64) : a = Int64.neg (Int64.neg a) := Int64.neg_neg.symm
theorem int64_mul_neg_one (a : Int64) : Int64.neg a = Int64.mul a (-1) := by
  show -a = a * -1; rw [Int64.mul_neg, Int64.mul_one]
theorem int64_zero_sub (a : Int64) : Int64.neg a = Int64.sub 0 a := (Int64.zero_sub a).symm
theorem int64_sub_lit (a b : Int64) : Int64.add a (-b) = Int64.sub a b := (Int64.sub_eq_add_neg a b).symm
theorem int_sub_zero (a : Int) : a = Int.sub a 0 := (Int.sub_zero a).symm
theorem int_div_one (a : Int) : a = Int.tdiv a 1 := (Int.tdiv_one a).symm
theorem int_ediv_one (a : Int) : a = Int.ediv a 1 := (Int.ediv_one a).symm
theorem int_neg_neg (a : Int) : a = Int.neg (Int.neg a) := (Int.neg_neg a).symm
theorem int_mul_neg_one (a : Int) : Int.neg a = Int.mul a (-1) := (Int.mul_neg_one a).symm
theorem int_zero_sub (a : Int) : Int.neg a = Int.sub 0 a := (Int.zero_sub a).symm
theorem int_sub_lit (a b : Int) : Int.add a (-b) = Int.sub a b := Int.sub_eq_add_neg.symm
theorem nat_sub_zero (a : Nat) : a = Nat.sub a 0 := rfl
theorem nat_div_one (a : Nat) : a = Nat.div a 1 := (Nat.div_one a).symm

end IntUnit

/-- The negation of a value of a leaf type (the identity where there is none). -/
def negDen : (p : LeanPrimTy) → p.denote → p.denote
  | .uint8, a => UInt8.neg a
  | .uint16, a => UInt16.neg a
  | .uint32, a => UInt32.neg a
  | .uint64, a => UInt64.neg a
  | .int8, a => Int8.neg a
  | .int16, a => Int16.neg a
  | .int32, a => Int32.neg a
  | .int64, a => Int64.neg a
  | .int, a => Int.neg a
  | _, a => a

/-- The operand `y` of an operand written `-y` (a negation of a fixed-width integer or of an
    `Int`). -/
def PExpr.negOf? : (p : LeanPrimTy) → {o : Lvl} → (x : PExpr Δ Φ Γ (.prim p) o) →
    Option ((o' : Lvl) × (y : PExpr Δ Φ Γ (.prim p) o') ×'
      ∀ κ ρ, PExpr.eval x κ ρ = negDen p (y.eval κ ρ))
  | .uint8, _, .neu (.extern (.uint8BasicExtern .lean_uint8_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .uint16, _, .neu (.extern (.uint16BasicExtern .lean_uint16_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .uint32, _, .neu (.extern (.uint32BasicExtern .lean_uint32_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .uint64, _, .neu (.extern (.uint64BasicExtern .lean_uint64_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .int8, _, .neu (.extern (.int8BasicExtern .lean_int8_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .int16, _, .neu (.extern (.int16BasicExtern .lean_int16_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .int32, _, .neu (.extern (.int32BasicExtern .lean_int32_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .int64, _, .neu (.extern (.int64BasicExtern .lean_int64_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | .int, _, .neu (.extern (.intBasicExtern .lean_int_neg) (.cons y .nil) _) => some ⟨_, y, fun _ _ => rfl⟩
  | _, _, _ => none

/-- **A unit operand dropped** from a call on integers: `x - 0` and `x / 1` are `x`, and
    `-(-x)` is `x`. -/
def Neu.intUnit? {ℓ : Nat} : (p : LeanPrimTy) → (n : Neu Δ Φ Γ (.prim p) ℓ) → Option n.SameAs
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = UInt8.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint8_sub_zero _⟩
      else none
    | none => none
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = UInt8.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint8_div_one _⟩
      else none
    | none => none
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_neg) (.cons x .nil) _ =>
    match x.negOf? .uint8 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt8.neg (x.eval κ ρ); rw [hy]; exact IntUnit.uint8_neg_neg _⟩
    | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = UInt16.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint16_sub_zero _⟩
      else none
    | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = UInt16.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint16_div_one _⟩
      else none
    | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_neg) (.cons x .nil) _ =>
    match x.negOf? .uint16 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt16.neg (x.eval κ ρ); rw [hy]; exact IntUnit.uint16_neg_neg _⟩
    | none => none
  | .uint32, .extern (.uintBasicAuxExtern .lean_uint32_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = UInt32.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint32_sub_zero _⟩
      else none
    | none => none
  | .uint32, .extern (.uint32BasicExtern .lean_uint32_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = UInt32.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint32_div_one _⟩
      else none
    | none => none
  | .uint32, .extern (.uint32BasicExtern .lean_uint32_neg) (.cons x .nil) _ =>
    match x.negOf? .uint32 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt32.neg (x.eval κ ρ); rw [hy]; exact IntUnit.uint32_neg_neg _⟩
    | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = UInt64.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint64_sub_zero _⟩
      else none
    | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = UInt64.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.uint64_div_one _⟩
      else none
    | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_neg) (.cons x .nil) _ =>
    match x.negOf? .uint64 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt64.neg (x.eval κ ρ); rw [hy]; exact IntUnit.uint64_neg_neg _⟩
    | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Int8.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int8_sub_zero _⟩
      else none
    | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int8.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int8_div_one _⟩
      else none
    | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_neg) (.cons x .nil) _ =>
    match x.negOf? .int8 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = Int8.neg (x.eval κ ρ); rw [hy]; exact IntUnit.int8_neg_neg _⟩
    | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Int16.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int16_sub_zero _⟩
      else none
    | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int16.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int16_div_one _⟩
      else none
    | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_neg) (.cons x .nil) _ =>
    match x.negOf? .int16 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = Int16.neg (x.eval κ ρ); rw [hy]; exact IntUnit.int16_neg_neg _⟩
    | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Int32.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int32_sub_zero _⟩
      else none
    | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int32.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int32_div_one _⟩
      else none
    | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_neg) (.cons x .nil) _ =>
    match x.negOf? .int32 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = Int32.neg (x.eval κ ρ); rw [hy]; exact IntUnit.int32_neg_neg _⟩
    | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Int64.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int64_sub_zero _⟩
      else none
    | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int64.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int64_div_one _⟩
      else none
    | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_neg) (.cons x .nil) _ =>
    match x.negOf? .int64 with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = Int64.neg (x.eval κ ρ); rw [hy]; exact IntUnit.int64_neg_neg _⟩
    | none => none
  | .int, .extern (.intBasicExtern .lean_int_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Int.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int_sub_zero _⟩
      else none
    | none => none
  | .int, .extern (.intDivModExtern .lean_int_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int.tdiv _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int_div_one _⟩
      else none
    | none => none
  | .int, .extern (.intDivModExtern .lean_int_ediv) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Int.ediv _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.int_ediv_one _⟩
      else none
    | none => none
  | .int, .extern (.intBasicExtern .lean_int_neg) (.cons x .nil) _ =>
    match x.negOf? .int with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = Int.neg (x.eval κ ρ); rw [hy]; exact IntUnit.int_neg_neg _⟩
    | none => none
  | .nat, .extern (.preludeExtern .lean_nat_sub) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 0 then some ⟨_, x, fun κ ρ => by
        show _ = Nat.sub _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.nat_sub_zero _⟩
      else none
    | none => none
  | .nat, .extern (.preludeExtern .lean_nat_div) (.cons x (.cons y .nil)) _ =>
    match y.primLit? with
    | some ⟨v, _, hy⟩ =>
      if hv : v = 1 then some ⟨_, x, fun κ ρ => by
        show _ = Nat.div _ (y.eval κ ρ); rw [hy, hv]; exact IntUnit.nat_div_one _⟩
      else none
    | none => none
  | _, _ => none

/-- **A negation written as one**: `x * -1` and `0 - x` are `-x`; and **a subtraction of a
    literal written as an addition**: `x - k` is `x + (-k)` (which the sums of `Term.arithWalk`
    fold with the literals around it). -/
def Neu.intNeg? {ℓ : Nat} : (p : LeanPrimTy) → (n : Neu Δ Φ Γ (.prim p) ℓ) →
    Option {m : Neu Δ Φ Γ (.prim p) ℓ // ∀ κ ρ, m.eval κ ρ = n.eval κ ρ}
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.uint8BasicExtern .lean_uint8_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt8.neg (x.eval κ ρ) = UInt8.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint8_mul_neg_one _⟩
      else none
    | none => none
  | .uint8, .extern (.uint8BasicExtern .lean_uint8_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.uint8BasicExtern .lean_uint8_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt8.neg (x.eval κ ρ) = UInt8.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint8_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.uint8BasicExtern .lean_uint8_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt8.add (y.eval κ ρ) (-v) = UInt8.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.uint8_sub_lit _ _⟩
      | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.uint16BasicExtern .lean_uint16_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt16.neg (x.eval κ ρ) = UInt16.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint16_mul_neg_one _⟩
      else none
    | none => none
  | .uint16, .extern (.uint16BasicExtern .lean_uint16_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.uint16BasicExtern .lean_uint16_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt16.neg (x.eval κ ρ) = UInt16.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint16_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.uint16BasicExtern .lean_uint16_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt16.add (y.eval κ ρ) (-v) = UInt16.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.uint16_sub_lit _ _⟩
      | none => none
  | .uint32, .extern (.uint32BasicExtern .lean_uint32_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.uint32BasicExtern .lean_uint32_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt32.neg (x.eval κ ρ) = UInt32.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint32_mul_neg_one _⟩
      else none
    | none => none
  | .uint32, .extern (.uintBasicAuxExtern .lean_uint32_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.uint32BasicExtern .lean_uint32_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt32.neg (x.eval κ ρ) = UInt32.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint32_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.uintBasicAuxExtern .lean_uint32_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt32.add (y.eval κ ρ) (-v) = UInt32.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.uint32_sub_lit _ _⟩
      | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.uint64BasicExtern .lean_uint64_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt64.neg (x.eval κ ρ) = UInt64.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint64_mul_neg_one _⟩
      else none
    | none => none
  | .uint64, .extern (.uint64BasicExtern .lean_uint64_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.uint64BasicExtern .lean_uint64_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show UInt64.neg (x.eval κ ρ) = UInt64.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.uint64_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.uint64BasicExtern .lean_uint64_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show UInt64.add (y.eval κ ρ) (-v) = UInt64.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.uint64_sub_lit _ _⟩
      | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.int8BasicExtern .lean_int8_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int8.neg (x.eval κ ρ) = Int8.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int8_mul_neg_one _⟩
      else none
    | none => none
  | .int8, .extern (.int8BasicExtern .lean_int8_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.int8BasicExtern .lean_int8_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int8.neg (x.eval κ ρ) = Int8.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int8_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.int8BasicExtern .lean_int8_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int8.add (y.eval κ ρ) (-v) = Int8.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.int8_sub_lit _ _⟩
      | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.int16BasicExtern .lean_int16_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int16.neg (x.eval κ ρ) = Int16.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int16_mul_neg_one _⟩
      else none
    | none => none
  | .int16, .extern (.int16BasicExtern .lean_int16_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.int16BasicExtern .lean_int16_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int16.neg (x.eval κ ρ) = Int16.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int16_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.int16BasicExtern .lean_int16_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int16.add (y.eval κ ρ) (-v) = Int16.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.int16_sub_lit _ _⟩
      | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.int32BasicExtern .lean_int32_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int32.neg (x.eval κ ρ) = Int32.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int32_mul_neg_one _⟩
      else none
    | none => none
  | .int32, .extern (.int32BasicExtern .lean_int32_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.int32BasicExtern .lean_int32_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int32.neg (x.eval κ ρ) = Int32.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int32_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.int32BasicExtern .lean_int32_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int32.add (y.eval κ ρ) (-v) = Int32.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.int32_sub_lit _ _⟩
      | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.int64BasicExtern .lean_int64_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int64.neg (x.eval κ ρ) = Int64.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int64_mul_neg_one _⟩
      else none
    | none => none
  | .int64, .extern (.int64BasicExtern .lean_int64_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.int64BasicExtern .lean_int64_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int64.neg (x.eval κ ρ) = Int64.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int64_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.int64BasicExtern .lean_int64_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int64.add (y.eval κ ρ) (-v) = Int64.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.int64_sub_lit _ _⟩
      | none => none
  | .int, .extern (.intBasicExtern .lean_int_mul) (.cons x (.cons y .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = -1 then
        some ⟨.extern (.intBasicExtern .lean_int_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int.neg (x.eval κ ρ) = Int.mul (x.eval κ ρ) (y.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int_mul_neg_one _⟩
      else none
    | none => none
  | .int, .extern (.intBasicExtern .lean_int_sub) (.cons y (.cons x .nil)) h =>
    match y.primLit? with
    | some ⟨v, ho, hy⟩ =>
      if hv : v = 0 then
        some ⟨.extern (.intBasicExtern .lean_int_neg) (.cons x .nil) (by subst ho; exact h), fun κ ρ => by
          show Int.neg (x.eval κ ρ) = Int.sub (y.eval κ ρ) (x.eval κ ρ)
          rw [hy, hv]; exact IntUnit.int_zero_sub _⟩
      else none
    | none =>
      match x.primLit? with
      | some ⟨v, ho, hx⟩ =>
        some ⟨.extern (.intBasicExtern .lean_int_add) (.cons y (.cons (.lit _ (-v)) .nil)) (by subst ho; exact h),
          fun κ ρ => by
            show Int.add (y.eval κ ρ) (-v) = Int.sub (y.eval κ ρ) (x.eval κ ρ)
            rw [hx]; exact IntUnit.int_sub_lit _ _⟩
      | none => none
  | _, _ => none

/-- **A unit operand of an integer operation dropped, or a negation written as one**
    (`x - 0` is `x`, `x * -1` is `-x`, …), when the result is a neutral expression of the same
    level (otherwise the expression is kept). -/
def Neu.intUnit (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ) :
    Neu Δ Φ Γ (.prim p) ℓ :=
  match Neu.intUnit? p n with
  | some r =>
    if h : r.o = some ℓ then
      match PExpr.asNeu? (h ▸ r.e) with
      | some m => m.1
      | none => n
    else n
  | none =>
    match Neu.intNeg? p n with
    | some m => m.1
    | none => n

theorem Neu.intUnit_eval (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (Neu.intUnit p n).eval κ ρ = n.eval κ ρ := by
  unfold Neu.intUnit
  split
  · rename_i r _
    split
    · rename_i h
      split
      · rename_i m _
        rw [m.2, PExpr.eval_levelCast, r.eval]
      · rfl
    · rfl
  · split
    · rename_i m _
      exact m.2 κ ρ
    · rfl

end LeanScript

end
