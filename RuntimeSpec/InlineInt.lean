module

public import RuntimeSpec.Model

@[expose] public section

set_option autoImplicit false

/-!
# The arithmetic of `Int64`, the negation of `Int` and the subtraction of `Nat` written inline

The backend writes the arithmetic of `Int64` at the `BigInt` representation inline
(`scripts/js_ops_inline.json`), instead of calling its functions in `runtime.js`; each form is
the body of the runtime's function, each operand read once, from left to right:

| operation | `Int64` (`BigInt`) |
|---|---|
| `add` | `BigInt.asIntN(64, a + b)` |
| `sub` | `BigInt.asIntN(64, a - b)` |
| `mul` | `BigInt.asIntN(64, a * b)` |
| `neg` | `BigInt.asIntN(64, -a)` |
| `complement` | `BigInt.asIntN(64, ~a)` |
| `land`, `lor`, `xor` | `BigInt.asIntN(64, a & b)`, … |

and the negation of `Int` and of `Int64` at the `number` representation as `0 - a` (the
runtime's body: `0 - a` rather than `-a`, which would answer `-0` for `0`), and the
subtraction of `Nat` at the `number` representation as `Math.max(0, a - b)` (the runtime's
`a > b ? a - b : 0` reads both operands twice; the difference of two safe naturals is exact).

These theorems prove each arithmetic form equal to the Lean operation in the model of
`RuntimeSpec.Model` (a `BigInt` `Int64` is its `toInt`, a `number` `Int`/`Int64` is the integer
itself, of which a safe one never is `Int64.minValue`).
-/

namespace RuntimeSpec

/-- `BigInt.asIntN(64, a + b)` is `Int64.add`. -/
theorem int64_add_inline (a b : Int64) : asIntN 64 (a.toInt + b.toInt) = (a + b).toInt := by
  rw [asIntN, Int64.toInt_add]

/-- `BigInt.asIntN(64, a - b)` is `Int64.sub`. -/
theorem int64_sub_inline (a b : Int64) : asIntN 64 (a.toInt - b.toInt) = (a - b).toInt := by
  rw [asIntN, Int64.toInt_sub]

/-- `BigInt.asIntN(64, a * b)` is `Int64.mul`. -/
theorem int64_mul_inline (a b : Int64) : asIntN 64 (a.toInt * b.toInt) = (a * b).toInt := by
  rw [asIntN, Int64.toInt_mul]

/-- `BigInt.asIntN(64, -a)` is `Int64.neg`. -/
theorem int64_neg_inline (a : Int64) : asIntN 64 (-a.toInt) = (-a).toInt := by
  rw [asIntN, Int64.toInt_neg]

/-- `BigInt.asIntN(64, ~a)` (`~a` is `-a - 1` on a `BigInt`) is `Int64.complement`. -/
theorem int64_complement_inline (a : Int64) : asIntN 64 (-a.toInt - 1) = (~~~a).toInt := by
  rw [asIntN, Int64.toInt_not]

/-- `0 - a` is `Int.neg` on a `number`. -/
theorem int_neg_inline (a : Int) : 0 - a = -a := Int.zero_sub a

/-- `0 - a` is `Int64.neg` on a `number`: a safe integer is not `Int64.minValue`, whose
negation is the only one that wraps around. -/
theorem int64_neg_inline_num (a : Int64) (ha : IsSafe a.toInt) : 0 - a.toInt = (-a).toInt := by
  rw [Int.zero_sub, Int64.toInt_neg, Int.bmod_eq_of_le_mul_two] <;>
  · simp only [IsSafe, maxSafe] at ha
    omega

/-- `Math.max(0, a - b)` is `Nat.sub` on `number`s (`a - b` is exact on two safe naturals). -/
theorem nat_sub_inline (a b : Nat) : max 0 ((a : Int) - b) = ((a - b : Nat) : Int) := by
  omega

end RuntimeSpec
