module

public import HashableFloat.Identities

@[expose] public section

set_option autoImplicit false

/-!
# Commutativity of IEEE addition and multiplication

`x + y = y + x` and `x * y = y * x`, **exactly** (bit for bit), for every `Float` and `Float32`
(`NaN`, infinities and both zeros included), in Lean's logical model of floats
(`Float.Model`, `UnpackedFloat`).  Unlike associativity, these laws hold in IEEE arithmetic:
both operations round the exact result, which does not depend on the order of the operands.

The `Term` optimiser uses them to put the operand that needs parentheses in JavaScript on the
left of a float `+`/`*` (`LeanScript.Term.Optimize.FloatComm`).
-/

namespace LeanScript.FloatIdentities

open Float.Model UnpackedFloat

theorem sign_mul_comm (a b : Sign) : a * b = b * a := by cases a <;> cases b <;> rfl

/-- Addition of unpacked floats is commutative. -/
theorem add_comm (spec : Format) (x y : UnpackedFloat) :
    UnpackedFloat.add spec x y = UnpackedFloat.add spec y x := by
  cases x <;> cases y <;> simp only [UnpackedFloat.add]
  all_goals first
    | rfl
    | (rename_i s₁ s₂; cases s₁ <;> cases s₂ <;> rfl)
    | simp only [Int.min_comm, Int.add_comm]

/-- Multiplication of unpacked floats is commutative. -/
theorem mul_comm (spec : Format) (x y : UnpackedFloat) :
    UnpackedFloat.mul spec x y = UnpackedFloat.mul spec y x := by
  cases x <;> cases y <;> simp only [UnpackedFloat.mul, sign_mul_comm, Nat.mul_comm, Int.add_comm]

theorem Float.add_comm (a b : Float) : Float.add a b = Float.add b a := by
  cases a with | ofModel m =>
  cases b with | ofModel n =>
  show _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.add _ m.unpack n.unpack)) =
    _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.add _ n.unpack m.unpack))
  rw [FloatIdentities.add_comm]

theorem Float.mul_comm (a b : Float) : Float.mul a b = Float.mul b a := by
  cases a with | ofModel m =>
  cases b with | ofModel n =>
  show _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.mul _ m.unpack n.unpack)) =
    _root_.Float.ofModel (Float.Model.pack (UnpackedFloat.mul _ n.unpack m.unpack))
  rw [FloatIdentities.mul_comm]

theorem Float32.add_comm (a b : Float32) : Float32.add a b = Float32.add b a := by
  cases a with | ofModel m =>
  cases b with | ofModel n =>
  show _root_.Float32.ofModel (Float32.Model.pack (UnpackedFloat.add _ m.unpack n.unpack)) =
    _root_.Float32.ofModel (Float32.Model.pack (UnpackedFloat.add _ n.unpack m.unpack))
  rw [FloatIdentities.add_comm]

theorem Float32.mul_comm (a b : Float32) : Float32.mul a b = Float32.mul b a := by
  cases a with | ofModel m =>
  cases b with | ofModel n =>
  show _root_.Float32.ofModel (Float32.Model.pack (UnpackedFloat.mul _ m.unpack n.unpack)) =
    _root_.Float32.ofModel (Float32.Model.pack (UnpackedFloat.mul _ n.unpack m.unpack))
  rw [FloatIdentities.mul_comm]

end LeanScript.FloatIdentities
