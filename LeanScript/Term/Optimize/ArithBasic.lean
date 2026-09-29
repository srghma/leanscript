module

public import LeanScript.Term.Optimize.Append
public import LeanScript.Term.Optimize.Atom

@[expose] public section

set_option autoImplicit false

/-!
# Chains of additions and multiplications: the operations

The operations whose chains `Term.arithWalk` normalises (`ArithOp`: the additions and the
multiplications of `Int`, `Nat`, `UInt8`–`UInt64` and `Int8`–`Int64`), their laws, their externs,
the operands of a chain (`ArithOp.flat`), its literals and its unknowns.  The rest of the pass is
in `LeanScript.Term.Optimize.ArithPow` (powers in products) and
`LeanScript.Term.Optimize.Arith`.
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks}

/-- The associative and commutative operations whose chains are normalised. -/
inductive ArithOp where
  | intAdd | intMul
  | natAdd | natMul
  | uint8Add | uint8Mul
  | uint16Add | uint16Mul
  | uint32Add | uint32Mul
  | uint64Add | uint64Mul
  | int8Add | int8Mul
  | int16Add | int16Mul
  | int32Add | int32Mul
  | int64Add | int64Mul
  deriving DecidableEq, Repr

namespace ArithOp

/-- The type of the operands. -/
def prim : ArithOp → LeanPrimTy
  | .intAdd | .intMul => .int
  | .natAdd | .natMul => .nat
  | .uint8Add | .uint8Mul => .uint8
  | .uint16Add | .uint16Mul => .uint16
  | .uint32Add | .uint32Mul => .uint32
  | .uint64Add | .uint64Mul => .uint64
  | .int8Add | .int8Mul => .int8
  | .int16Add | .int16Mul => .int16
  | .int32Add | .int32Mul => .int32
  | .int64Add | .int64Mul => .int64

/-- The values of the operands. -/
abbrev D (a : ArithOp) : Type := a.prim.denote

/-- The operation, as the evaluator of its extern computes it. -/
def op : (a : ArithOp) → a.D → a.D → a.D
  | .intAdd => fun x y => Int.add x y
  | .intMul => fun x y => Int.mul x y
  | .natAdd => fun x y => Nat.add x y
  | .natMul => fun x y => Nat.mul x y
  | .uint8Add => fun x y => UInt8.add x y
  | .uint8Mul => fun x y => UInt8.mul x y
  | .uint16Add => fun x y => UInt16.add x y
  | .uint16Mul => fun x y => UInt16.mul x y
  | .uint32Add => fun x y => UInt32.add x y
  | .uint32Mul => fun x y => UInt32.mul x y
  | .uint64Add => fun x y => UInt64.add x y
  | .uint64Mul => fun x y => UInt64.mul x y
  | .int8Add => fun x y => Int8.add x y
  | .int8Mul => fun x y => Int8.mul x y
  | .int16Add => fun x y => Int16.add x y
  | .int16Mul => fun x y => Int16.mul x y
  | .int32Add => fun x y => Int32.add x y
  | .int32Mul => fun x y => Int32.mul x y
  | .int64Add => fun x y => Int64.add x y
  | .int64Mul => fun x y => Int64.mul x y

/-- The unit of the operation. -/
def unit : (a : ArithOp) → a.D
  | .intAdd => (0 : Int) | .intMul => (1 : Int)
  | .natAdd => (0 : Nat) | .natMul => (1 : Nat)
  | .uint8Add => (0 : UInt8) | .uint8Mul => (1 : UInt8)
  | .uint16Add => (0 : UInt16) | .uint16Mul => (1 : UInt16)
  | .uint32Add => (0 : UInt32) | .uint32Mul => (1 : UInt32)
  | .uint64Add => (0 : UInt64) | .uint64Mul => (1 : UInt64)
  | .int8Add => (0 : Int8) | .int8Mul => (1 : Int8)
  | .int16Add => (0 : Int16) | .int16Mul => (1 : Int16)
  | .int32Add => (0 : Int32) | .int32Mul => (1 : Int32)
  | .int64Add => (0 : Int64) | .int64Mul => (1 : Int64)

theorem op_comm : (a : ArithOp) → (x y : a.D) → a.op x y = a.op y x
  | .intAdd, x, y => Int.add_comm x y | .intMul, x, y => Int.mul_comm x y
  | .natAdd, x, y => Nat.add_comm x y | .natMul, x, y => Nat.mul_comm x y
  | .uint8Add, x, y => UInt8.add_comm x y | .uint8Mul, x, y => UInt8.mul_comm x y
  | .uint16Add, x, y => UInt16.add_comm x y | .uint16Mul, x, y => UInt16.mul_comm x y
  | .uint32Add, x, y => UInt32.add_comm x y | .uint32Mul, x, y => UInt32.mul_comm x y
  | .uint64Add, x, y => UInt64.add_comm x y | .uint64Mul, x, y => UInt64.mul_comm x y
  | .int8Add, x, y => Int8.add_comm x y | .int8Mul, x, y => Int8.mul_comm x y
  | .int16Add, x, y => Int16.add_comm x y | .int16Mul, x, y => Int16.mul_comm x y
  | .int32Add, x, y => Int32.add_comm x y | .int32Mul, x, y => Int32.mul_comm x y
  | .int64Add, x, y => Int64.add_comm x y | .int64Mul, x, y => Int64.mul_comm x y

theorem op_assoc : (a : ArithOp) → (x y z : a.D) → a.op (a.op x y) z = a.op x (a.op y z)
  | .intAdd, x, y, z => Int.add_assoc x y z | .intMul, x, y, z => Int.mul_assoc x y z
  | .natAdd, x, y, z => Nat.add_assoc x y z | .natMul, x, y, z => Nat.mul_assoc x y z
  | .uint8Add, x, y, z => UInt8.add_assoc x y z | .uint8Mul, x, y, z => UInt8.mul_assoc x y z
  | .uint16Add, x, y, z => UInt16.add_assoc x y z
  | .uint16Mul, x, y, z => UInt16.mul_assoc x y z
  | .uint32Add, x, y, z => UInt32.add_assoc x y z
  | .uint32Mul, x, y, z => UInt32.mul_assoc x y z
  | .uint64Add, x, y, z => UInt64.add_assoc x y z
  | .uint64Mul, x, y, z => UInt64.mul_assoc x y z
  | .int8Add, x, y, z => Int8.add_assoc x y z | .int8Mul, x, y, z => Int8.mul_assoc x y z
  | .int16Add, x, y, z => Int16.add_assoc x y z | .int16Mul, x, y, z => Int16.mul_assoc x y z
  | .int32Add, x, y, z => Int32.add_assoc x y z | .int32Mul, x, y, z => Int32.mul_assoc x y z
  | .int64Add, x, y, z => Int64.add_assoc x y z | .int64Mul, x, y, z => Int64.mul_assoc x y z

theorem unit_op : (a : ArithOp) → (x : a.D) → a.op a.unit x = x
  | .intAdd, x => Int.zero_add x | .intMul, x => Int.one_mul x
  | .natAdd, x => Nat.zero_add x | .natMul, x => Nat.one_mul x
  | .uint8Add, x => UInt8.zero_add x | .uint8Mul, x => UInt8.one_mul x
  | .uint16Add, x => UInt16.zero_add x | .uint16Mul, x => UInt16.one_mul x
  | .uint32Add, x => UInt32.zero_add x | .uint32Mul, x => UInt32.one_mul x
  | .uint64Add, x => UInt64.zero_add x | .uint64Mul, x => UInt64.one_mul x
  | .int8Add, x => Int8.zero_add x | .int8Mul, x => Int8.one_mul x
  | .int16Add, x => Int16.zero_add x | .int16Mul, x => Int16.one_mul x
  | .int32Add, x => Int32.zero_add x | .int32Mul, x => Int32.one_mul x
  | .int64Add, x => Int64.zero_add x | .int64Mul, x => Int64.one_mul x

theorem op_unit (a : ArithOp) (x : a.D) : a.op x a.unit = x := by
  rw [op_comm, unit_op]

/-- `x ∘ (y ∘ z) = y ∘ (x ∘ z)`. -/
theorem op_left_comm (a : ArithOp) (x y z : a.D) : a.op x (a.op y z) = a.op y (a.op x z) := by
  rw [← op_assoc, op_comm a x y, op_assoc]

/-- Equality of the values is decidable. -/
def decEq : (a : ArithOp) → DecidableEq a.D
  | .intAdd | .intMul => inferInstanceAs (DecidableEq Int)
  | .natAdd | .natMul => inferInstanceAs (DecidableEq Nat)
  | .uint8Add | .uint8Mul => inferInstanceAs (DecidableEq UInt8)
  | .uint16Add | .uint16Mul => inferInstanceAs (DecidableEq UInt16)
  | .uint32Add | .uint32Mul => inferInstanceAs (DecidableEq UInt32)
  | .uint64Add | .uint64Mul => inferInstanceAs (DecidableEq UInt64)
  | .int8Add | .int8Mul => inferInstanceAs (DecidableEq Int8)
  | .int16Add | .int16Mul => inferInstanceAs (DecidableEq Int16)
  | .int32Add | .int32Mul => inferInstanceAs (DecidableEq Int32)
  | .int64Add | .int64Mul => inferInstanceAs (DecidableEq Int64)

/-- Whether a value is the unit. -/
def isUnit (a : ArithOp) (x : a.D) : Bool := @decide (x = a.unit) (a.decEq x a.unit)

theorem eq_unit_of_isUnit (a : ArithOp) (x : a.D) (h : a.isUnit x = true) : x = a.unit :=
  @of_decide_eq_true _ (a.decEq x a.unit) h

/-! ### The multiplication that counts the copies of an operand of a sum -/

/-- Whether the operation is an addition (repeated operands are then counted, `x * k`). -/
def isAdd : ArithOp → Bool
  | .intAdd | .natAdd | .uint8Add | .uint16Add | .uint32Add | .uint64Add
  | .int8Add | .int16Add | .int32Add | .int64Add => true
  | _ => false

/-- The multiplication of the type of an addition (the operation itself otherwise). -/
def mul : (a : ArithOp) → a.D → a.D → a.D
  | .intAdd => fun x y => Int.mul x y
  | .natAdd => fun x y => Nat.mul x y
  | .uint8Add => fun x y => UInt8.mul x y
  | .uint16Add => fun x y => UInt16.mul x y
  | .uint32Add => fun x y => UInt32.mul x y
  | .uint64Add => fun x y => UInt64.mul x y
  | .int8Add => fun x y => Int8.mul x y
  | .int16Add => fun x y => Int16.mul x y
  | .int32Add => fun x y => Int32.mul x y
  | .int64Add => fun x y => Int64.mul x y
  | a => a.op

/-- The one of the multiplication of the type of an addition. -/
def one : (a : ArithOp) → a.D
  | .intAdd => (1 : Int)
  | .natAdd => (1 : Nat)
  | .uint8Add => (1 : UInt8)
  | .uint16Add => (1 : UInt16)
  | .uint32Add => (1 : UInt32)
  | .uint64Add => (1 : UInt64)
  | .int8Add => (1 : Int8)
  | .int16Add => (1 : Int16)
  | .int32Add => (1 : Int32)
  | .int64Add => (1 : Int64)
  | a => a.unit

theorem mul_one : (a : ArithOp) → a.isAdd = true → (x : a.D) → a.mul x a.one = x
  | .intAdd, _, x => Int.mul_one x
  | .natAdd, _, x => Nat.mul_one x
  | .uint8Add, _, x => UInt8.mul_one x
  | .uint16Add, _, x => UInt16.mul_one x
  | .uint32Add, _, x => UInt32.mul_one x
  | .uint64Add, _, x => UInt64.mul_one x
  | .int8Add, _, x => Int8.mul_one x
  | .int16Add, _, x => Int16.mul_one x
  | .int32Add, _, x => Int32.mul_one x
  | .int64Add, _, x => Int64.mul_one x

theorem mul_op : (a : ArithOp) → a.isAdd = true → (x y z : a.D) →
    a.mul x (a.op y z) = a.op (a.mul x y) (a.mul x z)
  | .intAdd, _, x, y, z => Int.mul_add x y z
  | .natAdd, _, x, y, z => Nat.left_distrib x y z
  | .uint8Add, _, _, _, _ => UInt8.mul_add
  | .uint16Add, _, _, _, _ => UInt16.mul_add
  | .uint32Add, _, _, _, _ => UInt32.mul_add
  | .uint64Add, _, _, _, _ => UInt64.mul_add
  | .int8Add, _, _, _, _ => Int8.mul_add
  | .int16Add, _, _, _, _ => Int16.mul_add
  | .int32Add, _, _, _, _ => Int32.mul_add
  | .int64Add, _, _, _, _ => Int64.mul_add

/-! ### The externs -/

/-- The extern of the operation. -/
def ext : (a : ArithOp) → Extern ks [.prim a.prim, .prim a.prim] (.prim a.prim)
  | .intAdd => .intBasicExtern .lean_int_add
  | .intMul => .intBasicExtern .lean_int_mul
  | .natAdd => .preludeExtern .lean_nat_add
  | .natMul => .preludeExtern .lean_nat_mul
  | .uint8Add => .uint8BasicExtern .lean_uint8_add
  | .uint8Mul => .uint8BasicExtern .lean_uint8_mul
  | .uint16Add => .uint16BasicExtern .lean_uint16_add
  | .uint16Mul => .uint16BasicExtern .lean_uint16_mul
  | .uint32Add => .uintBasicAuxExtern .lean_uint32_add
  | .uint32Mul => .uint32BasicExtern .lean_uint32_mul
  | .uint64Add => .uint64BasicExtern .lean_uint64_add
  | .uint64Mul => .uint64BasicExtern .lean_uint64_mul
  | .int8Add => .int8BasicExtern .lean_int8_add
  | .int8Mul => .int8BasicExtern .lean_int8_mul
  | .int16Add => .int16BasicExtern .lean_int16_add
  | .int16Mul => .int16BasicExtern .lean_int16_mul
  | .int32Add => .int32BasicExtern .lean_int32_add
  | .int32Mul => .int32BasicExtern .lean_int32_mul
  | .int64Add => .int64BasicExtern .lean_int64_add
  | .int64Mul => .int64BasicExtern .lean_int64_mul

/-- The extern of the multiplication of the type of an addition. -/
def mulExt : (a : ArithOp) → Extern ks [.prim a.prim, .prim a.prim] (.prim a.prim)
  | .intAdd => .intBasicExtern .lean_int_mul
  | .natAdd => .preludeExtern .lean_nat_mul
  | .uint8Add => .uint8BasicExtern .lean_uint8_mul
  | .uint16Add => .uint16BasicExtern .lean_uint16_mul
  | .uint32Add => .uint32BasicExtern .lean_uint32_mul
  | .uint64Add => .uint64BasicExtern .lean_uint64_mul
  | .int8Add => .int8BasicExtern .lean_int8_mul
  | .int16Add => .int16BasicExtern .lean_int16_mul
  | .int32Add => .int32BasicExtern .lean_int32_mul
  | .int64Add => .int64BasicExtern .lean_int64_mul
  | a => a.ext

variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- A call of a binary extern on two operands of which one at least is open. -/
def call {σ : Ty ks} {o₁ o₂ : Lvl} {ℓ : Nat} (e : Extern ks [σ, σ] σ)
    (x : PExpr Δ Φ Γ σ o₁) (y : PExpr Δ Φ Γ σ o₂) (h : Lvl.meet o₁ o₂ = some ℓ) :
    PExpr Δ Φ Γ σ (some ℓ) :=
  .neu (.extern e (.cons x (.cons y .nil)) (by rw [Lvl.meet_none]; exact h))

theorem call_ext_eval : (a : ArithOp) → {o₁ o₂ : Lvl} → {ℓ : Nat} →
    (x : PExpr Δ Φ Γ (.prim a.prim) o₁) → (y : PExpr Δ Φ Γ (.prim a.prim) o₂) →
    (h : Lvl.meet o₁ o₂ = some ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (call a.ext x y h).eval κ ρ = a.op (x.eval κ ρ) (y.eval κ ρ)
  | .intAdd, _, _, _, _, _, _, _, _ => rfl | .intMul, _, _, _, _, _, _, _, _ => rfl
  | .natAdd, _, _, _, _, _, _, _, _ => rfl | .natMul, _, _, _, _, _, _, _, _ => rfl
  | .uint8Add, _, _, _, _, _, _, _, _ => rfl | .uint8Mul, _, _, _, _, _, _, _, _ => rfl
  | .uint16Add, _, _, _, _, _, _, _, _ => rfl | .uint16Mul, _, _, _, _, _, _, _, _ => rfl
  | .uint32Add, _, _, _, _, _, _, _, _ => rfl | .uint32Mul, _, _, _, _, _, _, _, _ => rfl
  | .uint64Add, _, _, _, _, _, _, _, _ => rfl | .uint64Mul, _, _, _, _, _, _, _, _ => rfl
  | .int8Add, _, _, _, _, _, _, _, _ => rfl | .int8Mul, _, _, _, _, _, _, _, _ => rfl
  | .int16Add, _, _, _, _, _, _, _, _ => rfl | .int16Mul, _, _, _, _, _, _, _, _ => rfl
  | .int32Add, _, _, _, _, _, _, _, _ => rfl | .int32Mul, _, _, _, _, _, _, _, _ => rfl
  | .int64Add, _, _, _, _, _, _, _, _ => rfl | .int64Mul, _, _, _, _, _, _, _, _ => rfl

theorem call_mulExt_eval : (a : ArithOp) → a.isAdd = true → {o₁ o₂ : Lvl} → {ℓ : Nat} →
    (x : PExpr Δ Φ Γ (.prim a.prim) o₁) → (y : PExpr Δ Φ Γ (.prim a.prim) o₂) →
    (h : Lvl.meet o₁ o₂ = some ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (call a.mulExt x y h).eval κ ρ = a.mul (x.eval κ ρ) (y.eval κ ρ)
  | .intAdd, _, _, _, _, _, _, _, _, _ => rfl
  | .natAdd, _, _, _, _, _, _, _, _, _ => rfl
  | .uint8Add, _, _, _, _, _, _, _, _, _ => rfl
  | .uint16Add, _, _, _, _, _, _, _, _, _ => rfl
  | .uint32Add, _, _, _, _, _, _, _, _, _ => rfl
  | .uint64Add, _, _, _, _, _, _, _, _, _ => rfl
  | .int8Add, _, _, _, _, _, _, _, _, _ => rfl
  | .int16Add, _, _, _, _, _, _, _, _, _ => rfl
  | .int32Add, _, _, _, _, _, _, _, _, _ => rfl
  | .int64Add, _, _, _, _, _, _, _, _, _ => rfl

/-- The two operands of a call of the operation, with the fact that the call combines them. -/
structure Split (a : ArithOp) {o : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o) where
  o₁ : Lvl
  o₂ : Lvl
  x : PExpr Δ Φ Γ (.prim a.prim) o₁
  y : PExpr Δ Φ Γ (.prim a.prim) o₂
  eval : ∀ κ ρ, e.eval κ ρ = a.op (x.eval κ ρ) (y.eval κ ρ)

/-- The operands, when a pure expression is a call of the operation. -/
def view : (a : ArithOp) → {o : Lvl} → (e : PExpr Δ Φ Γ (.prim a.prim) o) → Option (a.Split e)
  | .intAdd, _, .neu (.extern (.intBasicExtern .lean_int_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .intMul, _, .neu (.extern (.intBasicExtern .lean_int_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .natAdd, _, .neu (.extern (.preludeExtern .lean_nat_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .natMul, _, .neu (.extern (.preludeExtern .lean_nat_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint8Add, _, .neu (.extern (.uint8BasicExtern .lean_uint8_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint8Mul, _, .neu (.extern (.uint8BasicExtern .lean_uint8_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint16Add, _, .neu (.extern (.uint16BasicExtern .lean_uint16_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint16Mul, _, .neu (.extern (.uint16BasicExtern .lean_uint16_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint32Add, _, .neu (.extern (.uintBasicAuxExtern .lean_uint32_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint32Mul, _, .neu (.extern (.uint32BasicExtern .lean_uint32_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint64Add, _, .neu (.extern (.uint64BasicExtern .lean_uint64_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .uint64Mul, _, .neu (.extern (.uint64BasicExtern .lean_uint64_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int8Add, _, .neu (.extern (.int8BasicExtern .lean_int8_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int8Mul, _, .neu (.extern (.int8BasicExtern .lean_int8_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int16Add, _, .neu (.extern (.int16BasicExtern .lean_int16_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int16Mul, _, .neu (.extern (.int16BasicExtern .lean_int16_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int32Add, _, .neu (.extern (.int32BasicExtern .lean_int32_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int32Mul, _, .neu (.extern (.int32BasicExtern .lean_int32_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int64Add, _, .neu (.extern (.int64BasicExtern .lean_int64_add) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | .int64Mul, _, .neu (.extern (.int64BasicExtern .lean_int64_mul) (.cons x (.cons y .nil)) _) =>
      some ⟨_, _, x, y, fun _ _ => rfl⟩
  | _, _, _ => none

/-! ### Operands -/

/-- An operand of a chain: a pure expression of the type, at any level. -/
abbrev Opnd (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) (a : ArithOp) : Type :=
  Σ o : Lvl, PExpr Δ Φ Γ (.prim a.prim) o

/-- The value of an operand. -/
def val (a : ArithOp) (p : Opnd Δ Φ Γ a) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.D := p.2.eval κ ρ

/-- The operands combined, `x₁ ∘ (x₂ ∘ (… ∘ unit))`. -/
def den (a : ArithOp) (ops : List (Opnd Δ Φ Γ a)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.D :=
  ops.foldr (fun p acc => a.op (a.val p κ ρ) acc) a.unit

@[simp] theorem den_nil (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    a.den ([] : List (Opnd Δ Φ Γ a)) κ ρ = a.unit := rfl

@[simp] theorem den_cons (a : ArithOp) (p : Opnd Δ Φ Γ a) (ops : List (Opnd Δ Φ Γ a))
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.den (p :: ops) κ ρ = a.op (a.val p κ ρ) (a.den ops κ ρ) :=
  rfl

theorem den_append (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (xs ys : List (Opnd Δ Φ Γ a)) → a.den (xs ++ ys) κ ρ = a.op (a.den xs κ ρ) (a.den ys κ ρ)
  | [], ys => by simp [unit_op]
  | x :: xs, ys => by simp [den_append a κ ρ xs ys, op_assoc]

/-- Splitting the operands by a test and combining each part changes nothing. -/
theorem den_filter (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (f : Opnd Δ Φ Γ a → Bool) :
    (ops : List (Opnd Δ Φ Γ a)) →
    a.den ops κ ρ = a.op (a.den (ops.filter f) κ ρ) (a.den (ops.filter (fun p => !f p)) κ ρ)
  | [] => by simp [unit_op]
  | x :: xs => by
    rw [den_cons, den_filter a κ ρ f xs]
    cases h : f x
    · simp [h, op_left_comm]
    · simp [h, op_assoc]

/-- The operands of a chain, however it is grouped (at most `n` levels deep). -/
def flat (a : ArithOp) : Nat → {o : Lvl} → PExpr Δ Φ Γ (.prim a.prim) o → List (Opnd Δ Φ Γ a)
  | 0, _, e => [⟨_, e⟩]
  | n + 1, _, e =>
    match a.view e with
    | some s => flat a n s.x ++ flat a n s.y
    | none => [⟨_, e⟩]

theorem flat_den (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (n : Nat) → {o : Lvl} → (e : PExpr Δ Φ Γ (.prim a.prim) o) →
    a.den (flat a n e) κ ρ = e.eval κ ρ
  | 0, _, e => by simp only [flat, den_cons, den_nil, val]; exact a.op_unit _
  | n + 1, _, e => by
    unfold flat
    split
    · rename_i s _
      rw [den_append, flat_den a κ ρ n, flat_den a κ ρ n, s.eval]
    · simp only [den_cons, den_nil, val]; exact a.op_unit _

/-! ### Literals -/

/-- The value of an operand that is a literal. -/
def litVal? (a : ArithOp) : {o : Lvl} → PExpr Δ Φ Γ (.prim a.prim) o → Option a.D
  | _, .lit _ v => some v
  | _, _ => none

theorem litVal?_eval (a : ArithOp) {o : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o) (v : a.D)
    (h : a.litVal? e = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : e.eval κ ρ = v := by
  unfold litVal? at h
  split at h
  · cases h; rfl
  · cases h

/-- Whether an operand is a literal. -/
def isLit (a : ArithOp) (p : Opnd Δ Φ Γ a) : Bool := (a.litVal? p.2).isSome

/-- The literals among the operands, folded. -/
def lits (a : ArithOp) (ops : List (Opnd Δ Φ Γ a)) : a.D :=
  ops.foldr (fun p acc => match a.litVal? p.2 with
    | some v => a.op v acc
    | none => acc) a.unit

theorem den_filter_isLit (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (ops : List (Opnd Δ Φ Γ a)) → a.den (ops.filter a.isLit) κ ρ = a.lits ops
  | [] => rfl
  | x :: xs => by
    have ih := den_filter_isLit a κ ρ xs
    unfold isLit
    cases h : a.litVal? x.2 with
    | none => simp [h, lits]; exact ih
    | some v =>
      simp only [List.filter_cons, h, Option.isSome_some, ite_true, den_cons]
      rw [show List.filter (fun p => (a.litVal? p.snd).isSome) xs = xs.filter a.isLit from rfl,
        ih, val, a.litVal?_eval x.2 v h κ ρ]
      simp [lits, h]

/-! ### Counting the copies of an unknown -/

/-- The position of an operand that is an unknown. -/
def varIdx? (a : ArithOp) : Opnd Δ Φ Γ a → Option Nat
  | ⟨_, .neu (.var x)⟩ => some x.index
  | _ => none

theorem varIdx?_eval (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (p q : Opnd Δ Φ Γ a) (i : Nat)
    (hp : a.varIdx? p = some i) (hq : a.varIdx? q = some i) : a.val p κ ρ = a.val q κ ρ := by
  unfold varIdx? at hp hq
  split at hp
  · split at hq
    · rename_i x _ _ y
      have e1 := Option.some.inj hp
      have e2 := Option.some.inj hq
      have ⟨_, h2⟩ := UVar.eq_of_index_eq (Δ := Δ) x y (by rw [e1, e2])
      exact eq_of_heq (h2 ρ)
    · cases hq
  · cases hp

end ArithOp

end LeanScript

end
