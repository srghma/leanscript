module

public import LeanScript.Term.Extern

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the fixed-width integers (`UInt8` … `Int64`)

The value of every entry of the families of `LeanScript.LeanInitPureExterns.FixedWidth`, at the
instantiation of the catalogue to the types of the language (`LeanScript.Extern`), on the
values of its arguments: the Lean function the entry stands for.

The arguments are first bound at their Lean types, so the Lean function elaborates as in
Lean.  A `Float` is the `HashableFloat` of the language: an argument is its underlying
float and a result is normalised (`HashableFloat.normalize`).  A function that returns
`Decidable p` answers `decide p` (`ExternBool`).  A proof that the Lean function takes is
erased by the language, so it is decided on the values of the arguments; when it does not
hold (which never happens in a term translated from a Lean program, which had to prove it)
the answer is a default value.
-/

namespace LeanScript

/-- The value of an entry of `UIntBasicAuxExtern` on the values of its arguments. -/
def UIntBasicAuxExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UIntBasicAuxExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint64_to_nat__UInt64_toNat, x1 =>
    let x1 : UInt64 := x1
    (UInt64.toNat x1 : Nat)
  | _, _, .lean_uint32_to_uint8, x1 =>
    let x1 : UInt32 := x1
    (UInt32.toUInt8 x1 : UInt8)
  | _, _, .lean_uint64_to_uint32, x1 =>
    let x1 : UInt64 := x1
    (UInt64.toUInt32 x1 : UInt32)
  | _, _, .lean_uint32_to_uint16, x1 =>
    let x1 : UInt32 := x1
    (UInt32.toUInt16 x1 : UInt16)
  | _, _, .lean_uint16_to_uint32, x1 =>
    let x1 : UInt16 := x1
    (UInt16.toUInt32 x1 : UInt32)
  | _, _, .lean_uint32_to_uint64, x1 =>
    let x1 : UInt32 := x1
    (UInt32.toUInt64 x1 : UInt64)
  | _, _, .lean_uint32_of_nat__UInt32_ofNat, x1 =>
    let x1 : Nat := x1
    (UInt32.ofNat x1 : UInt32)
  | _, _, .lean_uint32_sub, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.sub x1 x2 : UInt32)
  | _, _, .lean_uint16_to_nat__UInt16_toNat, x1 =>
    let x1 : UInt16 := x1
    (UInt16.toNat x1 : Nat)
  | _, _, .lean_uint16_to_uint8, x1 =>
    let x1 : UInt16 := x1
    (UInt16.toUInt8 x1 : UInt8)
  | _, _, .lean_uint32_add, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.add x1 x2 : UInt32)
  | _, _, .lean_uint8_to_uint64, x1 =>
    let x1 : UInt8 := x1
    (UInt8.toUInt64 x1 : UInt64)
  | _, _, .lean_uint8_to_nat__UInt8_toNat, x1 =>
    let x1 : UInt8 := x1
    (UInt8.toNat x1 : Nat)
  | _, _, .lean_uint64_of_nat__UInt64_ofNat, x1 =>
    let x1 : Nat := x1
    (UInt64.ofNat x1 : UInt64)
  | _, _, .lean_uint8_to_uint32, x1 =>
    let x1 : UInt8 := x1
    (UInt8.toUInt32 x1 : UInt32)
  | _, _, .lean_uint16_of_nat__UInt16_ofNat, x1 =>
    let x1 : Nat := x1
    (UInt16.ofNat x1 : UInt16)
  | _, _, .lean_uint16_to_uint64, x1 =>
    let x1 : UInt16 := x1
    (UInt16.toUInt64 x1 : UInt64)
  | _, _, .lean_uint64_to_uint8, x1 =>
    let x1 : UInt64 := x1
    (UInt64.toUInt8 x1 : UInt8)
  | _, _, .lean_uint64_to_uint16, x1 =>
    let x1 : UInt64 := x1
    (UInt64.toUInt16 x1 : UInt16)
  | _, _, .lean_uint8_to_uint16, x1 =>
    let x1 : UInt8 := x1
    (UInt8.toUInt16 x1 : UInt16)

/-- The value of an entry of `UInt8BasicExtern` on the values of its arguments. -/
def UInt8BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UInt8BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint8_sub, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.sub x1 x2 : UInt8)
  | _, _, .lean_uint8_neg, x1 =>
    let x1 : UInt8 := x1
    (UInt8.neg x1 : UInt8)
  | _, _, .lean_uint8_lor, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.lor x1 x2 : UInt8)
  | _, _, .lean_uint8_div, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.div x1 x2 : UInt8)
  | _, _, .lean_uint8_shift_right, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.shiftRight x1 x2 : UInt8)
  | _, _, .lean_uint8_shift_left, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.shiftLeft x1 x2 : UInt8)
  | _, _, .lean_uint8_land, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.land x1 x2 : UInt8)
  | _, _, .lean_uint8_mul, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.mul x1 x2 : UInt8)
  | _, _, .lean_uint8_add, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.add x1 x2 : UInt8)
  | _, _, .lean_uint8_complement, x1 =>
    let x1 : UInt8 := x1
    (UInt8.complement x1 : UInt8)
  | _, _, .lean_uint8_mod, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.mod x1 x2 : UInt8)
  | _, _, .lean_bool_to_uint8, x1 =>
    let x1 : Bool := x1
    (Bool.toUInt8 x1 : UInt8)
  | _, _, .lean_uint8_xor, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    (UInt8.xor x1 x2 : UInt8)

/-- The value of an entry of `UInt16BasicExtern` on the values of its arguments. -/
def UInt16BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UInt16BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint16_neg, x1 =>
    let x1 : UInt16 := x1
    (UInt16.neg x1 : UInt16)
  | _, _, .lean_uint16_add, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.add x1 x2 : UInt16)
  | _, _, .lean_uint16_lor, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.lor x1 x2 : UInt16)
  | _, _, .lean_uint16_mul, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.mul x1 x2 : UInt16)
  | _, _, .lean_uint16_land, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.land x1 x2 : UInt16)
  | _, _, .lean_uint16_complement, x1 =>
    let x1 : UInt16 := x1
    (UInt16.complement x1 : UInt16)
  | _, _, .lean_uint16_xor, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.xor x1 x2 : UInt16)
  | _, _, .lean_uint16_shift_left, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.shiftLeft x1 x2 : UInt16)
  | _, _, .lean_uint16_mod, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.mod x1 x2 : UInt16)
  | _, _, .lean_uint16_dec_lt, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    ExternBool.toBool (UInt16.decLt x1 x2)
  | _, _, .lean_uint16_div, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.div x1 x2 : UInt16)
  | _, _, .lean_uint16_dec_le, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    ExternBool.toBool (UInt16.decLe x1 x2)
  | _, _, .lean_uint16_sub, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.sub x1 x2 : UInt16)
  | _, _, .lean_bool_to_uint16, x1 =>
    let x1 : Bool := x1
    (Bool.toUInt16 x1 : UInt16)
  | _, _, .lean_uint16_shift_right, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    (UInt16.shiftRight x1 x2 : UInt16)

/-- The value of an entry of `UInt32BasicExtern` on the values of its arguments. -/
def UInt32BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UInt32BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint32_mod, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.mod x1 x2 : UInt32)
  | _, _, .lean_bool_to_uint32, x1 =>
    let x1 : Bool := x1
    (Bool.toUInt32 x1 : UInt32)
  | _, _, .lean_uint32_div, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.div x1 x2 : UInt32)
  | _, _, .lean_uint32_shift_right, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.shiftRight x1 x2 : UInt32)
  | _, _, .lean_uint32_neg, x1 =>
    let x1 : UInt32 := x1
    (UInt32.neg x1 : UInt32)
  | _, _, .lean_uint32_lor, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.lor x1 x2 : UInt32)
  | _, _, .lean_uint32_xor, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.xor x1 x2 : UInt32)
  | _, _, .lean_uint32_shift_left, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.shiftLeft x1 x2 : UInt32)
  | _, _, .lean_uint32_mul, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.mul x1 x2 : UInt32)
  | _, _, .lean_uint32_land, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    (UInt32.land x1 x2 : UInt32)
  | _, _, .lean_uint32_complement, x1 =>
    let x1 : UInt32 := x1
    (UInt32.complement x1 : UInt32)

/-- The value of an entry of `UInt64BasicExtern` on the values of its arguments. -/
def UInt64BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UInt64BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint64_shift_left, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.shiftLeft x1 x2 : UInt64)
  | _, _, .lean_uint64_shift_right, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.shiftRight x1 x2 : UInt64)
  | _, _, .lean_uint64_complement, x1 =>
    let x1 : UInt64 := x1
    (UInt64.complement x1 : UInt64)
  | _, _, .lean_uint64_add, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.add x1 x2 : UInt64)
  | _, _, .lean_uint64_lor, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.lor x1 x2 : UInt64)
  | _, _, .lean_uint64_mod, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.mod x1 x2 : UInt64)
  | _, _, .lean_uint64_div, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.div x1 x2 : UInt64)
  | _, _, .lean_uint64_mul, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.mul x1 x2 : UInt64)
  | _, _, .lean_uint64_land, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.land x1 x2 : UInt64)
  | _, _, .lean_bool_to_uint64, x1 =>
    let x1 : Bool := x1
    (Bool.toUInt64 x1 : UInt64)
  | _, _, .lean_uint64_dec_le, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    ExternBool.toBool (UInt64.decLe x1 x2)
  | _, _, .lean_uint64_sub, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.sub x1 x2 : UInt64)
  | _, _, .lean_uint64_neg, x1 =>
    let x1 : UInt64 := x1
    (UInt64.neg x1 : UInt64)
  | _, _, .lean_uint64_dec_lt, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    ExternBool.toBool (UInt64.decLt x1 x2)
  | _, _, .lean_uint64_xor, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (UInt64.xor x1 x2 : UInt64)

/-- The value of an entry of `Int8BasicExtern` on the values of its arguments. -/
def Int8BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    Int8BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int8_add, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.add x1 x2 : Int8)
  | _, _, .lean_int8_div, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.div x1 x2 : Int8)
  | _, _, .lean_int8_to_int16, x1 =>
    let x1 : Int8 := x1
    (Int8.toInt16 x1 : Int16)
  | _, _, .lean_int8_shift_right, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.shiftRight x1 x2 : Int8)
  | _, _, .lean_int8_mod, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.mod x1 x2 : Int8)
  | _, _, .lean_bool_to_int8, x1 =>
    let x1 : Bool := x1
    (Bool.toInt8 x1 : Int8)
  | _, _, .lean_int8_shift_left, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.shiftLeft x1 x2 : Int8)
  | _, _, .lean_int8_xor, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.xor x1 x2 : Int8)
  | _, _, .lean_int8_complement, x1 =>
    let x1 : Int8 := x1
    (Int8.complement x1 : Int8)
  | _, _, .lean_int8_dec_eq, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    ExternBool.toBool (Int8.decEq x1 x2)
  | _, _, .lean_int8_neg, x1 =>
    let x1 : Int8 := x1
    (Int8.neg x1 : Int8)
  | _, _, .lean_int8_dec_lt, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    ExternBool.toBool (Int8.decLt x1 x2)
  | _, _, .lean_int8_abs, x1 =>
    let x1 : Int8 := x1
    (Int8.abs x1 : Int8)
  | _, _, .lean_int8_to_int32, x1 =>
    let x1 : Int8 := x1
    (Int8.toInt32 x1 : Int32)
  | _, _, .lean_int8_sub, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.sub x1 x2 : Int8)
  | _, _, .lean_int8_to_int64, x1 =>
    let x1 : Int8 := x1
    (Int8.toInt64 x1 : Int64)
  | _, _, .lean_int8_of_nat, x1 =>
    let x1 : Nat := x1
    (Int8.ofNat x1 : Int8)
  | _, _, .lean_int8_dec_le, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    ExternBool.toBool (Int8.decLe x1 x2)
  | _, _, .lean_int8_to_int, x1 =>
    let x1 : Int8 := x1
    (Int8.toInt x1 : Int)
  | _, _, .lean_int8_mul, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.mul x1 x2 : Int8)
  | _, _, .lean_int8_land, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.land x1 x2 : Int8)
  | _, _, .lean_int8_of_int, x1 =>
    let x1 : Int := x1
    (Int8.ofInt x1 : Int8)
  | _, _, .lean_int8_lor, (x1, x2) =>
    let x1 : Int8 := x1
    let x2 : Int8 := x2
    (Int8.lor x1 x2 : Int8)

/-- The value of an entry of `Int16BasicExtern` on the values of its arguments. -/
def Int16BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    Int16BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int16_of_nat, x1 =>
    let x1 : Nat := x1
    (Int16.ofNat x1 : Int16)
  | _, _, .lean_int16_dec_le, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    ExternBool.toBool (Int16.decLe x1 x2)
  | _, _, .lean_int16_shift_right, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.shiftRight x1 x2 : Int16)
  | _, _, .lean_int16_div, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.div x1 x2 : Int16)
  | _, _, .lean_int16_dec_lt, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    ExternBool.toBool (Int16.decLt x1 x2)
  | _, _, .lean_int16_to_int, x1 =>
    let x1 : Int16 := x1
    (Int16.toInt x1 : Int)
  | _, _, .lean_int16_mod, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.mod x1 x2 : Int16)
  | _, _, .lean_int16_dec_eq, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    ExternBool.toBool (Int16.decEq x1 x2)
  | _, _, .lean_bool_to_int16, x1 =>
    let x1 : Bool := x1
    (Bool.toInt16 x1 : Int16)
  | _, _, .lean_int16_abs, x1 =>
    let x1 : Int16 := x1
    (Int16.abs x1 : Int16)
  | _, _, .lean_int16_to_int32, x1 =>
    let x1 : Int16 := x1
    (Int16.toInt32 x1 : Int32)
  | _, _, .lean_int16_complement, x1 =>
    let x1 : Int16 := x1
    (Int16.complement x1 : Int16)
  | _, _, .lean_int16_land, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.land x1 x2 : Int16)
  | _, _, .lean_int16_of_int, x1 =>
    let x1 : Int := x1
    (Int16.ofInt x1 : Int16)
  | _, _, .lean_int16_mul, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.mul x1 x2 : Int16)
  | _, _, .lean_int16_shift_left, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.shiftLeft x1 x2 : Int16)
  | _, _, .lean_int16_xor, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.xor x1 x2 : Int16)
  | _, _, .lean_int16_lor, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.lor x1 x2 : Int16)
  | _, _, .lean_int16_add, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.add x1 x2 : Int16)
  | _, _, .lean_int16_to_int8, x1 =>
    let x1 : Int16 := x1
    (Int16.toInt8 x1 : Int8)
  | _, _, .lean_int16_neg, x1 =>
    let x1 : Int16 := x1
    (Int16.neg x1 : Int16)
  | _, _, .lean_int16_sub, (x1, x2) =>
    let x1 : Int16 := x1
    let x2 : Int16 := x2
    (Int16.sub x1 x2 : Int16)
  | _, _, .lean_int16_to_int64, x1 =>
    let x1 : Int16 := x1
    (Int16.toInt64 x1 : Int64)

/-- The value of an entry of `Int32BasicExtern` on the values of its arguments. -/
def Int32BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    Int32BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int32_of_int, x1 =>
    let x1 : Int := x1
    (Int32.ofInt x1 : Int32)
  | _, _, .lean_int32_land, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.land x1 x2 : Int32)
  | _, _, .lean_int32_mul, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.mul x1 x2 : Int32)
  | _, _, .lean_int32_dec_le, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    ExternBool.toBool (Int32.decLe x1 x2)
  | _, _, .lean_int32_of_nat, x1 =>
    let x1 : Nat := x1
    (Int32.ofNat x1 : Int32)
  | _, _, .lean_int32_to_int64, x1 =>
    let x1 : Int32 := x1
    (Int32.toInt64 x1 : Int64)
  | _, _, .lean_int32_sub, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.sub x1 x2 : Int32)
  | _, _, .lean_int32_neg, x1 =>
    let x1 : Int32 := x1
    (Int32.neg x1 : Int32)
  | _, _, .lean_int32_abs, x1 =>
    let x1 : Int32 := x1
    (Int32.abs x1 : Int32)
  | _, _, .lean_int32_dec_eq, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    ExternBool.toBool (Int32.decEq x1 x2)
  | _, _, .lean_int32_dec_lt, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    ExternBool.toBool (Int32.decLt x1 x2)
  | _, _, .lean_int32_xor, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.xor x1 x2 : Int32)
  | _, _, .lean_int32_shift_left, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.shiftLeft x1 x2 : Int32)
  | _, _, .lean_int32_shift_right, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.shiftRight x1 x2 : Int32)
  | _, _, .lean_int32_complement, x1 =>
    let x1 : Int32 := x1
    (Int32.complement x1 : Int32)
  | _, _, .lean_bool_to_int32, x1 =>
    let x1 : Bool := x1
    (Bool.toInt32 x1 : Int32)
  | _, _, .lean_int32_to_int8, x1 =>
    let x1 : Int32 := x1
    (Int32.toInt8 x1 : Int8)
  | _, _, .lean_int32_add, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.add x1 x2 : Int32)
  | _, _, .lean_int32_lor, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.lor x1 x2 : Int32)
  | _, _, .lean_int32_mod, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.mod x1 x2 : Int32)
  | _, _, .lean_int32_to_int, x1 =>
    let x1 : Int32 := x1
    (Int32.toInt x1 : Int)
  | _, _, .lean_int32_to_int16, x1 =>
    let x1 : Int32 := x1
    (Int32.toInt16 x1 : Int16)
  | _, _, .lean_int32_div, (x1, x2) =>
    let x1 : Int32 := x1
    let x2 : Int32 := x2
    (Int32.div x1 x2 : Int32)

/-- The value of an entry of `Int64BasicExtern` on the values of its arguments. -/
def Int64BasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    Int64BasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int64_sub, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.sub x1 x2 : Int64)
  | _, _, .lean_int64_xor, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.xor x1 x2 : Int64)
  | _, _, .lean_int64_to_int8, x1 =>
    let x1 : Int64 := x1
    (Int64.toInt8 x1 : Int8)
  | _, _, .lean_int64_mul, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.mul x1 x2 : Int64)
  | _, _, .lean_int64_of_int, x1 =>
    let x1 : Int := x1
    (Int64.ofInt x1 : Int64)
  | _, _, .lean_int64_land, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.land x1 x2 : Int64)
  | _, _, .lean_int64_lor, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.lor x1 x2 : Int64)
  | _, _, .lean_int64_mod, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.mod x1 x2 : Int64)
  | _, _, .lean_int64_shift_left, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.shiftLeft x1 x2 : Int64)
  | _, _, .lean_int64_dec_lt, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    ExternBool.toBool (Int64.decLt x1 x2)
  | _, _, .lean_int64_complement, x1 =>
    let x1 : Int64 := x1
    (Int64.complement x1 : Int64)
  | _, _, .lean_int64_to_int32, x1 =>
    let x1 : Int64 := x1
    (Int64.toInt32 x1 : Int32)
  | _, _, .lean_int64_abs, x1 =>
    let x1 : Int64 := x1
    (Int64.abs x1 : Int64)
  | _, _, .lean_bool_to_int64, x1 =>
    let x1 : Bool := x1
    (Bool.toInt64 x1 : Int64)
  | _, _, .lean_int64_dec_eq, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    ExternBool.toBool (Int64.decEq x1 x2)
  | _, _, .lean_int64_dec_le, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    ExternBool.toBool (Int64.decLe x1 x2)
  | _, _, .lean_int64_of_nat, x1 =>
    let x1 : Nat := x1
    (Int64.ofNat x1 : Int64)
  | _, _, .lean_int64_to_int_sint, x1 =>
    let x1 : Int64 := x1
    (Int64.toInt x1 : Int)
  | _, _, .lean_int64_neg, x1 =>
    let x1 : Int64 := x1
    (Int64.neg x1 : Int64)
  | _, _, .lean_int64_add, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.add x1 x2 : Int64)
  | _, _, .lean_int64_div, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.div x1 x2 : Int64)
  | _, _, .lean_int64_to_int16, x1 =>
    let x1 : Int64 := x1
    (Int64.toInt16 x1 : Int16)
  | _, _, .lean_int64_shift_right, (x1, x2) =>
    let x1 : Int64 := x1
    let x2 : Int64 := x2
    (Int64.shiftRight x1 x2 : Int64)

/-- The value of an entry of `UIntLog2Extern` on the values of its arguments. -/
def UIntLog2Extern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UIntLog2Extern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint16_log2, x1 =>
    let x1 : UInt16 := x1
    (UInt16.log2 x1 : UInt16)
  | _, _, .lean_uint64_log2, x1 =>
    let x1 : UInt64 := x1
    (UInt64.log2 x1 : UInt64)
  | _, _, .lean_uint8_log2, x1 =>
    let x1 : UInt8 := x1
    (UInt8.log2 x1 : UInt8)
  | _, _, .lean_uint32_log2, x1 =>
    let x1 : UInt32 := x1
    (UInt32.log2 x1 : UInt32)

end LeanScript

end
