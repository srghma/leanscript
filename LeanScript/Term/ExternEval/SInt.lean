module

public import LeanScript.Term.Extern

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the signed fixed-width integers (`Int8` … `Int64`)

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

end LeanScript

end
