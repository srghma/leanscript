module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: floats

The value of every entry of the families of `LeanScript.LeanInitPureExterns.Float`, at the
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

/-- The value of an entry of `FloatExtern` on the values of its arguments. -/
def FloatExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    FloatExtern (MyTy := Ty ks) Ty.pair σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_float_frexp, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (let r := Float.frExp x1; (HashableFloat.normalize r.1, r.2))
  | _, _, .lean_uint8_to_float, x1 =>
    let x1 : UInt8 := x1
    HashableFloat.normalize (UInt8.toFloat x1)
  | _, _, .lean_float_to_bits__Float_toModel, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toModel x1 : Float.Model)
  | _, _, .lean_float_to_bits__Float_toBits, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toBits x1 : UInt64)
  | _, _, .lean_float_of_bits__Float_ofBits, x1 =>
    let x1 : UInt64 := x1
    HashableFloat.normalize (Float.ofBits x1)
  | _, _, .lean_float_of_bits__Float_ofModel, x1 =>
    let x1 : Float.Model := x1
    HashableFloat.normalize (Float.ofModel x1)
  | _, _, .lean_float_isnan, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    ExternBool.toBool (Float.isNaN x1)
  | _, _, .log10, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.log10 x1)
  | _, _, .cbrt, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.cbrt x1)
  | _, _, .log, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.log x1)
  | _, _, .lean_float_div, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.div x1 x2)
  | _, _, .lean_float_beq, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    ExternBool.toBool (Float.beq x1 x2)
  | _, _, .tan, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.tan x1)
  | _, _, .tanh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.tanh x1)
  | _, _, .exp2, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.exp2 x1)
  | _, _, .lean_float_to_uint16, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toUInt16 x1 : UInt16)
  | _, _, .lean_uint32_to_float, x1 =>
    let x1 : UInt32 := x1
    HashableFloat.normalize (UInt32.toFloat x1)
  | _, _, .lean_float_decLe__Float_decLe, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    ExternBool.toBool (Float.decLe x1 x2)
  | _, _, .lean_float_decLe__Float_le, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    ExternBool.toBool (Float.le x1 x2)
  | _, _, .lean_float_to_uint64, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toUInt64 x1 : UInt64)
  | _, _, .sqrt, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.sqrt x1)
  | _, _, .acos, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.acos x1)
  | _, _, .atan, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.atan x1)
  | _, _, .acosh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.acosh x1)
  | _, _, .floor, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.floor x1)
  | _, _, .fabs, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.abs x1)
  | _, _, .lean_float_to_uint32, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toUInt32 x1 : UInt32)
  | _, _, .lean_float_to_string, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toString x1 : String)
  | _, _, .lean_uint64_to_float, x1 =>
    let x1 : UInt64 := x1
    HashableFloat.normalize (UInt64.toFloat x1)
  | _, _, .lean_float_decLt__Float_decLt, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    ExternBool.toBool (Float.decLt x1 x2)
  | _, _, .lean_float_decLt__Float_lt, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    ExternBool.toBool (Float.lt x1 x2)
  | _, _, .lean_float_to_uint8, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toUInt8 x1 : UInt8)
  | _, _, .sin, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.sin x1)
  | _, _, .cosh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.cosh x1)
  | _, _, .exp, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.exp x1)
  | _, _, .ceil, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.ceil x1)
  | _, _, .lean_float_isfinite, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    ExternBool.toBool (Float.isFinite x1)
  | _, _, .round, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.round x1)
  | _, _, .cos, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.cos x1)
  | _, _, .log2, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.log2 x1)
  | _, _, .atanh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.atanh x1)
  | _, _, .atan2, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.atan2 x1 x2)
  | _, _, .sinh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.sinh x1)
  | _, _, .asinh, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.asinh x1)
  | _, _, .lean_float_mul, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.mul x1 x2)
  | _, _, .lean_uint16_to_float, x1 =>
    let x1 : UInt16 := x1
    HashableFloat.normalize (UInt16.toFloat x1)
  | _, _, .asin, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.asin x1)
  | _, _, .pow, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.pow x1 x2)
  | _, _, .lean_float_scaleb, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Int := x2
    HashableFloat.normalize (Float.scaleB x1 x2)
  | _, _, .lean_float_add, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.add x1 x2)
  | _, _, .lean_float_sub, (x1, x2) =>
    let x1 : Float := HashableFloat.toFloat x1
    let x2 : Float := HashableFloat.toFloat x2
    HashableFloat.normalize (Float.sub x1 x2)
  | _, _, .lean_float_negate, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat.normalize (Float.neg x1)
  | _, _, .lean_float_isinf, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    ExternBool.toBool (Float.isInf x1)

/-- The value of an entry of `SIntFloatExtern` on the values of its arguments. -/
def SIntFloatExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    SIntFloatExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int32_to_float, x1 =>
    let x1 : Int32 := x1
    HashableFloat.normalize (Int32.toFloat x1)
  | _, _, .lean_float_to_int16, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toInt16 x1 : Int16)
  | _, _, .lean_int16_to_float, x1 =>
    let x1 : Int16 := x1
    HashableFloat.normalize (Int16.toFloat x1)
  | _, _, .lean_float_to_int32, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toInt32 x1 : Int32)
  | _, _, .lean_int8_to_float, x1 =>
    let x1 : Int8 := x1
    HashableFloat.normalize (Int8.toFloat x1)
  | _, _, .lean_float_to_int8, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toInt8 x1 : Int8)
  | _, _, .lean_int64_to_float, x1 =>
    let x1 : Int64 := x1
    HashableFloat.normalize (Int64.toFloat x1)
  | _, _, .lean_float_to_int64, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    (Float.toInt64 x1 : Int64)

/-- The value of an entry of `Float32Extern` on the values of its arguments. -/
def Float32Extern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    Float32Extern (MyTy := Ty ks) Ty.pair σs τ → DenList E σs → Ty.den E τ
  | _, _, .tanhf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.tanh x1)
  | _, _, .exp2f, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.exp2 x1)
  | _, _, .lean_float32_div, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.div x1 x2)
  | _, _, .logf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.log x1)
  | _, _, .lean_float32_decLe__Float32_le, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    ExternBool.toBool (Float32.le x1 x2)
  | _, _, .lean_float32_decLe__Float32_decLe, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    ExternBool.toBool (Float32.decLe x1 x2)
  | _, _, .lean_float_to_float32, x1 =>
    let x1 : Float := HashableFloat.toFloat x1
    HashableFloat32.normalize (Float.toFloat32 x1)
  | _, _, .lean_float32_to_bits__Float32_toModel, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toModel x1 : Float32.Model)
  | _, _, .lean_float32_to_bits__Float32_toBits, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toBits x1 : UInt32)
  | _, _, .lean_float32_of_bits__Float32_ofBits, x1 =>
    let x1 : UInt32 := x1
    HashableFloat32.normalize (Float32.ofBits x1)
  | _, _, .lean_float32_of_bits__Float32_ofModel, x1 =>
    let x1 : Float32.Model := x1
    HashableFloat32.normalize (Float32.ofModel x1)
  | _, _, .atanf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.atan x1)
  | _, _, .acoshf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.acosh x1)
  | _, _, .lean_float32_frexp, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (let r := Float32.frExp x1; (HashableFloat32.normalize r.1, r.2))
  | _, _, .lean_float32_to_uint64, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toUInt64 x1 : UInt64)
  | _, _, .lean_float32_sub, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.sub x1 x2)
  | _, _, .lean_float32_to_uint16, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toUInt16 x1 : UInt16)
  | _, _, .asinf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.asin x1)
  | _, _, .powf, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.pow x1 x2)
  | _, _, .lean_float32_beq, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    ExternBool.toBool (Float32.beq x1 x2)
  | _, _, .lean_uint8_to_float32, x1 =>
    let x1 : UInt8 := x1
    HashableFloat32.normalize (UInt8.toFloat32 x1)
  | _, _, .tanf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.tan x1)
  | _, _, .lean_float32_to_float, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat.normalize (Float32.toFloat x1)
  | _, _, .lean_float32_isnan, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    ExternBool.toBool (Float32.isNaN x1)
  | _, _, .log10f, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.log10 x1)
  | _, _, .cbrtf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.cbrt x1)
  | _, _, .atan2f, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.atan2 x1 x2)
  | _, _, .sinhf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.sinh x1)
  | _, _, .cosf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.cos x1)
  | _, _, .lean_uint32_to_float32, x1 =>
    let x1 : UInt32 := x1
    HashableFloat32.normalize (UInt32.toFloat32 x1)
  | _, _, .lean_float32_isinf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    ExternBool.toBool (Float32.isInf x1)
  | _, _, .lean_float32_negate, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.neg x1)
  | _, _, .ceilf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.ceil x1)
  | _, _, .lean_float32_isfinite, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    ExternBool.toBool (Float32.isFinite x1)
  | _, _, .lean_float32_add, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.add x1 x2)
  | _, _, .lean_float32_scaleb, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Int := x2
    HashableFloat32.normalize (Float32.scaleB x1 x2)
  | _, _, .sinf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.sin x1)
  | _, _, .lean_float32_mul, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    HashableFloat32.normalize (Float32.mul x1 x2)
  | _, _, .lean_float32_to_string, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toString x1 : String)
  | _, _, .asinhf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.asinh x1)
  | _, _, .lean_float32_to_uint32, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toUInt32 x1 : UInt32)
  | _, _, .log2f, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.log2 x1)
  | _, _, .lean_uint64_to_float32, x1 =>
    let x1 : UInt64 := x1
    HashableFloat32.normalize (UInt64.toFloat32 x1)
  | _, _, .atanhf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.atanh x1)
  | _, _, .floorf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.floor x1)
  | _, _, .fabsf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.abs x1)
  | _, _, .roundf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.round x1)
  | _, _, .lean_float32_decLt__Float32_lt, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    ExternBool.toBool (Float32.lt x1 x2)
  | _, _, .lean_float32_decLt__Float32_decLt, (x1, x2) =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    let x2 : Float32 := HashableFloat32.toFloat32 x2
    ExternBool.toBool (Float32.decLt x1 x2)
  | _, _, .acosf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.acos x1)
  | _, _, .sqrtf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.sqrt x1)
  | _, _, .lean_uint16_to_float32, x1 =>
    let x1 : UInt16 := x1
    HashableFloat32.normalize (UInt16.toFloat32 x1)
  | _, _, .coshf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.cosh x1)
  | _, _, .expf, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    HashableFloat32.normalize (Float32.exp x1)
  | _, _, .lean_float32_to_uint8, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toUInt8 x1 : UInt8)

/-- The value of an entry of `SIntFloat32Extern` on the values of its arguments. -/
def SIntFloat32Extern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    SIntFloat32Extern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_float32_to_int64, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toInt64 x1 : Int64)
  | _, _, .lean_int32_to_float32, x1 =>
    let x1 : Int32 := x1
    HashableFloat32.normalize (Int32.toFloat32 x1)
  | _, _, .lean_float32_to_int8, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toInt8 x1 : Int8)
  | _, _, .lean_float32_to_int16, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toInt16 x1 : Int16)
  | _, _, .lean_int8_to_float32, x1 =>
    let x1 : Int8 := x1
    HashableFloat32.normalize (Int8.toFloat32 x1)
  | _, _, .lean_float32_to_int32, x1 =>
    let x1 : Float32 := HashableFloat32.toFloat32 x1
    (Float32.toInt32 x1 : Int32)
  | _, _, .lean_int16_to_float32, x1 =>
    let x1 : Int16 := x1
    HashableFloat32.normalize (Int16.toFloat32 x1)
  | _, _, .lean_int64_to_float32, x1 =>
    let x1 : Int64 := x1
    HashableFloat32.normalize (Int64.toFloat32 x1)

end LeanScript

end
