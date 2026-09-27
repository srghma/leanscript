module
prelude
public import LeanScript.Ty.LeanPrimTy
public import LeanScript.Ty.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: floating-point numbers (`Float`, `Float32` and their conversions to signed integers)

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised).  Every family is written against
the same parameters as `LeanInitPureExtern`; only the ones its entries use become its own.
-/

open LeanPrimTy
open LeanPrimTyCovariant

variable {MyTy : Type}
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  (ordering : MyTy)

-----------------------------
-- Init/Data/Float/Float.lean
-----------------------------
/-- The pure externs of `Init/Data/Float/Float.lean`. -/
inductive FloatExtern : List MyTy → MyTy → Type where
  | lean_float_frexp : FloatExtern [float] (prod float int) -- Float.frExp
  | lean_uint8_to_float : FloatExtern [uint8] float -- UInt8.toFloat
  | lean_float_to_bits__Float_toModel : FloatExtern [float] floatModel -- Float.toModel
  | lean_float_to_bits__Float_toBits : FloatExtern [float] uint64 -- Float.toBits
  | lean_float_of_bits__Float_ofBits : FloatExtern [uint64] float -- Float.ofBits
  | lean_float_of_bits__Float_ofModel : FloatExtern [floatModel] float -- Float.ofModel
  | lean_float_isnan : FloatExtern [float] LeanPrimTy.bool -- Float.isNaN
  | log10 : FloatExtern [float] float -- Float.log10
  | cbrt : FloatExtern [float] float -- Float.cbrt
  | log : FloatExtern [float] float -- Float.log
  | lean_float_div : FloatExtern [float, float] float -- Float.div
  | lean_float_beq : FloatExtern [float, float] LeanPrimTy.bool -- Float.beq
  | tan : FloatExtern [float] float -- Float.tan
  | tanh : FloatExtern [float] float -- Float.tanh
  | exp2 : FloatExtern [float] float -- Float.exp2
  | lean_float_to_uint16 : FloatExtern [float] uint16 -- Float.toUInt16
  | lean_uint32_to_float : FloatExtern [uint32] float -- UInt32.toFloat
  | lean_float_decLe__Float_decLe : FloatExtern [float, float] LeanPrimTy.bool -- Float.decLe
  | lean_float_decLe__Float_le : FloatExtern [float, float] LeanPrimTy.bool -- Float.le
  | lean_float_to_uint64 : FloatExtern [float] uint64 -- Float.toUInt64
  | sqrt : FloatExtern [float] float -- Float.sqrt
  | acos : FloatExtern [float] float -- Float.acos
  | atan : FloatExtern [float] float -- Float.atan
  | acosh : FloatExtern [float] float -- Float.acosh
  | floor : FloatExtern [float] float -- Float.floor
  | fabs : FloatExtern [float] float -- Float.abs
  | lean_float_to_uint32 : FloatExtern [float] uint32 -- Float.toUInt32
  | lean_float_to_string : FloatExtern [float] string -- Float.toString
  | lean_uint64_to_float : FloatExtern [uint64] float -- UInt64.toFloat
  | lean_float_decLt__Float_decLt : FloatExtern [float, float] LeanPrimTy.bool -- Float.decLt
  | lean_float_decLt__Float_lt : FloatExtern [float, float] LeanPrimTy.bool -- Float.lt
  | lean_float_to_uint8 : FloatExtern [float] uint8 -- Float.toUInt8
  | sin : FloatExtern [float] float -- Float.sin
  -- | lean_usize_to_float : denote LeanPrimTy.usize → FloatExtern float -- USize.toFloat
  | cosh : FloatExtern [float] float -- Float.cosh
  | exp : FloatExtern [float] float -- Float.exp
  | ceil : FloatExtern [float] float -- Float.ceil
  -- | lean_float_to_usize : Float → FloatExtern LeanPrimTy.usize -- Float.toUSize
  | lean_float_isfinite : FloatExtern [float] LeanPrimTy.bool -- Float.isFinite
  | round : FloatExtern [float] float -- Float.round
  | cos : FloatExtern [float] float -- Float.cos
  | log2 : FloatExtern [float] float -- Float.log2
  | atanh : FloatExtern [float] float -- Float.atanh
  | atan2 : FloatExtern [float, float] float -- Float.atan2
  | sinh : FloatExtern [float] float -- Float.sinh
  | asinh : FloatExtern [float] float -- Float.asinh
  | lean_float_mul : FloatExtern [float, float] float -- Float.mul
  | lean_uint16_to_float : FloatExtern [uint16] float -- UInt16.toFloat
  | asin : FloatExtern [float] float -- Float.asin
  | pow : FloatExtern [float, float] float -- Float.pow
  | lean_float_scaleb : FloatExtern [float, int] float -- Float.scaleB
  | lean_float_add : FloatExtern [float, float] float -- Float.add
  | lean_float_sub : FloatExtern [float, float] float -- Float.sub
  | lean_float_negate : FloatExtern [float] float -- Float.neg
  | lean_float_isinf : FloatExtern [float] LeanPrimTy.bool -- Float.isInf

----------------------------
-- Init/Data/SInt/Float.lean
----------------------------
/-- The pure externs of `Init/Data/SInt/Float.lean`. -/
inductive SIntFloatExtern : List MyTy → MyTy → Type where
  | lean_int32_to_float : SIntFloatExtern [int32] float -- Int32.toFloat
  | lean_float_to_int16 : SIntFloatExtern [float] int16 -- Float.toInt16
  | lean_int16_to_float : SIntFloatExtern [int16] float -- Int16.toFloat
  | lean_float_to_int32 : SIntFloatExtern [float] int32 -- Float.toInt32
  -- | lean_isize_to_float : denote LeanPrimTy.isize → SIntFloatExtern float -- ISize.toFloat
  | lean_int8_to_float : SIntFloatExtern [int8] float -- Int8.toFloat
  | lean_float_to_int8 : SIntFloatExtern [float] int8 -- Float.toInt8
  | lean_int64_to_float : SIntFloatExtern [int64] float -- Int64.toFloat
  | lean_float_to_int64 : SIntFloatExtern [float] int64 -- Float.toInt64
  -- | lean_float_to_isize : Float → SIntFloatExtern LeanPrimTy.isize -- Float.toISize

-------------------------------
-- Init/Data/Float/Float32.lean
-------------------------------
/-- The pure externs of `Init/Data/Float/Float32.lean`. -/
inductive Float32Extern : List MyTy → MyTy → Type where
  | tanhf : Float32Extern [float32] float32 -- Float32.tanh
  | exp2f : Float32Extern [float32] float32 -- Float32.exp2
  | lean_float32_div : Float32Extern [float32, float32] float32 -- Float32.div
  | logf : Float32Extern [float32] float32 -- Float32.log
  | lean_float32_decLe__Float32_le : Float32Extern [float32, float32] LeanPrimTy.bool -- Float32.le
  | lean_float32_decLe__Float32_decLe : Float32Extern [float32, float32] LeanPrimTy.bool -- Float32.decLe
  | lean_float_to_float32 : Float32Extern [float] float32 -- Float.toFloat32
  | lean_float32_to_bits__Float32_toModel : Float32Extern [float32] float32Model -- Float32.toModel
  | lean_float32_to_bits__Float32_toBits : Float32Extern [float32] uint32 -- Float32.toBits
  | lean_float32_of_bits__Float32_ofBits : Float32Extern [uint32] float32 -- Float32.ofBits
  | lean_float32_of_bits__Float32_ofModel : Float32Extern [float32Model] float32 -- Float32.ofModel
  | atanf : Float32Extern [float32] float32 -- Float32.atan
  | acoshf : Float32Extern [float32] float32 -- Float32.acosh
  | lean_float32_frexp : Float32Extern [float32] (prod float32 int) -- Float32.frExp
  | lean_float32_to_uint64 : Float32Extern [float32] uint64 -- Float32.toUInt64
  | lean_float32_sub : Float32Extern [float32, float32] float32 -- Float32.sub
  | lean_float32_to_uint16 : Float32Extern [float32] uint16 -- Float32.toUInt16
  -- | lean_usize_to_float32 : denote LeanPrimTy.usize → Float32Extern float32 -- USize.toFloat32
  | asinf : Float32Extern [float32] float32 -- Float32.asin
  | powf : Float32Extern [float32, float32] float32 -- Float32.pow
  | lean_float32_beq : Float32Extern [float32, float32] LeanPrimTy.bool -- Float32.beq
  | lean_uint8_to_float32 : Float32Extern [uint8] float32 -- UInt8.toFloat32
  | tanf : Float32Extern [float32] float32 -- Float32.tan
  | lean_float32_to_float : Float32Extern [float32] float -- Float32.toFloat
  | lean_float32_isnan : Float32Extern [float32] LeanPrimTy.bool -- Float32.isNaN
  | log10f : Float32Extern [float32] float32 -- Float32.log10
  | cbrtf : Float32Extern [float32] float32 -- Float32.cbrt
  | atan2f : Float32Extern [float32, float32] float32 -- Float32.atan2
  | sinhf : Float32Extern [float32] float32 -- Float32.sinh
  | cosf : Float32Extern [float32] float32 -- Float32.cos
  | lean_uint32_to_float32 : Float32Extern [uint32] float32 -- UInt32.toFloat32
  | lean_float32_isinf : Float32Extern [float32] LeanPrimTy.bool -- Float32.isInf
  | lean_float32_negate : Float32Extern [float32] float32 -- Float32.neg
  -- | lean_float32_to_usize : Float32 → Float32Extern LeanPrimTy.usize -- Float32.toUSize
  | ceilf : Float32Extern [float32] float32 -- Float32.ceil
  | lean_float32_isfinite : Float32Extern [float32] LeanPrimTy.bool -- Float32.isFinite
  | lean_float32_add : Float32Extern [float32, float32] float32 -- Float32.add
  | lean_float32_scaleb : Float32Extern [float32, int] float32 -- Float32.scaleB
  | sinf : Float32Extern [float32] float32 -- Float32.sin
  | lean_float32_mul : Float32Extern [float32, float32] float32 -- Float32.mul
  | lean_float32_to_string : Float32Extern [float32] string -- Float32.toString
  | asinhf : Float32Extern [float32] float32 -- Float32.asinh
  | lean_float32_to_uint32 : Float32Extern [float32] uint32 -- Float32.toUInt32
  | log2f : Float32Extern [float32] float32 -- Float32.log2
  | lean_uint64_to_float32 : Float32Extern [uint64] float32 -- UInt64.toFloat32
  | atanhf : Float32Extern [float32] float32 -- Float32.atanh
  | floorf : Float32Extern [float32] float32 -- Float32.floor
  | fabsf : Float32Extern [float32] float32 -- Float32.abs
  | roundf : Float32Extern [float32] float32 -- Float32.round
  | lean_float32_decLt__Float32_lt : Float32Extern [float32, float32] LeanPrimTy.bool -- Float32.lt
  | lean_float32_decLt__Float32_decLt : Float32Extern [float32, float32] LeanPrimTy.bool -- Float32.decLt
  | acosf : Float32Extern [float32] float32 -- Float32.acos
  | sqrtf : Float32Extern [float32] float32 -- Float32.sqrt
  | lean_uint16_to_float32 : Float32Extern [uint16] float32 -- UInt16.toFloat32
  | coshf : Float32Extern [float32] float32 -- Float32.cosh
  | expf : Float32Extern [float32] float32 -- Float32.exp
  | lean_float32_to_uint8 : Float32Extern [float32] uint8 -- Float32.toUInt8

------------------------------
-- Init/Data/SInt/Float32.lean
------------------------------
/-- The pure externs of `Init/Data/SInt/Float32.lean`. -/
inductive SIntFloat32Extern : List MyTy → MyTy → Type where
  | lean_float32_to_int64 : SIntFloat32Extern [float32] int64 -- Float32.toInt64
  -- | lean_float32_to_isize : Float32 → SIntFloat32Extern LeanPrimTy.isize -- Float32.toISize
  | lean_int32_to_float32 : SIntFloat32Extern [int32] float32 -- Int32.toFloat32
  | lean_float32_to_int8 : SIntFloat32Extern [float32] int8 -- Float32.toInt8
  | lean_float32_to_int16 : SIntFloat32Extern [float32] int16 -- Float32.toInt16
  -- | lean_isize_to_float32 : denote LeanPrimTy.isize → SIntFloat32Extern float32 -- ISize.toFloat32
  | lean_int8_to_float32 : SIntFloat32Extern [int8] float32 -- Int8.toFloat32
  | lean_float32_to_int32 : SIntFloat32Extern [float32] int32 -- Float32.toInt32
  | lean_int16_to_float32 : SIntFloat32Extern [int16] float32 -- Int16.toFloat32
  | lean_int64_to_float32 : SIntFloat32Extern [int64] float32 -- Int64.toFloat32

end LeanScript

end
