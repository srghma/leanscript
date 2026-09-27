module
prelude
public import LeanScript.Ty.LeanPrimTy
public import LeanScript.Ty.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: the fixed-width integers (`UInt8` … `UInt64`, `Int8` … `Int64`)

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

-------------------------------
-- Init/Data/UInt/BasicAux.lean
-------------------------------
/-- The pure externs of `Init/Data/UInt/BasicAux.lean`. -/
inductive UIntBasicAuxExtern : List MyTy → MyTy → Type where
  | lean_uint64_to_nat__UInt64_toNat : UIntBasicAuxExtern [uint64] nat -- UInt64.toNat
  | lean_uint32_to_uint8 : UIntBasicAuxExtern [uint32] uint8 -- UInt32.toUInt8
  -- | lean_usize_to_nat__USize_toNat : denote LeanPrimTy.usize → UIntBasicAuxExtern nat -- USize.toNat
  | lean_uint64_to_uint32 : UIntBasicAuxExtern [uint64] uint32 -- UInt64.toUInt32
  | lean_uint32_to_uint16 : UIntBasicAuxExtern [uint32] uint16 -- UInt32.toUInt16
  | lean_uint16_to_uint32 : UIntBasicAuxExtern [uint16] uint32 -- UInt16.toUInt32
  | lean_uint32_to_uint64 : UIntBasicAuxExtern [uint32] uint64 -- UInt32.toUInt64
  | lean_uint32_of_nat__UInt32_ofNat : UIntBasicAuxExtern [nat] uint32 -- UInt32.ofNat
  -- | lean_usize_add : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.usize -- USize.add
  | lean_uint32_sub : UIntBasicAuxExtern [uint32, uint32] uint32 -- UInt32.sub
  | lean_uint16_to_nat__UInt16_toNat : UIntBasicAuxExtern [uint16] nat -- UInt16.toNat
  | lean_uint16_to_uint8 : UIntBasicAuxExtern [uint16] uint8 -- UInt16.toUInt8
  -- | lean_usize_sub : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.usize -- USize.sub
  | lean_uint32_add : UIntBasicAuxExtern [uint32, uint32] uint32 -- UInt32.add
  -- | lean_usize_of_nat__USize_ofNat : Nat → UIntBasicAuxExtern LeanPrimTy.usize -- USize.ofNat
  -- | lean_usize_dec_le : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.bool -- USize.decLe
  | lean_uint8_to_uint64 : UIntBasicAuxExtern [uint8] uint64 -- UInt8.toUInt64
  | lean_uint8_to_nat__UInt8_toNat : UIntBasicAuxExtern [uint8] nat -- UInt8.toNat
  | lean_uint64_of_nat__UInt64_ofNat : UIntBasicAuxExtern [nat] uint64 -- UInt64.ofNat
  | lean_uint8_to_uint32 : UIntBasicAuxExtern [uint8] uint32 -- UInt8.toUInt32
  | lean_uint16_of_nat__UInt16_ofNat : UIntBasicAuxExtern [nat] uint16 -- UInt16.ofNat
  | lean_uint16_to_uint64 : UIntBasicAuxExtern [uint16] uint64 -- UInt16.toUInt64
  -- | lean_usize_dec_lt : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UIntBasicAuxExtern LeanPrimTy.bool -- USize.decLt
  | lean_uint64_to_uint8 : UIntBasicAuxExtern [uint64] uint8 -- UInt64.toUInt8
  | lean_uint64_to_uint16 : UIntBasicAuxExtern [uint64] uint16 -- UInt64.toUInt16
  | lean_uint8_to_uint16 : UIntBasicAuxExtern [uint8] uint16 -- UInt8.toUInt16

-------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt8` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt8`. -/
inductive UInt8BasicExtern : List MyTy → MyTy → Type where
  | lean_uint8_sub : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.sub
  | lean_uint8_neg : UInt8BasicExtern [uint8] uint8 -- UInt8.neg
  | lean_uint8_lor : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.lor
  | lean_uint8_div : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.div
  | lean_uint8_shift_right : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.shiftRight
  | lean_uint8_shift_left : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.shiftLeft
  | lean_uint8_land : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.land
  | lean_uint8_mul : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.mul
  | lean_uint8_add : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.add
  | lean_uint8_complement : UInt8BasicExtern [uint8] uint8 -- UInt8.complement
  | lean_uint8_mod : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.mod
  | lean_bool_to_uint8 : UInt8BasicExtern [LeanPrimTy.bool] uint8 -- Bool.toUInt8
  | lean_uint8_xor : UInt8BasicExtern [uint8, uint8] uint8 -- UInt8.xor

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt16` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt16`. -/
inductive UInt16BasicExtern : List MyTy → MyTy → Type where
  | lean_uint16_neg : UInt16BasicExtern [uint16] uint16 -- UInt16.neg
  | lean_uint16_add : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.add
  | lean_uint16_lor : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.lor
  | lean_uint16_mul : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.mul
  | lean_uint16_land : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.land
  | lean_uint16_complement : UInt16BasicExtern [uint16] uint16 -- UInt16.complement
  | lean_uint16_xor : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.xor
  | lean_uint16_shift_left : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.shiftLeft
  | lean_uint16_mod : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.mod
  | lean_uint16_dec_lt : UInt16BasicExtern [uint16, uint16] LeanPrimTy.bool -- UInt16.decLt
  | lean_uint16_div : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.div
  | lean_uint16_dec_le : UInt16BasicExtern [uint16, uint16] LeanPrimTy.bool -- UInt16.decLe
  | lean_uint16_sub : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.sub
  | lean_bool_to_uint16 : UInt16BasicExtern [LeanPrimTy.bool] uint16 -- Bool.toUInt16
  | lean_uint16_shift_right : UInt16BasicExtern [uint16, uint16] uint16 -- UInt16.shiftRight

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt32` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt32`. -/
inductive UInt32BasicExtern : List MyTy → MyTy → Type where
  | lean_uint32_mod : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.mod
  | lean_bool_to_uint32 : UInt32BasicExtern [LeanPrimTy.bool] uint32 -- Bool.toUInt32
  | lean_uint32_div : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.div
  | lean_uint32_shift_right : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.shiftRight
  | lean_uint32_neg : UInt32BasicExtern [uint32] uint32 -- UInt32.neg
  | lean_uint32_lor : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.lor
  | lean_uint32_xor : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.xor
  | lean_uint32_shift_left : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.shiftLeft
  | lean_uint32_mul : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.mul
  | lean_uint32_land : UInt32BasicExtern [uint32, uint32] uint32 -- UInt32.land
  | lean_uint32_complement : UInt32BasicExtern [uint32] uint32 -- UInt32.complement

--------------------------------------------------
-- Init/Data/UInt/Basic.lean, the `UInt64` entries
--------------------------------------------------
/-- The pure externs of `Init/Data/UInt/Basic.lean`, on `UInt64`. -/
inductive UInt64BasicExtern : List MyTy → MyTy → Type where
  | lean_uint64_shift_left : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.shiftLeft
  -- | lean_usize_land : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.land
  -- | lean_usize_mul : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.mul
  -- | lean_uint16_to_usize : UInt16 → UInt64BasicExtern LeanPrimTy.usize -- UInt16.toUSize
  | lean_uint64_shift_right : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.shiftRight
  -- | lean_usize_shift_left : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.shiftLeft
  -- | lean_usize_xor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.xor
  | lean_uint64_complement : UInt64BasicExtern [uint64] uint64 -- UInt64.complement
  | lean_uint64_add : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.add
  | lean_uint64_lor : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.lor
  | lean_uint64_mod : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.mod
  -- | lean_usize_lor : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.lor
  -- | lean_usize_neg : denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.neg
  | lean_uint64_div : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.div
  -- | lean_usize_to_uint64 : denote LeanPrimTy.usize → UInt64BasicExtern uint64 -- USize.toUInt64
  | lean_uint64_mul : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.mul
  -- | lean_usize_shift_right : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.shiftRight
  | lean_uint64_land : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.land
  | lean_bool_to_uint64 : UInt64BasicExtern [LeanPrimTy.bool] uint64 -- Bool.toUInt64
  | lean_uint64_dec_le : UInt64BasicExtern [uint64, uint64] LeanPrimTy.bool -- UInt64.decLe
  -- | lean_usize_of_nat__USize_ofNat32 : (n : Nat) → (h : n < 4294967296) → UInt64BasicExtern LeanPrimTy.usize -- USize.ofNat32
  | lean_uint64_sub : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.sub
  | lean_uint64_neg : UInt64BasicExtern [uint64] uint64 -- UInt64.neg
  -- | lean_usize_div : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.div
  -- | lean_uint32_to_usize : UInt32 → UInt64BasicExtern LeanPrimTy.usize -- UInt32.toUSize
  -- | lean_usize_to_uint16 : denote LeanPrimTy.usize → UInt64BasicExtern uint16 -- USize.toUInt16
  -- | lean_usize_to_uint8 : denote LeanPrimTy.usize → UInt64BasicExtern uint8 -- USize.toUInt8
  -- | lean_usize_mod : denote LeanPrimTy.usize → denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.mod
  | lean_uint64_dec_lt : UInt64BasicExtern [uint64, uint64] LeanPrimTy.bool -- UInt64.decLt
  -- | lean_uint8_to_usize : UInt8 → UInt64BasicExtern LeanPrimTy.usize -- UInt8.toUSize
  -- | lean_bool_to_usize : Bool → UInt64BasicExtern LeanPrimTy.usize -- Bool.toUSize
  -- | lean_uint64_to_usize : UInt64 → UInt64BasicExtern LeanPrimTy.usize -- UInt64.toUSize
  -- | lean_usize_to_uint32 : denote LeanPrimTy.usize → UInt64BasicExtern uint32 -- USize.toUInt32
  -- | lean_usize_complement : denote LeanPrimTy.usize → UInt64BasicExtern LeanPrimTy.usize -- USize.complement
  | lean_uint64_xor : UInt64BasicExtern [uint64, uint64] uint64 -- UInt64.xor

------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int8` entries
------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int8`. -/
inductive Int8BasicExtern : List MyTy → MyTy → Type where
  | lean_int8_add : Int8BasicExtern [int8, int8] int8 -- Int8.add
  | lean_int8_div : Int8BasicExtern [int8, int8] int8 -- Int8.div
  | lean_int8_to_int16 : Int8BasicExtern [int8] int16 -- Int8.toInt16
  | lean_int8_shift_right : Int8BasicExtern [int8, int8] int8 -- Int8.shiftRight
  | lean_int8_mod : Int8BasicExtern [int8, int8] int8 -- Int8.mod
  | lean_bool_to_int8 : Int8BasicExtern [LeanPrimTy.bool] int8 -- Bool.toInt8
  | lean_int8_shift_left : Int8BasicExtern [int8, int8] int8 -- Int8.shiftLeft
  | lean_int8_xor : Int8BasicExtern [int8, int8] int8 -- Int8.xor
  | lean_int8_complement : Int8BasicExtern [int8] int8 -- Int8.complement
  | lean_int8_dec_eq : Int8BasicExtern [int8, int8] LeanPrimTy.bool -- Int8.decEq
  | lean_int8_neg : Int8BasicExtern [int8] int8 -- Int8.neg
  | lean_int8_dec_lt : Int8BasicExtern [int8, int8] LeanPrimTy.bool -- Int8.decLt
  | lean_int8_abs : Int8BasicExtern [int8] int8 -- Int8.abs
  | lean_int8_to_int32 : Int8BasicExtern [int8] int32 -- Int8.toInt32
  | lean_int8_sub : Int8BasicExtern [int8, int8] int8 -- Int8.sub
  | lean_int8_to_int64 : Int8BasicExtern [int8] int64 -- Int8.toInt64
  | lean_int8_of_nat : Int8BasicExtern [nat] int8 -- Int8.ofNat
  | lean_int8_dec_le : Int8BasicExtern [int8, int8] LeanPrimTy.bool -- Int8.decLe
  | lean_int8_to_int : Int8BasicExtern [int8] int -- Int8.toInt
  | lean_int8_mul : Int8BasicExtern [int8, int8] int8 -- Int8.mul
  | lean_int8_land : Int8BasicExtern [int8, int8] int8 -- Int8.land
  | lean_int8_of_int : Int8BasicExtern [int] int8 -- Int8.ofInt
  | lean_int8_lor : Int8BasicExtern [int8, int8] int8 -- Int8.lor

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int16` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int16`. -/
inductive Int16BasicExtern : List MyTy → MyTy → Type where
  | lean_int16_of_nat : Int16BasicExtern [nat] int16 -- Int16.ofNat
  | lean_int16_dec_le : Int16BasicExtern [int16, int16] LeanPrimTy.bool -- Int16.decLe
  | lean_int16_shift_right : Int16BasicExtern [int16, int16] int16 -- Int16.shiftRight
  | lean_int16_div : Int16BasicExtern [int16, int16] int16 -- Int16.div
  | lean_int16_dec_lt : Int16BasicExtern [int16, int16] LeanPrimTy.bool -- Int16.decLt
  | lean_int16_to_int : Int16BasicExtern [int16] int -- Int16.toInt
  | lean_int16_mod : Int16BasicExtern [int16, int16] int16 -- Int16.mod
  | lean_int16_dec_eq : Int16BasicExtern [int16, int16] LeanPrimTy.bool -- Int16.decEq
  | lean_bool_to_int16 : Int16BasicExtern [LeanPrimTy.bool] int16 -- Bool.toInt16
  | lean_int16_abs : Int16BasicExtern [int16] int16 -- Int16.abs
  | lean_int16_to_int32 : Int16BasicExtern [int16] int32 -- Int16.toInt32
  | lean_int16_complement : Int16BasicExtern [int16] int16 -- Int16.complement
  | lean_int16_land : Int16BasicExtern [int16, int16] int16 -- Int16.land
  | lean_int16_of_int : Int16BasicExtern [int] int16 -- Int16.ofInt
  | lean_int16_mul : Int16BasicExtern [int16, int16] int16 -- Int16.mul
  | lean_int16_shift_left : Int16BasicExtern [int16, int16] int16 -- Int16.shiftLeft
  | lean_int16_xor : Int16BasicExtern [int16, int16] int16 -- Int16.xor
  | lean_int16_lor : Int16BasicExtern [int16, int16] int16 -- Int16.lor
  | lean_int16_add : Int16BasicExtern [int16, int16] int16 -- Int16.add
  | lean_int16_to_int8 : Int16BasicExtern [int16] int8 -- Int16.toInt8
  | lean_int16_neg : Int16BasicExtern [int16] int16 -- Int16.neg
  | lean_int16_sub : Int16BasicExtern [int16, int16] int16 -- Int16.sub
  | lean_int16_to_int64 : Int16BasicExtern [int16] int64 -- Int16.toInt64

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int32` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int32`. -/
inductive Int32BasicExtern : List MyTy → MyTy → Type where
  | lean_int32_of_int : Int32BasicExtern [int] int32 -- Int32.ofInt
  | lean_int32_land : Int32BasicExtern [int32, int32] int32 -- Int32.land
  | lean_int32_mul : Int32BasicExtern [int32, int32] int32 -- Int32.mul
  | lean_int32_dec_le : Int32BasicExtern [int32, int32] LeanPrimTy.bool -- Int32.decLe
  | lean_int32_of_nat : Int32BasicExtern [nat] int32 -- Int32.ofNat
  | lean_int32_to_int64 : Int32BasicExtern [int32] int64 -- Int32.toInt64
  | lean_int32_sub : Int32BasicExtern [int32, int32] int32 -- Int32.sub
  | lean_int32_neg : Int32BasicExtern [int32] int32 -- Int32.neg
  | lean_int32_abs : Int32BasicExtern [int32] int32 -- Int32.abs
  | lean_int32_dec_eq : Int32BasicExtern [int32, int32] LeanPrimTy.bool -- Int32.decEq
  | lean_int32_dec_lt : Int32BasicExtern [int32, int32] LeanPrimTy.bool -- Int32.decLt
  | lean_int32_xor : Int32BasicExtern [int32, int32] int32 -- Int32.xor
  | lean_int32_shift_left : Int32BasicExtern [int32, int32] int32 -- Int32.shiftLeft
  | lean_int32_shift_right : Int32BasicExtern [int32, int32] int32 -- Int32.shiftRight
  | lean_int32_complement : Int32BasicExtern [int32] int32 -- Int32.complement
  | lean_bool_to_int32 : Int32BasicExtern [LeanPrimTy.bool] int32 -- Bool.toInt32
  | lean_int32_to_int8 : Int32BasicExtern [int32] int8 -- Int32.toInt8
  | lean_int32_add : Int32BasicExtern [int32, int32] int32 -- Int32.add
  | lean_int32_lor : Int32BasicExtern [int32, int32] int32 -- Int32.lor
  | lean_int32_mod : Int32BasicExtern [int32, int32] int32 -- Int32.mod
  | lean_int32_to_int : Int32BasicExtern [int32] int -- Int32.toInt
  | lean_int32_to_int16 : Int32BasicExtern [int32] int16 -- Int32.toInt16
  | lean_int32_div : Int32BasicExtern [int32, int32] int32 -- Int32.div

-------------------------------------------------
-- Init/Data/SInt/Basic.lean, the `Int64` entries
-------------------------------------------------
/-- The pure externs of `Init/Data/SInt/Basic.lean`, on `Int64`. -/
inductive Int64BasicExtern : List MyTy → MyTy → Type where
  -- | lean_isize_complement : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.complement
  -- | lean_int64_to_isize : Int64 → Int64BasicExtern LeanPrimTy.isize -- Int64.toISize
  | lean_int64_sub : Int64BasicExtern [int64, int64] int64 -- Int64.sub
  -- | lean_isize_to_int8 : denote LeanPrimTy.isize → Int64BasicExtern int8 -- ISize.toInt8
  | lean_int64_xor : Int64BasicExtern [int64, int64] int64 -- Int64.xor
  -- | lean_isize_xor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.xor
  | lean_int64_to_int8 : Int64BasicExtern [int64] int8 -- Int64.toInt8
  -- | lean_isize_shift_left : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.shiftLeft
  | lean_int64_mul : Int64BasicExtern [int64, int64] int64 -- Int64.mul
  | lean_int64_of_int : Int64BasicExtern [int] int64 -- Int64.ofInt
  -- | lean_int32_to_isize : Int32 → Int64BasicExtern LeanPrimTy.isize -- Int32.toISize
  | lean_int64_land : Int64BasicExtern [int64, int64] int64 -- Int64.land
  | lean_int64_lor : Int64BasicExtern [int64, int64] int64 -- Int64.lor
  -- | lean_isize_mod : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.mod
  -- | lean_isize_shift_right : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.shiftRight
  -- | lean_isize_to_int16 : denote LeanPrimTy.isize → Int64BasicExtern int16 -- ISize.toInt16
  -- | lean_isize_div : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.div
  -- | lean_isize_add : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.add
  -- | lean_isize_lor : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.lor
  | lean_int64_mod : Int64BasicExtern [int64, int64] int64 -- Int64.mod
  -- | lean_isize_of_int : Int → Int64BasicExtern LeanPrimTy.isize -- ISize.ofInt
  | lean_int64_shift_left : Int64BasicExtern [int64, int64] int64 -- Int64.shiftLeft
  -- | lean_isize_land : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.land
  -- | lean_isize_mul : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.mul
  -- | lean_isize_to_int : denote LeanPrimTy.isize → Int64BasicExtern int -- ISize.toInt
  | lean_int64_dec_lt : Int64BasicExtern [int64, int64] LeanPrimTy.bool -- Int64.decLt
  -- | lean_isize_dec_le : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decLe
  -- | lean_isize_of_nat : Nat → Int64BasicExtern LeanPrimTy.isize -- ISize.ofNat
  -- | lean_isize_to_int64 : denote LeanPrimTy.isize → Int64BasicExtern int64 -- ISize.toInt64
  -- | lean_isize_sub : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.sub
  | lean_int64_complement : Int64BasicExtern [int64] int64 -- Int64.complement
  -- | lean_isize_abs : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.abs
  -- | lean_isize_to_int32 : denote LeanPrimTy.isize → Int64BasicExtern int32 -- ISize.toInt32
  | lean_int64_to_int32 : Int64BasicExtern [int64] int32 -- Int64.toInt32
  | lean_int64_abs : Int64BasicExtern [int64] int64 -- Int64.abs
  | lean_bool_to_int64 : Int64BasicExtern [LeanPrimTy.bool] int64 -- Bool.toInt64
  -- | lean_bool_to_isize : Bool → Int64BasicExtern LeanPrimTy.isize -- Bool.toISize
  | lean_int64_dec_eq : Int64BasicExtern [int64, int64] LeanPrimTy.bool -- Int64.decEq
  | lean_int64_dec_le : Int64BasicExtern [int64, int64] LeanPrimTy.bool -- Int64.decLe
  | lean_int64_of_nat : Int64BasicExtern [nat] int64 -- Int64.ofNat
  | lean_int64_to_int_sint : Int64BasicExtern [int64] int -- Int64.toInt
  -- | lean_isize_dec_lt : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decLt
  | lean_int64_neg : Int64BasicExtern [int64] int64 -- Int64.neg
  -- | lean_isize_neg : denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.isize -- ISize.neg
  | lean_int64_add : Int64BasicExtern [int64, int64] int64 -- Int64.add
  | lean_int64_div : Int64BasicExtern [int64, int64] int64 -- Int64.div
  -- | lean_int8_to_isize : Int8 → Int64BasicExtern LeanPrimTy.isize -- Int8.toISize
  -- | lean_isize_dec_eq : denote LeanPrimTy.isize → denote LeanPrimTy.isize → Int64BasicExtern LeanPrimTy.bool -- ISize.decEq
  | lean_int64_to_int16 : Int64BasicExtern [int64] int16 -- Int64.toInt16
  -- | lean_int16_to_isize : Int16 → Int64BasicExtern LeanPrimTy.isize -- Int16.toISize
  | lean_int64_shift_right : Int64BasicExtern [int64, int64] int64 -- Int64.shiftRight

---------------------------
-- Init/Data/UInt/Log2.lean
---------------------------
/-- The pure externs of `Init/Data/UInt/Log2.lean`. -/
inductive UIntLog2Extern : List MyTy → MyTy → Type where
  -- | lean_usize_log2 : denote LeanPrimTy.usize → UIntLog2Extern LeanPrimTy.usize -- USize.log2
  | lean_uint16_log2 : UIntLog2Extern [uint16] uint16 -- UInt16.log2
  | lean_uint64_log2 : UIntLog2Extern [uint64] uint64 -- UInt64.log2
  | lean_uint8_log2 : UIntLog2Extern [uint8] uint8 -- UInt8.log2
  | lean_uint32_log2 : UIntLog2Extern [uint32] uint32 -- UInt32.log2

end LeanScript

end
