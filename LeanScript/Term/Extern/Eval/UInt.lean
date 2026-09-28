module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the unsigned fixed-width integers (`UInt8` … `UInt64`)

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
