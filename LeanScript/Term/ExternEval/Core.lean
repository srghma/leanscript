module

public import LeanScript.Term.Extern

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the core of `Init` (`Prelude`, `Core`, `Nat`, `Int`, `Array`, `Util`, `Meta`, `Platform`)

The value of every entry of the families of `LeanScript.LeanInitPureExterns.Core`, at the
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

/-- The value of an entry of `PreludeExtern` on the values of its arguments. -/
def PreludeExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    PreludeExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_uint32_of_nat_mk, x1 =>
    let x1 : BitVec 32 := x1
    (UInt32.ofBitVec x1 : UInt32)
  | _, _, .lean_uint32_dec_eq, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    ExternBool.toBool (UInt32.decEq x1 x2)
  | _, _, .lean_uint32_dec_lt, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    ExternBool.toBool (UInt32.decLt x1 x2)
  | _, _, .lean_nat_div, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.div x1 x2 : Nat)
  | _, _, .lean_uint32_of_nat__UInt32_ofNatLT, n =>
    let n : Nat := n
    if h : n < UInt32.size then (UInt32.ofNatLT n h : UInt32) else (default : UInt32)
  | _, _, .lean_uint32_of_nat__Char_ofNatAux, n =>
    let n : Nat := n
    if h : n.isValidChar then (Char.ofNatAux n h : Char) else (default : Char)
  | _, _, (.lean_array_get_borrowed αt), (inhabited_default, x2, x3) =>
    let inhabited_default : Ty.den E αt := inhabited_default
    let x2 : Array (Ty.den E αt) := x2
    let x3 : Nat := x3
    (@Array.get!Internal _ ⟨inhabited_default⟩ x2 x3 : Ty.den E αt) -- `Array.get!InternalBorrowed` is `unsafe`: the same function, borrowing its array
  | _, _, .lean_uint8_to_nat__UInt8_toBitVec, x1 =>
    let x1 : UInt8 := x1
    (UInt8.toBitVec x1 : BitVec 8)
  | _, _, .lean_nat_dec_lt, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    ExternBool.toBool (Nat.decLt x1 x2)
  | _, _, .lean_nat_mod__Nat_modCore, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.mod x1 x2 : Nat) -- `Nat.modCore` has no compiled code; `Nat.mod` is the same function
  | _, _, .lean_nat_mod__Nat_mod, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.mod x1 x2 : Nat)
  | _, _, (.lean_array_push αt), (x1, x2) =>
    let x1 : Array (Ty.den E αt) := x1
    let x2 : Ty.den E αt := x2
    (Array.push x1 x2 : Array (Ty.den E αt))
  | _, _, .lean_nat_sub, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.sub x1 x2 : Nat)
  | _, _, .lean_uint8_dec_lt, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    ExternBool.toBool (UInt8.decLt x1 x2)
  | _, _, .lean_uint32_dec_le, (x1, x2) =>
    let x1 : UInt32 := x1
    let x2 : UInt32 := x2
    ExternBool.toBool (UInt32.decLe x1 x2)
  | _, _, (.lean_array_get_size αt), x1 =>
    let x1 : Array (Ty.den E αt) := x1
    (Array.size x1 : Nat)
  | _, _, .lean_nat_dec_eq__Nat_decEq, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    ExternBool.toBool (Nat.decEq x1 x2)
  | _, _, .lean_nat_dec_eq__Nat_beq, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    ExternBool.toBool (Nat.beq x1 x2)
  | _, _, (.lean_mk_empty_array_with_capacity__Array_emptyWithCapacity αt), x1 =>
    let x1 : Nat := x1
    (Array.emptyWithCapacity x1 : Array (Ty.den E αt))
  | _, _, (.lean_mk_empty_array_with_capacity__Array_mkEmpty αt), x1 =>
    let x1 : Nat := x1
    (Array.mkEmpty x1 : Array (Ty.den E αt))
  | _, _, .lean_uint8_of_nat__UInt8_ofNat, x1 =>
    let x1 : Nat := x1
    (UInt8.ofNat x1 : UInt8)
  | _, _, .lean_uint8_of_nat__UInt8_ofNatLT, n =>
    let n : Nat := n
    if h : n < UInt8.size then (UInt8.ofNatLT n h : UInt8) else (default : UInt8)
  | _, _, .lean_uint8_dec_le, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    ExternBool.toBool (UInt8.decLe x1 x2)
  | _, _, .lean_nat_dec_le__Nat_ble, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    ExternBool.toBool (Nat.ble x1 x2)
  | _, _, .lean_nat_dec_le__Nat_decLe, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    ExternBool.toBool (Nat.decLe x1 x2)
  | _, _, (.lean_array_get αt), (inhabited_default, x2, x3) =>
    let inhabited_default : Ty.den E αt := inhabited_default
    let x2 : Array (Ty.den E αt) := x2
    let x3 : Nat := x3
    (@Array.get!Internal _ ⟨inhabited_default⟩ x2 x3 : Ty.den E αt)
  | _, _, .lean_nat_add, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.add x1 x2 : Nat)
  | _, _, .lean_uint16_to_nat__UInt16_toBitVec, x1 =>
    let x1 : UInt16 := x1
    (UInt16.toBitVec x1 : BitVec 16)
  | _, _, .lean_uint16_of_nat_mk, x1 =>
    let x1 : BitVec 16 := x1
    (UInt16.ofBitVec x1 : UInt16)
  | _, _, .lean_uint16_dec_eq, (x1, x2) =>
    let x1 : UInt16 := x1
    let x2 : UInt16 := x2
    ExternBool.toBool (UInt16.decEq x1 x2)
  | _, _, .lean_string_dec_eq, (x1, x2) =>
    let x1 : String := x1
    let x2 : String := x2
    ExternBool.toBool (String.decEq x1 x2)
  | _, _, .lean_nat_pred, x1 =>
    let x1 : Nat := x1
    (Nat.pred x1 : Nat)
  | _, _, .lean_string_hash, x1 =>
    let x1 : String := x1
    (String.hash x1 : UInt64)
  | _, _, .lean_uint64_to_nat__UInt64_toBitVec, x1 =>
    let x1 : UInt64 := x1
    (UInt64.toBitVec x1 : BitVec 64)
  | _, _, .lean_uint64_of_nat_mk, x1 =>
    let x1 : BitVec 64 := x1
    (UInt64.ofBitVec x1 : UInt64)
  | _, _, .lean_uint32_to_nat__UInt32_toNat, x1 =>
    let x1 : UInt32 := x1
    (UInt32.toNat x1 : Nat)
  | _, _, .lean_uint32_to_nat__UInt32_toBitVec, x1 =>
    let x1 : UInt32 := x1
    (UInt32.toBitVec x1 : BitVec 32)
  | _, _, .lean_uint64_dec_eq, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    ExternBool.toBool (UInt64.decEq x1 x2)
  | _, _, .lean_uint16_of_nat__UInt16_ofNatLT, n =>
    let n : Nat := n
    if h : n < UInt16.size then (UInt16.ofNatLT n h : UInt16) else (default : UInt16)
  | _, _, .lean_uint8_of_nat_mk, x1 =>
    let x1 : BitVec 8 := x1
    (UInt8.ofBitVec x1 : UInt8)
  | _, _, .lean_uint8_dec_eq, (x1, x2) =>
    let x1 : UInt8 := x1
    let x2 : UInt8 := x2
    ExternBool.toBool (UInt8.decEq x1 x2)
  | _, _, .lean_nat_pow, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.pow x1 x2 : Nat)
  | _, _, .lean_nat_mul, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.mul x1 x2 : Nat)
  | _, _, .lean_string_utf8_byte_size, x1 =>
    let x1 : String := x1
    (String.utf8ByteSize x1 : Nat)
  | _, _, .lean_uint64_mix_hash, (x1, x2) =>
    let x1 : UInt64 := x1
    let x2 : UInt64 := x2
    (mixHash x1 x2 : UInt64)
  | _, _, .lean_uint64_of_nat__UInt64_ofNatLT, n =>
    let n : Nat := n
    if h : n < UInt64.size then (UInt64.ofNatLT n h : UInt64) else (default : UInt64)

/-- The value of an entry of `CoreExtern` on the values of its arguments. -/
def CoreExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    CoreExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_strict_or, (x1, x2) =>
    let x1 : Bool := x1
    let x2 : Bool := x2
    ExternBool.toBool (strictOr x1 x2)
  | _, _, (.lean_thunk_pure αt), x =>
    Ty.ofRelax E _ (Ty.toStrictOf E αt x)
  | _, _, (.lean_mk_thunk _), x =>
    x
  | _, _, (.lean_thunk_get_own αt), x =>
    Ty.ofStrictOf E αt (Ty.toRelax E _ x)
  | _, _, .lean_strict_and, (x1, x2) =>
    let x1 : Bool := x1
    let x2 : Bool := x2
    ExternBool.toBool (strictAnd x1 x2)

/-- The value of an entry of `IntBasicExtern` on the values of its arguments. -/
def IntBasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    IntBasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_nat_to_int, x1 =>
    let x1 : Nat := x1
    (Int.ofNat x1 : Int)
  | _, _, .lean_int_dec_le, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    ExternBool.toBool (Int.decLe x1 x2)
  | _, _, .lean_int_dec_lt, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    ExternBool.toBool (Int.decLt x1 x2)
  | _, _, .lean_int_dec_eq, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    ExternBool.toBool (Int.decEq x1 x2)
  | _, _, .lean_int_mul, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.mul x1 x2 : Int)
  | _, _, .lean_int_dec_nonneg, x1 =>
    let x1 : Int := x1
    ExternBool.toBool (Int.decNonneg x1)
  | _, _, .lean_int_neg_succ_of_nat, x1 =>
    let x1 : Nat := x1
    (Int.negSucc x1 : Int)
  | _, _, .lean_int_add, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.add x1 x2 : Int)
  | _, _, .lean_int_neg, x1 =>
    let x1 : Int := x1
    (Int.neg x1 : Int)
  | _, _, .lean_int_sub, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.sub x1 x2 : Int)
  | _, _, .lean_nat_abs, x1 =>
    let x1 : Int := x1
    (Int.natAbs x1 : Nat)

/-- The value of an entry of `NatDivExtern` on the values of its arguments. -/
def NatDivExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    NatDivExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_nat_div_exact, (x, y) =>
    let x : Nat := x
    let y : Nat := y
    if h : y ∣ x then (Nat.divExact x y h : Nat) else (default : Nat)

/-- The value of an entry of `NatBitwiseExtern` on the values of its arguments. -/
def NatBitwiseExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    NatBitwiseExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_nat_lxor, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.xor x1 x2 : Nat)
  | _, _, .lean_nat_shiftl, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.shiftLeft x1 x2 : Nat)
  | _, _, .lean_nat_shiftr, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.shiftRight x1 x2 : Nat)
  | _, _, .lean_nat_land, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.land x1 x2 : Nat)
  | _, _, .lean_nat_lor, (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Nat := x2
    (Nat.lor x1 x2 : Nat)

/-- The value of an entry of `UtilExtern` on the values of its arguments. -/
def UtilExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    UtilExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, (.lean_dbg_trace_if_shared αt), (x1, x2) =>
    let x1 : String := x1
    let x2 : Ty.den E αt := x2
    (dbgTraceIfShared x1 x2 : Ty.den E αt)

/-- The value of an entry of `ArraySetExtern` on the values of its arguments. -/
def ArraySetExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    ArraySetExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, (.lean_array_set αt), (x1, x2, x3) =>
    let x1 : Array (Ty.den E αt) := x1
    let x2 : Nat := x2
    let x3 : Ty.den E αt := x3
    (Array.set! x1 x2 x3 : Array (Ty.den E αt))
  | _, _, (.lean_array_fset αt), (xs, i, x3) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    let x3 : Ty.den E αt := x3
    if h : i < xs.size then (Array.set xs i x3 h : Array (Ty.den E αt)) else xs

/-- The value of an entry of `ArrayBasicExtern` on the values of its arguments. -/
def ArrayBasicExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    ArrayBasicExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, (.lean_array_fswap αt), (xs, i, j) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    let j : Nat := j
    if h : i < xs.size then if h1 : j < xs.size then (Array.swap xs i j h h1 : Array (Ty.den E αt)) else xs else xs
  | _, _, (.lean_mk_array αt), (x1, x2) =>
    let x1 : Nat := x1
    let x2 : Ty.den E αt := x2
    (Array.replicate x1 x2 : Array (Ty.den E αt))
  | _, _, (.lean_array_swap αt), (x1, x2, x3) =>
    let x1 : Array (Ty.den E αt) := x1
    let x2 : Nat := x2
    let x3 : Nat := x3
    (Array.swapIfInBounds x1 x2 x3 : Array (Ty.den E αt))
  | _, _, (.lean_array_pop αt), x1 =>
    let x1 : Array (Ty.den E αt) := x1
    (Array.pop x1 : Array (Ty.den E αt))

/-- The value of an entry of `MetaDefsExtern` on the values of its arguments. -/
def MetaDefsExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    MetaDefsExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_version_get_special_desc, _ =>
    (Lean.version.getSpecialDesc () : String)
  | _, _, .lean_version_get_is_release, _ =>
    ExternBool.toBool (Lean.version.getIsRelease ())
  | _, _, .lean_version_get_major, _ =>
    (Lean.version.major : Nat)
  | _, _, .lean_version_get_patch, _ =>
    (Lean.version.patch : Nat)
  | _, _, .lean_internal_is_stage0, _ =>
    ExternBool.toBool (Lean.Internal.isStage0 ())
  | _, _, .lean_version_get_minor, _ =>
    (Lean.version.minor : Nat)
  | _, _, .lean_get_githash, _ =>
    (Lean.getGithash () : String)
  | _, _, .lean_internal_has_llvm_backend, _ =>
    ExternBool.toBool (Lean.Internal.hasLLVMBackend ())

/-- The value of an entry of `NatLog2Extern` on the values of its arguments. -/
def NatLog2Extern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    NatLog2Extern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_nat_log2, x1 =>
    let x1 : Nat := x1
    (Nat.log2 x1 : Nat)

/-- The value of an entry of `IntDivModExtern` on the values of its arguments. -/
def IntDivModExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    IntDivModExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_int_emod, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.emod x1 x2 : Int)
  | _, _, .lean_int_div_exact, (x, y) =>
    let x : Int := x
    let y : Int := y
    if h : y ∣ x then (Int.divExact x y h : Int) else (default : Int)
  | _, _, .lean_int_mod, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.tmod x1 x2 : Int)
  | _, _, .lean_int_ediv, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.ediv x1 x2 : Int)
  | _, _, .lean_int_div, (x1, x2) =>
    let x1 : Int := x1
    let x2 : Int := x2
    (Int.tdiv x1 x2 : Int)

/-- The value of an entry of `PlatformExtern` on the values of its arguments. -/
def PlatformExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    PlatformExtern (MyTy := Ty ks) σs τ → DenList E σs → Ty.den E τ
  | _, _, .lean_system_platform_emscripten, _ =>
    ExternBool.toBool (System.Platform.getIsEmscripten ())
  | _, _, .lean_system_platform_target, _ =>
    (System.Platform.getTarget () : String)

end LeanScript

end
