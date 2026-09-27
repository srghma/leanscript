module
prelude
public import LeanScript.Ty.LeanPrimTy
public import LeanScript.Ty.LeanPrimTyCovariant
public import LeanScript.LeanInitPureExterns.Core
public import LeanScript.LeanInitPureExterns.FixedWidth
public import LeanScript.LeanInitPureExterns.String
public import LeanScript.LeanInitPureExterns.Float
-- public import Init.Data.FloatArray.Basic
-- public import Init.System.IO
-- public import Init.System.Promise
-- public import Init.ShareCommon
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

-- `usize`/`isize` are `uint64`/`int64` in this grammar, so every entry that speaks about
-- one is already covered by the `UInt64`/`Int64` entries and is commented out below.
-- protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64
-- protected abbrev LeanPrimTy.isize : LeanPrimTy := int64
-- protected abbrev USize_size : Nat := UInt64.size
-- protected abbrev LeanPrimTy.byteArray : LeanPrimTyCovariant LeanPrimTy := Array UInt8 -- Though array doesnt have analogues to lean_byte_array_copy_slice, lean_byte_array_hash, lean_sarray_dec_eq, lean_string_validate_utf8, lean_string_from_utf8_unchecked, lean_string_to_utf8, lean_string_utf8_get_fast - we will support them differently
-- protected abbrev LeanPrimTy.floatArray : LeanPrimTyCovariant LeanPrimTy := Array Float

variable {MyTy : Type}
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  -- the run-time handles are not values, so nothing that speaks about one is listed
  -- (`IO.Promise`, `IO.Process.Child`, `ShareCommon.Object`, `ShareCommon.State`)
  -- (io_promise : MyTy → MyTy)
  -- (io_process_child : IO.Process.StdioConfig → MyTy)
  -- (shareCommon_object : MyTy)
  -- (shareCommon_stateFactory : Type)
  -- (shareCommon_state : shareCommon_stateFactory -> MyTy)
  -- a list is the covariant former `LeanPrimTyCovariant.list` (like `array`), and a
  -- `Lean.Name` is the leaf `LeanPrimTy.leanName`
  (ordering : MyTy)
  -- A byte array is `Array UInt8` and a float array is `Array Float`, so neither is a
  -- type former of its own here; the entries that speak about one are commented out
  -- below, and will be supported either through the ordinary array entries or through a
  -- separate API.
  -- (byteArray : MyTy)
  -- (floatArray : MyTy)

/-!
## The catalogue, in two levels

The catalogue records which functions of `Init` are pure externs, with their types over any
grammar of types `MyTy`, indexed by its signature (`LeanInitPureExtern σs τ`: the types of the
arguments, then the type of the result).  It is the language's one kind of extern:
`LeanScript.Neu.extern e args` (`LeanScript.Term.PExpr`) is the call of the entry `e`,
instantiated at the types of the language (`LeanScript.Extern`), on pure expressions `args` of
the types `σs`, and `LeanScript.Extern.eval` gives the meaning of each entry (the Lean function
named in its comment).  `#leanscript_to_term` translates a call of such a Lean function to the
call of its entry (`LeanScript.TermElab.ToTerm.ExternTable`).

The families are in four modules, by theme: `LeanScript.LeanInitPureExterns.Core`
(`Prelude`, `Core`, `Nat`, `Int`, `Array`, …), `.FixedWidth` (`UInt8` … `Int64`),
`.String` and `.Float`.  This module holds the sections of `Init` whose entries are all
commented out, and `LeanInitPureExtern` itself.

Each `-- Init/…` section of the catalogue is an inductive of its own (a *family*,
`PreludeExtern`, `StringBasicExtern`, …; the long `UInt`/`SInt` sections are split by
width), and `LeanInitPureExtern` has one constructor per family, holding an entry of it.
The constructors of the entries are the families' (`PreludeExtern.lean_nat_add`); the
module `LeanScript.LeanInitPureExternShorthands` derives for each one a shorthand
in `LeanInitPureExtern`'s own namespace (`LeanInitPureExtern.lean_nat_add a b` is
`.preludeExtern (.lean_nat_add a b)`), usable in patterns as well, so an entry is still written
`.lean_nat_add a b` wherever a `LeanInitPureExtern` is expected.

Two reasons for the split:
* the compiled runtime keeps a constructor's number in 8 bits, and only the numbers
  `0 … 243` are for ordinary constructors, so compiled code cannot build a constructor
  (with fields) numbered past `243`: with one inductive of 460 entries, a definition
  building one of the later ones did not compile ("tag too big");
* a `match` on an inductive is reduced through its recursor, which takes one minor
  premise per constructor, so every `match` over a 460-way inductive instantiates 460
  alternatives; a two-level `match` instantiates the families plus one family.

Every family is written against the same parameters as `LeanInitPureExtern`, but only
the ones its entries use are its own parameters (as for any inductive in a `variable`
context), so the constructor of `LeanInitPureExtern` applies each family to those:
when an entry that uses another parameter (`option`, say) is added to a family, add it
there too.
-/

----------------------
-- Init/Data/Repr.lean: every entry is commented out, so it has no family
----------------------
-- | lean_string_of_usize : denote LeanPrimTy.usize → LeanInitPureExtern string -- USize.repr

-------------------------
-- Init/Data/Nat/Gcd.lean: every entry is commented out, so it has no family
-------------------------
-- `Nat.gcd` is translated as an ordinary function (from its definition, as if it had no
-- `@[extern]`)
-- | lean_nat_gcd__Nat_gcd__unary : (_ : Nat) ×' Nat → LeanInitPureExtern nat -- Nat.gcd._unary
-- | lean_nat_gcd__Nat_gcd : Nat → Nat → LeanInitPureExtern nat -- Nat.gcd

---------------------------------
-- Init/Data/ByteArray/Basic.lean: every entry is commented out, so it has no family
---------------------------------
-- | lean_byte_array_copy_slice : ByteArray → Nat → ByteArray → Nat → Nat → (exact : Bool := true) → LeanInitPureExtern byteArray -- ByteArray.copySlice -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_hash : ByteArray → LeanInitPureExtern uint64 -- ByteArray.hash -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_size__ByteArray_usize : ByteArray → LeanInitPureExtern LeanPrimTy.usize -- ByteArray.usize
-- | lean_sarray_dec_eq__ByteArray_beq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.beq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_dec_eq__ByteArray_decEq : ByteArray → ByteArray → LeanInitPureExtern LeanPrimTy.bool -- ByteArray.decEq -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_set : ByteArray → Nat → UInt8 → LeanInitPureExtern byteArray -- ByteArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_fget : (a : ByteArray) → (i : Nat) → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_uset : (a : ByteArray) → (i : USize) → UInt8 → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_fset : (a : ByteArray) → (i : Nat) → UInt8 → (h : i < a.size := by get_elem_tactic) → LeanInitPureExtern byteArray -- ByteArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_uget : (a : ByteArray) → (i : USize) → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern uint8 -- ByteArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_byte_array_get : ByteArray → Nat → LeanInitPureExtern uint8 -- ByteArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)

----------------------------------
-- Init/Data/FloatArray/Basic.lean: every entry is commented out, so it has no family
----------------------------------
-- | lean_mk_empty_float_array : Nat → LeanInitPureExtern floatArray -- FloatArray.emptyWithCapacity -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_get : FloatArray → Nat → LeanInitPureExtern float -- FloatArray.get! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_uget : (a : FloatArray) → (i : USize) → (h : i.toNat < a.size) → LeanInitPureExtern float -- FloatArray.uget -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_fset : (ds : FloatArray) → (i : Nat) → Float → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.set -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_uset : (a : FloatArray) → (i : USize) → Float → (h : i.toNat < a.size := by get_elem_tactic) → LeanInitPureExtern floatArray -- FloatArray.uset -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_fget : (ds : FloatArray) → (i : Nat) → (h : i < ds.size := by get_elem_tactic) → LeanInitPureExtern float -- FloatArray.get -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_set : FloatArray → Nat → Float → LeanInitPureExtern floatArray -- FloatArray.set! -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_data : FloatArray → LeanInitPureExtern (array float) -- FloatArray.data -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_sarray_size__FloatArray_usize : FloatArray → LeanInitPureExtern LeanPrimTy.usize -- FloatArray.usize
-- | lean_float_array_mk : Array Float → LeanInitPureExtern floatArray -- FloatArray.mk -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_size : FloatArray → LeanInitPureExtern nat -- FloatArray.size -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)
-- | lean_float_array_push : FloatArray → Float → LeanInitPureExtern floatArray -- FloatArray.push -- (byte/float arrays: supported through the ordinary array entries, or through a separate API, later)

----------------------
-- Init/System/IO.lean: every entry is commented out, so it has no family
----------------------
-- | lean_io_process_child_pid : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitPureExtern uint32 -- IO.Process.Child.pid

---------------------------
-- Init/System/Promise.lean: every entry is commented out, so it has no family
---------------------------
-- | lean_io_promise_result_opt : (αt : MyTy) → denote (io_promise αt) → LeanInitPureExtern (task (option αt)) -- IO.Promise.result?
-- | lean_option_get_or_block : (αt : MyTy) → Option (denote αt) → LeanInitPureExtern αt -- _private.Init.System.Promise.0.IO.Option.getOrBlock!

------------------------
-- Init/ShareCommon.lean: every entry is commented out, so it has no family
------------------------
-- | lean_sharecommon_quick : (αt : MyTy) → denote αt → LeanInitPureExtern αt -- ShareCommon.shareCommon'
-- | lean_state_sharecommon : (αt : MyTy) → {σ : shareCommon_stateFactory} → denote (shareCommon_state σ) → denote αt → LeanInitPureExtern (prod αt (shareCommon_state σ)) -- ShareCommon.State.shareCommon
-- | lean_sharecommon_eq : denote shareCommon_object → denote shareCommon_object → LeanInitPureExtern LeanPrimTy.bool -- ShareCommon.Object.eq
-- | lean_sharecommon_hash : denote shareCommon_object → LeanInitPureExtern uint64 -- ShareCommon.Object.hash

/-- A pure extern of `Init`, of signature `σs → τ`: an entry of one of the families above.
    An entry holds no value: its arguments (the types `σs`, in order) are given where it is
    called (`LeanScript.Neu.extern e args`, on pure expressions), so creating a value with an
    extern and computing with one are the same thing, a call.  The fields an entry does have
    are the type arguments of its Lean function (`αt` of `lean_array_push αt`) and, rarely, a
    literal that fixes a proposition of the function (`lean_float_of_scientific`); the proofs
    the Lean function takes are dropped (the meaning of the entry decides them).

    **No `DecidableEq`/`BEq`.**  The fields are types of the grammar and literals, so nothing
    in them prevents it, but the indices of an entry are computed through the abstract
    coercions and type formers above, so `deriving DecidableEq` cannot unify the indices of
    two entries. -/
inductive LeanInitPureExtern : List MyTy → MyTy → Type where
  /-- An entry of `PreludeExtern` (`Init/Prelude.lean`). -/
  | preludeExtern {σs : List MyTy} {τ : MyTy} : PreludeExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `CoreExtern` (`Init/Core.lean`). -/
  | coreExtern {σs : List MyTy} {τ : MyTy} : CoreExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `IntBasicExtern` (`Init/Data/Int/Basic.lean`). -/
  | intBasicExtern {σs : List MyTy} {τ : MyTy} : IntBasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `NatDivExtern` (`Init/Data/Nat/Div/Basic.lean`). -/
  | natDivExtern {σs : List MyTy} {τ : MyTy} : NatDivExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `NatBitwiseExtern` (`Init/Data/Nat/Bitwise/Basic.lean`). -/
  | natBitwiseExtern {σs : List MyTy} {τ : MyTy} : NatBitwiseExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UIntBasicAuxExtern` (`Init/Data/UInt/BasicAux.lean`). -/
  | uintBasicAuxExtern {σs : List MyTy} {τ : MyTy} : UIntBasicAuxExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringBootstrapExtern` (`Init/Data/String/Bootstrap.lean`). -/
  | stringBootstrapExtern {σs : List MyTy} {τ : MyTy} : StringBootstrapExtern fn1 fn2 σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UtilExtern` (`Init/Util.lean`). -/
  | utilExtern {σs : List MyTy} {τ : MyTy} : UtilExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `ArraySetExtern` (`Init/Data/Array/Set.lean`). -/
  | arraySetExtern {σs : List MyTy} {τ : MyTy} : ArraySetExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `ArrayBasicExtern` (`Init/Data/Array/Basic.lean`). -/
  | arrayBasicExtern {σs : List MyTy} {τ : MyTy} : ArrayBasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `MetaDefsExtern` (`Init/Meta/Defs.lean`). -/
  | metaDefsExtern {σs : List MyTy} {τ : MyTy} : MetaDefsExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `NatLog2Extern` (`Init/Data/Nat/Log2.lean`). -/
  | natLog2Extern {σs : List MyTy} {τ : MyTy} : NatLog2Extern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `IntDivModExtern` (`Init/Data/Int/DivMod/Basic.lean`). -/
  | intDivModExtern {σs : List MyTy} {τ : MyTy} : IntDivModExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UInt8BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt8` entries). -/
  | uint8BasicExtern {σs : List MyTy} {τ : MyTy} : UInt8BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UInt16BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt16` entries). -/
  | uint16BasicExtern {σs : List MyTy} {τ : MyTy} : UInt16BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UInt32BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt32` entries). -/
  | uint32BasicExtern {σs : List MyTy} {τ : MyTy} : UInt32BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UInt64BasicExtern` (`Init/Data/UInt/Basic.lean`, the `UInt64` entries). -/
  | uint64BasicExtern {σs : List MyTy} {τ : MyTy} : UInt64BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringPosRawExtern` (`Init/Data/String/PosRaw.lean`). -/
  | stringPosRawExtern {σs : List MyTy} {τ : MyTy} : StringPosRawExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringDefsExtern` (`Init/Data/String/Defs.lean`). -/
  | stringDefsExtern {σs : List MyTy} {τ : MyTy} : StringDefsExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `PlatformExtern` (`Init/System/Platform.lean`). -/
  | platformExtern {σs : List MyTy} {τ : MyTy} : PlatformExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringBasicExtern` (`Init/Data/String/Basic.lean`). -/
  | stringBasicExtern {σs : List MyTy} {τ : MyTy} : StringBasicExtern option σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringLengthExtern` (`Init/Data/String/Length.lean`). -/
  | stringLengthExtern {σs : List MyTy} {τ : MyTy} : StringLengthExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `Int8BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int8` entries). -/
  | int8BasicExtern {σs : List MyTy} {τ : MyTy} : Int8BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `Int16BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int16` entries). -/
  | int16BasicExtern {σs : List MyTy} {τ : MyTy} : Int16BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `Int32BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int32` entries). -/
  | int32BasicExtern {σs : List MyTy} {τ : MyTy} : Int32BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `Int64BasicExtern` (`Init/Data/SInt/Basic.lean`, the `Int64` entries). -/
  | int64BasicExtern {σs : List MyTy} {τ : MyTy} : Int64BasicExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringPatternExtern` (`Init/Data/String/Pattern/Basic.lean`). -/
  | stringPatternExtern {σs : List MyTy} {τ : MyTy} : StringPatternExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringSliceExtern` (`Init/Data/String/Slice.lean`). -/
  | stringSliceExtern {σs : List MyTy} {τ : MyTy} : StringSliceExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `StringModifyExtern` (`Init/Data/String/Modify.lean`). -/
  | stringModifyExtern {σs : List MyTy} {τ : MyTy} : StringModifyExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `FloatExtern` (`Init/Data/Float/Float.lean`). -/
  | floatExtern {σs : List MyTy} {τ : MyTy} : FloatExtern prod σs τ → LeanInitPureExtern σs τ
  /-- An entry of `UIntLog2Extern` (`Init/Data/UInt/Log2.lean`). -/
  | uintLog2Extern {σs : List MyTy} {τ : MyTy} : UIntLog2Extern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `SIntFloatExtern` (`Init/Data/SInt/Float.lean`). -/
  | sIntFloatExtern {σs : List MyTy} {τ : MyTy} : SIntFloatExtern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `Float32Extern` (`Init/Data/Float/Float32.lean`). -/
  | float32Extern {σs : List MyTy} {τ : MyTy} : Float32Extern prod σs τ → LeanInitPureExtern σs τ
  /-- An entry of `SIntFloat32Extern` (`Init/Data/SInt/Float32.lean`). -/
  | sIntFloat32Extern {σs : List MyTy} {τ : MyTy} : SIntFloat32Extern σs τ → LeanInitPureExtern σs τ
  /-- An entry of `OrdStringExtern` (`Init/Data/Ord/String.lean`). -/
  | ordStringExtern {σs : List MyTy} {τ : MyTy} : OrdStringExtern ordering σs τ → LeanInitPureExtern σs τ

end LeanScript

end
