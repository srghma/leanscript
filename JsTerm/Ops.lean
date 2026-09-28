module

public import JsTerm.Ty
public import LeanScript.Term.Extern.NameElab

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm`

**Generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`) and `runtime.js`; do not edit.

Every extern of the catalogue is split by the JavaScript representation of its arguments and
its result (`lean_nat_div : [nat, nat] → nat` is `bigint_nat__lean_nat_div : [bigint_nat,
bigint_nat] → bigint_nat` and `uint53__lean_nat_div : [uint53, uint53] → uint53`).  An
operation is either

* **imported** (`JsOpImported`): a call of the function of `runtime.js` named as its
  constructor (`JsOpImported.runtimeName`, read off the constructors by `ctor_names%`), which
  the generated module imports; or
* **inlined** (`JsOpInlinable`): written in place of its call as a JavaScript operator,
  conversion or literal over its arguments (`JsOpInlinable.template`).

The name of an operation is its *type prefix* and the name of the extern, joined by `__`: the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` for `n > 53`) in order of first appearance and without repetitions, or,
when there is none, the first leaf of the signature (`uint32__lean_uint32_add`), or the family
of a polymorphic operation (`array__lean_array_push_immutable`, `thunk__lean_mk_thunk`).  A
polymorphic array operation works on every layout of an array (`JsArrayLayout`: a generic
array or a typed array).

Both families are indexed by what an operation may do besides answering (`Effectfulness`,
`MayThrow`), by the types of its arguments and by the type of its result:

* an operation is **effectful** when it changes something outside of it: the `_mutable` array
  updates, which update their array argument in place (the backend calls them only on an array
  nothing else refers to), are the only ones; every other operation is **pure**;
* an operation **may throw** when its function in `runtime.js` may (a `throw`, directly or in a
  function it calls): the operations on a `number` representation of an unbounded type, which
  throw a `RangeError` when the result does not fit in a safe integer (so that no result is
  ever silently wrong).  The inlined operations never throw.

The array updates come in two versions: `…_immutable` (the extern: a copy of the array) and
`…_mutable` (the same update in place); `JsOpImported.toMutable?` pairs them.  An extern whose
function in `runtime.js` is an alias of another at the same signature (`lean_array_fset` of
`lean_array_set`) has that operation.
-/

namespace MoreJs

/-- Whether an operation changes something outside of it. -/
inductive Effectfulness where
  /-- It only computes its result. -/
  | pure
  /-- It changes something outside of it (it updates an argument in place). -/
  | effectful
  deriving DecidableEq, Repr, Inhabited

/-- Whether an operation may throw. -/
inductive MayThrow where
  /-- It never throws. -/
  | doesntThrow
  /-- It may throw (a `RangeError` when a result does not fit in its representation). -/
  | mayThrow
  deriving DecidableEq, Repr, Inhabited

/-- How an inlined operation is written in JavaScript, over its arguments. -/
inductive JsInline where
  /-- The argument of position `i` (from `0`). -/
  | arg (i : Nat)
  /-- `a op b`, for the JavaScript binary operator `op` (`+`, `&`, `===`, …). -/
  | bin (op : String) (a b : JsInline)
  /-- `op a`, for the JavaScript prefix operator `op` (`-`, `~`, `!`). -/
  | un (op : String) (a : JsInline)
  /-- `f(args)`, `f` a global function (`BigInt`, `Number`, `Math.sin`, `Uint8Array.from`). -/
  | call (f : String) (args : List JsInline)
  /-- `new C(args)`. -/
  | new (ctor : String) (args : List JsInline)
  /-- An integer `number` literal. -/
  | num (n : Int)
  /-- A `BigInt` literal. -/
  | big (n : Int)
  /-- `[]`. -/
  | emptyArray
  /-- `a.field` (`a.length`). -/
  | member (a : JsInline) (field : String)
  deriving Inhabited, Repr

/-- The name of a function of `runtime.js` for the name of an operation: the characters a
    JavaScript identifier cannot have are written `$` and their code in hexadecimal (`get?` is
    `get$3F`, `get!` is `get$21`, `next'` is `next$27`). -/
def jsSafeName (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '?' => acc ++ "$3F"
    | '!' => acc ++ "$21"
    | '\'' => acc ++ "$27"
    | c => acc.push c) ""

/-- The operations implemented by the function of `runtime.js` named as the constructor,
    indexed by their effects, the types of their arguments and the type of their result. -/
inductive JsOpImported : Effectfulness → MayThrow → List JsTy → JsTy → Type where
  /-- Array.push -/
  | array__lean_array_push_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A, E] A
  /-- Array.toList -/
  | typedArray__lean_array_to_list : (t : JsTypedElem) → JsOpImported .pure .doesntThrow [(.typedArray t)] (.list (.terminal t.leaf))
  /-- Array.get!Internal -/
  | bigint_nat__lean_array_get : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [E, A, (.terminal .bigint_nat)] E
  /-- Array.get!Internal -/
  | uint53__lean_array_get : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [E, A, (.terminal .uint53)] E
  /-- Thunk.pure -/
  | thunk__lean_thunk_pure : (α : JsTy) → JsOpImported .pure .doesntThrow [α] (.thunk α)
  /-- Thunk.mk -/
  | thunk__lean_mk_thunk : (α : JsTy) → JsOpImported .pure .doesntThrow [(.fn [] α)] (.thunk α)
  /-- Thunk.get -/
  | thunk__lean_thunk_get_own : (α : JsTy) → JsOpImported .pure .doesntThrow [(.thunk α)] α
  /-- dbgTraceIfShared -/
  | string__lean_dbg_trace_if_shared : (α : JsTy) → JsOpImported .pure .doesntThrow [(.terminal .string), α] α
  /-- Array.set! -/
  | bigint_nat__lean_array_set_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A, (.terminal .bigint_nat), E] A
  /-- Array.set! -/
  | uint53__lean_array_set_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A, (.terminal .uint53), E] A
  /-- Array.replicate -/
  | bigint_nat__lean_mk_array : (α : JsTy) → JsOpImported .pure .mayThrow [(.terminal .bigint_nat), α] (.array α)
  /-- Array.replicate -/
  | typedArray__bigint_nat__lean_mk_array : (t : JsTypedElem) → JsOpImported .pure .mayThrow [(.terminal .bigint_nat), (.terminal t.leaf)] (.typedArray t)
  /-- Array.replicate -/
  | uint53__lean_mk_array : (α : JsTy) → JsOpImported .pure .doesntThrow [(.terminal .uint53), α] (.array α)
  /-- Array.replicate -/
  | typedArray__uint53__lean_mk_array : (t : JsTypedElem) → JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal t.leaf)] (.typedArray t)
  /-- Array.swapIfInBounds -/
  | bigint_nat__lean_array_swap_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A, (.terminal .bigint_nat), (.terminal .bigint_nat)] A
  /-- Array.swapIfInBounds -/
  | uint53__lean_array_swap_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A, (.terminal .uint53), (.terminal .uint53)] A
  /-- Array.pop -/
  | array__lean_array_pop_immutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .pure .doesntThrow [A] A
  /-- `array__lean_array_push_immutable`, updating the array in place (Array.push) -/
  | array__lean_array_push_mutable : (α : JsTy) → JsOpImported .effectful .doesntThrow [(.array α), α] (.array α)
  /-- `array__lean_array_pop_immutable`, updating the array in place (Array.pop) -/
  | array__lean_array_pop_mutable : (α : JsTy) → JsOpImported .effectful .doesntThrow [(.array α)] (.array α)
  /-- `bigint_nat__lean_array_set_immutable`, updating the array in place (Array.set!) -/
  | bigint_nat__lean_array_set_mutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .effectful .doesntThrow [A, (.terminal .bigint_nat), E] A
  /-- `uint53__lean_array_set_immutable`, updating the array in place (Array.set!) -/
  | uint53__lean_array_set_mutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .effectful .doesntThrow [A, (.terminal .uint53), E] A
  /-- `bigint_nat__lean_array_swap_immutable`, updating the array in place (Array.swapIfInBounds) -/
  | bigint_nat__lean_array_swap_mutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .effectful .doesntThrow [A, (.terminal .bigint_nat), (.terminal .bigint_nat)] A
  /-- `uint53__lean_array_swap_immutable`, updating the array in place (Array.swapIfInBounds) -/
  | uint53__lean_array_swap_mutable : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpImported .effectful .doesntThrow [A, (.terminal .uint53), (.terminal .uint53)] A
  /-- Nat.div -/
  | bigint_nat__lean_nat_div : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.div -/
  | uint53__lean_nat_div : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Char.ofNatAux (decides `n.isValidChar`) -/
  | bigint_nat__lean_uint32_of_nat__Char_ofNatAux : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .string)
  /-- Char.ofNatAux (decides `n.isValidChar`) -/
  | uint53__lean_uint32_of_nat__Char_ofNatAux : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .string)
  /-- Nat.mod -/
  | bigint_nat__lean_nat_mod__Nat_mod : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.mod -/
  | uint53__lean_nat_mod__Nat_mod : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.sub -/
  | bigint_nat__lean_nat_sub : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.sub -/
  | uint53__lean_nat_sub : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt8.ofNat -/
  | bigint_nat__lean_uint8_of_nat__UInt8_ofNat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint8)
  /-- UInt8.ofNat -/
  | uint53__lean_uint8_of_nat__UInt8_ofNat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint8)
  /-- Nat.add -/
  | uint53__lean_nat_add : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.pred -/
  | bigint_nat__lean_nat_pred : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.pred -/
  | uint53__lean_nat_pred : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- String.hash -/
  | bigint_nat__lean_string_hash : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.hash -/
  | uint53__lean_string_hash : JsOpImported .pure .mayThrow [(.terminal .string)] (.terminal .uint53)
  /-- UInt64.toBitVec -/
  | bigint_nat__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal (.int53_bitvec_big 64 (by decide)))
  /-- UInt64.ofBitVec -/
  | bigint_bitvec64__uint53__lean_uint64_of_nat_mk : JsOpImported .pure .mayThrow [(.terminal (.bigint_bitvec_big 64 (by decide)))] (.terminal .uint53)
  /-- Nat.pow -/
  | bigint_nat__lean_nat_pow : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.pow -/
  | uint53__lean_nat_pow : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.mul -/
  | uint53__lean_nat_mul : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- String.utf8ByteSize -/
  | bigint_nat__lean_string_utf8_byte_size : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.utf8ByteSize -/
  | uint53__lean_string_utf8_byte_size : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .uint53)
  /-- mixHash -/
  | bigint_nat__lean_uint64_mix_hash : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- mixHash -/
  | uint53__lean_uint64_mix_hash : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- UInt64.ofNatLT (decides `n < UInt64.size`) -/
  | uint53__lean_uint64_of_nat__UInt64_ofNatLT : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- Int.ofNat -/
  | bigint_nat__int53__lean_nat_to_int : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int.mul -/
  | int53__lean_int_mul : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.negSucc -/
  | bigint_nat__bigint_int__lean_int_neg_succ_of_nat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- Int.negSucc -/
  | bigint_nat__int53__lean_int_neg_succ_of_nat : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int.negSucc -/
  | uint53__bigint_int__lean_int_neg_succ_of_nat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_int)
  /-- Int.negSucc -/
  | uint53__int53__lean_int_neg_succ_of_nat : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .int53)
  /-- Int.add -/
  | int53__lean_int_add : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.neg -/
  | int53__lean_int_neg : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int53)
  /-- Int.sub -/
  | int53__lean_int_sub : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.natAbs -/
  | bigint_int__bigint_nat__lean_nat_abs : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_nat)
  /-- Int.natAbs -/
  | bigint_int__uint53__lean_nat_abs : JsOpImported .pure .mayThrow [(.terminal .bigint_int)] (.terminal .uint53)
  /-- Int.natAbs -/
  | int53__bigint_nat__lean_nat_abs : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .bigint_nat)
  /-- Int.natAbs -/
  | int53__uint53__lean_nat_abs : JsOpImported .pure .mayThrow [(.terminal .int53)] (.terminal .uint53)
  /-- Nat.divExact (decides `y ∣ x`) -/
  | bigint_nat__lean_nat_div_exact : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.divExact (decides `y ∣ x`) -/
  | uint53__lean_nat_div_exact : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.xor -/
  | uint53__lean_nat_lxor : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.shiftLeft -/
  | uint53__lean_nat_shiftl : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.shiftRight -/
  | uint53__lean_nat_shiftr : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.land -/
  | uint53__lean_nat_land : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Nat.lor -/
  | uint53__lean_nat_lor : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Lean.version.getSpecialDesc -/
  | string__lean_version_get_special_desc : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .string))
  /-- Lean.version.getIsRelease -/
  | bool__lean_version_get_is_release : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bool))
  /-- _private.Init.Meta.Defs.0.Lean.version.getMajor -/
  | bigint_nat__lean_version_get_major : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bigint_nat))
  /-- _private.Init.Meta.Defs.0.Lean.version.getMajor -/
  | uint53__lean_version_get_major : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .uint53))
  /-- _private.Init.Meta.Defs.0.Lean.version.getPatch -/
  | bigint_nat__lean_version_get_patch : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bigint_nat))
  /-- _private.Init.Meta.Defs.0.Lean.version.getPatch -/
  | uint53__lean_version_get_patch : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .uint53))
  /-- Lean.Internal.isStage0 -/
  | bool__lean_internal_is_stage0 : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bool))
  /-- _private.Init.Meta.Defs.0.Lean.version.getMinor -/
  | bigint_nat__lean_version_get_minor : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bigint_nat))
  /-- _private.Init.Meta.Defs.0.Lean.version.getMinor -/
  | uint53__lean_version_get_minor : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .uint53))
  /-- Lean.getGithash -/
  | string__lean_get_githash : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .string))
  /-- Lean.Internal.hasLLVMBackend -/
  | bool__lean_internal_has_llvm_backend : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bool))
  /-- Nat.log2 -/
  | bigint_nat__lean_nat_log2 : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- Nat.log2 -/
  | uint53__lean_nat_log2 : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- Int.emod -/
  | bigint_int__lean_int_emod : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.emod -/
  | int53__lean_int_emod : JsOpImported .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.divExact (decides `y ∣ x`) -/
  | bigint_int__lean_int_div_exact : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.divExact (decides `y ∣ x`) -/
  | int53__lean_int_div_exact : JsOpImported .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.tmod -/
  | bigint_int__lean_int_mod : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.tmod -/
  | int53__lean_int_mod : JsOpImported .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.ediv -/
  | bigint_int__lean_int_ediv : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.ediv -/
  | int53__lean_int_ediv : JsOpImported .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int.tdiv -/
  | bigint_int__lean_int_div : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int.tdiv -/
  | int53__lean_int_div : JsOpImported .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- System.Platform.getIsEmscripten -/
  | bool__lean_system_platform_emscripten : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .bool))
  /-- System.Platform.getTarget -/
  | string__lean_system_platform_target : JsOpImported .pure .doesntThrow [] (.fn [] (.terminal .string))
  /-- UInt64.toNat -/
  | bigint_nat__uint53__lean_uint64_to_nat__UInt64_toNat : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal .uint53)
  /-- UInt32.toUInt8 -/
  | uint32__lean_uint32_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint8)
  /-- UInt64.toUInt32 -/
  | bigint_nat__lean_uint64_to_uint32 : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint32)
  /-- UInt64.toUInt32 -/
  | uint53__lean_uint64_to_uint32 : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint32)
  /-- UInt32.toUInt16 -/
  | uint32__lean_uint32_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint16)
  /-- UInt32.ofNat -/
  | bigint_nat__lean_uint32_of_nat__UInt32_ofNat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint32)
  /-- UInt32.ofNat -/
  | uint53__lean_uint32_of_nat__UInt32_ofNat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint32)
  /-- UInt32.sub -/
  | uint32__lean_uint32_sub : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt16.toUInt8 -/
  | uint16__lean_uint16_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint8)
  /-- UInt32.add -/
  | uint32__lean_uint32_add : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt64.ofNat -/
  | bigint_nat__lean_uint64_of_nat__UInt64_ofNat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.ofNat -/
  | bigint_nat__uint53__lean_uint64_of_nat__UInt64_ofNat : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal .uint53)
  /-- UInt64.ofNat -/
  | uint53__bigint_nat__lean_uint64_of_nat__UInt64_ofNat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- UInt64.ofNat -/
  | uint53__lean_uint64_of_nat__UInt64_ofNat : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt16.ofNat -/
  | bigint_nat__lean_uint16_of_nat__UInt16_ofNat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint16)
  /-- UInt16.ofNat -/
  | uint53__lean_uint16_of_nat__UInt16_ofNat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint16)
  /-- UInt64.toUInt8 -/
  | bigint_nat__lean_uint64_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint8)
  /-- UInt64.toUInt8 -/
  | uint53__lean_uint64_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint8)
  /-- UInt64.toUInt16 -/
  | bigint_nat__lean_uint64_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .uint16)
  /-- UInt64.toUInt16 -/
  | uint53__lean_uint64_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint16)
  /-- UInt8.sub -/
  | uint8__lean_uint8_sub : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.neg -/
  | uint8__lean_uint8_neg : JsOpImported .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.lor -/
  | uint8__lean_uint8_lor : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.div -/
  | uint8__lean_uint8_div : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.shiftRight -/
  | uint8__lean_uint8_shift_right : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.shiftLeft -/
  | uint8__lean_uint8_shift_left : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.land -/
  | uint8__lean_uint8_land : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.mul -/
  | uint8__lean_uint8_mul : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.add -/
  | uint8__lean_uint8_add : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.complement -/
  | uint8__lean_uint8_complement : JsOpImported .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt8.mod -/
  | uint8__lean_uint8_mod : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- Bool.toUInt8 -/
  | bool__lean_bool_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .uint8)
  /-- UInt8.xor -/
  | uint8__lean_uint8_xor : JsOpImported .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .uint8)
  /-- UInt16.neg -/
  | uint16__lean_uint16_neg : JsOpImported .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.add -/
  | uint16__lean_uint16_add : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.lor -/
  | uint16__lean_uint16_lor : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.mul -/
  | uint16__lean_uint16_mul : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.land -/
  | uint16__lean_uint16_land : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.complement -/
  | uint16__lean_uint16_complement : JsOpImported .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.xor -/
  | uint16__lean_uint16_xor : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.shiftLeft -/
  | uint16__lean_uint16_shift_left : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.mod -/
  | uint16__lean_uint16_mod : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.div -/
  | uint16__lean_uint16_div : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt16.sub -/
  | uint16__lean_uint16_sub : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- Bool.toUInt16 -/
  | bool__lean_bool_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .uint16)
  /-- UInt16.shiftRight -/
  | uint16__lean_uint16_shift_right : JsOpImported .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .uint16)
  /-- UInt32.mod -/
  | uint32__lean_uint32_mod : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- Bool.toUInt32 -/
  | bool__lean_bool_to_uint32 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .uint32)
  /-- UInt32.div -/
  | uint32__lean_uint32_div : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.shiftRight -/
  | uint32__lean_uint32_shift_right : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.neg -/
  | uint32__lean_uint32_neg : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.lor -/
  | uint32__lean_uint32_lor : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.xor -/
  | uint32__lean_uint32_xor : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.shiftLeft -/
  | uint32__lean_uint32_shift_left : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.mul -/
  | uint32__lean_uint32_mul : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.land -/
  | uint32__lean_uint32_land : JsOpImported .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .uint32)
  /-- UInt32.complement -/
  | uint32__lean_uint32_complement : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint32)
  /-- UInt64.shiftLeft -/
  | bigint_nat__lean_uint64_shift_left : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.shiftLeft -/
  | uint53__lean_uint64_shift_left : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.shiftRight -/
  | bigint_nat__lean_uint64_shift_right : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.shiftRight -/
  | uint53__lean_uint64_shift_right : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.complement -/
  | bigint_nat__lean_uint64_complement : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.complement -/
  | uint53__lean_uint64_complement : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.add -/
  | bigint_nat__lean_uint64_add : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.add -/
  | uint53__lean_uint64_add : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.lor -/
  | bigint_nat__lean_uint64_lor : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.lor -/
  | uint53__lean_uint64_lor : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.mod -/
  | bigint_nat__lean_uint64_mod : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.mod -/
  | uint53__lean_uint64_mod : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.div -/
  | bigint_nat__lean_uint64_div : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.div -/
  | uint53__lean_uint64_div : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.mul -/
  | bigint_nat__lean_uint64_mul : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.mul -/
  | uint53__lean_uint64_mul : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.land -/
  | bigint_nat__lean_uint64_land : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.land -/
  | uint53__lean_uint64_land : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Bool.toUInt64 -/
  | bigint_nat__lean_bool_to_uint64 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .bigint_nat)
  /-- Bool.toUInt64 -/
  | uint53__lean_bool_to_uint64 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .uint53)
  /-- UInt64.sub -/
  | bigint_nat__lean_uint64_sub : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.sub -/
  | uint53__lean_uint64_sub : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.neg -/
  | bigint_nat__lean_uint64_neg : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.neg -/
  | uint53__lean_uint64_neg : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt64.xor -/
  | bigint_nat__lean_uint64_xor : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.xor -/
  | uint53__lean_uint64_xor : JsOpImported .pure .mayThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Int8.add -/
  | int8__lean_int8_add : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.div -/
  | int8__lean_int8_div : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.shiftRight -/
  | int8__lean_int8_shift_right : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.mod -/
  | int8__lean_int8_mod : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Bool.toInt8 -/
  | bool__lean_bool_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .int8)
  /-- Int8.shiftLeft -/
  | int8__lean_int8_shift_left : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.xor -/
  | int8__lean_int8_xor : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.complement -/
  | int8__lean_int8_complement : JsOpImported .pure .doesntThrow [(.terminal .int8)] (.terminal .int8)
  /-- Int8.neg -/
  | int8__lean_int8_neg : JsOpImported .pure .doesntThrow [(.terminal .int8)] (.terminal .int8)
  /-- Int8.abs -/
  | int8__lean_int8_abs : JsOpImported .pure .doesntThrow [(.terminal .int8)] (.terminal .int8)
  /-- Int8.sub -/
  | int8__lean_int8_sub : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.ofNat -/
  | bigint_nat__lean_int8_of_nat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .int8)
  /-- Int8.ofNat -/
  | uint53__lean_int8_of_nat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .int8)
  /-- Int8.mul -/
  | int8__lean_int8_mul : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.land -/
  | int8__lean_int8_land : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int8.ofInt -/
  | bigint_int__lean_int8_of_int : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int8)
  /-- Int8.ofInt -/
  | int53__lean_int8_of_int : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int8)
  /-- Int8.lor -/
  | int8__lean_int8_lor : JsOpImported .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .int8)
  /-- Int16.ofNat -/
  | bigint_nat__lean_int16_of_nat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .int16)
  /-- Int16.ofNat -/
  | uint53__lean_int16_of_nat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .int16)
  /-- Int16.shiftRight -/
  | int16__lean_int16_shift_right : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.div -/
  | int16__lean_int16_div : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.mod -/
  | int16__lean_int16_mod : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Bool.toInt16 -/
  | bool__lean_bool_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .int16)
  /-- Int16.abs -/
  | int16__lean_int16_abs : JsOpImported .pure .doesntThrow [(.terminal .int16)] (.terminal .int16)
  /-- Int16.complement -/
  | int16__lean_int16_complement : JsOpImported .pure .doesntThrow [(.terminal .int16)] (.terminal .int16)
  /-- Int16.land -/
  | int16__lean_int16_land : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.ofInt -/
  | bigint_int__lean_int16_of_int : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int16)
  /-- Int16.ofInt -/
  | int53__lean_int16_of_int : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int16)
  /-- Int16.mul -/
  | int16__lean_int16_mul : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.shiftLeft -/
  | int16__lean_int16_shift_left : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.xor -/
  | int16__lean_int16_xor : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.lor -/
  | int16__lean_int16_lor : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.add -/
  | int16__lean_int16_add : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int16.toInt8 -/
  | int16__lean_int16_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .int16)] (.terminal .int8)
  /-- Int16.neg -/
  | int16__lean_int16_neg : JsOpImported .pure .doesntThrow [(.terminal .int16)] (.terminal .int16)
  /-- Int16.sub -/
  | int16__lean_int16_sub : JsOpImported .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .int16)
  /-- Int32.ofInt -/
  | bigint_int__lean_int32_of_int : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int32)
  /-- Int32.ofInt -/
  | int53__lean_int32_of_int : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int32)
  /-- Int32.land -/
  | int32__lean_int32_land : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.mul -/
  | int32__lean_int32_mul : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.ofNat -/
  | bigint_nat__lean_int32_of_nat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .int32)
  /-- Int32.ofNat -/
  | uint53__lean_int32_of_nat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .int32)
  /-- Int32.sub -/
  | int32__lean_int32_sub : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.neg -/
  | int32__lean_int32_neg : JsOpImported .pure .doesntThrow [(.terminal .int32)] (.terminal .int32)
  /-- Int32.abs -/
  | int32__lean_int32_abs : JsOpImported .pure .doesntThrow [(.terminal .int32)] (.terminal .int32)
  /-- Int32.xor -/
  | int32__lean_int32_xor : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.shiftLeft -/
  | int32__lean_int32_shift_left : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.shiftRight -/
  | int32__lean_int32_shift_right : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.complement -/
  | int32__lean_int32_complement : JsOpImported .pure .doesntThrow [(.terminal .int32)] (.terminal .int32)
  /-- Bool.toInt32 -/
  | bool__lean_bool_to_int32 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .int32)
  /-- Int32.toInt8 -/
  | int32__lean_int32_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .int32)] (.terminal .int8)
  /-- Int32.add -/
  | int32__lean_int32_add : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.lor -/
  | int32__lean_int32_lor : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.mod -/
  | int32__lean_int32_mod : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int32.toInt16 -/
  | int32__lean_int32_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .int32)] (.terminal .int16)
  /-- Int32.div -/
  | int32__lean_int32_div : JsOpImported .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .int32)
  /-- Int64.sub -/
  | bigint_int__lean_int64_sub : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.sub -/
  | int53__lean_int64_sub : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.xor -/
  | bigint_int__lean_int64_xor : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.xor -/
  | int53__lean_int64_xor : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt8 -/
  | bigint_int__lean_int64_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int8)
  /-- Int64.toInt8 -/
  | int53__lean_int64_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int8)
  /-- Int64.mul -/
  | bigint_int__lean_int64_mul : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.mul -/
  | int53__lean_int64_mul : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.ofInt -/
  | bigint_int__lean_int64_of_int : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.ofInt -/
  | bigint_int__int53__lean_int64_of_int : JsOpImported .pure .mayThrow [(.terminal .bigint_int)] (.terminal .int53)
  /-- Int64.ofInt -/
  | int53__bigint_int__lean_int64_of_int : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .bigint_int)
  /-- Int64.ofInt -/
  | int53__lean_int64_of_int : JsOpImported .pure .mayThrow [(.terminal .int53)] (.terminal .int53)
  /-- Int64.land -/
  | bigint_int__lean_int64_land : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.land -/
  | int53__lean_int64_land : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.lor -/
  | bigint_int__lean_int64_lor : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.lor -/
  | int53__lean_int64_lor : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.mod -/
  | bigint_int__lean_int64_mod : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.mod -/
  | int53__lean_int64_mod : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.shiftLeft -/
  | bigint_int__lean_int64_shift_left : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.shiftLeft -/
  | int53__lean_int64_shift_left : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.complement -/
  | bigint_int__lean_int64_complement : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.complement -/
  | int53__lean_int64_complement : JsOpImported .pure .mayThrow [(.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt32 -/
  | bigint_int__lean_int64_to_int32 : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int32)
  /-- Int64.toInt32 -/
  | int53__lean_int64_to_int32 : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int32)
  /-- Int64.abs -/
  | bigint_int__lean_int64_abs : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.abs -/
  | int53__lean_int64_abs : JsOpImported .pure .mayThrow [(.terminal .int53)] (.terminal .int53)
  /-- Bool.toInt64 -/
  | bigint_int__lean_bool_to_int64 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .bigint_int)
  /-- Bool.toInt64 -/
  | int53__lean_bool_to_int64 : JsOpImported .pure .doesntThrow [(.terminal .bool)] (.terminal .int53)
  /-- Int64.ofNat -/
  | bigint_nat__bigint_int__lean_int64_of_nat : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- Int64.ofNat -/
  | bigint_nat__int53__lean_int64_of_nat : JsOpImported .pure .mayThrow [(.terminal .bigint_nat)] (.terminal .int53)
  /-- Int64.ofNat -/
  | uint53__bigint_int__lean_int64_of_nat : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_int)
  /-- Int64.ofNat -/
  | uint53__int53__lean_int64_of_nat : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .int53)
  /-- Int64.toInt -/
  | bigint_int__int53__lean_int64_to_int_sint : JsOpImported .pure .mayThrow [(.terminal .bigint_int)] (.terminal .int53)
  /-- Int64.neg -/
  | bigint_int__lean_int64_neg : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.neg -/
  | int53__lean_int64_neg : JsOpImported .pure .mayThrow [(.terminal .int53)] (.terminal .int53)
  /-- Int64.add -/
  | bigint_int__lean_int64_add : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.add -/
  | int53__lean_int64_add : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.div -/
  | bigint_int__lean_int64_div : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.div -/
  | int53__lean_int64_div : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- Int64.toInt16 -/
  | bigint_int__lean_int64_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .int16)
  /-- Int64.toInt16 -/
  | int53__lean_int64_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .int53)] (.terminal .int16)
  /-- Int64.shiftRight -/
  | bigint_int__lean_int64_shift_right : JsOpImported .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- Int64.shiftRight -/
  | int53__lean_int64_shift_right : JsOpImported .pure .mayThrow [(.terminal .int53), (.terminal .int53)] (.terminal .int53)
  /-- UInt16.log2 -/
  | uint16__lean_uint16_log2 : JsOpImported .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint16)
  /-- UInt64.log2 -/
  | bigint_nat__lean_uint64_log2 : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- UInt64.log2 -/
  | uint53__lean_uint64_log2 : JsOpImported .pure .mayThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- UInt8.log2 -/
  | uint8__lean_uint8_log2 : JsOpImported .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint8)
  /-- UInt32.log2 -/
  | uint32__lean_uint32_log2 : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint32)
  /-- String.Internal.get -/
  | string__lean_string_utf8_get__String_Internal_get : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.trim -/
  | string__lean_string_trim : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .string)
  /-- Substring.Raw.Internal.drop -/
  | bigint_nat__lean_substring_drop : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .bigint_nat)] (.terminal .substring)
  /-- Substring.Raw.Internal.drop -/
  | uint53__lean_substring_drop : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .uint53)] (.terminal .substring)
  /-- Substring.Raw.Internal.prev -/
  | substring__lean_substring_prev : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .uint53)] (.terminal .uint53)
  /-- Substring.Raw.Internal.extract -/
  | substring__lean_substring_extract : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .uint53), (.terminal .uint53)] (.terminal .substring)
  /-- String.Internal.foldl -/
  | string__lean_string_foldl : JsOpImported .pure .doesntThrow [(.fn [(.terminal .string), (.terminal .string)] (.terminal .string)), (.terminal .string), (.terminal .string)] (.terminal .string)
  /-- Substring.Raw.Internal.toString -/
  | substring__lean_substring_tostring : JsOpImported .pure .doesntThrow [(.terminal .substring)] (.terminal .string)
  /-- String.Internal.getUTF8Byte (decides `n < s.utf8ByteSize`) -/
  | bigint_nat__lean_string_get_byte_fast__String_Internal_getUTF8Byte : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .bigint_nat)] (.terminal .uint8)
  /-- String.Internal.getUTF8Byte (decides `n < s.utf8ByteSize`) -/
  | uint53__lean_string_get_byte_fast__String_Internal_getUTF8Byte : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint8)
  /-- String.Internal.isEmpty -/
  | string__lean_string_isempty : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .bool)
  /-- String.Internal.isPrefixOf -/
  | string__lean_string_isprefixof : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- String.Internal.dropRight -/
  | bigint_nat__lean_string_dropright : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .bigint_nat)] (.terminal .string)
  /-- String.Internal.dropRight -/
  | uint53__lean_string_dropright : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- Substring.Raw.Internal.takeWhile -/
  | substring__lean_substring_takewhile : JsOpImported .pure .doesntThrow [(.terminal .substring), (.fn [(.terminal .string)] (.terminal .bool))] (.terminal .substring)
  /-- Substring.Raw.Internal.get -/
  | substring__lean_substring_get : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.contains -/
  | string__lean_string_contains : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- String.Internal.front -/
  | string__lean_string_front : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .string)
  /-- String.Internal.posOf -/
  | string__lean_string_posof : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .uint53)
  /-- Substring.Raw.Internal.all -/
  | substring__lean_substring_all : JsOpImported .pure .doesntThrow [(.terminal .substring), (.fn [(.terminal .string)] (.terminal .bool))] (.terminal .bool)
  /-- String.Internal.intercalate -/
  | string__lean_string_intercalate : JsOpImported .pure .doesntThrow [(.terminal .string), (.list (.terminal .string))] (.terminal .string)
  /-- String.Internal.drop -/
  | bigint_nat__lean_string_drop : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .bigint_nat)] (.terminal .string)
  /-- String.Internal.drop -/
  | uint53__lean_string_drop : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.length -/
  | bigint_nat__lean_string_length__String_Internal_length : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .bigint_nat)
  /-- String.Internal.length -/
  | uint53__lean_string_length__String_Internal_length : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .uint53)
  /-- String.Internal.atEnd -/
  | string__lean_string_utf8_at_end__String_Internal_atEnd : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .bool)
  /-- Substring.Raw.Internal.beq -/
  | substring__lean_substring_beq : JsOpImported .pure .doesntThrow [(.terminal .substring), (.terminal .substring)] (.terminal .bool)
  /-- String.Internal.nextWhile -/
  | string__lean_string_nextwhile : JsOpImported .pure .doesntThrow [(.terminal .string), (.fn [(.terminal .string)] (.terminal .bool)), (.terminal .uint53)] (.terminal .uint53)
  /-- String.Internal.next -/
  | string__lean_string_utf8_next__String_Internal_next : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.mk -/
  | string__lean_string_mk__String_mk : JsOpImported .pure .doesntThrow [(.list (.terminal .string))] (.terminal .string)
  /-- String.Internal.any -/
  | string__lean_string_any : JsOpImported .pure .doesntThrow [(.terminal .string), (.fn [(.terminal .string)] (.terminal .bool))] (.terminal .bool)
  /-- String.Internal.pushn -/
  | bigint_nat__lean_string_pushn : JsOpImported .pure .mayThrow [(.terminal .string), (.terminal .string), (.terminal .bigint_nat)] (.terminal .string)
  /-- String.Internal.pushn -/
  | uint53__lean_string_pushn : JsOpImported .pure .mayThrow [(.terminal .string), (.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Internal.capitalize -/
  | string__lean_string_capitalize : JsOpImported .pure .doesntThrow [(.terminal .string)] (.terminal .string)
  /-- String.Internal.extract -/
  | string__lean_string_utf8_extract__String_Internal_extract : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53), (.terminal .uint53)] (.terminal .string)
  /-- String.Pos.Raw.Internal.min -/
  | uint53__lean_string_pos_min : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Substring.Raw.Internal.front -/
  | substring__lean_substring_front : JsOpImported .pure .doesntThrow [(.terminal .substring)] (.terminal .string)
  /-- String.Pos.Raw.Internal.sub -/
  | uint53__lean_string_pos_sub : JsOpImported .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .uint53)
  /-- Substring.Raw.Internal.isEmpty -/
  | substring__lean_substring_isempty : JsOpImported .pure .doesntThrow [(.terminal .substring)] (.terminal .bool)
  /-- String.Internal.offsetOfPos -/
  | bigint_nat__lean_string_offsetofpos : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .bigint_nat)
  /-- String.Internal.offsetOfPos -/
  | uint53__lean_string_offsetofpos : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.getUTF8Byte (decides `p < s.rawEndPos`) -/
  | string__lean_string_get_byte_fast__String_getUTF8Byte : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint8)
  /-- String.Pos.Raw.get? -/
  | string__lean_string_utf8_get_opt__String_Pos_Raw_get? : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.union [] [(.terminal .string)] [])
  /-- String.Pos.Raw.prev -/
  | string__lean_string_utf8_prev__String_Pos_Raw_prev : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.next' (decides `¬String.Pos.Raw.atEnd s p = Bool.true`) -/
  | string__lean_string_utf8_next_fast__String_next' : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.Pos.next (decides `pos ≠ s.endPos`) -/
  | string__lean_string_utf8_next_fast__String_Pos_next : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .uint53)
  /-- String.data -/
  | string__lean_string_data__String_data : JsOpImported .pure .doesntThrow [(.terminal .string)] (.list (.terminal .string))
  /-- String.extract -/
  | string__lean_string_utf8_extract_fast : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53), (.terminal .uint53)] (.terminal .string)
  /-- String.Pos.Raw.get! -/
  | string__lean_string_utf8_get_bang__String_Pos_Raw_get! : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .string)
  /-- String.Pos.Raw.isValid -/
  | string__lean_string_is_valid_pos : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53)] (.terminal .bool)
  /-- String.Slice.Pattern.Internal.memcmpStr (decides `len.offsetBy lstart ≤ lhs.rawEndPos`, `len.offsetBy rstart ≤ rhs.rawEndPos`) -/
  | string__lean_string_memcmp : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .string), (.terminal .uint53), (.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- String.Slice.instDecidableLt -/
  | stringSlice__lean_slice_dec_lt : JsOpImported .pure .doesntThrow [(.terminal .stringSlice), (.terminal .stringSlice)] (.terminal .bool)
  /-- String.Slice.hash -/
  | bigint_nat__lean_slice_hash : JsOpImported .pure .doesntThrow [(.terminal .stringSlice)] (.terminal .bigint_nat)
  /-- String.Slice.hash -/
  | uint53__lean_slice_hash : JsOpImported .pure .mayThrow [(.terminal .stringSlice)] (.terminal .uint53)
  /-- String.Pos.Raw.set -/
  | string__lean_string_utf8_set__String_Pos_Raw_set : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53), (.terminal .string)] (.terminal .string)
  /-- String.Pos.set (decides `p ≠ s.endPos`) -/
  | string__lean_string_utf8_set__String_Pos_set : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .uint53), (.terminal .string)] (.terminal .string)
  /-- String.compare -/
  | string__lean_string_compare : JsOpImported .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.enum 3 (-1))
  /-- Float.frExp -/
  | bigint_int__lean_float_frexp : JsOpImported .pure .doesntThrow [(.terminal .float)] (.record (.terminal .float) (.terminal .bigint_int) [])
  /-- Float.frExp -/
  | int53__lean_float_frexp : JsOpImported .pure .doesntThrow [(.terminal .float)] (.record (.terminal .float) (.terminal .int53) [])
  /-- Float.toBits -/
  | bigint_nat__lean_float_to_bits__Float_toBits : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bigint_nat)
  /-- Float.toBits -/
  | uint53__lean_float_to_bits__Float_toBits : JsOpImported .pure .mayThrow [(.terminal .float)] (.terminal .uint53)
  /-- Float.ofBits -/
  | bigint_nat__lean_float_of_bits__Float_ofBits : JsOpImported .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .float)
  /-- Float.ofBits -/
  | uint53__lean_float_of_bits__Float_ofBits : JsOpImported .pure .doesntThrow [(.terminal .uint53)] (.terminal .float)
  /-- Float.isNaN -/
  | float__lean_float_isnan : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bool)
  /-- Float.toUInt16 -/
  | float__lean_float_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .uint16)
  /-- Float.toUInt64 -/
  | bigint_nat__lean_float_to_uint64 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bigint_nat)
  /-- Float.toUInt64 -/
  | uint53__lean_float_to_uint64 : JsOpImported .pure .mayThrow [(.terminal .float)] (.terminal .uint53)
  /-- Float.toUInt32 -/
  | float__lean_float_to_uint32 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .uint32)
  /-- Float.toString -/
  | float__lean_float_to_string : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .string)
  /-- Float.toUInt8 -/
  | float__lean_float_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .uint8)
  /-- Float.isFinite -/
  | float__lean_float_isfinite : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bool)
  /-- Float.round -/
  | float__round : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- Float.scaleB -/
  | bigint_int__lean_float_scaleb : JsOpImported .pure .doesntThrow [(.terminal .float), (.terminal .bigint_int)] (.terminal .float)
  /-- Float.scaleB -/
  | int53__lean_float_scaleb : JsOpImported .pure .doesntThrow [(.terminal .float), (.terminal .int53)] (.terminal .float)
  /-- Float.isInf -/
  | float__lean_float_isinf : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bool)
  /-- Float.toInt16 -/
  | float__lean_float_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .int16)
  /-- Float.toInt32 -/
  | float__lean_float_to_int32 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .int32)
  /-- Float.toInt8 -/
  | float__lean_float_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .int8)
  /-- Float.toInt64 -/
  | bigint_int__lean_float_to_int64 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .bigint_int)
  /-- Float.toInt64 -/
  | int53__lean_float_to_int64 : JsOpImported .pure .mayThrow [(.terminal .float)] (.terminal .int53)
  /-- Float32.div -/
  | float32__lean_float32_div : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float.toFloat32 -/
  | float__lean_float_to_float32 : JsOpImported .pure .doesntThrow [(.terminal .float)] (.terminal .float32)
  /-- Float32.toBits -/
  | float32__lean_float32_to_bits__Float32_toBits : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .uint32)
  /-- Float32.ofBits -/
  | uint32__lean_float32_of_bits__Float32_ofBits : JsOpImported .pure .doesntThrow [(.terminal .uint32)] (.terminal .float32)
  /-- Float32.frExp -/
  | bigint_int__lean_float32_frexp : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.record (.terminal .float32) (.terminal .bigint_int) [])
  /-- Float32.frExp -/
  | int53__lean_float32_frexp : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.record (.terminal .float32) (.terminal .int53) [])
  /-- Float32.toUInt64 -/
  | bigint_nat__lean_float32_to_uint64 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .bigint_nat)
  /-- Float32.toUInt64 -/
  | uint53__lean_float32_to_uint64 : JsOpImported .pure .mayThrow [(.terminal .float32)] (.terminal .uint53)
  /-- Float32.sub -/
  | float32__lean_float32_sub : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float32.toUInt16 -/
  | float32__lean_float32_to_uint16 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .uint16)
  /-- Float32.isNaN -/
  | float32__lean_float32_isnan : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .bool)
  /-- Float32.isInf -/
  | float32__lean_float32_isinf : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .bool)
  /-- Float32.isFinite -/
  | float32__lean_float32_isfinite : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .bool)
  /-- Float32.add -/
  | float32__lean_float32_add : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float32.scaleB -/
  | bigint_int__lean_float32_scaleb : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .bigint_int)] (.terminal .float32)
  /-- Float32.scaleB -/
  | int53__lean_float32_scaleb : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .int53)] (.terminal .float32)
  /-- Float32.mul -/
  | float32__lean_float32_mul : JsOpImported .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- Float32.toString -/
  | float32__lean_float32_to_string : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .string)
  /-- Float32.toUInt32 -/
  | float32__lean_float32_to_uint32 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .uint32)
  /-- Float32.round -/
  | float32__roundf : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- Float32.toUInt8 -/
  | float32__lean_float32_to_uint8 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .uint8)
  /-- Float32.toInt64 -/
  | bigint_int__lean_float32_to_int64 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .bigint_int)
  /-- Float32.toInt64 -/
  | int53__lean_float32_to_int64 : JsOpImported .pure .mayThrow [(.terminal .float32)] (.terminal .int53)
  /-- Float32.toInt8 -/
  | float32__lean_float32_to_int8 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .int8)
  /-- Float32.toInt16 -/
  | float32__lean_float32_to_int16 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .int16)
  /-- Float32.toInt32 -/
  | float32__lean_float32_to_int32 : JsOpImported .pure .doesntThrow [(.terminal .float32)] (.terminal .int32)

/-- The names of the constructors of `JsOpImported`, in order. -/
def JsOpImported.names : Array String := ctor_names% JsOpImported

/-- The name of the operation (the name of its constructor). -/
def JsOpImported.name {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpImported e t σs τ) : String :=
  JsOpImported.names[op.ctorIdx]!

/-- The name of the function of `runtime.js` that implements the operation: the name of its
    constructor, made a JavaScript identifier (`jsSafeName`). -/
def JsOpImported.runtimeName {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpImported e t σs τ) : String :=
  jsSafeName op.name

/-- The operations written inline, indexed by their effects, the types of their arguments
    and the type of their result. -/
inductive JsOpInlinable : Effectfulness → MayThrow → List JsTy → JsTy → Type where
  /-- `BigInt(a.length)` (Array.size) -/
  | bigint_nat__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlinable .pure .doesntThrow [A] (.terminal .bigint_nat)
  /-- `a.length` (Array.size) -/
  | uint53__lean_array_get_size : {A E : JsTy} → (l : JsArrayLayout A E) → JsOpInlinable .pure .doesntThrow [A] (.terminal .uint53)
  /-- `a` (Array.toList) -/
  | array__lean_array_to_list : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.array α)] (.list α)
  /-- `[]` (Array.emptyWithCapacity) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.typedArray t)
  /-- `[]` (Array.emptyWithCapacity) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.emptyWithCapacity) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.typedArray t)
  /-- `[]` (Array.mkEmpty) -/
  | bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.typedArray t)
  /-- `[]` (Array.mkEmpty) -/
  | uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.array α)
  /-- `new C(0)` (Array.mkEmpty) -/
  | typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.typedArray t)
  /-- `a` (Array.mk) -/
  | array__lean_array_mk : (α : JsTy) → JsOpInlinable .pure .doesntThrow [(.list α)] (.array α)
  /-- `C.from(a)` (Array.mk) -/
  | typedArray__lean_array_mk : (t : JsTypedElem) → JsOpInlinable .pure .doesntThrow [(.list (.terminal t.leaf))] (.typedArray t)
  /-- `a` (UInt32.ofBitVec) -/
  | bitvec32__lean_uint32_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 32 (by decide) (by decide)))] (.terminal .uint32)
  /-- `a === b` (UInt32.decEq) -/
  | uint32__lean_uint32_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a < b` (UInt32.decLt) -/
  | uint32__lean_uint32_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a` (UInt8.toBitVec) -/
  | uint8__lean_uint8_to_nat__UInt8_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal (.bitvec_small 8 (by decide) (by decide)))
  /-- `a < b` (Nat.decLt) -/
  | bigint_nat__lean_nat_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (Nat.decLt) -/
  | uint53__lean_nat_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt8.decLt) -/
  | uint8__lean_uint8_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (UInt32.decLe) -/
  | uint32__lean_uint32_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint32), (.terminal .uint32)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_decEq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.decEq) -/
  | uint53__lean_nat_dec_eq__Nat_decEq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | bigint_nat__lean_nat_dec_eq__Nat_beq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (Nat.beq) -/
  | uint53__lean_nat_dec_eq__Nat_beq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (UInt8.decLe) -/
  | uint8__lean_uint8_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | bigint_nat__lean_nat_dec_le__Nat_ble : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.ble) -/
  | uint53__lean_nat_dec_le__Nat_ble : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | bigint_nat__lean_nat_dec_le__Nat_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (Nat.decLe) -/
  | uint53__lean_nat_dec_le__Nat_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a + b` (Nat.add) -/
  | bigint_nat__lean_nat_add : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toBitVec) -/
  | uint16__lean_uint16_to_nat__UInt16_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal (.bitvec_small 16 (by decide) (by decide)))
  /-- `a` (UInt16.ofBitVec) -/
  | bitvec16__lean_uint16_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 16 (by decide) (by decide)))] (.terminal .uint16)
  /-- `a === b` (UInt16.decEq) -/
  | uint16__lean_uint16_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a === b` (String.decEq) -/
  | string__lean_string_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt64.toBitVec) -/
  | bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `BigInt(a)` (UInt64.toBitVec) -/
  | uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal (.bigint_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.toBitVec) -/
  | uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal (.int53_bitvec_big 64 (by decide)))
  /-- `a` (UInt64.ofBitVec) -/
  | bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bigint_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.ofBitVec) -/
  | int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .bigint_nat)
  /-- `a` (UInt64.ofBitVec) -/
  | int53_bitvec64__uint53__lean_uint64_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.int53_bitvec_big 64 (by decide)))] (.terminal .uint53)
  /-- `BigInt(a)` (UInt32.toNat) -/
  | bigint_nat__lean_uint32_to_nat__UInt32_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toNat) -/
  | uint53__lean_uint32_to_nat__UInt32_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint53)
  /-- `a` (UInt32.toBitVec) -/
  | uint32__lean_uint32_to_nat__UInt32_toBitVec : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal (.bitvec_small 32 (by decide) (by decide)))
  /-- `a === b` (UInt64.decEq) -/
  | bigint_nat__lean_uint64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a === b` (UInt64.decEq) -/
  | uint53__lean_uint64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (UInt8.ofBitVec) -/
  | bitvec8__lean_uint8_of_nat_mk : JsOpInlinable .pure .doesntThrow [(.terminal (.bitvec_small 8 (by decide) (by decide)))] (.terminal .uint8)
  /-- `a === b` (UInt8.decEq) -/
  | uint8__lean_uint8_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .uint8), (.terminal .uint8)] (.terminal .bool)
  /-- `a * b` (Nat.mul) -/
  | bigint_nat__lean_nat_mul : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a || b` (strictOr) -/
  | bool__lean_strict_or : JsOpInlinable .pure .doesntThrow [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a && b` (strictAnd) -/
  | bool__lean_strict_and : JsOpInlinable .pure .doesntThrow [(.terminal .bool), (.terminal .bool)] (.terminal .bool)
  /-- `a` (Int.ofNat) -/
  | bigint_nat__bigint_int__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int.ofNat) -/
  | uint53__bigint_int__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_int)
  /-- `a` (Int.ofNat) -/
  | uint53__int53__lean_nat_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .int53)
  /-- `a <= b` (Int.decLe) -/
  | bigint_int__lean_int_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int.decLe) -/
  | int53__lean_int_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | bigint_int__lean_int_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int.decLt) -/
  | int53__lean_int_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | bigint_int__lean_int_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int.decEq) -/
  | int53__lean_int_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a * b` (Int.mul) -/
  | bigint_int__lean_int_mul : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a >= 0n` (Int.decNonneg) -/
  | bigint_int__lean_int_dec_nonneg : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bool)
  /-- `a >= 0` (Int.decNonneg) -/
  | int53__lean_int_dec_nonneg : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .bool)
  /-- `a + b` (Int.add) -/
  | bigint_int__lean_int_add : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `-a` (Int.neg) -/
  | bigint_int__lean_int_neg : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a - b` (Int.sub) -/
  | bigint_int__lean_int_sub : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `a ^ b` (Nat.xor) -/
  | bigint_nat__lean_nat_lxor : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a << b` (Nat.shiftLeft) -/
  | bigint_nat__lean_nat_shiftl : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a >> b` (Nat.shiftRight) -/
  | bigint_nat__lean_nat_shiftr : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a & b` (Nat.land) -/
  | bigint_nat__lean_nat_land : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a | b` (Nat.lor) -/
  | bigint_nat__lean_nat_lor : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .bigint_nat)
  /-- `BigInt(a)` (UInt64.toNat) -/
  | uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .bigint_nat)
  /-- `a` (UInt64.toNat) -/
  | uint53__lean_uint64_to_nat__UInt64_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .uint53)
  /-- `a` (UInt16.toUInt32) -/
  | uint16__lean_uint16_to_uint32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt32.toUInt64) -/
  | bigint_nat__lean_uint32_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .bigint_nat)
  /-- `a` (UInt32.toUInt64) -/
  | uint53__lean_uint32_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt16.toNat) -/
  | bigint_nat__lean_uint16_to_nat__UInt16_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toNat) -/
  | uint53__lean_uint16_to_nat__UInt16_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toUInt64) -/
  | bigint_nat__lean_uint8_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toUInt64) -/
  | uint53__lean_uint8_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint53)
  /-- `BigInt(a)` (UInt8.toNat) -/
  | bigint_nat__lean_uint8_to_nat__UInt8_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .bigint_nat)
  /-- `a` (UInt8.toNat) -/
  | uint53__lean_uint8_to_nat__UInt8_toNat : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt32) -/
  | uint8__lean_uint8_to_uint32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint32)
  /-- `BigInt(a)` (UInt16.toUInt64) -/
  | bigint_nat__lean_uint16_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .bigint_nat)
  /-- `a` (UInt16.toUInt64) -/
  | uint53__lean_uint16_to_uint64 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .uint53)
  /-- `a` (UInt8.toUInt16) -/
  | uint8__lean_uint8_to_uint16 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .uint16)
  /-- `a < b` (UInt16.decLt) -/
  | uint16__lean_uint16_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt16.decLe) -/
  | uint16__lean_uint16_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint16), (.terminal .uint16)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | bigint_nat__lean_uint64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a <= b` (UInt64.decLe) -/
  | uint53__lean_uint64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | bigint_nat__lean_uint64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat), (.terminal .bigint_nat)] (.terminal .bool)
  /-- `a < b` (UInt64.decLt) -/
  | uint53__lean_uint64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .uint53), (.terminal .uint53)] (.terminal .bool)
  /-- `a` (Int8.toInt16) -/
  | int8__lean_int8_to_int16 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int16)
  /-- `a === b` (Int8.decEq) -/
  | int8__lean_int8_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a < b` (Int8.decLt) -/
  | int8__lean_int8_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `a` (Int8.toInt32) -/
  | int8__lean_int8_to_int32 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int32)
  /-- `BigInt(a)` (Int8.toInt64) -/
  | bigint_int__lean_int8_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt64) -/
  | int53__lean_int8_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int8.decLe) -/
  | int8__lean_int8_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int8), (.terminal .int8)] (.terminal .bool)
  /-- `BigInt(a)` (Int8.toInt) -/
  | bigint_int__lean_int8_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .bigint_int)
  /-- `a` (Int8.toInt) -/
  | int53__lean_int8_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .int53)
  /-- `a <= b` (Int16.decLe) -/
  | int16__lean_int16_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a < b` (Int16.decLt) -/
  | int16__lean_int16_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `BigInt(a)` (Int16.toInt) -/
  | bigint_int__lean_int16_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt) -/
  | int53__lean_int16_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int53)
  /-- `a === b` (Int16.decEq) -/
  | int16__lean_int16_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int16), (.terminal .int16)] (.terminal .bool)
  /-- `a` (Int16.toInt32) -/
  | int16__lean_int16_to_int32 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int32)
  /-- `BigInt(a)` (Int16.toInt64) -/
  | bigint_int__lean_int16_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .bigint_int)
  /-- `a` (Int16.toInt64) -/
  | int53__lean_int16_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .int53)
  /-- `a <= b` (Int32.decLe) -/
  | int32__lean_int32_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt64) -/
  | bigint_int__lean_int32_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt64) -/
  | int53__lean_int32_to_int64 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .int53)
  /-- `a === b` (Int32.decEq) -/
  | int32__lean_int32_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `a < b` (Int32.decLt) -/
  | int32__lean_int32_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int32), (.terminal .int32)] (.terminal .bool)
  /-- `BigInt(a)` (Int32.toInt) -/
  | bigint_int__lean_int32_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .bigint_int)
  /-- `a` (Int32.toInt) -/
  | int53__lean_int32_to_int : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .int53)
  /-- `a < b` (Int64.decLt) -/
  | bigint_int__lean_int64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a < b` (Int64.decLt) -/
  | int53__lean_int64_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | bigint_int__lean_int64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a === b` (Int64.decEq) -/
  | int53__lean_int64_dec_eq : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | bigint_int__lean_int64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int), (.terminal .bigint_int)] (.terminal .bool)
  /-- `a <= b` (Int64.decLe) -/
  | int53__lean_int64_dec_le : JsOpInlinable .pure .doesntThrow [(.terminal .int53), (.terminal .int53)] (.terminal .bool)
  /-- `a` (Int64.toInt) -/
  | bigint_int__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .bigint_int)
  /-- `BigInt(a)` (Int64.toInt) -/
  | int53__bigint_int__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .bigint_int)
  /-- `a` (Int64.toInt) -/
  | int53__lean_int64_to_int_sint : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .int53)
  /-- `a + b` (String.Internal.append) -/
  | string__lean_string_append__String_Internal_append : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.push) -/
  | string__lean_string_push : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a + b` (String.append) -/
  | string__lean_string_append__String_append : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .string)
  /-- `a < b` (String.decidableLT) -/
  | string__lean_string_dec_lt : JsOpInlinable .pure .doesntThrow [(.terminal .string), (.terminal .string)] (.terminal .bool)
  /-- `a` (UInt8.toFloat) -/
  | uint8__lean_uint8_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .float)
  /-- `a` (Float.toModel) -/
  | float__lean_float_to_bits__Float_toModel : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (Float.ofModel) -/
  | float__lean_float_of_bits__Float_ofModel : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log10(a)` (Float.log10) -/
  | float__log10 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cbrt(a)` (Float.cbrt) -/
  | float__cbrt : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log(a)` (Float.log) -/
  | float__log : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a / b` (Float.div) -/
  | float__lean_float_div : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a === b` (Float.beq) -/
  | float__lean_float_beq : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.tan(a)` (Float.tan) -/
  | float__tan : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.tanh(a)` (Float.tanh) -/
  | float__tanh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.pow(2, a)` (Float.exp2) -/
  | float__exp2 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (UInt32.toFloat) -/
  | uint32__lean_uint32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .float)
  /-- `a <= b` (Float.decLe) -/
  | float__lean_float_decLe__Float_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a <= b` (Float.le) -/
  | float__lean_float_decLe__Float_le : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.sqrt(a)` (Float.sqrt) -/
  | float__sqrt : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.acos(a)` (Float.acos) -/
  | float__acos : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atan(a)` (Float.atan) -/
  | float__atan : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.acosh(a)` (Float.acosh) -/
  | float__acosh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.floor(a)` (Float.floor) -/
  | float__floor : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.abs(a)` (Float.abs) -/
  | float__fabs : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Number(a)` (UInt64.toFloat) -/
  | bigint_nat__lean_uint64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .float)
  /-- `a` (UInt64.toFloat) -/
  | uint53__lean_uint64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .float)
  /-- `a < b` (Float.decLt) -/
  | float__lean_float_decLt__Float_decLt : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `a < b` (Float.lt) -/
  | float__lean_float_decLt__Float_lt : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .bool)
  /-- `Math.sin(a)` (Float.sin) -/
  | float__sin : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cosh(a)` (Float.cosh) -/
  | float__cosh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.exp(a)` (Float.exp) -/
  | float__exp : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.ceil(a)` (Float.ceil) -/
  | float__ceil : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.cos(a)` (Float.cos) -/
  | float__cos : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.log2(a)` (Float.log2) -/
  | float__log2 : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atanh(a)` (Float.atanh) -/
  | float__atanh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.atan2(a, b)` (Float.atan2) -/
  | float__atan2 : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `Math.sinh(a)` (Float.sinh) -/
  | float__sinh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.asinh(a)` (Float.asinh) -/
  | float__asinh : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a * b` (Float.mul) -/
  | float__lean_float_mul : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a` (UInt16.toFloat) -/
  | uint16__lean_uint16_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .float)
  /-- `Math.asin(a)` (Float.asin) -/
  | float__asin : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `Math.pow(a, b)` (Float.pow) -/
  | float__pow : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a + b` (Float.add) -/
  | float__lean_float_add : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `a - b` (Float.sub) -/
  | float__lean_float_sub : JsOpInlinable .pure .doesntThrow [(.terminal .float), (.terminal .float)] (.terminal .float)
  /-- `-a` (Float.neg) -/
  | float__lean_float_negate : JsOpInlinable .pure .doesntThrow [(.terminal .float)] (.terminal .float)
  /-- `a` (Int32.toFloat) -/
  | int32__lean_int32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .float)
  /-- `a` (Int16.toFloat) -/
  | int16__lean_int16_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .float)
  /-- `a` (Int8.toFloat) -/
  | int8__lean_int8_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .float)
  /-- `Number(a)` (Int64.toFloat) -/
  | bigint_int__lean_int64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .float)
  /-- `a` (Int64.toFloat) -/
  | int53__lean_int64_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .float)
  /-- `Math.fround(Math.tanh(a))` (Float32.tanh) -/
  | float32__tanhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.pow(2, a))` (Float32.exp2) -/
  | float32__exp2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.log(a))` (Float32.log) -/
  | float32__logf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a <= b` (Float32.le) -/
  | float32__lean_float32_decLe__Float32_le : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a <= b` (Float32.decLe) -/
  | float32__lean_float32_decLe__Float32_decLe : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (Float32.toModel) -/
  | float32__lean_float32_to_bits__Float32_toModel : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Float32.ofModel) -/
  | float32__lean_float32_of_bits__Float32_ofModel : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.atan(a))` (Float32.atan) -/
  | float32__atanf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.acosh(a))` (Float32.acosh) -/
  | float32__acoshf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.asin(a))` (Float32.asin) -/
  | float32__asinf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.pow(a, b))` (Float32.pow) -/
  | float32__powf : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- `a === b` (Float32.beq) -/
  | float32__lean_float32_beq : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a` (UInt8.toFloat32) -/
  | uint8__lean_uint8_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint8)] (.terminal .float32)
  /-- `Math.fround(Math.tan(a))` (Float32.tan) -/
  | float32__tanf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Float32.toFloat) -/
  | float32__lean_float32_to_float : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float)
  /-- `Math.fround(Math.log10(a))` (Float32.log10) -/
  | float32__log10f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.cbrt(a))` (Float32.cbrt) -/
  | float32__cbrtf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.atan2(a, b))` (Float32.atan2) -/
  | float32__atan2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sinh(a))` (Float32.sinh) -/
  | float32__sinhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.cos(a))` (Float32.cos) -/
  | float32__cosf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (UInt32.toFloat32) -/
  | uint32__lean_uint32_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint32)] (.terminal .float32)
  /-- `-a` (Float32.neg) -/
  | float32__lean_float32_negate : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.ceil(a)` (Float32.ceil) -/
  | float32__ceilf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sin(a))` (Float32.sin) -/
  | float32__sinf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.asinh(a))` (Float32.asinh) -/
  | float32__asinhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.log2(a))` (Float32.log2) -/
  | float32__log2f : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | bigint_nat__lean_uint64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_nat)] (.terminal .float32)
  /-- `Number(a)` (UInt64.toFloat32) -/
  | uint53__lean_uint64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint53)] (.terminal .float32)
  /-- `Math.fround(Math.atanh(a))` (Float32.atanh) -/
  | float32__atanhf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.floor(a)` (Float32.floor) -/
  | float32__floorf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.abs(a)` (Float32.abs) -/
  | float32__fabsf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a < b` (Float32.lt) -/
  | float32__lean_float32_decLt__Float32_lt : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `a < b` (Float32.decLt) -/
  | float32__lean_float32_decLt__Float32_decLt : JsOpInlinable .pure .doesntThrow [(.terminal .float32), (.terminal .float32)] (.terminal .bool)
  /-- `Math.fround(Math.acos(a))` (Float32.acos) -/
  | float32__acosf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.sqrt(a))` (Float32.sqrt) -/
  | float32__sqrtf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (UInt16.toFloat32) -/
  | uint16__lean_uint16_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .uint16)] (.terminal .float32)
  /-- `Math.fround(Math.cosh(a))` (Float32.cosh) -/
  | float32__coshf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `Math.fround(Math.exp(a))` (Float32.exp) -/
  | float32__expf : JsOpInlinable .pure .doesntThrow [(.terminal .float32)] (.terminal .float32)
  /-- `a` (Int32.toFloat32) -/
  | int32__lean_int32_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int32)] (.terminal .float32)
  /-- `a` (Int8.toFloat32) -/
  | int8__lean_int8_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int8)] (.terminal .float32)
  /-- `a` (Int16.toFloat32) -/
  | int16__lean_int16_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int16)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | bigint_int__lean_int64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .bigint_int)] (.terminal .float32)
  /-- `Number(a)` (Int64.toFloat32) -/
  | int53__lean_int64_to_float32 : JsOpInlinable .pure .doesntThrow [(.terminal .int53)] (.terminal .float32)

/-- The names of the constructors of `JsOpInlinable`, in order. -/
def JsOpInlinable.names : Array String := ctor_names% JsOpInlinable

/-- The name of the operation (the name of its constructor). -/
def JsOpInlinable.name {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpInlinable e t σs τ) : String :=
  JsOpInlinable.names[op.ctorIdx]!

namespace JsOpImported

/-- The globals passed before the arguments (the constructor of a typed array). -/
def extraArgs {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} :
    JsOpImported e t σs τ → List String
  | .typedArray__bigint_nat__lean_mk_array t => [t.kind.ctorName]
  | .typedArray__uint53__lean_mk_array t => [t.kind.ctorName]
  | _ => []

/-- The version of an array update that updates the array in place, if it has one. -/
def toMutable? {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} :
    JsOpImported e t σs τ → Option (Σ t' : MayThrow, JsOpImported .effectful t' σs τ)
  | .array__lean_array_push_immutable (.generic α) => some ⟨_, .array__lean_array_push_mutable α⟩
  | .array__lean_array_pop_immutable (.generic α) => some ⟨_, .array__lean_array_pop_mutable α⟩
  | .bigint_nat__lean_array_set_immutable l => some ⟨_, .bigint_nat__lean_array_set_mutable l⟩
  | .uint53__lean_array_set_immutable l => some ⟨_, .uint53__lean_array_set_mutable l⟩
  | .bigint_nat__lean_array_swap_immutable l => some ⟨_, .bigint_nat__lean_array_swap_mutable l⟩
  | .uint53__lean_array_swap_immutable l => some ⟨_, .uint53__lean_array_swap_mutable l⟩
  | _ => none

end JsOpImported

/-- The JavaScript of an inlined operation, over its arguments. -/
def JsOpInlinable.template {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} :
    JsOpInlinable e t σs τ → JsInline
  | .bigint_nat__lean_array_get_size _ => .call "BigInt" [.member (.arg 0) "length"]
  | .uint53__lean_array_get_size _ => .member (.arg 0) "length"
  | .array__lean_array_to_list _ => .arg 0
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t => .new t.kind.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_emptyWithCapacity t => .new t.kind.ctorName [.num 0]
  | .bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__bigint_nat__lean_mk_empty_array_with_capacity__Array_mkEmpty t => .new t.kind.ctorName [.num 0]
  | .uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty _ => .emptyArray
  | .typedArray__uint53__lean_mk_empty_array_with_capacity__Array_mkEmpty t => .new t.kind.ctorName [.num 0]
  | .array__lean_array_mk _ => .arg 0
  | .typedArray__lean_array_mk t => .call (t.kind.ctorName ++ ".from") [.arg 0]
  | .bitvec32__lean_uint32_of_nat_mk => .arg 0
  | .uint32__lean_uint32_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_nat__UInt8_toBitVec => .arg 0
  | .bigint_nat__lean_nat_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint32__lean_uint32_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_eq__Nat_decEq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_eq__Nat_decEq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_eq__Nat_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_eq__Nat_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_le__Nat_ble => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_le__Nat_ble => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_dec_le__Nat_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_nat_dec_le__Nat_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_add => .bin "+" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_nat__UInt16_toBitVec => .arg 0
  | .bitvec16__lean_uint16_of_nat_mk => .arg 0
  | .uint16__lean_uint16_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .string__lean_string_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .arg 0
  | .uint53__bigint_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .call "BigInt" [.arg 0]
  | .uint53__int53_bitvec64__lean_uint64_to_nat__UInt64_toBitVec => .arg 0
  | .bigint_bitvec64__bigint_nat__lean_uint64_of_nat_mk => .arg 0
  | .int53_bitvec64__bigint_nat__lean_uint64_of_nat_mk => .call "BigInt" [.arg 0]
  | .int53_bitvec64__uint53__lean_uint64_of_nat_mk => .arg 0
  | .bigint_nat__lean_uint32_to_nat__UInt32_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint32_to_nat__UInt32_toNat => .arg 0
  | .uint32__lean_uint32_to_nat__UInt32_toBitVec => .arg 0
  | .bigint_nat__lean_uint64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bitvec8__lean_uint8_of_nat_mk => .arg 0
  | .uint8__lean_uint8_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_mul => .bin "*" (.arg 0) (.arg 1)
  | .bool__lean_strict_or => .bin "||" (.arg 0) (.arg 1)
  | .bool__lean_strict_and => .bin "&&" (.arg 0) (.arg 1)
  | .bigint_nat__bigint_int__lean_nat_to_int => .arg 0
  | .uint53__bigint_int__lean_nat_to_int => .call "BigInt" [.arg 0]
  | .uint53__int53__lean_nat_to_int => .arg 0
  | .bigint_int__lean_int_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int53__lean_int_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_mul => .bin "*" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_dec_nonneg => .bin ">=" (.arg 0) (.big 0)
  | .int53__lean_int_dec_nonneg => .bin ">=" (.arg 0) (.num 0)
  | .bigint_int__lean_int_add => .bin "+" (.arg 0) (.arg 1)
  | .bigint_int__lean_int_neg => .un "-" (.arg 0)
  | .bigint_int__lean_int_sub => .bin "-" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_lxor => .bin "^" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_shiftl => .bin "<<" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_shiftr => .bin ">>" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_land => .bin "&" (.arg 0) (.arg 1)
  | .bigint_nat__lean_nat_lor => .bin "|" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_to_nat__UInt64_toNat => .arg 0
  | .uint53__bigint_nat__lean_uint64_to_nat__UInt64_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint64_to_nat__UInt64_toNat => .arg 0
  | .uint16__lean_uint16_to_uint32 => .arg 0
  | .bigint_nat__lean_uint32_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint32_to_uint64 => .arg 0
  | .bigint_nat__lean_uint16_to_nat__UInt16_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_nat__UInt16_toNat => .arg 0
  | .bigint_nat__lean_uint8_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_uint64 => .arg 0
  | .bigint_nat__lean_uint8_to_nat__UInt8_toNat => .call "BigInt" [.arg 0]
  | .uint53__lean_uint8_to_nat__UInt8_toNat => .arg 0
  | .uint8__lean_uint8_to_uint32 => .arg 0
  | .bigint_nat__lean_uint16_to_uint64 => .call "BigInt" [.arg 0]
  | .uint53__lean_uint16_to_uint64 => .arg 0
  | .uint8__lean_uint8_to_uint16 => .arg 0
  | .uint16__lean_uint16_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_nat__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint53__lean_uint64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int8__lean_int8_to_int16 => .arg 0
  | .int8__lean_int8_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int8__lean_int8_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int8__lean_int8_to_int32 => .arg 0
  | .bigint_int__lean_int8_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int8_to_int64 => .arg 0
  | .int8__lean_int8_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int8_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int8_to_int => .arg 0
  | .int16__lean_int16_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int16__lean_int16_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int16_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int16_to_int => .arg 0
  | .int16__lean_int16_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int16__lean_int16_to_int32 => .arg 0
  | .bigint_int__lean_int16_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int16_to_int64 => .arg 0
  | .int32__lean_int32_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int32_to_int64 => .call "BigInt" [.arg 0]
  | .int53__lean_int32_to_int64 => .arg 0
  | .int32__lean_int32_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int32__lean_int32_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int32_to_int => .call "BigInt" [.arg 0]
  | .int53__lean_int32_to_int => .arg 0
  | .bigint_int__lean_int64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_eq => .bin "===" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .int53__lean_int64_dec_le => .bin "<=" (.arg 0) (.arg 1)
  | .bigint_int__lean_int64_to_int_sint => .arg 0
  | .int53__bigint_int__lean_int64_to_int_sint => .call "BigInt" [.arg 0]
  | .int53__lean_int64_to_int_sint => .arg 0
  | .string__lean_string_append__String_Internal_append => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_push => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_append__String_append => .bin "+" (.arg 0) (.arg 1)
  | .string__lean_string_dec_lt => .bin "<" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_float => .arg 0
  | .float__lean_float_to_bits__Float_toModel => .arg 0
  | .float__lean_float_of_bits__Float_ofModel => .arg 0
  | .float__log10 => .call "Math.log10" [.arg 0]
  | .float__cbrt => .call "Math.cbrt" [.arg 0]
  | .float__log => .call "Math.log" [.arg 0]
  | .float__lean_float_div => .bin "/" (.arg 0) (.arg 1)
  | .float__lean_float_beq => .bin "===" (.arg 0) (.arg 1)
  | .float__tan => .call "Math.tan" [.arg 0]
  | .float__tanh => .call "Math.tanh" [.arg 0]
  | .float__exp2 => .call "Math.pow" [.num 2, .arg 0]
  | .uint32__lean_uint32_to_float => .arg 0
  | .float__lean_float_decLe__Float_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float__lean_float_decLe__Float_le => .bin "<=" (.arg 0) (.arg 1)
  | .float__sqrt => .call "Math.sqrt" [.arg 0]
  | .float__acos => .call "Math.acos" [.arg 0]
  | .float__atan => .call "Math.atan" [.arg 0]
  | .float__acosh => .call "Math.acosh" [.arg 0]
  | .float__floor => .call "Math.floor" [.arg 0]
  | .float__fabs => .call "Math.abs" [.arg 0]
  | .bigint_nat__lean_uint64_to_float => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float => .arg 0
  | .float__lean_float_decLt__Float_decLt => .bin "<" (.arg 0) (.arg 1)
  | .float__lean_float_decLt__Float_lt => .bin "<" (.arg 0) (.arg 1)
  | .float__sin => .call "Math.sin" [.arg 0]
  | .float__cosh => .call "Math.cosh" [.arg 0]
  | .float__exp => .call "Math.exp" [.arg 0]
  | .float__ceil => .call "Math.ceil" [.arg 0]
  | .float__cos => .call "Math.cos" [.arg 0]
  | .float__log2 => .call "Math.log2" [.arg 0]
  | .float__atanh => .call "Math.atanh" [.arg 0]
  | .float__atan2 => .call "Math.atan2" [.arg 0, .arg 1]
  | .float__sinh => .call "Math.sinh" [.arg 0]
  | .float__asinh => .call "Math.asinh" [.arg 0]
  | .float__lean_float_mul => .bin "*" (.arg 0) (.arg 1)
  | .uint16__lean_uint16_to_float => .arg 0
  | .float__asin => .call "Math.asin" [.arg 0]
  | .float__pow => .call "Math.pow" [.arg 0, .arg 1]
  | .float__lean_float_add => .bin "+" (.arg 0) (.arg 1)
  | .float__lean_float_sub => .bin "-" (.arg 0) (.arg 1)
  | .float__lean_float_negate => .un "-" (.arg 0)
  | .int32__lean_int32_to_float => .arg 0
  | .int16__lean_int16_to_float => .arg 0
  | .int8__lean_int8_to_float => .arg 0
  | .bigint_int__lean_int64_to_float => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float => .arg 0
  | .float32__tanhf => .call "Math.fround" [.call "Math.tanh" [.arg 0]]
  | .float32__exp2f => .call "Math.fround" [.call "Math.pow" [.num 2, .arg 0]]
  | .float32__logf => .call "Math.fround" [.call "Math.log" [.arg 0]]
  | .float32__lean_float32_decLe__Float32_le => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLe__Float32_decLe => .bin "<=" (.arg 0) (.arg 1)
  | .float32__lean_float32_to_bits__Float32_toModel => .arg 0
  | .float32__lean_float32_of_bits__Float32_ofModel => .arg 0
  | .float32__atanf => .call "Math.fround" [.call "Math.atan" [.arg 0]]
  | .float32__acoshf => .call "Math.fround" [.call "Math.acosh" [.arg 0]]
  | .float32__asinf => .call "Math.fround" [.call "Math.asin" [.arg 0]]
  | .float32__powf => .call "Math.fround" [.call "Math.pow" [.arg 0, .arg 1]]
  | .float32__lean_float32_beq => .bin "===" (.arg 0) (.arg 1)
  | .uint8__lean_uint8_to_float32 => .arg 0
  | .float32__tanf => .call "Math.fround" [.call "Math.tan" [.arg 0]]
  | .float32__lean_float32_to_float => .arg 0
  | .float32__log10f => .call "Math.fround" [.call "Math.log10" [.arg 0]]
  | .float32__cbrtf => .call "Math.fround" [.call "Math.cbrt" [.arg 0]]
  | .float32__atan2f => .call "Math.fround" [.call "Math.atan2" [.arg 0, .arg 1]]
  | .float32__sinhf => .call "Math.fround" [.call "Math.sinh" [.arg 0]]
  | .float32__cosf => .call "Math.fround" [.call "Math.cos" [.arg 0]]
  | .uint32__lean_uint32_to_float32 => .arg 0
  | .float32__lean_float32_negate => .un "-" (.arg 0)
  | .float32__ceilf => .call "Math.ceil" [.arg 0]
  | .float32__sinf => .call "Math.fround" [.call "Math.sin" [.arg 0]]
  | .float32__asinhf => .call "Math.fround" [.call "Math.asinh" [.arg 0]]
  | .float32__log2f => .call "Math.fround" [.call "Math.log2" [.arg 0]]
  | .bigint_nat__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .uint53__lean_uint64_to_float32 => .call "Number" [.arg 0]
  | .float32__atanhf => .call "Math.fround" [.call "Math.atanh" [.arg 0]]
  | .float32__floorf => .call "Math.floor" [.arg 0]
  | .float32__fabsf => .call "Math.abs" [.arg 0]
  | .float32__lean_float32_decLt__Float32_lt => .bin "<" (.arg 0) (.arg 1)
  | .float32__lean_float32_decLt__Float32_decLt => .bin "<" (.arg 0) (.arg 1)
  | .float32__acosf => .call "Math.fround" [.call "Math.acos" [.arg 0]]
  | .float32__sqrtf => .call "Math.fround" [.call "Math.sqrt" [.arg 0]]
  | .uint16__lean_uint16_to_float32 => .arg 0
  | .float32__coshf => .call "Math.fround" [.call "Math.cosh" [.arg 0]]
  | .float32__expf => .call "Math.fround" [.call "Math.exp" [.arg 0]]
  | .int32__lean_int32_to_float32 => .arg 0
  | .int8__lean_int8_to_float32 => .arg 0
  | .int16__lean_int16_to_float32 => .arg 0
  | .bigint_int__lean_int64_to_float32 => .call "Number" [.arg 0]
  | .int53__lean_int64_to_float32 => .call "Number" [.arg 0]

end MoreJs

end
