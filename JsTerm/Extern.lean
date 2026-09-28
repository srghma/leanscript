module

public import JsTerm.Syntax
public import LeanScript.Term.Extern.Name

@[expose] public section

set_option autoImplicit false

/-!
# Externs in JavaScript

A call of an extern of the catalogue (`LeanScript.Neu.extern`) becomes, in JavaScript,

* an **operator** or another short expression, for the externs whose meaning is one at the
  chosen representation (`Nat.add` on `BigInt`s is `a + b`, `Nat.decLt` is `a < b` on
  numbers and on `BigInt`s, `String.append` is `a + b`, `UInt8.toNat` on numbers is the
  argument itself, `Array.emptyWithCapacity` is `[]`, …), or
* a call of a function of the **runtime**: the JavaScript modules of the `runtime/`
  directory, which the generated module imports (`import { $lean_nat_sub } from
  "../runtime/lean_runtime_nat_bigint.mjs";`).  Nothing is generated for them: they are
  ordinary hand-written JavaScript.

## The runtime modules

The runtime is one module per *knob* of the configuration (`JsConfig`) and per choice of that
knob, plus one module that no knob changes (`RtFile`):

| module | what it holds |
| --- | --- |
| `lean_runtime_non_configurable.mjs` | the functions whose result is of a type no knob changes (a `Bool`, a `String`, a `Char`, an array, the fixed-width types below 64 bits, a `Float`, …) |
| `lean_runtime_nat_bigint.mjs`, `lean_runtime_nat_num.mjs` | the functions answering a `Nat`, a `BigInt` or a number |
| `lean_runtime_int_*.mjs`, `lean_runtime_uint64_*.mjs`, `lean_runtime_int64_*.mjs`, `lean_runtime_bitvec_*.mjs` | the same for `Int`, `UInt64`, `Int64` and the bit vectors of more than 53 bits |

A module imports each runtime function from the module of the type the function answers with
(`RtFile.ofResult`); where a function takes an argument of another configurable type, it
accepts either representation of it.  The name of the function is the C symbol of the extern
behind a `$` (`lean_nat_sub` is `$lean_nat_sub`), except for the few symbols that stand for
externs of different meanings (`rtName`).

Which functions a runtime module exports is read off the module itself (`Runtime`): an extern
the runtime has no function for becomes a call of `$lean_extern_unimplemented`, which throws
when it is called, so the rest of the module still loads and runs.
-/

namespace MoreJs

open LeanScript

/-! ## Building terms of the grammar -/

/-- The operator on `number`s of the same name as an operator on `BigInt`s. -/
def JsBigIntBinOp.toNum : JsBigIntBinOp → JsNumBinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor | .shl => .shl | .shr => .shr

namespace Js

/-- A variable. -/
def v (x : String) : JsExpr := .var x
/-- A `number` literal of an integer. -/
def num (n : Int) : JsExpr := .lit (.int n)
/-- A `BigInt` literal. -/
def big (n : Int) : JsExpr := .lit (.bigint n)
/-- An integer literal at the layout `t` (a `BigInt` or a `number`). -/
def intAt (t : JsTerm) (n : Int) : JsExpr := if t.isBigInt then big n else num n
/-- A string literal. -/
def str (s : String) : JsExpr := .lit (.str s)
/-- `f(args)`, for a global function `f` (`BigInt`, `Number`, …). -/
def call (f : String) (args : List JsExpr) : JsExpr := .call (.var f) args
/-- `o.m(args)`. -/
def meth (o : JsExpr) (m : String) (args : List JsExpr) : JsExpr := .call (.member o m) args

end Js

open Js

/-- A JavaScript typed array constructor for a layout, if it is a typed array. -/
def typedCtor? : JsTerm → Option String
  | .uint8Array => some "Uint8Array" | .uint16Array => some "Uint16Array"
  | .uint32Array => some "Uint32Array" | .int8Array => some "Int8Array"
  | .int16Array => some "Int16Array" | .int32Array => some "Int32Array"
  | .float32Array => some "Float32Array" | .float64Array => some "Float64Array"
  | .bigUint64Array => some "BigUint64Array" | .bigInt64Array => some "BigInt64Array"
  | _ => none

/-! ## The runtime modules -/

/-- The externs whose result is an element of their argument (whatever its type): their
    runtime function does not depend on the representation of the result. -/
def polymorphicResult : List String :=
  ["lean_array_get", "lean_array_get_borrowed", "lean_thunk_get_own"]

/-- The module of the runtime function of the extern of C symbol `sym`, whose result has the
    layout `resTy` and is of the configurable type of knob `resKnob` (if any). -/
def RtFile.ofResult (sym : String) (resKnob : Option RtKnob) (resTy : JsTerm) : RtFile :=
  if polymorphicResult.contains sym then .nonConfigurable else
  match resKnob with
  | some k => .knob k resTy.isBigInt
  | none => .nonConfigurable

/-- Which functions each runtime module exports. -/
structure Runtime where
  /-- Does the module export a function of this name? -/
  has : RtFile → String → Bool

/-- A runtime assumed to export every function the backend asks for (for the unit tests). -/
def Runtime.trusting : Runtime := ⟨fun _ _ => true⟩

instance : Inhabited Runtime := ⟨Runtime.trusting⟩

/-- The names a JavaScript module exports as `export const NAME`, `export function NAME` or
    `export let NAME` at the start of a line. -/
def exportedNames (src : String) : List String :=
  (src.splitOn "\n").filterMap fun line =>
    let rest? := ["export const ", "export function ", "export let "].findSome? fun p =>
      (line.dropPrefix? p).map (·.toString)
    rest?.bind fun rest =>
      let name := String.ofList (rest.toList.takeWhile fun c => c.isAlphanum || c == '_' || c == '$')
      if name.isEmpty then none else some name

/-- The runtime of the exports of each module (`(file name, source)` pairs). -/
def Runtime.ofSources (srcs : List (String × String)) : Runtime :=
  let table := srcs.map fun (f, s) => (f, exportedNames s)
  ⟨fun file n => match table.lookup file.fileName with
    | some ns => ns.contains n
    | none => false⟩

/-- The function that throws in place of an extern the runtime has no function for. -/
def unimplementedFn : RtFn := { file := .nonConfigurable, name := "$lean_extern_unimplemented" }

/-! ## The externs -/

/-- The name of the runtime function of an extern: `$` and its C symbol, except where one
    symbol stands for externs of different meanings. -/
def rtName (name : String) : String :=
  match name with
  | "lean_uint32_of_nat__Char_ofNatAux" => "Char_ofNatAux"
  | "lean_uint64_to_nat__UInt64_toBitVec" => "UInt64_toBitVec"
  | _ => "$" ++ externSymbol name

/-- The conversions that keep the value (a widening, the value of a bit vector as a
    number, …): each is its argument, converted from its layout to the layout of the result
    (`convValue?`). -/
def valueConversions : List String :=
  ["lean_float32_to_float", "lean_int16_to_float", "lean_int16_to_float32", "lean_int16_to_int",
   "lean_int16_to_int32", "lean_int16_to_int64", "lean_int32_to_float", "lean_int32_to_float32",
   "lean_int32_to_int", "lean_int32_to_int64", "lean_int64_to_float", "lean_int64_to_int_sint",
   "lean_int8_to_float", "lean_int8_to_float32", "lean_int8_to_int", "lean_int8_to_int16",
   "lean_int8_to_int32", "lean_int8_to_int64", "lean_nat_to_int", "lean_uint16_of_nat_mk",
   "lean_uint16_to_float", "lean_uint16_to_float32", "lean_uint16_to_nat__UInt16_toBitVec",
   "lean_uint16_to_nat__UInt16_toNat", "lean_uint16_to_uint32", "lean_uint16_to_uint64",
   "lean_uint32_of_nat_mk", "lean_uint32_to_float", "lean_uint32_to_float32",
   "lean_uint32_to_nat__UInt32_toBitVec", "lean_uint32_to_nat__UInt32_toNat",
   "lean_uint32_to_uint64", "lean_uint64_of_nat_mk", "lean_uint64_to_float",
   "lean_uint64_to_nat__UInt64_toBitVec", "lean_uint64_to_nat__UInt64_toNat",
   "lean_uint8_of_nat_mk", "lean_uint8_to_float", "lean_uint8_to_float32",
   "lean_uint8_to_nat__UInt8_toBitVec", "lean_uint8_to_nat__UInt8_toNat", "lean_uint8_to_uint16",
   "lean_uint8_to_uint32", "lean_uint8_to_uint64"]

/-- A value `e` of layout `src` at the layout `dst`, when that needs no check: the value
    itself, `BigInt(e)` from a number to a `BigInt`, `Number(e)` from a `BigInt` to a float.
    From a `BigInt` to a number standing for an integer the value must be checked to fit
    (`none`: the runtime function does it). -/
def convValue? (src dst : JsTerm) (e : JsExpr) : Option JsExpr :=
  match dst with
  | .float | .float32 => some (if src.isBigInt then call "Number" [e] else e)
  | _ =>
    if src.isBigInt == dst.isBigInt then some e
    else if dst.isBigInt then some (call "BigInt" [e])
    else none

/-- The fixed-width operations `lean_<type>_dec_eq` / `_dec_lt` / `_dec_le`: the operation. -/
def fixedCmp? (sym : String) : Option String := do
  let rest ← (sym.dropPrefix? "lean_").map (·.toString)
  let rest ← if rest.startsWith "uint" then some (rest.drop 4).toString
    else if rest.startsWith "int" then some (rest.drop 3).toString else none
  let digits := (rest.takeWhile Char.isDigit).toString
  unless ["8", "16", "32", "64"].contains digits do none
  let op := (rest.drop (digits.length + 1)).toString
  if ["dec_eq", "dec_lt", "dec_le"].contains op then some op else none

/-- The call of an extern, as an expression of the grammar, and the runtime functions it
    calls: an operator or a short expression when its meaning is one at this representation,
    otherwise a call of its runtime function (`$lean_extern_unimplemented` when the runtime
    has none).  `resKnob` is the knob of the type of the result, if it is a configurable one. -/
def lowerExtern (rt : Runtime) (name : String) (argTys : List JsTerm) (resTy : JsTerm)
    (resKnob : Option RtKnob) (args : List JsExpr) : JsExpr × List RtFn :=
  let sym := externSymbol name
  let t0 := argTys.headD .bool
  let bin (o : JsBinOp) : Option JsExpr := match args with
    | [x, y] => some (.bin o x y)
    | _ => none
  let isBig := t0.isBigInt
  -- an arithmetic operator on the representation of the first argument
  let arith (nop : JsNumBinOp) (bop : JsBigIntBinOp) : Option JsExpr :=
    bin (if isBig then .bigint bop else .num nop)
  let arg0 := args.headD (.var "undefined")
  let inline? : Option JsExpr :=
    -- a `Float.Model` (`Float32.Model`) is laid out as the `Float` (`Float32`) it models
    if name ∈ ["lean_float_to_bits__Float_toModel", "lean_float_of_bits__Float_ofModel",
        "lean_float32_to_bits__Float32_toModel", "lean_float32_of_bits__Float32_ofModel"] then
      args.head?
    else if valueConversions.contains name then convValue? t0 resTy arg0 else
    match sym with
    | "lean_nat_add" | "lean_int_add" => if isBig then bin (.bigint .add) else none
    | "lean_nat_mul" | "lean_int_mul" => if isBig then bin (.bigint .mul) else none
    | "lean_int_sub" => if isBig then bin (.bigint .sub) else none
    | "lean_nat_dec_eq" | "lean_int_dec_eq" | "lean_string_dec_eq" | "lean_float_beq" =>
      bin .strictEq
    | "lean_nat_dec_lt" | "lean_int_dec_lt" | "lean_float_decLt" => arith .lt .lt
    | "lean_nat_dec_le" | "lean_int_dec_le" | "lean_float_decLe" => arith .le .le
    | "lean_int_dec_nonneg" =>
      some (.bin (if isBig then .bigint .ge else .num .ge) arg0 (intAt t0 0))
    | "lean_strict_and" => bin (.bool .and)
    | "lean_strict_or" => bin (.bool .or)
    -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one
    -- code point), how `a = b` on `Char` is translated
    | "lean_string_push" => match args with
      | [.lit (.str ""), ch] => some ch
      | _ => bin (.str .concat)
    | "lean_string_append" => bin (.str .concat)
    -- a list and a generic array are both JavaScript arrays
    | "lean_array_mk" => match typedCtor? resTy with
      | some k => some (meth (.var k) "from" [arg0])
      | none => some arg0
    | "lean_array_to_list" => match t0 with
      | .genericArray _ => some arg0
      | _ => none
    | "lean_mk_empty_array_with_capacity" => match typedCtor? resTy with
      | some k => some (.new (.var k) [num 0])
      | none => some (.array [])
    | "lean_float_add" => bin (.num .add)
    | "lean_float_sub" => bin (.num .sub)
    | "lean_float_mul" => bin (.num .mul)
    | "lean_float_div" => bin (.num .div)
    | _ =>
      match fixedCmp? sym with
      | some "dec_eq" => bin .strictEq
      | some "dec_lt" => arith .lt .lt
      | some "dec_le" => arith .le .le
      | _ => none
  match inline? with
  | some e => (e, [])
  | none =>
    -- `Array.replicate` on a typed array takes the constructor of the typed array
    let (fname, args) := match sym, typedCtor? resTy with
      | "lean_mk_array", some k => ("$lean_mk_typed_array", .var k :: args)
      | _, _ => (rtName name, args)
    let f : RtFn := { file := RtFile.ofResult sym resKnob resTy, name := fname }
    if rt.has f.file f.name then (.helper f.name args, [f])
    else (.helper unimplementedFn.name [str name], [unimplementedFn])

end MoreJs

end
