module

public import LeanScript.Ty.Syntax.LeanPrimTy

@[expose] public section

set_option autoImplicit false

/-!
# The configuration: how each Lean type is represented in JavaScript

`LeanScript.Term` models *Lean* code: its leaves are `LeanPrimTy`s, whose values are Lean
values (`Nat`, `UInt64`, …).  `JsTerm` models *JavaScript* code, and a Lean type can be
represented in more than one way there.  The choice is this configuration:

| Lean | JavaScript | knob |
| --- | --- | --- |
| `Nat` | a number (`UInt53`) or a `BigInt` | `natRepr` |
| `Int` | a number (`Int53`) or a `BigInt` | `intRepr` |
| `UInt64` | a number (`UInt53`) or a `BigInt` | `uint64Repr` |
| `Int64` | a number (`Int53`) or a `BigInt` | `int64Repr` |
| `BitVec n`, `n > 53` | a number (`UInt53`) or a `BigInt` | `bitvecRepr` |
| `BitVec n`, `n ≤ 53` | always a number | — |
| `UInt8/16/32`, `Int8/16/32` | always a number | — |
| `Float`, `Float32` | always a number | — |
| `String.Pos.Raw` | always a number (a UTF-8 byte offset) | — |
| `Char` | always a one-character string | — |
| `Bool` | always a JavaScript boolean | — |
| `String` | always a JavaScript string | — |
| `Array α` | a JavaScript array, or a typed array (the `array…Repr` knobs; `Array Bool` and `Array Char` are always generic) | `array…Repr` |
| `List α` (the standard library's) | tagged cons cells `{ tag: 0 }` / `{ tag: 1, _1: head, _2: tail }`, or an immutable JavaScript array | `listRepr` |

A number representation of an unbounded type (`Nat` as `UInt53`) is only faithful below
`2^53`: a literal that does not fit is refused when the term is converted
(`JsTerm.Lower.FromTerm`), and the arithmetic of the generated runtime throws a `RangeError`
instead of silently losing precision.

`JsConfig.reprOfPrim` answers the question for *every* constructor of `LeanPrimTy`, with no
catch-all case, so a terminal type added to the language has to be given a representation
here before this module builds; `JsConfig.knobOfPrim?` says which knob decides it.
-/

namespace MoreJs

open LeanScript

/-- How a numeric Lean type is represented: as a JavaScript number, or as a `BigInt`. -/
inductive JsNumRepr where
  /-- A JavaScript number (a double): fast, exact only below `2^53`. -/
  | num
  /-- A JavaScript `BigInt`: exact at every size, and a different JavaScript type — a
      `BigInt` is never `===` to a number and mixing the two throws. -/
  | bigint
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Whether to prefer a dedicated JS TypedArray or a standard generic `Array<T>`. -/
inductive ArrayTypedOrGeneric where
  /-- Use a typed array (e.g. `Uint8Array`, `Float64Array`). -/
  | typedArray
  /-- Use a generic JavaScript `Array<T>`. -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array UInt64` in JS. -/
inductive ArrayUint64Repr where
  /-- JavaScript `BigUint64Array`. Elements are JS `bigint` (only when `uint64Repr` is
      `bigint`; otherwise the array is generic). -/
  | bigUint64Array
  /-- Generic JS array (`Array<bigint>` or `Array<number>` per `uint64Repr`). -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array Int64` in JS. -/
inductive ArrayInt64Repr where
  /-- JavaScript `BigInt64Array`. Elements are JS `bigint` (only when `int64Repr` is
      `bigint`; otherwise the array is generic). -/
  | bigInt64Array
  /-- Generic JS array (`Array<bigint>` or `Array<number>` per `int64Repr`). -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Strategy for modeling `Array (BitVec n)` in JS. -/
inductive ArrayBitVecRepr where
  /-- Rounds up non-power-of-two widths to the smallest fitting typed array:
      `1..8` ⇒ `Uint8Array`, `9..16` ⇒ `Uint16Array`, `17..32` ⇒ `Uint32Array`,
      `33..64` ⇒ `BigUint64Array` (if `bitvecRepr = .bigint`), `> 64` ⇒ generic. -/
  | roundUpToSmallestTypedArray
  /-- Only exact powers of 2 (8, 16, 32, 64) use typed arrays; odd widths stay generic. -/
  | exactTypedArrayOnly
  /-- All `BitVec` arrays are generic `Array<T>`. -/
  | genericArray
  deriving Repr, DecidableEq, BEq, Inhabited

-- /-- Strategy for modeling `Array Bool` in JS. -/
-- inductive ArrayBoolRepr where
--   /-- Standard JS `Array<boolean>`. -/
--   | genericArray
--   /-- Byte buffer `Uint8Array` (stores `0` or `1` per byte). -/
--   | uint8Array
--   deriving Repr, DecidableEq, BEq, Inhabited
--
-- /-- Strategy for modeling `Array Char` in JS. -/
-- inductive ArrayCharRepr where
--   /-- `Array<string>` where each element is a one-character string. -/
--   | genericArray
--   /-- `Uint32Array` holding the Unicode scalar values. -/
--   | uint32Array
--   deriving Repr, DecidableEq, BEq, Inhabited

-- (`Array Bool` and `Array Char` are always generic JavaScript arrays for now:
-- `Array<boolean>` and `Array<string>` of one-character strings.)

/-- Strategy for representing Lean `List` and list-like inductive types in JavaScript. -/
inductive ListRepr where
  /-- Default: Emit lists as standard tagged union cons-cells:
      `def x = [1, 2, 3]` is rendered as:
      `const k0 = { tag: 0 }; export const x = { tag: 1, _1: 1, _2: { tag: 1, _1: 2, _2: { tag: 1, _1: 3, _2: k0 } } };`
      This guarantees `O(1)` tail-sharing for all functional list operations. -/
  | taggedUnion -- default in faithful preset

  /--
    Emit the standard library `List` as a native JavaScript `Array` (`[...]`).
    This concerns only `List` from `Std` (even when elements are shared/used non-linearly),
    non `Std` `List`-like tagged unions
    (e.g. `inductive MyList (α : Type u) where | nil : MyList α | cons (head : α) (tail : MyList α) : MyList α`)
    should always be converted to tagged union.
  -/
  | stdListToJsArray -- default in pbo preset
  deriving Repr, DecidableEq, BEq, Inhabited

/-- The configuration of the backend: every representation decision, in one record.  The
    default keeps Lean's semantics exactly (`BigInt` wherever a knob allows one). -/
structure JsConfig where
  /-- How `Nat` is represented. -/
  natRepr : JsNumRepr := .bigint
  /-- How `Int` is represented. -/
  intRepr : JsNumRepr := .bigint
  /-- How `UInt64` is represented. -/
  uint64Repr : JsNumRepr := .bigint
  /-- How `Int64` is represented. -/
  int64Repr : JsNumRepr := .bigint
  /-- How a bit vector of `n > 53` bits is represented.  A narrower one fits in a number
      exactly and is one whatever this says. -/
  bitvecRepr : JsNumRepr := .bigint
  /-- How fixed-width 8/16/32-bit integer arrays are modeled. -/
  arrayFixedIntRepr : ArrayTypedOrGeneric := .typedArray
  /-- How `Array UInt64` is modeled. -/
  arrayUint64Repr : ArrayUint64Repr := .bigUint64Array
  /-- How `Array Int64` is modeled. -/
  arrayInt64Repr : ArrayInt64Repr := .bigInt64Array
  /-- How `Array (BitVec n)` is modeled. -/
  arrayBitVecRepr : ArrayBitVecRepr := .roundUpToSmallestTypedArray
  /-- How `Array Float` and `Array Float32` are modeled. -/
  arrayFloatRepr : ArrayTypedOrGeneric := .typedArray
  /-- Strategy for representing `List` and list-like inductive types in JS. -/
  listRepr : ListRepr := .taggedUnion
  deriving Repr, DecidableEq, Inhabited

namespace JsConfig

/-- The default configuration: a `BigInt` everywhere a knob allows one. -/
def default : JsConfig := {}

/-- Everything that can be a number is a number, and every array is a generic array: the
    representation `purescript-backend-optimizer` uses. -/
def presetPBO : JsConfig where
  natRepr := .num
  intRepr := .num
  uint64Repr := .num
  int64Repr := .num
  bitvecRepr := .num
  arrayFixedIntRepr := .genericArray
  arrayUint64Repr := .genericArray
  arrayInt64Repr := .genericArray
  arrayBitVecRepr := .genericArray
  arrayFloatRepr := .genericArray
  listRepr := .stdListToJsArray

/-- The representation that keeps Lean's semantics exactly: `BigInt` everywhere an
    unbounded or 64-bit integer can appear (the default). -/
def presetFaithful : JsConfig := {}

/-- The configuration a preset name denotes, as the command line spells it. -/
def ofPresetName? : String → Option JsConfig
  | "pbo" => some presetPBO
  | "faithful" => some presetFaithful
  | _ => none

/-- Which knob decides a terminal type, named as the command line spells it; `none` where
    the type has one representation only.  Every constructor of `LeanPrimTy` is listed:
    there is no catch-all, so a new terminal type must be classified here. -/
def knobOfPrim? : LeanPrimTy → Option String
  | .nat => some "nat"
  | .int => some "int"
  | .uint64 => some "uint64"
  | .int64 => some "int64"
  | .bitvec n _ => if 53 < n then some "bitvec" else none
  | .bool | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => none
  | .char | .string | .stringPos _ _ | .stringPosRaw | .substringRaw | .stringSlice => none
  | .float | .float32 | .floatModel | .float32Model => none

/-- How a *terminal* type is represented.  There is no catch-all case. -/
def reprOfPrim (cfg : JsConfig) : LeanPrimTy → JsNumRepr
  | .nat => cfg.natRepr
  | .int => cfg.intRepr
  | .uint64 => cfg.uint64Repr
  | .int64 => cfg.int64Repr
  | .bitvec n _ => if 53 < n then cfg.bitvecRepr else .num
  | .bool | .uint8 | .uint16 | .uint32 | .int8 | .int16 | .int32 => .num
  | .char | .string | .stringPos _ _ | .stringPosRaw | .substringRaw | .stringSlice => .num
  | .float | .float32 | .floatModel | .float32Model => .num

/-- How a numeric representation is spelled on the command line. -/
def reprName : JsNumRepr → String
  | .num => "num"
  | .bigint => "bigint"

/-- A numeric representation, from its spelling. -/
def reprOfName? : String → Option JsNumRepr
  | "num" | "number" => some .num
  | "bigint" => some .bigint
  | _ => none

/-- Set a knob by the name the command line spells it with. -/
def setKnob? (cfg : JsConfig) (knob val : String) : Option JsConfig := do
  match knob with
  | "nat" => return { cfg with natRepr := ← reprOfName? val }
  | "int" => return { cfg with intRepr := ← reprOfName? val }
  | "uint64" => return { cfg with uint64Repr := ← reprOfName? val }
  | "int64" => return { cfg with int64Repr := ← reprOfName? val }
  | "bitvec" => return { cfg with bitvecRepr := ← reprOfName? val }
  | "array-fixed-int" => match val with
    | "typed" => return { cfg with arrayFixedIntRepr := .typedArray }
    | "generic" => return { cfg with arrayFixedIntRepr := .genericArray }
    | _ => none
  | "array-float" => match val with
    | "typed" => return { cfg with arrayFloatRepr := .typedArray }
    | "generic" => return { cfg with arrayFloatRepr := .genericArray }
    | _ => none
  | "array-uint64" => match val with
    | "typed" => return { cfg with arrayUint64Repr := .bigUint64Array }
    | "generic" => return { cfg with arrayUint64Repr := .genericArray }
    | _ => none
  | "array-int64" => match val with
    | "typed" => return { cfg with arrayInt64Repr := .bigInt64Array }
    | "generic" => return { cfg with arrayInt64Repr := .genericArray }
    | _ => none
  | "array-bitvec" => match val with
    | "round-up" => return { cfg with arrayBitVecRepr := .roundUpToSmallestTypedArray }
    | "exact" => return { cfg with arrayBitVecRepr := .exactTypedArrayOnly }
    | "generic" => return { cfg with arrayBitVecRepr := .genericArray }
    | _ => none
  | "list" => match val with
    | "tagged" | "tagged-union" => return { cfg with listRepr := .taggedUnion }
    | "array" | "js-array" => return { cfg with listRepr := .stdListToJsArray }
    | _ => none
  | _ => none

/-- How a list representation is spelled on the command line. -/
def listReprName : ListRepr → String
  | .taggedUnion => "tagged"
  | .stdListToJsArray => "array"

/-- The configuration in one line, as the command line spells it.  This is what the header
    of every generated file says, so an output can be traced back to its settings. -/
def describe (cfg : JsConfig) : String :=
  let typed (b : Bool) := if b then "typed" else "generic"
  String.intercalate " "
    [ "nat=" ++ reprName cfg.natRepr, "int=" ++ reprName cfg.intRepr,
      "uint64=" ++ reprName cfg.uint64Repr, "int64=" ++ reprName cfg.int64Repr,
      "bitvec=" ++ reprName cfg.bitvecRepr,
      "array-fixed-int=" ++ typed (cfg.arrayFixedIntRepr == .typedArray),
      "array-float=" ++ typed (cfg.arrayFloatRepr == .typedArray),
      "array-uint64=" ++ typed (cfg.arrayUint64Repr == .bigUint64Array),
      "array-int64=" ++ typed (cfg.arrayInt64Repr == .bigInt64Array),
      "array-bitvec=" ++ (match cfg.arrayBitVecRepr with
        | .roundUpToSmallestTypedArray => "round-up" | .exactTypedArrayOnly => "exact"
        | .genericArray => "generic"),
      "list=" ++ listReprName cfg.listRepr ]

end JsConfig

example : JsConfig.knobOfPrim? .nat = some "nat" := rfl
example : JsConfig.knobOfPrim? (.bitvec 64) = some "bitvec" := by decide
example : JsConfig.knobOfPrim? (.bitvec 53) = none := by decide
example : JsConfig.reprOfPrim .presetPBO .nat = .num := rfl
example : JsConfig.reprOfPrim .default .uint64 = .bigint := rfl

end MoreJs

end
