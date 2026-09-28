module

public import JsTerm.Config
public import LeanScript.Term.Syntax.Common

@[expose] public section

set_option autoImplicit false

/-!
# `JsTerm`: the types of the JavaScript grammar

`LeanScript.Ty` describes *Lean* values.  `JsTerm` describes how such a value is laid out
in JavaScript, once the configuration (`MoreJs.JsConfig`) has chosen a representation for
every configurable type: a `Nat` is a `nat` (a non-negative `BigInt`) or a `uint53` (a
non-negative integer `number` below `2^53`), an `Array UInt8` is a `genericArray uint8` or a
`uint8Array`, and so on.

The compound shapes have one layout each:

| `Ty` | `JsTerm` | JavaScript |
| --- | --- | --- |
| `record t fs` | `tuple [t, …]` | an array `[f₀, f₁, …]` |
| `union cs` | `tagged [[fields₀], [fields₁], …]` | an array `[tag, f₀, f₁, …]` |
| `enum s` | `enum n shift` | the number `shift + i` |
| `list t` | `list t` | an (immutable) JavaScript array |
| `fn a b` | `fn a b` | a one-argument function (curried) |
| `thunk t` | `thunk t` | a memoising thunk object (`$thunk`, `$force`) |
| `lazy t` | `lazy t` | a function of no argument |
| `data r` | `data name` | a JavaScript value of the layout of one layer (`dataLayer`) |

`lowerScalarPrim` and `lowerArrayPrim` are the configuration-dependent part: how a leaf, and
an array of leaves, is represented.
-/

namespace MoreJs

open LeanScript

/-- The types of the JavaScript grammar: how a Lean value is laid out in JavaScript. -/
inductive JsTerm where
  /-- A JavaScript `boolean`. -/
  | bool
  /-- A non-negative `BigInt` (an unbounded natural number). -/
  | nat
  /-- A non-negative integer `number` below `2^53`. -/
  | uint53
  /-- A `BigInt` (an unbounded integer). -/
  | int
  /-- An integer `number` of absolute value below `2^53`. -/
  | int53
  /-- A bit vector of at most 53 bits, as a `number`. -/
  | bitvec_small (n : Nat) (h_le_53 : n ≤ 53) (h_pos : 0 < n)
  /-- A bit vector of more than 53 bits, as a `BigInt`. -/
  | bitvec_big (n : Nat) (h_gt_53 : 53 < n)
  /-- Fixed-width integers that always fit in a `number`. -/
  | uint8 | uint16 | uint32 | int8 | int16 | int32
  /-- A 64-bit IEEE float, a `number`. -/
  | float
  /-- A 32-bit IEEE float, a `number` (rounded by `Math.fround`). -/
  | float32
  /-- A JavaScript `string` (also a `Char`, as a string of one code point). -/
  | string
  /-- A `Substring.Raw`: `[str, startPos, stopPos]`. -/
  | substring
  /-- A `String.Slice`: `[str, startPos, stopPos]`. -/
  | stringSlice
  /-- A value the JavaScript runtime only passes around (`Float.Model`, …). -/
  | opaque (name : String)
  /-- A generic JavaScript `Array`. -/
  | genericArray (elem : JsTerm)
  /-- The typed arrays. -/
  | uint8Array | uint16Array | uint32Array | int8Array | int16Array | int32Array
  | float32Array | float64Array | bigUint64Array | bigInt64Array
  /-- A Lean `List`, as an immutable JavaScript array. -/
  | list (elem : JsTerm)
  /-- A one-argument function. -/
  | fn (dom cod : JsTerm)
  /-- A record: an array of its fields. -/
  | tuple (fields : List JsTerm)
  /-- A union: an array of the tag and the fields of the constructor. -/
  | tagged (ctors : List (List JsTerm))
  /-- An enum: a number, `shift` for the first constructor. -/
  | enum (n : Nat) (shift : Int)
  /-- A declared datatype, by name (`D<block>_<member>`). -/
  | data (name : String)
  /-- A memoised delay. -/
  | thunk (t : JsTerm)
  /-- A delay recomputed each time: a function of no argument. -/
  | lazy (t : JsTerm)
  deriving Inhabited, Repr, BEq

namespace JsTerm

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTerm → Bool
  | .nat | .int | .bitvec_big .. => true
  | _ => false

/-- A rendering for the `-JsTerm.txt` dump. -/
partial def pretty : JsTerm → String
  | .bool => "boolean"
  | .nat => "nat(bigint)"
  | .uint53 => "uint53(number)"
  | .int => "int(bigint)"
  | .int53 => "int53(number)"
  | .bitvec_small n _ _ => s!"bitvec{n}(number)"
  | .bitvec_big n _ => s!"bitvec{n}(bigint)"
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32"
  | .float => "float" | .float32 => "float32"
  | .string => "string" | .substring => "substring" | .stringSlice => "stringSlice"
  | .opaque n => s!"opaque({n})"
  | .genericArray t => s!"Array<{t.pretty}>"
  | .uint8Array => "Uint8Array" | .uint16Array => "Uint16Array"
  | .uint32Array => "Uint32Array" | .int8Array => "Int8Array" | .int16Array => "Int16Array"
  | .int32Array => "Int32Array" | .float32Array => "Float32Array"
  | .float64Array => "Float64Array" | .bigUint64Array => "BigUint64Array"
  | .bigInt64Array => "BigInt64Array"
  | .list t => s!"List<{t.pretty}>"
  | .fn a b => s!"({a.pretty} => {b.pretty})"
  | .tuple ts => "[" ++ ", ".intercalate (ts.map pretty) ++ "]"
  | .tagged cs => "(" ++ " | ".intercalate
      ((List.range cs.length).zip cs |>.map fun (i, fs) =>
        "[" ++ ", ".intercalate (toString i :: fs.map pretty) ++ "]") ++ ")"
  | .enum n shift => s!"enum{n}@{shift}"
  | .data n => n
  | .thunk t => s!"Thunk<{t.pretty}>"
  | .lazy t => s!"(() => {t.pretty})"

instance : ToString JsTerm := ⟨pretty⟩

end JsTerm

/-- Lower a scalar `LeanPrimTy` to `JsTerm` based on the configuration. -/
def lowerScalarPrim (cfg : JsConfig) (prim : LeanPrimTy) : JsTerm :=
  match prim with
  | .bool => .bool
  | .nat => match cfg.natRepr with
    | .bigint => .nat
    | .num => .uint53
  | .int => match cfg.intRepr with
    | .bigint => .int
    | .num => .int53
  | .bitvec n hNondeg =>
    if h : n ≤ 53 then
      .bitvec_small n h (by omega)
    else
      match cfg.bitvecRepr with
      | .bigint => .bitvec_big n (by omega)
      | .num => .uint53
  | .uint8 => .uint8
  | .uint16 => .uint16
  | .uint32 => .uint32
  | .uint64 => match cfg.uint64Repr with
    | .bigint => .nat
    | .num => .uint53
  | .int8 => .int8
  | .int16 => .int16
  | .int32 => .int32
  | .int64 => match cfg.int64Repr with
    | .bigint => .int
    | .num => .int53
  | .float => .float
  | .float32 => .float32
  | .char => .string
  | .string => .string
  | .stringPos _ _ => .uint53
  | .stringPosRaw => .uint53
  | .substringRaw => .substring
  | .stringSlice => .stringSlice
  | .floatModel => .opaque "Float.Model"
  | .float32Model => .opaque "Float32.Model"

/-- Lowers an array of a leaf type into the optimized `JsTerm`. -/
def lowerArrayPrim (cfg : JsConfig) (prim : LeanPrimTy) : JsTerm :=
  match prim with
  | .bool => .genericArray .bool
  | .bitvec n _ =>
    let generic : JsTerm := .genericArray (lowerScalarPrim cfg prim)
    match cfg.arrayBitVecRepr with
    | .genericArray => generic
    | .exactTypedArrayOnly =>
      if n == 8 then .uint8Array
      else if n == 16 then .uint16Array
      else if n == 32 then .uint32Array
      else if n == 64 then
        match cfg.bitvecRepr with
        | .bigint => .bigUint64Array
        | .num => generic
      else generic
    | .roundUpToSmallestTypedArray =>
      if n ≤ 8 then .uint8Array
      else if n ≤ 16 then .uint16Array
      else if n ≤ 32 then .uint32Array
      else if n ≤ 64 then
        match cfg.bitvecRepr with
        | .bigint => .bigUint64Array
        | .num => generic
      else generic
  | .uint8 => match cfg.arrayFixedIntRepr with
    | .typedArray => .uint8Array
    | .genericArray => .genericArray .uint8
  | .uint16 => match cfg.arrayFixedIntRepr with
    | .typedArray => .uint16Array
    | .genericArray => .genericArray .uint16
  | .uint32 => match cfg.arrayFixedIntRepr with
    | .typedArray => .uint32Array
    | .genericArray => .genericArray .uint32
  | .int8 => match cfg.arrayFixedIntRepr with
    | .typedArray => .int8Array
    | .genericArray => .genericArray .int8
  | .int16 => match cfg.arrayFixedIntRepr with
    | .typedArray => .int16Array
    | .genericArray => .genericArray .int16
  | .int32 => match cfg.arrayFixedIntRepr with
    | .typedArray => .int32Array
    | .genericArray => .genericArray .int32
  | .uint64 =>
    match cfg.arrayUint64Repr, cfg.uint64Repr with
    | .bigUint64Array, .bigint => .bigUint64Array
    | _, _ => .genericArray (lowerScalarPrim cfg .uint64)
  | .int64 =>
    match cfg.arrayInt64Repr, cfg.int64Repr with
    | .bigInt64Array, .bigint => .bigInt64Array
    | _, _ => .genericArray (lowerScalarPrim cfg .int64)
  | .float => match cfg.arrayFloatRepr with
    | .typedArray => .float64Array
    | .genericArray => .genericArray .float
  | .float32 => match cfg.arrayFloatRepr with
    | .typedArray => .float32Array
    | .genericArray => .genericArray .float32
  | .char => .genericArray .string
  | other => .genericArray (lowerScalarPrim cfg other)

/-- The name of member `j` of a block of a signature, as a JavaScript type name. -/
def refName {ks : List Nat} : Ref ks → String :=
  go 0
where
  go {ks : List Nat} (depth : Nat) : Ref ks → String
    | .here j => s!"D{depth}_{j.val}"
    | .there r => go (depth + 1) r

mutual
/-- The layout of a Lean type in JavaScript. -/
def lowerTy (cfg : JsConfig) {ks : List Nat} {d : Bool} : Ty ks d → JsTerm
  | .prim p => lowerScalarPrim cfg p
  | .fn a b => .fn (lowerTy cfg a) (lowerTy cfg b)
  | .array (.prim p) => lowerArrayPrim cfg p
  | .array t => .genericArray (lowerTy cfg t)
  | .list t => .list (lowerTy cfg t)
  | .enum s => .enum s.nOfConstructors s.shift
  | .record t fs => .tuple (lowerTy cfg t :: lowerFields cfg fs)
  | .union cs (h := _) => .tagged (lowerCtors cfg cs)
  | .data r => .data (refName r)
  | .thunk t => .thunk (lowerTy cfg t)
  | .lazy t => .lazy (lowerTy cfg t)
/-- The layouts of the fields of a record or a constructor. -/
def lowerFields (cfg : JsConfig) {ks : List Nat} : Fields ks → List JsTerm
  | .one t => [lowerTy cfg t]
  | .cons t fs => lowerTy cfg t :: lowerFields cfg fs
/-- The layouts of the fields of a constructor. -/
def lowerCtor (cfg : JsConfig) {ks : List Nat} {b : Bool} : Ctor ks b → List JsTerm
  | .nullary => []
  | .fields fs => lowerFields cfg fs
/-- The layouts of the constructors of a union. -/
def lowerCtors (cfg : JsConfig) {ks : List Nat} {bs : List Bool} : Ctors ks bs →
    List (List JsTerm)
  | .two a b => [lowerCtor cfg a, lowerCtor cfg b]
  | .cons c cs => lowerCtor cfg c :: lowerCtors cfg cs
end

example : lowerTy JsConfig.default (Ty.nat : Ty []) = .nat := rfl
example : lowerTy JsConfig.presetPBO (Ty.nat : Ty []) = .uint53 := rfl
example : lowerTy JsConfig.default (.array (.prim .uint8) : Ty []) = .uint8Array := rfl
example : lowerTy JsConfig.presetPBO (.array (.prim .uint8) : Ty []) = .genericArray .uint8 := rfl

end MoreJs

end
