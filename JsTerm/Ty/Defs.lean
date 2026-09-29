module

public import LeanScript.Ty.Syntax.LeanPrimTy

@[expose] public section

set_option autoImplicit false

/-!
# The types of `JsTerm`

`JsTerm` is a **simply typed** language: every expression has a type `JsTy`, every variable
is typed by its context, and every operation (`JsTerm.Ops.Imported`, `JsTerm.Ops.Inlinable`) has a fixed
signature.  `LeanScript.Ty` describes *Lean* values; `JsTy` describes how such a
value is laid out in JavaScript, once the configuration (`MoreJs.JsConfig`) has chosen a
representation for every configurable type: a `Nat` is a `bigint_nat` (a non-negative
`BigInt`) or a `uint53` (a non-negative integer `number` below `2^53`), an `Array UInt8` is
an `array uint8` or a `typedArray uint8`, and so on.

The leaves are `JsTerminalTy`; the compound shapes have one layout each:

| `Ty` | `JsTy` | JavaScript |
| --- | --- | --- |
| a leaf | `terminal t` | a boolean, a number, a `BigInt` or a string (`JsTerminalTy`) |
| `array t` | `array t` or `typedArray e` | a JavaScript `Array`, or a typed array (`Uint8Array`, …) of the element `e` |
| `record t fs` | `record f₁ f₂ [f₃, …]` | an object `{ _1: f₁, _2: f₂, … }` (two fields or more) |
| `union cs` | `union c₀ c₁ [c₂, …]` | an object `{ tag: i, _1: f₁, _2: f₂, … }`, the constructor's position `i` counting from `0` (two constructors or more, each the list of its fields) |
| `enum s` | `enum n shift` | the number `shift + i` |
| `list t` | `list t` (`listRepr = stdListToJsArray`) | an (immutable) JavaScript array |
| `list t` | `consList t` (`listRepr = taggedUnion`) | cons cells: `{ tag: 0 }` (`[]`) and `{ tag: 1, _1: head, _2: tail }` |
| `fn a (fn b c)` | `fn [a, b] c` | a function of all its arguments (uncurried) |
| `thunk t` | `thunk t` | a memoising thunk object |
| `lazy t` | `fn [] t` | a function of no argument |
| `data r` | `data name` | a declared datatype (not converted yet) |

A Lean function type is uncurried **maximally**: `Nat → Nat → Nat` is `fn [nat, nat] nat`, a
JavaScript function of two arguments, wherever the value goes (a parameter, a field, the
result of a function).  A delay (`lazy t`) is a function of no argument, so `Nat → Lazy
Nat` stays `fn [nat] (fn [] nat)`: only the arrows of `Ty.fn` are merged.

Records and unions are structural: a record has two fields or more and a union two
constructors or more (the source types guarantee both: a structure of one field is unboxed,
a type of one constructor is a record, before this stage), so the type of an empty record
or a union of one constructor cannot be written.

Decidable equality of `JsTy` is in `JsTerm.Ty.DecEq`; the names, renderings and array layouts
in `JsTerm.Ty.Basic`; how a Lean type is lowered to its `JsTy` (`lowerTy`) in `JsTerm.Ty.Lower`.
-/

namespace MoreJs

open LeanScript

/-- The leaves of `JsTy`: the JavaScript representations of the terminal Lean types. -/
inductive JsTerminalTy where
  /-- A JavaScript `boolean`. -/
  | bool
  /-- A non-negative `BigInt` (an unbounded natural number). -/
  | bigint_nat
  /-- A non-negative integer `number` below `2^53`. -/
  | uint53
  /-- A `BigInt` (an unbounded integer). -/
  | bigint_int
  /-- An integer `number` of absolute value below `2^53`. -/
  | int53
  /-- A bit vector of at most 53 bits, as a `number` (a bit vector of `0` or `1` bits is
      erased before this stage, so `2 ≤ n`). -/
  | bitvec_small (n : Nat) (h_le_53 : n ≤ 53) (h_pos_and_not_2_point : 2 ≤ n)
  /-- A bit vector of more than 53 bits, as a `BigInt`. -/
  | bigint_bitvec_big (n : Nat) (h_gt_53 : 53 < n)
  /-- A bit vector of more than 53 bits, as a `number` (exact below `2^53` only). -/
  | int53_bitvec_big (n : Nat) (h_gt_53 : 53 < n)
  /-- Fixed-width integers that always fit in a `number`. -/
  | uint8 | uint16 | uint32 | int8 | int16 | int32
  /-- A 64-bit IEEE float, a `number` (also a `Float.Model`, the same value). -/
  | float
  /-- A 32-bit IEEE float, a `number` rounded by `Math.fround` (also a `Float32.Model`). -/
  | float32
  /-- A JavaScript `string` (also a `Char`, as a string of one code point). -/
  | string
  /-- A `Substring.Raw`: `[str, startPos, stopPos]`. -/
  | substring
  /-- A `String.Slice`: `[str, startPos, stopPos]`. -/
  | stringSlice
  deriving Inhabited, Repr, DecidableEq

/-- The typed arrays of JavaScript. -/
inductive JsTypedArray where
  | uint8Array | uint16Array | uint32Array | int8Array | int16Array | int32Array
  | float32Array | float64Array | bigUint64Array | bigInt64Array
  deriving Inhabited, Repr, DecidableEq

/-- The element types a JavaScript typed array holds.  The typed array follows from the
    element (`JsTypedElem.kind`), and so does the leaf an element is read as
    (`JsTypedElem.leaf`): only the pairs that are JavaScript values can be written. -/
inductive JsTypedElem where
  /-- A `UInt8`, in a `Uint8Array` (and so on for the other fixed-width integers). -/
  | uint8 | uint16 | uint32 | int8 | int16 | int32
  /-- A `Float32`, in a `Float32Array`. -/
  | float32
  /-- A `Float`, in a `Float64Array`. -/
  | float64
  /-- A `UInt64` at the `BigInt` representation, in a `BigUint64Array`. -/
  | uint64
  /-- An `Int64` at the `BigInt` representation, in a `BigInt64Array`. -/
  | int64
  /-- A `BitVec n` of at most 32 bits, in the smallest unsigned typed array that holds it. -/
  | bitvec (n : Nat) (h₂ : 2 ≤ n) (h₃₂ : n ≤ 32)
  /-- A `BitVec n` of 54 to 64 bits at the `BigInt` representation, in a `BigUint64Array`. -/
  | bitvecBig (n : Nat) (h₅₃ : 53 < n) (h₆₄ : n ≤ 64)
  deriving Inhabited, Repr, DecidableEq

namespace JsTypedElem

/-- The typed array that holds the element. -/
def kind : JsTypedElem → JsTypedArray
  | .uint8 => .uint8Array | .uint16 => .uint16Array | .uint32 => .uint32Array
  | .int8 => .int8Array | .int16 => .int16Array | .int32 => .int32Array
  | .float32 => .float32Array | .float64 => .float64Array
  | .uint64 => .bigUint64Array | .int64 => .bigInt64Array
  | .bitvec n _ _ => if n ≤ 8 then .uint8Array else if n ≤ 16 then .uint16Array else .uint32Array
  | .bitvecBig .. => .bigUint64Array

/-- The leaf an element is read as. -/
def leaf : JsTypedElem → JsTerminalTy
  | .uint8 => .uint8 | .uint16 => .uint16 | .uint32 => .uint32
  | .int8 => .int8 | .int16 => .int16 | .int32 => .int32
  | .float32 => .float32 | .float64 => .float
  | .uint64 => .bigint_nat | .int64 => .bigint_int
  | .bitvec n h₂ h₃₂ => .bitvec_small n (by omega) h₂
  | .bitvecBig n h _ => .bigint_bitvec_big n h

end JsTypedElem

/-- The types of `JsTerm`: how a Lean value is laid out in JavaScript. -/
inductive JsTy where
  /-- A leaf. -/
  | terminal (t : JsTerminalTy)
  /-- A generic JavaScript `Array`. -/
  | array (elem : JsTy)
  /-- A typed array (`Uint8Array`, …) of the elements `elem` (a `BitVec 5` in a
      `Uint8Array`, …). -/
  | typedArray (elem : JsTypedElem)
  /-- A Lean `List`, as an immutable JavaScript array (`ListRepr.stdListToJsArray`). -/
  | list (elem : JsTy)
  /-- A Lean `List`, as tagged cons cells (`ListRepr.taggedUnion`): the empty list is
      `{ tag: 0 }`, `head :: tail` is `{ tag: 1, _1: head, _2: tail }` — the layout of a union
      of the constructors `nil` and `cons`, which a structural `union` cannot write (the type
      is recursive).  A tail is shared, never copied. -/
  | consList (elem : JsTy)
  /-- A function of the arguments `doms` (none for a delay): `(x₁, …, xₙ) => …`. -/
  | fn (doms : List JsTy) (cod : JsTy)
  /-- A record of two fields or more: an object `{ _1: f₁, _2: f₂, … }` (numbered from `1`). -/
  | record (f₁ f₂ : JsTy) (fs : List JsTy)
  /-- A union of two constructors or more, each the list of its fields: an object
      `{ tag: i, _1: f₁, … }` of the position `i` (from `0`) of the constructor and its fields
      (numbered from `1`). -/
  | union (c₀ c₁ : List JsTy) (cs : List (List JsTy))
  /-- An enum: a number, `shift` for the first of its `n` constructors. -/
  | enum (n : Nat) (shift : Int)
  /-- A declared datatype, by name (`D<block>_<member>`). -/
  | data (name : String)
  /-- A memoised delay. -/
  | thunk (t : JsTy)
  deriving Inhabited, Repr

end MoreJs

end
