module

public import JsTerm.Config
public import LeanScript.Term.Syntax.Common

@[expose] public section

set_option autoImplicit false

/-!
# The types of `JsTerm`

`JsTerm` is a **simply typed** language: every expression has a type `JsTy`, every variable
is typed by its context, and every operation (`JsTerm.Ops`) has a fixed
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
| `list t` | `list t` | an (immutable) JavaScript array |
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

`lowerScalarPrim` and `lowerArrayPrim` are the configuration-dependent part: how a leaf, and
an array of leaves, is represented.
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
  /-- A Lean `List`, as an immutable JavaScript array. -/
  | list (elem : JsTy)
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

namespace JsTy

mutual
/-- Decidable equality of types. -/
def decEqTy : (a b : JsTy) → Decidable (a = b)
  | .terminal x0, .terminal y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .terminal _, .array _ => isFalse (fun h => by cases h)
  | .terminal _, .typedArray _ => isFalse (fun h => by cases h)
  | .terminal _, .list _ => isFalse (fun h => by cases h)
  | .terminal _, .fn _ _ => isFalse (fun h => by cases h)
  | .terminal _, .record _ _ _ => isFalse (fun h => by cases h)
  | .terminal _, .union _ _ _ => isFalse (fun h => by cases h)
  | .terminal _, .enum _ _ => isFalse (fun h => by cases h)
  | .terminal _, .data _ => isFalse (fun h => by cases h)
  | .terminal _, .thunk _ => isFalse (fun h => by cases h)
  | .array _, .terminal _ => isFalse (fun h => by cases h)
  | .array x0, .array y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .array _, .typedArray _ => isFalse (fun h => by cases h)
  | .array _, .list _ => isFalse (fun h => by cases h)
  | .array _, .fn _ _ => isFalse (fun h => by cases h)
  | .array _, .record _ _ _ => isFalse (fun h => by cases h)
  | .array _, .union _ _ _ => isFalse (fun h => by cases h)
  | .array _, .enum _ _ => isFalse (fun h => by cases h)
  | .array _, .data _ => isFalse (fun h => by cases h)
  | .array _, .thunk _ => isFalse (fun h => by cases h)
  | .typedArray _, .terminal _ => isFalse (fun h => by cases h)
  | .typedArray _, .array _ => isFalse (fun h => by cases h)
  | .typedArray x0, .typedArray y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .typedArray _, .list _ => isFalse (fun h => by cases h)
  | .typedArray _, .fn _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .record _ _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .union _ _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .enum _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .data _ => isFalse (fun h => by cases h)
  | .typedArray _, .thunk _ => isFalse (fun h => by cases h)
  | .list _, .terminal _ => isFalse (fun h => by cases h)
  | .list _, .array _ => isFalse (fun h => by cases h)
  | .list _, .typedArray _ => isFalse (fun h => by cases h)
  | .list x0, .list y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .list _, .fn _ _ => isFalse (fun h => by cases h)
  | .list _, .record _ _ _ => isFalse (fun h => by cases h)
  | .list _, .union _ _ _ => isFalse (fun h => by cases h)
  | .list _, .enum _ _ => isFalse (fun h => by cases h)
  | .list _, .data _ => isFalse (fun h => by cases h)
  | .list _, .thunk _ => isFalse (fun h => by cases h)
  | .fn _ _, .terminal _ => isFalse (fun h => by cases h)
  | .fn _ _, .array _ => isFalse (fun h => by cases h)
  | .fn _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .fn _ _, .list _ => isFalse (fun h => by cases h)
  | .fn x0 x1, .fn y0 y1 =>
    match decEqTys x0 y0, decEqTy x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .fn _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .data _ => isFalse (fun h => by cases h)
  | .fn _ _, .thunk _ => isFalse (fun h => by cases h)
  | .record _ _ _, .terminal _ => isFalse (fun h => by cases h)
  | .record _ _ _, .array _ => isFalse (fun h => by cases h)
  | .record _ _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .record _ _ _, .list _ => isFalse (fun h => by cases h)
  | .record _ _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .record x0 x1 x2, .record y0 y1 y2 =>
    match decEqTy x0 y0, decEqTy x1 y1, decEqTys x2 y2 with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (h0 ▸ h1 ▸ h2 ▸ rfl)
    | isFalse h, _, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .record _ _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .record _ _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .record _ _ _, .data _ => isFalse (fun h => by cases h)
  | .record _ _ _, .thunk _ => isFalse (fun h => by cases h)
  | .union _ _ _, .terminal _ => isFalse (fun h => by cases h)
  | .union _ _ _, .array _ => isFalse (fun h => by cases h)
  | .union _ _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .union _ _ _, .list _ => isFalse (fun h => by cases h)
  | .union _ _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .union _ _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .union x0 x1 x2, .union y0 y1 y2 =>
    match decEqTys x0 y0, decEqTys x1 y1, decEqTyss x2 y2 with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (h0 ▸ h1 ▸ h2 ▸ rfl)
    | isFalse h, _, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .union _ _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .union _ _ _, .data _ => isFalse (fun h => by cases h)
  | .union _ _ _, .thunk _ => isFalse (fun h => by cases h)
  | .enum _ _, .terminal _ => isFalse (fun h => by cases h)
  | .enum _ _, .array _ => isFalse (fun h => by cases h)
  | .enum _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .enum _ _, .list _ => isFalse (fun h => by cases h)
  | .enum _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .enum x0 x1, .enum y0 y1 =>
    match decEq x0 y0, decEq x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .enum _ _, .data _ => isFalse (fun h => by cases h)
  | .enum _ _, .thunk _ => isFalse (fun h => by cases h)
  | .data _, .terminal _ => isFalse (fun h => by cases h)
  | .data _, .array _ => isFalse (fun h => by cases h)
  | .data _, .typedArray _ => isFalse (fun h => by cases h)
  | .data _, .list _ => isFalse (fun h => by cases h)
  | .data _, .fn _ _ => isFalse (fun h => by cases h)
  | .data _, .record _ _ _ => isFalse (fun h => by cases h)
  | .data _, .union _ _ _ => isFalse (fun h => by cases h)
  | .data _, .enum _ _ => isFalse (fun h => by cases h)
  | .data x0, .data y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .data _, .thunk _ => isFalse (fun h => by cases h)
  | .thunk _, .terminal _ => isFalse (fun h => by cases h)
  | .thunk _, .array _ => isFalse (fun h => by cases h)
  | .thunk _, .typedArray _ => isFalse (fun h => by cases h)
  | .thunk _, .list _ => isFalse (fun h => by cases h)
  | .thunk _, .fn _ _ => isFalse (fun h => by cases h)
  | .thunk _, .record _ _ _ => isFalse (fun h => by cases h)
  | .thunk _, .union _ _ _ => isFalse (fun h => by cases h)
  | .thunk _, .enum _ _ => isFalse (fun h => by cases h)
  | .thunk _, .data _ => isFalse (fun h => by cases h)
  | .thunk x0, .thunk y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)

/-- Decidable equality of lists of types. -/
def decEqTys : (a b : List JsTy) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match decEqTy a b, decEqTys as bs with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
/-- Decidable equality of lists of lists of types. -/
def decEqTyss : (a b : List (List JsTy)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match decEqTys a b, decEqTyss as bs with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
end

instance : DecidableEq JsTy := decEqTy

end JsTy

instance : Coe JsTerminalTy JsTy := ⟨JsTy.terminal⟩

namespace JsTerminalTy

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTerminalTy → Bool
  | .bigint_nat | .bigint_int | .bigint_bitvec_big .. => true
  | _ => false

/-- The name of the leaf, as the names of the operations spell it (`bigint_nat`,
    `uint53`, `bitvec32`, …). -/
def name : JsTerminalTy → String
  | .bool => "bool" | .bigint_nat => "bigint_nat" | .uint53 => "uint53"
  | .bigint_int => "bigint_int" | .int53 => "int53"
  | .bitvec_small n _ _ => s!"bitvec{n}"
  | .bigint_bitvec_big n _ => s!"bigint_bitvec{n}"
  | .int53_bitvec_big n _ => s!"int53_bitvec{n}"
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32"
  | .float => "float" | .float32 => "float32"
  | .string => "string" | .substring => "substring" | .stringSlice => "stringSlice"

/-- A rendering for the `-JsTerm.txt` dump. -/
def pretty : JsTerminalTy → String
  | .bool => "boolean"
  | .bigint_nat => "nat(bigint)"
  | .uint53 => "uint53(number)"
  | .bigint_int => "int(bigint)"
  | .int53 => "int53(number)"
  | .bitvec_small n _ _ => s!"bitvec{n}(number)"
  | .bigint_bitvec_big n _ => s!"bitvec{n}(bigint)"
  | .int53_bitvec_big n _ => s!"bitvec{n}(number)"
  | t => t.name

end JsTerminalTy

namespace JsTypedArray

/-- The JavaScript constructor of the typed array. -/
def ctorName : JsTypedArray → String
  | .uint8Array => "Uint8Array" | .uint16Array => "Uint16Array"
  | .uint32Array => "Uint32Array" | .int8Array => "Int8Array" | .int16Array => "Int16Array"
  | .int32Array => "Int32Array" | .float32Array => "Float32Array"
  | .float64Array => "Float64Array" | .bigUint64Array => "BigUint64Array"
  | .bigInt64Array => "BigInt64Array"

end JsTypedArray

/-- The two representations of a natural number that count the iterations of a loop. -/
inductive JsNatTy : JsTy → Type where
  | bigint_nat : JsNatTy (.terminal .bigint_nat)
  | uint53 : JsNatTy (.terminal .uint53)
  deriving Repr

/-- The natural-number representation of a type, if it is one. -/
def JsNatTy.of? : (t : JsTy) → Option (JsNatTy t)
  | .terminal .bigint_nat => some .bigint_nat
  | .terminal .uint53 => some .uint53
  | _ => none

/-- How an array type is laid out: a generic array of elements `α`, or a typed array whose
    elements are read as the leaf of `t`. -/
inductive JsArrayLayout : JsTy → JsTy → Type where
  | generic (α : JsTy) : JsArrayLayout (.array α) α
  | typed (t : JsTypedElem) : JsArrayLayout (.typedArray t) (.terminal t.leaf)
  deriving Repr

/-- The layout of an array type, if it is one. -/
def JsArrayLayout.of? : (a : JsTy) → Option (Σ e, JsArrayLayout a e)
  | .array α => some ⟨α, .generic α⟩
  | .typedArray t => some ⟨.terminal t.leaf, .typed t⟩
  | _ => none

/-- The element type of an array layout is determined by the array type. -/
theorem JsArrayLayout.elem_unique {a e₁ e₂ : JsTy} :
    JsArrayLayout a e₁ → JsArrayLayout a e₂ → e₁ = e₂
  | .generic _, .generic _ => rfl
  | .typed _, .typed _ => rfl

namespace JsTy

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTy → Bool
  | .terminal t => t.isBigInt
  | _ => false

/-- The fields of a record type, in order. -/
def recordFields : JsTy → Option (List JsTy)
  | .record f₁ f₂ fs => some (f₁ :: f₂ :: fs)
  | _ => none

/-- The constructors of a union type, in order. -/
def unionCtors : JsTy → Option (List (List JsTy))
  | .union c₀ c₁ cs => some (c₀ :: c₁ :: cs)
  | _ => none

/-- A rendering for the `-JsTerm.txt` dump. -/
partial def pretty : JsTy → String
  | .terminal t => t.pretty
  | .array t => s!"Array<{t.pretty}>"
  | .typedArray t => s!"{t.kind.ctorName}<{t.leaf.pretty}>"
  | .list t => s!"List<{t.pretty}>"
  | .fn ds c => "(" ++ ", ".intercalate (ds.map pretty) ++ s!") => {c.pretty}"
  | .record f₁ f₂ fs => let ts := f₁ :: f₂ :: fs; "{ " ++ ", ".intercalate
      ((List.range ts.length).zip ts |>.map fun (i, t) => s!"_{i + 1}: {t.pretty}") ++ " }"
  | .union c₀ c₁ cs => let cs := c₀ :: c₁ :: cs; "(" ++ " | ".intercalate
      ((List.range cs.length).zip cs |>.map fun (i, fs) =>
        "{ " ++ ", ".intercalate (s!"tag: {i}" ::
          ((List.range fs.length).zip fs |>.map fun (j, t) => s!"_{j + 1}: {t.pretty}")) ++ " }") ++ ")"
  | .enum n shift => s!"enum{n}@{shift}"
  | .data n => n
  | .thunk t => s!"Thunk<{t.pretty}>"

instance : ToString JsTy := ⟨pretty⟩

end JsTy

/-- Lower a scalar `LeanPrimTy` to its leaf, based on the configuration. -/
def lowerScalarPrim (cfg : JsConfig) (prim : LeanPrimTy) : JsTerminalTy :=
  match prim with
  | .bool => .bool
  | .nat => match cfg.natRepr with
    | .bigint => .bigint_nat
    | .num => .uint53
  | .int => match cfg.intRepr with
    | .bigint => .bigint_int
    | .num => .int53
  | .bitvec n hNondeg =>
    if h : n ≤ 53 then
      .bitvec_small n h hNondeg
    else
      match cfg.bitvecRepr with
      | .bigint => .bigint_bitvec_big n (by omega)
      | .num => .int53_bitvec_big n (by omega)
  | .uint8 => .uint8
  | .uint16 => .uint16
  | .uint32 => .uint32
  | .uint64 => match cfg.uint64Repr with
    | .bigint => .bigint_nat
    | .num => .uint53
  | .int8 => .int8
  | .int16 => .int16
  | .int32 => .int32
  | .int64 => match cfg.int64Repr with
    | .bigint => .bigint_int
    | .num => .int53
  | .float => .float
  | .float32 => .float32
  | .char => .string
  | .string => .string
  | .stringPos _ _ => .uint53
  | .stringPosRaw => .uint53
  | .substringRaw => .substring
  | .stringSlice => .stringSlice
  | .floatModel => .float
  | .float32Model => .float32

/-- The element of the typed array an array of `BitVec n` is stored in, if any: `exact` says
    whether only the widths of a typed array (`8`, `16`, `32`, `64`) are.  A bit vector of
    33 to 53 bits is a `number`, which no typed array of more than 32 bits holds. -/
def bitvecTypedElem (cfg : JsConfig) (n : Nat) (h₂ : 2 ≤ n) (exact : Bool) : Option JsTypedElem :=
  if h : n ≤ 32 then
    if !exact || n == 8 || n == 16 || n == 32 then some (.bitvec n h₂ h) else none
  else if h' : 53 < n ∧ n ≤ 64 then
    if !exact || n == 64 then
      match cfg.bitvecRepr with
      | .bigint => some (.bitvecBig n h'.1 h'.2)
      | .num => none
    else none
  else none

/-- Lowers an array of a leaf type. -/
def lowerArrayPrim (cfg : JsConfig) (prim : LeanPrimTy) : JsTy :=
  let generic : JsTy := .array (.terminal (lowerScalarPrim cfg prim))
  let typedIf (typed : Bool) (t : JsTypedElem) : JsTy := if typed then .typedArray t else generic
  let fixed := cfg.arrayFixedIntRepr == .typedArray
  let floats := cfg.arrayFloatRepr == .typedArray
  match prim with
  | .bitvec n h₂ =>
    let elem? := match cfg.arrayBitVecRepr with
      | .genericArray => none
      | .exactTypedArrayOnly => bitvecTypedElem cfg n h₂ true
      | .roundUpToSmallestTypedArray => bitvecTypedElem cfg n h₂ false
    match elem? with
    | some t => .typedArray t
    | none => generic
  | .uint8 => typedIf fixed .uint8
  | .uint16 => typedIf fixed .uint16
  | .uint32 => typedIf fixed .uint32
  | .int8 => typedIf fixed .int8
  | .int16 => typedIf fixed .int16
  | .int32 => typedIf fixed .int32
  | .uint64 =>
    match cfg.arrayUint64Repr, cfg.uint64Repr with
    | .bigUint64Array, .bigint => .typedArray .uint64
    | _, _ => generic
  | .int64 =>
    match cfg.arrayInt64Repr, cfg.int64Repr with
    | .bigInt64Array, .bigint => .typedArray .int64
    | _, _ => generic
  | .float => typedIf floats .float64
  | .float32 => typedIf floats .float32
  | _ => generic

/-- The name of member `j` of a block of a signature, as a JavaScript type name. -/
def refName {ks : List Nat} : Ref ks → String :=
  go 0
where
  go {ks : List Nat} (depth : Nat) : Ref ks → String
    | .here j => s!"D{depth}_{j.val}"
    | .there r => go (depth + 1) r

/-- Is the type an arrow (`Ty.fn`)? -/
def _root_.LeanScript.Ty.isFn {ks : List Nat} {d : Bool} : Ty ks d → Bool
  | .fn .. => true
  | _ => false

/-- The layout of the function type `σ → τ`, from the layouts `a` of `σ` and `b` of `τ`: when `τ`
    is an arrow too (`fnRes`), its arguments are the arguments after `a` (the function is
    uncurried). -/
def JsTy.arrow (a : JsTy) (fnRes : Bool) (b : JsTy) : JsTy :=
  match fnRes, b with
  | true, .fn ds c => .fn (a :: ds) c
  | _, b => .fn [a] b

mutual
/-- The layout of a Lean type in JavaScript. -/
def lowerTy (cfg : JsConfig) {ks : List Nat} {d : Bool} : Ty ks d → JsTy
  | .prim p => .terminal (lowerScalarPrim cfg p)
  | .fn a b => JsTy.arrow (lowerTy cfg a) b.isFn (lowerTy cfg b)
  | .array (.prim p) => lowerArrayPrim cfg p
  | .array t => .array (lowerTy cfg t)
  | .list t => .list (lowerTy cfg t)
  | .enum s => .enum s.nOfConstructors s.shift
  | .record t fs => .record (lowerTy cfg t) (lowerFields1 cfg fs).1 (lowerFields1 cfg fs).2
  | .union cs (h := _) =>
    .union (lowerCtors2 cfg cs).1 (lowerCtors2 cfg cs).2.1 (lowerCtors2 cfg cs).2.2
  | .data r => .data (refName r)
  | .thunk t => .thunk (lowerTy cfg t)
  | .lazy t => .fn [] (lowerTy cfg t)
/-- The layouts of the fields of a record or a constructor. -/
def lowerFields (cfg : JsConfig) {ks : List Nat} : Fields ks → List JsTy
  | .one t => [lowerTy cfg t]
  | .cons t fs => lowerTy cfg t :: lowerFields cfg fs
/-- The layouts of one field or more: the first one and the others. -/
def lowerFields1 (cfg : JsConfig) {ks : List Nat} : Fields ks → JsTy × List JsTy
  | .one t => (lowerTy cfg t, [])
  | .cons t fs => (lowerTy cfg t, lowerFields cfg fs)
/-- The layouts of the fields of a constructor. -/
def lowerCtor (cfg : JsConfig) {ks : List Nat} {b : Bool} : Ctor ks b → List JsTy
  | .nullary => []
  | .fields fs => lowerFields cfg fs
/-- The layouts of the constructors of a union. -/
def lowerCtors (cfg : JsConfig) {ks : List Nat} {bs : List Bool} : Ctors ks bs →
    List (List JsTy)
  | .two a b => [lowerCtor cfg a, lowerCtor cfg b]
  | .cons c cs => lowerCtor cfg c :: lowerCtors cfg cs
/-- The layouts of two constructors or more: the first two and the others. -/
def lowerCtors2 (cfg : JsConfig) {ks : List Nat} {bs : List Bool} : Ctors ks bs →
    List JsTy × List JsTy × List (List JsTy)
  | .two a b => (lowerCtor cfg a, lowerCtor cfg b, [])
  | .cons c cs => (lowerCtor cfg c, lowerCtors1 cfg cs)
/-- The layouts of two constructors or more: the first one and the others. -/
def lowerCtors1 (cfg : JsConfig) {ks : List Nat} {bs : List Bool} : Ctors ks bs →
    List JsTy × List (List JsTy)
  | .two a b => (lowerCtor cfg a, [lowerCtor cfg b])
  | .cons c cs => (lowerCtor cfg c, lowerCtors cfg cs)
end

example : lowerTy JsConfig.default (Ty.nat : Ty []) = .terminal .bigint_nat := rfl
example : lowerTy JsConfig.presetPBO (Ty.nat : Ty []) = .terminal .uint53 := rfl
example : lowerTy JsConfig.default (.array (.prim .uint8) : Ty []) =
    .typedArray .uint8 := rfl
example : lowerTy JsConfig.presetPBO (.array (.prim .uint8) : Ty []) =
    .array (.terminal .uint8) := rfl

end MoreJs

end
