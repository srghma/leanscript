module

public import JsTerm.Config
public import LeanScript.Term.Syntax.Common

@[expose] public section

set_option autoImplicit false

/-!
# The types of `JsTerm`

`JsTerm` is a **simply typed** language: every expression has a type `JsTy`, every variable
is typed by its context, and every operation (`JsTerm.OpsImported`, `JsTerm.OpsInlined`)
has a fixed signature.  `LeanScript.Ty` describes *Lean* values; `JsTy` describes how such a
value is laid out in JavaScript, once the configuration (`MoreJs.JsConfig`) has chosen a
representation for every configurable type: a `Nat` is a `bigint_nat` (a non-negative
`BigInt`) or a `uint53` (a non-negative integer `number` below `2^53`), an `Array UInt8` is
an `array uint8` or a `typedArray uint8Array uint8`, and so on.

The leaves are `JsTerminalTy`; the compound shapes have one layout each:

| `Ty` | `JsTy` | JavaScript |
| --- | --- | --- |
| a leaf | `terminal t` | a boolean, a number, a `BigInt` or a string (`JsTerminalTy`) |
| `array t` | `array t` or `typedArray k e` | a JavaScript `Array`, or a typed array (`Uint8Array`, …) |
| `record t fs` | `record [t, …]` | an object `{ _1: f₁, _2: f₂, … }` |
| `union cs` | `union [[fields₀], [fields₁], …]` | an object `{ tag: i, _1: f₁, _2: f₂, … }`, the constructor's position `i` counting from `0` |
| `enum s` | `enum n shift` | the number `shift + i` |
| `list t` | `list t` | an (immutable) JavaScript array |
| `fn a b` | `fn a b` | a one-argument function (curried) |
| `thunk t` | `thunk t` | a memoising thunk object |
| `lazy t` | `lazy t` | a function of no argument |
| `data r` | `data name` | a declared datatype (not converted yet) |

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

/-- The types of `JsTerm`: how a Lean value is laid out in JavaScript. -/
inductive JsTy where
  /-- A leaf. -/
  | terminal (t : JsTerminalTy)
  /-- A generic JavaScript `Array`. -/
  | array (elem : JsTy)
  /-- A typed array (`Uint8Array`, …) whose elements are read as the leaf `elem` (a
      `BitVec 5` in a `Uint8Array`, …). -/
  | typedArray (kind : JsTypedArray) (elem : JsTerminalTy)
  /-- A Lean `List`, as an immutable JavaScript array. -/
  | list (elem : JsTy)
  /-- A one-argument function. -/
  | fn (dom cod : JsTy)
  /-- A record: an object `{ _1: f₁, _2: f₂, … }` of its fields (numbered from `1`). -/
  | record (fields : List JsTy)
  /-- A union: an object `{ tag: i, _1: f₁, … }` of the position `i` (from `0`) of the
      constructor and its fields (numbered from `1`). -/
  | union (ctors : List (List JsTy))
  /-- An enum: a number, `shift` for the first of its `n` constructors. -/
  | enum (n : Nat) (shift : Int)
  /-- A declared datatype, by name (`D<block>_<member>`). -/
  | data (name : String)
  /-- A memoised delay. -/
  | thunk (t : JsTy)
  /-- A delay recomputed each time: a function of no argument. -/
  | lazy (t : JsTy)
  deriving Inhabited, Repr

namespace JsTy

mutual
/-- Decidable equality of types. -/
def decEqTy : (a b : JsTy) → Decidable (a = b)
  | .terminal t₁, .terminal t₂ =>
    match decEq t₁ t₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .terminal _, .array _ => isFalse (fun h => by cases h)
  | .terminal _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .terminal _, .list _ => isFalse (fun h => by cases h)
  | .terminal _, .fn _ _ => isFalse (fun h => by cases h)
  | .terminal _, .record _ => isFalse (fun h => by cases h)
  | .terminal _, .union _ => isFalse (fun h => by cases h)
  | .terminal _, .enum _ _ => isFalse (fun h => by cases h)
  | .terminal _, .data _ => isFalse (fun h => by cases h)
  | .terminal _, .thunk _ => isFalse (fun h => by cases h)
  | .terminal _, .lazy _ => isFalse (fun h => by cases h)
  | .array _, .terminal _ => isFalse (fun h => by cases h)
  | .array e₁, .array e₂ =>
    match decEqTy e₁ e₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .array _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .array _, .list _ => isFalse (fun h => by cases h)
  | .array _, .fn _ _ => isFalse (fun h => by cases h)
  | .array _, .record _ => isFalse (fun h => by cases h)
  | .array _, .union _ => isFalse (fun h => by cases h)
  | .array _, .enum _ _ => isFalse (fun h => by cases h)
  | .array _, .data _ => isFalse (fun h => by cases h)
  | .array _, .thunk _ => isFalse (fun h => by cases h)
  | .array _, .lazy _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .terminal _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .array _ => isFalse (fun h => by cases h)
  | .typedArray k₁ e₁, .typedArray k₂ e₂ =>
    match decEq k₁ k₂, decEq e₁ e₂ with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .typedArray _ _, .list _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .record _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .union _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .data _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .thunk _ => isFalse (fun h => by cases h)
  | .typedArray _ _, .lazy _ => isFalse (fun h => by cases h)
  | .list _, .terminal _ => isFalse (fun h => by cases h)
  | .list _, .array _ => isFalse (fun h => by cases h)
  | .list _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .list e₁, .list e₂ =>
    match decEqTy e₁ e₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .list _, .fn _ _ => isFalse (fun h => by cases h)
  | .list _, .record _ => isFalse (fun h => by cases h)
  | .list _, .union _ => isFalse (fun h => by cases h)
  | .list _, .enum _ _ => isFalse (fun h => by cases h)
  | .list _, .data _ => isFalse (fun h => by cases h)
  | .list _, .thunk _ => isFalse (fun h => by cases h)
  | .list _, .lazy _ => isFalse (fun h => by cases h)
  | .fn _ _, .terminal _ => isFalse (fun h => by cases h)
  | .fn _ _, .array _ => isFalse (fun h => by cases h)
  | .fn _ _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .list _ => isFalse (fun h => by cases h)
  | .fn a₁ b₁, .fn a₂ b₂ =>
    match decEqTy a₁ a₂, decEqTy b₁ b₂ with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .fn _ _, .record _ => isFalse (fun h => by cases h)
  | .fn _ _, .union _ => isFalse (fun h => by cases h)
  | .fn _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .data _ => isFalse (fun h => by cases h)
  | .fn _ _, .thunk _ => isFalse (fun h => by cases h)
  | .fn _ _, .lazy _ => isFalse (fun h => by cases h)
  | .record _, .terminal _ => isFalse (fun h => by cases h)
  | .record _, .array _ => isFalse (fun h => by cases h)
  | .record _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .record _, .list _ => isFalse (fun h => by cases h)
  | .record _, .fn _ _ => isFalse (fun h => by cases h)
  | .record fs₁, .record fs₂ =>
    match decEqTys fs₁ fs₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .record _, .union _ => isFalse (fun h => by cases h)
  | .record _, .enum _ _ => isFalse (fun h => by cases h)
  | .record _, .data _ => isFalse (fun h => by cases h)
  | .record _, .thunk _ => isFalse (fun h => by cases h)
  | .record _, .lazy _ => isFalse (fun h => by cases h)
  | .union _, .terminal _ => isFalse (fun h => by cases h)
  | .union _, .array _ => isFalse (fun h => by cases h)
  | .union _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .union _, .list _ => isFalse (fun h => by cases h)
  | .union _, .fn _ _ => isFalse (fun h => by cases h)
  | .union _, .record _ => isFalse (fun h => by cases h)
  | .union cs₁, .union cs₂ =>
    match decEqTyss cs₁ cs₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .union _, .enum _ _ => isFalse (fun h => by cases h)
  | .union _, .data _ => isFalse (fun h => by cases h)
  | .union _, .thunk _ => isFalse (fun h => by cases h)
  | .union _, .lazy _ => isFalse (fun h => by cases h)
  | .enum _ _, .terminal _ => isFalse (fun h => by cases h)
  | .enum _ _, .array _ => isFalse (fun h => by cases h)
  | .enum _ _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .list _ => isFalse (fun h => by cases h)
  | .enum _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .record _ => isFalse (fun h => by cases h)
  | .enum _ _, .union _ => isFalse (fun h => by cases h)
  | .enum n₁ s₁, .enum n₂ s₂ =>
    match decEq n₁ n₂, decEq s₁ s₂ with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .enum _ _, .data _ => isFalse (fun h => by cases h)
  | .enum _ _, .thunk _ => isFalse (fun h => by cases h)
  | .enum _ _, .lazy _ => isFalse (fun h => by cases h)
  | .data _, .terminal _ => isFalse (fun h => by cases h)
  | .data _, .array _ => isFalse (fun h => by cases h)
  | .data _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .data _, .list _ => isFalse (fun h => by cases h)
  | .data _, .fn _ _ => isFalse (fun h => by cases h)
  | .data _, .record _ => isFalse (fun h => by cases h)
  | .data _, .union _ => isFalse (fun h => by cases h)
  | .data _, .enum _ _ => isFalse (fun h => by cases h)
  | .data n₁, .data n₂ =>
    match decEq n₁ n₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .data _, .thunk _ => isFalse (fun h => by cases h)
  | .data _, .lazy _ => isFalse (fun h => by cases h)
  | .thunk _, .terminal _ => isFalse (fun h => by cases h)
  | .thunk _, .array _ => isFalse (fun h => by cases h)
  | .thunk _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .thunk _, .list _ => isFalse (fun h => by cases h)
  | .thunk _, .fn _ _ => isFalse (fun h => by cases h)
  | .thunk _, .record _ => isFalse (fun h => by cases h)
  | .thunk _, .union _ => isFalse (fun h => by cases h)
  | .thunk _, .enum _ _ => isFalse (fun h => by cases h)
  | .thunk _, .data _ => isFalse (fun h => by cases h)
  | .thunk t₁, .thunk t₂ =>
    match decEqTy t₁ t₂ with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .thunk _, .lazy _ => isFalse (fun h => by cases h)
  | .lazy _, .terminal _ => isFalse (fun h => by cases h)
  | .lazy _, .array _ => isFalse (fun h => by cases h)
  | .lazy _, .typedArray _ _ => isFalse (fun h => by cases h)
  | .lazy _, .list _ => isFalse (fun h => by cases h)
  | .lazy _, .fn _ _ => isFalse (fun h => by cases h)
  | .lazy _, .record _ => isFalse (fun h => by cases h)
  | .lazy _, .union _ => isFalse (fun h => by cases h)
  | .lazy _, .enum _ _ => isFalse (fun h => by cases h)
  | .lazy _, .data _ => isFalse (fun h => by cases h)
  | .lazy _, .thunk _ => isFalse (fun h => by cases h)
  | .lazy t₁, .lazy t₂ =>
    match decEqTy t₁ t₂ with
    | isTrue h => isTrue (h ▸ rfl)
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
    elements are read as the leaf `e`. -/
inductive JsArrayLayout : JsTy → JsTy → Type where
  | generic (α : JsTy) : JsArrayLayout (.array α) α
  | typed (k : JsTypedArray) (e : JsTerminalTy) : JsArrayLayout (.typedArray k e) (.terminal e)
  deriving Repr

/-- The layout of an array type, if it is one. -/
def JsArrayLayout.of? : (a : JsTy) → Option (Σ e, JsArrayLayout a e)
  | .array α => some ⟨α, .generic α⟩
  | .typedArray k e => some ⟨.terminal e, .typed k e⟩
  | _ => none

/-- The element type of an array layout is determined by the array type. -/
theorem JsArrayLayout.elem_unique {a e₁ e₂ : JsTy} :
    JsArrayLayout a e₁ → JsArrayLayout a e₂ → e₁ = e₂
  | .generic _, .generic _ => rfl
  | .typed _ _, .typed _ _ => rfl

namespace JsTy

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTy → Bool
  | .terminal t => t.isBigInt
  | _ => false

/-- A rendering for the `-JsTerm.txt` dump. -/
partial def pretty : JsTy → String
  | .terminal t => t.pretty
  | .array t => s!"Array<{t.pretty}>"
  | .typedArray k e => s!"{k.ctorName}<{e.pretty}>"
  | .list t => s!"List<{t.pretty}>"
  | .fn a b => s!"({a.pretty} => {b.pretty})"
  | .record ts => "{ " ++ ", ".intercalate
      ((List.range ts.length).zip ts |>.map fun (i, t) => s!"_{i + 1}: {t.pretty}") ++ " }"
  | .union cs => "(" ++ " | ".intercalate
      ((List.range cs.length).zip cs |>.map fun (i, fs) =>
        "{ " ++ ", ".intercalate (s!"tag: {i}" ::
          ((List.range fs.length).zip fs |>.map fun (j, t) => s!"_{j + 1}: {t.pretty}")) ++ " }") ++ ")"
  | .enum n shift => s!"enum{n}@{shift}"
  | .data n => n
  | .thunk t => s!"Thunk<{t.pretty}>"
  | .lazy t => s!"(() => {t.pretty})"

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

/-- Lowers an array of a leaf type. -/
def lowerArrayPrim (cfg : JsConfig) (prim : LeanPrimTy) : JsTy :=
  let e := lowerScalarPrim cfg prim
  let generic : JsTy := .array (.terminal e)
  let typed (k : JsTypedArray) : JsTy := .typedArray k e
  match prim with
  | .bool => generic
  | .bitvec n _ =>
    match cfg.arrayBitVecRepr with
    | .genericArray => generic
    | .exactTypedArrayOnly =>
      if n == 8 then typed .uint8Array
      else if n == 16 then typed .uint16Array
      else if n == 32 then typed .uint32Array
      else if n == 64 then
        match cfg.bitvecRepr with
        | .bigint => typed .bigUint64Array
        | .num => generic
      else generic
    | .roundUpToSmallestTypedArray =>
      if n ≤ 8 then typed .uint8Array
      else if n ≤ 16 then typed .uint16Array
      else if n ≤ 32 then typed .uint32Array
      else if n ≤ 64 then
        match cfg.bitvecRepr with
        | .bigint => typed .bigUint64Array
        | .num => generic
      else generic
  | .uint8 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .uint8Array
    | .genericArray => generic
  | .uint16 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .uint16Array
    | .genericArray => generic
  | .uint32 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .uint32Array
    | .genericArray => generic
  | .int8 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .int8Array
    | .genericArray => generic
  | .int16 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .int16Array
    | .genericArray => generic
  | .int32 => match cfg.arrayFixedIntRepr with
    | .typedArray => typed .int32Array
    | .genericArray => generic
  | .uint64 =>
    match cfg.arrayUint64Repr, cfg.uint64Repr with
    | .bigUint64Array, .bigint => typed .bigUint64Array
    | _, _ => generic
  | .int64 =>
    match cfg.arrayInt64Repr, cfg.int64Repr with
    | .bigInt64Array, .bigint => typed .bigInt64Array
    | _, _ => generic
  | .float => match cfg.arrayFloatRepr with
    | .typedArray => typed .float64Array
    | .genericArray => generic
  | .float32 => match cfg.arrayFloatRepr with
    | .typedArray => typed .float32Array
    | .genericArray => generic
  | _ => generic

/-- The name of member `j` of a block of a signature, as a JavaScript type name. -/
def refName {ks : List Nat} : Ref ks → String :=
  go 0
where
  go {ks : List Nat} (depth : Nat) : Ref ks → String
    | .here j => s!"D{depth}_{j.val}"
    | .there r => go (depth + 1) r

mutual
/-- The layout of a Lean type in JavaScript. -/
def lowerTy (cfg : JsConfig) {ks : List Nat} {d : Bool} : Ty ks d → JsTy
  | .prim p => .terminal (lowerScalarPrim cfg p)
  | .fn a b => .fn (lowerTy cfg a) (lowerTy cfg b)
  | .array (.prim p) => lowerArrayPrim cfg p
  | .array t => .array (lowerTy cfg t)
  | .list t => .list (lowerTy cfg t)
  | .enum s => .enum s.nOfConstructors s.shift
  | .record t fs => .record (lowerTy cfg t :: lowerFields cfg fs)
  | .union cs (h := _) => .union (lowerCtors cfg cs)
  | .data r => .data (refName r)
  | .thunk t => .thunk (lowerTy cfg t)
  | .lazy t => .lazy (lowerTy cfg t)
/-- The layouts of the fields of a record or a constructor. -/
def lowerFields (cfg : JsConfig) {ks : List Nat} : Fields ks → List JsTy
  | .one t => [lowerTy cfg t]
  | .cons t fs => lowerTy cfg t :: lowerFields cfg fs
/-- The layouts of the fields of a constructor. -/
def lowerCtor (cfg : JsConfig) {ks : List Nat} {b : Bool} : Ctor ks b → List JsTy
  | .nullary => []
  | .fields fs => lowerFields cfg fs
/-- The layouts of the constructors of a union. -/
def lowerCtors (cfg : JsConfig) {ks : List Nat} {bs : List Bool} : Ctors ks bs →
    List (List JsTy)
  | .two a b => [lowerCtor cfg a, lowerCtor cfg b]
  | .cons c cs => lowerCtor cfg c :: lowerCtors cfg cs
end

example : lowerTy JsConfig.default (Ty.nat : Ty []) = .terminal .bigint_nat := rfl
example : lowerTy JsConfig.presetPBO (Ty.nat : Ty []) = .terminal .uint53 := rfl
example : lowerTy JsConfig.default (.array (.prim .uint8) : Ty []) =
    .typedArray .uint8Array .uint8 := rfl
example : lowerTy JsConfig.presetPBO (.array (.prim .uint8) : Ty []) =
    .array (.terminal .uint8) := rfl

end MoreJs

end
