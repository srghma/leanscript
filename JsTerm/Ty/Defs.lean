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
| `record t fs` | `obj (record n) [f₁, …, fₙ]` | an object `{ _1: f₁, _2: f₂, … }` (two fields or more) |
| `union cs` | `obj (union [a₀, a₁, …]) [fields…]` | an object `{ tag: i, _1: f₁, _2: f₂, … }`, the constructor's position `i` counting from `0` (two constructors or more; `aᵢ` fields each) |
| `enum s` | `enum n shift` | the number `shift + i` |
| `list t` | `list t` (`listRepr = stdListToJsArray`) | an (immutable) JavaScript array |
| `list t` | `obj consList [t]` (`listRepr = taggedUnion`) | cons cells: `{ tag: 0 }` (`[]`) and `{ tag: 1, _1: head, _2: tail }` |
| `fn a (fn b c)` | `fn [a, b] c` | a function of all its arguments (uncurried) |
| `thunk t` | `thunk t` | a memoising thunk object |
| `lazy t` | `fn [] t` | a function of no argument |
| `data r` | `obj (decl i) []` | a declared datatype: an object (or array, or function) laid out as its body, declaration `i` of the signature (`JsSig`) |

A Lean function type is uncurried **maximally**: `Nat → Nat → Nat` is `fn [nat, nat] nat`, a
JavaScript function of two arguments, wherever the value goes (a parameter, a field, the
result of a function).  A delay (`lazy t`) is a function of no argument, so `Nat → Lazy
Nat` stays `fn [nat] (fn [] nat)`: only the arrows of `Ty.fn` are merged.

## Object types are nominal

Every object type is a **name**, `obj id args` (`proposals/TypedDataProposals3.md`, Proposals
P and Q): an identity (`JsObjId`) and type arguments.  The layout — the fields of a record, the
constructors of a union — is not written in the type; it is read from the declaration
(`JsSig.fieldsOf`, `JsSig.ctorsOf`), so a record, a tagged union, a cons cell and a value of a
declared (recursive) datatype are all built and taken apart by the same four forms of the
grammar (`record_mk`, `destructure`, `union_mk`, `unionCases`), at one index, `obj id args`.
Equality of types stays syntactic (an identity and a list of types): no type contains a binder.

* A structural record or union of the source is an **anonymous declaration** whose identity is
  its layout (`record n`, `union arities`) and whose arguments are its fields: equal layouts
  share their declaration, and it needs no table.
* `List α` as cons cells is the prelude's declaration `consList` at `[α]`: one declaration for
  every element type.
* A declared datatype of the source is `decl i`: its number is stable (`refIndex`: the position
  of the datatype among the datatypes of the source's signature, oldest first, whatever the
  scope), and its body — one layer, a structural type whose recursive positions are
  `obj (decl j) []` — is row `i` of the signature `JsSig`, a parameter of the grammar.  One layer
  in and out are the casts `JsExpr.fold` / `JsExpr.unfold`, which print as nothing.

Records and unions have two fields or constructors or more (the source types guarantee both: a
structure of one field is unboxed, a type of one constructor is a record, before this stage).

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

/-- The identity of an object type (`JsTy.obj`): **every** object the backend builds (a record,
    a tagged union, a cons cell, a value of a declared datatype) has a nominal type, an
    identity and a list of type arguments, and the identity says where the layout comes from.

    * `record n` and `union arities` are the **anonymous** declarations of the structural types
      of the source: the identity *is* the layout (the number of fields of a record, the number
      of fields of each constructor of a union), and the arguments are the types of the fields,
      in order.  So two structural types of the same layout share their declaration (`Option
      String` and `Option Nat` are `union [0, 1]` at `[string]` and at `[nat]`), and the
      layout of an anonymous declaration needs no table.
    * `consList` is the one declaration of the prelude with a parameter: `List α` as cons cells,
      `[[], [α, List α]]`, at the argument `[α]`.  It serves every element type.
    * `decl i` is declaration `i` of the signature of the function (`JsSig`): a declared, possibly
      recursive, datatype of the source (its number is its position among the datatypes of the
      source's signature, oldest first: `refIndex`, the same in every scope). -/
inductive JsObjId where
  /-- An anonymous record of `n` fields (`n ≥ 2`): `{ _1: f₁, …, _n: fₙ }`. -/
  | record (n : Nat)
  /-- An anonymous union whose constructors have `arities` fields: `{ tag: i, _1: f₁, … }`. -/
  | union (arities : List Nat)
  /-- The prelude's `List α` as cons cells: `{ tag: 0 }` and `{ tag: 1, _1: head, _2: tail }`. -/
  | consList
  /-- Declaration `i` of the signature. -/
  | decl (i : Nat)
  deriving Inhabited, Repr, DecidableEq, Hashable

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
  /-- A function of the arguments `doms` (none for a delay): `(x₁, …, xₙ) => …`. -/
  | fn (doms : List JsTy) (cod : JsTy)
  /-- An enum: a number, `shift` for the first of its `n` constructors. -/
  | enum (n : Nat) (shift : Int)
  /-- A memoised delay. -/
  | thunk (t : JsTy)
  /-- An object of the declaration `id` at the type arguments `args` (`JsObjId`): records,
      tagged unions, cons cells and declared datatypes alike.  Its layout is read from the
      declaration (`JsSig.fieldsOf`, `JsSig.ctorsOf`), never from the type itself. -/
  | obj (id : JsObjId) (args : List JsTy)
  deriving Inhabited, Repr

/-- The prelude's `List α` as cons cells (`ListRepr.taggedUnion`). -/
abbrev JsTy.consList (α : JsTy) : JsTy := .obj .consList [α]

/-- The anonymous record of the fields `fs` (two or more). -/
abbrev JsTy.record (fs : List JsTy) : JsTy := .obj (.record fs.length) fs

/-- The anonymous union of the constructors `cs` (two or more), each the list of its fields. -/
abbrev JsTy.union (cs : List (List JsTy)) : JsTy := .obj (.union (cs.map List.length)) cs.flatten

/-- The fields `ts` cut into the constructors of `arities` fields. -/
def splitArities : List Nat → List JsTy → List (List JsTy)
  | [], _ => []
  | a :: as, ts => ts.take a :: splitArities as (ts.drop a)

/-- The signature of a function: its declared datatypes.  Declaration `i` is the **body** of
    datatype `i`, one layer of it: the structural type (an anonymous record or union, or the one
    field of a datatype of one constructor of one field) whose recursive positions are
    `obj (decl j) []`.  It is a parameter of the grammar (`JsExpr S …`): an expression's type
    only names a declaration, and the layout is read here. -/
structure JsSig where
  /-- The body of each declaration, by its number. -/
  decls : Array JsTy := #[]
  deriving Inhabited, Repr

namespace JsSig

/-- The body of declaration `i` (itself, when the signature has no declaration `i`). -/
def body (S : JsSig) (i : Nat) : JsTy := S.decls[i]?.getD (.obj (.decl i) [])

/-- The constructors of the union declaration `id` at the arguments `args`, each the list of
    its fields (none for a record or a declaration that is not a union). -/
def ctorsOf (S : JsSig) : JsObjId → List JsTy → List (List JsTy)
  | .union ar, args => splitArities ar args
  | .consList, [α] => [[], [α, .obj .consList [α]]]
  | .consList, _ => []
  | .record _, _ => []
  | .decl i, _ => match S.body i with
    | .obj (.union ar) args => splitArities ar args
    | _ => []

/-- The fields of the record declaration `id` at the arguments `args` (none for a union or a
    declaration that is not a record). -/
def fieldsOf (S : JsSig) : JsObjId → List JsTy → List JsTy
  | .record _, args => args
  | .decl i, _ => match S.body i with
    | .obj (.record _) args => args
    | _ => []
  | _, _ => []

end JsSig

end MoreJs

end
