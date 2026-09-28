module

public import JsTerm.Ty.Config
public import JsTerm.Ty.Basic
public import LeanScript.Term.Syntax.Common

@[expose] public section

set_option autoImplicit false

/-!
# Lowering a Lean type to its `JsTy`

`lowerTy cfg τ` is the layout in JavaScript of the Lean type `τ` (a `LeanScript.Ty`), under
the configuration `cfg`.  `lowerScalarPrim` and `lowerArrayPrim` are the
configuration-dependent part: how a leaf, and an array of leaves, is represented.
-/

namespace MoreJs

open LeanScript

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
