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
configuration-dependent part: how a leaf, and an array of leaves, is represented; and
`cfg.listRepr` says whether the standard library's `List` (`Ty.list`) is a JavaScript array
(`JsTy.list`) or tagged cons cells (`JsTy.consList`).  A user datatype shaped like a list
(`inductive MyList | nil | cons (h : α) (t : MyList)`) is never `Ty.list` — only `List` is read
as the built-in list — so it is a tagged union whatever `listRepr` says.
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

/-- The number of datatypes in the blocks `ks` (a block of size `k` has `k + 1`). -/
def blocksSize (ks : List Nat) : Nat := (ks.map (· + 1)).sum

/-- The number of a declared datatype: its position among the datatypes of the signature,
    **oldest first** (the members of the oldest block are `0`, `1`, …).  It does not depend on
    the scope: a datatype of an older block keeps its number under the newer blocks
    (`refIndex_there`), so the same datatype has the same declaration (`JsObjId.decl`)
    wherever it is named. -/
def refIndex : {ks : List Nat} → Ref ks → Nat
  | _ :: ks, .here j => blocksSize ks + j.val
  | _ :: _, .there r => refIndex r

/-- A datatype of an older block keeps its number. -/
@[simp] theorem refIndex_there {k : Nat} {ks : List Nat} (r : Ref ks) :
    refIndex (Ref.there (k := k) r) = refIndex r := rfl

/-- The number of a datatype is below the number of datatypes of the signature. -/
theorem refIndex_lt : {ks : List Nat} → (r : Ref ks) → refIndex r < blocksSize ks
  | k :: ks, .here j => by
    simp only [refIndex, blocksSize, List.map_cons, List.sum_cons]; omega
  | k :: ks, .there r => by
    have := refIndex_lt r
    simp only [refIndex, blocksSize, List.map_cons, List.sum_cons] at *; omega

/-- Two datatypes of a signature have the same number only if they are the same datatype. -/
theorem refIndex_injective : {ks : List Nat} → {r₁ r₂ : Ref ks} →
    refIndex r₁ = refIndex r₂ → r₁ = r₂
  | _ :: _, .here j₁, .here j₂, h => by
    simp only [refIndex] at h; exact congrArg Ref.here (Fin.ext (by omega))
  | _ :: _, .here _, .there r₂, h => by
    have := refIndex_lt r₂; simp only [refIndex] at h; omega
  | _ :: _, .there r₁, .here _, h => by
    have := refIndex_lt r₁; simp only [refIndex] at h; omega
  | _ :: _, .there _, .there _, h => congrArg Ref.there (refIndex_injective h)

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
  | .list t => match cfg.listRepr with
    | .stdListToJsArray => .list (lowerTy cfg t)
    | .taggedUnion => .obj .consList [lowerTy cfg t]
  | .enum s => .enum s.nOfConstructors s.shift
  | .record t fs => .obj (.record (lowerFields cfg fs).length.succ) (lowerTy cfg t :: lowerFields cfg fs)
  | .union cs (h := _) =>
    .obj (.union ((lowerCtors cfg cs).map List.length)) (lowerCtors cfg cs).flatten
  | .data r => .obj (.decl (cfg.declCanon.getD (refIndex r) (refIndex r))) []
  | .thunk t => .thunk (lowerTy cfg t)
  | .lazy t => .fn [] (lowerTy cfg t)
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
    .typedArray .uint8 := rfl
example : lowerTy JsConfig.presetPBO (.array (.prim .uint8) : Ty []) =
    .array (.terminal .uint8) := rfl
/-- Under `ListRepr.taggedUnion` the standard library's `List` is laid out as cons cells. -/
theorem lowerTy_list_of_taggedUnion (cfg : JsConfig) (h : cfg.listRepr = .taggedUnion)
    {ks : List Nat} {d : Bool} (t : Ty ks) :
    lowerTy cfg (Ty.list (d := d) t) = .obj .consList [lowerTy cfg t] := by
  simp only [lowerTy, h]

/-- Under `ListRepr.stdListToJsArray` the standard library's `List` is laid out as a JavaScript
    array. -/
theorem lowerTy_list_of_stdListToJsArray (cfg : JsConfig) (h : cfg.listRepr = .stdListToJsArray)
    {ks : List Nat} {d : Bool} (t : Ty ks) :
    lowerTy cfg (Ty.list (d := d) t) = .list (lowerTy cfg t) := by
  simp only [lowerTy, h]

/-- A declared datatype — a user's list-like inductive (`MyList`) among them — is laid out the
    same whatever `listRepr` says: only the standard library's `List` follows the knob. -/
theorem lowerTy_data_listRepr (cfg : JsConfig) (r : ListRepr) {ks : List Nat} {d : Bool}
    (ref : Ref ks) :
    lowerTy { cfg with listRepr := r } (Ty.data (d := d) ref) = lowerTy cfg (Ty.data (d := d) ref) := by
  simp only [lowerTy]

example : lowerTy JsConfig.presetFaithful (.list .nat : Ty []) =
    .obj .consList [.terminal .bigint_nat] := rfl
/-- A record is the anonymous declaration of its number of fields, at its fields. -/
example : lowerTy JsConfig.presetPBO (.record .nat (.one .string) : Ty []) =
    .obj (.record 2) [.terminal .uint53, .terminal .string] := rfl
/-- `Option String` and `Option Nat` share the anonymous declaration `union [0, 1]`. -/
example : lowerTy JsConfig.presetPBO (.union (.two .nullary (.fields (.one .string))) : Ty []) =
    .obj (.union [0, 1]) [.terminal .string] := rfl
example : lowerTy JsConfig.presetPBO (.union (.two .nullary (.fields (.one .nat))) : Ty []) =
    .obj (.union [0, 1]) [.terminal .uint53] := rfl
/-- A declared datatype is its stable number: member `1` of the only block of sizes `[2]`
    (three members), and the same datatype seen from under a newer block of two members. -/
example : lowerTy JsConfig.presetPBO (.data (.here ⟨1, by decide⟩) : Ty [2]) =
    .obj (.decl 1) [] := rfl
example : lowerTy JsConfig.presetPBO (.data (.there (.here ⟨1, by decide⟩)) : Ty [1, 2]) =
    .obj (.decl 1) [] := rfl
example : lowerTy JsConfig.presetPBO (.data (.here ⟨1, by decide⟩) : Ty [1, 2]) =
    .obj (.decl 4) [] := rfl
example : lowerTy JsConfig.presetPBO (.list .nat : Ty []) =
    .list (.terminal .uint53) := rfl

end MoreJs

end
