module

public import LeanScript.Nominal.Term
public meta import Lean.Elab.Command

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Reading Lean types

The first stage shared by `leanscript_signature`, `#leanscript_get_ty` and
`#leanscript_get_ctor`: a Lean type is normalised (`normType`), its head is classified
(`classify`: a leaf, `→`, `Array`, `Thunk`, a type variable, or an inductive instance), and
the fields of an inductive instance's constructors are read (`readCtors`), with the fields
the language erases (proofs, instances, `Unit`) dropped.

A *type variable* is a local `α : Type`: `#leanscript_get_ctor Option.some` reads `Option α`
with `α` a local, and `α` becomes an argument `(α : Ty ks)` of the generated function.
-/

open Lean Meta Elab

namespace LeanScript.Nominal.Gen

/-- Every error of the generators starts with this. -/
def errPrefix : String := "LeanScript"

/-- Throw an error of the generators. -/
def fail {α : Type} (msg : MessageData) : MetaM α :=
  throwError m!"{errPrefix}: {msg}"

/-- The head of a (normalised) type. -/
inductive Head where
  /-- A leaf, given by the `LeanPrimTy` that names it. -/
  | prim (p : Lean.Term)
  /-- A non-dependent function type. -/
  | fn (a b : Expr)
  /-- `Array a`. -/
  | array (a : Expr)
  /-- `Thunk a`. -/
  | thunk (a : Expr)
  /-- A type variable (a local `α : Type`). -/
  | var (x : FVarId)
  /-- An instance of an inductive type. -/
  | node (e : Expr)

/-- Normalise a type: head normal form, type arguments normalised. -/
partial def normType (e : Expr) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e with
  | .forallE n a b bi =>
    if b.hasLooseBVars then return e
    return .forallE n (← normType a) (← normType b) bi
  | _ =>
    let fn := e.getAppFn
    if fn.isConst then
      let args ← e.getAppArgs.mapM fun a => do
        if (← isType a) then normType a else pure a
      return mkAppN fn args
    return e

/-- A natural number literal, if the expression evaluates to one. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let e' ← whnf e
  if let some n := e'.rawNatLit? then return some n
  evalNat e

/-- The head of a (normalised) type. -/
def classify (e : Expr) : MetaM Head := do
  if let .forallE _ a b _ := e then
    if b.hasLooseBVars then fail m!"dependent function type{indentExpr e}"
    return .fn a b
  if e.isFVar then
    if (← whnf (← inferType e)) == mkSort Level.one then return .var e.fvarId!
    fail m!"the type{indentExpr e}\nis a local that is not a type variable"
  let some (c, _) := e.getAppFn.const? | fail m!"not a type former application{indentExpr e}"
  let args := e.getAppArgs
  let p (s : Lean.Term) : MetaM Head := return .prim s
  match c, args.size with
  | ``Bool, 0 => p (← `(LeanPrimTy.bool))
  | ``Nat, 0 => p (← `(LeanPrimTy.nat))
  | ``Int, 0 => p (← `(LeanPrimTy.int))
  | ``UInt8, 0 => p (← `(LeanPrimTy.uint8))
  | ``UInt16, 0 => p (← `(LeanPrimTy.uint16))
  | ``UInt32, 0 => p (← `(LeanPrimTy.uint32))
  | ``UInt64, 0 => p (← `(LeanPrimTy.uint64))
  | ``Int8, 0 => p (← `(LeanPrimTy.int8))
  | ``Int16, 0 => p (← `(LeanPrimTy.int16))
  | ``Int32, 0 => p (← `(LeanPrimTy.int32))
  | ``Int64, 0 => p (← `(LeanPrimTy.int64))
  | ``Char, 0 => p (← `(LeanPrimTy.char))
  | ``String, 0 => p (← `(LeanPrimTy.string))
  | ``String.Pos.Raw, 0 => p (← `(LeanPrimTy.stringPosRaw))
  | ``Substring.Raw, 0 => p (← `(LeanPrimTy.substringRaw))
  | ``String.Slice, 0 => p (← `(LeanPrimTy.stringSlice))
  | ``Float, 0 => p (← `(LeanPrimTy.float))
  | ``Float32, 0 => p (← `(LeanPrimTy.float32))
  | ``Float.Model, 0 => p (← `(LeanPrimTy.floatModel))
  | ``Float32.Model, 0 => p (← `(LeanPrimTy.float32Model))
  | ``BitVec, 1 =>
    let some n ← natLit? args[0]! | fail m!"the width of{indentExpr e}\nis not a numeral"
    if n = 0 then fail m!"`BitVec 0` has one value"
    p (← `(LeanPrimTy.bitvec $(quote n)))
  | ``String.Pos, 1 =>
    let some s := (match (← whnf args[0]!) with | .lit (.strVal s) => some s | _ => none)
      | fail m!"the string of{indentExpr e}\nis not a literal"
    if s = "" then fail m!"`String.Pos \"\"` has one value"
    p (← `(LeanPrimTy.stringPos $(quote s)))
  | ``Array, 1 => return .array args[0]!
  | ``Thunk, 1 => return .thunk args[0]!
  | _, _ =>
    unless ((← getEnv).find? c).any (·.isInductive) do
      fail m!"`{c}` is not an inductive type{indentExpr e}"
    return .node e

/-- The built-in table of enum numberings: the number the first constructor prints as.
    `Ordering` prints as `-1, 0, 1`. -/
def enumShift (c : Name) : Int :=
  if c == ``Ordering then -1 else 0

/-- Is a field of this type erased: a proof, an instance, or `Unit`? -/
def isErasedField (bi : BinderInfo) (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if bi.isInstImplicit then return true
  if (← isClass? t).isSome then return true
  let t ← whnf t
  return t.isAppOf ``PUnit || t.isAppOf ``Unit

/-- The constructors of an inductive instance: their names and their relevant fields, in
    declaration order.  The instance may mention type variables. -/
def readCtors (e : Expr) : MetaM (Array (Name × Array Expr)) := do
  let some (c, us) := e.getAppFn.const? | fail m!"not an inductive instance{indentExpr e}"
  let info ← getConstInfoInduct c
  if info.numIndices ≠ 0 then
    fail m!"`{c}` is an inductive family with indices, which is not supported{indentExpr e}"
  let params := e.getAppArgs
  unless params.size = info.numParams do
    fail m!"`{c}` is not fully applied{indentExpr e}"
  info.ctors.toArray.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    forallTelescopeReducing ty fun xs _ => do
      let mut fields : Array Expr := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let t := decl.type
        if ← isErasedField decl.binderInfo t then continue
        if (← whnf t).isSort then
          fail m!"the constructor `{ctor}` has a field whose value is a type \
            (existential typing is not supported)"
        if xs.any (fun d => t.containsFVar d.fvarId!) then
          fail m!"a field of the constructor `{ctor}` has a type that depends on an earlier \
            field{indentExpr t}"
        fields := fields.push (← normType t)
      return (ctor, fields)

/-- The inductive instances a type mentions directly. -/
partial def occurrences (e : Expr) : MetaM (Array Expr) := do
  match ← classify e with
  | .prim _ | .var _ => return #[]
  | .fn a b => return (← occurrences a) ++ (← occurrences b)
  | .array a | .thunk a => occurrences a
  | .node n => return #[n]

end LeanScript.Nominal.Gen

end
