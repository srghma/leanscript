module

public import LeanScript.Term.Syntax.Term
public meta import Lean.Elab.Command
public meta import Lean.Meta.Constructions.CasesOn

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Reading Lean types: errors, heads and families

The error prefix of the generators, the classification `Head` of a Lean type, and the
recognition of erased fields and of instances of inductive families.
-/

open Lean Meta Elab

namespace LeanScript.Gen

/-- Every error of the generators starts with this. -/
def errPrefix : String := "LeanScript"

/-- Throw an error of the generators. -/
def fail {α : Type} (msg : MessageData) : MetaM α :=
  throwError m!"{errPrefix}: {msg}"

/-- The head of a (normalised) type. -/
inductive Head where
  /-- A leaf, given by the `LeanPrimTy` that names it. -/
  | prim (p : Lean.Term)
  /-- `Lean.Name`: not a leaf, but the list of its components (`Ty.leanName`). -/
  | leanName
  /-- A non-dependent function type. -/
  | fn (a b : Expr)
  /-- `Array a`. -/
  | array (a : Expr)
  /-- `List a`, read as the built-in list (`Ty.list`) when `builtinListOption` is set. -/
  | list (a : Expr)
  /-- `Thunk a`: a memoised delay. -/
  | thunk (a : Expr)
  /-- `Unit → a`: a delay recomputed every time. -/
  | lazy (a : Expr)
  /-- A type variable (a local `α : Type`). -/
  | var (x : FVarId)
  /-- An instance of an inductive type. -/
  | node (e : Expr)
  deriving Inhabited, Repr, BEq

/-- The option (not registered, set by the `leanscript` tool) under which `List α` is read as
    the built-in list `Ty.list α` (an immutable JavaScript array) instead of as a datatype
    that a signature must declare. -/
def builtinListOption : Name := `leanscript.builtinList

/-- Is `List α` read as the built-in list (`builtinListOption`)? -/
def useBuiltinList : MetaM Bool :=
  return (← getOptions).getBool builtinListOption false

/-- Is a field of this type erased: a proof or an instance?  (A `Unit` field of a
    constructor is erased too, but only there: see `isUnitField`.) -/
def isErasedField (bi : BinderInfo) (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if bi.isInstImplicit then return true
  return (← isClass? t).isSome

/-- Is a constructor field of this type erased because it is `Unit` (`PUnit`)?  `Unit` has one
    value, so a field of it carries no information: it is dropped from the constructor, and
    the value of the field is `()` wherever it is read.  So `Option Unit` has two field-less
    constructors, and is read as `Bool` (two values are only ever `Bool`: `none` is `false`,
    `some ()` is `true`), and `Nat × Unit` as `Nat`.  `Unit` itself still has no type in the
    language (a value of type `Unit` that is not a constructor field is refused). -/
def isUnitField (t : Expr) : MetaM Bool := do
  let t ← whnfR t
  return t.isConstOf ``Unit || t.getAppFn.isConstOf ``PUnit

/-- Is a constructor field of this type erased (`isErasedField`, `isUnitField`)? -/
def isErasedCtorField (bi : BinderInfo) (t : Expr) : MetaM Bool := do
  if ← isErasedField bi t then return true
  isUnitField t

/-- The inductive family (with indices, valued in `Type`) a type is a full application of:
    its information, universe levels, parameters and indices. -/
def familyApp? (e : Expr) : MetaM (Option (InductiveVal × List Level × Array Expr × Array Expr)) := do
  let some (c, us) := e.getAppFn.const? | return none
  let some (.inductInfo info) := (← getEnv).find? c | return none
  let args := e.getAppArgs
  unless info.numIndices > 0 && args.size == info.numParams + info.numIndices do return none
  if ← isProp e then return none
  return some (info, us, args[:info.numParams].toArray, args[info.numParams:].toArray)

end LeanScript.Gen

end
