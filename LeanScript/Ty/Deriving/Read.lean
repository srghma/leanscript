module

public meta import Lean
public meta import LeanScript.Ty.Class
public meta import LeanScript.Ty.WfTactic

@[expose] public section

meta section

/-!
# `deriving LeanScriptTyWf`: reading a declaration

The table of trees already built, what the handler reads off a Lean declaration, and the
dependency graph of a `mutual` block.  The handler itself is `LeanScript.Ty.Deriving`.
-/

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

/-! ## The table of trees already built -/

/-- A tree this project has already built, with the constant it was stored in and the
    theorem that it is a type. -/
structure SharedTy where
  /-- The hash of the tree, which is what the lookup is keyed on. -/
  hash : UInt64
  /-- The `def` holding the tree. -/
  declName : Name
  /-- The `theorem` that it is a type. -/
  wfName : Name
  deriving Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- Every tree `deriving LeanScriptTyWf` has built, in this module and in every module it
    imports.  Sharing spans modules because this does. -/
initialize sharedTyExt : SimplePersistentEnvExtension SharedTy (Array SharedTy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.flatten }

/-- The constants holding this tree, if some declaration has already been given it. -/
def findShared? (value : Expr) : MetaM (Option (Name × Name)) := do
  let env ← getEnv
  let h := value.hash
  for e in sharedTyExt.getState env do
    if e.hash == h then
      if let some ci := env.find? e.declName then
        if ci.value? == some value then return some (e.declName, e.wfName)
  return none

/-! ## Reading a Lean declaration -/

/-- What a Lean type translates to: a tree, nothing (it carries no value), or no tree at
    all, with the reason. -/
inductive TransRes where
  /-- A tree of the language. -/
  | ok : Expr → TransRes
  /-- A type the language erases: it carries no value. -/
  | erased
  /-- No shape of the language describes it, for this reason. -/
  | no : MessageData → TransRes

/-- Is this a type the language erases — a proposition, or a one-value type? -/
def isErasedType (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  match (← whnf e).getAppFn with
  | .const n _ => return n == ``Unit || n == ``PUnit
  | _ => return false

/-- Is this binder a **type field** — a field whose value is a type?  The field itself is
    erased, since a type carries no run-time value; a later field that holds a *value of
    it* is what the handler cannot translate. -/
def isTypeField (t : Expr) : MetaM Bool := do
  let t ← whnf t
  return t.isSort && t != .sort .zero

/-- Is this binder a type field, or a *family* of them — `State : Type`, `Elem : State →
    Type`, `f : Nat → Type`?  A declaration with such a field hides a type from the
    language: a value of it is a value of a type the model does not name, which is what
    the language calls an existential, and which it does not model. -/
def isExistentialField (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ body => isTypeField body

/-- The first field of `n` that hides a type, if it has one.  The declaration is refused
    as a whole: `LeanScript` has no existential type, so a declaration whose values carry
    a type of their own is not one it models. -/
def existentialField? (n : Name) (params : Array Expr) : MetaM (Option Name) := do
  let some (.inductInfo ind) := (← getEnv).find? n | return none
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let cty ← instantiateForall ci.type (params.extract 0 ind.numParams)
    let hit? ← forallTelescopeReducing cty fun xs _ => do
      for x in xs do
        if ← isExistentialField (← inferType x) then
          return some (← x.fvarId!.getUserName)
      return none
    if let some f := hit? then return some f
  return none

/-- Is this a binder the translation drops — a proof, a type, an instance or a one-value
    type? -/
def erasedBinder (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if (← whnf t).isSort then return true
  if ← isErasedType t then return true
  if (← isClass? t).isSome then return true
  return false

/-- The types of the values the declaration `n` **caches** — a `@[computed_field]` is
    stored in the runtime object, so it is one more field of it — in declaration order.

    Lean records a computed field by building a second inductive, `n._impl`, whose
    constructors carry the cached values ahead of the fields, so the types are read off a
    constructor that has a field.  A declaration all of whose constructors are field-less
    stores its cached values nowhere — they are a function of the constructor number —
    and the types are read off the `@[computed_field]` functions instead. -/
def computedFieldTys (n : Name) : MetaM (Except MessageData (List Expr)) := do
  let env ← getEnv
  if (env.find? (n ++ `_impl)).isNone then return .ok []
  let some (.inductInfo ind) := env.find? n | return .ok []
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    if ci.numFields == 0 then continue
    let some (.ctorInfo cimpl) := env.find? (c ++ `_impl)
      | return .error m!"`{n}` caches values in a way this handler cannot read"
    let k := cimpl.numFields - ci.numFields
    if k == 0 then return .ok []
    return ← forallTelescopeReducing cimpl.type fun xs _ => do
      let mut tys : List Expr := []
      for x in xs[ind.numParams:ind.numParams + k] do
        tys := tys ++ [← inferType x]
      return .ok tys
  -- every constructor is field-less: the cached value is a function of the constructor
  -- number and is stored nowhere, so its type is read off the function that computes it.
  -- Lean gives every computed field `f` of `n` a companion `n.f._override`.
  let mut fields : Array (Nat × Name × Expr) := #[]
  for (m, _) in env.constants.toList do
    let .str base "_override" := m | continue
    unless n.isPrefixOf base && base != n do continue
    if ind.ctors.contains base then continue
    if base == n ++ `casesOn || base == n ++ `rec || base == n ++ `recOn then continue
    let some ci := env.find? base | continue
    let res ← forallTelescopeReducing ci.type fun _ body => whnf body
    if res.hasLooseBVars || res.hasFVar then
      return .error m!"`{n}` caches a value whose type this handler cannot read"
    let line := (← findDeclarationRanges? base).map (·.range.pos.line) |>.getD 0
    fields := fields.push (line, base, res)
  let sorted := fields.qsort fun a b =>
    if a.1 == b.1 then Name.lt a.2.1 b.2.1 else a.1 < b.1
  return .ok (sorted.toList.map (·.2.2))

/-! ## The dependency graph of a `mutual` block

Lean's `mutual` blocks are not always *families*: a block whose members do not each reach
the others is several declarations that happen to be written together, and each of its
strongly connected components can be declared on its own, in dependency order. -/

/-- Which members of the block `names` the member `m` mentions in the types of the fields
    it keeps. -/
def blockDeps (names : List Name) (params : Array Expr) (m : Name) :
    MetaM (Except MessageData (List Name)) := do
  let some (.inductInfo mind) := (← getEnv).find? m
    | return .error m!"`{m}` is not an inductive declaration"
  let mut deps : List Name := []
  for c in mind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (params.extract 0 mind.numParams)
    let ds ← forallTelescopeReducing cty fun xs _ => do
      let mut ds : List Name := []
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        for k in t.getUsedConstants do
          if names.contains k && !ds.contains k then ds := ds ++ [k]
      return ds
    for d in ds do
      if !deps.contains d then deps := deps ++ [d]
  return .ok deps

/-- Everything reachable from `start` in the graph `edges`, `start` included. -/
def nameReach (edges : List (Name × List Name)) (start : Name) : List Name :=
  go edges.length [start] [start]
where
  /-- Breadth-first closure: `acc` is what has been reached, `frontier` what was reached
      last, and `fuel` bounds the number of rounds by the number of members. -/
  go : Nat → List Name → List Name → List Name
    | 0, acc, _ => acc
    | _ + 1, acc, [] => acc
    | k + 1, acc, frontier =>
        let next := frontier.flatMap fun m => ((edges.find? (·.1 == m)).map (·.2)).getD []
        let fresh := next.filter fun m => !acc.contains m
        go k (acc ++ fresh) fresh

/-- The members of the block `names` that belong to the same strongly connected component
    as `n`: the ones `n` reaches and that reach `n`, in declaration order. -/
def blockComponent (names : List Name) (edges : List (Name × List Name)) (n : Name) :
    List Name :=
  names.filter fun m => (nameReach edges n).contains m && (nameReach edges m).contains n

end LeanScript.Deriving

end

end
