module

public import LeanScript.Expr.Term
public import LeanScript.Ty.Class
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving.Build

@[expose] public section

meta section

/-!
# `#leanscript_ctor`: a constructor of any datatype, as a function on terms

```lean
#leanscript_ctor `Process `halt      -- the constructor `Process.halt`
#leanscript_ctor `ProcessOption `some
#leanscript_ctor `Option `some
#leanscript_ctor `Prod               -- a type with one constructor names it
#leanscript_layout `Process `step    -- the type of what that constructor builds
```

`#leanscript_ctor I c` is a **term**: the function that builds a `LeanScript.Term` out of the
terms of the fields of the constructor `I.c`.  `#leanscript_layout I c` is the function that
gives the `TyWf` of what it builds.  Both are generated the first time they are asked for,
as the definitions

| name | what it is |
| :-- | :-- |
| `I.c.leanScriptCtor` | the constructor function |
| `I.c.leanScriptLayout`, or `I.leanScriptLayout` | its layout (see *two kinds of datatype*) |

and are **cached**: the table of generated functions is an environment extension, so a later
`#leanscript_ctor` of the same constructor — in the same module or in any module that imports
it — is the constant already there, and nothing is generated twice.  When `I` belongs to
another module the names are put under the current module's name, so that two modules that do
not import each other can both ask for `Option.some` without a clash.

## The arguments of the function

The function takes the arguments the Lean constructor takes, in the same order, with a
**type** replaced by its `TyWf` and a **value** replaced by a `Term`:

```lean
Process.halt  : (α : Type) → (HaltedState : Type) → (HaltedState → Nat) → Process α
#leanscript_ctor `Process `halt :
  {Sg : Sig} → {Γ : Ctx} → (α HaltedState : TyWf) →
    Term Sg Γ (HaltedState ⇒ .prim .nat) → Term Sg Γ (Process.halt.leanScriptLayout α HaltedState)
```

A type is a parameter of the datatype, one of its type indices, or a type field of the
constructor (an existential).  A field whose type the language has **no tree for** — first of
all an occurrence of the datatype itself or of a member of its `mutual` block, but also a
type without a `LeanScriptTyWf` instance or a type that depends on a value — gets its tree
from one more `TyWf` argument, named after the field (`procTy`, `transTy`, …) and placed after
the type arguments.  Two fields of the same Lean type share that argument.  So a recursive
datatype is built **one layer at a time**: `List.cons` takes the tree of its tail, whatever it
is; this is exactly how a closed value of a datatype with existentials (`Process`) is written
down, where every layer may choose different types.

Every other field type is translated: a type argument is its `TyWf`, a function type is
`TyWf.fn` (a domain the language erases — `Unit`, a proof, an instance — is dropped), and an
application of a type former (`Option S`, `S × Nat`, `Array S`, `List S`, …) is the tree of
the former's own `LeanScriptTyWf` instance with the arguments' trees in place.  A field the
language erases is not an argument at all.

## Two kinds of datatype

* **No existentials** (every type field of every constructor is one of the type indices of
  its result, as `ProcessOption`'s `State` is): the datatype is one type of the language,
  shared by all its constructors — its record, its tagged union, its enum, `Bool`, or its
  one field — and each constructor builds that type, with its constructor number.  Its layout
  is `I.leanScriptLayout`, which takes the trees of **all** constructors' fields, so
  `ProcessOption.none` takes the tree of `proc` too.
* **With existentials** (`Process`): each constructor application may choose different types,
  so each constructor builds its own layout, `I.c.leanScriptLayout`: its record, or its one
  field.  Where values built with different choices meet, the caller puts them into a union
  of its own, as `TyTests/InductiveTypesTest/Existentials.lean` does.

A datatype whose model is a terminal type (`Nat`, `String`, `Char`, …) or a built-in type
former (`Array`, `Thunk`) has no constructor function — its values are literals, or have an
introduction form of their own; `Bool` is the enum of its two constructors, and an enum
whose instance chooses its own numbering (`Ordering`) keeps it.  A constructor that carries
no value (`Unit.unit`, `PUnit.unit`, a structure without fields), a proposition, and a
datatype that hides a *family* of types (`Elem : State → Type`) are refused.
-/

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType?)

/-- `LeanScript.TyWf`, as an expression. -/
def tyWfE : Expr := mkConst ``LeanScript.TyWf

/-! ## The cache -/

/-- One generated definition: what it was generated for (`kind` is `"fn"` for a constructor
    function and `"layout"` for a layout) and its name. -/
structure CtorFnEntry where
  /-- The constructor, or the datatype, it was generated for. -/
  key : Name
  /-- `"fn"` or `"layout"`. -/
  kind : String
  /-- The generated definition. -/
  decl : Name
  deriving Inhabited, BEq, Repr

/-- Every definition `#leanscript_ctor` has generated, here and in every imported module. -/
initialize ctorFnExt : SimplePersistentEnvExtension CtorFnEntry (Array CtorFnEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.flatten }

/-- The definition already generated for `key`, if there is one. -/
def cached? (key : Name) (kind : String) : CoreM (Option Name) := do
  let env ← getEnv
  for e in ctorFnExt.getState env do
    if e.key == key && e.kind == kind && env.contains e.decl then return some e.decl
  return none

/-- The name a generated definition gets: `base ++ suffix`, under the current module's name
    when `owner` was declared in another module. -/
def declNameFor (owner base : Name) (suffix : String) : CoreM Name := do
  let env ← getEnv
  let n := Name.str base suffix
  if (env.getModuleIdxFor? owner).isNone then return n
  return (← getMainModule) ++ n

/-! ## Translating the type of a field -/

/-- What a field type is translated in. -/
structure TrCtx where
  /-- The members of the datatype's `mutual` block: an occurrence of one is a hole. -/
  members : Array Name
  /-- Each type variable — parameter, type index or existential — with its `TyWf`. -/
  tyVars : Array (Expr × Expr)
  /-- The holes for the field types the language has no tree for: the Lean type, the name
      of the argument and the local it is. -/
  holes : IO.Ref (Array (Expr × Name × FVarId))
  /-- The names already taken by arguments. -/
  used : IO.Ref (Array Name)

/-- Run `k` with the holes created so far in the local context. -/
def withHoles (c : TrCtx) (k : MetaM α) : MetaM α := do
  let hs ← c.holes.get
  let mut lctx ← getLCtx
  for (_, n, id) in hs do
    unless lctx.contains id do lctx := lctx.mkLocalDecl id n tyWfE
  withLCtx lctx (← getLocalInstances) k

/-- A fresh argument name built from `base`. -/
def freshName (c : TrCtx) (base : String) : MetaM Name := do
  let used ← c.used.get
  let mut n := Name.mkSimple base
  let mut i := 2
  while used.contains n do
    n := Name.mkSimple s!"{base}{i}"
    i := i + 1
  c.used.modify (·.push n)
  return n

/-- The last component of a binder's name, without macro scopes. -/
def baseName (n : Name) : String :=
  match n.eraseMacroScopes with
  | .str _ s => s
  | _ => "x"

/-- The hole for the field type `t` of the field `field`: shared with every field of the same
    type. -/
def holeFor (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  if let some (_, _, id) := (← c.holes.get).find? (·.1 == t) then return .fvar id
  let n ← freshName c (baseName field ++ "Ty")
  let id ← mkFreshFVarId
  c.holes.modify (·.push (t, n, id))
  return .fvar id

/-- The bundle of a closed type that has an instance: `TyWf.prim p` for a terminal type,
    `tyWfOf t` otherwise. -/
def closedLayout (t inst : Expr) : MetaM Expr := do
  let b ← mkAppOptM ``LeanScript.tyWfOf #[some t, some inst]
  let tree ← whnf (mkApp (mkConst ``LeanScript.TyWf.toTy) b)
  if let (``LeanScript.Ty.prim, #[p]) := tree.getAppFnArgs then
    return mkApp (mkConst ``LeanScript.TyWf.prim) p
  return b

mutual

/-- The tree `e : Ty` of an instance, rewritten with the bundled smart constructors of
    `LeanScript.TyWf`, each stand-in `x` becoming its `y`.  `none` when the tree holds a node
    that has no bundled smart constructor (a recursive binder). -/
partial def convTy (sub : Array (Expr × Expr)) (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if let some (_, y) := sub.find? (·.1 == α) then return some y
    if sub.any (fun (x, _) => α.containsFVar x.fvarId!) then return none
    let tree ← whnf e
    if let (``LeanScript.Ty.prim, #[p]) := tree.getAppFnArgs then
      return some (mkApp (mkConst ``LeanScript.TyWf.prim) p)
    match e with
    | .proj _ 0 b => return some b
    | _ =>
      match e.getAppFnArgs with
      | (``LeanScript.TyWf.toTy, #[b]) => return some b
      | (``LeanScript.tyOf, #[α, inst]) =>
          return some (← mkAppOptM ``LeanScript.tyWfOf #[some α, some inst])
      | _ => return none
  let un (ctor : Name) (a : Expr) : MetaM (Option Expr) := do
    let some a' ← convTy sub a | return none
    return some (mkApp (mkConst ctor) a')
  match e.getAppFnArgs with
  | (``LeanScript.Ty.prim, #[p]) => return some (mkApp (mkConst ``LeanScript.TyWf.prim) p)
  | (``LeanScript.Ty.fn, #[a, b]) =>
      let some a' ← convTy sub a | return none
      let some b' ← convTy sub b | return none
      return some (mkApp2 (mkConst ``LeanScript.TyWf.fn) a' b')
  | (``LeanScript.Ty.array, #[a]) => un ``LeanScript.TyWf.array a
  | (``LeanScript.Ty.thunk, #[a]) => un ``LeanScript.TyWf.thunk a
  | (``LeanScript.Ty.lazy, #[a]) => un ``LeanScript.TyWf.lazy a
  | (``LeanScript.Ty.enum, #[s]) => return some (mkApp (mkConst ``LeanScript.TyWf.enum) s)
  | (``LeanScript.Ty.record, #[fs]) =>
      let some fs' ← convSch sub fs | return none
      return some (mkApp (mkConst ``LeanScript.TyWf.record) fs')
  | (``LeanScript.Ty.taggedUnion, #[l]) =>
      let some l' ← convSch sub l | return none
      return some (mkApp (mkConst ``LeanScript.TyWf.taggedUnion) l')
  | _ =>
      let e' ← whnf e
      if e' == e then return none
      convTy sub e'

/-- A schema, a list or a non-empty list of trees, rewritten element by element. -/
partial def convSch (sub : Array (Expr × Expr)) (e : Expr) : MetaM (Option Expr) := do
  let e ← whnf e
  let fn := e.getAppFn
  unless fn.isConst do return none
  let mut out := fn
  for a in e.getAppArgs do
    if a.isConstOf ``LeanScript.Ty then
      out := mkApp out tyWfE
      continue
    let aty ← whnf (← inferType a)
    if aty.isConstOf ``LeanScript.Ty then
      let some a' ← convTy sub a | return none
      out := mkApp out a'
    else if (aty.find? (·.isConstOf ``LeanScript.Ty)).isSome then
      let some a' ← convSch sub a | return none
      out := mkApp out a'
    else
      out := mkApp out a
  return some out

end

/-- The universe a type lives in: `u` for `Sort u`. -/
def sortLevel (t : Expr) : MetaM Level := do
  match ← whnf (← inferType t) with
  | .sort l => return l
  | _ => throwError "`#leanscript_ctor`: {t} is not a type"

mutual

/-- The `TyWf` of the field type `t`, or `none` when the language erases it. -/
partial def trTy (c : TrCtx) (field : Name) (t : Expr) : MetaM (Option Expr) := do
  if ← erasedBinder t then return none
  let t ← instantiateMVars t
  if let some (_, h) := c.tyVars.find? (·.1 == t) then return some h
  let mentions (e : Expr) := e.getUsedConstants.any c.members.contains
  if !t.hasFVar && !mentions t then
    if let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[t]) then
      return some (← closedLayout t inst)
  let tw ← whnf t
  if let some (_, h) := c.tyVars.find? (·.1 == tw) then return some h
  if tw.isForall then return some (← trFn c field tw)
  if !tw.hasFVar && !mentions tw then
    if let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[tw]) then
      return some (← closedLayout tw inst)
    return some (← holeFor c field t)
  some <$> trFormer c field tw

/-- A function type: `TyWf.fn` over the domains the language keeps.  A dependent or
    polymorphic function type is a hole. -/
partial def trFn (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let r? ← forallTelescopeReducing t fun xs body => do
    let isX (id : FVarId) := xs.any (·.fvarId! == id)
    let mut doms : Array Expr := #[]
    for x in xs do
      let d ← inferType x
      if d.hasAnyFVar isX then return none
      if (← whnf d).isSort then return none
      if ← erasedBinder d then continue
      match ← trTy c field d with
      | some a => doms := doms.push a
      | none => pure ()
    if body.hasAnyFVar isX then return none
    match ← trTy c field body with
    | none => return none
    | some r => return some (doms.foldr (fun a b => mkApp2 (mkConst ``LeanScript.TyWf.fn) a b) r)
  match r? with
  | some r => return r
  | none => holeFor c field t

/-- An application of a type former to types that mention type variables or the datatype:
    the former's own tree, at the trees of those arguments. -/
partial def trFormer (c : TrCtx) (field : Name) (t : Expr) : MetaM Expr := do
  let fn := t.getAppFn
  let .const fnName _ := fn | holeFor c field t
  if c.members.contains fnName then return ← holeFor c field t
  let args := t.getAppArgs
  let mut idxs : Array Nat := #[]
  let mut subs : Array Expr := #[]
  for i in [0:args.size] do
    let a := args[i]!
    unless a.hasFVar || a.getUsedConstants.any c.members.contains do continue
    unless ← isTypeField (← inferType a) do return ← holeFor c field t
    match ← trTy c field a with
    | some a' => idxs := idxs.push i; subs := subs.push a'
    | none => return ← holeFor c field t
  let standDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    idxs.mapIdx fun k i => (Name.mkSimple s!"X{k}", .default, fun _ => inferType args[i]!)
  let r? ← withLocalDecls standDecls fun xs => do
    let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      xs.mapIdx fun k x => (Name.mkSimple s!"instX{k}", .instImplicit,
        fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[x])
    withLocalDecls instDecls fun insts => do
      let mut args' := args
      for k in [0:idxs.size] do args' := args'.set! idxs[k]! xs[k]!
      let t' := mkAppN fn args'
      let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[t'])
        | return none
      -- stand-ins for the arguments' trees, replaced by those trees at the end
      let yDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
        xs.mapIdx fun k _ => (Name.mkSimple s!"Y{k}", .default, fun _ => pure tyWfE)
      withLocalDecls yDecls fun ys => do
        let tree ← whnf (← mkAppOptM ``LeanScript.tyOf #[some t', some inst])
        let clean? ← convTy (xs.zip ys) tree
        let clean? ← match clean? with
          | some r =>
              if (xs ++ insts).any (fun x => r.containsFVar x.fvarId!) then pure none
              else if ← isTypeCorrect r then pure (some r) else pure none
          | none => pure none
        let r ← match clean? with
          | some r => pure r
          | none => do
            -- the instance itself, at `PUnit` with the stand-in's tree as its model
            let mut vals : Array Expr := #[]
            for x in xs do vals := vals.push (mkConst ``PUnit [← sortLevel x])
            let mut instVals : Array Expr := #[]
            for k in [0:xs.size] do
              instVals := instVals.push (← mkAppM ``LeanScript.TyWf.asModelOf #[ys[k]!, vals[k]!])
            let bundle ← mkAppOptM ``LeanScript.tyWfOf #[some t', some inst]
            pure ((← mkLambdaFVars (xs ++ insts) bundle).beta (vals ++ instVals))
        return some (r.replaceFVars ys subs)
  match r? with
  | some r => return r
  | none => holeFor c field t

end

/-! ## Reading the datatype -/

/-- How a datatype is laid out: one type for all constructors, or one layout per
    constructor. -/
structure Classified where
  /-- Every type field of every constructor is a type index of its result. -/
  whole : Bool
  /-- For each constructor, for each field: the type index it is, if it is one. -/
  idxMaps : Array (Array (Option Nat))
  /-- The name a constructor gives each type index, if one does. -/
  idxNames : Array (Option Name)

/-- Classify the constructors of `ind`, at the parameters `params`. -/
def classify (ind : InductiveVal) (params : Array Expr) (typeIdx : Array Bool) :
    MetaM Classified := do
  let mut whole := true
  let mut maps : Array (Array (Option Nat)) := #[]
  let mut names : Array (Option Name) := typeIdx.map fun _ => none
  for d in ind.ctors do
    let di ← getConstInfoCtor d
    let cty ← instantiateForall di.type params
    let (m, ok, ns) ← forallBoundedTelescope cty di.numFields fun xs r => do
      let rArgs := r.getAppArgs.extract ind.numParams r.getAppArgs.size
      let mut m : Array (Option Nat) := #[]
      let mut ok := true
      let mut ns : Array (Nat × Name) := #[]
      for x in xs do
        let t ← inferType x
        if ← isExistentialField t then
          unless ← isTypeField t do
            throwError "`#leanscript_ctor`: the type `{ind.name}` hides a family of types \
              in the field `{← x.fvarId!.getUserName}` of `{d}`, which the language has no \
              shape for"
          match (List.range rArgs.size).find? (fun k => rArgs[k]! == x && typeIdx[k]!) with
          | some k => m := m.push (some k); ns := ns.push (k, ← x.fvarId!.getUserName)
          | none => m := m.push none; ok := false
        else m := m.push none
      -- every type index must be a type field, and no two the same one
      let mut seen : Array Expr := #[]
      for k in [0:rArgs.size] do
        if typeIdx[k]! then
          let a := rArgs[k]!
          unless a.isFVar && xs.contains a && !seen.contains a do ok := false
          seen := seen.push a
      return (m, ok, ns)
    whole := whole && ok
    maps := maps.push m
    for (k, n) in ns do
      if names[k]!.isNone && !n.hasMacroScopes then names := names.set! k (some n)
  return { whole, idxMaps := maps, idxNames := names }

/-- Walk the fields of the constructor `di` at `params`, a field that is type index `i`
    becoming `idxVars[i]`, and run `k` on the others. -/
def withCtorFields {α : Type} (di : ConstructorVal) (params idxVars : Array Expr)
    (m : Array (Option Nat)) (k : Array Expr → MetaM α) : MetaM α := do
  go (← instantiateForall di.type params) m.toList #[]
where
  /-- One binder at a time. -/
  go (t : Expr) : List (Option Nat) → Array Expr → MetaM α
    | [], acc => k acc
    | mi :: rest, acc => do
      let t ← whnf t
      let .forallE n d b bi := t
        | throwError "`#leanscript_ctor`: the constructor `{di.name}` has fewer fields than \
            its declaration says"
      match mi with
      | some i => go (b.instantiate1 idxVars[i]!) rest acc
      | none => withLocalDecl n bi d fun x => go (b.instantiate1 x) rest (acc.push x)

/-- The layout of a datatype's values, or of one constructor's. -/
inductive Shape where
  /-- One field: the value is that field. -/
  | newtype
  /-- A record, from this schema. -/
  | record (sch : Expr)
  /-- A tagged union, from this schema. -/
  | union (l : Expr)
  /-- An enum, from this schema. -/
  | enum (s : Expr)
  /-- `Bool`. -/
  | bool

/-- The layout of one constructor's fields. -/
def singleShape (what : MessageData) (fs : Array Expr) : MetaM (Shape × Expr) := do
  match fs.toList with
  | [] => throwError "`#leanscript_ctor`: {what} carries no value — a unit-like type has no \
      constructor function"
  | [a] => return (.newtype, a)
  | a :: b :: rest =>
      let sch ← mkAppM ``LeanScript.LeanRecordSchema.mk #[a, b, ← mkListLit tyWfE rest]
      return (.record sch, mkApp (mkConst ``LeanScript.TyWf.record) sch)

/-- A non-empty list of trees. -/
def mkNE (a : Expr) (as : List Expr) : MetaM Expr := do
  mkAppM ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk #[a, ← mkListLit tyWfE as]

/-- A list of lists of trees. -/
def mkLL (ess : List (List Expr)) : MetaM Expr := do
  mkListLit (← mkAppM ``List #[tyWfE]) (← ess.mapM (mkListLit tyWfE))

/-- The constructors of a tagged union from the first that carries a field. -/
def mkCtorsWithPayload? : List (List Expr) → MetaM (Option Expr)
  | [] => return none
  | [] :: rest => do
      match ← mkCtorsWithPayload? rest with
      | some r => return some (← mkAppM ``LeanScript.CtorsWithPayload.skip #[r])
      | none => return none
  | (f :: fs) :: rest => do
      return some (← mkAppM ``LeanScript.CtorsWithPayload.here #[← mkNE f fs, ← mkLL rest])

/-- The layout of a datatype with these constructors. -/
def wholeShape (name : Name) (enumOverride : Option Expr) (cls : Array (Array Expr)) :
    MetaM (Shape × Expr) := do
  if h : cls.size = 1 then
    return ← singleShape m!"the only constructor of `{name}`" cls[0]
  if cls.all (·.isEmpty) then
    if cls.size == 2 then
      return (.bool, mkApp (mkConst ``LeanScript.TyWf.prim) (mkConst ``LeanScript.LeanPrimTy.bool))
    let s ← match enumOverride with
      | some s => pure s
      | none => mkAppM ``LeanScript.LeanEnumSchema.mk #[mkNatLit (cls.size - 3), toExpr (0 : Int)]
    return (.enum s, mkApp (mkConst ``LeanScript.TyWf.enum) s)
  let l? ← match (cls.toList.map (·.toList)) with
    | (f :: fs) :: next :: rest =>
        some <$> mkAppM ``LeanScript.LeanTaggedUnionSchema.payloadFirst
          #[← mkNE f fs, ← mkListLit tyWfE next, ← mkLL rest]
    | [] :: rest => do
        match ← mkCtorsWithPayload? rest with
        | some r => some <$> mkAppM ``LeanScript.LeanTaggedUnionSchema.skip #[r]
        | none => pure none
    | _ => pure none
  let some l := l? | throwError "`#leanscript_ctor`: `{name}` has no tagged-union layout"
  return (.union l, mkApp (mkConst ``LeanScript.TyWf.taggedUnion) l)

/-- Refuse a datatype whose model is a terminal type or a built-in type former, and read off
    the numbering of an enum whose instance chooses its own. -/
def builtinModel (ind : InductiveVal) (params : Array Expr) : MetaM (Option Expr) := do
  if ind.numIndices != 0 then return none
  let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    params.mapIdx fun k p => (Name.mkSimple s!"inst{k}", .instImplicit,
      fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[p])
  withLocalDecls instDecls fun _ => do
    let ty := mkAppN (mkConst ind.name (ind.levelParams.map Level.param)) params
    let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[ty])
      | return none
    let tree ← whnf (← mkAppOptM ``LeanScript.tyOf #[some ty, some inst])
    match tree.getAppFnArgs with
    | (``LeanScript.Ty.prim, _) =>
        if ind.name == ``Bool then return none
        throwError "`#leanscript_ctor`: `{ind.name}` is modelled by a terminal type of the \
          language, whose values are literals; it has no constructor function"
    | (``LeanScript.Ty.array, _) | (``LeanScript.Ty.thunk, _) | (``LeanScript.Ty.lazy, _)
    | (``LeanScript.Ty.fn, _) =>
        throwError "`#leanscript_ctor`: `{ind.name}` is modelled by a built-in type former of \
          the language, which has an introduction form of its own"
    | (``LeanScript.Ty.enum, #[s]) =>
        if s.hasFVar then return none else return some s
    | _ => return none

/-! ## Generating the definitions -/

/-- Add a reducible definition, compiled when it can be. -/
def addReducibleDef (name : Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwError "`#leanscript_ctor`: internal error, `{name}` still has metavariables"
  let lvls := LeanScript.Deriving.usedLevels type value
  addDecl (.defnDecl { name, levelParams := lvls, type, value, hints := .abbrev,
    safety := .safe })
  try compileDecls [name] catch _ => pure ()
  setReducibleAttribute name

/-- A spine of the terms `xs`, at the trees `tys`. -/
def mkSpineE (sg γ : Expr) (tys : List Expr) (xs : Array Expr) : MetaM Expr := do
  let mut sp := mkApp2 (mkConst ``LeanScript.Spine.nil) sg γ
  let tysA := tys.toArray
  for i in [0:xs.size] do
    let j := xs.size - 1 - i
    sp := mkAppN (mkConst ``LeanScript.Spine.cons)
      #[sg, γ, tysA[j]!, ← mkListLit tyWfE (tys.drop (j + 1)), xs[j]!, sp]
  return sp

/-- The body of the constructor function: the value of shape `shape` built as constructor
    `cidx` from the terms `xs`, at the trees `tys`. -/
def mkBody (sg γ : Expr) (shape : Shape) (cidx : Nat) (tys : Array Expr) (xs : Array Expr) :
    MetaM Expr := do
  match shape with
  | .newtype => return xs[0]!
  | .record sch =>
      return mkAppN (mkConst ``LeanScript.Term.record_mk)
        #[sg, γ, sch, ← mkSpineE sg γ tys.toList xs]
  | .union l =>
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyWfE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit cidx, lenE])
      return mkAppN (mkConst ``LeanScript.Term.taggedUnion_mk)
        #[sg, γ, l, mkNatLit cidx, prf, ← mkSpineE sg γ tys.toList xs]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit cidx, nE])
      return mkAppN (mkConst ``LeanScript.Term.enum_mk)
        #[sg, γ, s, mkAppN (mkConst ``Fin.mk) #[nE, mkNatLit cidx, prf]]
  | .bool =>
      return mkAppN (mkConst ``LeanScript.Term.bool_mk) #[sg, γ, toExpr (cidx == 1)]

/-- The field names and the trees of the fields a constructor keeps, in the context `c`. -/
def translateFields (c : TrCtx) (xs : Array Expr) : MetaM (Array (Name × Expr)) := do
  let mut out := #[]
  for x in xs do
    let t ← inferType x
    if ← erasedBinder t then continue
    let n ← x.fvarId!.getUserName
    if let some a ← trTy c n t then out := out.push (n, a)
  return out

/-- Declare a `TyWf` local for each type variable, named as it is. -/
def withTyVarHoles {α : Type} (vars : Array (Expr × Name)) (k : Array (Expr × Expr) → MetaM α) :
    MetaM α := do
  let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    vars.map fun (_, n) => (n, .default, fun _ => pure tyWfE)
  withLocalDecls decls fun hs => k (vars.map (·.1) |>.zip hs)

/-- Generate the layout and the constructor function once the fields are translated:
    `holes` are the arguments, `shape`/`layout` the layout, `fields` the kept fields of the
    constructor. -/
def emit (cName layoutKey layoutOwner : Name) (layoutBase : Name) (c : TrCtx)
    (tyVarHoles : Array Expr) (shape : Shape) (layout : Expr) (cidx : Nat)
    (fields : Array (Name × Expr)) : MetaM (Name × Name) := withHoles c do
  let holeIds := (← c.holes.get).map fun (_, _, id) => Expr.fvar id
  let holes := tyVarHoles ++ holeIds
  -- the layout, shared when it has been generated already
  let layoutName ← match ← cached? layoutKey "layout" with
    | some n => pure n
    | none => do
      let n ← declNameFor layoutOwner layoutBase "leanScriptLayout"
      if (← getEnv).contains n then
        throwError "`#leanscript_ctor`: `{n}` is already declared"
      addReducibleDef n (← mkForallFVars holes tyWfE) (← mkLambdaFVars holes layout)
      modifyEnv fun env => ctorFnExt.addEntry env { key := layoutKey, kind := "layout", decl := n }
      pure n
  let layoutC ← mkConstWithLevelParams layoutName
  let layoutApp := mkAppN layoutC holes
  unless ← isDefEq layoutApp layout do
    throwError "`#leanscript_ctor`: the cached layout `{layoutName}` does not match the \
      datatype any more"
  let fnName ← declNameFor layoutOwner cName "leanScriptCtor"
  if (← getEnv).contains fnName then
    throwError "`#leanscript_ctor`: `{fnName}` is already declared"
  withLocalDecl `Sg .implicit (mkConst ``LeanScript.Sig) fun sg =>
  withLocalDecl `Γ .implicit (mkConst ``LeanScript.Ctx) fun γ => do
    let termOf (τ : Expr) := mkApp3 (mkConst ``LeanScript.Term) sg γ τ
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      fields.map fun (n, τ) => (n, .default, fun _ => pure (termOf τ))
    withLocalDecls decls fun xs => do
      let body ← mkBody sg γ shape cidx (fields.map (·.2)) xs
      let binders := #[sg, γ] ++ holes ++ xs
      addReducibleDef fnName (← mkForallFVars binders (termOf layoutApp))
        (← mkLambdaFVars binders body)
  modifyEnv fun env => ctorFnExt.addEntry env { key := cName, kind := "fn", decl := fnName }
  return (layoutName, fnName)

/-- The layout and the constructor function of the constructor `cName`, generated if they
    have not been. -/
def ensureCtorFn (cName : Name) : MetaM (Name × Name) := do
  if let some fn ← cached? cName "fn" then
    if let some lay ← cached? cName "layout" then return (lay, fn)
    let ci ← getConstInfoCtor cName
    if let some lay ← cached? ci.induct "layout" then return (lay, fn)
  let ci ← getConstInfoCtor cName
  let ind ← getConstInfoInduct ci.induct
  if ← forallTelescopeReducing ind.type fun _ body => pure body.isProp then
    throwError "`#leanscript_ctor`: `{ind.name}` is a proposition, which carries no value"
  forallBoundedTelescope ind.type ind.numParams fun params indBody => do
    for p in params do
      let s ← whnf (← inferType p)
      unless s.isSort && s != .sort .zero do
        throwError "`#leanscript_ctor`: `{ind.name}` has the parameter `{p}`, which is not a \
          type; only datatypes whose parameters are all types have constructor functions"
    let enumOverride ← builtinModel ind params
    forallTelescopeReducing indBody fun idxs _ => do
      let typeIdx ← idxs.mapM fun x => do isTypeField (← inferType x)
      let cl ← classify ind params typeIdx
      let holesRef ← IO.mkRef #[]
      let paramVars ← params.mapM fun p => do return (p, (← p.fvarId!.getUserName).eraseMacroScopes)
      if cl.whole then
        let mut idxVars : Array (Expr × Name) := #[]
        for k in [0:idxs.size] do
          if typeIdx[k]! then
            let n ← match cl.idxNames[k]! with
              | some n => pure n
              | none => pure (← idxs[k]!.fvarId!.getUserName).eraseMacroScopes
            idxVars := idxVars.push (idxs[k]!, n)
        let vars := paramVars ++ idxVars
        withTyVarHoles vars fun tyVars => do
          let c : TrCtx := { members := ind.all.toArray, tyVars, holes := holesRef,
                             used := ← IO.mkRef (vars.map (·.2)) }
          let mut cls : Array (Array Expr) := #[]
          let mut mine : Array (Name × Expr) := #[]
          for h : j in [0:ind.ctors.length] do
            let d := ind.ctors[j]!
            let di ← getConstInfoCtor d
            let fs ← withCtorFields di params idxs cl.idxMaps[j]! fun xs => translateFields c xs
            cls := cls.push (fs.map (·.2))
            if d == cName then mine := fs
          let (shape, layout) ← withHoles c (wholeShape ind.name enumOverride cls)
          emit cName ind.name ind.name ind.name c (tyVars.map (·.2)) shape layout ci.cidx mine
      else
        let di := ci
        withCtorFields di params #[] (cl.idxMaps[ci.cidx]!.map fun _ => none) fun xs => do
          let mut exVars : Array (Expr × Name) := #[]
          for x in xs do
            if ← isTypeField (← inferType x) then
              exVars := exVars.push (x, (← x.fvarId!.getUserName).eraseMacroScopes)
          let vars := paramVars ++ exVars
          withTyVarHoles vars fun tyVars => do
            let c : TrCtx := { members := ind.all.toArray, tyVars, holes := holesRef,
                               used := ← IO.mkRef (vars.map (·.2)) }
            let fs ← translateFields c xs
            let (shape, layout) ← withHoles c
              (singleShape m!"the constructor `{cName}`" (fs.map (·.2)))
            emit cName cName ind.name cName c (tyVars.map (·.2)) shape layout ci.cidx fs

/-! ## The elaborators -/

/-- `#leanscript_ctor I c`: the constructor function of the constructor `I.c`, generated the
    first time and cached.  `#leanscript_ctor I.c` names the constructor in full, and
    `#leanscript_ctor I` names the only constructor of `I`. -/
syntax:max (name := leanscriptCtor) "#leanscript_ctor " name (ppSpace name)? : term

/-- `#leanscript_layout I c`: the layout of what `#leanscript_ctor I c` builds, as a function
    of its type arguments. -/
syntax:max (name := leanscriptLayout) "#leanscript_layout " name (ppSpace name)? : term

/-- A name as written, resolved against the open namespaces. -/
def resolveName (n : Name) : TermElabM Name := do
  try resolveGlobalConstNoOverload (mkIdent n)
  catch _ =>
    if (← getEnv).contains n then return n
    throwError "`#leanscript_ctor`: unknown constant `{n}`"

/-- The constructor the syntax names. -/
def ctorOfSyntax (stx : Syntax) : TermElabM Name := do
  let some n1 := stx[1].isNameLit? | throwUnsupportedSyntax
  let n2? := stx[2].getOptional?.bind (·.isNameLit?)
  let env ← getEnv
  match n2? with
  | some n2 =>
      let i ← resolveName n1
      let some (.inductInfo ind) := env.find? i
        | throwError "`#leanscript_ctor`: `{i}` is not an inductive type"
      if ind.ctors.contains (i ++ n2) then return i ++ n2
      let c ← try resolveName n2 catch _ =>
        throwError "`#leanscript_ctor`: `{i}` has no constructor `{n2}`"
      unless ind.ctors.contains c do
        throwError "`#leanscript_ctor`: `{c}` is not a constructor of `{i}`"
      return c
  | none =>
      let x ← resolveName n1
      match env.find? x with
      | some (.ctorInfo _) => return x
      | some (.inductInfo ind) =>
          match ind.ctors with
          | [c] => return c
          | _ => throwError "`#leanscript_ctor`: `{x}` has {ind.ctors.length} constructors; \
              name the one you mean"
      | _ => throwError "`#leanscript_ctor`: `{x}` is not a constructor"

@[term_elab leanscriptCtor]
def elabLeanscriptCtor : TermElab := fun stx expected? => do
  let c ← ctorOfSyntax stx
  let (_, fn) ← ensureCtorFn c
  elabTerm (mkCIdentFrom stx fn) expected?

@[term_elab leanscriptLayout]
def elabLeanscriptLayout : TermElab := fun stx expected? => do
  let c ← ctorOfSyntax stx
  let (lay, _) ← ensureCtorFn c
  elabTerm (mkCIdentFrom stx lay) expected?

end LeanScript.CtorFn

end

end
