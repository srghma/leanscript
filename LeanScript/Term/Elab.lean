import Lean
import LeanScript.Ty
import LeanScript.Expr

/-!
# `#leanjs_generate_term_and_ctx_for`: what a Lean definition compiles to

This is the front end of the translation: the command reads a Lean declaration out of
the environment and reports, for that one declaration,

* its **signature**, as Lean prints it;
* the `Ty` of its first parameter and the `Ty` of the rest of it (`argTy` / `resTy`) —
  the answer of `LeanScript.Ty`'s own type translation, which is what decides whether
  the declaration can be held by `LeanScript.Expr.Term` at all;
* the **kind of recursion** Lean used to elaborate it, which decides *which constructor*
  of `Term` its body becomes;
* the **primitives** it uses — the `@[extern]` constants, which become `Term.prim`
  nodes — and the **context** it needs: the other declarations that would have to be
  translated with it, each marked `ok` or `BAD` according to whether *they* can be held.

## The six kinds of recursion, and what holds each

Lean elaborates a `def` in one of a few ways, and the report names which:

| Lean                                 | `Term`                                            |
| :----------------------------------- | :------------------------------------------------ |
| no recursion                          | nothing special                                    |
| structural recursion                  | the **recursor** of the datatype recursed on       |
| mutual structural recursion           | the recursors of the mutual block                  |
| well-founded recursion                | `Term.fixAcc` — the accessibility proof is a field |
| partial fixpoint (`partial_fixpoint`, a `while` loop in a `do` block) | **nothing**: there is no such constructor |
| `partial` / `unsafe`                  | **nothing**                                        |

The first four are total, so they have a meaning as a Lean function and `Term` can hold
them.  The last two are not, and a declaration that is one of them — or that calls one —
is reported as `rejected`.  This is the design, not a gap: `LeanScript.Eval.evalTerm` is
a total Lean function with no fuel and no stuck state, which is only possible because
every `Term` it can be handed terminates.

## Structural recursion uses the recursor of the datatype

`Nat`, `Array`, the enums, the records and the tagged unions built from a schema, and
the datatypes of `LeanPrimTyCovariant` all have recursors, and a structurally recursive
definition is translated by the recursor of whichever one it recurses on.  Everything
else — a measure that decreases, a lexicographic pair, a nested call — goes through
`Term.fixAcc`, which takes the relation, its `DecidableRel`, the subject of the
recursion and a proof that the subject is accessible.

## What this command does *not* do

It does not build the `Term`.  Reading a Lean declaration's elaborated body back into a
typed, intrinsically-scoped term of a *different* language is a compiler, not a report,
and it is not in this tree; `SnapshotsMy.LeanScriptModels` holds terms for several of
these functions, written out by hand, and checked against the
Lean function they model.  What the command does is decide, and say, exactly which of
them a compiler could accept and what it would need.
-/

open Lean Meta Elab Command

namespace LeanScript.Term

/-! ## Rendering a `Ty` -/

mutual

/-- A one-line rendering of a type of the term language, as an s-expression. -/
partial def tyStr : Ty → String
  | .prim p => p.pretty
  | .fn a b => "(fn " ++ tyStr a ++ " " ++ tyStr b ++ ")"
  | .primCovariant (.array a) => "(array " ++ tyStr a ++ ")"
  -- | .primCovariant (.task a) => "(task " ++ tyStr a ++ ")"
  -- | .primCovariant (.promise a) => "(promise " ++ tyStr a ++ ")"
  | .primCovariant (.thunk a) => "(thunk " ++ tyStr a ++ ")"
  | .primCovariant (.lazy a) => "(lazy " ++ tyStr a ++ ")"
  | .enum e => "(enum " ++ toString e.nOfConstructors ++ " from " ++ toString e.shift ++ ")"
  | .record fs => "(record" ++ String.join ((fs.toList).map (fun a => " " ++ tyStr a)) ++ ")"
  | .taggedUnion tu =>
      "(taggedUnion" ++ String.join ((tu.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map tyStr) ++ "]")) ++ ")"
  | .recTaggedUnion l =>
      "(recTaggedUnion" ++ String.join ((l.schema.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recObject fs =>
      "(recObject" ++ String.join ((fs.fields.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .recAlias b => "(recAlias " ++ rtyStr b.body ++ ")"
  | .mutualRecursiveFamily _ => "(mutualRecursiveFamily …)"
  | .withComputedFields b cs =>
      "(withComputedFields " ++ tyStr b ++ " [" ++
        " ".intercalate (cs.toList.map (·.pretty)) ++ "])"

/-- A one-line rendering of a type *inside* a recursive declaration. -/
partial def rtyStr : RTy → String
  | .self => "self"
  | .familyMember i => "(familyMember " ++ toString i ++ ")"
  | .prim p => p.pretty
  | .fn a b => "(fn " ++ rtyStr a ++ " " ++ rtyStr b ++ ")"
  | .primCovariant (.array a) => "(array " ++ rtyStr a ++ ")"
  -- | .primCovariant (.task a) => "(task " ++ rtyStr a ++ ")"
  -- | .primCovariant (.promise a) => "(promise " ++ rtyStr a ++ ")"
  | .primCovariant (.thunk a) => "(thunk " ++ rtyStr a ++ ")"
  | .primCovariant (.lazy a) => "(lazy " ++ rtyStr a ++ ")"
  | .enum e => "(enum " ++ toString e.nOfConstructors ++ " from " ++ toString e.shift ++ ")"
  | .record fs => "(record" ++ String.join ((fs.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .taggedUnion tu =>
      "(taggedUnion" ++ String.join ((tu.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recTaggedUnion l =>
      "(recTaggedUnion" ++ String.join ((l.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recObject fs => "(recObject" ++ String.join ((fs.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .recAlias b => "(recAlias " ++ rtyStr b ++ ")"
  | .mutualRecursiveFamily _ => "(mutualRecursiveFamily …)"
  | .withComputedFields b cs =>
      "(withComputedFields " ++ rtyStr b ++ " [" ++
        " ".intercalate (cs.toList.map (·.pretty)) ++ "])"

end

/-! ## Translating a Lean type into a `Ty`

The translation is the one the table in `LeanScript.Ty`'s module doc-comment describes.
It answers `none` for a type the language has no shape for — a type variable, a `Prop`
other than in an erased position, a monad, a dependent function type, a structure with a
field whose type has no `Ty`. -/

/-- The terminal types, by the name of the Lean type. -/
def primOfName : Name → Option LeanPrimTy
  | ``Nat => some .nat
  | ``Int => some .int
  | ``Bool => some .bool
  | ``Char => some .char
  | ``String => some .string
  | ``UInt8 => some .uint8
  | ``UInt16 => some .uint16
  | ``UInt32 => some .uint32
  | ``UInt64 => some .uint64
  | ``Int8 => some .int8
  | ``Int16 => some .int16
  | ``Int32 => some .int32
  | ``Int64 => some .int64
  | ``Float => some .float
  | ``Float32 => some .float32
  | ``String.Pos.Raw => some .stringPosRaw
  | ``Substring.Raw => some .substringRaw
  | ``String.Slice => some .stringSlice
  | _ => none

/-- Is this a type the language erases — a proposition, or a one-value type? -/
def isErasedType (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  let e ← whnf e
  match e.getAppFn with
  | .const n _ => return n == ``Unit || n == ``PUnit
  | _ => return false

/-- The result of translating a Lean type. -/
inductive TyResult where
  /-- A type of the language. -/
  | ok (τ : Ty)
  /-- A type the language erases: it carries no value. -/
  | erased
  /-- No shape of the language describes it, for this reason. -/
  | no (reason : String)
  deriving Inhabited

/-- Does the constant `n` occur in this type? -/
def occursIn (n : Name) (e : Expr) : MetaM Bool := do
  return (← instantiateMVars e).find? (fun s => s.isConstOf n) |>.isSome

/-! ### The values a declaration caches

A Lean declaration may cache a value **computed from itself** — `Lean.Name` stores its
own `hash`, declared `@[computed_field]`.  Lean records that by building a second
inductive, `T._impl`, whose constructors carry the cached values ahead of the fields, so
the types of the cached values are read off it and no declaration has to be named here.
`Ty.withComputedFields` is where they land. -/

/-- The terminal types of the values the declaration `n` caches, in declaration order:
    `.inl none` when it caches nothing, and `.inr` with a reason when it caches a value
    of a type that is not terminal, which `Ty.withComputedFields` has no room for. -/
def computedFieldPrimTys (n : Name) :
    MetaM (Sum (Option (NonEmpty.ListCorrectByConstruction.NonEmptyList LeanPrimTy)) String) := do
  let env ← getEnv
  -- no `T._impl`: the declaration has no computed field at all
  let some (.inductInfo _) := env.find? (n ++ `_impl) | return .inl none
  let some (.inductInfo ind) := env.find? n | return .inl none
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    -- a constructor with no field stores no cached value, so it says nothing about them
    if ci.numFields == 0 then continue
    let some (.ctorInfo cimpl) := env.find? (c ++ `_impl)
      | return .inr s!"`{n}` caches values in a way this translation cannot read"
    let k := cimpl.numFields - ci.numFields
    if k == 0 then return .inl none
    return ← forallTelescopeReducing cimpl.type fun xs _ => do
      let mut tys : List LeanPrimTy := []
      for x in xs[ind.numParams:ind.numParams + k] do
        let t ← whnf (← inferType x)
        let some p := t.getAppFn.constName?.bind primOfName
          | return .inr s!"`{n}` caches a value of a type that is not terminal"
        tys := tys ++ [p]
      match tys with
      | [] => return .inl none
      | t :: ts => return .inl (some ⟨t, ts⟩)
  -- every constructor is field-less, so the cached values are nowhere to be read
  return .inr s!"`{n}` caches values and has no constructor with a field to read them from"

mutual

/-- The `Ty` of a Lean type, if it has one.

    `depth` bounds the recursion: a type whose translation needs more than `depth`
    nested datatypes is refused rather than diverging. -/
partial def toTy (e : Expr) (depth : Nat := 8) : MetaM TyResult := do
  if depth == 0 then return .no "nested too deeply"
  let e ← whnf e
  if (← isProp e) then return .erased
  if e.isSort then return .no "a type or a proposition, which carries no value"
  if e.isForall then
    -- the parameters that carry a value, in order; the erased ones (the proofs) drop
    -- out, and what is left has to be non-dependent
    return ← forallTelescopeReducing e fun xs body => do
      let mut doms : List Ty := []
      let mut kept : Array FVarId := #[]
      for x in xs do
        let d ← inferType x
        if ← isErasedType d then continue
        if d.hasAnyFVar (fun f => kept.contains f) then
          return .no "a dependent function type"
        match ← toTy d (depth - 1) with
        | .ok a => doms := doms ++ [a]; kept := kept.push x.fvarId!
        | .erased => pure ()
        | .no r => return .no r
      if body.hasAnyFVar (fun f => kept.contains f) then
        return .no "a dependent function type"
      match ← toTy body (depth - 1) with
      | .ok r => return .ok (doms.foldr Ty.fn r)
      | .erased => return .no "a function answering with an erased type"
      | .no r => return .no r
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const n _ := f | return .no "not a constant type"
  if let some p := primOfName n then return .ok (.prim p)
  if n == ``Unit || n == ``PUnit then return .erased
  if n == ``Array && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.array a)
    | .erased => return .no "an array of an erased type"
    | .no r => return .no r
  if n == ``List && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (Ty.list a)
    | .erased => return .no "a list of an erased type"
    | .no r => return .no r
  if n == ``Thunk && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.thunk a)
    | .erased => return .no "a thunk of an erased type"
    | .no r => return .no r
  if n == ``Option && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.option a)
    | .erased => return .no "an option of an erased type"
    | .no r => return .no r
  if n == ``Prod && args.size == 2 then
    match ← toTy args[0]! (depth - 1), ← toTy args[1]! (depth - 1) with
    | .ok a, .ok b => return .ok (.prod a b)
    | .no r, _ => return .no r
    | _, .no r => return .no r
    | _, _ => return .no "a pair with an erased component"
  -- a user-declared inductive
  let env ← getEnv
  let some (.inductInfo ind) := env.find? n | return .no s!"no shape for `{n}`"
  if ind.all.length > 1 then return .no s!"`{n}` is part of a mutual block"
  -- a recursive declaration: its `Ty` is `Ty.recTaggedUnion`, whose fields are
  -- *descriptions* rather than types, so an occurrence of the declaration among them is
  -- `RTy.self`
  if ind.isRec then
    unless ind.numIndices == 0 do
      return .no s!"`{n}` is an indexed family, which the recursive shapes have no room for"
    unless ind.numParams == 0 do
      return .no s!"`{n}` is a recursive declaration with parameters, which the recursive shapes have no room for"
    let mut ctorRTys : List (List RTy) := []
    for c in ind.ctors do
      let cinfo ← getConstInfoCtor c
      let fields : Sum (List RTy) String ← forallTelescopeReducing cinfo.type fun xs _ => do
        let mut fs : List RTy := []
        for x in xs do
          match ← toRTyField n (← inferType x) depth with
          | .inl (some a) => fs := fs ++ [a]
          | .inl none => pure ()
          | .inr r => return Sum.inr r
        return Sum.inl fs
      match fields with
      | .inr r => return .no r
      | .inl fs => ctorRTys := ctorRTys ++ [fs]
    let some sch := LeanTaggedUnionSchema.ofList? ctorRTys
      | return .no s!"`{n}` is a recursive declaration the tagged-union schema refuses"
    if h : RTy.Wf (.recTaggedUnion sch) then
      return ← withComputedFieldsOf n (.recTaggedUnion ⟨sch, h⟩)
    else
      return .no s!"`{n}` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all)"
  -- the fields of each constructor, with the parameters instantiated
  let mut ctorTys : List (List Ty) := []
  for c in ind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (args.extract 0 ind.numParams)
    let fields : Sum (List Ty) String ← forallTelescopeReducing cty fun xs _ => do
      let mut fs : List Ty := []
      for x in xs do
        match ← toTy (← inferType x) (depth - 1) with
        | .ok a => fs := fs ++ [a]
        | .erased => pure ()
        | .no r => return Sum.inr r
      return Sum.inl fs
    match fields with
    | .inr r => return .no r
    | .inl fs => ctorTys := ctorTys ++ [fs]
  match ctorTys with
  | [] => return .no s!"`{n}` has no constructors"
  | [[]] => return .erased
  | [[a]] => return ← withComputedFieldsOf n a  -- a newtype: the wrapper is erased
  | [fs] =>
      match LeanRecordSchema.ofList? fs with
      | some sch => return ← withComputedFieldsOf n (.record sch)
      | none => return .no "a record of fewer than two fields"
  | _ =>
      if ctorTys.all (·.isEmpty) then
        match Ty.enumOrBool? ctorTys.length 0 with
        | some τ => return ← withComputedFieldsOf n τ
        | none => return .no "an enum of fewer than two constructors"
      else
        match LeanTaggedUnionSchema.ofList? ctorTys with
        | some sch => return ← withComputedFieldsOf n (.taggedUnion sch)
        | none => return .no "a tagged union the schema refuses"

/-- The `Ty` of the declaration `n`, whose shape is `τ`, with the types of the values it
    caches attached — `Ty.withComputedFields` — when it caches any. -/
partial def withComputedFieldsOf (n : Name) (τ : Ty) : MetaM TyResult := do
  match ← computedFieldPrimTys n with
  | .inr r => return .no r
  | .inl none => return .ok τ
  | .inl (some cs) => return .ok (.withComputedFields τ cs)

/-- One field of a constructor of the recursive declaration `n`, as a payload type: an
    occurrence of `n` itself is `RTy.self`, an array whose elements mention `n` is an
    array of payload types, and anything else is a closed `Ty` read as a payload.  The
    answer is `.inr` with a reason when the field has no shape, and `.inl none` when the
    field is erased. -/
partial def toRTyField (n : Name) (t0 : Expr) (depth : Nat) :
    MetaM (Sum (Option RTy) String) := do
  if depth == 0 then return .inr "nested too deeply"
  let t ← whnf t0
  if t.getAppFn.constName? == some n then return .inl (some (RTy.self))
  -- an array of fields: the elements may themselves mention the declaration
  if t.isAppOfArity ``Array 1 then
    let a := t.appArg!
    if (← occursIn n a) then
      match ← toRTyField n a (depth - 1) with
      | .inl (some r) => return .inl (some (.primCovariant (.array r)))
      | .inl none => return .inr "an array of an erased type"
      | .inr r => return .inr r
  match ← toTy t (depth - 1) with
  | .ok a => return .inl (some (Ty.toRTy a))
  | .erased => return .inl none
  | .no r => return .inr r

end

/-! ## Which kind of recursion Lean used -/

/-- How Lean elaborated a definition, which decides what could hold it. -/
inductive RecursionKind where
  /-- Not recursive. -/
  | none
  /-- Structurally recursive; `mutual` if the block has more than one member. -/
  | structural (isMutual : Bool)
  /-- Recursive with a decreasing measure. -/
  | wellFounded (isMutual : Bool)
  /-- `partial_fixpoint`, or a `while` loop in a `do` block. -/
  | partialFixpoint
  /-- `partial` or `unsafe`. -/
  | partialUnsafe
  deriving Inhabited, BEq

/-- Can a `Term` hold a definition elaborated this way? -/
def RecursionKind.representable : RecursionKind → Bool
  | .partialFixpoint | .partialUnsafe => false
  | _ => true

/-- The report's rendering of the kind, and the note that goes with it. -/
def RecursionKind.describe : RecursionKind → String × String
  | .none => ("none", "(no recursion to encode)")
  | .structural false => ("structural", "(encoded with the recursor of the datatype)")
  | .structural true => ("mutual structural", "(encoded with the recursors of the block)")
  | .wellFounded false => ("well-founded", "(encoded as Term.fixAcc: the Acc proof is a field)")
  | .wellFounded true => ("mutual well-founded", "(encoded as Term.fixAcc over the whole block)")
  | .partialFixpoint => ("partial fixpoint", "NOT REPRESENTABLE in Term")
  | .partialUnsafe => ("partial (unsafe)", "NOT REPRESENTABLE in Term")

/-- How Lean elaborated this declaration. -/
def recursionKindOf (n : Name) : CoreM RecursionKind := do
  let env ← getEnv
  if let some info := Elab.Structural.eqnInfoExt.find? env n then
    return .structural (info.declNames.size > 1)
  if let some info := Elab.WF.eqnInfoExt.find? env n then
    return .wellFounded (info.declNames.size > 1)
  if let some _ := Elab.PartialFixpoint.eqnInfoExt.find? env n then
    return .partialFixpoint
  match env.find? n with
  | some (.defnInfo di) =>
      if di.safety != .safe then return .partialUnsafe
      -- a self-referential body that no elaborator registered is a `partial_fixpoint`
      -- unfolded by hand, or a `Lean.Order.fix`
      if di.value.getUsedConstants.any (fun c => c == ``Lean.Order.fix) then
        return .partialFixpoint
      return .none
  | some (.opaqueInfo _) => return .partialUnsafe
  | _ => return .none

/-! ## The context a definition needs

A translation of a definition needs, besides the definition itself, everything the
definition's body mentions.  Three kinds of name are *not* part of that context:

* a name with no run-time content — a type, a constructor, a recursor, a theorem, an
  axiom;
* a name the translation **inlines** — an instance, a structure projection, a matcher,
  and the auxiliary definitions Lean generates for a `def` (`f._unary`, `f.match_1`,
  `Nat.brecOn`, …).  Those are looked *through*: what they mention is part of the
  context, they themselves are not;
* an `@[extern]` constant.  That is a *primitive*: it is the runtime's own function, it
  becomes a `Term.prim` node, and the walk stops there — which is exactly the catalogue
  `LeanScript.LeanInitPureExterns` lists.

What is left is reported as the context, each entry marked `ok` if it is itself
representable and `BAD` if it is not. -/

/-- The auxiliary constructions of an inductive type, which carry no user code. -/
def isRecursorLike (n : Name) : Bool :=
  match n with
  | .str _ s =>
      s == "rec" || s == "recOn" || s == "casesOn" || s == "brecOn" || s == "below"
        || s == "binductionOn" || s == "ibelow" || s == "noConfusion"
        || s == "noConfusionType" || s == "ndrec" || s == "ndrecOn"
  | _ => false

/-- The handful of core constants the translation has a node for rather than a call:
    `if`-`then`-`else` is `Term.bool_elim`. -/
def isBuiltin (n : Name) : Bool :=
  n == ``ite || n == ``dite || n == ``cond || n == ``id

/-- The scaffolding Lean's own well-founded elaboration leaves in a body:
    `WellFounded.fix` and the relation it was handed.  `Term.fixAcc` carries the
    relation and the accessibility proof in fields of its own, so none of this is part
    of the context a translation would need. -/
def isRecursionScaffolding (n : Name) : Bool :=
  n == ``WellFounded.fix || n == ``WellFounded.fixF || n == ``WellFounded.apply
    || n == ``invImage || n == ``measure || n == ``sizeOfWFRel
    || n == ``Prod.lex || n == ``PSigma.lex || n == ``PSigma.mk
    || n == ``Acc.rec || n == ``WellFoundedRelation.rel
    || n == ``emptyWf || n == ``PProd.mk || n == ``WellFounded.Nat.fix

/-- Is this a name with no run-time content at all? -/
def isSkipped (env : Environment) (n : Name) : Bool :=
  if isRecursorLike n || isRecursionScaffolding n then true
  else match env.find? n with
    | some (.inductInfo _) | some (.ctorInfo _) | some (.recInfo _)
    | some (.thmInfo _) | some (.axiomInfo _) | some (.quotInfo _) => true
    | some (.defnInfo di) => di.type.isSort || di.type.getForallBody.isSort
    | _ => false

/-- Is this a name the translation looks *through* rather than *at*? -/
def isInlined (n : Name) : CoreM Bool := do
  let env ← getEnv
  return isBuiltin n || n.isInternal || Lean.Meta.isInstanceCore env n
    || Lean.Meta.isMatcherCore env n || (← Lean.isProjectionFn n)

/-- One entry of the context: a declaration the translation would need. -/
structure CtxEntry where
  /-- Its name. -/
  name : Name
  /-- Is it representable? -/
  ok : Bool
  /-- The module it comes from, or `_current` for this one. -/
  mod : String
  deriving Inhabited

/-- What the walk over the dependencies has learnt. -/
structure ScanState where
  /-- Which names have already been decided, and how. -/
  seen : Std.HashMap Name Bool := {}
  /-- The `@[extern]` constants reached. -/
  prims : Std.HashSet Name := {}
  deriving Inhabited

/-- The names a definition's body mentions that the context has to hold: the walk goes
    *through* the inlined names and stops at everything else. -/
partial def listableDeps (n : Name) (fuel : Nat) :
    StateRefT (Std.HashSet Name) (StateRefT ScanState CoreM) (List Name) := do
  if fuel == 0 then return []
  if (← getThe (Std.HashSet Name)).contains n then return []
  modifyThe (Std.HashSet Name) (·.insert n)
  let env ← getEnv
  let some (.defnInfo di) := env.find? n | return []
  let mut out : List Name := []
  for c in di.value.getUsedConstants do
    if c == n then continue
    if Lean.isExtern env c then
      modifyThe ScanState fun s => { s with prims := s.prims.insert c }
      continue
    if isSkipped env c then continue
    if ← isInlined c then
      out := out ++ (← listableDeps c (fuel - 1))
    else
      out := out ++ [c]
  return out

/-- Is `n` representable — a total definition, all of whose dependencies are
    representable?  The walk stops at `@[extern]` constants and at the names with no
    run-time content. -/
partial def scan (n : Name) (fuel : Nat) : StateRefT ScanState CoreM Bool := do
  let env ← getEnv
  if let some b := (← getThe ScanState).seen[n]? then return b
  if fuel == 0 then return false
  if Lean.isExtern env n then
    modifyThe ScanState fun s =>
      { s with prims := s.prims.insert n, seen := s.seen.insert n true }
    return true
  if isSkipped env n then
    modifyThe ScanState fun s => { s with seen := s.seen.insert n true }
    return true
  -- assume representable while the body is looked at, so a recursive call terminates
  modifyThe ScanState fun s => { s with seen := s.seen.insert n true }
  let kind ← recursionKindOf n
  unless kind.representable do
    modifyThe ScanState fun s => { s with seen := s.seen.insert n false }
    return false
  let some (.defnInfo di) := env.find? n
    | modifyThe ScanState fun s => { s with seen := s.seen.insert n false }
      return false
  let mut ok := true
  for c in di.value.getUsedConstants do
    if c == n then continue
    unless ← scan c (fuel - 1) do ok := false
  modifyThe ScanState fun s => { s with seen := s.seen.insert n ok }
  return ok

/-- Whether the definition is representable, the declarations it needs with their own
    verdicts, and the `@[extern]` constants it uses. -/
def analyse (n : Name) : CoreM (Bool × List CtxEntry × List Name) := do
  let env ← getEnv
  let ((selfOk, deps), st) ← (do
      let selfOk ← scan n 200
      let (deps, _) ← (listableDeps n 200).run {}
      let mut entries : List (Name × Bool) := []
      let mut seenNames : Std.HashSet Name := {}
      for c in deps do
        unless seenNames.contains c do
          seenNames := seenNames.insert c
          entries := entries ++ [(c, ← scan c 200)]
      pure (selfOk, entries)).run {}
  let modOf (c : Name) : String :=
    match env.getModuleIdxFor? c with
    | some i => toString env.header.moduleNames[i.toNat]!
    | none => "_current"
  let es := deps.map (fun (c, ok) => { name := c, ok, mod := modOf c : CtxEntry })
  let es := es.toArray.qsort (fun a b => toString a.name < toString b.name) |>.toList
  let prims := st.prims.toList.toArray.qsort (fun a b => toString a < toString b) |>.toList
  return (selfOk, es, prims)

/-! ## The report -/

/-- Pad a string on the right to `n` characters. -/
private def pad (s : String) (n : Nat) : String :=
  s ++ "".pushn ' ' (n - s.length)

/-- Report on one declaration. -/
def report (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? n | throwError "unknown declaration `{n}`"
  let sig ← liftTermElabM do
    let f ← ppExpr ci.type
    pure (toString f)
  let kind ← liftCoreM (recursionKindOf n)
  let (kindStr, kindNote) := kind.describe
  -- argTy / resTy
  let (argStr, resStr, tyOk, tyWhy) ← liftTermElabM do
    match ← toTy ci.type with
    | .ok (.fn a b) => pure (tyStr a, tyStr b, true, "")
    | .ok τ => pure ("-                  (a constant, not a function)", tyStr τ, true, "")
    | .erased => pure ("-", "-", false, "it carries no value")
    | .no r => pure ("-", "-", false, r)
  let (selfOk, ctx, prims) ← liftCoreM (analyse n)
  let status :=
    if !kind.representable then "rejected"
    else if !tyOk then "rejected           (" ++ tyWhy ++ ")"
    else if !selfOk then "rejected           (a definition it calls is not representable)"
    else "representable in Term"
  let primsStr :=
    if prims.isEmpty then " -"
    else "\n" ++ "\n".intercalate (prims.map (fun c => "    " ++ toString c))
  let ctxStr :=
    if ctx.isEmpty then " -"
    else "\n" ++ "\n".intercalate (ctx.map (fun e =>
      "    " ++ (if e.ok then "ok " else "BAD") ++ " " ++ toString e.name ++ "  [" ++ e.mod ++ "]"))
  logInfo <| String.intercalate "\n" [
    "LeanFunction " ++ toString n,
    "  signature   : " ++ sig,
    "  argTy       : " ++ argStr,
    "  resTy       : " ++ resStr,
    "  recursion   : " ++ pad kindStr 19 ++ kindNote,
    "  status      : " ++ status,
    "  primitives  :" ++ primsStr,
    "  context     :" ++ ctxStr]

/-- Report on what a Lean definition would compile to: its `Ty`, the kind of recursion
    Lean used, the primitives it needs and the context it would drag in. -/
syntax (name := generateTermAndCtxFor)
  "#leanjs_generate_term_and_ctx_for " ident : command

@[command_elab generateTermAndCtxFor]
def elabGenerateTermAndCtxFor : CommandElab := fun stx => do
  match stx with
  | `(#leanjs_generate_term_and_ctx_for $i:ident) => do
      let n ← liftCoreM (realizeGlobalConstNoOverload i)
      report n
  | _ => throwUnsupportedSyntax

/-! ## Reporting on a whole module

`#leanjs_generate_term_and_ctx_for_all` is the same report, applied to **every public
function of the file it appears in**: every `def` the module itself declares that is not
private, not an instance, not a projection and not one of the auxiliary definitions an
elaborator generates.  That is what the snapshot files use, so that adding a function to
one of them adds a line to its report rather than being silently left out. -/

/-- Is this name nested inside an instance — the method of a `deriving`d instance, say? -/
def isUnderInstance (env : Environment) : Name → Bool
  | .anonymous => false
  | .num p _ => isUnderInstance env p
  | .str p _ => Lean.Meta.isInstanceCore env p || isUnderInstance env p

/-- `s` without a trailing `_<digits>`: Lean numbers the scaffolding it makes for a
    family of types, so `below_1` and `brecOn_2` are `below` and `brecOn`. -/
def dropIndexSuffix (s : String) : String :=
  let rev := s.toList.reverse
  let digits := rev.takeWhile Char.isDigit
  match rev.drop digits.length with
  | '_' :: more =>
      if digits.isEmpty || more.isEmpty then s else String.ofList more.reverse
  | _ => s

/-- The names of the definitions Lean puts in the environment *for a declared type*
    rather than because the file asked for them: the eliminators and the course-of-values
    scaffolding of an `inductive`, and the projections and injectivity lemmas of a
    `structure`. -/
def isTypeScaffoldingComponent (s : String) : Bool :=
  let s := dropIndexSuffix s
  isRecursorLike (.str .anonymous s)
    || s == "ctorElim" || s == "ctorElimType" || s == "toCtorIdx" || s == "ctorIdx"
    || s == "induct" || s == "fun_cases" || s == "injEq" || s == "sizeOf_spec"
    || s == "eq_def" || s == "eq" || s == "mk" || s == "sizeOf_eq"

/-- Was this name made *for a type* the file declares — `Tree.brecOn_1.go`, say — rather
    than written in it?  Every component of the name is looked at, since the scaffolding
    of a nested recursion hides under a name of its own; and `C.elim` is taken as made
    for the constructor `C` rather than written, which is why the constructor is looked
    up rather than the component only matched. -/
def isTypeScaffolding (env : Environment) : Name → Bool
  | .anonymous => false
  | .num p _ => isTypeScaffolding env p
  | .str p s =>
      isTypeScaffoldingComponent s
        || (s == "elim" && (env.find? p matches some (.ctorInfo _)))
        || isTypeScaffolding env p

/-- Is this a declaration of the current module that the report should cover? -/
def isPublicFunction (env : Environment) (n : Name) : CoreM Bool := do
  if env.getModuleIdxFor? n |>.isSome then return false      -- imported
  if n.isInternal || isPrivateName n then return false
  if isRecursorLike n || isRecursionScaffolding n then return false
  if isTypeScaffolding env n then return false
  match env.find? n with
  | some (.defnInfo _) | some (.opaqueInfo _) => pure ()
  | _ => return false
  if Lean.Meta.isInstanceCore env n || Lean.Meta.isMatcherCore env n then return false
  -- the body of a `deriving` instance (`instDecidableEqFoo.decEq`, …) is the instance's,
  -- not a function the file declares
  if isUnderInstance env n then return false
  if ← Lean.isProjectionFn n then return false
  return true

/-- The public functions of the current module, in alphabetical order. -/
def publicFunctions : CoreM (Array Name) := do
  let env ← getEnv
  let mut ns : Array Name := #[]
  for (n, _) in env.constants.map₂ do
    if ← isPublicFunction env n then ns := ns.push n
  return ns.qsort (fun a b => toString a < toString b)

/-- Report on every public function of the file this command appears in. -/
syntax (name := generateTermAndCtxForAll)
  "#leanjs_generate_term_and_ctx_for_all" : command

@[command_elab generateTermAndCtxForAll]
def elabGenerateTermAndCtxForAll : CommandElab := fun _ => do
  let ns ← liftCoreM publicFunctions
  if ns.isEmpty then
    logInfo "no public function in this module"
  for n in ns do
    report n

end LeanScript.Term
