module

public meta import LeanScript.ToTerm.TransRecObjectCases

@[expose] public section

meta section

/-!
# The translation: a structural recursion on a recursive record

`transRecObjectBrecOn?`, the clause of the translation for a structural recursion on a
**recursive record** — an inductive type with one constructor that mentions itself only
inside another type, such as

```lean
inductive Cell where
  | mk (label : Nat) (next : Option Cell)
```

whose tree is `Ty.recObject`.  Lean compiles such a recursion into `Cell.brecOn`, whose
branch is handed the whole history of the recursion; the grammar's fold of a record,
`LeanScript.Term.recObject_rec' k`, hands its branch the record's fields and a **window**:
the fields again, with every subvalue replaced by the *answer tree* of depth `k` at it
(`LeanScript.TyWf.recObjectRecBinders`).

**How the branch is read.**  At depth `k` the window is taken apart completely: the record
of fields at each level, a dispatch on each field that holds subvalues, and, for each
subvalue at levels `1 … k`, the answer tree there — the answer at it and the window of its
own fields.  The subvalues at level `k + 1` are the frontier: only their answers are in
the window.  Each leaf of that case tree fixes the **shape** of the value `k + 1` levels
down, so the Lean branch is instantiated at that shape — the labels, and the frontier
subvalues, as variables — and at the history built for it, whose entries are the
variables standing for the answers.  The branch then reduces: its `match` is taken
apart by the shape, and its reads of the history become those variables.

The depth is the smallest `k` at which, at every leaf, nothing is left of a frontier
subvalue or of the history below the frontier: a branch that reads the answer two cells
down (`fib`) is depth `1`, one that only reads the answer at the cell below (a sum, a
tail-recursive loop) is depth `0`.

The record's fields may be values that do not mention the record, or values of a
(non-recursive) union or structure type — `Option Cell`, `Nat × Cell` — whose fields are
read in the same way, or arrays of such values (`Array Cell`, `Array (Option Cell)`,
`Array (Array Cell)`): an array is a frontier value, and the answer of the recursion at it
(and at its list) is the fold of the window's array (`recObjListAnswer`).  A field may
also be a function into the record (`Nat → Cell`) or a delay of it (`Thunk Cell`), a
frontier value at every depth.  Its window is the function of the answer trees (or the
delayed answer tree): at depth `0` that is the function of the answers (the delayed
answer), and deeper the function of the answers, `fun a => (window a).1` (the delayed
answer, `Thunk.mk (window.get).1`), is bound beside it (`LeanScript.Term.fnTreeAnswer`, `LeanScript.Term.thunkTreeAnswer`,
whose values `LeanScript.RecFnFieldFacts` proves are the depth-`0` window).  Either way
the answer at `f a` is that function applied to `a`.  The value `f a` itself is never
taken apart: Lean's structural recursion does not accept a recursive call on what a
`match` on `f a` binds, so no branch does that.

A declaration of **several constructors** whose occurrences sit inside other types is a
recursive newtype whose body is the union of its constructors
(`LeanScript.Deriving.assembleShape`); its fold reads that body as a union field whose
constructors are the declaration's own (`RecObjInfo.unionAlias`).
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- How deep a fold of a recursive record the translation looks for: the option
    `leanscript.toTerm.maxRecObjectRecDepth` (`24` by default). -/
def maxRecObjectRecDepth : MetaM Nat :=
  return leanscript.toTerm.maxRecObjectRecDepth.get (← getOptions)

/-- A structural recursion on a **recursive record**, as Lean compiled it: `X.brecOn` on a
    type whose tree is `Ty.recObject`.  It becomes `LeanScript.Term.recObject_rec' k`, at
    the smallest depth `k` that serves every read of the history (see the module
    documentation).  `none` when the recursion is not on a recursive record. -/
def transRecObjectBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "brecOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  unless ii.numIndices == 0 do return none
  let nP := ii.numParams
  let nM := ri.numMotives
  let arity := nP + nM + 1 + nM
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let major := args[nP + nM]!
  let sty ← tyOfTerm major
  -- a recursive record, or a recursive newtype (whose one field is its body)
  let (isAlias, fs, hwf) ← match ← tyView sty with
    | .recObject fs hwf => pure (false, fs, hwf)
    | .recAlias b hwf => pure (true, b, hwf)
    | _ => return none
  let params := args.extract 0 nP
  let motives := args.extract nP (nP + nM)
  let brecF := args[nP + nM + 1]!
  -- the motive of the record: non-dependent
  let m0 ← whnf motives[0]!
  unless m0.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  let τLean ← lambdaBoundedTelescope m0 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    return body
  let τ ← tyOfType τLean
  let selfTy ← whnf (← inferType major)
  let ilvls := selfTy.getAppFn.constLevels!
  let ctor := ii.ctors[0]!
  -- several constructors: a recursive newtype whose body is the union of them
  let unionAlias := ii.ctors.length > 1
  if unionAlias && !isAlias then return none
  let ctorFields (cn : Name) : MetaM (Array RecObjField) := do
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls) params
    forallTelescopeReducing cty fun xs _ => do
      let mut out := #[]
      for x in xs do
        let t ← inferType x
        if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
        if ← LeanScript.Deriving.erasedBinder t then
          throwError "`#leanscript_to_term`: the constructor {cn} has a field the \
            language erases, which the fold of a record does not read"
        out := out.push (← classifyRecObjField ind selfTy t)
      return out
  let fields ← if unionAlias then
      pure #[RecObjPayloadField.union ind ilvls params
        (← ii.ctors.toArray.mapM fun cn => return (cn, ← ctorFields cn))]
    else ctorFields ctor
  if isAlias then
    unless fields.size == 1 &&
        fields.all (fun f => f matches .union .. | .struct .. | .array ..) do
      throwError "`#leanscript_to_term`: the recursive newtype {ind} is folded only when \
        its body is a value of a union type (such as `Option {ind}`) or of a structure \
        (such as `Nat × Option {ind}`)"
  -- every branch of the `brecOn`, and the type each motive is a function of (the record,
  -- then the auxiliary types of a nested occurrence: `Option Cell`, `Array Tree`, …)
  let brecFs := args.extract (nP + nM + 1) arity
  let motiveDoms ← brecFs.mapM fun f => do
    let .forallE _ d _ _ ← whnf (← inferType f)
      | throwError "`#leanscript_to_term`: internal: a branch of {n} is not a function"
    return d
  let info : RecObjInfo :=
    { ind, ctor, lvls := ilvls, params, selfTy, fields, τLean, τ, isAlias, unionAlias, trans,
      motives, brecFs, motiveDoms }
  let scrutT ← trans c major
  let attempt (k : Nat) : MetaM Expr := do
    let bindersE ← reduceTy
      (mkAppN (mkConst (if isAlias then ``LeanScript.TyWf.recAliasRecBinders
        else ``LeanScript.TyWf.recObjectRecBinders)) #[fs, hwf, τ, mkNatLit k])
    let bTys := (← listOfExpr bindersE).toArray
    -- the binders of the branch: the fields of the record (Lean variables, for the ones
    -- that do not mention it), then the window
    let nF := if isAlias then 0 else fields.size
    let decls : Array (Name × (Array Expr → MetaM Expr)) :=
      (Array.range nF).map fun i => match fields[i]! with
        | .plain t => (Name.mkSimple s!"b{i}", fun _ => pure t)
        | _ => (Name.mkSimple s!"b{i}", fun _ => pure (mkConst ``Unit))
    withLocalDeclsD decls fun bs => do
    let ids ← (Array.range bTys.size).mapM fun i =>
      if h : i < bs.size then pure bs[i].fvarId! else mkFreshFVarId
    let c1 := c.pushFields (ids.zip bTys)
    let branch ← recObjLevel info c1 #[] #[] ids.back! bTys.back! k
      (fun c' answers frontier vals =>
        recObjLeaf trans info brecF motives c' answers frontier vals)
      (outer := if isAlias then none else some bs)
    return mkAppN (mkConst (if isAlias then `LeanScript.Term.recAlias_rec'
      else `LeanScript.Term.recObject_rec'))
      #[c.sg, c.gamma, τ, fs, hwf, mkNatLit k, scrutT, branch]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  let maxK ← maxRecObjectRecDepth
  for k in [0:maxK + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the recursive record (or \
        newtype) {ind} is not the fold of a record at any depth up to \
        {maxK} (the option `leanscript.toTerm.maxRecObjectRecDepth`) — the fold \
        `recObject_rec k` gives its branch the fields and the answers `k + 1` levels \
        down, so a branch that takes apart or reads a value further down, or uses a \
        subvalue other than through the answer at it, has no term.  At the last depth \
        tried: {lastErr.getD m!"(no error)"}"
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
