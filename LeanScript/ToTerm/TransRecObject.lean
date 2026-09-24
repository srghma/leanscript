module

public meta import LeanScript.ToTerm.TransRec
public meta import LeanScript.ToTerm.Brec

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
`LeanScript.Term.recObject_rec k`, hands its branch the record's fields and a **window**:
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
(non-recursive) union type — `Option Cell` — whose constructors hold the
record directly or values that do not mention it.  Any other recursive record is
refused.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- How the fold of a record reads one field of it. -/
inductive RecObjField where
  /-- A field that does not mention the record, of this Lean type. -/
  | plain (ty : Expr)
  /-- A field of a union type (`Option Cell`): the inductive, its universe levels and
      parameters, and for each constructor its name and its fields — `none` for a field
      that is the record itself, `some α` for one of the Lean type `α`, which does not
      mention it. -/
  | union (ind : Name) (lvls : List Level) (params : Array Expr)
      (ctors : Array (Name × Array (Option Expr)))
  deriving Inhabited

/-- What the fold of a record needs to know about it and about the recursion. -/
structure RecObjInfo where
  /-- The inductive type. -/
  ind : Name
  /-- Its constructor, with universe levels and parameters. -/
  ctor : Name
  /-- The universe levels. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- The Lean type of the record, at its parameters. -/
  selfTy : Expr
  /-- How each field is read. -/
  fields : Array RecObjField
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- Is it a recursive **newtype** (`Ty.recAlias`)?  Then the one field is the body, and
      a window is that body itself rather than a record of fields. -/
  isAlias : Bool := false

/-- How a field of this Lean type is read by the fold of the record `info`. -/
def classifyRecObjField (ind : Name) (selfTy : Expr) (fty : Expr) : MetaM RecObjField := do
  let mentions (t : Expr) : Bool := (t.find? fun s => s.isConstOf ind).isSome
  if !mentions fty then return .plain fty
  let fty' ← whnf fty
  let .const j jl := fty'.getAppFn
    | throwError "`#leanscript_to_term`: the field of type {fty} of the recursive record \
        {ind} is not a value of a union type"
  let some (.inductInfo ji) := (← getEnv).find? j
    | throwError "`#leanscript_to_term`: the field of type {fty} of the recursive record \
        {ind} is not a value of an inductive type"
  let jargs := fty'.getAppArgs
  unless ji.numIndices == 0 && jargs.size == ji.numParams && !ji.isRec do
    throwError "`#leanscript_to_term`: the field of type {fty} of the recursive record \
      {ind} is not a value of a non-recursive union type"
  let mut ctors := #[]
  for cn in ji.ctors do
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams jl) jargs
    let fs ← forallTelescopeReducing cty fun xs _ => do
      let mut out : Array (Option Expr) := #[]
      for x in xs do
        let t ← inferType x
        if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
        if ← LeanScript.Deriving.erasedBinder t then
          throwError "`#leanscript_to_term`: the constructor {cn} has a field the \
            language erases, which the fold of a record does not read"
        if ← isDefEq t selfTy then out := out.push none
        else if mentions t then
          throwError "`#leanscript_to_term`: the field of type {t} of {cn} mentions the \
            recursive record {ind} other than as the record itself"
        else out := out.push (some t)
      return out
    ctors := ctors.push (cn, fs)
  return .union j jl jargs ctors

/-- Reduce the reads of a history built out of `PProd.mk`s: its projections, wherever they
    sit in the branch. -/
def reduceHistoryProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun s => do
    match s with
    | .proj .. =>
        let s' ← whnfCore s
        return .done s'
    | _ =>
        if s.isAppOfArity ``PProd.fst 3 || s.isAppOfArity ``PProd.snd 3 then
          return .done (← whnfCore s)
        return .done s)

/-- The value of the history of a structural recursion on a record, at a value whose
    shape is known `k + 1` levels down.  `placeholder` is the type of the history with
    each motive replaced by a variable (`motiveVars`), so that the entry of the history
    that is the answer at a subvalue `x` is visibly `motiveVars[0] x`; `real` replaces
    those variables by the actual motives.  The answer at `x` is the variable `answers`
    maps it to; the entries of the other motives must be `PUnit`; anything that is still
    stuck — the history below a frontier subvalue — becomes a fresh metavariable, which
    the branch must not read. -/
partial def buildRecObjHistory (motiveVars : Array Expr) (motives : Array Expr)
    (answers : Array (Expr × Expr)) (placeholder : Expr) : MetaM Expr := do
  let real (t : Expr) : Expr := t.replaceFVars motiveVars motives
  let t ← whnf placeholder
  match t.getAppFn, t.getAppArgs with
  | .const ``PProd ls, #[a, b] =>
      let va ← buildRecObjHistory motiveVars motives answers a
      let vb ← buildRecObjHistory motiveVars motives answers b
      return mkAppN (mkConst ``PProd.mk ls) #[real a, real b, va, vb]
  | .const ``PUnit ls, #[] => return mkConst ``PUnit.unit ls
  | .fvar f, #[x] =>
      if motiveVars[0]!.fvarId! == f then
        for (s, ans) in answers do
          if s == x then return ans
        for (s, ans) in answers do
          if ← isDefEq s x then return ans
        throwError "`#leanscript_to_term`: internal: no answer for the subvalue {x}"
      else
        let rt ← whnf (real t)
        match rt with
        | .const ``PUnit ls => return mkConst ``PUnit.unit ls
        | _ => throwError "`#leanscript_to_term`: this recursion on a recursive record \
            also recurses on {x}, which the fold of a record has no answer for"
  | _, _ => mkFreshExprMVar (real t)

/-- The branch of the fold, at one leaf of the case tree: the Lean branch instantiated at
    the value built from the fields `vals`, reduced, and translated in `c`. -/
def recObjLeaf (trans : TransFn) (info : RecObjInfo) (brecF : Expr) (motives : Array Expr)
    (c : TCtx) (answers : Array (Expr × Expr)) (frontier : Array Expr) (vals : Array Expr) :
    MetaM Expr := do
  let shape := mkAppN (mkConst info.ctor info.lvls) (info.params ++ vals)
  let fty ← instantiateForall (← inferType brecF) #[shape]
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nP := info.params.size
  let nM := motives.size
  let motiveTys ← motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildRecObjHistory ms motives answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN brecF #[shape, hist])
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    throwError "`#leanscript_to_term`: this recursion on a recursive record reads the \
      value of the function further down than the depth tried"
  for g in frontier do
    if body.containsFVar g.fvarId! then
      throwError "`#leanscript_to_term`: this recursion on a recursive record takes apart \
        a value further down than the depth tried"
  trans c body

mutual

/-- Take apart a **window** — the record of fields of one level, with each subvalue
    replaced by its answer tree of depth `j` — bound in `c` as `wv` of type `wTy`, and
    continue with the Lean values of the fields. -/
partial def recObjLevel (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (wv : FVarId) (wTy : Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  if info.isAlias then
    -- a newtype has one field, its body, and the window is that body itself
    return ← recObjFieldsFrom info c answers frontier #[mkFVar wv] #[wTy] 0 #[] j k
  let .record fsW ← tyView wTy
    | throwError "`#leanscript_to_term`: internal: the window of the fold is not a record"
  let fTys := (← recordFieldTys fsW).toArray
  unless fTys.size == info.fields.size do
    throwError "`#leanscript_to_term`: internal: the window has {fTys.size} fields, the \
      record {info.ind} {info.fields.size}"
  -- the fields that do not mention the record are Lean variables, the others are read
  -- through the dispatch below
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    info.fields.mapIdx fun i f => match f with
      | .plain t => (Name.mkSimple s!"f{i}", fun _ => pure t)
      | .union .. => (Name.mkSimple s!"u{i}", fun _ => pure (mkConst ``Unit))
  let scrut ← c.var wv
  withLocalDeclsD decls fun xs => do
    let c' := c.pushFields (xs.zip fTys |>.map fun (x, t) => (x.fvarId!, t))
    let body ← recObjFieldsFrom info c' answers frontier xs fTys 0 #[] j k
    return mkAppN (mkConst `LeanScript.Term.record_casesOn)
      #[c.sg, c.gamma, info.τ, fsW, scrut, body]

/-- The fields of one level from the `i`-th on: a field of a union type is dispatched on,
    each branch binding the constructor's fields. -/
partial def recObjFieldsFrom (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (xs fTys : Array Expr) (i : Nat) (vals : Array Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  if h : i < xs.size then
    match info.fields[i]! with
    | .plain _ =>
        recObjFieldsFrom info c answers frontier xs fTys (i + 1) (vals.push xs[i]) j k
    | .union _ ulvls uparams uctors =>
        let .taggedUnion l ← tyView fTys[i]!
          | throwError "`#leanscript_to_term`: the field {i} of the recursive record \
              {info.ind} is not a union of the language"
        let mkBranch : BranchFn := fun minor _ payloadTys => do
          let ci ← natOfExpr minor
          let (cn, pfs) := uctors[ci]!
          recObjPayload info c answers frontier pfs payloadTys.toArray j
            fun c' answers' frontier' pvals =>
              let v := mkAppN (mkConst cn ulvls) (uparams ++ pvals)
              recObjFieldsFrom info c' answers' frontier' xs fTys (i + 1) (vals.push v) j k
        let minors := (Array.range uctors.size).map mkNatLit
        let cases ← mkTaggedUnionCases mkBranch c info.τ l 0 minors (uctors.map (·.1))
        return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn)
          #[c.sg, c.gamma, info.τ, l, ← c.var xs[i].fvarId!, cases]
  else
    k c answers frontier vals

/-- The fields of one constructor of a union field: those that do not mention the record
    are Lean variables; each one that is the record is, in the window, its answer tree —
    at depth `0` the answer alone, which leaves the subvalue a frontier variable, and
    otherwise the answer beside the window of its own fields, which is taken apart in
    turn. -/
partial def recObjPayload (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array (Option Expr)) (pTys : Array Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  unless pfs.size == pTys.size do
    throwError "`#leanscript_to_term`: internal: a constructor of a field of {info.ind} \
      has {pfs.size} fields, its tree {pTys.size}"
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    pfs.mapIdx fun i f => match f with
      | some t => (Name.mkSimple s!"p{i}", fun _ => pure t)
      | none =>
          if j == 0 then (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
          else (Name.mkSimple s!"tree{i}", fun _ => pure (mkConst ``Unit))
  withLocalDeclsD decls fun ps => do
    let c' := c.pushFields (ps.zip pTys |>.map fun (x, t) => (x.fvarId!, t))
    recObjPayloadFrom info c' answers frontier pfs ps pTys j 0 #[] k

/-- The fields of one constructor of a union field, from the `i`-th on. -/
partial def recObjPayloadFrom (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array (Option Expr)) (ps pTys : Array Expr) (j : Nat)
    (i : Nat) (pvals : Array Expr)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  let go := recObjPayloadFrom info
  if h : i < ps.size then
    match pfs[i]! with
    | some _ => go c answers frontier pfs ps pTys j (i + 1) (pvals.push ps[i]) k
    | none =>
        if j == 0 then
          -- the frontier: the answer is bound, the subvalue is a variable nothing may
          -- take apart
          withLocalDeclD `sub info.selfTy fun g =>
            go c (answers.push (g, ps[i])) (frontier.push g) pfs ps pTys j (i + 1)
              (pvals.push g) k
        else
          let .record fsT ← tyView pTys[i]!
            | throwError "`#leanscript_to_term`: internal: an answer tree is not a record"
          let tTys := (← recordFieldTys fsT).toArray
          let some wTy := tTys[1]?
            | throwError "`#leanscript_to_term`: internal: an answer tree has no window"
          withLocalDeclD `ans info.τLean fun ans => do
            let wv ← mkFreshFVarId
            let c2 := c.pushFields #[(ans.fvarId!, tTys[0]!), (wv, wTy)]
            let inner ← recObjLevel info c2 answers frontier wv wTy (j - 1)
              fun c3 answers3 frontier3 subVals => do
                let sub := mkAppN (mkConst info.ctor info.lvls) (info.params ++ subVals)
                go c3 (answers3.push (sub, ans)) frontier3 pfs ps pTys j (i + 1)
                  (pvals.push sub) k
            return mkAppN (mkConst `LeanScript.Term.record_casesOn)
              #[c.sg, c.gamma, info.τ, fsT, ← c.var ps[i].fvarId!, inner]
  else
    k c answers frontier pvals

end

/-- How deep a fold of a recursive record the translation looks for. -/
def maxRecObjectRecDepth : Nat := 8

/-- A structural recursion on a **recursive record**, as Lean compiled it: `X.brecOn` on a
    type whose tree is `Ty.recObject`.  It becomes `LeanScript.Term.recObject_rec k`, at
    the smallest depth `k` that serves every read of the history (see the module
    documentation).  `none` when the recursion is not on a recursive record. -/
def transRecObjectBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "brecOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  unless ii.numIndices == 0 && ii.ctors.length == 1 do return none
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
  let ci ← getConstInfoCtor ctor
  let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls) params
  let fields ← forallTelescopeReducing cty fun xs _ => do
    let mut out := #[]
    for x in xs do
      let t ← inferType x
      if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
        throwError "`#leanscript_to_term`: the constructor {ctor} has a dependent field"
      if ← LeanScript.Deriving.erasedBinder t then
        throwError "`#leanscript_to_term`: the constructor {ctor} has a field the \
          language erases, which the fold of a record does not read"
      out := out.push (← classifyRecObjField ind selfTy t)
    return out
  if isAlias then
    unless fields.size == 1 && fields.all (· matches .union ..) do
      throwError "`#leanscript_to_term`: the recursive newtype {ind} is folded only when \
        its body is a value of a union type (such as `Option {ind}`)"
  let info : RecObjInfo :=
    { ind, ctor, lvls := ilvls, params, selfTy, fields, τLean, τ, isAlias }
  let scrutT ← trans c major
  let attempt (k : Nat) : MetaM Expr := do
    let bindersE ← reduceTy
      (mkAppN (mkConst (if isAlias then ``LeanScript.TyWf.recAliasRecBinders
        else ``LeanScript.TyWf.recObjectRecBinders)) #[fs, hwf, τ, mkNatLit k])
    let bTys := (← listOfExpr bindersE).toArray
    let ids ← bTys.mapM fun _ => mkFreshFVarId
    let c1 := c.pushFields (ids.zip bTys)
    let branch ← recObjLevel info c1 #[] #[] ids.back! bTys.back! k
      fun c' answers frontier vals =>
        recObjLeaf trans info brecF motives c' answers frontier vals
    return mkAppN (mkConst (if isAlias then `LeanScript.Term.recAlias_rec
      else `LeanScript.Term.recObject_rec))
      #[c.sg, c.gamma, τ, fs, hwf, mkNatLit k, scrutT, branch]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  for k in [0:maxRecObjectRecDepth + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the recursive record (or \
        newtype) {ind} is not the fold of a record at any depth up to \
        {maxRecObjectRecDepth} — the fold \
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
