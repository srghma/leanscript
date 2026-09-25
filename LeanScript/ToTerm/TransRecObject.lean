module

public meta import LeanScript.ToTerm.TransRecObjectPieces

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

mutual

/-- Take apart a **window** — the record of fields of one level, with each subvalue
    replaced by its answer tree of depth `j` — bound in `c` as `wv` of type `wTy`, and
    continue with the Lean values of the fields. -/
partial def recObjLevel (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (wv : FVarId) (wTy : Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr)
    (outer : Option (Array Expr) := none) :
    MetaM Expr := do
  if info.isAlias then
    -- a newtype has one field, its body, and the window is that body itself
    return ← recObjPayloadFrom info c answers frontier info.fields #[mkFVar wv] #[wTy] j 0
      #[] k
  let .record fsW ← tyView wTy
    | throwError "`#leanscript_to_term`: internal: the window of the fold is not a record"
  let fTys := (← recordFieldTys fsW).toArray
  unless fTys.size == info.fields.size do
    throwError "`#leanscript_to_term`: internal: the window has {fTys.size} fields, the \
      record {info.ind} {info.fields.size}"
  -- at the top level, a field that does not mention the record is read where the
  -- branch binds it, not out of the window, which holds the same value
  let override : Array (Option Expr) := match outer with
    | some o => info.fields.mapIdx fun i f => match f, o[i]? with
        | .plain _, some v => some v
        | _, _ => none
    | none => #[]
  let body ← recObjPayload info c answers frontier info.fields fTys j k override
  -- `recObjPayload` bound the fields in the context of the branch of this dispatch
  return mkAppN (mkConst `LeanScript.Term.record_casesOn)
    #[c.sg, c.gamma, info.τ, fsW, ← c.var wv, body]

/-- The fields of one constructor of a union field: those that do not mention the record
    are Lean variables; each one that is the record is, in the window, its answer tree —
    at depth `0` the answer alone, which leaves the subvalue a frontier variable, and
    otherwise the answer beside the window of its own fields, which is taken apart in
    turn. -/
partial def recObjPayload (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array RecObjPayloadField) (pTys : Array Expr) (j : Nat)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr)
    (override : Array (Option Expr) := #[]) :
    MetaM Expr := do
  unless pfs.size == pTys.size do
    throwError "`#leanscript_to_term`: internal: a constructor of a field of {info.ind} \
      has {pfs.size} fields, its tree {pTys.size}"
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    pfs.mapIdx fun i f => match f with
      | .plain t => (Name.mkSimple s!"p{i}", fun _ => pure t)
      | .self =>
          if j == 0 then (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
          else (Name.mkSimple s!"tree{i}", fun _ => pure (mkConst ``Unit))
      | .struct .. => (Name.mkSimple s!"s{i}", fun _ => pure (mkConst ``Unit))
      | .union .. => (Name.mkSimple s!"u{i}", fun _ => pure (mkConst ``Unit))
      | .arraySelf .. => (Name.mkSimple s!"a{i}", fun _ => pure (mkConst ``Unit))
  withLocalDeclsD decls fun ps => do
    let c' := c.pushFields (ps.zip pTys |>.map fun (x, t) => (x.fvarId!, t))
    -- a value given from outside replaces the variable, where there is one
    let ps' := ps.mapIdx fun i x => (override[i]?.bind id).getD x
    recObjPayloadFrom info c' answers frontier pfs ps' pTys j 0 #[] k

/-- The fields of one constructor of a union field, from the `i`-th on. -/
partial def recObjPayloadFrom (info : RecObjInfo) (c : TCtx) (answers : Array (Expr × Expr))
    (frontier : Array Expr) (pfs : Array RecObjPayloadField) (ps pTys : Array Expr) (j : Nat)
    (i : Nat) (pvals : Array Expr)
    (k : TCtx → Array (Expr × Expr) → Array Expr → Array Expr → MetaM Expr) :
    MetaM Expr := do
  let go := recObjPayloadFrom info
  if h : i < ps.size then
    match pfs[i]! with
    | .plain _ => go c answers frontier pfs ps pTys j (i + 1) (pvals.push ps[i]) k
    | .struct sc slvls sparams sfs =>
        -- a structure around the record: its case analysis, and its fields read in turn
        let .record fsS ← tyView pTys[i]!
          | throwError "`#leanscript_to_term`: internal: the tree of a structure inside \
              {info.ind} is not a record"
        let sTys := (← recordFieldTys fsS).toArray
        let inner ← recObjPayload info c answers frontier sfs sTys j
          fun c' answers' frontier' svals => do
            let v := mkAppN (mkConst sc slvls) (sparams ++ svals)
            go c' answers' frontier' pfs ps pTys j (i + 1) (pvals.push v) k
        return mkAppN (mkConst `LeanScript.Term.record_casesOn)
          #[c.sg, c.gamma, info.τ, fsS, ← c.var ps[i].fvarId!, inner]
    | .union _ ulvls uparams uctors =>
        -- a union around the record: its dispatch, each branch binding the fields of its
        -- constructor, which are read in turn
        let .taggedUnion l ← tyView pTys[i]!
          | throwError "`#leanscript_to_term`: the tree of a union inside {info.ind} is not \
              a tagged union of the language"
        let mkBranch : BranchFn := fun minor _ payloadTys => do
          let ci ← natOfExpr minor
          let (cn, cfs) := uctors[ci]!
          recObjPayload info c answers frontier cfs payloadTys.toArray j
            fun c' answers' frontier' cvals =>
              let v := mkAppN (mkConst cn ulvls) (uparams ++ cvals)
              go c' answers' frontier' pfs ps pTys j (i + 1) (pvals.push v) k
        let minors := (Array.range uctors.size).map mkNatLit
        let cases ← mkTaggedUnionCases mkBranch c info.τ l 0 minors (uctors.map (·.1))
        return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn)
          #[c.sg, c.gamma, info.τ, l, ← c.var ps[i].fvarId!, cases]
    | .arraySelf arrTy =>
        -- an array of the record: a frontier value, whose own answer (if the recursion
        -- has one for it) is computed from the answers at its elements and bound
        withLocalDeclD `arr arrTy fun arrV => do
          let u ← getDecLevel info.selfTy
          let aux? ← recObjAuxMotive info arrTy
          let list? ← recObjAuxMotive info (mkApp (mkConst ``List [u]) info.selfTy)
          let win ← c.var ps[i].fvarId!
          let listOfArr := mkApp2 (mkConst ``Array.toList [u]) info.selfTy arrV
          -- the answer at the list inside the array, if the recursion has one for lists
          let withList (cont : TCtx → Array (Expr × Expr) → Option (Nat × Expr) → MetaM Expr) :
              MetaM Expr := do
            match list? with
            | none => cont c answers none
            | some (mL, τLLean) =>
                let τL ← tyOfType τLLean
                let listT ← recObjListAnswer info c win pTys[i]! j mL τLLean
                withLocalDeclD `ansList τLLean fun ansL => do
                  let cL := c.pushFields #[(ansL.fvarId!, τL)]
                  let body ← cont cL (answers.push (motiveKey mL listOfArr, ansL))
                    (some (mL, ansL))
                  return mkAppN (mkConst `LeanScript.Term.letE)
                    #[c.sg, c.gamma, τL, info.τ, listT, body]
          withList fun cL answersL ansL? => do
            -- then the answer at the array, if the recursion has one for arrays
            match aux? with
            | none =>
                go cL answersL (frontier.push arrV) pfs ps pTys j (i + 1) (pvals.push arrV) k
            | some (mA, τALean) =>
                let τA ← tyOfType τALean
                let arrT ← recObjArrAnswer info cL mA ansL?
                withLocalDeclD `ansArr τALean fun ansA => do
                  let cA := cL.pushFields #[(ansA.fvarId!, τA)]
                  let body ← go cA (answersL.push (motiveKey mA arrV, ansA))
                    (frontier.push arrV) pfs ps pTys j (i + 1) (pvals.push arrV) k
                  return mkAppN (mkConst `LeanScript.Term.letE)
                    #[c.sg, cL.gamma, τA, info.τ, arrT, body]
    | .self =>
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

/-- How deep a fold of a recursive record the translation looks for: the option
    `leanscript.toTerm.maxRecObjectRecDepth` (`24` by default). -/
def maxRecObjectRecDepth : MetaM Nat :=
  return leanscript.toTerm.maxRecObjectRecDepth.get (← getOptions)

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
    unless fields.size == 1 &&
        fields.all (fun f => f matches .union .. | .struct .. | .arraySelf ..) do
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
    { ind, ctor, lvls := ilvls, params, selfTy, fields, τLean, τ, isAlias, trans, motives,
      brecFs, motiveDoms }
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
    return mkAppN (mkConst (if isAlias then `LeanScript.Term.recAlias_rec
      else `LeanScript.Term.recObject_rec))
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
