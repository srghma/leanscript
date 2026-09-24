module

public meta import LeanScript.ToTerm.TransRecObject

@[expose] public section

meta section

/-!
# The translation: a structural recursion on a recursive tagged union

`transRecUnionBrecOn?`, the clause of the translation for a structural recursion on a
**recursive tagged union** — an inductive type with several constructors whose fields are
either the type itself or values that do not mention it, such as

```lean
inductive Tree where
  | leaf
  | node (left : Tree) (val : Nat) (right : Tree)
```

whose tree is `Ty.recTaggedUnion`.  (`List α` is one too; `List.brecOn` comes here when
the one-step translation of `LeanScript.ToTerm.TransBrec` cannot serve it.)

Lean compiles such a recursion into `Tree.brecOn`, whose branch is handed the whole
history of the recursion; the grammar's fold, `LeanScript.Term.recTaggedUnion_rec k`,
hands each branch the constructor's fields and the answers at its occurrences of the
union (`TyWf.recBinders`), and lets a branch **look further down**, at most `k` times
along a path: dispatch again on one of those occurrences (`LeanScript.FoldKBranch.deep`)
and be handed *its* fields and answers.

**How the branch is read.**  The case tree is built top down.  At each node the value's
shape is known down to that node: the constructors dispatched on along the path, and a
variable for every field not descended into.  The Lean branch is instantiated at that
shape and at the history built for it — whose entry at a subvalue that is bound is the
variable standing for the answer there, and whose deeper parts are unknown — and reduced.
If nothing unknown is left, that is the answer (`FoldKBranch.here`).  Otherwise, when the
depth allows it, each occurrence among the node's fields is tried in turn as the one to
look into (`FoldKBranch.deep`).

The depth is the smallest `k` (up to `maxRecUnionRecDepth`) at which every branch is
served.  A recursion that needs to look into **two** subvalues at once (the answers at
the grandchildren below both children of a binary tree) has no term, since a deeper look
descends one path.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- One constructor of a recursive tagged union, as the fold reads it. -/
structure RecUnionCtor where
  /-- The Lean constructor. -/
  name : Name
  /-- Its fields: `none` for a field that is the union itself, `some α` for one of the
      Lean type `α`, which does not mention it. -/
  fields : Array (Option Expr)
  /-- The list of its field trees, as an expression of type `List (TyWfIn 1)` — the index
      of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr

/-- What the fold of a recursive tagged union needs to know about it and the recursion. -/
structure RecUnionInfo where
  /-- The inductive type. -/
  ind : Name
  /-- The universe levels. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- The Lean type of the union, at its parameters. -/
  selfTy : Expr
  /-- The constructors, in order. -/
  ctors : Array RecUnionCtor
  /-- The schema of the union. -/
  l : Expr
  /-- The binders of a branch, `TyWf.recBinders ty τ`. -/
  bindE : Expr
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- The Lean branch of the `brecOn`. -/
  brecF : Expr
  /-- The motives of the `brecOn`. -/
  motives : Array Expr

/-- The index lists of the branches of a dispatch on this schema, one per constructor, in
    order: `fields.toList` for a constructor with a non-empty payload, `[]` for one
    without, as `LeanScript.TaggedUnionFoldKCases` is indexed. -/
partial def recUnionCtorIndices (l : Expr) : MetaM (Array Expr) := do
  let ι := tyWfInE 1
  let toListE (ne : Expr) : Expr :=
    mkApp2 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
      ι ne
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) ι
  let rec cps (cp : Expr) : MetaM (Array Expr) := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
        return #[toListE fields] ++ (← listOfExpr rest).toArray
    | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
        return #[nilE] ++ (← cps rest)
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      return #[toListE fields, next] ++ (← listOfExpr rest).toArray
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return #[nilE] ++ (← cps rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- Replace the variables descended into by the shapes found for them, in the order they
    were descended into (a shape may mention variables descended into later). -/
def resolveShape (descend : Array (FVarId × Expr)) (e : Expr) : Expr :=
  descend.foldl (init := e) fun acc (f, s) => acc.replaceFVar (.fvar f) s

/-- The branch of the fold at a node of the case tree: the Lean branch instantiated at the
    shape found so far (`top` resolved through `descend`) and at the history in which the
    answer at a bound subvalue is its variable (`answers`), reduced, and translated in
    `c`.  Fails when the reduced branch still reads something the fold has not given. -/
def recUnionLeaf (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr)) : MetaM Expr := do
  let shape := resolveShape descend top
  let answers := answers.map fun (s, a) => (resolveShape descend s, a)
  let fty ← instantiateForall (← inferType info.brecF) #[shape]
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nP := info.params.size
  let nM := info.motives.size
  let motiveTys ← info.motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildRecObjHistory ms info.motives answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN info.brecF #[shape, hist])
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    throwError "`#leanscript_to_term`: this recursion on a recursive tagged union reads \
      the value of the function, or takes a value apart, further down than the fold \
      looks at this depth"
  trans c body

/-- The pointer at the `p`-th field of this list of field trees, which is an occurrence
    of the union. -/
def mkSelfFieldE (fsL : Array Expr) (p : Nat) : MetaM Expr := do
  let ι := tyWfInE 1
  let mut acc : Option Expr := none
  for r in [0:p + 1] do
    let i := p - r
    let a := fsL[i]!
    let rest ← mkListLit ι (fsL.extract (i + 1) fsL.size).toList
    match acc with
    | none =>
        let h ← mkEqRefl (mkConst ``LeanScript.Ty.self)
        acc := some (mkAppN (mkConst ``LeanScript.SelfField.here) #[a, rest, h])
    | some inner =>
        acc := some (mkAppN (mkConst ``LeanScript.SelfField.there) #[a, rest, inner])
  return acc.get!

/-- The branches of a fold over the schema `l`, in its shape: `pre` are the implicit
    arguments every family of the case tree shares (signature, schema, binders, context,
    answer type, depth), and `branches` one `FoldKBranch` per constructor. -/
partial def mkRecUnionFoldKCases (pre : Array Expr) (l : Expr) (branches : Array Expr) :
    MetaM Expr := do
  let rest (from_ : Nat) (fsLists : List Expr) : MetaM Expr := do
    let mut acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.nil) pre
    let n := fsLists.length
    for i in [0:n] do
      let idx := n - 1 - i
      let fs := fsLists[idx]!
      let more ← mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE 1))
        (fsLists.drop (idx + 1))
      acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.cons)
        (pre ++ #[fs, more, branches[from_ + idx]!, acc])
    return acc
  let rec cpCases (cp : Expr) (i : Nat) : MetaM Expr := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, restL]) =>
        let rs ← listOfExpr restL
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.here)
          (pre ++ #[fields, restL, branches[i]!, ← rest (i + 1) rs])
    | (``LeanScript.CtorsWithPayload.skip, #[_, more]) =>
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.skip)
          (pre ++ #[more, branches[i]!, ← cpCases more (i + 1)])
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, restL]) =>
      let rs ← listOfExpr restL
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.payloadFirst)
        (pre ++ #[fields, next, restL, branches[0]!, branches[1]!, ← rest 2 rs])
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) =>
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.skip)
        (pre ++ #[cp, branches[0]!, ← cpCases cp 1])
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

mutual

/-- The branches of a depth-`j` dispatch on the union, bound at `target` (a variable of
    the Lean type of the union, which each branch's shape is found for). -/
partial def recUnionCases (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (j : Nat)
    (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) : MetaM Expr := do
  let branches ← info.ctors.mapM fun ct =>
    recUnionBranch trans info c j top target descend answers ct
  let pre : Array Expr := #[c.sg, info.l, info.bindE, c.gamma, info.τ, mkNatLit j]
  mkRecUnionFoldKCases pre info.l branches

/-- The branch of one constructor, at depth `j`: the answer, if the Lean branch is served
    by what is known at this node, and otherwise a look into one of its occurrences. -/
partial def recUnionBranch (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (j : Nat)
    (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (ct : RecUnionCtor) : MetaM Expr := do
  let bTys := (← listOfExpr (← reduceTy (mkApp info.bindE ct.fsE)))
  -- the Lean variables the branch binds: each field, and after each occurrence the
  -- answer at it
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for h : i in [0:ct.fields.size] do
    match ct.fields[i] with
    | some t => decls := decls.push (Name.mkSimple s!"x{i}", fun _ => pure t)
    | none =>
        decls := decls.push (Name.mkSimple s!"sub{i}", fun _ => pure info.selfTy)
        decls := decls.push (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
  unless decls.size == bTys.length do
    throwError "`#leanscript_to_term`: internal: the branch of {ct.name} binds \
      {decls.size} values, its tree {bTys.length}"
  withLocalDeclsD decls fun xs => do
    let c' := c.pushFields (xs.zip bTys.toArray |>.map fun (x, t) => (x.fvarId!, t))
    -- the Lean fields, the subvalues and their answers
    let mut vals : Array Expr := #[]
    let mut subs : Array (Nat × Expr × Expr) := #[]
    let mut pos := 0
    for h : i in [0:ct.fields.size] do
      match ct.fields[i] with
      | some _ =>
          vals := vals.push xs[pos]!
          pos := pos + 1
      | none =>
          vals := vals.push xs[pos]!
          subs := subs.push (i, xs[pos]!, xs[pos + 1]!)
          pos := pos + 2
    let shape := mkAppN (mkConst ct.name info.lvls) (info.params ++ vals)
    let descend' := descend.push (target, shape)
    let answers' := answers ++ subs.map fun (_, s, a) => (s, a)
    let hereE := mkAppN (mkConst `LeanScript.FoldKBranch.here)
      #[c.sg, info.l, info.bindE, c.gamma, ct.fsE, info.τ, mkNatLit j]
    try
      return mkApp hereE (← recUnionLeaf trans info c' top descend' answers')
    catch ex =>
      if j == 0 then throw ex
      let mut lastEx := ex
      for (p, s, _) in subs do
        try
          let inner ← recUnionCases trans info c' (j - 1) top s.fvarId! descend' answers'
          let sf ← mkSelfFieldE ct.fsL p
          return mkAppN (mkConst `LeanScript.FoldKBranch.deep)
            #[c.sg, info.l, info.bindE, c.gamma, ct.fsE, info.τ, mkNatLit (j - 1), sf, inner]
        catch ex' => lastEx := ex'
      throw lastEx

end

/-- How deep a fold of a recursive tagged union the translation looks for. -/
def maxRecUnionRecDepth : Nat := 6

/-- A structural recursion on a **recursive tagged union**, as Lean compiled it: `X.brecOn`
    on a type whose tree is `Ty.recTaggedUnion`.  It becomes
    `LeanScript.Term.recTaggedUnion_rec k`, at the smallest depth `k` that serves every
    branch (see the module documentation).  `none` when the recursion is not on a
    recursive tagged union. -/
def transRecUnionBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "brecOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  unless ii.numIndices == 0 && ri.numMotives == 1 do return none
  let nP := ii.numParams
  let arity := nP + 3
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let major := args[nP + 1]!
  let sty ← tyOfTerm major
  let .recTaggedUnion l _ ← tyView sty | return none
  let params := args.extract 0 nP
  let motives := args.extract nP (nP + 1)
  let brecF := args[nP + 2]!
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
  let idxs ← recUnionCtorIndices l
  unless idxs.size == ii.ctors.length do
    throwError "`#leanscript_to_term`: internal: the tree of {ind} has {idxs.size} \
      constructors, the type {ii.ctors.length}"
  let mentions (t : Expr) : Bool := (t.find? fun s => s.isConstOf ind).isSome
  let mut ctors : Array RecUnionCtor := #[]
  for h : i in [0:ii.ctors.length] do
    let cn := ii.ctors[i]
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls) params
    let fields ← forallTelescopeReducing cty fun xs _ => do
      let mut out : Array (Option Expr) := #[]
      for x in xs do
        let t ← inferType x
        if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
        if ← LeanScript.Deriving.erasedBinder t then
          throwError "`#leanscript_to_term`: the constructor {cn} has a field the \
            language erases, which the fold of a recursive tagged union does not read"
        if ← isDefEq t selfTy then out := out.push none
        else if mentions t then
          throwError "`#leanscript_to_term`: the field of type {t} of {cn} mentions {ind} \
            other than as the type itself"
        else out := out.push (some t)
      return out
    let fsE := idxs[i]!
    let fsL := (← listOfExpr (← reduceTy fsE)).toArray
    unless fsL.size == fields.size do
      throwError "`#leanscript_to_term`: internal: {cn} has {fields.size} fields, its \
        tree {fsL.size}"
    ctors := ctors.push { name := cn, fields, fsE, fsL }
  let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
  let info : RecUnionInfo :=
    { ind, lvls := ilvls, params, selfTy, ctors, l, bindE, τLean, τ, brecF, motives }
  let .recTaggedUnion _ hwf ← tyView sty | return none
  let scrutT ← trans c major
  let attempt (k : Nat) : MetaM Expr :=
    withLocalDeclD `top selfTy fun top => do
      let cases ← recUnionCases trans info c k top top.fvarId! #[] #[]
      return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_rec)
        #[c.sg, c.gamma, τ, l, hwf, mkNatLit k, scrutT, cases]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  for k in [0:maxRecUnionRecDepth + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the recursive tagged union \
        {ind} is not the fold of a recursive tagged union at any depth up to \
        {maxRecUnionRecDepth} — the fold `recTaggedUnion_rec k` gives each branch the \
        constructor's fields and the answers at its occurrences, and may look into one \
        occurrence at a time, at most `k` times along a path, so a branch that reads \
        the value of the function further down, or looks into two subvalues at once, \
        has no term.  At the last depth tried: {lastErr.getD m!"(no error)"}"
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
