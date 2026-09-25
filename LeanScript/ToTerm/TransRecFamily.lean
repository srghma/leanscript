module

public meta import LeanScript.ToTerm.TransRecFamilyPieces
public meta import LeanScript.ToTerm.Default

@[expose] public section

meta section

/-!
# The translation: a structural recursion on a mutual recursive family

`transRecFamilyBrecOn?`, the clause of the translation for a structural recursion on the
members of a **mutual inductive block**, such as

```lean
mutual
  inductive A where
    | stop
    | next (label : Nat) (b : B)
  inductive B where
    | stop
    | next (label : Nat) (a : A)
end
```

whose trees are `Ty.mutualRecursiveFamily` (one per member, each selecting itself).

Lean compiles a (mutual) structural recursion on such a block into `A.brecOn` (or
`B.brecOn`), which takes one motive and one branch **per member** and hands each branch
the whole history of the recursion.  The grammar's fold,
`LeanScript.Term.mutualRecursiveFamily_rec' k`, takes the branches of every member of the
family, with one answer type `τ` for all of them, each branch binding the constructor's
fields and the answers at its occurrences of members (`TyWf.famRecBinders`), and lets a
branch **look further down**, at most `k` times, into an occurrence of any member: one of
the node it stands at (`LeanScript.FamilyFoldKBranch.deep`), or one it has not looked into
yet at a node above it on the path (`LeanScript.FamilyFoldKBranch.deepOuter`).

**How a branch is read** is what `LeanScript.ToTerm.TransRecUnion` does for a single
recursive union: the case tree of each member is built top down, the Lean branch of that
member is instantiated at the shape known so far and at the history in which the answer
at each bound subvalue is its variable, and it is reduced.  If nothing unknown is left,
that is the answer (`FamilyFoldKBranch.here`).  Otherwise the unknown parts are the
histories below subvalues not looked into yet, each a metavariable whose type names its
subvalue; when the depth allows it, each of those subvalues is tried in turn as the one to
look into — at this node (`FamilyFoldKBranch.deep`) or at a node above
(`FamilyFoldKBranch.deepOuter`), those furthest up first.  So a recursion that reads the
answers at the grandchildren below **both** children of a binary node looks into the left
child and then, from there, into the right one: depth `2`.

**The answer type.**  Every member whose motive is a function to the answer type has its
branch translated.  A member whose motive is `PUnit` — Lean's choice when a recursion on
one member only passes *through* another, as in

```lean
def A.len : A → Nat
  | .stop => 0
  | .next _ .stop => 1
  | .next _ (.next _ a) => a.len + 2
```

— has no Lean branch to translate, and the fold still needs one for it; its branches
answer a default (of the `Inhabited` instance of the answer type, or else a value built
from its constructors, `LeanScript.ToTerm.synthDefault?`), an answer that no
branch of the translated members reads, since their Lean branches have no entry for it.

The depth is the smallest `k` (up to `maxRecFamilyRecDepth`) at which every branch is
served.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

mutual

/-- The branches of a depth-`j` dispatch on member `m` of the family, bound at `target`
    (a variable of the Lean type of that member), below the nodes `outer` (innermost
    first); `descended` are the subvalues already looked into.  `topM` and `top` are the
    member and the variable the case tree started from, whose Lean branch every leaf
    runs. -/
partial def recFamCases (trans : TransFn) (info : RecFamInfo) (c : TCtx) (j : Nat)
    (topM : Nat) (top : Expr) (m : Nat) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (outer : List FamFrame) (descended : Array FVarId) :
    MetaM Expr := do
  let mi := info.members[m]!
  let branches ← mi.ctors.mapM fun ct =>
    recFamBranch trans info c j topM top target descend answers outer descended ct
  let jE := mkNatLit j
  let pre : Array Expr :=
    #[c.sg, info.nE, info.msE, info.bindE, c.gamma, info.τ, jE, ← famOuterE info outer]
  match (← whnf mi.schema).getAppFnArgs with
  | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
      let cases ← mkFamTUFoldKCases info.sc pre l branches
      return mkAppN (mkConst `LeanScript.FamilyMemberFoldKCases.ctors) (pre ++ #[l, cases])
  | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
      return mkAppN (mkConst `LeanScript.FamilyMemberFoldKCases.record)
        (pre ++ #[fs, branches[0]!])
  | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
      return mkAppN (mkConst `LeanScript.FamilyMemberFoldKCases.alias)
        (pre ++ #[b, branches[0]!])
  | _ => throwError "`#leanscript_to_term`: internal: not a member of a family: \
      {mi.schema}"

/-- The branch of one constructor, at depth `j`: the answer, if the Lean branch is served
    by what is known at this node, and otherwise a look into an occurrence whose history
    it reads — one of this node's (`FamilyFoldKBranch.deep`) or one of a node above
    (`FamilyFoldKBranch.deepOuter`). -/
partial def recFamBranch (trans : TransFn) (info : RecFamInfo) (c : TCtx) (j : Nat)
    (topM : Nat) (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (outer : List FamFrame) (descended : Array FVarId)
    (ct : FamCtor) : MetaM Expr := do
  let bTys := (← listOfExpr (← reduceTy (mkApp info.bindE ct.fsE)))
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for h : i in [0:ct.fields.size] do
    match ct.fields[i] with
    | .plain t => decls := decls.push (Name.mkSimple s!"x{i}", fun _ => pure t)
    | .member k =>
        let st := info.members[k]!.selfTy
        decls := decls.push (Name.mkSimple s!"sub{i}", fun _ => pure st)
        decls := decls.push (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
  unless decls.size == bTys.length do
    throwError "`#leanscript_to_term`: internal: the branch of {ct.name} binds \
      {decls.size} values, its tree {bTys.length}"
  withLocalDeclsD decls fun xs => do
    let c' := c.pushFields (xs.zip bTys.toArray |>.map fun (x, t) => (x.fvarId!, t))
    let mut vals : Array Expr := #[]
    let mut subs : Array (Nat × Nat × Expr × Expr) := #[]
    let mut pos := 0
    for h : i in [0:ct.fields.size] do
      match ct.fields[i] with
      | .plain _ =>
          vals := vals.push xs[pos]!
          pos := pos + 1
      | .member k =>
          vals := vals.push xs[pos]!
          subs := subs.push (i, k, xs[pos]!, xs[pos + 1]!)
          pos := pos + 2
    let shape := mkAppN (mkConst ct.name ct.lvls) (ct.params ++ vals)
    let descend' := descend.push (target, shape)
    let answers' := answers ++ subs.map fun (_, _, s, a) => (s, a)
    let descended' := descended.push target
    let frame : FamFrame :=
      { fsE := ct.fsE, fsL := ct.fsL,
        subs := subs.map fun (p, k, s, _) => (p, k, s.fvarId!) }
    -- the occurrences not yet looked into: those of the nodes above (`some i`, the
    -- `i`-th innermost), outermost first, then this node's (`none`)
    let mut cands : Array (Option Nat × Nat × Nat × FVarId) := #[]
    for h : r in [0:outer.length] do
      let i := outer.length - 1 - r
      for (p, k, f) in outer[i]!.subs do
        unless descended'.contains f do
          cands := cands.push (some i, p, k, f)
    for (p, k, f) in frame.subs do
      cands := cands.push (none, p, k, f)
    let outerE ← famOuterE info outer
    let jE := mkNatLit j
    let hereE := mkAppN (mkConst `LeanScript.FamilyFoldKBranch.here)
      #[c.sg, info.nE, info.msE, info.bindE, c.gamma, ct.fsE, info.τ, jE, outerE]
    -- a look into the occurrence `cand`, whose nested dispatch is at depth `j - 1`
    let look (cand : Option Nat × Nat × Nat × FVarId) : MetaM Expr := do
      let (where_, p, k, f) := cand
      let inner ← recFamCases trans info c' (j - 1) topM top k f descend' answers'
        (frame :: outer) descended'
      let memberAt ← mkFamMemberAtE info k
      let pre := #[c.sg, info.nE, info.msE, info.bindE, c.gamma, ct.fsE, info.τ,
        mkNatLit (j - 1), mkNatLit k, info.members[k]!.schema, outerE]
      match where_ with
      | none =>
          let field ← mkFamMemberFieldE info ct.fsL p k
          return mkAppN (mkConst `LeanScript.FamilyFoldKBranch.deep)
            (pre ++ #[field, memberAt, inner])
      | some i =>
          let field ← mkFamMemberFieldE info outer[i]!.fsL p k
          let ofield ← mkFamOuterFieldE info k outer i field
          return mkAppN (mkConst `LeanScript.FamilyFoldKBranch.deepOuter)
            (pre ++ #[ofield, memberAt, inner])
    let res ← try
        pure (Except.ok (← recFamLeaf trans info c' topM top descend' answers'
          (cands.map (·.2.2.2))))
      catch ex => pure (Except.error ex)
    match res with
    | .ok (.inl body) => return mkApp hereE body
    | .ok (.inr needed) =>
        -- the branch reads the history below the subvalues `needed`: each of them is
        -- tried in turn as the one to look into, those of the nodes furthest up first
        if j == 0 then
          throwError "`#leanscript_to_term`: this recursion on a mutual family reads the \
            value of the function further down than the fold looks at this depth"
        let mut lastEx : Option Exception := none
        for cand in cands do
          if needed.contains cand.2.2.2 then
            try
              return ← look cand
            catch ex' => lastEx := some ex'
        match lastEx with
        | some ex' => throw ex'
        | none => throwError "`#leanscript_to_term`: internal: no occurrence to look into"
    | .error ex =>
        -- nothing below is read, but the branch is not translated as it stands: looking
        -- into one of this node's occurrences may still expose what it takes apart
        if j == 0 then throw ex
        let mut lastEx := ex
        for cand in cands do
          if cand.1.isNone then
            try
              return ← look cand
            catch ex' => lastEx := ex'
        throw lastEx

end

/-- How deep a fold of a mutual family the translation looks for: the option
    `leanscript.toTerm.maxRecFamilyRecDepth` (`16` by default). -/
def maxRecFamilyRecDepth : MetaM Nat :=
  return leanscript.toTerm.maxRecFamilyRecDepth.get (← getOptions)

/-- The field trees of each constructor of a member schema, as index expressions. -/
def famMemberCtorIndices (sc : Nat) (schema : Expr) : MetaM (Array Expr) := do
  let ι := tyWfInE sc
  match (← whnf schema).getAppFnArgs with
  | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) => famCtorIndices sc l
  | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
      return #[mkApp2 (mkConst ``LeanScript.LeanRecordSchema.toList) ι fs]
  | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
      return #[← mkListLit ι [b]]
  | _ => throwError "`#leanscript_to_term`: internal: not a member of a family: {schema}"

/-- A structural recursion on a **mutual inductive block**, as Lean compiled it:
    `X.brecOn` on a member whose tree is `Ty.mutualRecursiveFamily`.  It becomes
    `LeanScript.Term.mutualRecursiveFamily_rec' k`, at the smallest depth `k` that serves
    every branch (see the module documentation).  `none` when the recursion is not on a
    member of a mutual family. -/
def transRecFamilyBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  -- `X.brecOn`, or `X.brecOn_i` for the `i`-th auxiliary type of a nested inductive
  unless n.isStr && (n.getString! == "brecOn" || n.getString!.startsWith "brecOn_") do
    return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  let nP := ii.numParams
  let nM := ri.numMotives
  -- a mutual block, or a nested inductive (whose auxiliary types, `List T`, are members of
  -- its family too)
  unless ii.numIndices == 0 && nM ≥ 2 do return none
  let arity := nP + nM + 1 + nM
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let major := args[nP + nM]!
  let sty ← tyOfTerm major
  let .mutualRecursiveFamily nE fB hwf ← tyView sty | return none
  let sc := (← natOfExpr nE) + 2
  unless sc == nM do
    throwError "`#leanscript_to_term`: the family of {ind} has {sc} members, its \
      recursor {nM} motives (a nested occurrence under a wrapper whose model is not \
      recursive, `Option`, say, has a motive of its own but no member)"
  let params := args.extract 0 nP
  let motives := args.extract nP (nP + nM)
  let brecFs := args.extract (nP + nM + 1) arity
  let selfTy ← whnf (← inferType major)
  -- the levels of the block: those of `brecOn`, but the one of its motive
  let ilvls := if lvls.length == ii.levelParams.length + 1 then lvls.tail else lvls
  -- the members' Lean types, in the order of the motives: the declared members, then the
  -- auxiliary types of a nested inductive
  let recLvls := if ri.levelParams.length == ii.levelParams.length + 1 then
    Level.one :: ilvls else ilvls
  let recTy ← instantiateForall (ri.type.instantiateLevelParams ri.levelParams recLvls)
    params
  let selfTys ← forallBoundedTelescope recTy nM fun ms _ => ms.mapM fun m => do
    let .forallE _ d _ _ ← whnf (← inferType m)
      | throwError "`#leanscript_to_term`: internal: a motive of {ind} is not a function"
    if d.hasAnyFVar (fun f => ms.any (·.fvarId! == f)) then
      throwError "`#leanscript_to_term`: internal: a motive of {ind} depends on another"
    return d
  let mut cur? : Option Nat := none
  for h : j in [0:selfTys.size] do
    if cur?.isNone then
      if ← isDefEq selfTy selfTys[j] then cur? := some j
  let some cur := cur?
    | throwError "`#leanscript_to_term`: internal: {selfTy} is not a member of the family \
        of {ind}"
  -- the answer type: the motive of the member the recursion returns a value of
  let motiveBody (m : Expr) : MetaM (Option Expr) := do
    let m ← whnf m
    unless m.isLambda do return none
    lambdaBoundedTelescope m 1 fun xs body => do
      let body ← whnf body
      if body.containsFVar xs[0]!.fvarId! then return none
      return some body
  let some τLean ← motiveBody motives[cur]!
    | throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
  let mut answering : Array Bool := #[]
  let mut bodies : Array Expr := #[]
  let mut uniform := true
  for m in motives do
    match ← motiveBody m with
    | some b =>
        bodies := bodies.push b
        if ← isDefEq b τLean then answering := answering.push true
        else if (← whnf b).isConstOf ``PUnit then answering := answering.push false
        else
          answering := answering.push true
          uniform := false
    | none =>
        throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
          language has no eliminator for"
  -- members answering different types: the fold answers the tuple of all of them
  let mut slots : Array (Option Nat) := #[]
  let mut comps : Array Expr := #[]
  for h : j in [0:bodies.size] do
    if answering[j]! then
      slots := slots.push (some comps.size)
      comps := comps.push bodies[j]
    else slots := slots.push none
  let unfoldDefault (t : Expr) : MetaM Expr := do
    let some d0 ← synthDefault? t
      | throwError "`#leanscript_to_term`: the members of this recursion on a \
        mutual family answer different types, and the fold answers the tuple of them, \
        filled in with defaults; {t} has no `Inhabited` instance, and no constructor \
        whose fields all have a default"
    let d ← Meta.reduce d0
    return d.replace fun s => if s.isConstOf ``Nat.zero then some (mkNatLit 0) else none
  let compDflts ← if uniform then pure #[] else comps.mapM unfoldDefault
  let τLeanCur := τLean
  let τLean ← if uniform then pure τLean else tupleTy comps
  let τ ← tyOfType τLean
  let dflt ← if answering.all id then pure none
    else if uniform then do
      let some d ← synthDefault? τLean
        | throwError "`#leanscript_to_term`: the fold of this recursion on a mutual family \
          fills the members it does not answer at with a default; {τLean} has no \
          `Inhabited` instance, and no constructor whose fields all have a default"
      pure (some d)
    else pure (some (← tupleMk compDflts))
  -- the members' schemas, in order
  let msE ← reduceTy (mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.members)
    (tyWfInE sc) fB)
  let schemas := (← listOfExpr msE).toArray
  let mentionsIdx (t : Expr) : MetaM (Option Nat) := do
    for h : j in [0:selfTys.size] do
      if ← isDefEq t selfTys[j] then return some j
    return none
  let mentions (t : Expr) : Bool :=
    (t.find? fun s => match s with | .const k _ => ii.all.contains k | _ => false).isSome
  let mut members : Array FamMemberInfo := #[]
  for h : j in [0:selfTys.size] do
    let jTy := selfTys[j]
    let .const jn jlvls := jTy.getAppFn
      | throwError "`#leanscript_to_term`: internal: member {jTy} of the family of {ind} \
          is not an inductive type"
    let jparams := jTy.getAppArgs
    let ji ← getConstInfoInduct jn
    let schema := schemas[j]!
    let idxs ← famMemberCtorIndices sc schema
    unless idxs.size == ji.ctors.length do
      throwError "`#leanscript_to_term`: internal: the tree of {jn} has {idxs.size} \
        constructors, the type {ji.ctors.length}"
    let mut ctors : Array FamCtor := #[]
    for h : i in [0:ji.ctors.length] do
      let cn := ji.ctors[i]
      let ci ← getConstInfoCtor cn
      let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams jlvls)
        jparams
      let fields ← forallTelescopeReducing cty fun xs _ => do
        let mut out : Array FamField := #[]
        for x in xs do
          let t ← inferType x
          if t.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
            throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
          if ← LeanScript.Deriving.erasedBinder t then
            throwError "`#leanscript_to_term`: the constructor {cn} has a field the \
              language erases, which the fold of a family does not read"
          if let some k ← mentionsIdx t then out := out.push (.member k)
          else if mentions t then
            throwError "`#leanscript_to_term`: the field of type {t} of {cn} mentions the \
              mutual block other than as one of its members"
          else out := out.push (.plain t)
        return out
      let fsE := idxs[i]!
      let fsL := (← listOfExpr (← reduceTy fsE)).toArray
      unless fsL.size == fields.size do
        throwError "`#leanscript_to_term`: internal: {cn} has {fields.size} fields, its \
          tree {fsL.size}"
      ctors := ctors.push { name := cn, fields, fsE, fsL, lvls := jlvls, params := jparams }
    members := members.push
      { ind := jn, selfTy := selfTys[j]!, schema, ctors, brecF := brecFs[j]!,
        answering := answering[j]! }
  let bindE := mkApp3 (mkConst ``LeanScript.TyWf.famRecBinders) nE fB hwf
  let bindE := mkApp bindE τ
  let info : RecFamInfo :=
    { lvls := ilvls, params, nE, sc, msE, members, bindE, τLean, τ, motives, dflt,
      tuple := !uniform, slots, comps, compDflts }
  let scrutT ← trans c major
  let elem := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (tyWfInE sc)
  let attempt (k : Nat) : MetaM Expr := do
    let kE := mkNatLit k
    let pre : Array Expr := #[c.sg, nE, msE, bindE, c.gamma, τ, kE]
    let mut acc := mkAppN (mkConst `LeanScript.FamilyFoldKCases.nil) pre
    for r in [0:schemas.size] do
      let j := schemas.size - 1 - r
      let mj := members[j]!
      let casesJ ← withLocalDeclD `top mj.selfTy fun top =>
        recFamCases trans info c k j top j top.fvarId! #[] #[] [] #[]
      let restL ← mkListLit elem (schemas.extract (j + 1) schemas.size).toList
      acc := mkAppN (mkConst `LeanScript.FamilyFoldKCases.cons)
        (pre ++ #[schemas[j]!, restL, casesJ, acc])
    return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_rec')
      #[c.sg, c.gamma, τ, nE, fB, hwf, kE, scrutT, acc]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  let maxK ← maxRecFamilyRecDepth
  for k in [0:maxK + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the mutual family of {ind} is \
        not the fold of a family at any depth up to {maxK} (the option \
        `leanscript.toTerm.maxRecFamilyRecDepth`) — the fold \
        `mutualRecursiveFamily_rec k` gives each branch the constructor's fields and the \
        answers at its occurrences, and may look into an occurrence of the node or of a \
        node above it, at most `k` times in all, so a branch that reads the value of the \
        function further down than that has no term.  At the last depth \
        tried: {lastErr.getD m!"(no error)"}"
  -- a tuple fold: the answer of the member recursed on is its component
  let core ← if uniform then pure core else do
    let some i := slots[cur]!
      | throwError "`#leanscript_to_term`: internal: the member recursed on does not answer"
    let projFn ← withLocalDeclD `t τLean fun t => do
      mkLambdaFVars #[t] (← tupleProj comps.size i t)
    let pT ← trans c projFn
    pure (mkAppN (mkConst `LeanScript.Term.ap) #[c.sg, c.gamma, τ, ← tyOfType τLeanCur, pT, core])
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
