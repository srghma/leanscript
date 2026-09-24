module

public meta import LeanScript.ToTerm.TransRecUnion

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
`LeanScript.Term.mutualRecursiveFamily_rec k`, takes the branches of every member of the
family, with one answer type `τ` for all of them, each branch binding the constructor's
fields and the answers at its occurrences of members (`TyWf.famRecBinders`), and lets a
branch **look further down**, at most `k` times along a path, into an occurrence of any
member (`LeanScript.FamilyFoldKBranch.deep`).

**How a branch is read** is what `LeanScript.ToTerm.TransRecUnion` does for a single
recursive union: the case tree of each member is built top down, the Lean branch of that
member is instantiated at the shape known so far and at the history in which the answer
at each bound subvalue is its variable, and it is reduced.  If nothing unknown is left,
that is the answer (`FamilyFoldKBranch.here`); otherwise each occurrence among the node's
fields is tried in turn as the one to look into (`FamilyFoldKBranch.deep`).

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
answer `default` (of the `Inhabited` instance of the answer type), an answer that no
branch of the translated members reads, since their Lean branches have no entry for it.

The depth is the smallest `k` (up to `maxRecFamilyRecDepth`) at which every branch is
served.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- One field of a constructor of a member of a family, as the fold reads it. -/
inductive FamField where
  /-- A field that does not mention the family, of this Lean type. -/
  | plain (ty : Expr)
  /-- A field that is a value of member `i` of the family. -/
  | member (i : Nat)
  deriving Inhabited

/-- One constructor of a member of a family, as the fold reads it. -/
structure FamCtor where
  /-- The Lean constructor. -/
  name : Name
  /-- Its fields. -/
  fields : Array FamField
  /-- The list of its field trees, as an expression of type `List (TyWfIn (n + 2))` —
      the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  deriving Inhabited

/-- One member of a family, as the fold reads it. -/
structure FamMemberInfo where
  /-- The Lean inductive. -/
  ind : Name
  /-- The Lean type of the member, at the parameters. -/
  selfTy : Expr
  /-- The member's schema, an expression of type `LeanFamMemberSchema (TyWfIn (n + 2))`. -/
  schema : Expr
  /-- The constructors, in order. -/
  ctors : Array FamCtor
  /-- The Lean branch of the `brecOn` for this member. -/
  brecF : Expr
  /-- Is the motive of this member the answer type (and not `PUnit`)? -/
  answering : Bool
  deriving Inhabited

/-- What the fold of a mutual family needs to know about it and the recursion. -/
structure RecFamInfo where
  /-- The universe levels of the inductives. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- `n`, as an expression: the family has `n + 2` members. -/
  nE : Expr
  /-- The scope of the family, `n + 2`. -/
  sc : Nat
  /-- The members, in order, as an expression of type
      `List (LeanFamMemberSchema (TyWfIn (n + 2)))`. -/
  msE : Expr
  /-- The members. -/
  members : Array FamMemberInfo
  /-- The binders of a branch, `TyWf.famRecBinders f hwf τ`. -/
  bindE : Expr
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- The motives of the `brecOn`. -/
  motives : Array Expr
  /-- The answer given by the branches of a member whose motive is `PUnit`. -/
  dflt : Option Expr

/-- The history of a structural recursion on a family, at a value whose shape is known:
    as `LeanScript.ToTerm.buildRecObjHistory`, except that the entry of **any** motive
    marked in `answering` at a bound subvalue is the variable `answers` maps it to. -/
partial def buildFamHistory (motiveVars : Array Expr) (motives : Array Expr)
    (answering : Array Bool) (answers : Array (Expr × Expr)) (placeholder : Expr) :
    MetaM Expr := do
  let real (t : Expr) : Expr := t.replaceFVars motiveVars motives
  let t ← whnf placeholder
  match t.getAppFn, t.getAppArgs with
  | .const ``PProd ls, #[a, b] =>
      let va ← buildFamHistory motiveVars motives answering answers a
      let vb ← buildFamHistory motiveVars motives answering answers b
      return mkAppN (mkConst ``PProd.mk ls) #[real a, real b, va, vb]
  | .const ``PUnit ls, #[] => return mkConst ``PUnit.unit ls
  | .fvar f, #[x] =>
      match motiveVars.findIdx? (·.fvarId! == f) with
      | some i =>
          if answering[i]! then
            for (s, ans) in answers do
              if s == x then return ans
            for (s, ans) in answers do
              if ← isDefEq s x then return ans
            mkFreshExprMVar (real t)
          else
            let rt ← whnf (real t)
            match rt with
            | .const ``PUnit ls => return mkConst ``PUnit.unit ls
            | _ => mkFreshExprMVar (real t)
      | none => mkFreshExprMVar (real t)
  | _, _ => mkFreshExprMVar (real t)

/-- The branch of the fold at a node of the case tree of member `top`'s branches: the
    Lean branch of that member instantiated at the shape found so far and at the history
    in which the answer at a bound subvalue is its variable, reduced, and translated in
    `c`.  Fails when the reduced branch still reads something the fold has not given. -/
def recFamLeaf (trans : TransFn) (info : RecFamInfo) (c : TCtx) (topM : Nat) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr)) : MetaM Expr := do
  let mi := info.members[topM]!
  unless mi.answering do
    let some d := info.dflt
      | throwError "`#leanscript_to_term`: internal: no default answer"
    -- the default of `Nat` unfolds to `Nat.zero`, which is written as the literal
    let d' ← whnf d
    if d'.isConstOf ``Nat.zero then return ← trans c (mkNatLit 0)
    return ← trans c d
  let shape := resolveShape descend top
  let answers := answers.map fun (s, a) => (resolveShape descend s, a)
  let fty ← instantiateForall (← inferType mi.brecF) #[shape]
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nP := info.params.size
  let nM := info.motives.size
  let motiveTys ← info.motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let answering := info.members.map (·.answering)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildFamHistory ms info.motives answering answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN mi.brecF #[shape, hist])
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    throwError "`#leanscript_to_term`: this recursion on a mutual family reads the value \
      of the function, or takes a value apart, further down than the fold looks at this \
      depth"
  trans c body

/-- The pointer at the `p`-th field of this list of field trees, which is an occurrence
    of member `i` of the family. -/
def mkFamMemberFieldE (info : RecFamInfo) (fsL : Array Expr) (p i : Nat) : MetaM Expr := do
  let ι := tyWfInE info.sc
  let iE := mkNatLit i
  let pred := mkAppN (mkConst ``LeanScript.IsFamilyMemberField) #[info.nE, iE]
  let mut acc : Option Expr := none
  for r in [0:p + 1] do
    let j := p - r
    let a := fsL[j]!
    let rest ← mkListLit ι (fsL.extract (j + 1) fsL.size).toList
    match acc with
    | none =>
        let h ← mkEqRefl (mkApp (mkConst ``LeanScript.Ty.familyMember) iE)
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.here) #[ι, pred, a, rest, h])
    | some inner =>
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.there) #[ι, pred, a, rest, inner])
  return acc.get!

/-- The proof that member `i` of the family is its `i`-th schema. -/
def mkFamMemberAtE (info : RecFamInfo) (i : Nat) : MetaM Expr := do
  let ms := info.members.map (·.schema)
  let elem := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (tyWfInE info.sc)
  let tail (j : Nat) : MetaM Expr := mkListLit elem (ms.extract j ms.size).toList
  let mut acc := mkAppN (mkConst ``LeanScript.FamilyMemberAt.here)
    #[info.nE, ms[i]!, ← tail (i + 1)]
  for r in [0:i] do
    let j := i - 1 - r
    acc := mkAppN (mkConst ``LeanScript.FamilyMemberAt.there)
      #[info.nE, mkNatLit (i - 1 - j), ms[j]!, ms[i]!, ← tail (j + 1), acc]
  return acc

/-- The index lists of the branches of a dispatch on this schema of `TyWfIn sc`, one per
    constructor, in order. -/
partial def famCtorIndices (sc : Nat) (l : Expr) : MetaM (Array Expr) := do
  let ι := tyWfInE sc
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

/-- The branches of a fold over the member schema `l` (of a `ctors` member), in its
    shape: `pre` are the implicit arguments every family of the case tree shares
    (signature, `n`, members, binders, context, answer type, depth). -/
partial def mkFamTUFoldKCases (sc : Nat) (pre : Array Expr) (l : Expr)
    (branches : Array Expr) : MetaM Expr := do
  let ι := tyWfInE sc
  let rest (from_ : Nat) (fsLists : List Expr) : MetaM Expr := do
    let mut acc := mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCasesRest.nil) pre
    let n := fsLists.length
    for i in [0:n] do
      let idx := n - 1 - i
      let fs := fsLists[idx]!
      let more ← mkListLit (mkApp (mkConst ``List [Level.zero]) ι) (fsLists.drop (idx + 1))
      acc := mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCasesRest.cons)
        (pre ++ #[fs, more, branches[from_ + idx]!, acc])
    return acc
  let rec cpCases (cp : Expr) (i : Nat) : MetaM Expr := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, restL]) =>
        let rs ← listOfExpr restL
        return mkAppN (mkConst `LeanScript.FamilyCtorsWithPayloadFoldKCases.here)
          (pre ++ #[fields, restL, branches[i]!, ← rest (i + 1) rs])
    | (``LeanScript.CtorsWithPayload.skip, #[_, more]) =>
        return mkAppN (mkConst `LeanScript.FamilyCtorsWithPayloadFoldKCases.skip)
          (pre ++ #[more, branches[i]!, ← cpCases more (i + 1)])
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, restL]) =>
      let rs ← listOfExpr restL
      return mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCases.payloadFirst)
        (pre ++ #[fields, next, restL, branches[0]!, branches[1]!, ← rest 2 rs])
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) =>
      return mkAppN (mkConst `LeanScript.FamilyTaggedUnionFoldKCases.skip)
        (pre ++ #[cp, branches[0]!, ← cpCases cp 1])
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

mutual

/-- The branches of a depth-`j` dispatch on member `m` of the family, bound at `target`
    (a variable of the Lean type of that member).  `topM` and `top` are the member and
    the variable the case tree started from, whose Lean branch every leaf runs. -/
partial def recFamCases (trans : TransFn) (info : RecFamInfo) (c : TCtx) (j : Nat)
    (topM : Nat) (top : Expr) (m : Nat) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) : MetaM Expr := do
  let mi := info.members[m]!
  let branches ← mi.ctors.mapM fun ct =>
    recFamBranch trans info c j topM top target descend answers ct
  let jE := mkNatLit j
  let pre : Array Expr := #[c.sg, info.nE, info.msE, info.bindE, c.gamma, info.τ, jE]
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
    by what is known at this node, and otherwise a look into one of its occurrences. -/
partial def recFamBranch (trans : TransFn) (info : RecFamInfo) (c : TCtx) (j : Nat)
    (topM : Nat) (top : Expr) (target : FVarId) (descend : Array (FVarId × Expr))
    (answers : Array (Expr × Expr)) (ct : FamCtor) : MetaM Expr := do
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
    let shape := mkAppN (mkConst ct.name info.lvls) (info.params ++ vals)
    let descend' := descend.push (target, shape)
    let answers' := answers ++ subs.map fun (_, _, s, a) => (s, a)
    let jE := mkNatLit j
    let hereE := mkAppN (mkConst `LeanScript.FamilyFoldKBranch.here)
      #[c.sg, info.nE, info.msE, info.bindE, c.gamma, ct.fsE, info.τ, jE]
    try
      return mkApp hereE (← recFamLeaf trans info c' topM top descend' answers')
    catch ex =>
      if j == 0 then throw ex
      let mut lastEx := ex
      for (p, k, s, _) in subs do
        try
          let inner ← recFamCases trans info c' (j - 1) topM top k s.fvarId! descend'
            answers'
          let field ← mkFamMemberFieldE info ct.fsL p k
          let memberAt ← mkFamMemberAtE info k
          return mkAppN (mkConst `LeanScript.FamilyFoldKBranch.deep)
            #[c.sg, info.nE, info.msE, info.bindE, c.gamma, ct.fsE, info.τ,
              mkNatLit (j - 1), mkNatLit k, info.members[k]!.schema, field, memberAt, inner]
        catch ex' => lastEx := ex'
      throw lastEx

end

/-- How deep a fold of a mutual family the translation looks for. -/
def maxRecFamilyRecDepth : Nat := 6

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
    `LeanScript.Term.mutualRecursiveFamily_rec k`, at the smallest depth `k` that serves
    every branch (see the module documentation).  `none` when the recursion is not on a
    member of a mutual family. -/
def transRecFamilyBrecOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name)
    (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  unless n.getString! == "brecOn" do return none
  let ind := n.getPrefix
  let some (.inductInfo ii) := (← getEnv).find? ind | return none
  let some (.recInfo ri) := (← getEnv).find? (ind ++ `rec) | return none
  unless ii.numIndices == 0 && ii.all.length ≥ 2 do return none
  let nP := ii.numParams
  let nM := ri.numMotives
  -- a nested inductive has motives for its auxiliary types too: not a family of its own
  unless nM == ii.all.length do return none
  let arity := nP + nM + 1 + nM
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let major := args[nP + nM]!
  let sty ← tyOfTerm major
  let .mutualRecursiveFamily nE fB hwf ← tyView sty | return none
  let sc := (← natOfExpr nE) + 2
  unless sc == ii.all.length do
    throwError "`#leanscript_to_term`: the family of {ind} has {sc} members, the mutual \
      block {ii.all.length}"
  let params := args.extract 0 nP
  let motives := args.extract nP (nP + nM)
  let brecFs := args.extract (nP + nM + 1) arity
  let selfTy ← whnf (← inferType major)
  let ilvls := selfTy.getAppFn.constLevels!
  let selfTys := ii.all.toArray.map fun j => mkAppN (mkConst j ilvls) params
  let some cur := ii.all.idxOf? ind
    | throwError "`#leanscript_to_term`: internal: {ind} is not in its own block"
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
  let τ ← tyOfType τLean
  let mut answering : Array Bool := #[]
  for m in motives do
    match ← motiveBody m with
    | some b =>
        if ← isDefEq b τLean then answering := answering.push true
        else if (← whnf b).isConstOf ``PUnit then answering := answering.push false
        else
          throwError "`#leanscript_to_term`: the members of this recursion on a mutual \
            family answer different types ({b} and {τLean}), and the fold of a family \
            has one answer type"
    | none =>
        throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
          language has no eliminator for"
  let dflt ← if answering.all id then pure none else do
    let inst ← synthInstance (← mkAppM ``Inhabited #[τLean])
    pure (some (← mkAppOptM ``Inhabited.default #[τLean, inst]))
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
  for h : j in [0:ii.all.length] do
    let jn := ii.all[j]
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
      let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams ilvls)
        params
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
      ctors := ctors.push { name := cn, fields, fsE, fsL }
    members := members.push
      { ind := jn, selfTy := selfTys[j]!, schema, ctors, brecF := brecFs[j]!,
        answering := answering[j]! }
  let bindE := mkApp3 (mkConst ``LeanScript.TyWf.famRecBinders) nE fB hwf
  let bindE := mkApp bindE τ
  let info : RecFamInfo :=
    { lvls := ilvls, params, nE, sc, msE, members, bindE, τLean, τ, motives, dflt }
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
        recFamCases trans info c k j top j top.fvarId! #[] #[]
      let restL ← mkListLit elem (schemas.extract (j + 1) schemas.size).toList
      acc := mkAppN (mkConst `LeanScript.FamilyFoldKCases.cons)
        (pre ++ #[schemas[j]!, restL, casesJ, acc])
    return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_rec)
      #[c.sg, c.gamma, τ, nE, fB, hwf, kE, scrutT, acc]
  let mut found : Option Expr := none
  let mut lastErr : Option MessageData := none
  for k in [0:maxRecFamilyRecDepth + 1] do
    if found.isNone then
      try
        found := some (← attempt k)
      catch ex =>
        lastErr := some ex.toMessageData
  let some core := found
    | throwError "`#leanscript_to_term`: this recursion on the mutual family of {ind} is \
        not the fold of a family at any depth up to {maxRecFamilyRecDepth} — the fold \
        `mutualRecursiveFamily_rec k` gives each branch the constructor's fields and the \
        answers at its occurrences, and may look into one occurrence at a time, at most \
        `k` times along a path, so a branch that reads the value of the function further \
        down, or looks into two subvalues at once, has no term.  At the last depth \
        tried: {lastErr.getD m!"(no error)"}"
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity))
    extra)

end LeanScript.ToTerm

end

end
