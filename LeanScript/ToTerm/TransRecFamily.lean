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
  /-- The universe levels and the parameters the constructor is applied at: those of the
      block, or those of the wrapper an auxiliary type of a nested inductive is
      (`List.cons` at `Rose`). -/
  lvls : List Level := []
  /-- See `lvls`. -/
  params : Array Expr := #[]
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
  /-- Do the answering members answer different types?  Then the fold answers the tuple
      `τLean` of all of them (`PProd`, nested to the right), each member's branch fills in
      its own component and the defaults elsewhere, and an answer at an occurrence of a
      member is read as its component. -/
  tuple : Bool := false
  /-- In a tuple fold, the component of each motive (`none` for a `PUnit` one). -/
  slots : Array (Option Nat) := #[]
  /-- In a tuple fold, the component types. -/
  comps : Array Expr := #[]
  /-- In a tuple fold, the default of each component, unfolded. -/
  compDflts : Array Expr := #[]

/-- The `i`-th component of a value `x` of the right-nested tuple of `n` components. -/
def tupleProj (n i : Nat) (x : Expr) : MetaM Expr := do
  let mut cur := x
  for _ in [0:i] do cur ← mkAppM ``PProd.snd #[cur]
  if i + 1 < n then cur ← mkAppM ``PProd.fst #[cur]
  return cur

/-- The right-nested tuple of these components. -/
def tupleMk (xs : Array Expr) : MetaM Expr := do
  let mut acc := xs.back!
  for r in [1:xs.size] do
    acc ← mkAppM ``PProd.mk #[xs[xs.size - 1 - r]!, acc]
  return acc

/-- The right-nested tuple type of these types. -/
def tupleTy (ts : Array Expr) : MetaM Expr := do
  let mut acc := ts.back!
  for r in [1:ts.size] do
    acc ← mkAppM ``PProd #[ts[ts.size - 1 - r]!, acc]
  return acc

/-- The answer of member `m` read out of the fold's answer `a`. -/
def RecFamInfo.readAnswer (info : RecFamInfo) (m : Nat) (a : Expr) : MetaM Expr := do
  unless info.tuple do return a
  let some i := info.slots[m]! | return a
  tupleProj info.comps.size i a

/-- The history of a structural recursion on a family, at a value whose shape is known:
    as `LeanScript.ToTerm.buildRecObjHistory`, except that the entry of **any** motive
    marked in `answering` at a bound subvalue is the variable `answers` maps it to. -/
partial def buildFamHistory (motiveVars : Array Expr) (motives : Array Expr)
    (answering : Array Bool) (answers : Array (Expr × Expr)) (placeholder : Expr)
    (proj : Nat → Expr → MetaM Expr := fun _ a => pure a) :
    MetaM Expr := do
  let real (t : Expr) : Expr := t.replaceFVars motiveVars motives
  let t ← whnf placeholder
  match t.getAppFn, t.getAppArgs with
  | .const ``PProd ls, #[a, b] =>
      let va ← buildFamHistory motiveVars motives answering answers a proj
      let vb ← buildFamHistory motiveVars motives answering answers b proj
      return mkAppN (mkConst ``PProd.mk ls) #[real a, real b, va, vb]
  | .const ``PUnit ls, #[] => return mkConst ``PUnit.unit ls
  | .fvar f, #[x] =>
      match motiveVars.findIdx? (·.fvarId! == f) with
      | some i =>
          if answering[i]! then
            for (s, ans) in answers do
              if s == x then return ← proj i ans
            for (s, ans) in answers do
              if ← isDefEq s x then return ← proj i ans
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
    `c`.

    When the reduced branch still reads something the fold has not given — the history
    below a subvalue that has not been looked into — the result is `.inr` of those of the
    `pending` subvalues (the occurrences not yet looked into, at this node and at the
    nodes above it) whose history it reads: a deeper look into one of them is what the
    branch needs.  It fails when it reads nothing that a deeper look could give. -/
def recFamLeaf (trans : TransFn) (info : RecFamInfo) (c : TCtx) (topM : Nat) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr))
    (pending : Array FVarId) : MetaM (Expr ⊕ Array FVarId) := do
  let mi := info.members[topM]!
  unless mi.answering do
    let some d := info.dflt
      | throwError "`#leanscript_to_term`: internal: no default answer"
    -- the default is unfolded all the way — for an answer that is a function (a recursion
    -- with arguments after the value) it is `fun _ => default`, and the instance is not a
    -- value of the language — and the default of `Nat`, `Nat.zero`, is written as the
    -- literal
    let d' ← Meta.reduce d
    let d' := d'.replace fun s => if s.isConstOf ``Nat.zero then some (mkNatLit 0) else none
    return .inl (← trans c d')
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
    let h ← buildFamHistory ms info.motives answering answers placeholder info.readAnswer
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN mi.brecF #[shape, hist])
  let body ← instantiateMVars (← reduceHistoryProjs body)
  -- in a tuple fold, the member's answer is its component, the defaults elsewhere
  let body ← if info.tuple then
      match info.slots[topM]! with
      | some i => tupleMk (info.compDflts.set! i body)
      | none => pure body
    else pure body
  if body.hasExprMVar then
    -- the unknown parts of the history are the histories below the subvalues not looked
    -- into, each a metavariable whose type names its subvalue
    let mut tys : Array Expr := #[]
    for m in ← getMVars body do
      tys := tys.push (← instantiateMVars (← m.getType))
    let needed := pending.filter fun f => tys.any (·.containsFVar f)
    unless needed.isEmpty do return .inr needed
    throwError "`#leanscript_to_term`: this recursion on a mutual family reads the value \
      of the function, or takes a value apart, further down than the fold looks at this \
      depth"
  return .inl (← trans { c with foldInds := c.foldInds ++ info.members.map (·.ind) } body)

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

/-- A node of the case tree of a fold of a family that the fold has dispatched on: its
    constructor's field trees (`fsE`, with elements `fsL`) and, for each of its
    occurrences of a member, the position of the field, the member, and the variable bound
    for the subvalue there. -/
structure FamFrame where
  /-- The list of the constructor's field trees, the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- The occurrences of members among the fields: position, member and variable. -/
  subs : Array (Nat × Nat × FVarId)
  deriving Inhabited

/-- The nodes above a branch, innermost first, as the expression of type
    `List (List (TyWfIn (n + 2)))` the families of the case tree are indexed by. -/
def famOuterE (info : RecFamInfo) (outer : List FamFrame) : MetaM Expr :=
  mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE info.sc)) (outer.map (·.fsE))

/-- The pointer `LeanScript.FamilyOuterMemberField` at the occurrence `field` (of member
    `k`) of the `i`-th node above (`0` the innermost). -/
def mkFamOuterFieldE (info : RecFamInfo) (k : Nat) :
    List FamFrame → Nat → Expr → MetaM Expr
  | f :: rest, 0, field => do
      return mkAppN (mkConst ``LeanScript.FamilyOuterMemberField.here)
        #[info.nE, mkNatLit k, f.fsE, ← famOuterE info rest, field]
  | f :: rest, i + 1, field => do
      return mkAppN (mkConst ``LeanScript.FamilyOuterMemberField.there)
        #[info.nE, mkNatLit k, f.fsE, ← famOuterE info rest,
          ← mkFamOuterFieldE info k rest i field]
  | [], _, _ => throwError "`#leanscript_to_term`: internal: no node above to look into"

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
    `LeanScript.Term.mutualRecursiveFamily_rec k`, at the smallest depth `k` that serves
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
    let inst ← try synthInstance (← mkAppM ``Inhabited #[t])
      catch _ => throwError "`#leanscript_to_term`: the members of this recursion on a \
        mutual family answer different types, and the fold answers the tuple of them, \
        filled in with defaults; {t} has no `Inhabited` instance"
    let d ← Meta.reduce (← mkAppOptM ``Inhabited.default #[t, inst])
    return d.replace fun s => if s.isConstOf ``Nat.zero then some (mkNatLit 0) else none
  let compDflts ← if uniform then pure #[] else comps.mapM unfoldDefault
  let τLeanCur := τLean
  let τLean ← if uniform then pure τLean else tupleTy comps
  let τ ← tyOfType τLean
  let dflt ← if answering.all id then pure none
    else if uniform then do
      let inst ← synthInstance (← mkAppM ``Inhabited #[τLean])
      pure (some (← mkAppOptM ``Inhabited.default #[τLean, inst]))
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
    return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_rec)
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
