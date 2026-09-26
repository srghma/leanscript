module

public meta import LeanScript.ToTerm.TransRecFamilyPieces
public meta import LeanScript.ToTerm.Default

@[expose] public section

meta section

/-!
# The translation of a recursion on a mutual family: the case tree

`recFamCases` / `recFamBranch`, the depth-`j` dispatches that
`LeanScript.ToTerm.transRecFamilyBrecOn?` builds for each member of the family.
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
    (answers : Array (Expr × Expr)) (outer : List FamFrame) (descended : Array FVarId)
    (nested : Array FamNested) : MetaM Expr := do
  let mi := info.members[m]!
  let branches ← mi.ctors.mapM fun ct =>
    recFamBranch trans info c j topM top target descend answers outer descended nested ct
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
    (nested : Array FamNested) (ct : FamCtor) : MetaM Expr := do
  let bTys := (← listOfExpr (← reduceTy (mkApp info.bindE ct.fsE)))
  let mut decls : Array (Name × (Array Expr → MetaM Expr)) := #[]
  for h : i in [0:ct.fields.size] do
    match ct.fields[i] with
    | .plain t => decls := decls.push (Name.mkSimple s!"x{i}", fun _ => pure t)
    | .member k =>
        let st := info.members[k]!.selfTy
        decls := decls.push (Name.mkSimple s!"sub{i}", fun _ => pure st)
        decls := decls.push (Name.mkSimple s!"ans{i}", fun _ => pure info.τLean)
    | .nested t _ p =>
        -- the field, then the window of the answers at the values it holds: a Lean value
        -- for a function (of the answers) and a delay (of the answer), and otherwise a
        -- placeholder, which only the terms folding it read
        decls := decls.push (Name.mkSimple s!"x{i}", fun _ => pure t)
        let wTy : MetaM Expr := match p with
          | .fn _ dom => mkArrow dom info.τLean
          | .thunk _ => mkAppM ``Thunk #[info.τLean]
          | _ => pure (mkConst ``Unit)
        decls := decls.push (Name.mkSimple s!"win{i}", fun _ => wTy)
  unless decls.size == bTys.length do
    throwError "`#leanscript_to_term`: internal: the branch of {ct.name} binds \
      {decls.size} values, its tree {bTys.length}"
  withLocalDeclsD decls fun xs => do
    let c' := c.pushFields (xs.zip bTys.toArray |>.map fun (x, t) => (x.fvarId!, t))
    let mut vals : Array Expr := #[]
    let mut subs : Array (Nat × Nat × Expr × Expr) := #[]
    let mut nested' := nested
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
      | .nested _ k p =>
          -- a delay is given as `Thunk.mk g`, whose history Lean can take apart
          let v ← if p matches .thunk _ then famThunkShape xs[pos]! else pure xs[pos]!
          vals := vals.push v
          nested' := nested'.push
            { member := k, read := p, val := v, win := xs[pos + 1]!.fvarId!,
              winTy := bTys[pos + 1]! }
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
        (frame :: outer) descended' nested'
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
          (cands.map (·.2.2.2)) nested'))
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

end LeanScript.ToTerm

end

end
