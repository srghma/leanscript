module

public meta import LeanScript.ToTerm.Cases
public meta import LeanScript.ToTerm.Match
public meta import LeanScript.ToTerm.Cache

@[expose] public section

meta section

/-!
# The translation: applications, dispatches and recursors

The clauses of the translation that meet a recursor, a sparse `casesOn`, or the call of an
inlinable definition.  They are written outside the `mutual` block of
`LeanScript.ToTerm.Trans`: each takes the translation itself as its first argument
`trans`, which it calls on the subexpressions it meets.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- The translation itself, as the clauses outside its `mutual` block are given it: the
    term a Lean expression translates to, in a context. -/
abbrev TransFn := TCtx → Expr → MetaM Expr

/-- Apply a translated function to the arguments it is given, dropping the ones the
    language erases (types, instances and proofs). -/
def applyArgs (trans : TransFn) (c : TCtx) (t : Expr) (fn : Expr)
    (args : Array Expr) : MetaM Expr := do
  let mut t := t
  let mut cur := fn
  for a in args do
    let fty ← whnf (← inferType cur)
    let .forallE _ d _ _ := fty
      | throwError "`#leanscript_to_term`: too many arguments for {cur}"
    let next := mkApp cur a
    if ← LeanScript.Deriving.erasedBinder d then
      cur := next
      continue
    let σ ← tyOfType d
    let τ ← tyOfTerm next
    let a' ← trans c a
    t := mkAppN (mkConst `LeanScript.Term.ap) #[c.sg, c.gamma, σ, τ, t, a']
    cur := next
  return t

/-- A branch of a dispatch: the fields it binds become the innermost variables, the
    first field at index `0`. -/
def transBranch (trans : TransFn) (c : TCtx) (minor : Expr) (ctorName : Name)
    (fieldTys : List Expr) : MetaM Expr := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let mut keep : Array Expr := #[]
    for x in xs do
      unless ← LeanScript.Deriving.erasedBinder (← inferType x) do
        keep := keep.push x
    unless keep.size == fieldTys.length do
      throwError "`#leanscript_to_term`: the branch of {ctorName} binds {keep.size} \
        values but its tree has {fieldTys.length} fields"
    let c' := c.pushFields ((keep.zip fieldTys.toArray).map fun (x, t) => (x.fvarId!, t))
    trans c' ((mkAppN minor xs).headBeta)

/-- A `match` that names only some of the constructors, as Lean compiled it: the
    auxiliary `f._sparseCasesOn_i`.  Its branches and its `else` branch are the branches
    and the default of the grammar's partial dispatch, so this is where
    `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` and
    `recTaggedUnion_casesOnWithDefault` are built.

    A type whose tree has no partial dispatch — a record, a terminal type, a one-field
    wrapper — is not handled here: the auxiliary is unfolded and the exhaustive dispatch
    is built instead, which is what `none` means. -/
def transSparseCasesOn? (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM (Option Expr) := do
  let some (arity, named) ← sparseCasesOnInfo? n | return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[0]!
  unless motive.isLambda do return none
  let major := args[1]!
  let sty ← tyOfTerm major
  -- the grammar has a partial dispatch for a sum type only
  let view ← tyView sty
  match view with
  | .enum _ | .taggedUnion _ | .recTaggedUnion _ _ => pure ()
  | _ => return none
  let .const indName _ := (← whnf (← inferType major)).getAppFn | return none
  let indInfo ← getConstInfoInduct indName
  let ctors := indInfo.ctors.toArray
  if named.length ≥ ctors.size then return none
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    tyOfType body
  -- the branches, by constructor number, and the default
  let mut minors : Array Expr := ctors.map fun _ => (Lean.mkConst ``True)
  for j in [0:named.length] do
    minors := minors.set! named[j]! args[2 + j]!
  let elseArg := args[2 + named.length]!
  let elseTy ← whnf (← inferType elseArg)
  let .forallE _ dom _ _ := elseTy | return none
  let dflt ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then
      throwError "`#leanscript_to_term`: the default branch of this `match` uses the \
        proof that the value is none of the constructors named, which the language \
        erases"
    return b
  let dfltTerm ← trans c dflt
  let scrut ← trans c major
  let kE := mkNatLit named.length
  let core ← match view with
    | .enum s =>
        let cases ← mkEnumSomeCases (transBranch trans c) c τ s named 0 minors ctors
        let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, nE])
        pure <| mkAppN (mkConst `LeanScript.Term.enum_casesOnWithDefault)
          #[c.sg, c.gamma, τ, s, kE, scrut, cases, dfltTerm, hk]
    | .taggedUnion l =>
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, kE, scrut, cases, dfltTerm, hk]
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ unfE named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, hwf, kE, scrut, cases, dfltTerm, hk]
    | _ => return none
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra)

/-- The eliminator a recursor becomes. -/
def transRecCore (trans : TransFn) (c : TCtx) (ri : RecursorVal) (τ : Expr) (minors : Array Expr)
    (major : Expr) : MetaM Expr := do
  let ind := ri.getMajorInduct

  let scrut ← trans c major
  match ind with
  | ``Nat =>
      -- the fold, or the case analysis when the branch does not use the recursive value
      let natTy ← tyOfType (mkConst ``Nat)
      let z ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 2) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[1]!.fvarId! then
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy), (xs[1]!.fvarId!, τ)]
          return mkAppN (mkConst `LeanScript.Term.nat_rec)
            #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], ← trans c' body]
        else
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy)]
          return mkAppN (mkConst `LeanScript.Term.nat_casesOn)
            #[c.sg, c.gamma, τ, scrut, z, ← trans c' body]
  | ``List =>
      let sty ← tyOfTerm major
      let .recTaggedUnion l hwf ← tyView sty
        | throwError "`#leanscript_to_term`: {major} is not a list"
      let (cp, fieldsNE, restL) ← listSchemaParts l
      -- the head of the payload is written in the scope the binder opens; as a *value*
      -- of the language it is that tree, unfolded — which for an element type that is
      -- not an occurrence is the tree itself
      let σ ← match ← nonEmptyTys fieldsNE with
        | [σ, _] => bundleTyE 0 (← treeOfTyE σ)
        | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
      let nil ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 3) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[2]!.fvarId! then
          -- the fold: the branch is given the value of the fold at the tail
          let c' := c.pushFields
            #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty), (xs[2]!.fvarId!, τ)]
          let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
          let ι := tyWfInE 1
          let depth := mkNatLit 0
          let nilFs := mkApp (mkConst ``List.nil [Level.zero]) ι
          let consFs := mkApp2
            (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
            ι fieldsNE
          -- the branches of a depth-zero fold: one answer each, none of them looking
          -- further down
          let nilBranch := mkAppN (mkConst `LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, nilFs, τ, depth, nil]
          let consBranch := mkAppN (mkConst `LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, consFs, τ, depth, ← trans c' body]
          let restCases := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.nil)
            #[c.sg, l, bindE, c.gamma, τ, depth]
          let consCases := mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.here)
            #[c.sg, l, bindE, c.gamma, τ, depth, fieldsNE, restL, consBranch, restCases]
          let cases := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.skip)
            #[c.sg, l, bindE, c.gamma, τ, depth, cp, nilBranch, consCases]
          return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_rec)
            #[c.sg, c.gamma, τ, l, hwf, depth, scrut, cases]
        else
          -- the case analysis: the branches are over the unfolded schema, in which the
          -- tail is a list again
          let (cpU, fieldsU, restU) ←
            listSchemaParts (← reduceTy
              (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf))
          let c' := c.pushFields #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty)]
          let restCases := mkAppN (mkConst `LeanScript.TaggedUnionFoldCasesRest.nil)
            #[c.sg, tyE, idBindE, c.gamma, τ]
          let consCases := mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldCases.here)
            #[c.sg, tyE, idBindE, c.gamma, τ, fieldsU, restU, ← trans c' body, restCases]
          let cases := mkAppN (mkConst `LeanScript.TaggedUnionFoldCases.skip)
            #[c.sg, tyE, idBindE, c.gamma, τ, cpU, nil, consCases]
          return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
  | ``Bool =>
      return mkAppN (mkConst `LeanScript.Term.bool_casesOn)
        #[c.sg, c.gamma, τ, scrut, ← trans c minors[1]!, ← trans c minors[0]!]
  | _ =>
      let indInfo ← getConstInfoInduct ind
      if indInfo.isRec then
        throwError "`#leanscript_to_term`: {ind} is a recursive type, and the only folds \
          the translation produces from a recursor are `nat_rec` and `recTaggedUnion_rec`, \
          for `Nat` and `List` (a structural recursion on a recursive record or a \
          recursive tagged union, a recursive newtype or a mutual block, as Lean \
          compiles it, is `recObject_rec`, `recTaggedUnion_rec`, `recAlias_rec` or \
          `mutualRecursiveFamily_rec`)"
      let sty ← tyOfTerm major
      let ctors := indInfo.ctors.toArray
      match ← tyView sty with
      | .record fs =>
          let fieldTys ← recordFieldTys fs
          let body ← transBranch trans c minors[0]! ctors[0]! fieldTys
          return mkAppN (mkConst `LeanScript.Term.record_casesOn)
            #[c.sg, c.gamma, τ, fs, scrut, body]
      | .taggedUnion l =>
          -- a `match` with a wildcard repeats one branch: that is the partial dispatch
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, lenE])
            return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOnWithDefault)
              #[c.sg, c.gamma, τ, l, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkTaggedUnionCases (transBranch trans c) c τ l 0 minors ctors
          return mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, scrut, cases]
      | .enum s =>
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkEnumSomeCases (transBranch trans c) c τ s named 0 minors ctors
            let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, nE])
            return mkAppN (mkConst `LeanScript.Term.enum_casesOnWithDefault)
              #[c.sg, c.gamma, τ, s, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkEnumCases (transBranch trans c) c τ s minors ctors
          return mkAppN (mkConst `LeanScript.Term.enum_casesOn)
            #[c.sg, c.gamma, τ, s, scrut, cases]
      | .prim _ =>
          if (← isBoolTy sty) && minors.size == 2 then
            return mkAppN (mkConst `LeanScript.Term.bool_casesOn)
              #[c.sg, c.gamma, τ, scrut, ← transBranch trans c minors[1]! ctors[1]! [],
                ← transBranch trans c minors[0]! ctors[0]! []]
          throwError "`#leanscript_to_term`: a terminal type has no dispatch of its own"
      | _ =>
          if minors.size == 1 then
            -- a one-field wrapper: its case analysis substitutes the value
            return ← transBranch trans c minors[0]! ctors[0]! [← tyOfTerm major]
          throwError "`#leanscript_to_term`: the tree of {ind} has no dispatch in the \
            grammar"

/-- An application of a recursor. -/
def transRecApp (trans : TransFn) (c : TCtx) (e : Expr) (ri : RecursorVal) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  unless ri.numMotives == 1 && ri.numIndices == 0 do
    throwError "`#leanscript_to_term`: {ri.name} is not an eliminator the language has"
  let arity := ri.numParams + 1 + ri.numMinors + 1
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[ri.numParams]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {ri.name} is not a function"
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {ri.name} is used with a dependent motive, \
        which the language has no eliminator for"
    tyOfType body
  let minors := args.extract (ri.numParams + 1) (ri.numParams + 1 + ri.numMinors)
  let major := args[ri.numParams + 1 + ri.numMinors]!
  let core ← transRecCore trans c ri τ minors major
  let extra := args.extract arity args.size
  if extra.isEmpty then return core
  applyArgs trans c core (mkAppN (mkConst ri.name lvls) (args.extract 0 arity)) extra

/-- Translate a closed definition, once: the translation is stored as a function of the
    context, and two definitions of the same shape share one tree. -/
def transClosedCached (trans : TransFn) (c : TCtx) (v : Expr) : MetaM Expr := do
  if v.hasFVar || v.hasMVar then return ← trans c v
  let st ← cacheRef.get
  if let some entry := st.entries.find? fun en => en.sg == c.sg && en.src == v then
    cacheRef.modify fun s => { s with hits := s.hits + 1 }
    return mkApp entry.fn c.gamma
  let fn ← withLocalDeclD `Γ ctxE fun g => do
    let t ← trans { c with base := g, binders := #[] } v
    mkLambdaFVars #[g] t
  let h := fn.hash
  let st ← cacheRef.get
  let shared? := st.entries.find? fun en => en.hash == h && en.fn == fn
  let fn := match shared? with | some en => en.fn | none => fn
  cacheRef.modify fun s =>
    { s with
      entries := s.entries.push { sg := c.sg, src := v, fn := fn, hash := h },
      shared := if shared?.isSome then s.shared + 1 else s.shared }
  return mkApp fn c.gamma

/-- A call of an inlinable function: its definition is translated, once, and used
    here. -/
def transInline (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let info ← getConstInfo n
  let some val := info.value? |
    throwError "`#leanscript_to_term`: `{n}` has no definition to inline"
  let val := val.instantiateLevelParams info.levelParams lvls
  -- how many leading arguments does the language erase?
  let nLeading ← forallTelescopeReducing info.type fun xs _ => do
    let mut k := 0
    for h : i in [0:xs.size] do
      if i ≥ args.size then break
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then k := k + 1 else break
    return k
  let leading := args.extract 0 nLeading
  let headVal := (mkAppN val leading).headBeta
  if headVal.hasFVar || headVal.hasMVar then
    let some e' ← unfoldHere? e
      | throwError "`#leanscript_to_term`: cannot inline `{n}`"
    return ← trans c e'
  let t ← transClosedCached trans c headVal
  applyArgs trans c t (mkAppN (mkConst n lvls) leading) (args.extract nLeading args.size)

end LeanScript.ToTerm

end

end
