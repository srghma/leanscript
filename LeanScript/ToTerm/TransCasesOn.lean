module

public meta import LeanScript.ToTerm.Cases
public meta import LeanScript.ToTerm.Match
public meta import LeanScript.ToTerm.Cache
public meta import LeanScript.ToTerm.Brec

@[expose] public section

meta section

/-!
# The translation: applied branches and sparse `casesOn`

`TransFn` (the translation, as the clauses outside the `mutual` block of
`LeanScript.ToTerm.Trans` are given it), the application of a translated branch to its
fields, and the clause for a sparse `casesOn` and a one-field wrapper's case analysis.
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

/-- The member a family selects, with its fields unfolded in the scope of the whole
    family: the index of `mutualRecursiveFamily_mk`, `…_casesOn` and
    `…_casesOnWithDefault`. -/
def famCurrentUnfolded (nE f hwf : Expr) : MetaM Expr := do
  let sc := (← natOfExpr nE) + 2
  let curE := mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.current) (tyWfInE sc) f
  reduceTy (mkAppN (mkConst ``LeanScript.LeanFamMemberSchema.map)
    #[tyWfInE sc, tyE, mkApp3 (mkConst ``LeanScript.TyWfIn.unfoldFam) nE f hwf, curE])

/-- A `_sparseCasesOn_` auxiliary written as the exhaustive `casesOn` it stands for: the
    named constructors keep their branches, every other one takes the `else` branch (when
    that branch does not use the proof that the value is none of the named constructors,
    which the language erases).  Used for a type with no partial dispatch of its own. -/
def sparseAsCasesOn? (n : Name) (args : Array Expr) :
    MetaM (Option Expr) := do
  let some (arity, named, p) ← sparseCasesOnInfo? n | return none
  if args.size < arity then return none
  let motive := args[p]!
  let major := args[p + 1]!
  let mty ← whnf (← inferType major)
  let .const indName indLvls := mty.getAppFn | return none
  let some (.inductInfo ii) := (← getEnv).find? indName | return none
  unless ii.numIndices == 0 do return none
  let ctors := ii.ctors.toArray
  if named.length ≥ ctors.size then return none
  unless (← getEnv).contains (indName ++ `casesOn) do return none
  let motiveLvl ← do
    let mt ← whnf (← inferType motive)
    let .forallE _ _ b _ := mt | return none
    let .sort u := (← whnf b) | return none
    pure u
  let elseArg := args[p + 2 + named.length]!
  let .forallE _ dom _ _ ← whnf (← inferType elseArg) | return none
  let dflt? ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then return none
    return some b
  let some dflt := dflt? | return none
  let params := mty.getAppArgs
  let casesOn := mkAppN (mkConst (indName ++ `casesOn) (motiveLvl :: indLvls))
    (params ++ #[motive, major])
  let mut cur := casesOn
  for i in [0:ctors.size] do
    let minor ← match named.idxOf? i with
      | some j => pure args[p + 2 + j]!
      | none => do
          let .forallE _ d _ _ ← whnf (← inferType cur)
            | throwError "`#leanscript_to_term`: internal: {indName}.casesOn takes too few \
                branches"
          forallTelescopeReducing d fun xs _ => mkLambdaFVars xs dflt
    cur := mkApp cur minor
  let extra := args.extract arity args.size
  return some (mkAppN cur extra)

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
  let some (arity, named, p) ← sparseCasesOnInfo? n | return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[p]!
  unless motive.isLambda do return none
  let major := args[p + 1]!
  let sty ← tyOfTerm major
  -- the grammar has a partial dispatch for a sum type only
  let view ← tyView sty
  match view with
  | .enum _ | .taggedUnion _ | .recTaggedUnion _ _ | .mutualRecursiveFamily _ _ _ => pure ()
  | _ => return none
  let .const indName _ := (← whnf (← inferType major)).getAppFn | return none
  -- inside the branches of a fold of a family, taking one of its values apart is the
  -- fold's look further down (see `TCtx.foldInds`)
  if view matches .mutualRecursiveFamily .. then
    if c.foldInds.contains indName then return none
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
    minors := minors.set! named[j]! args[p + 2 + j]!
  let elseArg := args[p + 2 + named.length]!
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
        pure <| mkAppN (mkConst `LeanScript.Term.enum_casesOnWithDefault')
          #[c.sg, c.gamma, τ, s, kE, scrut, cases, dfltTerm, hk]
    | .taggedUnion l =>
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.taggedUnion_casesOnWithDefault')
          #[c.sg, c.gamma, τ, l, kE, scrut, cases, dfltTerm, hk]
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ unfE named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst `LeanScript.Term.recTaggedUnion_casesOnWithDefault')
          #[c.sg, c.gamma, τ, l, hwf, kE, scrut, cases, dfltTerm, hk]
    | .mutualRecursiveFamily nE f hwf =>
        -- only a member with constructors can be dispatched on partially
        let (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) :=
            (← famCurrentUnfolded nE f hwf).getAppFnArgs
          | return none
        let cases ← mkTaggedUnionSomeCases (transBranch trans c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        let someCases := mkAppN (mkConst `LeanScript.FamilyMemberSomeCases.ctors)
          #[c.sg, c.gamma, τ, jnilE, l, kE, cases, hk]
        pure <| mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_casesOnWithDefault')
          #[c.sg, c.gamma, τ, nE, f, hwf, scrut, someCases, dfltTerm]
    | _ => return none
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra)

/-- The case analysis of a value of a **structure the language models by its one kept
    field** (a subtype `{x // p x}`, whose proof is erased): the branch, applied to the
    projections of the value, which is bound once by a `let` unless it is a variable.
    `none` when the type has more than one constructor. -/
def wrapperCasesAsProjs? (major : Expr) (minors : Array Expr) (ctors : Array Name) :
    MetaM (Option Expr) := do
  unless minors.size == 1 && ctors.size == 1 do return none
  let ci ← getConstInfoCtor ctors[0]!
  unless ci.numFields > 0 do return none
  let build (v : Expr) : Expr :=
    (mkAppN minors[0]! ((List.range ci.numFields).toArray.map fun i =>
      Expr.proj ci.induct i v)).headBeta
  if major.consumeMData.isFVar then return some (build major)
  withLetDecl `s (← inferType major) major fun s => do
    return some (← mkLetFVars #[s] (build s))

end LeanScript.ToTerm

end

end
