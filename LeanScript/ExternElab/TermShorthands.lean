module

public meta import Lean.Elab.Command

public section

/-!
# `derive_extern_term_shorthands`: one term former per entry of the extern catalogue

`derive_extern_term_shorthands PExpr` adds, for every shorthand `LeanInitPureExtern.c` of an
entry of the catalogue (`LeanScript.LeanInitPureExternShorthands`), the definition
`PExpr.c`: the call of the extern `c` on pure expressions of the types of its arguments,

```
@[match_pattern, reducible] def PExpr.c {ks} {Δ : DSig ks} {Γ : Ctx ks} (fields of c)
    (a1 : PExpr Δ Γ σ₁) … (an : PExpr Δ Γ σₙ) : PExpr Δ Γ τ :=
  .neu (.extern (.c fields) (.cons a1 (… (.cons an .nil))))
```

so `PExpr.lean_string_any (.lit .string "12345") f` is a call of `String.Internal.any`.
`derive_extern_term_shorthands Neu` adds the same definitions in the namespace `Neu` (without
the `.neu`), for the places that take a neutral expression (the condition of `Term.ite`).
The fields of `c` are its type arguments (`αt`), the types `σᵢ` and `τ` are those of the
entry at the instantiation of the catalogue to the types of the language
(`LeanScript.Extern`), with the coercions of the catalogue unfolded (`Ty.prim .nat`, not
`↑LeanPrimTy.nat`).
-/

namespace LeanScript

open Lean Meta Elab Command

/-- Unfold the coercions and the type formers passed to the catalogue in a type of the
    language (`↑LeanPrimTy.nat` is `Ty.prim .nat`). -/
meta def normExternTy (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isAppOf ``Coe.coe || e.getAppFn.isLambda then
      return .visit (← whnf e)
    return .continue)

/-- The elements of a list literal (up to `whnf`). -/
meta partial def externListElems (e : Expr) : MetaM (Array Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return #[e.appFn!.appArg!] ++ (← externListElems e.appArg!)
  if e.isAppOfArity ``List.nil 1 then
    return #[]
  throwError "`derive_extern_term_shorthands`: not a list literal{indentExpr e}"

/-- Add the term former `target.c` (`target` is `PExpr` or `Neu`) of the shorthand `sc`
    (`LeanInitPureExtern.c`). -/
meta def addExternTermShorthand (target sc : Name) : MetaM Unit := do
  let info ← getConstInfo sc
  let name := target ++ Name.mkSimple sc.getString!
  let names := binderNamesOf info.type
  withLocalDecl `ks .implicit (mkApp (mkConst ``List [0]) (mkConst ``Nat)) fun ks => do
  withLocalDecl `Δ .implicit (mkApp (mkConst `LeanScript.DSig) ks) fun Δ => do
  withLocalDecl `Γ .implicit (mkApp (mkConst `LeanScript.Ctx) ks) fun Γ => do
    let (xs, _, ty) ← forallMetaTelescope info.type
    let tyTy := mkApp2 (mkConst `LeanScript.Ty) ks (mkConst ``Bool.true)
    let σs ← mkFreshExprMVar (mkApp (mkConst ``List [0]) tyTy)
    let τ ← mkFreshExprMVar tyTy
    unless ← isDefEq ty (mkApp3 (mkConst `LeanScript.Extern) ks σs τ) do
      throwError "`derive_extern_term_shorthands`: `{.ofConstName sc}` is not an extern"
    -- the fields of the entry: the binders left undetermined, explicitly
    let mut pending : Array (Name × MVarId) := #[]
    for i in [0:xs.size] do
      if let .mvar m ← instantiateMVars xs[i]! then
        unless pending.any (·.2 == m) do
          pending := pending.push (names[i]!, m)
    let rec go (k : Nat) (fvs : Array Expr) : MetaM Unit := do
      if h : k < pending.size then
        let (n, m) := pending[k]
        let ty ← instantiateMVars (← m.getType)
        withLocalDeclD n ty fun x => do
          m.assign x
          go (k + 1) (fvs.push x)
      else
        let σs ← instantiateMVars σs
        let τ ← normExternTy (← instantiateMVars τ)
        let e ← instantiateMVars (mkAppN (mkConst sc) xs)
        let elems ← externListElems σs
        let argTys ← elems.mapM fun σ => do
          return mkApp4 (mkConst `LeanScript.PExpr) ks Δ Γ (← normExternTy σ)
        let argDecls := argTys.mapIdx fun i t => (Name.mkSimple s!"a{i + 1}", t)
        withLocalDeclsDND argDecls fun as => do
          -- `.cons a1 (… (.cons an .nil))`, at the types of the entry
          let mut args := mkApp3 (mkConst `LeanScript.Args.nil) ks Δ Γ
          let mut tail : Expr := mkApp (mkConst ``List.nil [0]) tyTy
          for i in (List.range as.size).reverse do
            args := mkAppN (mkConst `LeanScript.Args.cons) #[ks, Δ, Γ, elems[i]!, tail, as[i]!, args]
            tail := mkApp3 (mkConst ``List.cons [0]) tyTy elems[i]! tail
          let neu := mkAppN (mkConst `LeanScript.Neu.extern) #[ks, Δ, Γ, σs, τ, e, args]
          let (body, resTy) :=
            if target == `LeanScript.Neu then (neu, mkApp4 (mkConst `LeanScript.Neu) ks Δ Γ τ)
            else (mkApp5 (mkConst `LeanScript.PExpr.neu) ks Δ Γ τ neu,
              mkApp4 (mkConst `LeanScript.PExpr) ks Δ Γ τ)
          let bs := #[ks, Δ, Γ] ++ fvs ++ as
          let value ← mkLambdaFVars bs body
          let type ← mkForallFVars bs resTy
          let decl := Declaration.defnDecl
            { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
          withExporting do
            addDecl decl
            setReducibleAttribute name
            matchPatternAttr.setTag name
            addDocStringCore name s!"A call of the extern `{sc.getString!}` \
              (`{sc}`), as a {if target == `LeanScript.Neu then "neutral" else "pure"} \
              expression."
          compileDecl decl
    go 0 #[]
where
  binderNamesOf : Expr → Array Name
    | .forallE n _ b _ => #[n] ++ binderNamesOf b
    | _ => #[]

/-- `derive_extern_term_shorthands PExpr` (or `Neu`): for every entry `c` of the catalogue of
    externs, the term former `PExpr.c` of the call of `c` on pure expressions (see the module
    doc). -/
syntax (name := deriveExternTermShorthands) "derive_extern_term_shorthands " ident : command

@[command_elab deriveExternTermShorthands]
meta def elabDeriveExternTermShorthands : CommandElab
  | `(derive_extern_term_shorthands $id) => liftTermElabM do
      let target ← realizeGlobalConstNoOverloadWithInfo id
      let outer := `LeanScript.LeanInitPureExtern
      let outerInfo ← getConstInfoInduct outer
      for wrap in outerInfo.ctors do
        let wrapInfo ← getConstInfoCtor wrap
        let fam ← forallTelescope wrapInfo.type fun xs _ => do
          let some entry := xs.back? | throwError "no entry"
          let some fam := (← whnf (← inferType entry)).getAppFn.constName? |
            throwError "not an inductive"
          pure fam
        for c in (← getConstInfoInduct fam).ctors do
          addExternTermShorthand target (outer ++ Name.mkSimple c.getString!)
  | _ => throwUnsupportedSyntax

end LeanScript

end
