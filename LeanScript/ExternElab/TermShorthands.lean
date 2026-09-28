module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Binders

public section

/-!
# `derive_extern_term_shorthands`: one term former per entry of the extern catalogue

`derive_extern_term_shorthands PExpr` adds, for every shorthand `LeanInitPureExtern.c` of an
entry of the catalogue (`LeanScript.LeanInitPureExterns.Shorthands`), the definition
`PExpr.c`: the call of the extern `c` on pure expressions of the types of its arguments,

```
@[match_pattern, reducible] def PExpr.c {ks} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}
    (fields of c) {o₁ … oₙ : Lvl} (a1 : PExpr Δ Φ Γ σ₁ o₁) … (an : PExpr Δ Φ Γ σₙ oₙ) {ℓ : Nat}
    (h : Lvl.meet o₁ (… (Lvl.meet oₙ none)) = some ℓ := by rfl) : PExpr Δ Φ Γ τ (some ℓ) :=
  .neu (.extern (.c fields) (.cons a1 (… (.cons an .nil))) h)
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
    (`LeanInitPureExtern.c`); `auto` is the constant of the syntax of the tactic `rfl`, the
    default proof of the level equation. -/
meta def addExternTermShorthand (target sc auto : Name) : MetaM Unit := do
  let info ← getConstInfo sc
  let name := target ++ Name.mkSimple sc.getString!
  let names := binderNamesOf info.type
  let lvlTy := mkApp (mkConst ``Option [0]) (mkConst ``Nat)
  withLocalDecl `ks .implicit (mkApp (mkConst ``List [0]) (mkConst ``Nat)) fun ks => do
  withLocalDecl `Δ .implicit (mkApp (mkConst `LeanScript.DSig) ks) fun Δ => do
  withLocalDecl `Φ .implicit (mkApp (mkConst `LeanScript.KCtx) ks) fun Φ => do
  withLocalDecl `Γ .implicit (mkApp (mkConst `LeanScript.UCtx) ks) fun Γ => do
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
        let lvlDecls := elems.mapIdx fun i _ =>
          (Name.mkSimple s!"o{i + 1}", BinderInfo.implicit, fun (_ : Array Expr) => pure lvlTy)
        withLocalDecls lvlDecls fun os => do
        let argDecls ← elems.mapIdxM fun i σ => do
          return (Name.mkSimple s!"a{i + 1}",
            mkApp5 (mkConst `LeanScript.PExpr) ks Δ Φ Γ (← normExternTy σ) |>.app os[i]!)
        withLocalDeclsDND argDecls fun as => do
        withLocalDecl `ℓ .implicit (mkConst ``Nat) fun ℓ => do
          -- `.cons a1 (… (.cons an .nil))`, at the types of the entry, and its level
          let mut args := mkApp4 (mkConst `LeanScript.Args.nil) ks Δ Φ Γ
          let mut tail : Expr := mkApp (mkConst ``List.nil [0]) tyTy
          let mut lvl : Expr := mkApp (mkConst ``Option.none [0]) (mkConst ``Nat)
          for i in (List.range as.size).reverse do
            args := mkAppN (mkConst `LeanScript.Args.cons)
              #[ks, Δ, Φ, Γ, elems[i]!, tail, os[i]!, lvl, as[i]!, args]
            tail := mkApp3 (mkConst ``List.cons [0]) tyTy elems[i]! tail
            lvl := mkApp2 (mkConst `LeanScript.Lvl.meet) os[i]! lvl
          let someℓ := mkApp2 (mkConst ``Option.some [0]) (mkConst ``Nat) ℓ
          let eqTy := mkApp3 (mkConst ``Eq [1]) lvlTy lvl someℓ
          withLocalDeclD `h (mkApp2 (mkConst ``autoParam [0]) eqTy (mkConst auto)) fun h => do
          let neu := mkAppN (mkConst `LeanScript.Neu.extern) #[ks, Δ, Φ, Γ, σs, τ, lvl, ℓ, e, args, h]
          let (body, resTy) :=
            if target == `LeanScript.Neu then (neu, mkApp6 (mkConst `LeanScript.Neu) ks Δ Φ Γ τ ℓ)
            else (mkAppN (mkConst `LeanScript.PExpr.neu) #[ks, Δ, Φ, Γ, τ, ℓ, neu],
              mkApp6 (mkConst `LeanScript.PExpr) ks Δ Φ Γ τ someℓ)
          let bs := #[ks, Δ, Φ, Γ] ++ fvs ++ os ++ as ++ #[ℓ, h]
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
              expression.  The last argument, the equation of the level of the arguments \
              (at least one of them is open), is proved by `rfl` by default."
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
      let auto ← withExporting <| Lean.Elab.Term.declareTacticSyntax (← `(tactic| rfl))
        (name? := some (target ++ `externLvlAuto))
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
          addExternTermShorthand target (outer ++ Name.mkSimple c.getString!) auto
  | _ => throwUnsupportedSyntax

end LeanScript

end
