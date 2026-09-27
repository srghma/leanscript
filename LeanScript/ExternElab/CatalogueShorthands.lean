module

public meta import Lean.Elab.Command

public section

/-!
# `derive_catalogue_shorthands`: one shorthand per entry of a two-level catalogue

A *two-level catalogue* is an inductive `Outer` each of whose constructors wraps one entry
of a *family*, another inductive:

```
inductive Outer : List MyTy → MyTy → Type where
  | fooExtern {σs : List MyTy} {τ : MyTy} : FooExtern … σs τ → Outer σs τ
  | barExtern {σs : List MyTy} {τ : MyTy} : BarExtern … σs τ → Outer σs τ
```

(the indices are the signature of the entry: the types of its arguments, then of its result)

(`LeanScript.LeanInitPureExtern` is one.)  `derive_catalogue_shorthands Outer` adds, for
every constructor `FooExtern.c` of every family, the definition `Outer.c`, which builds the
entry and wraps it in the constructor of its family:

```
@[match_pattern, reducible] def Outer.c : <the arguments of FooExtern.c> → Outer … σs τ :=
  fun x₁ … xₙ => .fooExtern (.c x₁ … xₙ)
```

So an entry is written `.c x₁ … xₙ` wherever an `Outer` is expected (and matched on as
well, since the shorthand is `@[match_pattern]`).  Each shorthand takes all the parameters
of `Outer` but its indices first, implicitly and in their order, whichever of them its family
uses, so a shorthand can be applied to the parameters of `Outer` like a constructor of
`Outer`; its explicit arguments are the ones of `FooExtern.c`.

The shorthands are computed from the constructors themselves, so they never need to be
regenerated when an entry is added to, changed in or removed from a family.
-/

namespace LeanScript

open Lean Meta Elab Command

/-- The leading `fun`s of `e`, with the `autoParam`/`optParam` annotations of their binder
    types removed (they belong in the type of a definition, not in its value). -/
meta def dropBinderAnnotations : Expr → Expr
  | .lam n d b bi => .lam n d.cleanupAnnotations (dropBinderAnnotations b) bi
  | e => e

/-- The names of the leading binders of a type. -/
meta def binderNames : Expr → Array Name
  | .forallE n _ b _ => #[n] ++ binderNames b
  | _ => #[]

/-- Add the shorthand `outer.c` of the entry `c` of the family that the constructor `wrap`
    of `outer` wraps.

    The entry `c` is applied to fresh metavariables for the parameters of its family and to
    its own arguments; `wrap` is applied to fresh metavariables for its parameters, its
    indices and its entry, and its entry is unified with `c …`.  What is left undetermined
    becomes a binder of the shorthand: first the parameters of `outer` (implicitly, in their
    order), then the parameters of the family that Lean promoted from an index of the entry
    (explicitly), then the arguments of `c`. -/
meta def addCatalogueShorthand (outer wrap c : Name) : MetaM Unit := do
  let wrapInfo ← getConstInfoCtor wrap
  let cInfo ← getConstInfoCtor c
  unless wrapInfo.levelParams.isEmpty && cInfo.levelParams.isEmpty do
    throwError "`derive_catalogue_shorthands`: `{.ofConstName wrap}` or `{.ofConstName c}` \
      is universe polymorphic, which is not supported"
  let name := outer ++ Name.mkSimple c.getString!
  let wrapNames := binderNames wrapInfo.type
  let cNames := binderNames cInfo.type
  let (pms, _, rest) ← forallMetaBoundedTelescope cInfo.type cInfo.numParams
  forallTelescope rest fun args _ => do
    let (ms, _, _) ← forallMetaTelescope wrapInfo.type
    let e := mkAppN (mkConst c) (pms ++ args)
    unless ← isDefEq ms.back! e do
      throwError "`derive_catalogue_shorthands`: `{.ofConstName wrap}` cannot hold{indentExpr e}"
    -- the metavariables left, in the order of the binders of the shorthand
    let mut pending : Array (Name × BinderInfo × MVarId) := #[]
    for i in [0:wrapInfo.numParams] do
      if let .mvar m ← instantiateMVars ms[i]! then
        unless pending.any (·.2.2 == m) do
          pending := pending.push (wrapNames[i]!, .implicit, m)
    for i in [0:pms.size] do
      if let .mvar m ← instantiateMVars pms[i]! then
        unless pending.any (·.2.2 == m) do
          pending := pending.push (cNames[i]!, .default, m)
    let rec go (k : Nat) (fvs : Array Expr) : MetaM Unit := do
      if h : k < pending.size then
        let (n, bi, m) := pending[k]
        let ty ← instantiateMVars (← m.getType)
        withLocalDecl n bi ty fun x => do
          m.assign x
          go (k + 1) (fvs.push x)
      else
        let body ← instantiateMVars (mkAppN (mkConst wrap) ms)
        if body.hasMVar then
          throwError "`derive_catalogue_shorthands`: internal: {body} is not determined"
        let xs := fvs ++ args
        let value := dropBinderAnnotations (← mkLambdaFVars xs body)
        let type ← mkForallFVars xs (← inferType body)
        let decl := Declaration.defnDecl
          { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
        withExporting do
          addDecl decl
          setReducibleAttribute name
          matchPatternAttr.setTag name
          addDocStringCore name s!"`{c.getPrefix.getString!}.{c.getString!}`, \
            as an entry of the catalogue `{outer}`."
        compileDecl decl
    go 0 #[]

/-- `derive_catalogue_shorthands Outer`: for every entry `FooExtern.c` of every family
    wrapped by a constructor `Outer.fooExtern` of `Outer`, the shorthand
    `Outer.c x₁ … xₙ := .fooExtern (.c x₁ … xₙ)`, reducible and usable in patterns (see the
    module doc). -/
syntax (name := deriveCatalogueShorthands) "derive_catalogue_shorthands " ident : command

@[command_elab deriveCatalogueShorthands]
meta def elabDeriveCatalogueShorthands : CommandElab
  | `(derive_catalogue_shorthands $id) => liftTermElabM do
      let outer ← realizeGlobalConstNoOverloadWithInfo id
      let outerInfo ← getConstInfoInduct outer
      for wrap in outerInfo.ctors do
        let wrapInfo ← getConstInfoCtor wrap
        -- the family is the type of the last field of the constructor
        let fam ← forallTelescope wrapInfo.type fun xs _ => do
          let some entry := xs.back? | throwError "`derive_catalogue_shorthands`: \
            the constructor `{.ofConstName wrap}` holds no entry"
          let some fam := (← whnf (← inferType entry)).getAppFn.constName? |
            throwError "`derive_catalogue_shorthands`: the entry of `{.ofConstName wrap}` \
              is not an inductive"
          pure fam
        for c in (← getConstInfoInduct fam).ctors do
          addCatalogueShorthand outer wrap c
  | _ => throwUnsupportedSyntax

end LeanScript

end
