module

public meta import LeanScript.TermElab.ToTerm.Expr.Calls

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: constructors

The translation of constructor applications, parameterised by the expression translator
`tr` (`LeanScript.TermElab.ToTerm.Expr`).
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

variable (tr : Loc → Expr → TM Src)

/-- A value `a : Fin m → T` of a field that the language reads as `Nat → Option T`
    (`finOptArrow`): `fun j => if h : j < m then some (a ⟨j, h⟩) else none`, translated (a
    field of an opened constructor is already such a function; `m = 0` is `fun _ => none`). -/
partial def trOptField (L : Loc) (a : Expr) (aTy : Expr) : TM Src := do
  if let .fvar x := a then
    if (← get).optFields.contains x then return ← tr L a
  let .forallE _ d T _ := aTy | fail m!"the value{indentExpr a}\nis not a function"
  let d ← whnf d
  unless d.isAppOfArity ``Fin 1 && !T.hasLooseBVars do
    fail m!"the value{indentExpr a}\nis not a function on `Fin m`"
  let m := d.appArg!
  let OT ← mkAppM ``Option #[T]
  let v ← withLocalDeclD `j (mkConst ``Nat) fun j => do
    if (← natLit? m) == some 0 then
      return ← mkLambdaFVars #[j] (← mkAppOptM ``Option.none #[T])
    let lt ← mkAppM ``LT.lt #[j, m]
    let dec ← synthInstance (mkApp (mkConst ``Decidable) lt)
    let yes ← withLocalDeclD `h lt fun h => do
      mkLambdaFVars #[h] (← mkAppM ``Option.some #[mkApp a (← mkAppOptM ``Fin.mk #[m, j, h])])
    let no ← withLocalDeclD `h (mkNot lt) fun h => do
      mkLambdaFVars #[h] (← mkAppOptM ``Option.none #[T])
    mkLambdaFVars #[j] (← mkAppOptM ``dite #[OT, lt, dec, yes, no])
  tr L v

/-- A constructor application: `#leanscript_get_ctor` of the constructor, every parameter
    given by name, applied to the terms of the fields kept. -/
partial def trCtor (L : Loc) (cinfo : ConstructorVal) (fn : Expr) (args : Array Expr) :
    TM Src := do
  unless args.size == cinfo.numParams + cinfo.numFields do
    fail m!"the constructor `{cinfo.name}` is not fully applied"
  let mut ty ← inferType fn
  let mut named : Array (TSyntax ``leanscriptNamedArg) := #[]
  let mut fields : Array Src := #[]
  let mask ← ctorErasedMask cinfo.name fn.constLevels! args[:cinfo.numParams].toArray
  let optMask ← ctorOptMask cinfo.name fn.constLevels! args[:cinfo.numParams].toArray
  -- a constructor of a type-indexed family (`Nest.cons {α} a r`): it is generated at the index
  -- the family is read at (`Nest.Elem Nat`), and a field of type `α` is put in it
  let ind ← getConstInfoInduct cinfo.induct
  let tyIdx? ← if ← typeIndexed ind then
      let (p, kinds) ← ctorIndexKinds ind cinfo.name
      let canon := (← normType (← inferType (mkAppN fn args)) false).appArg!
      pure (some (p, kinds, canon))
    else pure none
  for i in [0:args.size] do
    ty ← whnf ty
    let .forallE n _ b _ := ty | fail m!"bad constructor `{cinfo.name}`"
    let a := args[i]!
    if i < cinfo.numParams then
      if a.hasFVar then fail m!"the parameter `{n}` of `{cinfo.name}` is not closed{indentExpr a}"
      named := named.push (← `(leanscriptNamedArg| ($(mkIdent n) := $(← exprToSyntax a))))
    else if let some (p, kinds, canon) := tyIdx? then
      let q := i - cinfo.numParams
      if q == p then
        if canon.hasFVar then
          fail m!"the constructor `{cinfo.name}` is used at the index{indentExpr a}\nwhich is \
            not closed"
        named := named.push (← `(leanscriptNamedArg| ($(mkIdent n) := $(← exprToSyntax canon))))
      else if !mask[q]! then
        match kinds[q]! with
        | some true =>
          let v ← injectElem ind args[:cinfo.numParams].toArray args[cinfo.numParams + p]! a
          fields := fields.push (← tr L v)
        | some false => fields := fields.push (← tr L a)
        | none =>
          fail m!"the field `{n}` of `{cinfo.name}` mentions the type index other than as the \
            index itself or inside `{ind.name}`: its value cannot be put in the element type"
    else if !mask[i - cinfo.numParams]! then
      if optMask[i - cinfo.numParams]! then
        fields := fields.push (← trOptField tr L a (← whnf (← inferType a)))
      else
        fields := fields.push (← tr L a)
    ty := b.instantiate1 a
  let T ← normType (← inferType (mkAppN fn args)) false
  if (← cirOf L T false).hasData then modify fun s => { s with usesData := true }
  let ctorFn ← `(#leanscript_get_ctor $(mkIdent (`_root_ ++ cinfo.name)) $named*)
  -- what the constructor function builds, for the case analyses of it the normaliser reduces
  let plan ← lm (planType T L.prog?)
  let shape? : Option Anf.CtorShape ← match plan.ctors.findIdx? (·.1 == cinfo.name) with
    | none => pure none
    | some pos => do
      let kind : Anf.CtorKind :=
        if plan.isBool then .bool (pos == 1)
        else if plan.enum?.isSome then .enum pos
        else if plan.ctors.size == 1 then (if fields.size == 1 then .wrap else .record)
        else .union pos
      let data? ← match plan.data? with
        | some (b, j) => pure (some (← brefStx L.c b, quote j))
        | none => pure none
      pure (some { kind, data? })
  return .ctor (← `(($ctorFn))) fields shape?

end LeanScript.Gen

end
