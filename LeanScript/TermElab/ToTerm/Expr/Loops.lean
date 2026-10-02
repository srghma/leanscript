module

public meta import LeanScript.TermElab.ToTerm.While

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: loops

The translation of range `for` loops, structurally terminating `while` loops and the
arguments of an application, parameterised by the expression translator `tr`
(`LeanScript.TermElab.ToTerm.Expr`).
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

variable (tr : Loc → Expr → TM Src)

/-- A loop in `Id` of `n` steps with state `β`, from `init`, whose step at `k` on the state
    `v` of a `yield` is `mkBody k v : ForInStep β`.  It is `Comp.nat_rec` on `n` whose answer
    is a `ForInStep β`: it starts at `yield init`, the step at `k` is the body on the value of
    a `yield` and keeps a `done` (a `break` or a `return`), and the loop is the value in the
    final step. -/
partial def trStepLoop (L : Loc) (β n init : Expr) (mkBody : Expr → Expr → TM Expr) :
    TM Src := do
  let stepTy ← mkAppM ``ForInStep #[β]
  let ρ ← tyStx L stepTy
  let tn ← tr L n
  let tz ← tr L (← mkAppM ``ForInStep.yield #[init])
  let ts ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `acc stepTy fun acc => do
    let done ← withLocalDeclD `v β fun v => do
      mkLambdaFVars #[v] (← mkAppM ``ForInStep.done #[v])
    let yield ← withLocalDeclD `v β fun v => do mkLambdaFVars #[v] (← mkBody k v)
    let motive ← withLocalDeclD `t stepTy fun t => mkLambdaFVars #[t] stepTy
    let cases ← mkAppOptM ``ForInStep.casesOn #[β, motive, acc, done, yield]
    tr ((L.bind k.fvarId!).bind acc.fvarId!) cases
  let fin ← withLocalDeclD `r stepTy fun r => do
    let idF ← withLocalDeclD `v β fun v => mkLambdaFVars #[v] v
    let motive ← withLocalDeclD `t stepTy fun t => mkLambdaFVars #[t] β
    let cases ← mkAppOptM ``ForInStep.casesOn #[β, motive, r, idF, idF]
    tr (L.bind r.fvarId!) cases
  return .letE (Src.natRec (some ρ) tn tz ts) fin

/-- The translation `r` of `fn` applied to the arguments `args`; an argument `()` forces the
    lazy delay `Unit → τ` it is applied to. -/
partial def appArgs (L : Loc) (fn : Expr) (r : Src) (args : Array Expr) :
    TM Src := do
  let mut r := r
  for i in [0:args.size] do
    let a := args[i]!
    -- a type argument of a field of a polymorphic type, read at the stand-ins (`eraseDeps`):
    -- erased, when it is the stand-in
    if ← isType a then
      let .forallE _ d _ _ ← whnf (← inferType (mkAppN fn args[:i].toArray))
        | fail m!"the type argument{indentExpr a}\nof{indentExpr fn}\nis not expected"
      if let some v ← typeStandIn? d then
        unless ← isDefEq a v do
          fail m!"the polymorphic function{indentExpr fn}\nis applied to the type{indentExpr a}\n\
            where the language reads it at the stand-in{indentExpr v}"
        continue
    if ← isUnitType (← inferType a) then
      r ← delayCoerceTy L (← inferType (mkAppN fn args[:i].toArray))
        (← inferType (mkAppN fn args[:i+1].toArray)) r
    else
      r := Src.app r (← tr L a)
  return r

/-- `for i in range do body` in `Id` (`forIn range init f`, whose step is `mkBody i r`):
    with `range = [a:b:s]`, the loop runs `n = (b - a + s - 1) / s` times, at `i = a + k * s`.
    It is the loop of `trStepLoop` of `n` steps, whose step at `k` is the body at `i`. -/
partial def trRangeFor (L : Loc) (β range init : Expr) (mkBody : Expr → Expr → TM Expr) :
    TM Src := do
  let range ← instantiateMVars range
  let (a, b, s) ← if range.isAppOfArity ``Std.Legacy.Range.mk 4 then
      pure (range.getArg! 0, range.getArg! 1, range.getArg! 2)
    else pure (mkApp (mkConst ``Std.Legacy.Range.start) range,
      mkApp (mkConst ``Std.Legacy.Range.stop) range, mkApp (mkConst ``Std.Legacy.Range.step) range)
  let a0 := (← natLit? a) == some 0
  let s1 := (← natLit? s) == some 1
  let len ← if a0 then pure b else mkAppM ``HSub.hSub #[b, a]
  let n ← if s1 then pure len else
    mkAppM ``HDiv.hDiv #[← mkAppM ``HSub.hSub #[← mkAppM ``HAdd.hAdd #[len, s], mkNatLit 1], s]
  trStepLoop tr L β n init fun k v => do
    let ks ← if s1 then pure k else mkAppM ``HMul.hMul #[k, s]
    let i ← if a0 then pure ks else mkAppM ``HAdd.hAdd #[a, ks]
    mkBody i v

/-- `while c do body` in `Id` (`forIn Loop.mk init f`, of state type `β`): accepted only when
    it is structurally terminating (`whileBound?`, see `LeanScript.TermElab.ToTerm.While`), and
    then the loop of `trStepLoop` whose number of steps bounds the number of iterations, with
    the step `f () v`.  No fuel: when the bounded loop stops, the `while` loop has stopped. -/
partial def trWhile (L : Loc) (e β init f : Expr) : TM Src := do
  let some n ← whileBound? β init f
    | fail m!"the `while` loop{indentExpr e}\nis not structurally terminating: the language has \
        no unbounded loop, so a `while` loop is only accepted when its condition bounds a `Nat` \
        variable `x` of the loop (`x > 0`, `x ≠ 0`, `x < b`, `x ≤ b`, with `b` unchanged by the \
        loop) and every iteration that goes on moves `x` towards the bound by a literal step \
        (`x := x - k`, `x := x / k`, `x := x + k`)"
  trStepLoop tr L β n init fun _ v => pure (mkApp2 f (mkConst ``Unit.unit) v).headBeta

end LeanScript.Gen

end
