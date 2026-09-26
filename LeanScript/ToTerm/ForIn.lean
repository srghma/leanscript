module

public import Lean.Meta

@[expose] public section

meta section

/-!
# `for` loops in the identity monad

A `for` loop in `Id` whose body never leaves the loop early is a fold: its value is the
state after the last iteration.  `do` compiles the body to a function answering
`Id (ForInStep β)`, in which every path ends in `pure (ForInStep.yield s')`, possibly
under `let`s (`let mut` updates), join points (`have __do_jp := fun … => …`, which `do`
introduces after an `if` without `else` or with a `continue`), `if`/`if h :`/`match`, and
`>>=` in `Id`.

* `forInYieldValue β e` turns such a body into the **new state** itself, a Lean
  expression of type `β`: `pure (yield s')` becomes `s'`, and the constructs above are kept,
  re-typed at `β`.  A path that reaches `ForInStep.done` (`break`, or `return` out of the
  loop) is refused: the fold has no way to stop early.
* `listForInAsFoldl` uses it for a loop over a **list**: `for x in l do body` with initial
  state `init` is `l.foldl (fun s x => body' x s) init`, and `for h : x in l do body` is the
  same fold over `l.attach` when the body reads the membership proof `h` (the language
  erases proofs, and `l.attach` is translated as `l`).  The translator then translates this
  `List.foldl` as any other.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- The error for a loop body that leaves the loop. -/
def forInBreakError {α} : MetaM α :=
  throwError "`#leanscript_to_term`: this `for` leaves the loop early (`break` or \
    `return`), which the fold a loop becomes cannot express"

/-- The body of a `for` in `Id`, an expression of type `Id (ForInStep β)` every path of
    which yields, as the state it yields (an expression of type `β`).  See the module
    header. -/
partial def forInYieldValue (β : Expr) (e0 : Expr) : MetaM Expr := do
  let e := e0.consumeMData.headBeta
  match e with
  | .letE n t v b nonDep =>
      -- a join point is a function: substitute it, so that each call to it becomes a
      -- β-redex whose body is a path of the loop
      if v.consumeMData.isLambda then
        return ← forInYieldValue β (b.instantiate1 v)
      return ← withLetDecl n t v (nondep := nonDep) fun x => do
        let b' ← forInYieldValue β (b.instantiate1 x)
        return .letE n t v (b'.abstract #[x]) nonDep
  | _ => pure ()
  match e.getAppFnArgs with
  | (``Pure.pure, #[_, _, _, v]) => return ← forInYieldValue β v
  | (``Bind.bind, #[_, _, _, _, x, f]) => return ← forInYieldValue β (mkApp f x)
  | (``ForInStep.yield, #[_, v]) => return v
  | (``ForInStep.done, #[_, _]) => forInBreakError
  | (``ite, #[_, c, inst, a, b]) =>
      let u ← getLevel β
      return mkApp5 (mkConst ``ite [u]) β c inst (← forInYieldValue β a)
        (← forInYieldValue β b)
  | (``dite, #[_, c, inst, a, b]) =>
      let u ← getLevel β
      let branch (f : Expr) : MetaM Expr := do
        let f ← if f.isLambda then pure f else etaExpand f
        lambdaBoundedTelescope f 1 fun hs body => do
          mkLambdaFVars hs (← forInYieldValue β body)
      return mkApp5 (mkConst ``dite [u]) β c inst (← branch a) (← branch b)
  | _ => pure ()
  if let some mapp ← matchMatcherApp? e then
    let motive ← lambdaTelescope mapp.motive fun xs _ => mkLambdaFVars xs β
    let alts ← mapp.alts.mapIdxM fun i alt =>
      lambdaBoundedTelescope alt (mapp.altNumParams[i]!) fun xs body => do
        mkLambdaFVars xs (← forInYieldValue β body)
    let uElim ← getLevel β
    let mapp := { mapp with motive, alts }
    let mapp ← match mapp.uElimPos? with
      | some pos => pure { mapp with matcherLevels := mapp.matcherLevels.set! pos uElim }
      | none => pure mapp
    return mapp.toExpr
  -- anything else: unfold it one step and look again
  let e' ← whnfCore e
  if e' != e then return ← forInYieldValue β e'
  let e' ← whnf e
  if e' != e then return ← forInYieldValue β e'
  throwError "`#leanscript_to_term`: the body of this `for` does not yield the state of \
    the next iteration:{indentExpr e}"

/-- `for x in l do body` (`forIn l init body`, `withProof := false`) or
    `for h : x in l do body` (`forIn' l init body`, `withProof := true`), in `Id`, over a
    list `l : List α`, as the `List.foldl` it computes.  See the module header. -/
def listForInAsFoldl (α β l init body : Expr) (withProof : Bool) : MetaM Expr := do
  let u ← getDecLevel β
  let v ← getDecLevel α
  let foldl (γ f xs : Expr) : MetaM Expr := do
    let w ← getDecLevel γ
    return mkApp5 (mkConst ``List.foldl [u, w]) β γ f init xs
  withLocalDeclD `x α fun x => withLocalDeclD `state β fun s => do
    if !withProof then
      let next ← forInYieldValue β (mkApp2 body x s)
      return ← foldl α (← mkLambdaFVars #[s, x] next) l
    let hTy := (← whnf (← inferType body)).bindingBody!.bindingDomain!
    withLocalDeclD `h (hTy.instantiate1 x) fun h => do
      let next ← forInYieldValue β (mkApp3 body x h s)
      unless next.containsFVar h.fvarId! do
        return ← foldl α (← mkLambdaFVars #[s, x] next) l
      -- the proof is read: fold over `l.attach`, whose elements carry it
      let attached := mkApp2 (mkConst ``List.attach [v]) α l
      let γ := (← whnf (← inferType attached)).appArg!
      withLocalDeclD `p γ fun p => do
        let pv ← mkAppM ``Subtype.val #[p]
        let ph ← mkAppM ``Subtype.property #[p]
        let next' := (next.replaceFVar x pv).replaceFVar h ph
        foldl γ (← mkLambdaFVars #[s, p] next') attached

end LeanScript.ToTerm
