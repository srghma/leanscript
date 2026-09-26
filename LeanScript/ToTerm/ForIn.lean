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
  re-typed at `β`.
* A body some path of which reaches `ForInStep.done s'` (`break`, or `return` out of the
  loop) is still a fold, of the **step** `ForInStep β` rather than the state: it starts
  from `yield init`, a `done` step is kept as it is, from `yield s` the body's step at `s`
  is taken, and the value of the loop is the state of the last step.  `forInBody` reads
  such a body as its step (an expression of type `ForInStep β`, the constructs above
  re-typed at it), and tells which of the two kinds of body it has.
* `listForInAsFoldl` uses it for a loop over a **list**: `for x in l do body` with initial
  state `init` is `l.foldl (fun s x => body' x s) init` (or the fold of the step), and
  `for h : x in l do body` is the same fold over `l.attach` when the body reads the
  membership proof `h` (the language erases proofs, and `l.attach` is translated as `l`).
  The translator then translates this `List.foldl` as any other.
* `rangeForInBreakAsNatRec` is the fold of the step for `for i in [:n]`, as `Nat.rec`.

Each rewriting is proved an equation of Lean's logic in `LeanScript/ListLibraryFacts.lean`.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- The error for a loop body that does not end in a step of the loop. -/
def forInBodyError {α} (e : Expr) : MetaM α :=
  throwError "`#leanscript_to_term`: the body of this `for` does not end in a step of the \
    loop (`ForInStep.yield` or `ForInStep.done`):{indentExpr e}"

/-- The body of a `for` in `Id`, an expression of type `Id (ForInStep β)`, pushed down to
    its steps.

    With `step := false`, every path must yield, and the answer is the state it yields
    (an expression of type `β`); a path that reaches `ForInStep.done` is refused.  With
    `step := true` the answer is the step itself, an expression of type `ForInStep β`
    whose paths end in `ForInStep.yield s'` or `ForInStep.done s'`.  See the module
    header. -/
partial def forInBodyAux (β : Expr) (step : Bool) (e0 : Expr) : MetaM Expr := do
  let ρ ← if step then mkAppM ``ForInStep #[β] else pure β
  let e := e0.consumeMData.headBeta
  match e with
  | .letE n t v b nonDep =>
      -- a join point is a function: substitute it, so that each call to it becomes a
      -- β-redex whose body is a path of the loop
      if v.consumeMData.isLambda then
        return ← forInBodyAux β step (b.instantiate1 v)
      return ← withLetDecl n t v (nondep := nonDep) fun x => do
        let b' ← forInBodyAux β step (b.instantiate1 x)
        return .letE n t v (b'.abstract #[x]) nonDep
  | _ => pure ()
  match e.getAppFnArgs with
  | (``Pure.pure, #[_, _, _, v]) => return ← forInBodyAux β step v
  | (``Bind.bind, #[_, _, _, _, x, f]) => return ← forInBodyAux β step (mkApp f x)
  | (``ForInStep.yield, #[_, v]) => return if step then e else v
  | (``ForInStep.done, #[_, _]) =>
      if step then return e
      throwError "`#leanscript_to_term`: internal: a `break` read as a state"
  | (``ite, #[_, c, inst, a, b]) =>
      let u ← getLevel ρ
      return mkApp5 (mkConst ``ite [u]) ρ c inst (← forInBodyAux β step a)
        (← forInBodyAux β step b)
  | (``dite, #[_, c, inst, a, b]) =>
      let u ← getLevel ρ
      let branch (f : Expr) : MetaM Expr := do
        let f ← if f.isLambda then pure f else etaExpand f
        lambdaBoundedTelescope f 1 fun hs body => do
          mkLambdaFVars hs (← forInBodyAux β step body)
      return mkApp5 (mkConst ``dite [u]) ρ c inst (← branch a) (← branch b)
  | _ => pure ()
  if let some mapp ← matchMatcherApp? e then
    let motive ← lambdaTelescope mapp.motive fun xs _ => mkLambdaFVars xs ρ
    let alts ← mapp.alts.mapIdxM fun i alt =>
      lambdaBoundedTelescope alt (mapp.altNumParams[i]!) fun xs body => do
        mkLambdaFVars xs (← forInBodyAux β step body)
    let uElim ← getLevel ρ
    let mapp := { mapp with motive, alts }
    let mapp ← match mapp.uElimPos? with
      | some pos => pure { mapp with matcherLevels := mapp.matcherLevels.set! pos uElim }
      | none => pure mapp
    return mapp.toExpr
  -- anything else: unfold it one step and look again
  let e' ← whnfCore e
  if e' != e then return ← forInBodyAux β step e'
  let e' ← whnf e
  if e' != e then return ← forInBodyAux β step e'
  forInBodyError e

/-- The body of a `for` in `Id` that always yields, as the state it yields (an expression
    of type `β`).  See `forInBodyAux`. -/
def forInYieldValue (β : Expr) (e : Expr) : MetaM Expr :=
  forInBodyAux β false e

/-- The body of a `for` in `Id`, read as the loop needs it: when no path leaves the loop,
    the state it yields (of type `β`) and `false`; otherwise the step it answers (of type
    `ForInStep β`, a `ForInStep.done` on the paths that `break` or `return`) and
    `true`. -/
def forInBody (β : Expr) (e : Expr) : MetaM (Expr × Bool) := do
  let stepE ← forInBodyAux β true e
  if (stepE.find? (·.isConstOf ``ForInStep.done)).isSome then
    return (stepE, true)
  return (← forInBodyAux β false e, false)

/-- `ForInStep.casesOn t done yield`, at the non-dependent motive `ρ`. -/
def mkForInStepCases (β ρ t done yield : Expr) : MetaM Expr := do
  let u ← getDecLevel β
  let w ← getLevel ρ
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  let motive := mkLambda `_ .default stepTy ρ
  return mkAppN (mkConst ``ForInStep.casesOn [w, u]) #[β, motive, t, done, yield]

/-- The state a step carries, whether the loop goes on or stops (`ForInStep.value`, as a
    case analysis). -/
def mkForInStepState (β t : Expr) : MetaM Expr := do
  let idβ := mkLambda `s .default β (.bvar 0)
  mkForInStepCases β β t idβ idβ

/-- The step of a loop that can stop, as a function of the step before it: a loop that
    has stopped stays stopped (`ForInStep.done s` is kept), and one that goes on with the
    state `s` takes the step `next` (an expression in the free variable `s`).  `k` gets
    the free variable of the step before and this step. -/
def withForInStepAfter {γ} (β s next : Expr) (k : Expr → Expr → MetaM γ) : MetaM γ := do
  let stepTy ← mkAppM ``ForInStep #[β]
  withLocalDeclD `step stepTy fun st => do
    let u ← getDecLevel β
    let done := mkLambda `s .default β (mkApp2 (mkConst ``ForInStep.done [u]) β (.bvar 0))
    let yield ← mkLambdaFVars #[s] next
    k st (← mkForInStepCases β stepTy st done yield)

/-- `for x in l do body` (`forIn l init body`, `withProof := false`) or
    `for h : x in l do body` (`forIn' l init body`, `withProof := true`), in `Id`, over a
    list `l : List α`, as the `List.foldl` it computes.  See the module header. -/
def listForInAsFoldl (α β l init body : Expr) (withProof : Bool) : MetaM Expr := do
  let u ← getDecLevel β
  let v ← getDecLevel α
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  -- the fold over the elements `xs : List γ` whose element is the free variable `x` and
  -- whose body, read with the state `s`, is `next` (a state, or a step when `breaks`)
  let fold (s next : Expr) (breaks : Bool) (γ x xs : Expr) : MetaM Expr := do
    let w ← getDecLevel γ
    unless breaks do
      return mkApp5 (mkConst ``List.foldl [u, w]) β γ (← mkLambdaFVars #[s, x] next) init xs
    withForInStepAfter β s next fun st after => do
      let f ← mkLambdaFVars #[st, x] after
      let init' := mkApp2 (mkConst ``ForInStep.yield [u]) β init
      mkForInStepState β (mkApp5 (mkConst ``List.foldl [u, w]) stepTy γ f init' xs)
  withLocalDeclD `x α fun x => withLocalDeclD `state β fun s => do
    if !withProof then
      let (next, breaks) ← forInBody β (mkApp2 body x s)
      return ← fold s next breaks α x l
    let hTy := (← whnf (← inferType body)).bindingBody!.bindingDomain!
    withLocalDeclD `h (hTy.instantiate1 x) fun h => do
      let (next, breaks) ← forInBody β (mkApp3 body x h s)
      unless next.containsFVar h.fvarId! do
        return ← fold s next breaks α x l
      -- the proof is read: fold over `l.attach`, whose elements carry it
      let attached := mkApp2 (mkConst ``List.attach [v]) α l
      let γ := (← whnf (← inferType attached)).appArg!
      withLocalDeclD `p γ fun p => do
        let pv ← mkAppM ``Subtype.val #[p]
        let ph ← mkAppM ``Subtype.property #[p]
        let next' := (next.replaceFVar x pv).replaceFVar h ph
        fold s next' breaks γ p attached

/-- `for i in [:n] do body` in `Id` whose body can leave the loop, with initial state
    `init : β`, as a Lean expression: the recursion on `n` whose value is the step after
    `n` iterations — `ForInStep.yield init` at `0`, and after it, the step of the body at
    the index `i` if the loop has not stopped — of which the state is read. -/
def rangeForInBreakAsNatRec (β stop init i s next : Expr) : MetaM Expr := do
  let u ← getDecLevel β
  let stepTy := mkApp (mkConst ``ForInStep [u]) β
  let branch ← withForInStepAfter β s next fun st after => mkLambdaFVars #[i, st] after
  let motive := mkLambda `_ .default (mkConst ``Nat) stepTy
  let init' := mkApp2 (mkConst ``ForInStep.yield [u]) β init
  let r := mkApp4 (mkConst ``Nat.rec [← getLevel stepTy]) motive init' branch stop
  mkForInStepState β r

end LeanScript.ToTerm
