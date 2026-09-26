module

public import Lean.Meta
public meta import LeanScript.ToTerm.ForIn

@[expose] public section

meta section

/-!
# `while` loops: accepted only as structural recursions

The language has no loop that is not a fold — no fuel, no measure.  A `while c do …`
(and `repeat …`, `repeat … until c`) in the identity monad is accepted only when its
**syntax** shows it is a structural recursion, and it is then the recursion on `Nat` it
stands for.  Anything else is rejected.

`do` compiles such a loop to `forIn Lean.Loop.mk init f`, whose body answers a step
`ForInStep β` (`yield s` to go on, `done s` to stop).  The body is read as its step with
`forInBodyAux β true`: a tree of `let`s, `if`s, `if h :`s and `match`es whose leaves are
`ForInStep.yield s'` and `ForInStep.done s'`.

**The structural test** (`whileCounter?`).  The loop is a structural recursion when some
component `x : Nat` of the state (a `let mut` variable: the *counter*) moves by one on
every path that ends in `ForInStep.yield s'` — that is, the component of `s'` at the
counter's place is, on every such path,

* **down**: `x - 1` (or `Nat.pred x`, `Nat.sub x 1`), on a path that has tested `x ≠ 0`
  (`x > 0`, `0 < x`, `x ≠ 0`, `x != 0`, `!(x == 0)`, `1 ≤ x`, the `else` of `x = 0`,
  `x == 0`, `x ≤ 0`, …, possibly inside `&&` and `decide`), or `n`, in the case `n + 1`
  of a `match` on `x` (or on a path that has tested `x = n + 1`); the loop is the
  recursion on `x`;
* or **up**: `x + 1`, on a path that has tested `x < b` (or `x ≤ b`, i.e. `x < b + 1`)
  for one bound `b` that does not mention the state, so that the loop cannot change it;
  the loop is the recursion on `b - x`, exactly as `for x in [x:b]` is.

Paths ending in `ForInStep.done` (the loop's condition failing, `break`, `return` from
inside) are unconstrained.  The test is purely syntactic up to reducible unfolding (and
instances): no measure is inferred, and no proof is searched for.

**The translation** (`whileAsNatRec`).  A loop whose counter starts at `x₀` takes at most
`x₀ + 1` iterations (`b - x₀ + 1` when it counts up to `b`), so it is the recursion on
that number whose value is the step after each iteration, a stopped loop staying stopped (`rangeForInBreakAsNatRec`, the fold the
translator already uses for a `for` that can `break`).  The equation is
`LeanScript.loop_forIn_eq_natRec` (`LeanScript/WhileFacts.lean`), whose hypothesis — every
`yield` makes the measure `x` (or `b - x`) smaller — is exactly what the structural test
checks.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-- The places of the `Nat` components of a loop state of type `β`: `let mut` variables
    are packed into nested pairs (`Prod`, `MProd`), and a place is the path of `fst`
    (`false`) / `snd` (`true`) projections to a component. -/
partial def natStatePaths (β : Expr) : MetaM (Array (List Bool)) := do
  let β' ← whnfR β
  if β'.isAppOfArity ``Prod 2 || β'.isAppOfArity ``MProd 2 then
    let l ← natStatePaths β'.appFn!.appArg!
    let r ← natStatePaths β'.appArg!
    return l.map (false :: ·) ++ r.map (true :: ·)
  if ← withReducible (isDefEq β' (mkConst ``Nat)) then return #[[]]
  return #[]

/-- The component at the place `p` of a state `e`: read off a pair written out, and
    projected otherwise. -/
partial def stateComponent (e : Expr) : List Bool → MetaM Expr
  | [] => return e
  | b :: p => do
      let e := e.consumeMData.headBeta
      match e.getAppFnArgs with
      | (``Prod.mk, #[_, _, a, c]) | (``MProd.mk, #[_, _, a, c]) =>
          stateComponent (if b then c else a) p
      | _ =>
          let ty ← whnfR (← inferType e)
          let n := if ty.isAppOfArity ``MProd 2 then ``MProd else ``Prod
          let proj := if b then n ++ `snd else n ++ `fst
          stateComponent (← mkAppM proj #[e]) p

/-- The facts a test gives, taken apart: a conjunction is its two sides, a `Bool` test
    `b = true` is read through `&&`, `!`, `decide`, and a negated one through `||`. -/
partial def splitFact (f : Expr) : MetaM (List Expr) := do
  let f := f.consumeMData
  if let some (a, b) := f.and? then
    return (← splitFact a) ++ (← splitFact b)
  if let some (_, lhs, rhs) := f.eq? then
    if rhs.isConstOf ``Bool.true then
      match lhs.consumeMData.getAppFnArgs with
      | (``and, #[a, b]) =>
          return (← splitFact (← mkEq a rhs)) ++ (← splitFact (← mkEq b rhs))
      | (``Decidable.decide, #[p, _]) => return f :: (← splitFact p)
      | (``not, #[a]) => return f :: (← splitFact (mkNot (← mkEq a rhs)))
      | _ => pure ()
  if let some p := f.not? then
    if let some (_, lhs, rhs) := p.eq? then
      if rhs.isConstOf ``Bool.true then
        match lhs.consumeMData.getAppFnArgs with
        | (``or, #[a, b]) =>
            return (← splitFact (mkNot (← mkEq a rhs))) ++ (← splitFact (mkNot (← mkEq b rhs)))
        | (``Decidable.decide, #[q, _]) => return f :: (← splitFact (mkNot q))
        | _ => pure ()
  return [f]

/-- Is `e`, up to reducible unfolding and instances, the proposition `c`? -/
def factIs (e c : Expr) : MetaM Bool :=
  withNewMCtxDepth <| withTransparency .instances <| isDefEq e c

/-- The forms of the fact `x ≠ 0` a test can give. -/
def nonzeroForms (x : Expr) : MetaM (Array Expr) := do
  let zero := mkNatLit 0
  let one := mkNatLit 1
  let tru := mkConst ``Bool.true
  let fls := mkConst ``Bool.false
  let beq0 ← mkAppM ``BEq.beq #[x, zero]
  return #[
    ← mkAppM ``LT.lt #[zero, x],
    ← mkAppM ``LE.le #[one, x],
    mkNot (← mkEq x zero),
    mkNot (← mkEq zero x),
    mkNot (← mkAppM ``LE.le #[x, zero]),
    mkNot (← mkAppM ``LT.lt #[x, one]),
    ← mkEq (← mkAppM ``bne #[x, zero]) tru,
    ← mkEq (mkApp (mkConst ``not) beq0) tru,
    mkNot (← mkEq beq0 tru),
    ← mkEq beq0 fls]

/-- Does one of the facts `facts` say that `x ≠ 0`?  Besides the forms of
    `nonzeroForms`, a fact `x = p` whose right side is a successor (`n + 1`,
    `Nat.succ n`, a positive literal) says it. -/
def factsNonzero (facts : List Expr) (x : Expr) : MetaM Bool := do
  let forms ← nonzeroForms x
  for f in facts do
    for c in forms do
      if ← factIs f c then return true
    if let some (_, a, p) := f.eq? then
      if ← factIs a x then
        let p' ← whnfR p
        if p'.isAppOfArity ``Nat.succ 1 then return true
        if let some k ← (evalNat p).run then
          if k > 0 then return true
        if let (``HAdd.hAdd, #[_, _, _, _, _, k]) := p.consumeMData.getAppFnArgs then
          if let some k ← (evalNat k).run then
            if k > 0 then return true
  return false

/-- Is `v` the predecessor of `x`, on a path whose tests gave the facts `facts`?  Either
    `v` is `x - 1` and the facts say `x ≠ 0`, or a fact says `x = v + 1`. -/
def isPredecessor (facts : List Expr) (x v : Expr) : MetaM Bool := do
  let v := v.consumeMData
  -- `x - 1`, `Nat.pred x`, `Nat.sub x 1`, under `x ≠ 0`
  if v.isAppOf ``HSub.hSub || v.isAppOf ``Sub.sub || v.isAppOf ``Nat.sub ||
      v.isAppOf ``Nat.pred then
    let pred ← mkAppM ``HSub.hSub #[x, mkNatLit 1]
    if ← factIs v pred then
      if ← factsNonzero facts x then return true
  -- `n`, where `x = n + 1`
  let succ := mkApp (mkConst ``Nat.succ) v
  for f in facts do
    if let some (_, a, p) := f.eq? then
      if ← factIs a x then
        if ← factIs p succ then return true
      if ← factIs p x then
        if ← factIs a succ then return true
  return false

/-- The facts that hold in the case of a `match` whose parameters are the free variables
    `xs`, read off the equation of the `match` for that case: each discriminant equals the
    pattern of the case, and the hypotheses of the equation (a case after an overlapping
    one, such as `| _ =>` after `| 0 =>`, has `x = 0 → False`) hold.  A pattern that is
    just a parameter of the case is the discriminant itself: it comes back as a
    substitution (the parameters, and the discriminants to put in their place), applied
    to the facts and to be applied to the case.  A fact that mentions
    a variable of the equation which is not a parameter of the case is left out, and no
    facts come out of an equation that is not of the expected shape. -/
def matchCaseFacts (mapp : MatcherApp) (i : Nat) (xs : Array Expr) :
    MetaM (List Expr × Array Expr × Array Expr) := do
  try
    let eqns ← Match.getEquationsFor mapp.matcherName
    let some eqn := eqns.eqnNames[i]? | return ([], #[], #[])
    let info ← getConstInfo eqn
    let us := mapp.matcherLevels.toList
    let ty ← instantiateForall (info.type.instantiateLevelParams info.levelParams us)
      mapp.params
    forallTelescopeReducing ty fun ys body => do
      let some (_, lhs, rhs) := body.eq? | return ([], #[], #[])
      let lhsArgs := lhs.getAppArgs
      let start := mapp.params.size + 1
      let pats := lhsArgs.extract start (start + mapp.discrs.size)
      unless pats.size == mapp.discrs.size do return ([], #[], #[])
      -- the right side is the case applied to its parameters
      let rhsArgs := rhs.getAppArgs
      let mut vars : Array Expr := #[]
      let mut vals : Array Expr := #[]
      for a in rhsArgs, x in xs do
        if a.isFVar then
          vars := vars.push a
          vals := vals.push x
      let usable (e : Expr) : Bool := !(e.hasAnyFVar (ys.contains <| .fvar ·))
      let mut facts := []
      -- a pattern that is a parameter of the case is the discriminant itself
      let mut substVars : Array Expr := #[]
      let mut substVals : Array Expr := #[]
      for d in mapp.discrs, p in pats do
        let p' := p.replaceFVars vars vals
        if p'.isFVar && xs.contains p' && !(substVars.contains p') then
          substVars := substVars.push p'
          substVals := substVals.push d
        else if usable p' then facts := (← mkEq d p') :: facts
      for y in ys do
        let t := (← inferType y).replaceFVars vars vals
        if (← isProp t) && usable t then
          let t := match t with
            | .forallE _ q (.const ``False _) _ => mkNot q
            | t => t
          facts := t :: facts
      return (facts.map (·.replaceFVars substVars substVals), substVars, substVals)
  catch _ => return ([], #[], #[])

/-- Does every path of the step `e` (a Lean expression of type `ForInStep β`, as
    `forInBodyAux β true` gives it) that goes on with the loop pass the test `leaf`?  It
    is given the tests of the path (`facts`) and the component at the place `p` of the
    state the path yields.  Paths that stop (`ForInStep.done`) pass.  Anything that is not
    a `let`, an `if`, an `if h :`, a `match` or a step fails. -/
partial def yieldsAll (p : List Bool) (leaf : List Expr → Expr → MetaM Bool)
    (facts : List Expr) (e0 : Expr) : MetaM Bool := do
  let e := e0.consumeMData.headBeta
  if let .letE _ _ v b _ := e then
    return ← yieldsAll p leaf facts (b.instantiate1 v)
  match e.getAppFnArgs with
  | (``ForInStep.done, #[_, _]) => return true
  | (``ForInStep.yield, #[_, v]) => leaf facts (← stateComponent v p)
  | (``ite, #[_, c, _, a, b]) =>
      if !(← yieldsAll p leaf ((← splitFact c) ++ facts) a) then return false
      yieldsAll p leaf ((← splitFact (mkNot c)) ++ facts) b
  | (``dite, #[_, c, _, a, b]) =>
      let branch (f : Expr) (fact : Expr) : MetaM Bool := do
        let f ← if f.isLambda then pure f else etaExpand f
        lambdaBoundedTelescope f 1 fun _ body => do
          yieldsAll p leaf ((← splitFact fact) ++ facts) body
      if !(← branch a c) then return false
      branch b (mkNot c)
  | _ =>
    if let some mapp ← matchMatcherApp? e then
      for i in [:mapp.alts.size] do
        let ok ← lambdaBoundedTelescope mapp.alts[i]! (mapp.altNumParams[i]!) fun xs body => do
          let (caseFacts, substVars, substVals) ← matchCaseFacts mapp i xs
          yieldsAll p leaf (caseFacts ++ facts) (body.replaceFVars substVars substVals)
        if !ok then return false
      return true
    return false

/-- The upper bounds of `x` a fact gives: `b` for `x < b` (`b > x`, `¬ b ≤ x`), and
    `b + 1` for `x ≤ b` (`b ≥ x`, `¬ b < x`). -/
def factBounds (x f : Expr) : MetaM (Array Expr) := do
  let f := f.consumeMData
  let succ (b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[b, mkNatLit 1]
  let isX (a : Expr) : MetaM Bool := factIs a x
  let isNat (t : Expr) : MetaM Bool := withReducible <| isDefEq t (mkConst ``Nat)
  let mut out := #[]
  match f.getAppFnArgs with
  | (``LT.lt, #[t, _, a, b]) => if (← isNat t) && (← isX a) then out := out.push b
  | (``GT.gt, #[t, _, b, a]) => if (← isNat t) && (← isX a) then out := out.push b
  | (``LE.le, #[t, _, a, b]) => if (← isNat t) && (← isX a) then out := out.push (← succ b)
  | (``GE.ge, #[t, _, b, a]) => if (← isNat t) && (← isX a) then out := out.push (← succ b)
  | _ => pure ()
  if let some q := f.not? then
    match q.consumeMData.getAppFnArgs with
    | (``LE.le, #[t, _, b, a]) => if (← isNat t) && (← isX a) then out := out.push b
    | (``GE.ge, #[t, _, a, b]) => if (← isNat t) && (← isX a) then out := out.push b
    | (``LT.lt, #[t, _, b, a]) => if (← isNat t) && (← isX a) then out := out.push (← succ b)
    | (``GT.gt, #[t, _, a, b]) => if (← isNat t) && (← isX a) then out := out.push (← succ b)
    | _ => pure ()
  return out

/-- Is `v` the successor of `x`, on a path whose tests say `x < b`? -/
def isSuccessorBelow (facts : List Expr) (x b v : Expr) : MetaM Bool := do
  let v := v.consumeMData
  unless v.isAppOf ``HAdd.hAdd || v.isAppOf ``Add.add || v.isAppOf ``Nat.add ||
      v.isAppOf ``Nat.succ do
    return false
  unless ← factIs v (← mkAppM ``HAdd.hAdd #[x, mkNatLit 1]) do return false
  for f in facts do
    for b' in ← factBounds x f do
      if ← factIs b' b then return true
  return false

/-- How a `while` loop is a structural recursion: the place of its counter in the state,
    and how the counter moves.  With `bound := none` the counter goes **down** by one on
    every path that goes on; with `bound := some b` it goes **up** by one, on paths that
    have tested it below `b`, an expression that does not depend on the state (so the loop
    is the `for` over the range from the counter to `b`). -/
structure WhileCounter where
  path : List Bool
  bound : Option Expr

/-- The counter of a `while` loop whose state `s : β` has the step `step` (a Lean
    expression in the free variable `s`, as `forInBodyAux β true` gives it): the first
    `Nat` component of the state that every path going on with the loop replaces by its
    predecessor, or else the first one that every such path replaces by its successor
    under a test that it is below a bound that does not depend on the state (see the
    module header).  `none` when there is none: the loop is not a structural recursion. -/
def whileCounter? (β s step : Expr) : MetaM (Option WhileCounter) := do
  let paths ← natStatePaths β
  for p in paths do
    let x ← stateComponent s p
    if ← yieldsAll p (fun facts v => isPredecessor facts x v) [] step then
      return some { path := p, bound := none }
  -- counting up: the bounds tested on the paths, which may mention the variables in
  -- scope at the loop, but not the state
  let lctx ← getLCtx
  let closed (b : Expr) : Bool :=
    !b.containsFVar s.fvarId! && !(b.hasAnyFVar fun fv => !lctx.contains fv)
  for p in paths do
    let x ← stateComponent s p
    let cands ← IO.mkRef (#[] : Array Expr)
    discard <| yieldsAll p (fun facts _ => do
      for f in facts do
        for b in ← factBounds x f do
          if closed b then cands.modify (·.push b)
      return true) [] step
    for b in ← cands.get do
      if ← yieldsAll p (fun facts v => isSuccessorBelow facts x b v) [] step then
        return some { path := p, bound := some b }
  return none

/-- The error for a `while` loop that is not a structural recursion. -/
def whileNotStructuralError {α} : MetaM α :=
  throwError "`#leanscript_to_term`: this `while` / `repeat` loop is not a structural \
    recursion, so it is rejected.  A loop is accepted only when some `Nat` variable `x` of \
    its state (a `let mut`) moves by one on every path that goes on with the loop: down, \
    to `x - 1` after a test that `x ≠ 0` (`while x > 0`, `if x == 0 then break`, …) or to \
    `n` in the case `n + 1` of a `match` on `x`; or up, to `x + 1` after a test `x < b` \
    (or `x ≤ b`) whose bound `b` the loop does not change.  No fuel and no termination \
    measure are supported."

/-- The step of a loop `forIn Lean.Loop.mk init body` in `Id` at the state `s`, and its
    counter: the loop must be a structural recursion (`whileCounter?`), and is rejected
    otherwise. -/
def whileStepAndCounter (β body s : Expr) : MetaM (Expr × WhileCounter) := do
  let step ← forInBodyAux β true (mkApp2 body (mkConst ``Unit.unit) s)
  let some p ← whileCounter? β s step | whileNotStructuralError
  return (step, p)

/-- Reject every `while` loop in `e` that is not a structural recursion.  This is for code
    the translation would otherwise drop without looking at it — `do` in `Id` reads
    `x ← m; k x` as `k m`, so a loop whose result is never used would vanish — so that a
    loop is accepted only when it is a structural recursion, used or not. -/
def checkWhileLoops (e : Expr) : MetaM Unit := do
  discard <| Meta.transform e (pre := fun e => do
    if e.isAppOf ``ForIn.forIn then
      let args := e.getAppArgs
      if args.size ≥ 8 && args[0]!.consumeMData.isConstOf ``Id then
        if (← whnfR args[1]!).consumeMData.isConstOf ``Lean.Loop then
          let init := args[args.size - 2]!
          let β ← inferType init
          withLocalDeclD `state β fun s => do
            discard <| whileStepAndCounter β args[args.size - 1]! s
    return .continue)

/-- A `while` loop with initial state `init : β`, state variable `s` and step `step`,
    with the counter `w`: the recursion on the number of iterations the counter allows
    plus one — `x₀ + 1` for a counter going down from `x₀`, `b - x₀ + 1` for one going up
    from `x₀` below `b` — whose value is the step after each iteration, of which the state
    is read (`LeanScript.loop_forIn_eq_natRec`). -/
def whileAsNatRec (β init s step : Expr) (w : WhileCounter) : MetaM Expr := do
  let x₀ ← stateComponent init w.path
  let span ← match w.bound with
    | none => pure x₀
    | some b => mkAppM ``HSub.hSub #[b, x₀]
  let bound ← mkAppM ``HAdd.hAdd #[span, mkNatLit 1]
  withLocalDeclD `i (mkConst ``Nat) fun i =>
    rangeForInBreakAsNatRec β bound init i s step

end LeanScript.ToTerm
