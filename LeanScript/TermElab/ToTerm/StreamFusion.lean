module

public meta import LeanScript.TermElab.ToTerm.Fusion

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: fusing an unfold (a stream with a step function) into an array fold

A stream written as an *unfold* — a structure with a state, a seed and a step function
`step : State → Option (State × α)` (`structure Unfold α where State : Type; seed : State;
step : …`, `Tests/SnapshotsPBOPure/Fusion02.lean`) — cannot be a value of the language: one
of its fields is a type (the state is existential).  Neither can the loops that drive it,
which are defined by well-founded recursion on a measure of the state.  This file removes
both, before the expression translator (`LeanScript.TermElab.ToTerm.Expr`) sees them, by
turning a whole pipeline into one `Array.foldl`.

The rewrite is driven by the *bodies* of the definitions (their unfolding equations
`g.eq_def`), not by their names:

* **the drain** (`fuseStreamDrain?`): a call `g … u … s … acc …` of a definition of the
  program by well-founded recursion whose body is a case analysis of `u.step s` (one field of
  the structure `u`, applied to the parameter `s`) such that
  - `none ↦ acc` (a parameter, the accumulator), and
  - `some (s', a) ↦ g … u … s' … G(a, acc) …` (a self call that changes only `s` and `acc`,
    with `G` not mentioning `s'`),

  is `foldl G acc` over the elements of the stream `u` from the state `s`
  (`toArrayLoop u s acc` with `G = acc.push a`).

* **a transformer** (`consumerFor`): a stream `v` whose step (after `headNorm`, which inlines
  the helpers `mapU`, `filterMapU`, … that build the structure) is, at a fresh state `s`, a case
  analysis of `w.step s` for an inner stream `w` (possibly through a definition by
  well-founded recursion, whose equation is unfolded: `filterMapStep`), with
  - `none ↦ none` (the stream ends where the inner one ends), and
  - `some (s', a) ↦ R`, where `R` is a tree of `if`/`match`/`let` (not mentioning `s'`) whose
    leaves are `some (s', b)` (*emit* `b`) or the same step at `s'` (*skip*: the self call of
    the definition by well-founded recursion with only `s` changed to `s'`).

  A consumer `K acc b` of the elements of `v` is then the consumer of the elements of `w`
  that is `R` with *emit* `b` replaced by `K acc b` and *skip* by `acc`.

* **the source**: a stream whose step at `s` is
  `if h : s < arr.size then some (s + 1, arr[s]) else none` (`fromArray`): its elements from
  the state `s₀` are those of `arr` from the index `s₀`, so the consumer `K` is folded by
  `Array.foldl K acc arr s₀`.

The state is threaded unchanged from the drain to the source (every transformer steps the
inner stream at the state it is at and goes on from the state that one returns), so the start
of the fold is the state the drain is called at (`u.seed`, which reduces to `0`).

None of this is checked by Lean (the translator is not verified); the differential checks of
`leanscript --check` compare the JavaScript with Lean.
-/

open Lean Meta

namespace LeanScript.Gen

/-- Is `c` a definition of the program by well-founded recursion? -/
def isWfHelper (c : Name) : MetaM Bool := do
  if ← isLibraryDecl c then return false
  return (Elab.WF.eqnInfoExt.find? (← getEnv) c).isSome

/-- The right-hand side of the unfolding equation of `c` at the arguments `args` (all its
    parameters); `none` when there is no such equation. -/
def unfoldEqRhs? (c : Name) (lvls : List Level) (args : Array Expr) : MetaM (Option Expr) := do
  let some eq ← getUnfoldEqnFor? c (nonRec := true) | return none
  let info ← getConstInfo eq
  let ty := info.type.instantiateLevelParams info.levelParams lvls
  let ty ← instantiateForall ty args
  let ty ← whnfR ty
  let some (_, lhs, rhs) := ty.eq? | return none
  unless lhs.getAppFn.isConstOf c do return none
  return some rhs

/-- `t` is `v.i x` (a projection of a field of a structure that is not a class, applied to
    `x`): the structure `v` and the field `i`. -/
def stepCallOf? (env : Environment) (t : Expr) (x : Expr) : Option (Expr × Nat) := Id.run do
  unless t.isApp && t.appArg! == x do return none
  let f := t.appFn!
  match f with
  | .proj _ i v => return some (v, i)
  | _ =>
    let .const c _ := f.getAppFn | return none
    let some info := env.getProjectionFnInfo? c | return none
    if info.fromClass then return none
    if f.getAppNumArgs != info.numParams + 1 then return none
    return some (f.appArg!, info.i)

/-- The first subterm `v.i x` of `e` (see `stepCallOf?`): the subterm, `v` and `i`. -/
def findStepCall? (e : Expr) (x : Expr) : MetaM (Option (Expr × Expr × Nat)) := do
  let env ← getEnv
  let some t := e.find? (fun t => (stepCallOf? env t x).isSome) | return none
  let some (v, i) := stepCallOf? env t x | return none
  return some (t, v, i)

/-- Reduce the `match` at the head of `e` (its discriminants are constructor applications). -/
def reduceHeadMatch (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).headBeta.consumeMData
  match ← reduceMatcher? e with
  | .reduced e' => return e'.headBeta
  | _ => return e

/-- The expression `e` split on its subterm `d : Option (σ × α)`: the branch where `d` is
    `none`, and `k s' a` called with the branch where `d` is `some (s', a)` (`s'`, `a` fresh
    locals). -/
def splitOnOption? {β : Type} (e d : Expr) (k : Expr → Expr → Expr → Expr → MetaM (Option β)) :
    MetaM (Option β) := do
  let dt ← whnfR (← instantiateMVars (← inferType d))
  unless dt.isAppOfArity ``Option 1 do return none
  let lvls := dt.getAppFn.constLevels!
  let pt ← whnfR dt.appArg!
  unless pt.isAppOfArity ``Prod 2 do return none
  let σ := pt.appFn!.appArg!
  let α := pt.appArg!
  let abs ← kabstract e d
  unless abs.hasLooseBVars do return none
  let noneBr ← reduceHeadMatch (abs.instantiate1 (mkApp (mkConst ``Option.none lvls) pt))
  withLocalDeclD `s' σ fun s' => withLocalDeclD `a α fun a => do
    let p ← mkAppM ``Prod.mk #[s', a]
    let someBr ← reduceHeadMatch (abs.instantiate1 (mkApp2 (mkConst ``Option.some lvls) pt p))
    k noneBr someBr s' a

/-- The tree `e` of `if`/`match`/`let` with every leaf replaced by `leaf` of it, at the result
    type `resTy`; `none` when a leaf is not accepted by `leaf`, or a condition, discriminant or
    bound value mentions one of `avoid`. -/
partial def mapBranches (resTy : Expr) (avoid : Array FVarId) (leaf : Expr → MetaM (Option Expr))
    (e : Expr) : MetaM (Option Expr) := do
  let e := (← instantiateMVars e).headBeta
  if let some r ← leaf e then return some r
  let ok (x : Expr) : Bool := !avoid.any x.containsFVar
  let go := mapBranches resTy avoid leaf
  match e with
  | .mdata _ b => go b
  | .letE n t v b _ =>
    unless ok v do return none
    withLetDecl n t v fun x => do
      let some b' ← go (b.instantiate1 x) | return none
      return some (← mkLetFVars #[x] b')
  | _ =>
    let args := e.getAppArgs
    let lvl ← getLevel resTy
    if e.isAppOfArity ``ite 5 then
      unless ok args[1]! do return none
      let some t ← go args[3]! | return none
      let some f ← go args[4]! | return none
      return some (mkAppN (mkConst ``ite [lvl]) #[resTy, args[1]!, args[2]!, t, f])
    if e.isAppOfArity ``cond 4 then
      unless ok args[1]! do return none
      let some t ← go args[2]! | return none
      let some f ← go args[3]! | return none
      return some (mkAppN (mkConst ``cond [lvl]) #[resTy, args[1]!, t, f])
    if e.isAppOfArity ``dite 5 then
      unless ok args[1]! do return none
      let br (k : Expr) : MetaM (Option Expr) := do
        let .lam n d b bi := k | return none
        withLocalDecl n bi d fun h => do
          let some b' ← go (b.instantiate1 h) | return none
          return some (← mkLambdaFVars #[h] b')
      let some t ← br args[3]! | return none
      let some f ← br args[4]! | return none
      return some (mkAppN (mkConst ``dite [lvl]) #[resTy, args[1]!, args[2]!, t, f])
    if let some m ← matchMatcherApp? e then
      unless m.remaining.isEmpty do return none
      unless m.discrs.all ok && m.params.all ok do return none
      -- a motive that does not depend on the discriminants
      let some motive' ← lambdaTelescope m.motive fun xs b => do
          if xs.size != m.discrs.size then return none
          if b.hasAnyFVar (xs.contains <| .fvar ·) then return none
          return some (← mkLambdaFVars xs resTy)
        | return none
      let uElim ← getLevel resTy
      let mut alts : Array Expr := #[]
      for alt in m.alts, n in m.altNumParams do
        let some alt' ← lambdaBoundedTelescope alt n fun ys b => do
            let some b' ← go b | return none
            return some (← mkLambdaFVars ys b')
          | return none
        alts := alts.push alt'
      let uElimPos? := m.uElimPos?
      let lvls := match uElimPos? with
        | some p => m.matcherLevels.set! p uElim
        | none => m.matcherLevels
      return some { m with motive := motive', alts, matcherLevels := lvls }.toExpr
    return none

/-- The source of a stream: its step function `stepFn` at a fresh state `s` is
    `if h : s < arr.size then some (s + 1, arr[s]) else none`; the array `arr`. -/
def arraySource? (stepFn : Expr) : MetaM (Option Expr) := do
  let .forallE _ σ _ _ ← whnf (← inferType stepFn) | return none
  withLocalDeclD `s σ fun s => do
    let body ← headNorm (stepFn.beta #[s])
    unless body.isAppOfArity ``dite 5 do return none
    let args := body.getAppArgs
    let c ← instantiateMVars args[1]!
    unless c.isAppOfArity ``LT.lt 4 && c.appFn!.appArg! == s do return none
    let sz := c.appArg!
    unless sz.isAppOfArity ``Array.size 2 do return none
    let arr := sz.appArg!
    let .lam _ hTy t _ := args[3]! | return none
    let .lam _ hTy' f _ := args[4]! | return none
    let okT ← withLocalDeclD `h hTy fun h => do
      let t := (t.instantiate1 h).headBeta
      unless t.isAppOfArity ``Option.some 2 do return false
      let p := t.appArg!
      unless p.isAppOfArity ``Prod.mk 4 do return false
      let pa := p.getAppArgs
      unless ← isDefEq pa[2]! (mkNatAdd s (mkNatLit 1)) do return false
      let x := pa[3]!
      unless x.isAppOfArity ``GetElem.getElem 8 do return false
      let xa := x.getAppArgs
      return xa[5]! == arr && xa[6]! == s
    unless okT do return none
    let okF ← withLocalDeclD `h hTy' fun h =>
      return (f.instantiate1 h).headBeta.isAppOfArity ``Option.none 1
    unless okF do return none
    return some arr

/-- The consumer of the elements of the stream `v` (whose step is its field `i`) that runs the
    consumer `K : accTy → β → accTy` of the elements of the stream it transforms, down to the
    source: the array of the source and that consumer of its elements (see the module doc). -/
partial def consumerFor (v : Expr) (i : Nat) (K : Expr) (accTy : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let v ← headNorm v
  let .const ctor _ := v.getAppFn | return none
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | return none
  unless v.getAppNumArgs == cinfo.numParams + cinfo.numFields do return none
  let stepFn := v.getAppArgs[cinfo.numParams + i]!
  if let some arr ← arraySource? stepFn then return some (arr, K)
  let .forallE _ σ _ _ ← whnf (← inferType stepFn) | return none
  withLocalDeclD `s σ fun s => do
    let mut body ← headNorm (stepFn.beta #[s])
    -- a step that is a definition by well-founded recursion: its unfolding, and the self call
    let mut self? : Option (Name × Array Expr × Nat) := none
    if let .const g lvls := body.getAppFn then
      if ← isWfHelper g then
        let args := body.getAppArgs
        let some j := args.findIdx? (· == s) | return none
        let some rhs ← unfoldEqRhs? g lvls args | return none
        self? := some (g, args, j)
        body := rhs
    let some (t, w, i') ← findStepCall? body s | return none
    if w.containsFVar s.fvarId! then return none
    let some Kw ← splitOnOption? body t fun noneBr someBr s' a => do
        unless noneBr.consumeMData.isAppOfArity ``Option.none 1 do return none
        withLocalDeclD `acc accTy fun acc => do
          let leaf (e : Expr) : MetaM (Option Expr) := do
            let e := e.consumeMData
            if e.isAppOfArity ``Option.some 2 then
              let p := e.appArg!.consumeMData
              if p.isAppOfArity ``Prod.mk 4 && p.appFn!.appArg! == s' then
                let b := p.appArg!
                if !b.containsFVar s'.fvarId! then
                  return some (K.beta #[acc, b]).headBeta
            if let some (g, args, j) := self? then
              if e.isAppOf g && e.getAppNumArgs == args.size then
                let eargs := e.getAppArgs
                if eargs[j]! == s' && (List.range args.size).all
                    (fun k => k == j || eargs[k]! == args[k]!) then
                  return some acc
            return none
          let some r ← mapBranches accTy #[s'.fvarId!] leaf someBr | return none
          -- the consumer must not read the states
          if r.containsFVar s.fvarId! || r.containsFVar s'.fvarId! then return none
          return some (← mkLambdaFVars #[acc, a] r)
      | return none
    consumerFor w i' Kw accTy

/-- A call `g … u … s … acc …` of a definition by well-founded recursion that drains the stream
    `u` from the state `s` into the accumulator `acc` (see the module doc), with the stream a
    pipeline over an array: the `Array.foldl` of the fused consumer over that array. -/
def fuseStreamDrain? (e : Expr) : MetaM (Option Expr) := do
  let .const g lvls := e.getAppFn | return none
  unless ← isWfHelper g do return none
  let actuals := e.getAppArgs
  let info ← getConstInfo g
  let ty := info.type.instantiateLevelParams info.levelParams lvls
  -- the parameters that are values become locals; types and instances stay as they are
  let rec abstr (ty : Expr) (k : Nat) (xs : Array Expr) (args : Array Expr) :
      MetaM (Option Expr) := do
    if h : k < actuals.size then
      let .forallE n d b bi ← whnf ty | return none
      let a := actuals[k]
      if (← isType a) || (← isProp d) || bi.isInstImplicit || (← isProof a) then
        abstr (b.instantiate1 a) (k + 1) xs (args.push a)
      else
        withLocalDecl n .default d fun x =>
          abstr (b.instantiate1 x) (k + 1) (xs.push x) (args.push x)
    else
      if actuals.size != (← getConstInfo g).type.getForallBinderNames.length then return none
      let some rhs ← unfoldEqRhs? g lvls args | return none
      -- the case analysis of `u.step s`, `u` and `s` parameters
      let some (t, sVar, uVar, i) ← (do
          for s in xs do
            if let some (t, u, i) ← findStepCall? rhs s then
              if u.isFVar && xs.contains u then return some (t, s, u, i)
          return none : MetaM (Option (Expr × Expr × Expr × Nat)))
        | return none
      let some jS := args.findIdx? (· == sVar) | return none
      let some jU := args.findIdx? (· == uVar) | return none
      splitOnOption? rhs t fun noneBr someBr s' a => do
        let noneBr := noneBr.consumeMData
        let some jAcc := args.findIdx? (· == noneBr) | return none
        unless xs.contains noneBr && jAcc != jS && jAcc != jU do return none
        let someBr := someBr.consumeMData
        unless someBr.isAppOf g && someBr.getAppNumArgs == args.size do return none
        let rargs := someBr.getAppArgs
        unless rargs[jS]! == s' do return none
        unless (List.range args.size).all (fun k => k == jS || k == jAcc || rargs[k]! == args[k]!) do
          return none
        let G := rargs[jAcc]!
        if G.containsFVar s'.fvarId! || G.containsFVar sVar.fvarId! ||
            G.containsFVar uVar.fvarId! then
          return none
        let accTy ← inferType noneBr
        let aTy ← inferType a
        let Ktop ← withLocalDeclD `acc accTy fun acc => withLocalDeclD `b aTy fun b =>
          mkLambdaFVars #[acc, b] (G.replaceFVars #[noneBr, a] #[acc, b])
        -- the other parameters are their values
        let Ktop := Ktop.replaceFVars xs (xs.map fun x => actuals[args.idxOf x]!)
        let some (arr, Ksrc) ← consumerFor actuals[jU]! i Ktop accTy | return none
        let s0 ← headNorm actuals[jS]!
        let acc0 := actuals[jAcc]!
        let size ← mkAppM ``Array.size #[arr]
        let r ← mkAppOptM ``Array.foldl #[none, accTy, Ksrc, acc0, arr, s0, size]
        return some (← Core.betaReduce r)
  abstr ty 0 #[] #[]

end LeanScript.Gen

end
