module

public meta import LeanScript.TermElab.ToTerm.Expr.Ctor

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: case analyses, recursive calls and nested folds

The translation of `casesOn`/`match`, of recursive calls, and of folds over nested
containers, parameterised by the expression translator `tr`
(`LeanScript.TermElab.ToTerm.Expr`).
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

/-- The syntax of the reading of the Lean type `T`, when it has one (the type of a branch, for
    the join point of the rest of the computation). -/
def tyOf? (L : Loc) (T : Expr) : TM (Option Lean.Term) := do
  try return some (← (← cirOf L T false).stx L.c #[]) catch _ => return none

variable (tr : Loc → Expr → TM Src)

/-- A view of `x a₁ … aₙ`, where `x` is a field that holds members of the block inside a
    function or an array (`Loc.nest`): its term and what it holds. -/
partial def nestView? (L : Loc) (e : Expr) : TM (Option (Src × NShape)) := do
  let e := (← instantiateMVars e).headBeta
  let .fvar x := e.getAppFn | return none
  let some s := L.nest[x]? | return none
  let some i := L.index? x | return none
  let mut t ← varStx i
  let mut s := s
  for a in e.getAppArgs do
    match s with
    | .fn s' =>
      t := Src.app t (← tr L a)
      s := s'
    | _ => fail m!"cannot translate the application{indentExpr e}"
  return some (t, s)

/-- `Array.foldl f z xs 0 xs.size`: `Comp.array_foldl`, whose step binds the element (`#0`) and
    the accumulator (`#1`) and is the translation of `f acc x`. -/
partial def trFoldl (L : Loc) (args : Array Expr) : TM Src := do
  let elemTy := args[0]!
  let accTy := args[1]!
  discard <| cirOf L accTy
  let arr ← tr L args[4]!
  let z ← tr L args[3]!
  withLocalDeclD `acc accTy fun acc => withLocalDeclD `x elemTy fun x => do
    let body := (mkApp2 args[2]! acc x).headBeta
    return Src.arrayFoldl arr z (← tr ((L.bind acc.fvarId!).bind x.fvarId!) body)

/-- `Array.foldl f z xs` over an array `xs` that holds members of the block recursed on (with
    their answers): `Comp.array_foldl`, whose step sees each element as the subvalue, with the
    answer at it for the recursive calls. -/
partial def trNestFoldl (L : Loc) (arr : Src) (s : NShape) (args : Array Expr) :
    TM Src := do
  let elemTy := args[0]!
  let accTy := args[1]!
  discard <| cirOf L accTy
  let z ← tr L args[3]!
  withLocalDeclD `acc accTy fun acc => withLocalDeclD `x elemTy fun x => do
    let body := (mkApp2 args[2]! acc x).headBeta
    let L1 := L.bind acc.fvarId!
    match s with
    | .hole =>
      let L2 := ((L1.bind none).bind none).bind x.fvarId!
      let L2 := { L2 with ans := L2.ans.insert x.fvarId! (L2.slots.size - 2) }
      return Src.arrayFoldl arr z (Src.recordCases (.var 0) 2 (← tr L2 body))
    | s' =>
      let L2 := L1.bind x.fvarId!
      let L2 := { L2 with nest := L2.nest.insert x.fvarId! s' }
      return Src.arrayFoldl arr z (← tr L2 body)

/-- A recursive call `f … y …` on a subvalue `y` the recursion reached: the variable of its
    answer. -/
partial def trRecCall (L : Loc) (e : Expr) : TM Src := do
  let args := e.getAppArgs
  let n := L.params.size
  -- a partial application may leave out trailing parameters that the recursion changes: the
  -- answer is then a function of them
  for i in [args.size:n] do
    unless L.vary.contains i do
      fail m!"the recursive call{indentExpr e}\nis not fully applied"
  let mut out? : Option Src := none
  let mut varyArgs : Array Src := #[]
  for i in [0:min args.size n] do
    let a := args[i]!
    if L.idxParams.contains i then continue
    if L.vary.contains i then
      varyArgs := varyArgs.push (← tr L a)
      continue
    if a == L.params[i]! then continue
    if out?.isNone then
      if let .fvar y := a then
        if let some slot := L.ans[y]? then
          out? := some (← varStx (L.slots.size - 1 - slot))
          continue
      -- a member held inside a function field: the answer is next to the subvalue
      if let some (t, .hole) ← nestView? tr L a then
        out? := some (Src.recordCases t 2 (.var 1))
        continue
      -- a member read through a field `Fin m → X` (as `Nat → Option X`): the answer at the
      -- `Option X` is `none` or `some` of the answer at `X`; below `m` it is `some`, and the
      -- unreachable `none` gets the default of the answer type
      if let some (t, .optHole) ← nestView? tr L a then
        unless L.vary.isEmpty && args.size == n do
          fail m!"the recursive call{indentExpr e}\non a value read through a field `Fin m → _` \
            must pass the other parameters unchanged"
        let d ← defaultTerm tr L (← inferType e) m!"the recursive call{indentExpr e}"
        out? := some (Src.unionCases (← tyOf? L (← inferType e))
          (Src.recordCases t 2 (.var 1)) #[(0, d), (1, .var 0)])
        continue
    fail m!"the recursive call{indentExpr e}\nis not structural: it must pass the parameters \
      unchanged except the one recursed on, which must be a direct subvalue of it"
  let some t := out? | fail m!"the recursive call{indentExpr e}\ndoes not recurse on a subvalue"
  -- the answer is a function of the parameters that change, then applied to the arguments
  -- beyond the parameters (`ack2 m n` for `ack2 : Nat → (Nat → Nat)`)
  let extra ← args[n:].toArray.mapM (tr L)
  appStx t (varyArgs ++ extra)

/-- The case analysis of `y` at the top of the body `e` of the function `g` (through the
    `match` it is compiled from). -/
partial def peelCases (g : Name) (y e : Expr) : TM (Name × Array Expr) := do
  let e := (← instantiateMVars e).headBeta
  if let .mdata _ e := e then return ← peelCases g y e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if let .const c lvls := fn then
    if isCasesOnRecursor (← getEnv) c then
      let ind ← getConstInfoInduct c.getPrefix
      let nP := ind.numParams + ind.numIndices
      if args.size > nP + 1 && args[nP + 1]! == y then
        return (c, args)
    if ← isMatcher c then
      let info ← getConstInfo c
      let v := info.value!.instantiateLevelParams info.levelParams lvls
      return ← peelCases g y (← Core.betaReduce (v.beta args))
  fail m!"`{g}` must match on the parameter it recurses on at the top of its body"

/-- The branch of the fold at one member: the case analysis `c args` of the parameter recursed
    on, at the top of the body of the member's function.  Its fields are opened as windows
    (`openWindows`), and the parameter is the constructor application in each branch. -/
partial def recBranch (L : Loc) (c : Name) (args : Array Expr) : TM Src := do
  let ind ← getConstInfoInduct c.getPrefix
  let nP := ind.numParams + ind.numIndices
  let nM := ind.ctors.length
  unless args.size ≥ nP + 2 + nM do fail m!"`{c}` is not fully applied"
  let major := args[nP + 1]!
  let extra := args[nP + 2 + nM:].toArray
  let minors := args[nP + 2 : nP + 2 + nM].toArray
  let T ← normType (← inferType major) false
  let plan ← lm (planType T L.prog?)
  let ctorInfos ← ind.ctors.toArray.mapM getConstInfoCtor
  let ps := T.getAppArgs[:ind.numParams].toArray
  -- the parameters the recursive calls change are bound after the body of the member (the
  -- answer is a function of them)
  let vps := L.vary.map (L.params[·]!)
  withVaryLocals (L.bind none) (mkAppN (mkConst ``Unit) vps) fun Lb vs => do
    let vs := vs.getAppArgs
    let brs ← (List.range nM).toArray.mapM fun k => do
      let ci := ctorInfos[k]!
      let erased ← ctorErasedMask ci.name T.getAppFn.constLevels! ps
      withFields ind T major ci.name minors[k]! extra fun xs body => do
        let body := body.replaceFVar major
          (mkAppN (mkAppN (mkConst ci.name T.getAppFn.constLevels!) ps) xs)
        openWindows Lb L.mems xs erased L.depth (tr · (body.replaceFVars vps vs))
    casesSrc plan (← varStx vps.size) brs none

/-- A case analysis `T.casesOn motive major minors…`. -/
partial def trCases (L : Loc) (c : Name) (args : Array Expr) (e : Expr) : TM Src := do
  let ind ← getConstInfoInduct c.getPrefix
  -- the indices of a family are erased: they are skipped, and so are the fields that only
  -- name an index (`erasedFields`)
  let nP := ind.numParams + ind.numIndices
  let nM := ind.ctors.length
  unless args.size ≥ nP + 2 + nM do fail m!"`{c}` is not fully applied"
  let major := args[nP + 1]!
  let extra := args[nP + 2 + nM:].toArray
  let minors := (args[nP + 2 : nP + 2 + nM].toArray).map fun m => m
  let T ← normType (← inferType major) false
  let ps := T.getAppArgs[:ind.numParams].toArray
  let ctorInfos ← ind.ctors.toArray.mapM getConstInfoCtor
  let masks ← ind.ctors.toArray.mapM fun ctor =>
    ctorErasedMask ctor T.getAppFn.constLevels! ps
  -- open a branch: its fields as locals, the extra arguments pushed inside
  let openMinor {α : Type} (k : Nat) (m : Expr)
      (kont : Array Expr → Array Bool → Expr → TM α) : TM α := do
    withFields ind T major ctorInfos[k]!.name m extra fun xs b => kont xs masks[k]! b
  let recPos? := L.recParam? major minors
  -- in a branch of the case analysis of a parameter recursed on, the parameter is the
  -- constructor application
  let subst (k : Nat) (xs : Array Expr) (body : Expr) : Expr :=
    if recPos?.isSome then
      body.replaceFVar major (mkAppN (mkAppN (mkConst ctorInfos[k]!.name T.getAppFn.constLevels!)
        ps) xs)
    else body
  if ind.name == ``Nat then
    -- the parameters the recursive calls change: the answer is a function of them
    let vary ← match recPos? with
      | some p => varyingParams L p minors
      | none => pure #[]
    let Lv := if recPos?.isSome then { L with vary } else L
    let z ← openMinor 0 minors[0]! fun _ _ b => withVaryLocals Lv (subst 0 #[] b) tr
    let s ← openMinor 1 minors[1]! fun xs _ b => do
      let m := xs[0]!
      let L' := (Lv.bind m.fvarId!).bind none
      let L' := if recPos?.isSome then { L' with ans := L'.ans.insert m.fvarId! (L'.slots.size - 1) }
        else L'
      withVaryLocals L' (subst 1 xs b) tr
    if vary.isEmpty then
      return Src.natRec none (← tr L major) z s
    let ps := vary.map (L.params[·]!)
    let ρ ← tyStx L (← mkForallFVars ps (← inferType e))
    let r := Src.natRec (some ρ) (← tr L major) z s
    return ← appStx r (← ps.mapM (tr L))
  let plan ← lm (planType T L.prog?)
  if plan.data?.isSome then modify fun st => { st with usesData := true }
  -- a case analysis of a subvalue inside a window of a course-of-values recursion: its body
  -- is already there, its holes are windows one level shallower
  if let .fvar h := major then
    if let some (bodySlot, d) := L.win[h]? then
      let brs ← (List.range nM).toArray.mapM fun k => openMinor k minors[k]! fun xs erased body => do
        let ctorApp := mkAppN (mkAppN (mkConst ctorInfos[k]!.name T.getAppFn.constLevels!)
          ps) xs
        let body := body.replace fun s => if s == ctorApp then some major else none
        openWindows L L.mems xs erased d (tr · body)
      return ← casesSrc plan (← varStx (L.slots.size - 1 - bodySlot)) brs
        (← tyOf? L (← inferType e))
  -- structural recursion on a declared datatype: one fold of its whole block, whose branch
  -- at each member is the body of the function of the group that recurses on that member
  if let (some p, some (b, j)) := (recPos?, plan.data?) then
    let prog := L.prog?.get!
    let mems ← prog.members[b]!.mapM fun m => (normType m : MetaM Expr)
    let assign ← groupByMember L p mems
    -- the parameters the recursive calls change (in the body of any function of the group):
    -- the answers are functions of them
    let mut vary0 : Array Nat := #[]
    for i in [0:mems.size] do
      let some g := assign[i]! | continue
      let some eqn ← getUnfoldEqnFor? g (nonRec := true)
        | fail m!"`{g}` is not a definition that can be unfolded"
      let eqTy ← inferType (mkConst eqn)
      let v ← withLocalDeclD `y mems[i]! fun y => do
        let eq ← instantiateForall eqTy (L.params.set! p y)
        let some (_, _, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{g}`"
        varyingParams L p #[rhs]
      for q in v do unless vary0.contains q do vary0 := vary0.push q
    let vary := vary0.qsort (· < ·)
    let ps := vary.map (L.params[·]!)
    let L0 := { L with mems, vary }
    let mut ρs : Array Lean.Term := #[]
    let mut brs : Array Src := #[]
    for i in [0:mems.size] do
      match assign[i]! with
      | none =>
        -- a member `Option X` for a member `X` read through a field `Fin m → X` (as
        -- `Nat → Option X`): its answer is `none` or `some` of the answer at `X`
        if let some ρX ← optMemberAnswer L p mems assign i then
          unless vary.isEmpty do
            fail m!"a recursion through a field `Fin m → _` must pass the parameters other \
              than the one recursed on unchanged"
          ρs := ρs.push (← `(LeanScript.Ty.option $ρX))
          brs := brs.push (Src.unionCases none (.var 0)
            #[(0, Src.unionMk (some 0) (← `(LeanScript.CtorIx.two₁)) #[]),
              (1, Src.recordCases (.var 0) 2
                (Src.unionMk (some 1) (← `(LeanScript.CtorIx.two₂)) #[.var 1]))])
          continue
        -- no function of the group recurses on this member: its answers are never read
        ρs := ρs.push (← `(LeanScript.Ty.bool))
        brs := brs.push (Src.boolLit true)
      | some g =>
        let some eqn ← getUnfoldEqnFor? g (nonRec := true)
          | fail m!"`{g}` is not a definition that can be unfolded"
        let eqTy ← inferType (mkConst eqn)
        let (ρ, br) ← withLocalDeclD `y mems[i]! fun y => do
          let params := L.params.set! p y
          let eq ← instantiateForall eqTy params
          let some (_, _, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{g}`"
          let ρ ← tyStx L (← mkForallFVars ps (← inferType (mkAppN (mkConst g) params)))
          let (c', args') ← peelCases g y rhs
          return (ρ, ← recBranch tr { L0 with params } c' args')
        ρs := ρs.push ρ
        brs := brs.push br
    let ρFun ← if ρs.size = 1 then `(fun _ => $(ρs[0]!)) else finFunStx ρs
    let Δ := mkIdent (prog.name ++ `Δ)
    let bref ← brefStx L.c b
    let depth := L.depth
    let r : Src := .dataRec (some Δ) bref ρFun (if depth = 0 then none else some (quote depth))
      brs (quote j) (← tr L major)
    return ← appStx r (← ps.mapM (tr L))
  -- an ordinary case analysis
  let mut scrut ← tr L major
  if let some (b, j) := plan.data? then
    scrut := Src.dataOut (← brefStx L.c b) (quote j) scrut
  let brs ← (List.range nM).toArray.mapM fun k => openMinor k minors[k]! fun xs erased body => do
    let kept := (xs.zip erased).filter (!·.2) |>.map (·.1)
    let mut L' := L
    for x in kept.reverse do L' := L'.bind x.fvarId!
    tr L' body
  casesSrc plan scrut brs (← tyOf? L (← inferType e))

end LeanScript.Gen

end
