module

public meta import LeanScript.TermElab.ToTerm.While

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: the expression translator

`tr` and the functions it is mutually recursive with: the translation of a Lean expression
(an application, a projection, a constructor, a recursive call, a `casesOn`/`match`, an
extern, a range `for` loop, a structurally terminating `while` loop, a fold over a nested
container, ...) to the syntax of a
`LeanScript.Term`.  See `LeanScript.TermElab.ToTerm` for the definition translator.
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

/-- The syntax of the reading of the Lean type `T`, when it has one (the type of a branch, for
    the join point of the rest of the computation). -/
def tyOf? (L : Loc) (T : Expr) : TM (Option Lean.Term) := do
  try return some (← (← cirOf L T false).stx L.c #[]) catch _ => return none

mutual

/-- The translation of an expression. -/
partial def tr (L : Loc) (e : Expr) : TM Src := do
  let e := (← instantiateMVars e).headBeta
  match e with
  | .mdata _ e => tr L e
  | .fvar x =>
    if let some (ctor, actual, canon) := (← get).unusable[x]? then
      fail m!"the field `{(← x.getUserName).eraseMacroScopes}` of `{ctor}` is used at the \
        index{indentExpr actual}\nof `{ctor.getPrefix}`: the language reads the family at one \
        index, where the field is an element of{indentExpr canon}\nso it can only be used by a \
        function generic in the index"
    if L.nest.contains x then
      fail m!"the field `{(← x.getUserName).eraseMacroScopes}` holds values of the datatype recursed on, paired \
        with the answers at them: it can only be folded (`Array.foldl`), applied, or passed \
        to a recursive call"
    if let some i := L.index? x then return ← varStx i
    fail m!"the local `{← x.getUserName}` has no value in the language (a proof, an \
      instance or an erased field)"
  | .letE n t v b _ =>
    discard <| cirOf L t
    let tv ← tr L v
    withLocalDeclD n t fun x => do
      let body ← tr (L.bind x.fvarId!) (b.instantiate1 x)
      return .letE tv body
  | .lam n t b _ =>
    -- `fun _ : Unit => b` is a lazy delay of `b` (`Unit` has one value: no variable is bound)
    if ← isUnitType t then
      let b := b.instantiate1 (mkConst ``Unit.unit)
      return ← delayCoerceTy L (← inferType b) (← inferType e) (← tr L b)
    discard <| cirOf L t
    withLocalDeclD n t fun x => do
      return Src.lam none (← tr (L.bind x.fvarId!) (b.instantiate1 x))
  | .proj S i s =>
    -- a projection of a constructor application (`(⟨j, h⟩ : Fin m).val`) is that field
    if let some e' ← Meta.reduceProj? e then
      if (← whnfR s).isApp && (← whnfR s).getAppFn.isConst &&
          (← getEnv).isConstructor (← whnfR s).getAppFn.constName! then
        return ← tr L e'
    trProj L S i s
  | _ =>
    let T ← inferType e
    if (← isProp T) || (← isType e) then
      fail m!"the proof or type{indentExpr e}\nhas no value in the language"
    -- a closed value of a leaf type is a literal
    if !e.hasFVar && !e.hasMVar && !L.mentionsFn e then
      if let .prim p ← cirOf L T false then
        let d ← instantiateMVars (← Term.elabTerm (← `(LeanPrimTy.denote $p)) none)
        if ← isDefEq T d then
          if e.isConstOf ``Bool.true then return Src.boolLit true
          if e.isConstOf ``Bool.false then return Src.boolLit false
          return ← Src.lit p (← exprToSyntax e)
        -- a closed value of a type read as a leaf without being one (a wrapper `⟨1, h⟩ : Pos`,
        -- a quotient `Quot.mk r 3`): its head normal form, whose value is the literal
        let e' ← whnf e
        if e' != e then return ← tr L e'
    trApp L e

/-- A projection `s.i` of a structure. -/
partial def trProj (L : Loc) (S : Name) (i : Nat) (s : Expr) : TM Src := do
  let T ← normType (← inferType s) false
  let plan ← lm (planType T L.prog?)
  if plan.data?.isSome then modify fun st => { st with usesData := true }
  let ctor := (getStructureCtor (← getEnv) S).name
  -- the position of the field among the fields kept
  let cinfo ← getConstInfoCtor ctor
  let mut ty ← instantiateForall (cinfo.instantiateTypeLevelParams T.getAppFn.constLevels!)
    T.getAppArgs
  let mut q := 0
  for k in [0:i + 1] do
    ty ← whnf ty
    let .forallE _ d b bi := ty | fail m!"bad projection of `{S}`"
    let erased ← isErasedField bi d
    if k = i then
      if erased then fail m!"the field {i} of `{S}` is a proof or an instance"
    else if !erased then q := q + 1
    ty := b.instantiate1 (mkProj S k s)
  let n := plan.ctors[0]!.2.size
  let mut scrut ← tr L s
  if let some (b, j) := plan.data? then
    scrut := Src.dataOut (← brefStx L.c b) (quote j) scrut
  if n = 1 then return scrut
  return Src.recordCases scrut n (← varStx q)

/-- An application. -/
partial def trApp (L : Loc) (e : Expr) : TM Src := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .fvar x =>
    if L.nest.contains x then
      let some (t, s) ← nestView? L e | fail m!"cannot translate the application{indentExpr e}"
      unless s == .hole do
        fail m!"the value{indentExpr e}\nholds values of the datatype recursed on, paired with \
          the answers at them: it can only be folded (`Array.foldl`), applied, or passed to a \
          recursive call"
      return Src.recordCases t 2 (.var 0)
    -- a field `f : Fin m → T` read as `Nat → Option T`: `f i` is `some` below `m`, and the
    -- unreachable `none` gets the default of `T`
    if (← get).optFields.contains x && args.size ≥ 1 then
      let a := args[0]!
      let T ← inferType (mkApp fn a)
      let d ← defaultTerm L T m!"the application{indentExpr e}"
      let mut scrut := Src.app (← tr L fn) (← tr L a)
      -- `Option T` is a member of the block of `T`: taken apart after `data_out`
      let plan ← lm (planType (← normType (← mkAppM ``Option #[T]) false) L.prog?)
      if let some (b, j) := plan.data? then
        modify fun st => { st with usesData := true }
        scrut := Src.dataOut (← brefStx L.c b) (quote j) scrut
      let mut r := Src.unionCases (← tyOf? L T) scrut #[(0, d), (1, .var 0)]
      for a in args[1:] do r := Src.app r (← tr L a)
      return r
    appArgs L fn (← tr L fn) args
  | .const c _ =>
    let env ← getEnv
    if L.fns.contains c then return ← trRecCall L e
    -- delays: `Thunk.pure a`, `Thunk.mk f` and `t.get` are their values up to the delays
    if (c == ``Thunk.pure || c == ``Thunk.mk || c == ``Thunk.get) && args.size ≥ 2 then
      let e₂ := mkAppN fn args[:2].toArray
      let a := args[1]!
      let r ← delayCoerceTy L (← inferType a) (← inferType e₂) (← tr L a)
      return ← appArgs L e₂ r args[2:].toArray
    if c == ``ite && args.size == 5 then
      let d := mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!
      return Src.ite (← tyOf? L (← inferType e)) (← tr L d) (← tr L args[3]!) (← tr L args[4]!)
    if c == ``cond && args.size == 4 then
      return Src.ite (← tyOf? L (← inferType e)) (← tr L args[1]!) (← tr L args[2]!)
        (← tr L args[3]!)
    -- a case analysis of a `Bool` (`Bool.rec f t b`, `Bool.casesOn b f t`) is an `if`
    if (c == ``Bool.rec || c == ``Bool.casesOn) && args.size == 4 then
      let (f, t, b) := if c == ``Bool.rec then (args[1]!, args[2]!, args[3]!)
        else (args[2]!, args[3]!, args[1]!)
      return Src.ite (← tyOf? L (← inferType e)) (← tr L b) (← tr L t) (← tr L f)
    if c == ``dite && args.size == 5 then
      let d := mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!
      let br (k : Expr) (h : Expr) : TM Src :=
        withLocalDeclD `h h fun x => tr L (mkApp k x)
      return Src.ite (← tyOf? L (← inferType e)) (← tr L d) (← br args[3]! args[1]!)
        (← br args[4]! (mkNot args[1]!))
    if c == ``Decidable.decide && args.size == 2 then
      -- `decide (b = true)` is `b`
      if let some (_, b, t) := args[0]!.eq? then
        if t.isConstOf ``Bool.true && (← isDefEq (← inferType b) (mkConst ``Bool)) then
          return ← tr L b
      return ← trDecide L args[0]! args[1]!
    -- the monad `Id`: `Id.run x` is `x`, `pure x` is `x`, and `x >>= f` is `let y := x; f y`
    if c == ``Id.run && args.size ≥ 2 then return ← tr L (mkAppN args[1]! args[2:].toArray)
    if c == ``Pure.pure && args.size ≥ 4 then
      if ← isIdMonad args[0]! then return ← tr L (mkAppN args[3]! args[4:].toArray)
    if c == ``Bind.bind && args.size ≥ 6 then
      if ← isIdMonad args[0]! then
        discard <| cirOf L args[2]!
        let tx ← tr L args[4]!
        return ← withLocalDeclD `y args[2]! fun y => do
          let body ← tr (L.bind y.fvarId!) (mkAppN (mkApp args[5]! y) args[6:].toArray)
          return .letE tx body
    -- a `for` loop over a range `[a:b:s]` in `Id`
    if c == ``ForIn.forIn && args.size == 8 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Std.Legacy.Range then
        return ← trRangeFor L args[4]! args[5]! args[6]! fun i r => pure (mkApp2 args[7]! i r)
    -- a `while` loop in `Id`: only when it is structurally terminating
    if c == ``ForIn.forIn && args.size == 8 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Lean.Loop then
        return ← trWhile L e args[4]! args[6]! args[7]!
    if c == ``ForIn'.forIn' && args.size == 9 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Std.Legacy.Range then
        return ← trRangeFor L args[5]! args[6]! args[7]! fun i r => do
          let .forallE _ _ b _ ← whnf (← inferType args[8]!) | fail m!"bad `forIn'`"
          let .forallE _ hTy _ _ ← whnf (b.instantiate1 i) | fail m!"bad `forIn'`"
          -- the proof of membership is erased: a local that the translation never reads
          withLocalDeclD `h hTy fun h => pure (mkApp3 args[8]! i h r)
    if isCasesOnRecursor env c then return ← trCases L c args e
    -- a quotient is read as its carrier (`quotCarrier?`), a value of it as a representative:
    -- `Quot.mk r a` is `a`, and a function on the quotient (`Quot.lift f h q`, `Quot.rec`, …)
    -- is `f` applied to the representative `q`
    if c == ``Quot.mk && args.size ≥ 3 then return ← tr L (mkAppN args[2]! args[3:].toArray)
    if (c == ``Quot.lift || c == ``Quot.rec) && args.size == 5 then return ← tr L args[3]!
    if (c == ``Quot.lift || c == ``Quot.rec) && args.size ≥ 6 then
      return ← trQuotApp L args[3]! args[5]! args[6:].toArray
    if (c == ``Quot.recOn || c == ``Quot.hrecOn) && args.size ≥ 5 then
      return ← trQuotApp L args[4]! args[3]! args[6:].toArray
    if c == ``Quot.recOnSubsingleton && args.size ≥ 6 then
      return ← trQuotApp L args[5]! args[4]! args[6:].toArray
    if quotDefs.contains c then
      if let some e' ← unfoldDefinition? e then return ← tr L e'
    -- an unreachable branch (`| .nil => absurd` of `Vec.head : Vec α (n + 1) → α`): after the
    -- indices are erased it is reachable, and the language has no value to put there
    if c == ``False.elim || c == ``absurd || c == ``False.rec || c == ``Empty.elim ||
        isNoConfusion env c then
      fail m!"a branch that Lean proves unreachable{indentExpr e}\nis not supported: the \
        language has no term for it (and once the indices of an inductive family are erased, \
        as `Vec α (n + 1)` is `Vec α`, a list, such a branch is reachable)"
    -- a cast along an equation is the identity on values: the `match` of an inductive family
    -- (`Vec α n`) is compiled with such casts between the indices of its patterns
    if (c == ``Eq.ndrec || c == ``Eq.rec) && args.size ≥ 6 then
      return ← tr L (mkAppN args[3]! args[6:].toArray)
    if (c == ``cast || c == ``Eq.mpr || c == ``Eq.mp) && args.size ≥ 4 then
      return ← tr L (mkAppN args[3]! args[4:].toArray)
    -- `Fin.foldl n f z`: `Comp.nat_rec` on `n`, whose step at `k` is `f acc ⟨k, _⟩`
    if c == ``Fin.foldl && args.size == 4 then
      return ← trFinFoldl L args[0]! args[1]! args[2]! args[3]!
    -- an array literal `#[a, b, …]` (`List.toArray [a, b, …]`) of values that are not leaves
    if c == ``List.toArray && args.size == 2 then
      if let some xs ← listLit? args[1]! then
        let τ ← cirOf L (← inferType e) false
        unless τ.isLeaf do
          return Src.arrayMk (← xs.mapM (tr L))
    -- a fold over an array of members of the block recursed on
    if c == ``Array.foldl && args.size == 7 then
      if let some (arr, .array s) ← nestView? L args[4]! then
        unless (← natLit? args[5]!) == some 0 &&
            (← isDefEq args[6]! (← mkAppM ``Array.size #[args[4]!])) do
          fail m!"`Array.foldl` with bounds{indentExpr e}\nis not supported"
        return ← trNestFoldl L arr s args
      -- a fold over any other array, from `0` to its size: `Comp.array_foldl`
      if (← natLit? args[5]!) == some 0 &&
          (← isDefEq args[6]! (← mkAppM ``Array.size #[args[4]!])) then
        return ← trFoldl L args
    if ← isMatcher c then
      let info ← getConstInfo c
      let v := info.value!.instantiateLevelParams info.levelParams fn.constLevels!
      return ← tr L (← Core.betaReduce (v.beta args))
    if let some (.ctorInfo cinfo) := env.find? c then
      -- a constructor of a type of two values without fields (`Decidable.isTrue h`, the proof
      -- erased) is a `.bool`: the second constructor is `true`
      if let some b ← twoPointCtor? cinfo then return Src.boolLit b
      -- a wrapper of one value (`Fin.mk n v h`, `Subtype.mk v h`, `Vector.mk a h`) is erased
      -- to that value, also when its parameters mention locals (`⟨0, h⟩ : Fin c.n`)
      if let some a ← wrapperField? cinfo args then
        unless (← cirOf L (← inferType e) false) matches .data .. do return ← tr L a
      if !((← cirOf L (← inferType e) false) matches .prim _) then
        return ← trCtor L cinfo fn args
    if let some pinfo ← getProjectionFnInfo? c then
      if !pinfo.fromClass then
        if let some e' ← unfoldDefinition? e then return ← tr L e'
    -- a call of a helper definition (not from the library): its own translation, applied
    if !(← isLibraryDecl c) then
      if let some (.defnInfo _) := env.find? c then
        return ← (try trHelperCall L c e args
          catch ex => try trExtern L e fn args catch _ => throw ex)
    trExtern L e fn args
  | .proj .. =>
    -- a projection applied to arguments (`c.data i` for a function field)
    appArgs L fn (← tr L fn) args
  | _ => fail m!"cannot translate the application{indentExpr e}"

/-- The translation `r` of `fn` applied to the arguments `args`; an argument `()` forces the
    lazy delay `Unit → τ` it is applied to. -/
partial def appArgs (L : Loc) (fn : Expr) (r : Src) (args : Array Expr) :
    TM Src := do
  let mut r := r
  for i in [0:args.size] do
    let a := args[i]!
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
  trStepLoop L β n init fun k v => do
    let ks ← if s1 then pure k else mkAppM ``HMul.hMul #[k, s]
    let i ← if a0 then pure ks else mkAppM ``HAdd.hAdd #[a, ks]
    mkBody i v

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
  trStepLoop L β n init fun _ v => pure (mkApp2 f (mkConst ``Unit.unit) v).headBeta

/-- A call `c a₁ … aₙ` of a helper definition `c`: the translation of `c` (a closed term, so
    its syntax elaborates in any context), applied to the terms of the arguments. -/
partial def trHelperCall (L : Loc) (c : Name) (e : Expr) (args : Array Expr) : TM Src := do
  if (← get).inlining.contains c || L.fns.contains c then
    fail m!"the helper `{c}` calls itself back through another definition{indentExpr e}"
  let info ← getConstInfo c
  unless info.levelParams.isEmpty do fail m!"the helper `{c}` is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? c (nonRec := true)
    | fail m!"the helper `{c}` is not a definition that can be unfolded"
  let eqTy ← inferType (mkConst eqn)
  let helper ← forallTelescope eqTy fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{c}`"
    let params := lhs.getAppArgs
    unless params == xs do fail m!"unexpected unfolding equation of `{c}`"
    unless (← indexParams xs).isEmpty do
      fail m!"the helper `{c}` has a parameter that names an index of a later parameter's type"
    for x in xs do
      if ← isType x then fail m!"the parameter `{← x.fvarId!.getUserName}` of `{c}` is a type"
      if (← isClass? (← inferType x)).isSome then
        fail m!"the parameter `{← x.fvarId!.getUserName}` of `{c}` is an instance"
    let group ← mutualGroup c
    let recursive := group.any fun g => (rhs.find? (·.isConstOf g)).isSome
    let L0 : Loc := { slots := xs.map (some ·.fvarId!), fns := if recursive then group else #[],
                      params, prog? := L.prog?, c := L.c }
    let saved := (← get).inlining
    modify fun s => { s with inlining := s.inlining.push c }
    try
      -- the depth of the course-of-values recursion: the first that works
      let mut err? : Option Exception := none
      for d in [0:4] do
        if d > 0 && !recursive then break
        try
          let mut body ← tr { L0 with depth := d } rhs
          for _ in xs do body := Src.lam none body
          let ty ← tyStx L0 info.type
          return Src.ascribe body ty
        catch ex => if err?.isNone then err? := some ex
      throw err?.get!
    finally
      modify fun s => { s with inlining := saved }
  appStx helper (← args.mapM (tr L))

/-- A term of the default value of the Lean type `T` (its `Inhabited` instance, in head normal
    form), for a branch that Lean proves unreachable but the language does not (`what`). -/
partial def defaultTerm (L : Loc) (T : Expr) (what : MessageData) : TM Src := do
  let inst ← try synthInstance (← mkAppM ``Inhabited #[T])
    catch _ => fail m!"{what}\nis read through a field `Fin m → _` (as `Nat → Option _`): \
      below `m` it is `some`, but the language needs a value for `none`, and the type{indentExpr T}\n\
      has no `Inhabited` instance"
  tr L (← whnf (← mkAppOptM ``Inhabited.default #[T, inst]))

/-- `Fin.foldl n f z` (of type `α`): `Comp.nat_rec n z s`, whose step `s` binds the index `k`
    and the accumulator `acc` and is the translation of `f acc ⟨k, h⟩` (the bound `h` is a
    proof, erased). -/
partial def trFinFoldl (L : Loc) (α n f z : Expr) : TM Src := do
  discard <| cirOf L α
  let tn ← tr L n
  let tz ← tr L z
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `acc α fun acc => do
    let lt ← mkAppM ``LT.lt #[k, n]
    withLocalDeclD `h lt fun h => do
      let i ← mkAppOptM ``Fin.mk #[n, k, h]
      let body := (mkApp2 f acc i).headBeta
      let L' := (L.bind k.fvarId!).bind acc.fvarId!
      return Src.natRec none tn tz (← tr L' body)

/-- `f q` for a function `f` on the carrier of a quotient and a value `q` of the quotient
    (`Quot.lift f h q`), then applied to `extra`.  The value of `q` is a representative: for
    `Quot.mk r a` it is `a`, so the translation is the one of `f a`; otherwise it is bound
    (`letE`) to a local of the carrier, to which `f` is applied. -/
partial def trQuotApp (L : Loc) (f q : Expr) (extra : Array Expr) : TM Src := do
  let q ← instantiateMVars q
  if q.isAppOfArity ``Quot.mk 3 then return ← tr L (mkAppN f (#[q.appArg!] ++ extra))
  let some α := quotCarrier? (← whnf (← inferType q))
    | fail m!"the value{indentExpr q}\nis not a value of a quotient"
  let tq ← tr L q
  withLocalDeclD `a α fun y => do
    let body ← tr (L.bind y.fvarId!) (mkAppN f (#[y] ++ extra))
    return .letE tq body

/-- The only relevant field of a fully applied constructor application, when its type has
    one constructor and that constructor one field besides proofs and instances. -/
partial def wrapperField? (cinfo : ConstructorVal) (args : Array Expr) : TM (Option Expr) := do
  unless args.size == cinfo.numParams + cinfo.numFields do return none
  let ind ← getConstInfoInduct cinfo.induct
  unless ind.ctors.length == 1 do return none
  let mut ty ← inferType (mkAppN (mkConst cinfo.name (← mkFreshLevelMVars
    cinfo.levelParams.length)) args[0:cinfo.numParams].toArray)
  let mut kept : Array Expr := #[]
  for a in args[cinfo.numParams:] do
    ty ← whnf ty
    let .forallE _ d b bi := ty | return none
    unless ← isErasedField bi d do kept := kept.push a
    ty := b.instantiate1 a
  return if kept.size == 1 then some kept[0]! else none

/-- A call `c a₁ … aₙ` of a library function.  When `c` is the Lean function of an entry of
    the catalogue of externs (`externTable`), it is a call of that extern (`externCall`).
    Otherwise the call is unfolded (`unfoldCall?`) — an instance method (`a + b` on `Nat` is
    `HAdd.hAdd … a b`, which unfolds to `Nat.add a b`) or a definition in terms of other
    functions (`Nat.min a b` is `if a ≤ b then a else b`) — and translated. -/
partial def trExtern (L : Loc) (e fn : Expr) (args : Array Expr) : TM Src := do
  -- a value of a quotient is a representative: a call that computes to `Quot.mk r a` is `a`,
  -- any other call returning a quotient has no representative the language could compute
  if (quotCarrier? (← whnf (← inferType e))).isSome then
    let e' ← whnf e
    if e'.isAppOf ``Quot.mk then return ← tr L e'
    fail m!"the call{indentExpr e}\nreturns a value of a quotient, read as its carrier: the \
      language would need a representative of the class (`Quot.out` is not computable)"
  let .const c _ := fn | fail m!"cannot translate the application{indentExpr e}"
  if let some entry := externTable.find? c then
    return ← externCall L entry fn args
  -- `n.succ` is `n + 1`
  if c == ``Nat.succ && args.size == 1 then
    return ← tr L (mkApp2 (mkConst ``Nat.add) args[0]! (mkRawNatLit 1))
  -- `a[i]'h`: the language erases the proof `h`, so the element is read with the default of
  -- the element type when `i` is out of bounds (which it never is, the program proved it)
  if c == ``Array.getInternal && args.size == 4 then
    let inst ← try synthInstance (← mkAppM ``Inhabited #[args[0]!])
      catch _ => fail m!"the access{indentExpr e}\nerases its proof of bounds, and reads the \
        default of the element type when out of bounds: the element type{indentExpr args[0]!}\n\
        has no `Inhabited` instance"
    return ← tr L (← mkAppOptM ``Array.get!Internal #[args[0]!, inst, args[1]!, args[2]!])
  if let some e' ← unfoldCall? e then return ← tr L e'
  fail m!"the call{indentExpr e}\nis not a call of an extern: `{c}` is not the Lean function \
    of an entry of the catalogue of externs (`LeanInitPureExtern`), and its definition cannot \
    be unfolded"

/-- A call of the extern `entry` (an entry of the catalogue, `LeanInitPureExtern.entry`)
    whose Lean function is `fn`, applied to `args`: `Neu.extern (.entry _ …) args'`.  The
    arguments of the extern are the explicit arguments of `fn` that are values (not types,
    proofs or `()`), and the default value of an `[Inhabited α]` argument (`Array.get!Internal`
    takes the default as an argument of the extern); the proofs are erased (the evaluator of the
    extern decides them).  The type arguments of the entry (`αt` of `lean_array_push αt`) are
    found by unification with the types of the arguments. -/
partial def externCall (L : Loc) (entry : Name) (fn : Expr) (args : Array Expr) : TM Src := do
  let mut ty ← inferType fn
  let mut vals : Array Expr := #[]
  for a in args do
    ty ← whnf ty
    let .forallE _ d b bi := ty | fail m!"`{fn}` is applied to too many arguments"
    -- (a binder type may carry annotations: `(a : @& Array α)` is borrowed)
    let d := d.consumeMData
    if bi.isInstImplicit && d.isAppOfArity ``Inhabited 1 then
      let v ← whnf (← mkAppOptM ``Inhabited.default #[d.appArg!, a])
      vals := vals.push (if v.isConstOf ``Nat.zero then mkNatLit 0 else v)
    else if bi.isExplicit && !(← isProp d) && !(← isType a) && !(← isUnitType d) then
      vals := vals.push a
    ty := b.instantiate1 a
  let sc := `LeanScript.LeanInitPureExtern ++ entry
  let some info := (← getEnv).find? sc
    | fail m!"the entry `{entry}` of the catalogue of externs has no shorthand `{sc}`"
  let nFields := explicitBinderCount info.type
  let holes ← (List.replicate nFields ()).toArray.mapM fun _ => `(_)
  let entryStx ← `($(mkIdent (`_root_ ++ sc)) $holes*)
  let argSrcs ← vals.mapM (tr L)
  return .pneu (fun _ xs => do
      let mut as ← `(LeanScript.Args.nil)
      for x in xs.reverse do as ← `(LeanScript.Args.cons $x $as)
      `(LeanScript.Neu.extern $entryStx $as))
    #[] argSrcs fun _ _ => none

/-- `decide p` (of the instance `inst : Decidable p`): the call of the extern whose Lean
    function decides `p` (`Nat.decLt a b` for `a < b` on `Nat`: `lean_nat_dec_lt`, a `.bool`),
    `&&`, `||`, `!` of the decisions for `∧`, `∨`, `¬`, or else the instance unfolded
    (`instDecidableEqNat a b` is `Nat.decEq a b`). -/
partial def trDecide (L : Loc) (p inst : Expr) : TM Src := do
  let inst ← instantiateMVars inst
  let dec (q d : Expr) := mkApp2 (mkConst ``Decidable.decide) q d
  let lamBody (e : Expr) : Expr := match e with
    | .lam _ _ b _ => b
    | e => e
  if let .const c' _ := inst.getAppFn then
    if let some entry := externTable.find? c' then
      return ← externCall L entry inst.getAppFn inst.getAppArgs
    match c', inst.getAppArgs with
    | ``instDecidableAnd, #[q, r, dq, dr] =>
        return ← tr L (mkApp2 (mkConst ``and) (dec q dq) (dec r dr))
    | ``instDecidableOr, #[q, r, dq, dr] =>
        return ← tr L (mkApp2 (mkConst ``or) (dec q dq) (dec r dr))
    | ``instDecidableNot, #[q, dq] =>
        return ← tr L (mkApp (mkConst ``not) (dec q dq))
    | ``instDecidableTrue, _ => return ← tr L (mkConst ``Bool.true)
    | ``instDecidableFalse, _ => return ← tr L (mkConst ``Bool.false)
    | ``Decidable.isTrue, _ => return ← tr L (mkConst ``Bool.true)
    | ``Decidable.isFalse, _ => return ← tr L (mkConst ``Bool.false)
    -- a decision by cases: the decision in each branch (`if c then isTrue _ else isFalse _`
    -- is the decision of `c`)
    | ``ite, #[_, c, dc, t, f] | ``dite, #[_, c, dc, t, f] =>
        if (lamBody t).isAppOf ``Decidable.isTrue && (lamBody f).isAppOf ``Decidable.isFalse then
          return ← tr L (dec c dc)
        if (lamBody t).isAppOf ``Decidable.isFalse && (lamBody f).isAppOf ``Decidable.isTrue then
          return ← tr L (mkApp (mkConst ``not) (dec c dc))
        if c' == ``dite then
          let br (k : Expr) (h : Expr) : TM Expr :=
            withLocalDeclD `h h fun x => do mkLambdaFVars #[x] (dec p (mkApp k x).headBeta)
          return ← tr L (← mkAppOptM ``dite
            #[mkConst ``Bool, c, dc, ← br t c, ← br f (mkNot c)])
        return ← tr L (← mkAppOptM ``ite #[mkConst ``Bool, c, dc, dec p t, dec p f])
    -- a decision on a value of a quotient, by its representative `a` (`Quot.recOnSubsingleton q
    -- f` decides with `f a`)
    | ``Quot.recOnSubsingleton, #[α, r, motive, _, q, f] =>
        let g ← withLocalDeclD `a α fun a => do
          let pa := (mkApp motive (← mkAppOptM ``Quot.mk #[α, r, a])).headBeta
          mkLambdaFVars #[a] (dec pa (mkApp f a).headBeta)
        return ← trQuotApp L g q #[]
    | _, _ => pure ()
  if let some inst' ← unfoldCall? inst then return ← trDecide L p inst'
  -- any other decision: `decide` itself unfolded, a case analysis of the instance (a
  -- `Decidable p` is read as a `.bool`: `isTrue _` is `true`, `isFalse _` is `false`)
  if !inst.getAppFn.isConst || (← isMatcher inst.getAppFn.constName!) ||
      [``Eq.mpr, ``Eq.mp, ``Eq.rec, ``Eq.ndrec, ``cast, ``Quot.lift, ``Quot.rec,
        ``Quot.recOn].contains inst.getAppFn.constName! then
    if let some d ← unfoldDefinition? (mkApp2 (mkConst ``Decidable.decide) p inst) then
      return ← tr L d.headBeta
  fail m!"the condition{indentExpr p}\nis decided by{indentExpr inst}\nwhich is not the Lean \
    function of an entry of the catalogue of externs (`LeanInitPureExtern`), and cannot be \
    unfolded"

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
        fields := fields.push (← trOptField L a (← whnf (← inferType a)))
      else
        fields := fields.push (← tr L a)
    ty := b.instantiate1 a
  let T ← normType (← inferType (mkAppN fn args)) false
  if (← cirOf L T false).hasData then modify fun s => { s with usesData := true }
  let ctorFn ← `(#leanscript_get_ctor $(mkIdent (`_root_ ++ cinfo.name)) $named*)
  return .pnode .other (fun xs => `(($ctorFn) $xs*)) fields

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
      if let some (t, .hole) ← nestView? L a then
        out? := some (Src.recordCases t 2 (.var 1))
        continue
      -- a member read through a field `Fin m → X` (as `Nat → Option X`): the answer at the
      -- `Option X` is `none` or `some` of the answer at `X`; below `m` it is `some`, and the
      -- unreachable `none` gets the default of the answer type
      if let some (t, .optHole) ← nestView? L a then
        unless L.vary.isEmpty && args.size == n do
          fail m!"the recursive call{indentExpr e}\non a value read through a field `Fin m → _` \
            must pass the other parameters unchanged"
        let d ← defaultTerm L (← inferType e) m!"the recursive call{indentExpr e}"
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
          return (ρ, ← recBranch { L0 with params } c' args')
        ρs := ρs.push ρ
        brs := brs.push br
    let ρFun ← if ρs.size = 1 then `(fun _ => $(ρs[0]!)) else finFunStx ρs
    let Δ := mkIdent (prog.name ++ `Δ)
    let bref ← brefStx L.c b
    let depth := L.depth
    let r : Src := .comp (fun xs bs => do
        let brFun ← finFunStx bs
        if depth = 0 then
          `(LeanScript.Comp.data_rec (Δ := $Δ) $bref $ρFun $brFun $(quote j) $(xs[0]!))
        else
          `(LeanScript.Comp.data_brec (Δ := $Δ) $bref $ρFun $(quote depth) $brFun $(quote j)
            $(xs[0]!)))
      #[← tr L major] (brs.map (1, ·))
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

end

end LeanScript.Gen

end
