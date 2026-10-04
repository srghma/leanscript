module

public meta import LeanScript.TermElab.ToTerm.Expr.Cases
public meta import LeanScript.TermElab.ToTerm.Fusion
public meta import LeanScript.TermElab.ToTerm.StreamFusion

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: the expression translator

`tr`, `trProj` and `trApp`: the translation of a Lean expression
(an application, a projection, a constructor, a recursive call, a `casesOn`/`match`, an
extern, a range `for` loop, a structurally terminating `while` loop, a fold over a nested
container, ...) to the syntax of a
`LeanScript.Term`.  See `LeanScript.TermElab.ToTerm` for the definition translator.
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

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
    -- a local proof (`have h : p := …`) has no value: it is substituted into the body, where
    -- it is only ever used by other proofs (erased) or in types
    if ← isProp t then return ← tr L (b.instantiate1 v)
    -- a literal of the built-in list is substituted: its conversion to an array
    -- (`List.toArray`, in an append) is then an array literal
    if (← cirOf L t false) matches .list _ then
      if (← listLit? v).isSome then return ← tr L (b.instantiate1 v)
    -- an array literal used once (outside a `fun`) is substituted: an append onto it is then
    -- one literal (`#["a"] ++ xs` is `["a", ...xs]`)
    if usedOnceOutsideFun b then
      if ← arrayLit? v then return ← tr L (b.instantiate1 v)
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
    let ty ← tyStx L t
    withLocalDeclD n t fun x => do
      return Src.lam (some ty) (← tr (L.bind x.fvarId!) (b.instantiate1 x))
  | .proj S i s =>
    -- a projection of a constructor application (`(⟨j, h⟩ : Fin m).val`) is that field
    if let some e' ← Meta.reduceProj? e then
      if (← whnfR s).isApp && (← whnfR s).getAppFn.isConst &&
          (← getEnv).isConstructor (← whnfR s).getAppFn.constName! then
        return ← tr L e'
    -- a projection of a helper that unfolds to a constructor application (`headNorm`)
    if let some e' ← projByInlining? e then return ← tr L e'
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
          let val : Anf.LitVal := match e.nat? <|> e.rawNatLit? with
            | some n => .nat n
            | none => .other
          return ← Src.lit' p (← exprToSyntax e) val
        -- a closed `Float` (`Float32`): the literal of the language is its `HashableFloat`
        -- (`HashableFloat32`), the float with `NaN` and `-0.0` normalised to `0.0`, as the
        -- result of every float operation of the language is (`FloatExtern.eval`)
        if T.isConstOf ``Float && (← whnf d).isConstOf ``HashableFloat then
          return ← Src.lit' p (← `(HashableFloat.normalize $(← exprToSyntax e)))
        if T.isConstOf ``Float32 && (← whnf d).isConstOf ``HashableFloat32 then
          return ← Src.lit' p (← `(HashableFloat32.normalize $(← exprToSyntax e)))
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
    let erased ← isErasedCtorField bi d
    if k = i then
      if erased then fail m!"the field {i} of `{S}` is a proof, an instance or a `Unit`"
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
      let some (t, s) ← nestView? tr L e | fail m!"cannot translate the application{indentExpr e}"
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
      let d ← defaultTerm tr L T m!"the application{indentExpr e}"
      let mut scrut := Src.app (← tr L fn) (← tr L a)
      -- `Option T` is a member of the block of `T`: taken apart after `data_out`
      let plan ← lm (planType (← normType (← mkAppM ``Option #[T]) false) L.prog?)
      if let some (b, j) := plan.data? then
        modify fun st => { st with usesData := true }
        scrut := Src.dataOut (← brefStx L.c b) (quote j) scrut
      let mut r := Src.unionCases (← tyOf? L T) scrut #[(0, d), (1, .var 0)]
      for a in args[1:] do r := Src.app r (← tr L a)
      return r
    appArgs tr L fn (← tr L fn) args
  | .const c _ =>
    let env ← getEnv
    if L.fns.contains c then return ← trRecCall tr L e
    -- the functions of the new string API that go through a slice (`stringRewrite?`)
    if let some e' ← stringRewrite? e then return ← tr L e'
    -- `List.toArray (Array.foldr f [] xs)` that only conses: a fold pushing onto an array
    if c == ``List.toArray && args.size == 2 then
      if (← listLit? args[1]!).isNone then
        if let some e' ← fuseToArrayFoldr? args[1]! then return ← tr L e'
    -- delays: `Thunk.pure a`, `Thunk.mk f` and `t.get` are their values up to the delays
    if (c == ``Thunk.pure || c == ``Thunk.mk || c == ``Thunk.get) && args.size ≥ 2 then
      let e₂ := mkAppN fn args[:2].toArray
      let a := args[1]!
      let r ← delayCoerceTy L (← inferType a) (← inferType e₂) (← tr L a)
      return ← appArgs tr L e₂ r args[2:].toArray
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
      return ← trDecide tr L args[0]! args[1]!
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
        return ← trRangeFor tr L args[4]! args[5]! args[6]! fun i r => pure (mkApp2 args[7]! i r)
    -- a `while` loop in `Id`: only when it is structurally terminating
    if c == ``ForIn.forIn && args.size == 8 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Lean.Loop then
        return ← trWhile tr L e args[4]! args[6]! args[7]!
    if c == ``ForIn'.forIn' && args.size == 9 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Std.Legacy.Range then
        return ← trRangeFor tr L args[5]! args[6]! args[7]! fun i r => do
          let .forallE _ _ b _ ← whnf (← inferType args[8]!) | fail m!"bad `forIn'`"
          let .forallE _ hTy _ _ ← whnf (b.instantiate1 i) | fail m!"bad `forIn'`"
          -- the proof of membership is erased: a local that the translation never reads
          withLocalDeclD `h hTy fun h => pure (mkApp3 args[8]! i h r)
    if isCasesOnRecursor env c then return ← trCases tr L c args e
    -- a sparse case analysis (`T._sparseCasesOn_k`, of a `match` with overlapping patterns):
    -- the full case analysis it abbreviates
    if isSparseCasesOn env c then
      if let some e' ← sparseAsCasesOn? c fn.constLevels! args then return ← tr L e'
    -- a quotient is read as its carrier (`quotCarrier?`), a value of it as a representative:
    -- `Quot.mk r a` is `a`, and a function on the quotient (`Quot.lift f h q`, `Quot.rec`, …)
    -- is `f` applied to the representative `q`
    if c == ``Quot.mk && args.size ≥ 3 then return ← tr L (mkAppN args[2]! args[3:].toArray)
    if (c == ``Quot.lift || c == ``Quot.rec) && args.size == 5 then return ← tr L args[3]!
    if (c == ``Quot.lift || c == ``Quot.rec) && args.size ≥ 6 then
      return ← trQuotApp tr L args[3]! args[5]! args[6:].toArray
    if (c == ``Quot.recOn || c == ``Quot.hrecOn) && args.size ≥ 5 then
      return ← trQuotApp tr L args[4]! args[3]! args[6:].toArray
    if c == ``Quot.recOnSubsingleton && args.size ≥ 6 then
      return ← trQuotApp tr L args[5]! args[4]! args[6:].toArray
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
      return ← trFinFoldl tr L args[0]! args[1]! args[2]! args[3]!
    -- an array literal `#[a, b, …]` (`List.toArray [a, b, …]`)
    -- (also `Array.mk [a, b, …]`, the head normal form of a default `#[]` of `Inhabited`)
    if (c == ``List.toArray || c == ``Array.mk) && args.size == 2 then
      if let some xs ← listLit? args[1]! then
        discard <| cirOf L (← inferType e) false
        return Src.arrayMk (← xs.mapM (tr L))
    -- the built-in list (`useBuiltinList`): a literal `[a, b, …]` is `PExpr.list_mk`, and
    -- `xs ++ ys` is the extern `lean_list_append` (`List.append`)
    if c == ``List.nil || c == ``List.cons then
      if (← cirOf L (← inferType e) false) matches .list _ then
        if let some xs ← listLit? e then return .list (← xs.mapM (tr L))
        fail m!"the list{indentExpr e}\nis not a literal: the built-in list has no `cons` yet"
    if c == ``List.append && args.size == 3 then
      if (← cirOf L (← inferType e) false) matches .list _ then
        return ← trExtern tr L e fn args
      -- a list that is a datatype of the program: `List.append` is an ordinary function
      if let some e' ← unfoldCall? e then return ← tr L e'
    -- the conversions between a list and an array are their externs (`lean_array_mk`,
    -- `lean_array_to_list`), not the constructor and the projection of the structure `Array`
    if (c == ``Array.mk || c == ``Array.toList) && args.size == 2 then
      return ← trExtern tr L e fn args
    -- a fold over an array of members of the block recursed on
    if c == ``Array.foldl && args.size == 7 then
      if let some (arr, .array s) ← nestView? tr L args[4]! then
        unless (← natLit? args[5]!) == some 0 &&
            (← isDefEq args[6]! (← mkAppM ``Array.size #[args[4]!])) do
          fail m!"`Array.foldl` with bounds{indentExpr e}\nis not supported"
        return ← trNestFoldl tr L arr s args
      -- a fold over any other array, from `0` to its size: `Comp.array_foldl`
      if (← natLit? args[5]!) == some 0 &&
          (← isDefEq args[6]! (← mkAppM ``Array.size #[args[4]!])) then
        return ← trFoldl tr L args
    if ← isMatcher c then
      let info ← getConstInfo c
      let v := info.value!.instantiateLevelParams info.levelParams fn.constLevels!
      return ← tr L (← Core.betaReduce (v.beta args))
    -- the constructor and the projection of a fixed-width unsigned integer (`UInt32.ofBitVec`,
    -- `UInt32.toBitVec`) are their externs (the identity in JavaScript), not an erased wrapper:
    -- `UInt32` and `BitVec 32` are different leaves of the language
    if uintBitVecConv.contains c then return ← trExtern tr L e fn args
    if let some (.ctorInfo cinfo) := env.find? c then
      -- a constructor of a type of two values without fields (`Decidable.isTrue h`, the proof
      -- erased) is a `.bool`: the second constructor is `true`
      if let some b ← twoPointCtor? cinfo fn.constLevels! args then return Src.boolLit b
      -- a wrapper of one value (`Fin.mk n v h`, `Subtype.mk v h`, `Vector.mk a h`) is erased
      -- to that value, also when its parameters mention locals (`⟨0, h⟩ : Fin c.n`)
      if let some a ← wrapperField? cinfo args then
        unless (← cirOf L (← inferType e) false) matches .data .. do return ← tr L a
      if !((← cirOf L (← inferType e) false) matches .prim _) then
        return ← trCtor tr L cinfo fn args
    if let some pinfo ← getProjectionFnInfo? c then
      if !pinfo.fromClass then
        if let some e' ← unfoldDefinition? e then return ← tr L e'
    -- a definition by well-founded recursion that drains a stream (an unfold) built over an
    -- array: one `Array.foldl` (`fuseStreamDrain?`)
    if ← isWfHelper c then
      if let some e' ← (try fuseStreamDrain? e catch _ => pure none) then return ← tr L e'
    -- a call of a helper definition (not from the library): its own translation, applied
    if !(← isLibraryDecl c) then
      if let some (.defnInfo _) := env.find? c then
        return ← (try trHelperCall tr L c e args
          catch ex =>
            -- a helper that cannot be translated on its own (its parameter is a type, its
            -- type is in `Type 1`, …) and is not recursive: unfolded where it is used
            try
              unless ← isInlinableHelper c do throw ex
              let some e' ← unfoldDefinition? e | throw ex
              tr L e'
            catch _ => try trExtern tr L e fn args catch _ => throw ex)
    trExtern tr L e fn args
  | .proj .. =>
    -- a projection of a helper that unfolds to a constructor application (`headNorm`)
    if let some e' ← projByInlining? e then return ← tr L e'
    -- a projection applied to arguments (`c.data i` for a function field)
    appArgs tr L fn (← tr L fn) args
  | _ => fail m!"cannot translate the application{indentExpr e}"

end

end LeanScript.Gen

end
