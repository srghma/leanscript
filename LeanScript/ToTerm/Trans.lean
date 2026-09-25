module

public meta import LeanScript.ToTerm.TransBrec
public meta import LeanScript.ToTerm.TransRecObject
public meta import LeanScript.ToTerm.TransRecUnion
public meta import LeanScript.ToTerm.TransRecFamily
public meta import LeanScript.ToTerm.TransRecCases
public meta import LeanScript.ToTerm.Extern
public meta import LeanScript.ToTerm.Cache
public meta import LeanScript.ToTerm.Existential

@[expose] public section

meta section

/-!
# The translation

The translation proper: one `mutual` block, since every clause of it may meet any
expression.  The clauses for recursors, sparse `casesOn`s, inlined definitions and
structural recursion are in `LeanScript.ToTerm.TransRec` and `LeanScript.ToTerm.TransBrec`,
and are passed `trans` as an argument.  The elaborator that calls it is
`LeanScript.ToTerm.Elab`.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The translation -/

mutual

/-- The term a Lean expression translates to, in the context `c`. -/
partial def trans (c : TCtx) (e0 : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e0).headBeta
  match e with
  | .mdata _ b => trans c b
  | .fvar f => c.var f
  | .lam .. => transLam c e
  | .letE .. => transLet c e
  | .proj .. => transProj c e
  | .sort .. | .forallE .. =>
      throwError "`#leanscript_to_term`: a type is not a value of the language: {e}"
  | _ =>
      if let some t ← transLit? c e then return t
      transApp c e

/-- `fun x => b`. -/
partial def transLam (c : TCtx) (e : Expr) : MetaM Expr := do
  let fty ← whnf (← inferType e)
  let .forallE _ d _ _ := fty
    | throwError "`#leanscript_to_term`: not a function: {e}"
  -- a binder the language erases (`Unit`) is dropped, as a `Unit` domain is
  if ← LeanScript.Deriving.erasedBinder d then
    return ← trans c (← dropErasedBinder e)
  let σ ← tyOfType d
  lambdaBoundedTelescope e 1 fun xs body => do
    let c' := c.push xs[0]!.fvarId! σ
    let b ← trans c' body
    let τ ← tyOfTermOr body b
    return mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

/-- `let x := v; b`. -/
partial def transLet (c : TCtx) (e : Expr) : MetaM Expr := do
  let .letE n t v b _ := e
    | throwError "`#leanscript_to_term`: internal: not a `let`"
  let v' ← trans c v
  let σ ← tyOfTermOr v v'
  withLetDecl n t v fun x => do
    let c' := c.push x.fvarId! σ
    let body := b.instantiate1 x
    let b' ← trans c' body
    let τ ← tyOfTermOr body b'
    return mkAppN (mkConst `LeanScript.Term.letE) #[c.sg, c.gamma, σ, τ, v', b']

/-- A literal of a terminal type, carried into the term as it stands. -/
partial def transLit? (c : TCtx) (e : Expr) : MetaM (Option Expr) := do
  unless isLitLike e do return none
  let t ← whnf (← inferType e)
  let .const n _ := t.getAppFn | return none
  let some ctor := litCtorFor n | return none
  return some (mkAppN (mkConst ctor) #[c.sg, c.gamma, e])

/-- An application, or a bare head. -/
partial def transApp (c : TCtx) (e : Expr) : MetaM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  -- a redex the elaborator left behind (a `match` branch, say) is reduced, not applied
  if f.consumeMData.isLambda && !args.isEmpty then
    return ← trans c ((mkAppN f.consumeMData args).headBeta)
  match f with
  | .const n lvls => transConstApp c e n lvls args
  | .fvar id => applyArgs trans c (← c.var id) f args
  | .proj .. => applyArgs trans c (← transProj c f) f args
  | .lam .. | .letE .. => applyArgs trans c (← trans c f) f args
  | _ => throwError "`#leanscript_to_term`: cannot translate {e}"

/-- A structure projection: the case analysis that binds every field, followed by the
    field that was asked for. -/
partial def transProj (c : TCtx) (e : Expr) : MetaM Expr := do
  let .proj structName idx s := e
    | throwError "`#leanscript_to_term`: internal: not a projection"
  -- a projection out of a closed value — an instance, for one — is that value's field
  unless s.hasFVar do
    let e' ← whnf e
    unless e' == e do return ← trans c e'
  let sty ← tyOfTerm s
  let scrut ← trans c s
  let ind ← getConstInfoInduct structName
  let [ctorName] := ind.ctors
    | throwError "`#leanscript_to_term`: {structName} is not a structure"
  let ci ← getConstInfoCtor ctorName
  -- which of the fields that are kept is this one?
  let params := (← whnf (← inferType s)).getAppArgs
  let keptIdx? ← forallBoundedTelescope (← instantiateForall ci.type params)
      (some ci.numFields) fun xs _ => do
    let mut kept := 0
    let mut hit := none
    for h : i in [0:xs.size] do
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then continue
      if i == idx then hit := some kept
      kept := kept + 1
    return hit
  let some k := keptIdx?
    | throwError "`#leanscript_to_term`: the field {idx} of {structName} carries no \
        value of the language"
  match ← tyView sty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let τ ← tyOfTerm e
      let ids ← fieldTys.mapM fun t => do return ((← mkFreshFVarId), t)
      let c' := c.pushFields ids.toArray
      let some (fid, _) := ids[k]?
        | throwError "`#leanscript_to_term`: the field {idx} of {structName} is not a \
            field of its tree"
      let body ← c'.var fid
      return mkAppN (mkConst `LeanScript.Term.record_casesOn)
        #[c.sg, c.gamma, τ, fs, scrut, body]
  | _ =>
      -- a one-field structure is its field: the wrapper is erased
      if k == 0 then return scrut
      throwError "`#leanscript_to_term`: cannot project the field {idx} of \
        {structName}"

/-- `do` in the identity monad is not an effect: `Id.run`, `pure`, `>>=` and `<$>` are
    the plumbing a `do` block leaves behind, and each of them is a `let` or an
    application once the monad is `Id`.  A `for` over a range is the one that is not:
    it is a fold, and `transForInRange?` builds it.  In any other monad this answers
    `none`, and the call is refused as any other undeclared call is. -/
partial def transIdOp? (c : TCtx) (n : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let isId (m : Expr) : MetaM Bool := do return m.consumeMData.isConstOf ``Id
  match n with
  | ``Id.run =>
      let some x := args[1]? | return none
      return some (← trans c x)
  | ``Pure.pure =>
      unless args.size == 4 do return none
      unless ← isId args[0]! do return none
      return some (← trans c args[3]!)
  | ``Bind.bind =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[5]! args[4]!).headBeta)
  | ``Functor.map =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[4]! args[5]!).headBeta)
  | ``ForIn.forIn =>
      unless args.size ≥ 8 do return none
      unless ← isId args[0]! do return none
      transForInRange? c args[1]! args[args.size - 3]! args[args.size - 2]! args[args.size - 1]!
  | _ => return none

/-- `for i in [:n] do …`, in the identity monad: the loop is the fold of `n` whose value
    is the state, so it is `Term.nat_rec` — the branch binds the index (de Bruijn index
    `0`) and the state before the iteration (index `1`), and answers with the state
    after it.

    The range must start at `0` and step by `1`, and the body must always `yield`: a
    `break` or a `return` out of the loop would need a state the grammar's fold does not
    carry, and is refused rather than silently ignored. -/
partial def transForInRange? (c : TCtx) (ρ coll init body : Expr) : MetaM (Option Expr) := do
  unless ρ.consumeMData.isConstOf ``Std.Legacy.Range do return none
  let (``Std.Legacy.Range.mk, #[startE, stopE, stepE, _]) := (← whnf coll).getAppFnArgs
    | throwError "`#leanscript_to_term`: the range of this `for` is not written out"
  let some start ← evalNat (← whnf startE) | throwError
    "`#leanscript_to_term`: the range of this `for` does not start at a known number"
  let some step ← evalNat (← whnf stepE) | throwError
    "`#leanscript_to_term`: the range of this `for` does not step by a known number"
  unless start == 0 && step == 1 do
    throwError "`#leanscript_to_term`: a `for` over a range is the fold of its bound, so \
      the range has to start at `0` and step by `1`; this one starts at {start} and \
      steps by {step}"
  let β ← inferType init
  let τ ← tyOfType β
  let natTy ← tyOfType (mkConst ``Nat)
  let scrut ← trans c stopE
  let z ← trans c init
  let branch ← withLocalDeclD `i (mkConst ``Nat) fun i =>
    withLocalDeclD `state β fun s => do
      let stepBody ← whnf (mkApp2 body i s).headBeta
      let stepBody ← match stepBody.getAppFnArgs with
        | (``Pure.pure, #[_, _, _, v]) => whnf v
        | _ => pure stepBody
      let next ← match stepBody.getAppFnArgs with
        | (``ForInStep.yield, #[_, v]) => pure v
        | (``ForInStep.done, #[_, _]) =>
            throwError "`#leanscript_to_term`: this `for` leaves the loop early (`break` \
              or `return`), which the fold a loop becomes cannot express"
        | _ =>
            throwError "`#leanscript_to_term`: the body of this `for` does not yield the \
              state of the next iteration"
      let c' := c.pushFields #[(i.fvarId!, natTy), (s.fvarId!, τ)]
      trans c' next
  return some <| mkAppN (mkConst `LeanScript.Term.nat_rec)
    #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], branch]

/-- An application whose head is a constant. -/
partial def transConstApp (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  -- a function implemented by an extern of `Init` is that extern: it is never looked up
  -- in the signature, and one the catalogue does not model is refused
  unless (← isSpecialConst n args) do
    if let some t ← transExternApp? trans c e n lvls args then return t
  -- a function marked `@[extern]` that is translated as an ordinary function (`Nat.gcd`)
  -- is a declaration of the signature, whatever its definition is
  if externAsOrdinary.contains n then
    if let some g := c.global? n then
      let gt := mkAppN (mkConst `LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
      return ← applyArgs trans c gt (mkConst n lvls) args
    throwError "`#leanscript_to_term`: `{n}` is translated as an ordinary function, and is \
      not declared in the signature, so a term cannot call it.  Add a `GlobalDecl` named \
      \"{n.getString!}\" (or \"{n}\") to the signature."
  -- a structural recursion on a recursive record is the fold of the record
  if n.getString! == "brecOn" || (n.isStr && n.getString!.startsWith "brecOn_") then
    -- a structural recursion on a member of a mutual inductive block is the fold of
    -- the family, at the depth it needs
    if let some t ← transRecFamilyBrecOn? trans c e n lvls args then return t
    if let some t ← transRecObjectBrecOn? trans c e n lvls args then return t
    -- a structural recursion on a recursive tagged union other than a list is the fold
    -- of the union, at the depth it needs
    if n != ``List.brecOn then
      if let some t ← transRecUnionBrecOn? trans c e n lvls args then return t
  checkConst n
  if let some t ← transIdOp? c n args then return t
  if n == ``ite then return ← transIte c args
  if n == ``dite then return ← transDite c args
  -- `decide p`: the `Bool` the decision procedure gives, as the test of an `if` is read
  if n == ``Decidable.decide && args.size == 2 then
    return ← boolOfDecidable c args[0]! args[1]!
  -- `xs[i]` (with its proof) is the extern its instance unfolds to, `Array.getInternal`
  if n == ``GetElem.getElem then
    if let some x ← decidableExtern? e then return ← trans c x
  if n == ``cond then
    let some scrut := args[1]? | throwError "`#leanscript_to_term`: `cond` needs its test"
    return ← mkBoolCases c (← trans c scrut) args[2]! args[3]!
  if n == ``Thunk.get then
    let some t := args[1]? | throwError "`#leanscript_to_term`: `Thunk.get` needs a thunk"
    let τ ← tyOfTerm e
    return mkAppN (mkConst `LeanScript.Term.thunk_force) #[c.sg, c.gamma, τ, ← trans c t]
  if n == ``List.toArray || n == ``Array.mk then
    -- an array literal, written as the list of its elements
    return ← transListLit c e
  if n == ``List.brecOn then
    -- the one-step translation first (which also serves a recursion on the elements of
    -- an array); a recursion that reads further down the list is the fold of the list
    -- as a recursive tagged union, at the depth it needs
    let onArray := match args[2]? with
      | some major => (arrayOfToList? major).isSome
      | none => false
    try
      return ← transBrecOn trans c e n lvls args
    catch ex =>
      let fallback? : Option Expr ←
        if onArray = true then pure none else transRecUnionBrecOn? trans c e n lvls args
      match fallback? with
      | some t => return t
      | none => throw ex
  if n == ``Nat.brecOn then
    return ← transBrecOn trans c e n lvls args
  if isSparseCasesOn n then
    if let some t ← transSparseCasesOn? trans c e n lvls args then return t
    -- a type whose tree has no partial dispatch: the exhaustive one
    if let some e' ← sparseAsCasesOn? n args then return ← trans c e'
    if let some e' ← unfoldHere? e then return ← trans c e'
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ← transCtorApp c e ci args
  | some (.recInfo ri) => return ← transRecApp trans c e ri lvls args
  | _ => pure ()
  -- a one-level `match` on a value of a user-defined recursive type (a recursive union,
  -- record or newtype, or a member of a mutual block): its `…_casesOn`, not its recursor
  if let some t ← transRecKindCasesOn? trans c e n lvls args then return t
  if (← Meta.isMatcherApp e) || n.getString! == "casesOn" || n.getString! == "recOn" then
    if let some e' ← unfoldHere? e then
      return ← trans c e'
    throwError "`#leanscript_to_term`: cannot take apart the dispatch {n}"
  -- a structural recursion on lists applied to the elements of an array: unfolded, it
  -- is a `List.brecOn` on `a.toList`, which is the fold of the array `a`
  if args.any (fun a => (arrayOfToList? a).isSome) then
    if let some e' ← unfoldHere? e then
      let e' := e'.headBeta
      if e'.isAppOf ``List.brecOn then
        if let some major := e'.getAppArgs[2]? then
          if (arrayOfToList? major).isSome then
            return ← trans c e'
  if let some g := c.global? n then
    let gt := mkAppN (mkConst `LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
    return ← applyArgs trans c gt (mkConst n lvls) args
  -- the projection function of a structure, applied to a value: that projection, which
  -- is the record's case analysis rather than a function applied to the value
  if let some pinfo ← getProjectionFnInfo? n then
    if !pinfo.fromClass && args.size > pinfo.numParams then
      let ci ← getConstInfoCtor pinfo.ctorName
      let p := Expr.proj ci.induct pinfo.i args[pinfo.numParams]!
      return ← trans c (mkAppN p (args.extract (pinfo.numParams + 1) args.size))
  if ← isInlinable n then
    return ← transInline trans c e n lvls args
  -- a structural recursion defined on its own and called from here (or a wrapper of
  -- one): the fold it compiles to, inlined at the call site
  if ← callsStructuralRecursion n then
    return ← transInline trans c e n lvls args
  throwError "`#leanscript_to_term`: `{n}` is not declared in the signature and is not \
    inlinable, so a term cannot call it.  Either add a `GlobalDecl` named \
    \"{n.getString!}\" (or \"{n}\") to the signature, or mark `{n}` `@[inline]`.  (A \
    structural recursion is inlined without either.)"

/-- Is this call one the translation builds itself, although its head is implemented by
    an extern?  A constructor (`Thunk.mk`, `Array.mk`) is built in place, an array literal
    is built from all of its elements at once, and `Thunk.get` is `thunk_force`. -/
partial def isSpecialConst (n : Name) (args : Array Expr) : MetaM Bool := do
  if n == ``Array.mk then
    if let some l := args[1]? then return isListLit l
  if (← getEnv).find? n matches some (.ctorInfo _) then return true
  if n == ``Thunk.get then return true
  if n == ``List.toArray then
    if let some l := args[1]? then return isListLit l
  return false

/-- Is this list written out, element by element? -/
partial def isListLit (l : Expr) : Bool :=
  match l.consumeMData.getAppFnArgs with
  | (``List.nil, _) => true
  | (``List.cons, #[_, _, as]) => isListLit as
  | _ => false

/-- `if c then t else e`: the test must be a `Bool`. -/
partial def transIte (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `ite` needs its test"
  if let some n ← natZeroTest? cnd then
    return ← mkNatZeroCases c n args[3]! args[4]! none
  let inst := args[2]!
  let test ← boolOfDecidable c cnd inst
  mkBoolCases c test args[3]! args[4]!

/-- `if h : c then t else e`: the test is decided as for `if c then t else e`, and the
    proof `h` each branch binds is erased — a branch can still hand it to an extern that
    takes a proof, which decides the proposition again when the term runs
    (`Term.externCallChecked`). -/
partial def transDite (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `dite` needs its test"
  unless args.size == 5 do
    throwError "`#leanscript_to_term`: this `if h : c then … else …` is applied to \
      arguments, which the translation does not take apart"
  let test ← boolOfDecidable c cnd args[2]!
  let τ ← tyOfType args[0]!
  let branch (p : Expr) (b : Expr) : MetaM Expr :=
    withLocalDeclD `h p fun h => do
      let t ← trans c (mkApp b h).headBeta
      if t.containsFVar h.fvarId! then
        throwError "`#leanscript_to_term`: a branch of `if h : {cnd} then … else …` uses \
          the proof `h` as a value, and the language erases proofs"
      return t
  mkBoolCases' c test (← branch cnd args[3]!) (← branch (mkNot cnd) args[4]!) τ

/-- The natural number `n` of the test `n = 0` (or `0 = n`). -/
partial def natZeroTest? (cnd : Expr) : MetaM (Option Expr) := do
  let (``Eq, #[α, lhs, rhs]) := cnd.getAppFnArgs | return none
  unless (← whnf α).isConstOf ``Nat do return none
  if (← evalNat rhs) == some 0 then return some lhs
  if (← evalNat lhs) == some 0 then return some rhs
  return none

/-- `if n = 0 then t else e`: the case analysis on `n`, whose successor branch does not
    read the predecessor.  With `τ?`, both branches are translated against that type. -/
partial def mkNatZeroCases (c : TCtx) (n thenB elseB : Expr) (τ? : Option Expr) :
    MetaM Expr := do
  let natTy ← tyOfType (mkConst ``Nat)
  let scrut ← trans c n
  let c' := c.pushFields #[(← mkFreshFVarId, natTy)]
  let (τ, z, s) ← match τ? with
    | some τ => pure (τ, ← transCheck c thenB τ, ← transCheck c' elseB τ)
    | none => transBranchPair c thenB c' elseB
  return mkAppN (mkConst `LeanScript.Term.nat_casesOn) #[c.sg, c.gamma, τ, scrut, z, s]

/-- Two branches of one dispatch, each in its own context: their common type and their
    translations.  When the Lean type of the branches has no tree (a datatype with
    existentials), each branch is translated first; if the two types differ, they are joined
    (`joinTy`) and both branches are translated again against the join. -/
partial def transBranchPair (c1 : TCtx) (e1 : Expr) (c2 : TCtx) (e2 : Expr) :
    MetaM (Expr × Expr × Expr) := do
  match ← (try some <$> tyOfTerm e1 catch _ => pure none) with
  | some τ => return (τ, ← trans c1 e1, ← trans c2 e2)
  | none =>
    let t1 ← trans c1 e1
    let t2 ← trans c2 e2
    let τ1 ← termTyOf t1
    let τ2 ← termTyOf t2
    if ← isDefEq τ1 τ2 then return (τ1, t1, t2)
    let j ← joinTy τ1 τ2
    return (j, ← transCheck c1 e1 j, ← transCheck c2 e2 j)

/-- The term an expression translates to, **against** the type `τ`.  A constructor of a
    datatype with existentials takes the trees of its holes from `τ`, a function and the
    branches of an `if` pass `τ` on, and a value whose type is one alternative of a
    `TyWf.oneOf` is injected into it; any other expression is translated as it stands, and
    must have the type `τ`. -/
partial def transCheck (c : TCtx) (e0 τ0 : Expr) : MetaM Expr := do
  let τ ← instantiateMVars τ0
  let e := (← instantiateMVars e0).headBeta.consumeMData
  if τ.hasExprMVar then
    let t ← trans c e
    let τt ← termTyOf t
    unless ← isDefEq τt τ do
      throwError "`#leanscript_to_term`: this value has the type{indentExpr τt}\nwhich is \
        not of the form{indentExpr τ}"
    return t
  match e with
  | .lam _ d _ _ =>
      if ← LeanScript.Deriving.erasedBinder d then
        return ← transCheck c (← dropErasedBinder e) τ
      match τ.getAppFnArgs with
      | (``LeanScript.TyWf.fn, #[σ, ρ]) =>
          lambdaBoundedTelescope e 1 fun xs body => do
            let b ← transCheck (c.push xs[0]!.fvarId! σ) body ρ
            return mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, ρ, b]
      | _ => coerceTo c (← trans c e) τ
  | _ =>
    if let .const n _ := e.getAppFn then
      let args := e.getAppArgs
      if n == ``ite && args.size == 5 then
        if let some m ← natZeroTest? args[1]! then
          return ← mkNatZeroCases c m args[3]! args[4]! (some τ)
        let test ← boolOfDecidable c args[1]! args[2]!
        return ← mkBoolCases' c test (← transCheck c args[3]! τ) (← transCheck c args[4]! τ) τ
      if let some (.ctorInfo ci) := (← getEnv).find? n then
        if args.size ≥ ci.numParams + ci.numFields then
          if (← usesCtorFn e ci) && (← oneOfAlts? τ).isNone then
            return ← coerceTo c (← ctorFnApp trans transCheck c ci args (some τ)) τ
    coerceTo c (← trans c e) τ

/-- The `Bool` a decidable proposition tests. -/
partial def boolOfDecidable (c : TCtx) (cnd : Expr) (inst : Expr) : MetaM Expr := do
  match cnd.getAppFnArgs with
  | (``Eq, #[α, lhs, rhs]) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true then
        return ← trans c lhs
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.false then
        let t ← trans c lhs
        return ← mkBoolCases' c t (mkAppN (mkConst `LeanScript.Term.bool_mk)
            #[c.sg, c.gamma, mkConst ``Bool.false])
          (mkAppN (mkConst `LeanScript.Term.bool_mk) #[c.sg, c.gamma, mkConst ``Bool.true])
          (← tyOfType (mkConst ``Bool))
      -- a decision procedure that is an extern (`Nat.decEq`, say) is that extern
      if let some x ← decidableExtern? inst then return ← trans c x
      -- `a = b` at a type with a `BEq`: the test is `a == b`
      match ← trySynthInstance (← mkAppM ``BEq #[α]) with
      | .some _ => return ← trans c (← mkAppM ``BEq.beq #[lhs, rhs])
      | _ => pure ()
      throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`"
  | _ =>
      -- a decision procedure that is an extern (`Nat.decLt`, say) is that extern, whose
      -- value is the `Bool` it decides
      if let some x ← decidableExtern? inst then return ← trans c x
      let d ← whnf (mkApp2 (mkConst ``Decidable.decide) cnd inst)
      if d.isAppOfArity ``Decidable.decide 2 ||
          (d.find? (fun s => s.isConstOf ``Decidable.rec) |>.isSome) then
        throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`: write the \
          condition as a `Bool`, or declare the decision procedure in the signature"
      trans c d

/-- `bool_casesOn`, from the two Lean branches. -/
partial def mkBoolCases (c : TCtx) (test : Expr) (thenB elseB : Expr) : MetaM Expr := do
  let (τ, t, e) ← transBranchPair c thenB c elseB
  mkBoolCases' c test t e τ

/-- `bool_casesOn`, from the two translated branches. -/
partial def mkBoolCases' (c : TCtx) (test t e τ : Expr) : MetaM Expr := do
  return mkAppN (mkConst `LeanScript.Term.bool_casesOn) #[c.sg, c.gamma, τ, test, t, e]

/-- A list, or an array, written out: every element of it at once. -/
partial def transListLit (c : TCtx) (e : Expr) : MetaM Expr := do
  let ty ← tyOfTerm e
  let .array σ ← tyView ty
    | throwError "`#leanscript_to_term`: {e} is not an array"
  let mut elems : Array Expr := #[]
  let mut cur := e
  repeat
    match cur.getAppFnArgs with
    | (``List.nil, _) => break
    | (``List.cons, #[_, a, as]) => elems := elems.push a; cur := as
    | (``List.toArray, #[_, l]) => cur := l
    | (``Array.mk, #[_, l]) => cur := l
    | _ =>
        throwError "`#leanscript_to_term`: the grammar builds an array from all of its \
          elements at once, so only a list written out can be translated; {cur} is not \
          one"
  let mut ts := mkAppN (mkConst `LeanScript.Terms.nil) #[c.sg, c.gamma, σ]
  for i in [0:elems.size] do
    let a := elems[elems.size - 1 - i]!
    ts := mkAppN (mkConst `LeanScript.Terms.cons) #[c.sg, c.gamma, σ, ← trans c a, ts]
  return mkAppN (mkConst `LeanScript.Term.array_mk) #[c.sg, c.gamma, σ, ts]

/-- A spine of arguments at the given trees. -/
partial def mkSpine (c : TCtx) (tys : List Expr) (vals : Array Expr) : MetaM Expr := do
  unless tys.length == vals.size do
    throwError "`#leanscript_to_term`: this constructor carries {vals.size} values but \
      its tree has {tys.length} fields"
  let mut sp := mkAppN (mkConst `LeanScript.Spine.nil) #[c.sg, c.gamma]
  let tysA := tys.toArray
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    let t ← trans c vals[j]!
    sp := mkAppN (mkConst `LeanScript.Spine.cons)
      #[c.sg, c.gamma, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- An application of a constructor: it is built in place. -/
partial def transCtorApp (c : TCtx) (e : Expr) (ci : ConstructorVal)
    (args : Array Expr) : MetaM Expr := do
  if args.size < ci.numParams + ci.numFields then
    return ← trans c (← etaExpand e)
  if ci.induct == ``Array then
    return ← transListLit c e
  -- a value of a datatype with existentials: its constructor function
  if ← usesCtorFn e ci then
    return ← ctorFnApp trans transCheck c ci args none
  let ty ← tyOfTerm e
  let fields ← ctorValueArgs ci args
  -- a delay
  if let .thunk σ ← tyView ty then
    let some body := fields[0]?
      | throwError "`#leanscript_to_term`: a thunk needs its body"
    let inner := (mkApp body (mkConst ``Unit.unit)).headBeta
    return mkAppN (mkConst `LeanScript.Term.thunk_mk)
      #[c.sg, c.gamma, σ, ← trans c inner]
  -- a one-field wrapper is its field (a type with one constructor: a constructor of a
  -- union whose one field is the union itself, `succ n`, is not a wrapper)
  if h : fields.size = 1 then
    let indInfo ← getConstInfoInduct ci.induct
    let fty ← tyOfTerm fields[0]
    if indInfo.ctors.length == 1 && fty == ty then return ← trans c fields[0]
  match ← tyView ty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.record_mk) #[c.sg, c.gamma, fs, spine]
  | .taggedUnion l =>
      let ctys ← taggedUnionCtorTys l
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.taggedUnion_mk)
        #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
  | .recTaggedUnion l hwf =>
      -- the fields of a value are the payload **unfolded**: a field that is an
      -- occurrence of the union is a value of the union again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf
      let ctys ← taggedUnionCtorTys (← reduceTy unfE)
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_mk)
        #[c.sg, c.gamma, l, hwf, mkNatLit ci.cidx, prf, spine]
  | .recObject fs hwf =>
      -- the fields of a value are the record's fields **unfolded**: an occurrence of the
      -- record inside a field is a value of the record again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recObjectUnfold) fs hwf
      let fieldTys ← recordFieldTys (← reduceTy unfE)
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.recObject_mk) #[c.sg, c.gamma, fs, hwf, spine]
  | .recAlias b hwf =>
      -- the one field of a value is the body **unfolded**: an occurrence of the newtype
      -- inside it is a value of the newtype again
      let some v := fields[0]?
        | throwError "`#leanscript_to_term`: a value of the recursive newtype \
            {ci.induct} needs its body"
      unless fields.size == 1 do
        throwError "`#leanscript_to_term`: the constructor of the recursive newtype \
          {ci.induct} has {fields.size} fields"
      return mkAppN (mkConst `LeanScript.Term.recAlias_mk)
        #[c.sg, c.gamma, b, hwf, ← trans c v]
  | .mutualRecursiveFamily nE f hwf =>
      -- a value of the member the family selects, with its fields **unfolded** in the
      -- scope of the whole family: an occurrence of a member is a value of that member
      let curE := mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.current)
        (tyWfInE ((← natOfExpr nE) + 2)) f
      let unfE ← reduceTy (mkAppN (mkConst ``LeanScript.LeanFamMemberSchema.map)
        #[tyWfInE ((← natOfExpr nE) + 2), tyE,
          mkApp3 (mkConst ``LeanScript.TyWfIn.unfoldFam) nE f hwf, curE])
      let value ← match unfE.getAppFnArgs with
        | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
            let ctys ← taggedUnionCtorTys l
            let some fieldTys := ctys[ci.cidx]?
              | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no \
                  constructor {ci.cidx}"
            let spine ← mkSpine c fieldTys fields
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.ctors)
              #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
        | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
            let spine ← mkSpine c (← recordFieldTys fs) fields
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.record)
              #[c.sg, c.gamma, fs, spine]
        | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
            let some v := fields[0]?
              | throwError "`#leanscript_to_term`: a value of {ci.induct} needs its body"
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.alias)
              #[c.sg, c.gamma, b, ← trans c v]
        | _ => throwError "`#leanscript_to_term`: internal: the member of the family \
            {ci.induct} has no shape: {unfE}"
      return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_mk)
        #[c.sg, c.gamma, nE, f, hwf, value]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      return mkAppN (mkConst `LeanScript.Term.enum_mk)
        #[c.sg, c.gamma, s, ← mkFinLit nE ci.cidx]
  | .prim _ =>
      if ← isBoolTy ty then
        return mkAppN (mkConst `LeanScript.Term.bool_mk)
          #[c.sg, c.gamma, toExpr (ci.cidx == 1)]
      throwError "`#leanscript_to_term`: {ci.name} builds a value of a terminal type, \
        which has no constructor in the language; write it as a literal"
  | _ =>
      throwError "`#leanscript_to_term`: the tree of {ci.induct} has no introduction \
        form in the grammar"

end

end LeanScript.ToTerm

end

end
