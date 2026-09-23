module

public meta import LeanScript.ToTerm.Cases

@[expose] public section

meta section

/-!
# The translation

The translation proper: one `mutual` block, since every clause of it may meet any
expression.  The elaborator that calls it is `LeanScript.ToTerm.Elab`.
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
  let σ ← tyOfType d
  lambdaBoundedTelescope e 1 fun xs body => do
    let c' := c.push xs[0]!.fvarId! σ
    let τ ← tyOfTerm body
    let b ← trans c' body
    return mkAppN (mkConst ``LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

/-- `let x := v; b`. -/
partial def transLet (c : TCtx) (e : Expr) : MetaM Expr := do
  let .letE n t v b _ := e
    | throwError "`#leanscript_to_term`: internal: not a `let`"
  let σ ← tyOfType t
  let v' ← trans c v
  withLetDecl n t v fun x => do
    let c' := c.push x.fvarId! σ
    let body := b.instantiate1 x
    let τ ← tyOfTerm body
    let b' ← trans c' body
    return mkAppN (mkConst ``LeanScript.Term.letE) #[c.sg, c.gamma, σ, τ, v', b']

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
  | .fvar id => applyArgs c (← c.var id) f args
  | .proj .. => applyArgs c (← transProj c f) f args
  | .lam .. | .letE .. => applyArgs c (← trans c f) f args
  | _ => throwError "`#leanscript_to_term`: cannot translate {e}"

/-- Apply a translated function to the arguments it is given, dropping the ones the
    language erases (types, instances and proofs). -/
partial def applyArgs (c : TCtx) (t : Expr) (fn : Expr) (args : Array Expr) : MetaM Expr := do
  let mut t := t
  let mut cur := fn
  for a in args do
    let fty ← whnf (← inferType cur)
    let .forallE _ d _ _ := fty
      | throwError "`#leanscript_to_term`: too many arguments for {cur}"
    let next := mkApp cur a
    if ← LeanScript.Deriving.erasedBinder d then
      cur := next
      continue
    let σ ← tyOfType d
    let τ ← tyOfTerm next
    let a' ← trans c a
    t := mkAppN (mkConst ``LeanScript.Term.ap) #[c.sg, c.gamma, σ, τ, t, a']
    cur := next
  return t

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
      return mkAppN (mkConst ``LeanScript.Term.record_casesOn)
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
  return some <| mkAppN (mkConst ``LeanScript.Term.nat_rec)
    #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], branch]

/-- An application whose head is a constant. -/
partial def transConstApp (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  checkConst n
  if let some t ← transIdOp? c n args then return t
  if n == ``ite then return ← transIte c args
  if n == ``dite then
    throwError "`#leanscript_to_term`: `if h : c then …` binds a proof, which the \
      language erases; write the test as a `Bool`"
  if n == ``cond then
    let some scrut := args[1]? | throwError "`#leanscript_to_term`: `cond` needs its test"
    return ← mkBoolCases c (← trans c scrut) args[2]! args[3]!
  if n == ``Thunk.get then
    let some t := args[1]? | throwError "`#leanscript_to_term`: `Thunk.get` needs a thunk"
    let τ ← tyOfTerm e
    return mkAppN (mkConst ``LeanScript.Term.thunk_force) #[c.sg, c.gamma, τ, ← trans c t]
  if n == ``List.toArray || n == ``Array.mk then
    -- an array literal, written as the list of its elements
    return ← transListLit c e
  if n == ``Array.toList then
    throwError "`#leanscript_to_term`: a list and an array are different types here — \
      `List α` is the recursive tagged union it is and `Array α` is `Ty.array` — and \
      the grammar builds an array from all of its elements at once, so there is no \
      term for `Array.toList`"
  if n == ``Nat.brecOn || n == ``List.brecOn then
    return ← transBrecOn c e n lvls args
  if isSparseCasesOn n then
    if let some t ← transSparseCasesOn? c e n lvls args then return t
    -- a type whose tree has no partial dispatch: the exhaustive one, from the unfolding
    if let some e' ← unfoldHere? e then return ← trans c e'
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ← transCtorApp c e ci args
  | some (.recInfo ri) => return ← transRecApp c e ri lvls args
  | _ => pure ()
  if (← Meta.isMatcherApp e) || n.getString! == "casesOn" || n.getString! == "recOn" then
    if let some e' ← unfoldHere? e then
      return ← trans c e'
    throwError "`#leanscript_to_term`: cannot take apart the dispatch {n}"
  if let some g := c.global? n then
    let gt := mkAppN (mkConst ``LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
    return ← applyArgs c gt (mkConst n lvls) args
  if ← isInlinable n then
    return ← transInline c e n lvls args
  throwError "`#leanscript_to_term`: `{n}` is not declared in the signature and is not \
    inlinable, so a term cannot call it.  Either add a `GlobalDecl` named \
    \"{n.getString!}\" (or \"{n}\") to the signature, or mark `{n}` `@[inline]`."

/-- `if c then t else e`: the test must be a `Bool`. -/
partial def transIte (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `ite` needs its test"
  let inst := args[2]!
  let test ← boolOfDecidable c cnd inst
  mkBoolCases c test args[3]! args[4]!

/-- The `Bool` a decidable proposition tests. -/
partial def boolOfDecidable (c : TCtx) (cnd : Expr) (inst : Expr) : MetaM Expr := do
  match cnd.getAppFnArgs with
  | (``Eq, #[α, lhs, rhs]) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true then
        return ← trans c lhs
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.false then
        let t ← trans c lhs
        return ← mkBoolCases' c t (mkAppN (mkConst ``LeanScript.Term.bool_mk)
            #[c.sg, c.gamma, mkConst ``Bool.false])
          (mkAppN (mkConst ``LeanScript.Term.bool_mk) #[c.sg, c.gamma, mkConst ``Bool.true])
          (← tyOfType (mkConst ``Bool))
      -- `a = b` at a type with a `BEq`: the test is `a == b`
      match ← trySynthInstance (← mkAppM ``BEq #[α]) with
      | .some _ => return ← trans c (← mkAppM ``BEq.beq #[lhs, rhs])
      | _ => pure ()
      throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`"
  | _ =>
      let d ← whnf (mkApp2 (mkConst ``Decidable.decide) cnd inst)
      if d.find? (fun s => s.isConstOf ``Decidable.rec) |>.isSome then
        throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`: write the \
          condition as a `Bool`, or declare the decision procedure in the signature"
      trans c d

/-- `bool_casesOn`, from the two Lean branches. -/
partial def mkBoolCases (c : TCtx) (test : Expr) (thenB elseB : Expr) : MetaM Expr := do
  let τ ← tyOfTerm thenB
  mkBoolCases' c test (← trans c thenB) (← trans c elseB) τ

/-- `bool_casesOn`, from the two translated branches. -/
partial def mkBoolCases' (c : TCtx) (test t e τ : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``LeanScript.Term.bool_casesOn) #[c.sg, c.gamma, τ, test, t, e]

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
  let mut ts := mkAppN (mkConst ``LeanScript.Terms.nil) #[c.sg, c.gamma, σ]
  for i in [0:elems.size] do
    let a := elems[elems.size - 1 - i]!
    ts := mkAppN (mkConst ``LeanScript.Terms.cons) #[c.sg, c.gamma, σ, ← trans c a, ts]
  return mkAppN (mkConst ``LeanScript.Term.array_mk) #[c.sg, c.gamma, σ, ts]

/-- A spine of arguments at the given trees. -/
partial def mkSpine (c : TCtx) (tys : List Expr) (vals : Array Expr) : MetaM Expr := do
  unless tys.length == vals.size do
    throwError "`#leanscript_to_term`: this constructor carries {vals.size} values but \
      its tree has {tys.length} fields"
  let mut sp := mkAppN (mkConst ``LeanScript.Spine.nil) #[c.sg, c.gamma]
  let tysA := tys.toArray
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    let t ← trans c vals[j]!
    sp := mkAppN (mkConst ``LeanScript.Spine.cons)
      #[c.sg, c.gamma, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- An application of a constructor: it is built in place. -/
partial def transCtorApp (c : TCtx) (e : Expr) (ci : ConstructorVal)
    (args : Array Expr) : MetaM Expr := do
  if args.size < ci.numParams + ci.numFields then
    return ← trans c (← etaExpand e)
  if ci.induct == ``Array then
    return ← transListLit c e
  let ty ← tyOfTerm e
  let fields ← ctorValueArgs ci args
  -- a delay
  if let .thunk σ ← tyView ty then
    let some body := fields[0]?
      | throwError "`#leanscript_to_term`: a thunk needs its body"
    let inner := (mkApp body (mkConst ``Unit.unit)).headBeta
    return mkAppN (mkConst ``LeanScript.Term.thunk_mk)
      #[c.sg, c.gamma, σ, ← trans c inner]
  -- a one-field wrapper is its field
  if h : fields.size = 1 then
    let fty ← tyOfTerm fields[0]
    if fty == ty then return ← trans c fields[0]
  match ← tyView ty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst ``LeanScript.Term.record_mk) #[c.sg, c.gamma, fs, spine]
  | .taggedUnion l =>
      let ctys ← taggedUnionCtorTys l
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst ``LeanScript.Term.taggedUnion_mk)
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
      return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_mk)
        #[c.sg, c.gamma, l, hwf, mkNatLit ci.cidx, prf, spine]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      return mkAppN (mkConst ``LeanScript.Term.enum_mk)
        #[c.sg, c.gamma, s, ← mkFinLit nE ci.cidx]
  | .prim _ =>
      if ← isBoolTy ty then
        return mkAppN (mkConst ``LeanScript.Term.bool_mk)
          #[c.sg, c.gamma, toExpr (ci.cidx == 1)]
      throwError "`#leanscript_to_term`: {ci.name} builds a value of a terminal type, \
        which has no constructor in the language; write it as a literal"
  | _ =>
      throwError "`#leanscript_to_term`: the tree of {ci.induct} has no introduction \
        form in the grammar"

/-- A branch of a dispatch: the fields it binds become the innermost variables, the
    first field at index `0`. -/
partial def transBranch (c : TCtx) (minor : Expr) (ctorName : Name)
    (fieldTys : List Expr) : MetaM Expr := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let mut keep : Array Expr := #[]
    for x in xs do
      unless ← LeanScript.Deriving.erasedBinder (← inferType x) do
        keep := keep.push x
    unless keep.size == fieldTys.length do
      throwError "`#leanscript_to_term`: the branch of {ctorName} binds {keep.size} \
        values but its tree has {fieldTys.length} fields"
    let c' := c.pushFields ((keep.zip fieldTys.toArray).map fun (x, t) => (x.fvarId!, t))
    trans c' ((mkAppN minor xs).headBeta)

/-- A `match` that names only some of the constructors, as Lean compiled it: the
    auxiliary `f._sparseCasesOn_i`.  Its branches and its `else` branch are the branches
    and the default of the grammar's partial dispatch, so this is where
    `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` and
    `recTaggedUnion_casesOnWithDefault` are built.

    A type whose tree has no partial dispatch — a record, a terminal type, a one-field
    wrapper — is not handled here: the auxiliary is unfolded and the exhaustive dispatch
    is built instead, which is what `none` means. -/
partial def transSparseCasesOn? (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM (Option Expr) := do
  let some (arity, named) ← sparseCasesOnInfo? n | return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[0]!
  unless motive.isLambda do return none
  let major := args[1]!
  let sty ← tyOfTerm major
  -- the grammar has a partial dispatch for a sum type only
  let view ← tyView sty
  match view with
  | .enum _ | .taggedUnion _ | .recTaggedUnion _ _ => pure ()
  | _ => return none
  let .const indName _ := (← whnf (← inferType major)).getAppFn | return none
  let indInfo ← getConstInfoInduct indName
  let ctors := indInfo.ctors.toArray
  if named.length ≥ ctors.size then return none
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    tyOfType body
  -- the branches, by constructor number, and the default
  let mut minors : Array Expr := ctors.map fun _ => (Lean.mkConst ``True)
  for j in [0:named.length] do
    minors := minors.set! named[j]! args[2 + j]!
  let elseArg := args[2 + named.length]!
  let elseTy ← whnf (← inferType elseArg)
  let .forallE _ dom _ _ := elseTy | return none
  let dflt ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then
      throwError "`#leanscript_to_term`: the default branch of this `match` uses the \
        proof that the value is none of the constructors named, which the language \
        erases"
    return b
  let dfltTerm ← trans c dflt
  let scrut ← trans c major
  let kE := mkNatLit named.length
  let core ← match view with
    | .enum s =>
        let cases ← mkEnumSomeCases (transBranch c) c τ s named 0 minors ctors
        let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, nE])
        pure <| mkAppN (mkConst ``LeanScript.Term.enum_casesOnWithDefault)
          #[c.sg, c.gamma, τ, s, kE, scrut, cases, dfltTerm, hk]
    | .taggedUnion l =>
        let cases ← mkTaggedUnionSomeCases (transBranch c) c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, kE, scrut, cases, dfltTerm, hk]
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionSomeCases (transBranch c) c τ unfE named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, hwf, kE, scrut, cases, dfltTerm, hk]
    | _ => return none
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra)

/-- A structural recursion as Lean compiled it: `Nat.brecOn` or `List.brecOn`.

    The branch of a `brecOn` is given the **history** of the recursion — the value of the
    function at every smaller argument — and the grammar's folds give it the value at the
    immediate predecessor only.  So the history is reduced away here: the branch is
    instantiated at the two constructors of its type, with the head of the history
    replaced by a variable standing for the value at the predecessor, and what is left is
    the pair of branches of `Nat.rec` / `List.rec`, which
    `LeanScript.ToTerm.transRecCore` turns into `nat_rec` / `recTaggedUnion_rec` (or the
    case analysis, when the branch does not use that value).

    On a `Nat` the depth is not fixed at one.  If the branch at `n + 1` reads more of the
    history than its head, the depths `1, 2, …` are tried in turn: at depth `k` the
    branch is instantiated at `n + k + 1` with the `k + 1` nearest entries of the history
    replaced by variables, and the first depth at which nothing of the history is left is
    the depth of the `nat_rec` that is built — with the answers below it, the branch at
    `0, …, k`, as its base values.  A recursion that reads the history at an argument
    that is not a fixed number of steps back is refused. -/
partial def transBrecOn (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let isNat := n == ``Nat.brecOn
  let mIdx := if isNat then 0 else 1
  let arity := mIdx + 3
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[mIdx]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  let major := args[mIdx + 1]!
  let brecF := args[mIdx + 2]!
  let τLean ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    return body
  let τ ← tyOfType τLean
  let brecFTy ← inferType brecF
  -- the type of the history at a given argument
  let historyTy (t : Expr) : MetaM Expr := do
    return (← whnf (← instantiateForall brecFTy #[t])).bindingDomain!
  -- the branch at a constructor, with the head of the history read as `ih`
  let branchAt (scrutinee : Expr) (ih? : Option Expr) : MetaM Expr := do
    let ht ← historyTy scrutinee
    withLocalDeclD `history ht fun hist => do
      let body ← reduceBrecBodyDeep (mkApp2 brecF scrutinee hist)
      let body := match ih? with
        | some ih => substHistoryHead body hist.fvarId! ih
        | none => body
      if body.containsFVar hist.fvarId! then
        throwError "`#leanscript_to_term`: this recursion reads the value of the \
          function at an argument that is not the immediate predecessor, and the \
          grammar's folds descend one step at a time"
      return body
  -- what to do with the arguments a saturated `brecOn` is applied to on top of its own
  let finish (core : Expr) : MetaM Expr := do
    let extra := args.extract arity args.size
    if extra.isEmpty then return core
    applyArgs c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra
  if isNat then
    -- one step first: that is `Nat.rec`, and `transRecCore` may still turn it into the
    -- case analysis when the branch does not use the value of the fold
    let depth0? : Option (Array Expr) ←
      try
        let z ← branchAt (mkConst ``Nat.zero) none
        let s ← withLocalDeclD `n (mkConst ``Nat) fun nv =>
          withLocalDeclD `ih τLean fun ih => do
            let body ← branchAt (mkApp (mkConst ``Nat.succ) nv) (some ih)
            mkLambdaFVars #[nv, ih] body
        pure (some #[z, s])
      catch _ => pure none
    if let some minors := depth0? then
      let some (.recInfo ri) := (← getEnv).find? ``Nat.rec
        | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
      return ← finish (← transRecCore c ri τ minors major)
    -- more than one step: the branch at `n + k + 1`, with the `k + 1` nearest answers
    -- read out of the history and bound as `ih₀, …, ihₖ` — nearest first
    let stepAt (k : Nat) : MetaM Expr :=
      withLocalDeclD `n (mkConst ``Nat) fun nv => do
        let mut scrutE := nv
        for _ in [0:k + 1] do scrutE := mkApp (mkConst ``Nat.succ) scrutE
        let ihDecls : Array (Name × (Array Expr → MetaM Expr)) :=
          (Array.range (k + 1)).map fun i =>
            (Name.mkSimple s!"ih{i}", fun _ => pure τLean)
        withLocalDeclsD ihDecls fun ihs => do
          let ht ← historyTy scrutE
          withLocalDeclD `history ht fun hist => do
            let body ← reduceBrecBodyDeep (mkApp2 brecF scrutE hist)
            let body := substHistory body hist.fvarId! ihs
            if body.containsFVar hist.fvarId! then
              throwError "`#leanscript_to_term`: this recursion reads the value of the \
                function at an argument that is not one of its {k + 1} nearest \
                predecessors"
            mkLambdaFVars (#[nv] ++ ihs) body
    let mut found : Option (Nat × Expr) := none
    for k in [1:maxNatRecDepth + 1] do
      if found.isNone then
        found ← try pure (some (k, ← stepAt k)) catch _ => pure none
    let some (k, s) := found
      | throwError "`#leanscript_to_term`: this recursion does not descend by a fixed \
          number of steps — the fold of a natural number the grammar has gives its branch \
          the answers at the `k + 1` nearest predecessors, so a call at an argument such \
          as `n / 2` has no term"
    -- the answers below the depth: the branch at `0, …, k`, each one allowed to read the
    -- answers already known
    let mut baseVals : Array Expr := #[]
    for j in [0:k + 1] do
      let mut jE : Expr := mkConst ``Nat.zero
      for _ in [0:j] do jE := mkApp (mkConst ``Nat.succ) jE
      let ht ← historyTy jE
      let v ← withLocalDeclD `history ht fun hist => do
        let body ← reduceBrecBodyDeep (mkApp2 brecF jE hist)
        let body := substHistory body hist.fvarId! baseVals.reverse
        if body.containsFVar hist.fvarId! then
          throwError "`#leanscript_to_term`: the answer at {j} reads the value of the \
            function at an argument the fold has not computed yet"
        pure body
      baseVals := baseVals.push v
    let scrutT ← trans c major
    let natTy ← tyOfType (mkConst ``Nat)
    -- the base values are written nearest first: `(f k, …, f 1, f 0)`
    let baseTerms ← baseVals.reverse.mapM fun v => trans c v
    let base := mkNatRecBase c τ baseTerms
    let core ← lambdaBoundedTelescope s (k + 2) fun xs body => do
      let c' := c.pushFields
        (#[(xs[0]!.fvarId!, natTy)] ++ (xs.extract 1 xs.size).map fun x => (x.fvarId!, τ))
      return mkAppN (mkConst ``LeanScript.Term.nat_rec)
        #[c.sg, c.gamma, τ, mkNatLit k, scrutT, base, ← trans c' body]
    return ← finish core
  let minors ←
    do
      let α := args[0]!
      let listTy := mkApp (mkConst ``List [← getDecLevel α]) α
      let nil := mkApp (mkConst ``List.nil [← getDecLevel α]) α
      let z ← branchAt nil none
      let s ← withLocalDeclD `head α fun hd =>
        withLocalDeclD `tail listTy fun tl =>
          withLocalDeclD `ih τLean fun ih => do
            let cons := mkApp3 (mkConst ``List.cons [← getDecLevel α]) α hd tl
            let body ← branchAt cons (some ih)
            mkLambdaFVars #[hd, tl, ih] body
      pure #[z, s]
  let some (.recInfo ri) := (← getEnv).find? ``List.rec
    | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
  finish (← transRecCore c ri τ minors major)

/-- An application of a recursor. -/
partial def transRecApp (c : TCtx) (e : Expr) (ri : RecursorVal) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  unless ri.numMotives == 1 && ri.numIndices == 0 do
    throwError "`#leanscript_to_term`: {ri.name} is not an eliminator the language has"
  let arity := ri.numParams + 1 + ri.numMinors + 1
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[ri.numParams]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {ri.name} is not a function"
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {ri.name} is used with a dependent motive, \
        which the language has no eliminator for"
    tyOfType body
  let minors := args.extract (ri.numParams + 1) (ri.numParams + 1 + ri.numMinors)
  let major := args[ri.numParams + 1 + ri.numMinors]!
  let core ← transRecCore c ri τ minors major
  let extra := args.extract arity args.size
  if extra.isEmpty then return core
  applyArgs c core (mkAppN (mkConst ri.name lvls) (args.extract 0 arity)) extra

/-- The eliminator a recursor becomes. -/
partial def transRecCore (c : TCtx) (ri : RecursorVal) (τ : Expr) (minors : Array Expr)
    (major : Expr) : MetaM Expr := do
  let ind := ri.getMajorInduct

  let scrut ← trans c major
  match ind with
  | ``Nat =>
      -- the fold, or the case analysis when the branch does not use the recursive value
      let natTy ← tyOfType (mkConst ``Nat)
      let z ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 2) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[1]!.fvarId! then
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy), (xs[1]!.fvarId!, τ)]
          return mkAppN (mkConst ``LeanScript.Term.nat_rec)
            #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], ← trans c' body]
        else
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy)]
          return mkAppN (mkConst ``LeanScript.Term.nat_casesOn)
            #[c.sg, c.gamma, τ, scrut, z, ← trans c' body]
  | ``List =>
      let sty ← tyOfTerm major
      let .recTaggedUnion l hwf ← tyView sty
        | throwError "`#leanscript_to_term`: {major} is not a list"
      let (cp, fieldsNE, restL) ← listSchemaParts l
      -- the head of the payload is written in the scope the binder opens; as a *value*
      -- of the language it is that tree, unfolded — which for an element type that is
      -- not an occurrence is the tree itself
      let σ ← match ← nonEmptyTys fieldsNE with
        | [σ, _] => bundleTyE 0 (← treeOfTyE σ)
        | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
      let nil ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 3) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[2]!.fvarId! then
          -- the fold: the branch is given the value of the fold at the tail
          let c' := c.pushFields
            #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty), (xs[2]!.fvarId!, τ)]
          let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
          let ι := tyWfInE 1
          let depth := mkNatLit 0
          let nilFs := mkApp (mkConst ``List.nil [Level.zero]) ι
          let consFs := mkApp2
            (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
            ι fieldsNE
          -- the branches of a depth-zero fold: one answer each, none of them looking
          -- further down
          let nilBranch := mkAppN (mkConst ``LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, nilFs, τ, depth, nil]
          let consBranch := mkAppN (mkConst ``LeanScript.FoldKBranch.here)
            #[c.sg, l, bindE, c.gamma, consFs, τ, depth, ← trans c' body]
          let restCases := mkAppN (mkConst ``LeanScript.TaggedUnionFoldKCasesRest.nil)
            #[c.sg, l, bindE, c.gamma, τ, depth]
          let consCases := mkAppN (mkConst ``LeanScript.CtorsWithPayloadFoldKCases.here)
            #[c.sg, l, bindE, c.gamma, τ, depth, fieldsNE, restL, consBranch, restCases]
          let cases := mkAppN (mkConst ``LeanScript.TaggedUnionFoldKCases.skip)
            #[c.sg, l, bindE, c.gamma, τ, depth, cp, nilBranch, consCases]
          return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_rec)
            #[c.sg, c.gamma, τ, l, hwf, depth, scrut, cases]
        else
          -- the case analysis: the branches are over the unfolded schema, in which the
          -- tail is a list again
          let (cpU, fieldsU, restU) ←
            listSchemaParts (← reduceTy
              (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf))
          let c' := c.pushFields #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty)]
          let restCases := mkAppN (mkConst ``LeanScript.TaggedUnionCasesRest.nil)
            #[c.sg, c.gamma, τ]
          let consCases := mkAppN (mkConst ``LeanScript.CtorsWithPayloadCases.here)
            #[c.sg, c.gamma, τ, fieldsU, restU, ← trans c' body, restCases]
          let cases := mkAppN (mkConst ``LeanScript.TaggedUnionCases.skip)
            #[c.sg, c.gamma, τ, cpU, nil, consCases]
          return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
  | ``Bool =>
      return mkAppN (mkConst ``LeanScript.Term.bool_casesOn)
        #[c.sg, c.gamma, τ, scrut, ← trans c minors[1]!, ← trans c minors[0]!]
  | _ =>
      let indInfo ← getConstInfoInduct ind
      if indInfo.isRec then
        throwError "`#leanscript_to_term`: {ind} is a recursive type, and the only folds \
          the translation produces are `nat_rec` and `recTaggedUnion_rec`, for `Nat` and \
          `List`"
      let sty ← tyOfTerm major
      let ctors := indInfo.ctors.toArray
      match ← tyView sty with
      | .record fs =>
          let fieldTys ← recordFieldTys fs
          let body ← transBranch c minors[0]! ctors[0]! fieldTys
          return mkAppN (mkConst ``LeanScript.Term.record_casesOn)
            #[c.sg, c.gamma, τ, fs, scrut, body]
      | .taggedUnion l =>
          -- a `match` with a wildcard repeats one branch: that is the partial dispatch
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkTaggedUnionSomeCases (transBranch c) c τ l named 0 minors ctors
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, lenE])
            return mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOnWithDefault)
              #[c.sg, c.gamma, τ, l, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkTaggedUnionCases (transBranch c) c τ l 0 minors ctors
          return mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, scrut, cases]
      | .enum s =>
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkEnumSomeCases (transBranch c) c τ s named 0 minors ctors
            let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, nE])
            return mkAppN (mkConst ``LeanScript.Term.enum_casesOnWithDefault)
              #[c.sg, c.gamma, τ, s, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkEnumCases (transBranch c) c τ s minors ctors
          return mkAppN (mkConst ``LeanScript.Term.enum_casesOn)
            #[c.sg, c.gamma, τ, s, scrut, cases]
      | .prim _ =>
          if (← isBoolTy sty) && minors.size == 2 then
            return mkAppN (mkConst ``LeanScript.Term.bool_casesOn)
              #[c.sg, c.gamma, τ, scrut, ← transBranch c minors[1]! ctors[1]! [],
                ← transBranch c minors[0]! ctors[0]! []]
          throwError "`#leanscript_to_term`: a terminal type has no dispatch of its own"
      | _ =>
          if minors.size == 1 then
            -- a one-field wrapper: its case analysis substitutes the value
            return ← transBranch c minors[0]! ctors[0]! [← tyOfTerm major]
          throwError "`#leanscript_to_term`: the tree of {ind} has no dispatch in the \
            grammar"

/-- A call of an inlinable function: its definition is translated, once, and used
    here. -/
partial def transInline (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let info ← getConstInfo n
  let some val := info.value? |
    throwError "`#leanscript_to_term`: `{n}` has no definition to inline"
  let val := val.instantiateLevelParams info.levelParams lvls
  -- how many leading arguments does the language erase?
  let nLeading ← forallTelescopeReducing info.type fun xs _ => do
    let mut k := 0
    for h : i in [0:xs.size] do
      if i ≥ args.size then break
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then k := k + 1 else break
    return k
  let leading := args.extract 0 nLeading
  let headVal := (mkAppN val leading).headBeta
  if headVal.hasFVar || headVal.hasMVar then
    let some e' ← unfoldHere? e
      | throwError "`#leanscript_to_term`: cannot inline `{n}`"
    return ← trans c e'
  let t ← transClosedCached c headVal
  applyArgs c t (mkAppN (mkConst n lvls) leading) (args.extract nLeading args.size)

/-- Translate a closed definition, once: the translation is stored as a function of the
    context, and two definitions of the same shape share one tree. -/
partial def transClosedCached (c : TCtx) (v : Expr) : MetaM Expr := do
  if v.hasFVar || v.hasMVar then return ← trans c v
  let st ← cacheRef.get
  if let some entry := st.entries.find? fun en => en.sg == c.sg && en.src == v then
    cacheRef.modify fun s => { s with hits := s.hits + 1 }
    return mkApp entry.fn c.gamma
  let fn ← withLocalDeclD `Γ ctxE fun g => do
    let t ← trans { c with base := g, binders := #[] } v
    mkLambdaFVars #[g] t
  let h := fn.hash
  let st ← cacheRef.get
  let shared? := st.entries.find? fun en => en.hash == h && en.fn == fn
  let fn := match shared? with | some en => en.fn | none => fn
  cacheRef.modify fun s =>
    { s with
      entries := s.entries.push { sg := c.sg, src := v, fn := fn, hash := h },
      shared := if shared?.isSome then s.shared + 1 else s.shared }
  return mkApp fn c.gamma

end

end LeanScript.ToTerm

end

end
