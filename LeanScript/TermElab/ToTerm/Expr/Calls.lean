module

public meta import LeanScript.TermElab.ToTerm.Expr.Loops
public meta import Lean.Compiler.ExternAttr

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: calls

The translation of calls of helper definitions, of library functions and externs, of
`decide`, of `Fin.foldl`, and of functions on quotients, parameterised by the expression
translator `tr` (`LeanScript.TermElab.ToTerm.Expr`).
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

variable (tr : Loc → Expr → TM Src)

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
                      fn := c,
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
          for x in xs.reverse do body := Src.lam (some (← tyStx L0 (← inferType x))) body
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

/-- A call of the extern `entry` (an entry of the catalogue, `LeanInitPureExtern.entry`)
    whose Lean function is `fn`, applied to `args`: `Neu.extern (.entry _ …) args'`.  The
    arguments of the extern are the explicit arguments of `fn` that are values (not types,
    proofs or `()`), the default value of an `[Inhabited α]` argument (`Array.get!Internal`
    takes the default as an argument of the extern), and the function `fun x y => x == y` of a
    `[BEq α]` argument (`Array.contains`); the proofs are erased (the evaluator of the
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
    else if bi.isInstImplicit && d.isAppOfArity ``BEq 1 then
      -- a `[BEq α]` argument is its function `beq` (`fun x y => x == y`), which the extern
      -- takes as an argument (`Array.contains`, `Array.idxOf?`)
      let α := d.appArg!
      let f ← withLocalDeclD `x α fun x => withLocalDeclD `y α fun y => do
        mkLambdaFVars #[x, y] (← mkAppOptM ``BEq.beq #[α, a, x, y])
      vals := vals.push f
    else if bi.isExplicit && !(← isProp d) && !(← isType a) && !(← isUnitType d) then
      vals := vals.push a
    ty := b.instantiate1 a
  -- an argument that another argument also computes (the array of `(xs.map f).filter p`,
  -- whose default bound is `(xs.map f).size`) is bound once: `let a := xs.map f; a.filter p 0
  -- a.size`, not two computations of `xs.map f`
  let trivial (v : Expr) : Bool :=
    v.isFVar || v.isConst || v.isLit || v.isLambda || v.hasLooseBVars || v.isMVar
  if let some v := vals.find? fun v => !trivial v &&
      vals.any fun w => w != v && (w.find? (· == v)).isSome then
    let call := mkAppN fn args
    let body ← kabstract call v
    if body.hasLooseBVars then
      return ← tr L (.letE `a (← inferType v) v body false)
  let sc := `LeanScript.LeanInitPureExtern ++ entry
  let some info := (← getEnv).find? sc
    | fail m!"the entry `{entry}` of the catalogue of externs has no shorthand `{sc}`"
  let nFields := explicitBinderCount info.type
  let holes ← (List.replicate nFields ()).toArray.mapM fun _ => `(_)
  let entryStx ← `($(mkIdent (`_root_ ++ sc)) $holes*)
  let argSrcs ← vals.mapM (tr L)
  return .extern entryStx argSrcs

/-- Is `a` a type of functions (`Nat → Nat`)? -/
def isFunType (a : Expr) : MetaM Bool := do
  if !(← isType a) then return false
  let a ← whnf a
  return a.isForall && !(← isProp a)

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
    -- a function of values that are functions (`Array.map g` on an array of functions) is
    -- unfolded rather than the extern: JavaScript uncurries `fun x => fun y => b` to
    -- `(x, y) => b`, which the operations of the externs (which take `(x) => …`) do not accept
    unless !isExtern (← getEnv) c && (← args.anyM fun a => isFunType a) do
      return ← externCall tr L entry fn args
    if let some e' ← unfoldCall? e then return ← tr L e'
    return ← externCall tr L entry fn args
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

/-- The value of a float literal (`1.0`, `2`, `-1.5`: `OfScientific.ofScientific`, `OfNat.ofNat`,
    `Float.ofScientific`, `Float.ofNat`, their negations), or `none`. -/
partial def floatLit? (e : Expr) : MetaM (Option Float) := do
  let e ← instantiateMVars e
  let nat? (n : Expr) : Option Nat := match n.rawNatLit? with
    | some k => some k
    | none => n.nat?
  let bool? (b : Expr) : Option Bool :=
    if b.isConstOf ``Bool.true then some true
    else if b.isConstOf ``Bool.false then some false else none
  let isFloat (t : Expr) : Bool := t.isConstOf ``Float
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``OfScientific.ofScientific, #[t, _, m, s, x] =>
    if !isFloat t then return none
    return do Float.ofScientific (← nat? m) (← bool? s) (← nat? x)
  | some ``Float.ofScientific, #[m, s, x] =>
    return do Float.ofScientific (← nat? m) (← bool? s) (← nat? x)
  | some ``OfNat.ofNat, #[t, n, _] =>
    if !isFloat t then return none
    return (nat? n).map Float.ofNat
  | some ``Float.ofNat, #[n] => return (nat? n).map Float.ofNat
  | some ``Neg.neg, #[t, _, x] =>
    if !isFloat t then return none
    return (← floatLit? x).map (- ·)
  | some ``Float.neg, #[x] => return (← floatLit? x).map (- ·)
  | _, _ => return none

/-- Is the float finite and non-zero (its model unpacks to `.finite`)?  Then `x = c` is
    `x == c` (`decide_float_eq_beq_of_finite`). -/
def floatFiniteNonzero (c : Float) : Bool :=
  match Float.Model.UnpackedFloat.unpack .binary64 c.toBits.toBitVec with
  | .finite .. => true
  | _ => false

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
      return ← externCall tr L entry inst.getAppFn inst.getAppArgs
    match c', inst.getAppArgs with
    | ``instDecidableAnd, #[q, r, dq, dr] =>
        return ← tr L (mkApp2 (mkConst ``and) (dec q dq) (dec r dr))
    | ``instDecidableOr, #[q, r, dq, dr] =>
        return ← tr L (mkApp2 (mkConst ``or) (dec q dq) (dec r dr))
    | ``instDecidableNot, #[q, dq] =>
        return ← tr L (mkApp (mkConst ``not) (dec q dq))
    -- `a = b` on `Char`: `Char` is a leaf, so the instance's `decEq a.val b.val` (a
    -- projection of the leaf) has no translation; the language compares the one-character
    -- strings `"".push a` and `"".push b` instead (`String.push` and `String.decEq` are
    -- externs), which are equal exactly when `a = b`
    | ``instDecidableEqChar, #[a, b] =>
        let one (c : Expr) : Expr := mkApp2 (mkConst ``String.push) (mkStrLit "") c
        let (x, y) := (one a, one b)
        return ← tr L (dec (← mkEq x y) (mkApp2 (mkConst ``String.decEq) x y))
    -- `a = b` on `Float` (a `match` on float literals, `| 1.0 => …`): `Float` is a leaf, so the
    -- instance's comparison of the models has no translation.  Against a finite non-zero
    -- literal `c` it is `x == c` (`Float.beq`, `===` in JavaScript;
    -- `decide_float_eq_beq_of_finite`), otherwise the comparison of the bit patterns
    -- (`decide_float_eq_toBits`), which tells the zeros apart and NaN equal to itself
    | ``instDecidableEqFloat, #[a, b] =>
        let finite (x : Expr) : MetaM Bool := return (← floatLit? x).any floatFiniteNonzero
        if ← finite b then return ← tr L (mkApp2 (mkConst ``Float.beq) a b)
        if ← finite a then return ← tr L (mkApp2 (mkConst ``Float.beq) b a)
        let bits (c : Expr) : Expr := mkApp (mkConst ``Float.toBits) c
        let (x, y) := (bits a, bits b)
        return ← tr L (dec (← mkEq x y) (mkApp2 (mkConst ``UInt64.decEq) x y))
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
        return ← trQuotApp tr L g q #[]
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

end LeanScript.Gen

end
