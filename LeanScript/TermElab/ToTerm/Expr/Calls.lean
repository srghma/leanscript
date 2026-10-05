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
    unless ← isErasedCtorField bi d do kept := kept.push a
    ty := b.instantiate1 a
  return if kept.size == 1 then some kept[0]! else none

/-- Is the entry one of the hash maps with string keys (`StrMapExtern`)? -/
def isStrMapEntry (entry : Name) : Bool :=
  entry.toString.startsWith "lean_str_map_"

/-- Is the call `Std.HashMap.f α β instBEq instHashable …` one on string keys compared and hashed
    by `String`'s own instances (the hash maps of `Ty.strMap`, whose functions are the entries
    of `StrMapExtern`)?  Any other hash map is not a type of the language: its functions are
    unfolded. -/
def strKeyedHashMapCall (args : Array Expr) : MetaM Bool := do
  if args.size < 4 then return false
  unless (← whnf args[0]!).isConstOf ``String do return false
  let beq ← synthInstance (← mkAppM ``BEq #[mkConst ``String])
  let hash ← synthInstance (← mkAppM ``Hashable #[mkConst ``String])
  return (← withReducibleAndInstances (isDefEq args[2]! beq)) &&
    (← withReducibleAndInstances (isDefEq args[3]! hash))

/-- A call of the extern `entry` (an entry of the catalogue, `LeanInitPureExtern.entry`)
    whose Lean function is `fn`, applied to `args`: `Neu.extern (.entry _ …) args'`.  The
    arguments of the extern are the explicit arguments of `fn` that are values (not types,
    proofs or `()`), the default value of an `[Inhabited α]` argument (`Array.get!Internal`
    takes the default as an argument of the extern), and the function `fun x y => x == y` of a
    `[BEq α]` argument (`Array.contains`); the proofs are erased (the evaluator of the
    extern decides them).  The type arguments of the entry (`αt` of `lean_array_push αt`) are
    found by unification with the types of the arguments. -/
partial def externCall (L : Loc) (entry : Name) (fn : Expr) (args : Array Expr) : TM Src := do
  -- the entries of the hash maps with string keys (`StrMapExtern`) do not take the `BEq`
  -- instance of the key: it is `String`'s own (`strKeyedHashMapCall`)
  let strMap := isStrMapEntry entry
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
    else if bi.isInstImplicit && d.isAppOfArity ``BEq 1 && !strMap then
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
  -- A call of a local function (`f x`) is left alone: the optimiser's common subexpression
  -- elimination (`Term.cseLetE`) shares it, keeping the calls in source order, whereas binding
  -- it here would compute it before the argument containing it (`f i ++ f n ++ f i ++ f n`
  -- would compute `f n` first).
  let trivial (v : Expr) : Bool :=
    v.isFVar || v.isConst || v.isLit || v.isLambda || v.hasLooseBVars || v.isMVar ||
    v.getAppFn.isFVar
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

/-- The fixed-width unsigned integer type whose values are the bit vectors of width `w`
    (`UInt32` for `BitVec 32`: a structure around a `BitVec 32`), if there is one. -/
def uintOfWidth? : Nat → Option Name
  | 8 => some ``UInt8
  | 16 => some ``UInt16
  | 32 => some ``UInt32
  | 64 => some ``UInt64
  | _ => none

/-- The constructors and projections of the fixed-width unsigned integers, between the integer
    and its bit vector (`UInt32.ofBitVec`, `UInt32.toBitVec`): externs of the catalogue, not
    erased wrappers, since the integer and the bit vector are different leaves. -/
def uintBitVecConv : List Name :=
  [``UInt8.ofBitVec, ``UInt16.ofBitVec, ``UInt32.ofBitVec, ``UInt64.ofBitVec,
   ``UInt8.toBitVec, ``UInt16.toBitVec, ``UInt32.toBitVec, ``UInt64.toBitVec]

/-- The operations of `BitVec w` that are, at the widths of `uintOfWidth?`, the operation of
    the same name of the fixed-width integer (an extern): `BitVec.add` is `UInt32.add`, …
    (`LeanScript/TermElab/ToTerm/BitVecOps.lean`). -/
def bitvecOpTable : List (Name × Name) :=
  [(``BitVec.add, `add), (``BitVec.sub, `sub), (``BitVec.mul, `mul), (``BitVec.udiv, `div),
   (``BitVec.umod, `mod), (``BitVec.neg, `neg), (``BitVec.and, `land), (``BitVec.or, `lor),
   (``BitVec.xor, `xor), (``BitVec.not, `complement)]

/-- The decisions of `BitVec w` that are, at the widths of `uintOfWidth?`, the decision of the
    fixed-width integer (an extern): `instDecidableLtBitVec` is `UInt32.decLt`, …
    (`LeanScript/TermElab/ToTerm/BitVecOps.lean`). -/
def bitvecDecTable : List (Name × Name) :=
  [(``instDecidableEqBitVec, `decEq), (``BitVec.decEq, `decEq),
   (``instDecidableLtBitVec, `decLt), (``instDecidableLeBitVec, `decLe)]

/-- `c w x₁ … xₖ`, a function of `bitvecOpTable` or `bitvecDecTable` (`table`) at a width `w`
    of `uintOfWidth?`: the fixed-width integer type `U`, the name of its function and the
    arguments read as values of `U` (`U.ofBitVec xᵢ`, the identity in JavaScript). -/
def bitvecUIntCall? (table : List (Name × Name)) (c : Name) (args : Array Expr) :
    MetaM (Option (Name × Name × Array Expr)) := do
  let some op := table.lookup c | return none
  let some w := args[0]? | return none
  let some n ← natLit? w | return none
  let some u := uintOfWidth? n | return none
  let xs := args[1:].toArray
  if xs.isEmpty then return none
  return some (u, u ++ op, xs.map (mkApp (mkConst (u ++ `ofBitVec))))

/-- An operation of `BitVec w` at a width of a fixed-width integer (`BitVec.add x y` at width
    `32`): the operation of the integer, on the bit vectors read as integers, read back as a bit
    vector (`(UInt32.add (.ofBitVec x) (.ofBitVec y)).toBitVec`, proved equal by
    `bitvec32_add`), or `none`.  The definition of `BitVec.add` takes the leaf apart
    (`x.toNat`), which has no translation. -/
def bitvecOpCall? (c : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let some (u, f, xs) ← bitvecUIntCall? bitvecOpTable c args | return none
  unless xs.size == (if c == ``BitVec.neg || c == ``BitVec.not then 1 else 2) do return none
  return some (mkApp (mkConst (u ++ `toBitVec)) (mkAppN (mkConst f) xs))

/-- A shift of `BitVec w` (`BitVec.shiftLeft x n`, `BitVec.ushiftRight x n`, by a natural
    number `n`) at a width `w` of a fixed-width integer `U`, read as the shift of `U`, which
    takes its count modulo `w` where the bit vector's answers `0` from `w` on
    (`LeanScript/TermElab/ToTerm/BitVecOps.lean`, `bitvec32_shiftLeft`, …):

* by a bit vector `y` of the same width (`x <<< y` is `x <<< y.toNat`):
  `if U.ofBitVec y < w then (U.ofBitVec x <<< U.ofBitVec y).toBitVec else 0`;
* by a literal `k`: `(U.ofBitVec x <<< k).toBitVec` when `k < w`, `0` otherwise;
* by any other `n`: `if n < w then (U.ofBitVec x <<< U.ofNat n).toBitVec else 0`. -/
def bitvecShiftCall? (c : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let op ← if c == ``BitVec.shiftLeft then pure `shiftLeft
    else if c == ``BitVec.ushiftRight then pure `shiftRight else return none
  unless args.size == 3 do return none
  let some w ← natLit? args[0]! | return none
  let some u := uintOfWidth? w | return none
  let uTy := Lean.mkConst u
  let x := mkApp (mkConst (u ++ `ofBitVec)) args[1]!
  let n := args[2]!
  let zero ← mkNumeral (mkApp (mkConst ``BitVec) args[0]!) 0
  let wU ← mkNumeral uTy w
  let shift (k : Expr) : Expr := mkApp (mkConst (u ++ `toBitVec)) (mkApp2 (mkConst (u ++ op)) x k)
  -- the count is read twice (by the test and by the shift): one that is computed is bound
  -- first (`let c := 32 - k; if c < 32 then … else 0`)
  let share (v : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
    if v.isFVar || v.isConst || v.isLit || v.hasLooseBVars then k v
    else withLetDecl `c (← inferType v) v fun f => do mkLetFVars #[f] (← k f)
  let n' ← instantiateMVars n
  if n'.isAppOfArity ``BitVec.toNat 2 then
    if (← natLit? n'.appFn!.appArg!) == some w then
      return some (← share n'.appArg! fun yb => do
        let y := mkApp (mkConst (u ++ `ofBitVec)) yb
        mkAppM ``ite #[← mkAppM ``LT.lt #[y, wU], shift y, zero])
  if let some k ← natLit? n then
    if k < w then return some (shift (← mkNumeral uTy k)) else return some zero
  let wN := mkNatLit w
  return some (← share n fun n => do
    mkAppM ``ite #[← mkAppM ``LT.lt #[n, wN], shift (mkApp (mkConst (u ++ `ofNat)) n), zero])

/-- `BitVec.toNat x` at a width `w` of a fixed-width integer `U`: `(U.ofBitVec x).toNat`
    (`bitvec32_toNat`, …), an extern of the catalogue. -/
def bitvecToNatCall? (c : Name) (args : Array Expr) : MetaM (Option Expr) := do
  unless c == ``BitVec.toNat && args.size == 2 do return none
  let some w ← natLit? args[0]! | return none
  let some u := uintOfWidth? w | return none
  return some (mkApp (mkConst (u ++ `toNat)) (mkApp (mkConst (u ++ `ofBitVec)) args[1]!))

/-- A decision of `BitVec w` at a width of a fixed-width integer (`instDecidableLtBitVec x y`
    at width `32`): `decide` of the decision of the integer, on the bit vectors read as
    integers (`decide (UInt32.ofBitVec x < .ofBitVec y)` by `UInt32.decLt`, proved equal by
    `bitvec32_lt`), or `none`. -/
def bitvecDecide? (c : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let some (_, f, xs) ← bitvecUIntCall? bitvecDecTable c args | return none
  unless xs.size == 2 do return none
  let inst := mkAppN (mkConst f) xs
  let ty ← whnfR (← inferType inst)
  unless ty.isAppOfArity ``Decidable 1 do return none
  return some (mkApp2 (mkConst ``Decidable.decide) ty.appArg! inst)

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
  -- an operation of `BitVec w` at the width of a fixed-width integer is the integer's
  if let some e' ← bitvecOpCall? c args then return ← tr L e'
  if let some e' ← bitvecShiftCall? c args then return ← tr L e'
  if let some e' ← bitvecToNatCall? c args then return ← tr L e'
  if let some entry := externTable.find? c then
    if isStrMapEntry entry && !(← strKeyedHashMapCall args) then
      if let some e' ← unfoldCall? e then return ← tr L e'
      fail m!"the call{indentExpr e}\nis on a hash map whose keys are not strings compared and \
        hashed by `String`'s own instances (only those are a type of the language, `Ty.strMap`)"
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
    -- a decision of `BitVec w` at the width of a fixed-width integer is the integer's
    if let some e' ← bitvecDecide? c' inst.getAppArgs then return ← tr L e'
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
    -- `a < b` and `a ≤ b` on `Char`: the instances compare `a.val` and `b.val` (projections of
    -- the leaf); the language compares the one-character strings instead, with the extern
    -- `String.decidableLT` (`decide_char_lt_push`, `decide_char_le_push`): `a ≤ b` is
    -- `!("".push b < "".push a)`, as `String.decLE` decides it
    | ``Char.instDecidableLt, #[a, b] | ``Char.instDecidableLe, #[a, b] =>
        let one (c : Expr) : Expr := mkApp2 (mkConst ``String.push) (mkStrLit "") c
        let strLt (x y : Expr) : Expr :=
          dec (mkApp4 (mkConst ``LT.lt [Level.zero]) (mkConst ``String) (mkConst ``String.instLT) x y)
            (mkApp2 (mkConst ``String.decidableLT) x y)
        if c' == ``Char.instDecidableLt then return ← tr L (strLt (one a) (one b))
        return ← tr L (mkApp (mkConst ``not) (strLt (one b) (one a)))
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
