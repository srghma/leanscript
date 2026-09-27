module

public meta import LeanScript.GenElab.GetCtor
public meta import LeanScript.TermElab.Anf
public meta import Lean.Elab.PreDefinition.Structural.Eqns
public meta import Lean.Elab.PreDefinition.WF.Eqns

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: translation state and helpers

The state of a translation (`TS`, `TM`), the context of the expression being translated
(`Loc`), and the helpers of the expression translator in `LeanScript.TermElab.ToTerm.Expr`: syntax
builders, the recognition of nested datatypes, mutual groups, constructor fields, and the
parameters a recursive call changes.  See `LeanScript.TermElab.ToTerm` for the translation itself.
-/

open Lean Meta Elab Term
open LeanScript.Anf (Src)

namespace LeanScript.Gen

/-- The state of a translation: the state of the type translator, and whether a declared
    datatype has been used (then the term is over the current program). -/
structure TS where
  st : St
  usesData : Bool := false
  /-- Fields of type `α` of a type-indexed family opened at an index other than the one the
      family is read at (`withFields`), with that index and the element type: they have no
      value of their Lean type in the language. -/
  unusable : Std.HashMap FVarId (Name × Expr × Expr) := {}
  /-- Fields `f : Fin m → T` of an opened constructor that the language reads as
      `Nat → Option T` (`finOptArrow`: the codomain is on a recursive cycle). -/
  optFields : Std.HashSet FVarId := {}
  /-- The helper definitions whose translation is being inlined (`trHelper`), innermost last:
      a helper that calls itself back through another is refused. -/
  inlining : Array Name := #[]

abbrev TM := StateT TS TermElabM

/-- Run a step of the type translator. -/
def lm {α : Type} (x : M α) : TM α := fun s => do
  let (a, st) ← (x.run s.st : MetaM _)
  return (a, { s with st })

/-- Where the members of the block recursed on sit inside a field that holds them inside an
    `Array` or a function (`node (qs : Array Q)`, `node (f : Nat → G)`).  In a branch of the
    fold, such a field holds, at each of these places, the pair of the subvalue and the answer
    at it (`DSig.Block.recBody`). -/
inductive NShape where
  /-- A member of the block, directly: the pair of the subvalue and the answer at it. -/
  | hole
  /-- The member `Option X` that the language puts for a member `X` read through a field
      `Fin m → X` (`finOptArrow`): the pair of the subvalue and the answer at it, which is
      `none` or `some` of the answer at the `X` inside. -/
  | optHole
  /-- An array of such. -/
  | array (s : NShape)
  /-- A function whose results are such. -/
  | fn (s : NShape)
  deriving Inhabited, BEq

/-- The variables in scope and what the translation knows about them. -/
structure Loc where
  /-- The variables of the term's context, outermost first: `some x` a Lean local, `none` a
      variable with no Lean local (the answer of a recursive call, a pair of a subvalue and
      its answer, …). -/
  slots : Array (Option FVarId) := #[]
  /-- A subvalue the recursion reached ↦ the variable holding the answer at it. -/
  ans : Std.HashMap FVarId Nat := {}
  /-- The functions of the (mutual) group of the function translated, when it is recursive:
      each recurses on one member of the block, and calls of them are answers of the fold. -/
  fns : Array Name := #[]
  /-- The Lean types of the members of the block recursed on (inside a branch of the fold). -/
  mems : Array Expr := #[]
  /-- The fields of a branch that hold members of the block inside an `Array` or a function,
      paired with their answers. -/
  nest : Std.HashMap FVarId NShape := {}
  /-- Its parameters. -/
  params : Array Expr := #[]
  /-- The positions of its parameters that only name an index of a later parameter's type
      (`n` in `Vec.sum {n} (v : Vec Nat n)`): they have no value in the language, and a
      recursive call may change them. -/
  idxParams : Array Nat := #[]
  /-- The program. -/
  prog? : Option ProgInfo := none
  /-- The number of visible blocks (those of the program). -/
  c : Nat := 0
  /-- A subvalue whose window has its body ↦ the variable of the body, and the depth of the
      windows in its holes. -/
  win : Std.HashMap FVarId (Nat × Nat) := {}
  /-- The depth of the course-of-values recursion (`0`: `data_rec`). -/
  depth : Nat := 0
  /-- Inside the fold of a recursion: the positions of the parameters that the recursive calls
      change (an accumulator: `acc` in `loop f (n + 1) acc = loop f n (f acc)`), besides the one
      recursed on.  The answer of the fold is then a function of them, and a recursive call
      applies the answer to its arguments at these positions. -/
  vary : Array Nat := #[]

def Loc.bind (L : Loc) (x : Option FVarId) : Loc := { L with slots := L.slots.push x }

def Loc.index? (L : Loc) (x : FVarId) : Option Nat :=
  (L.slots.findIdx? (· == some x)).map fun p => L.slots.size - 1 - p

/-- A de Bruijn index. -/
def dbStx : Nat → MetaM Lean.Term
  | 0 => `(DeBruijn.head)
  | n + 1 => do `(DeBruijn.tail $(← dbStx n))

/-- The source variable of de Bruijn index `i`. -/
def varStx (i : Nat) : MetaM Src := pure (.var i)

/-- The closed translation of a type.  With `check := false` (the inferred type of a
    subterm) an inductive family at closed indices is not checked for having few values
    (`normType`). -/
def cirOf (L : Loc) (T : Expr) (check : Bool := true) : TM CIR := do
  let t ← lm do
    let T ← normType T check
    discover T
    discard <| declareBlocks false (L.prog?.map ProgInfo.name)
    toCIR T
  if t.hasData then modify fun s => { s with usesData := true }
  return t

def tyStx (L : Loc) (T : Expr) : TM Lean.Term := do (← cirOf L T).stx L.c #[]

/-- The delay of a type: `0` none, `1` a thunk, `2` a lazy delay. -/
def CIR.delayKind : CIR → Nat
  | .thunk _ => 1
  | .lazy _ => 2
  | _ => 0

/-- The term `t` of type `src` as a term of type `dst`, where the two types are one type up to
    its delays (`t.get : Unit → τ` of `t : Thunk (Unit → τ)`, both read as delays of `τ`): the
    delay of `src` is forced and the one of `dst` made.  Delays evaluate as the identity, so
    this only changes how the value is printed. -/
def delayCoerce (L : Loc) (src dst : CIR) (t : Src) : TM Src := do
  if src.delayKind == dst.delayKind then return t
  let forced ← match src with
    | .thunk a => do pure (Src.thunkForce (← a.stx L.c #[]) t)
    | .lazy a => do pure (Src.lazyForce (← a.stx L.c #[]) t)
    | _ => pure t
  match dst with
  | .thunk a => do pure (Src.thunkMk (← a.stx L.c #[]) forced)
  | .lazy a => do pure (Src.lazyMk (← a.stx L.c #[]) forced)
  | _ => pure forced

/-- A translation of Lean type `src` as a term of the reading of `dst`, a Lean type equal to
    `src` up to delays: `delayCoerce` between their readings. -/
def delayCoerceTy (L : Loc) (src dst : Expr) (t : Src) : TM Src := do
  delayCoerce L (← cirOf L src false) (← cirOf L dst false) t

/-- Is a type one whose values are Lean's own values (so an extern can take and return it)? -/
partial def CIR.isLeaf : CIR → Bool
  | .prim _ => true
  | .array a => a.isLeaf
  | _ => false

/-- Does the expression mention the function translated? -/
def Loc.mentionsFn (L : Loc) (e : Expr) : Bool :=
  L.fns.any fun f => (e.find? (·.isConstOf f)).isSome

/-- The value arguments of an application: explicit arguments whose type is a leaf type.
    Every other argument must be closed (a type, an instance, a literal parameter). -/
def valueArgs (L : Loc) (what : MessageData) (fn : Expr) (args : Array Expr) :
    TM (Array Nat) := do
  let mut ty ← inferType fn
  let mut out := #[]
  for i in [0:args.size] do
    ty ← whnf ty
    let .forallE _ d b bi := ty | fail m!"{what} is applied to too many arguments"
    let a := args[i]!
    let isVal ← if bi.isExplicit && !(← isProp d) && !(← isType a) then
        try pure (← cirOf L (← inferType a) false).isLeaf catch _ => pure false
      else pure false
    if isVal then out := out.push i
    else if a.hasFVar then
      fail m!"the argument{indentExpr a}\nof {what} is not a value of a leaf type (an extern \
        takes and returns values of leaf types only)"
    ty := b.instantiate1 a
  return out

/-- The syntax of the `k`-th component of a `DenList` of `n` values: a right-nested product
    with no trailing `PUnit`, so the last component is not followed by `Prod.fst`. -/
def compStx (v : Lean.Term) (k n : Nat) : MetaM Lean.Term := do
  let mut r := v
  for _ in [0:k] do r ← `(Prod.snd $r)
  if k + 1 == n then return r
  `(Prod.fst $r)

/-- Is `e` a structural-recursion target: the case analysis of parameter `x` whose branches
    call the function? -/
def Loc.recParam? (L : Loc) (major : Expr) (minors : Array Expr) : Option Nat :=
  if L.fns.isEmpty || !minors.any L.mentionsFn then none
  else if L.slots.size + L.idxParams.size != L.params.size then none
  else L.params.findIdx? (· == major)

/-- Is a (normalised) type one of the members `mems` of the block recursed on? -/
def isMember (mems : Array Expr) (T : Expr) : MetaM Bool := do
  let T ← normType T
  mems.anyM fun m => isDefEq T m

/-- Where a type holds members of the block recursed on: itself (`hole`), or inside an
    `Array` or a function (`none`: nowhere, the type is older than the block). -/
partial def nestShape (mems : Array Expr) (T : Expr) : MetaM (Option NShape) := do
  let T ← normType T
  if ← isMember mems T then return some .hole
  match T with
  | .forallE _ _ b _ =>
    if b.hasLooseBVars then return none
    return (← nestShape mems b).map .fn
  | _ =>
    if T.isAppOfArity ``Array 1 then return (← nestShape mems T.appArg!).map .array
    return none

/-- Open the fields of a branch of a recursion on a block whose members are `mems` (their Lean
    locals `xs`, the erased ones marked), the first field kept innermost.  A field that is a
    member is the window of depth `d` of the subvalue (`DSig.Block.win`), which is taken
    apart: the subvalue, the answer at it and, for `d > 0`, its body, whose holes are windows
    of depth `d - 1`.  A field that holds members inside an `Array` or a function holds the
    pairs of the subvalues and their answers (only at depth `0`). -/
partial def openWindows (L : Loc) (mems : Array Expr) (xs : Array Expr) (erased : Array Bool)
    (d : Nat) (kont : Loc → TM Src) : TM Src := do
  let kept := (xs.zip erased).filter (!·.2) |>.map (·.1)
  let holes ← kept.filterM fun x => do isMember mems (← inferType x)
  let mut L' := L
  for x in kept.reverse do
    L' := L'.bind (if holes.contains x then none else some x.fvarId!)
    unless holes.contains x do
      if let some s ← nestShape mems (← inferType x) then
        let s ← if (← get).optFields.contains x.fvarId! then
            if s == .fn .hole then pure (NShape.fn .optHole) else
              fail m!"the field `{← x.fvarId!.getUserName}` is read as a function to an \
                `Option` (its domain is a `Fin` of an earlier field): only a field \
                `Fin m → X` for a member `X` of the block recursed on is supported"
          else pure s
        if d > 0 then
          fail m!"the field `{← x.fvarId!.getUserName}` holds values of the datatype recursed \
            on inside an `Array` or a function: only a recursion that looks one level down \
            through it is supported"
        L' := { L' with nest := L'.nest.insert x.fvarId! s }
  let width := if d = 0 then 2 else 3
  let rec go (L' : Loc) (done : Nat) (hs : List Expr) : TM Src := do
    match hs with
    | [] => kont L'
    | h :: rest =>
      let pos := kept.findIdx? (· == h) |>.get!
      let idx := pos + width * done
      let L'' := if d > 0 then L'.bind none else L'
      let L'' := (L''.bind none).bind h.fvarId!
      let L'' := { L'' with ans := L''.ans.insert h.fvarId! (L''.slots.size - 2) }
      let L'' := if d > 0 then { L'' with win := L''.win.insert h.fvarId! (L''.slots.size - 3, d - 1) }
        else L''
      return Src.recordCases (← varStx idx) width (← go L'' (done + 1) rest)
  go L' 0 holes.toList

/-- The functions of the mutual group of `f` (as declared with `mutual`), `f` included. -/
def mutualGroup (f : Name) : MetaM (Array Name) := do
  let env ← getEnv
  if let some i := Elab.Structural.eqnInfoExt.find? env f then return i.declNames
  if let some i := Elab.WF.eqnInfoExt.find? env f then return i.declNames
  return #[f]

/-- The function of the group `L.fns` that recurses on each member `mems` of the block (at
    parameter `p`), if any.  Every function of the group must take the parameters of the
    function translated, except at `p`, where it takes a member. -/
def groupByMember (L : Loc) (p : Nat) (mems : Array Expr) : TM (Array (Option Name)) := do
  let mut assign : Array (Option Name) := Array.replicate mems.size none
  for g in L.fns do
    let info ← getConstInfo g
    unless info.levelParams.isEmpty do fail m!"`{g}` is universe polymorphic"
    let i? ← forallTelescope info.type fun ys _ => do
      unless ys.size == L.params.size do
        fail m!"`{g}` does not take the same parameters as the other functions of its \
          `mutual` group"
      for q in [0:ys.size] do
        if q != p then
          unless ← isDefEq (← inferType ys[q]!) (← inferType L.params[q]!) do
            fail m!"`{g}` does not take the same parameters as the other functions of its \
              `mutual` group"
      -- the index parameters are those of the function translated (a type index is fixed)
      let idx := L.idxParams.filter (· != p)
      let T ← normType ((← inferType ys[p]!).replaceFVars (idx.map (ys[·]!)) (idx.map (L.params[·]!)))
      mems.findIdxM? fun m => isDefEq T m
    let some i := i? | fail m!"`{g}` does not recurse on a member of the block recursed on"
    if let some g' := assign[i]! then
      fail m!"`{g'}` and `{g}` both recurse on the same datatype: one function per member \
        of the block is supported"
    assign := assign.set! i (some g)
  return assign

/-- For a constructor of a type-indexed family: the position of its index field (`α` in
    `Nest.cons {α} a r`), and for each field whether its type is that index (`some true`),
    does not mention it outside the family itself (`some false`: `Nest (α × α)` is read at the
    same index), or mentions it otherwise (`none`). -/
def ctorIndexKinds (ind : InductiveVal) (ctor : Name) : MetaM (Nat × Array (Option Bool)) := do
  let p ← indexField ind ctor
  let cinfo ← getConstInfoCtor ctor
  let kinds ← forallTelescopeReducing cinfo.type fun xs _ => do
    let a := xs[cinfo.numParams + p]!
    xs[cinfo.numParams:].toArray.mapM fun x => do
      let t ← instantiateMVars (← inferType x)
      if t == a then return some true
      let t' := t.replace fun s =>
        if s.isAppOfArity ind.name (ind.numParams + 1) then some (mkConst ``Unit) else none
      return if t'.containsFVar a.fvarId! then none else some false
  return (p, kinds)

/-- Record which fields `xs` of an opened constructor `ctor` the language reads as
    `Nat → Option T` (`finOptArrow`). -/
def markOptFields (ctor : Name) (xs : Array Expr) : TM Unit := do
  for x in xs do
    unless x.isFVar do continue
    if let .forallE _ d b _ ← whnf (← instantiateMVars (← inferType x)) then
      if ← finOptArrow ctor xs d b then
        modify fun s => { s with optFields := s.optFields.insert x.fvarId! }

/-- For each field of the constructor `ctor` at the parameters `params`: is it read as
    `Nat → Option T` (`finOptArrow`)? -/
def ctorOptMask (ctor : Name) (us : List Level) (params : Array Expr) : MetaM (Array Bool) := do
  let cinfo ← getConstInfoCtor ctor
  let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
  forallTelescopeReducing ty fun xs _ => xs.mapM fun x => do
    let .forallE _ d b _ ← whnf (← instantiateMVars (← inferType x)) | return false
    finOptArrow ctor xs d b

/-- The elements of a list literal `[a, b, …]` (`List.cons a (List.cons b … List.nil)`). -/
partial def listLit? (e : Expr) : MetaM (Option (Array Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``List.nil 1 then return some #[]
  if e.isAppOfArity ``List.cons 3 then
    let some rest ← listLit? e.appArg! | return none
    return some (#[e.appFn!.appArg!] ++ rest)
  return none

/-- For a member `mems[i]` of the block recursed on that is `Option X`, where `X` is a member
    recursed on by a function `g` of the group: the answer type at `X` (the result type of
    `g`, whose parameter `p` is a value of `X`). -/
def optMemberAnswer (L : Loc) (p : Nat) (mems : Array Expr) (assign : Array (Option Name))
    (i : Nat) : TM (Option Lean.Term) := do
  let T ← whnf mems[i]!
  unless T.isAppOfArity ``Option 1 do return none
  let some jx ← mems.findIdxM? (fun m => isDefEq m T.appArg!) | return none
  let some g := assign[jx]! | return none
  withLocalDeclD `y mems[jx]! fun y => do
    let params := L.params.set! p y
    return some (← tyStx L (← inferType (mkAppN (mkConst g) params)))

/-- Open the fields of a branch (the minor premise `minor`, applied to the extra arguments
    `extra`) of the constructor `ctor` of `ind`, for the scrutinee `major` whose (normalised)
    type is `T`; `k` receives the fields and the body.  For a type-indexed family the index
    field (`α` in `Nest.cons {α} a r`) is not opened: it is the index the family is read at
    (`Nest.Elem Nat`), so a field of type `α` holds an element of it.  When the scrutinee is at
    another index (`Nest Nat`, or `Nest (Nest.Elem Nat × Nest.Elem Nat)` one level down), such a
    field is a value of that index in Lean (a `Nat`), but an element in the language: it must
    not be used. -/
partial def withFields {α : Type} (ind : InductiveVal) (T major : Expr) (ctor : Name)
    (minor : Expr) (extra : Array Expr) (k : Array Expr → Expr → TM α) : TM α := do
  let n := (← getConstInfoCtor ctor).numFields
  let body (xs : Array Expr) : Expr := (mkAppN (mkAppN minor xs) extra).headBeta
  unless ← typeIndexed ind do
    return ← forallBoundedTelescope (← inferType minor) n fun xs _ => do
      markOptFields ctor xs
      k xs (body xs)
  let (p, kinds) ← ctorIndexKinds ind ctor
  let canon := T.getAppArgs[ind.numParams]!
  let actual := (← whnf (← inferType major)).appArg!
  let generic ← isDefEq actual canon
  let rec go (ty : Expr) (i : Nat) (xs : Array Expr) : TM α := do
    if i = n then
      unless generic do
        for q in [0:n] do
          if kinds[q]! == some true then
            let x := xs[q]!.fvarId!
            modify fun s => { s with unusable := s.unusable.insert x (ctor, actual, canon) }
      markOptFields ctor xs
      return ← k xs (body xs)
    let .forallE nm d b bi ← whnf ty | fail m!"bad branch of `{ctor}`"
    if p == i then return ← go (b.instantiate1 canon) (i + 1) (xs.push canon)
    withLocalDecl nm bi d fun x => go (b.instantiate1 x) (i + 1) (xs.push x)
  go (← inferType minor) 0 #[]

/-- The definitions on quotients that are unfolded to `Quot.mk`, `Quot.lift`, `Quot.rec`. -/
def quotDefs : List Name :=
  [``Quot.liftOn, ``Quotient.mk, ``Quotient.mk', ``Quotient.lift, ``Quotient.liftOn,
    ``Quotient.lift₂, ``Quotient.liftOn₂, ``Quotient.rec, ``Quotient.recOn,
    ``Quotient.hrecOn, ``Quotient.recOnSubsingleton]

/-- A Lean local standing for a value of type `t` passed to an extern: its type is the one of
    the translation's value, and the value passed to the Lean function is rebuilt from it.  A
    quotient is read as its carrier, so a representative `y` of `Quot r` is passed as
    `Quot.mk r y`: the extern computes on the class, as the Lean function does. -/
partial def externLocal (t : Expr) : MetaM (Expr × (Expr → MetaM Expr)) := do
  let t' ← whnf t
  if let some α := quotCarrier? t' then
    let (β, g) ← externLocal α
    return (β, fun y => do
      return mkApp3 (.const ``Quot.mk t'.getAppFn.constLevels!) α t'.appArg! (← g y))
  if t'.isAppOfArity ``Array 1 then
    let (β, g) ← externLocal t'.appArg!
    if β == t'.appArg! then return (t, pure)
    -- an array of values of quotients: the array of their classes
    return (mkApp (.const ``Array t'.getAppFn.constLevels!) β, fun y => do
      let f ← withLocalDeclD `z β fun z => do mkLambdaFVars #[z] (← g z)
      mkAppM ``Array.map #[f, y])
  return (t, pure)

/-- `fun | ⟨0, _⟩ => x₀ | ⟨1, _⟩ => x₁ | …`: a (dependent) function on `Fin n`. -/
def finFunStx (xs : Array Lean.Term) : MetaM Lean.Term := do
  let alts ← (List.range xs.size).toArray.mapM fun i =>
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(xs[i]!))
  `(fun $alts:matchAlt*)

/-- The positions of the parameters, other than `p` (the one recursed on) and the index
    parameters, that some recursive call in `es` (a call of a function of `L.fns`) does not pass
    unchanged, or does not pass at all (a partial application `hyperTCO n a`). -/
partial def varyingParams (L : Loc) (p : Nat) (es : Array Expr) : MetaM (Array Nat) := do
  let mut out : Array Nat := #[]
  for e in es do
    out ← go e out
  return out.qsort (· < ·)
where
  go (e : Expr) (acc : Array Nat) : MetaM (Array Nat) := do
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      let mut acc := acc
      if let .const c _ := fn then
        if L.fns.contains c then
          for q in [0:L.params.size] do
            if q == p || L.idxParams.contains q || acc.contains q then continue
            if h : q < args.size then
              if args[q] != L.params[q]! then acc := acc.push q
            else acc := acc.push q
      unless fn.isConst do acc ← go fn acc
      for a in args do acc ← go a acc
      return acc
    | .const c _ =>
      -- a function of the group unapplied: every parameter is missing
      if L.fns.contains c then
        let mut acc := acc
        for q in [0:L.params.size] do
          unless q == p || L.idxParams.contains q || acc.contains q do acc := acc.push q
        return acc
      return acc
    | .lam _ t b _ | .forallE _ t b _ => do go b (← go t acc)
    | .letE _ t v b _ => do go b (← go v (← go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => return acc

/-- In a branch of the fold of a recursion whose recursive calls change the parameters at the
    positions `L.vary`: bind a fresh local for each of them (the first outermost), put them for
    the parameters in `body`, translate with `k`, and wrap the result in one closure each. -/
def withVaryLocals (L : Loc) (body : Expr) (k : Loc → Expr → TM Src) : TM Src := do
  let ps := L.vary.map (L.params[·]!)
  let rec go (i : Nat) (L' : Loc) (xs : Array Expr) : TM Src := do
    if h : i < ps.size then
      let p := ps[i]
      let d ← p.fvarId!.getDecl
      withLocalDeclD d.userName d.type fun x => do
        return Src.lam none (← go (i + 1) (L'.bind x.fvarId!) (xs.push x))
    else
      k L' (body.replaceFVars ps xs)
  go 0 L #[]

/-- The positions of the parameters `xs` of a definition that only name an index of the type
    of a later parameter (`n` in `Vec.sum {n : Nat} (v : Vec Nat n)`): the indices of a family
    are erased, so they have no value in the language.  Such a parameter must not be used
    otherwise (it is not bound in the translation). -/
def indexParams (xs : Array Expr) : MetaM (Array Nat) := do
  let env ← getEnv
  -- `s` is an inductive family applied to `x` as one of its indices
  let isIdxOf (x : Expr) (s : Expr) : Bool := Id.run do
    let some (c, _) := s.getAppFn.const? | return false
    let some (.inductInfo info) := env.find? c | return false
    let args := s.getAppArgs
    unless info.numIndices > 0 && args.size == info.numParams + info.numIndices do return false
    return args[info.numParams:].toArray.contains x
  let mut out := #[]
  for i in [0:xs.size] do
    let x := xs[i]!
    let d ← x.fvarId!.getDecl
    if d.binderInfo.isInstImplicit || (← isProp d.type) then continue
    let mut isIdx := false
    for j in [i + 1:xs.size] do
      let t ← instantiateMVars (← inferType xs[j]!)
      if (t.find? (isIdxOf x)).isSome then isIdx := true
    if isIdx then out := out.push i
  return out

/-- Is `m` the monad `Id`? -/
def isIdMonad (m : Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars m)).isConstOf ``Id

/-- `t a₁ … aₙ` in the language: `Comp.app` of `t` to each of the terms `as`. -/
def appStx (t : Src) (as : Array Src) : MetaM Src := pure (Src.apps t as)

/-- The case analysis of a value `scrut` of the type of `plan`, one branch per constructor
    (binding its fields), of type `ty?` when known: the source of `casesBodyStx` (`ite`,
    `enum_casesOn`, a `let` of the single field, `record_casesOn`, `union_casesOn`). -/
def casesSrc (plan : TypePlan) (scrut : Src) (bs : Array Src) (ty? : Option Lean.Term) :
    MetaM Src := do
  let m := plan.ctors.size
  if plan.isBool then
    return Src.ite ty? scrut bs[1]! bs[0]!
  else if plan.enum?.isSome then
    let i := mkIdent `i
    return .cases ty? scrut (bs.map (0, ·)) fun c rhss => do
      let mut sel := rhss[m - 1]!
      for p in (List.range (m - 1)).reverse do
        sel ← `(if ($i).val = $(quote p) then $(rhss[p]!) else $sel)
      `(LeanScript.Term.enum_casesOn $c (fun $i => $sel))
  else if m = 1 then
    let n := plan.ctors[0]!.2.size
    if n = 1 then return .letE scrut bs[0]!
    else return Src.recordCases scrut n bs[0]!
  else
    return Src.unionCases ty? scrut
      ((List.range m).toArray.map fun p => (plan.ctors[p]!.2.size, bs[p]!))

/-- Is `c` declared in Lean's own library (`Init`, `Std`, `Lean`)?  Such a function is an
    extern of the language, never a helper whose definition is translated. -/
def isLibraryDecl (c : Name) : CoreM Bool := do
  let env ← getEnv
  let some i := env.getModuleIdxFor? c | return false
  let m := env.header.moduleNames[i.toNat]!
  return [`Init, `Std, `Lean].contains m.getRoot

end LeanScript.Gen

end
