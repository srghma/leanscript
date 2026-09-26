module

public meta import LeanScript.GetCtor
public meta import Lean.Meta.Eqns
public meta import Lean.Elab.PreDefinition.Structural.Eqns
public meta import Lean.Elab.PreDefinition.WF.Eqns

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term f`: a Lean definition as a `LeanScript.Term`

`#leanscript_to_term f` is a term: the translation of the Lean definition `f` to a closed
`LeanScript.Term`, of type `Term Δ [] τ` where `τ` is `#leanscript_get_ty` of the type of `f`.
Written as a command, it shows the type of the translation.  The translation is generic in
the signature (`{ks} {Δ : DSig ks}`) unless it uses a declared datatype, in which case it is a
term over the current program (`leanscript_signature`).

The definition is read through its unfolding equation (`f.eq_def`), so a definition by
structural recursion is read with its recursive calls in place, and `match` is read through
the `casesOn` it is compiled to.  The translation is in direct style:

| Lean | `Term` |
| :-- | :-- |
| a parameter, a `let`, a `fun` | `Term.var` (de Bruijn), `Term.letE`, `Term.lam` |
| a closed value of a leaf type (a literal) | `Term.lit` |
| `if c then t else e`, `cond`, `dite` (the proof unused) | `Term.ite` of `decide c` |
| a call of any other function on values of leaf types (or `decide` of such a relation) | `Term.extern`, named after the function, on the terms of its value arguments |
| a constructor | `#leanscript_get_ctor` of it (and so `data_in` for a recursive type) |
| a constructor of a wrapper of one value besides proofs (`⟨i, h⟩ : Fin c.n`, `Subtype.mk`), also when its parameters mention locals | that value |
| a projection applied to arguments (`c.data i` for a function field) | `Term.app` |
| a parameter that only names an index of a later parameter's type (`{n}` in `Vec.sum {n} (v : Vec Nat n)`) | nothing: indices are erased, so it is not a parameter of the translation (and cannot be used as a value) |
| a type parameter that only names the index of a type-indexed family (`{α}` in `Nest.length {α} (n : Nest α)`) | nothing: it is fixed to the index the family is read at (`Nest.Elem Nat`: the one the program declares, or `#leanscript_to_term f (α := Nat)`), so a recursive call at `α × α` is a call on the tail |
| a field of type `α` of a type-indexed family (`a` in `Nest.cons {α} a r`) | in a constructor application, the value put in the element type (`(2, 3)` is `Nest.Elem.node (leaf 2) (leaf 3)`); in a case analysis at an index other than the one read at (`Nest Nat`), refused if used |
| a value of a quotient `Quot r` / `Quotient s` (read as its carrier): `Quot.mk r a`, `⟦a⟧` | the representative `a` |
| `Quot.lift f h q`, `Quot.liftOn`, `Quot.rec`, `Quot.recOn`, `Quot.hrecOn`, `Quot.recOnSubsingleton`, `Quotient.lift`, `Quotient.lift₂`, … | `f` of the representative (`Term.letE` of `q` unless it is a `Quot.mk`) |
| an extern argument of a quotient type (or an `Array` of them) | the class `Quot.mk r a` of the representative `a` is passed to the Lean function |
| a cast along an equation (`Eq.ndrec`, `cast`, …, from the `match` of an inductive family) | the value cast |
| a case analysis (`match`, `casesOn`) | `#leanscript_get_cases`' shape: `ite`, `enum_casesOn`, `letE`, `record_casesOn`, `union_casesOn`; after `data_out` for a recursive type; `nat_rec` for `Nat` |
| a projection of a structure | `record_casesOn` (or the value itself, for one field) |
| structural recursion on a `Nat` parameter | `Term.nat_rec` |
| a recursion whose recursive calls change other parameters (an accumulator: `loop f (b + 1) acc = loop f b (f acc)`), or leave out trailing ones (`hyperTCO n a`, partially applied) | the fold answers a function of those parameters (`nat_rec`/`data_rec` applied to their current values); a recursive call applies the answer to its arguments there |
| a recursive call applied to more arguments than the parameters (`ack2 m n` for `ack2 : Nat → (Nat → Nat)`) | `Term.app` of the answer |
| a call of a helper definition (not from `Init`/`Std`/`Lean`) that cannot be an extern, because it takes or returns a value that is not of a leaf type (`ackInner (ack2 m)`, `hyperLoop (hyperTCO n a) b x`) | the helper's own translation (a closed term), applied to the terms of the arguments; a helper calling back the function translated is refused |
| `Id.run x`, `pure x`, `x >>= f` in `Id` (a `do` block) | `x`, `x`, `Term.letE` |
| `for i in [a:b:s] do …` in `Id` (`forIn`/`forIn'` over a `Std.Legacy.Range`) | `Term.nat_rec` on the number of iterations `(b - a + s - 1) / s`, at `i = a + k * s`, whose answer is a `ForInStep`: a `done` (`break`, `return`) is kept to the end, and the loop is the value in the final step |
| structural recursion on a parameter of a declared datatype, by one function or by a `mutual` group of functions (one per member of the block: `Even.toNat`/`Odd.toNat`, `Rose.sum`/`Rose.sumList`) | `Term.data_rec` of the whole block, one branch per member (a member no function recurses on gets a constant branch) |
| a recursive call on a member held in a function field (`(f 0).sum` in the branch of `node f`) | the answer next to the subvalue (`record_casesOn` of the applied field) |
| `Array.foldl step z qs` over a field `qs` that holds members in an `Array` (also `Array (Array Q)`, `Nat → Array Q`) | `Term.array_foldl` over the pairs of the subvalues and their answers; in `step`, a recursive call on the element is its answer |
| an array literal `#[a, b, …]` of values that are not leaves (`#[(none, 3)] : Array (Option T5 × Nat)`) | `Term.array_mk` |
| `Fin.foldl n f z` | `Term.nat_rec` on `n`, whose step at `k` is `f acc ⟨k, _⟩` |
| a value `a : Fin m → T` of a field read as `Nat → Option T` (`finOptArrow`: `RoseF.node m a`) | `fun j => if j < m then some (a ⟨j, _⟩) else none` (`fun _ => none` for `m = 0`) |
| `f i` for such a field `f` of an opened constructor | `f i` taken apart after `data_out`: `some x` is `x`, the unreachable `none` is the `Inhabited` default of `T` |
| a recursive call on `f i` for such a field | the answer at the member `Option T`: `some` of the answer at `f i` (the fold's branch at `Option T` is generated), `none` the `Inhabited` default of the answer type |
| the same, with recursive calls on subvalues up to four levels down (`f (y :: t)`, `f t` in the branch of `_ :: y :: t`) | `Term.data_brec` of the smallest depth that reaches them (for members used directly only) |

A recursive definition must recurse directly on one of its parameters, at the top of its
body (`f x = match x with …`); the other parameters may change (the answer of the fold is
then a function of them); in a branch the
parameter recursed on is the constructor application it was matched against.  The functions
of a `mutual` group all take the same parameters, except the one recursed on, which is a
different member of the block for each.  The recursion may be compiled by Lean as structural
or as well-founded (`qs.foldl (fun acc q => acc + q.sum) 0` is well-founded): the translator
reads the unfolding equations, and checks itself that every recursive call is on a subvalue.
A field that holds members inside an `Array` or a function holds, in the branch, the pairs
of the subvalues and their answers, so it can only be folded, applied, or passed to a
recursive call.

Everything else is refused with an error, in particular a type with one value or none
(`Unit`, `Empty`, …: as a parameter, a `let`, a field or a value), a type of two values
other than `Bool` (such a type *is* `bool`), a parameter that is a type or an instance,
mutual recursion through a helper, a recursive call that is not on a subvalue, a pattern on a numeral other than
`0`/`n + 1`, an extern whose argument or result is not a leaf type, and a call returning a quotient that does
not compute to `Quot.mk` (the language would need a representative).
-/

open Lean Meta Elab Term

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

def varStx (i : Nat) : MetaM Lean.Term := do `(LeanScript.Term.var $(← dbStx i))

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

/-- The syntax of the `k`-th component of a `DenList`. -/
def compStx (v : Lean.Term) (k : Nat) : MetaM Lean.Term := do
  let mut r := v
  for _ in [0:k] do r ← `(Prod.snd $r)
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
    (d : Nat) (kont : Loc → TM Lean.Term) : TM Lean.Term := do
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
  let rec go (L' : Loc) (done : Nat) (hs : List Expr) : TM Lean.Term := do
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
      `(LeanScript.Term.record_casesOn $(← varStx idx) $(← go L'' (done + 1) rest))
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
    the parameters in `body`, translate with `k`, and wrap the result in one `Term.lam` each. -/
def withVaryLocals (L : Loc) (body : Expr) (k : Loc → Expr → TM Lean.Term) : TM Lean.Term := do
  let ps := L.vary.map (L.params[·]!)
  let rec go (i : Nat) (L' : Loc) (xs : Array Expr) : TM Lean.Term := do
    if h : i < ps.size then
      let p := ps[i]
      let d ← p.fvarId!.getDecl
      withLocalDeclD d.userName d.type fun x => do
        `(LeanScript.Term.lam $(← go (i + 1) (L'.bind x.fvarId!) (xs.push x)))
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

/-- `t a₁ … aₙ` in the language: `Term.app` of `t` to each of the terms `as`. -/
def appStx (t : Lean.Term) (as : Array Lean.Term) : MetaM Lean.Term := do
  let mut r := t
  for a in as do r ← `(LeanScript.Term.app $r $a)
  return r

/-- Is `c` declared in Lean's own library (`Init`, `Std`, `Lean`)?  Such a function is an
    extern of the language, never a helper whose definition is translated. -/
def isLibraryDecl (c : Name) : CoreM Bool := do
  let env ← getEnv
  let some i := env.getModuleIdxFor? c | return false
  let m := env.header.moduleNames[i.toNat]!
  return [`Init, `Std, `Lean].contains m.getRoot

mutual

/-- The translation of an expression. -/
partial def tr (L : Loc) (e : Expr) : TM Lean.Term := do
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
      fail m!"the field `{← x.getUserName}` holds values of the datatype recursed on, paired \
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
      `(LeanScript.Term.letE $tv $body)
  | .lam n t b _ =>
    discard <| cirOf L t
    withLocalDeclD n t fun x => do
      `(LeanScript.Term.lam $(← tr (L.bind x.fvarId!) (b.instantiate1 x)))
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
        if ← isDefEq T d then return ← `(LeanScript.Term.lit $p $(← exprToSyntax e))
        -- a closed value of a type read as a leaf without being one (a wrapper `⟨1, h⟩ : Pos`,
        -- a quotient `Quot.mk r 3`): its head normal form, whose value is the literal
        let e' ← whnf e
        if e' != e then return ← tr L e'
    trApp L e

/-- A projection `s.i` of a structure. -/
partial def trProj (L : Loc) (S : Name) (i : Nat) (s : Expr) : TM Lean.Term := do
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
    scrut ← `(LeanScript.Term.data_out $(← brefStx L.c b) $(quote j) $scrut)
  if n = 1 then return scrut
  `(LeanScript.Term.record_casesOn $scrut $(← varStx q))

/-- An application. -/
partial def trApp (L : Loc) (e : Expr) : TM Lean.Term := do
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
      return ← `(LeanScript.Term.record_casesOn $t (LeanScript.Term.var DeBruijn.head))
    -- a field `f : Fin m → T` read as `Nat → Option T`: `f i` is `some` below `m`, and the
    -- unreachable `none` gets the default of `T`
    if (← get).optFields.contains x && args.size ≥ 1 then
      let a := args[0]!
      let T ← inferType (mkApp fn a)
      let d ← defaultTerm L T m!"the application{indentExpr e}"
      let mut scrut ← `(LeanScript.Term.app $(← tr L fn) $(← tr L a))
      -- `Option T` is a member of the block of `T`: taken apart after `data_out`
      let plan ← lm (planType (← normType (← mkAppM ``Option #[T]) false) L.prog?)
      if let some (b, j) := plan.data? then
        modify fun st => { st with usesData := true }
        scrut ← `(LeanScript.Term.data_out $(← brefStx L.c b) $(quote j) $scrut)
      let mut r ← `(LeanScript.Term.union_casesOn $scrut
        (LeanScript.Branches.two $d (LeanScript.Term.var DeBruijn.head)))
      for a in args[1:] do r ← `(LeanScript.Term.app $r $(← tr L a))
      return r
    let mut r ← tr L fn
    for a in args do r ← `(LeanScript.Term.app $r $(← tr L a))
    return r
  | .const c _ =>
    let env ← getEnv
    if L.fns.contains c then return ← trRecCall L e
    if c == ``ite && args.size == 5 then
      let d := mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!
      return ← `(LeanScript.Term.ite $(← tr L d) $(← tr L args[3]!) $(← tr L args[4]!))
    if c == ``cond && args.size == 4 then
      return ← `(LeanScript.Term.ite $(← tr L args[1]!) $(← tr L args[2]!) $(← tr L args[3]!))
    if c == ``dite && args.size == 5 then
      let d := mkApp2 (mkConst ``Decidable.decide) args[1]! args[2]!
      let br (k : Expr) (h : Expr) : TM Lean.Term :=
        withLocalDeclD `h h fun x => tr L (mkApp k x)
      return ← `(LeanScript.Term.ite $(← tr L d) $(← br args[3]! args[1]!)
        $(← br args[4]! (mkNot args[1]!)))
    if c == ``Decidable.decide && args.size == 2 then
      -- `decide (b = true)` is `b`
      if let some (_, b, t) := args[0]!.eq? then
        if t.isConstOf ``Bool.true && (← isDefEq (← inferType b) (mkConst ``Bool)) then
          return ← tr L b
      return ← trDecide L args[0]!
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
          `(LeanScript.Term.letE $tx $body)
    -- a `for` loop over a range `[a:b:s]` in `Id`
    if c == ``ForIn.forIn && args.size == 8 then
      if (← isIdMonad args[0]!) && (← whnfR args[1]!).isConstOf ``Std.Legacy.Range then
        return ← trRangeFor L args[4]! args[5]! args[6]! fun i r => pure (mkApp2 args[7]! i r)
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
    -- `Fin.foldl n f z`: `Term.nat_rec` on `n`, whose step at `k` is `f acc ⟨k, _⟩`
    if c == ``Fin.foldl && args.size == 4 then
      return ← trFinFoldl L args[0]! args[1]! args[2]! args[3]!
    -- an array literal `#[a, b, …]` (`List.toArray [a, b, …]`) of values that are not leaves
    if c == ``List.toArray && args.size == 2 then
      if let some xs ← listLit? args[1]! then
        let τ ← cirOf L (← inferType e) false
        unless τ.isLeaf do
          let mut es ← `(LeanScript.Elems.nil)
          for x in xs.reverse do es ← `(LeanScript.Elems.cons $(← tr L x) $es)
          return ← `(LeanScript.Term.array_mk $es)
    -- a fold over an array of members of the block recursed on
    if c == ``Array.foldl && args.size == 7 then
      if let some (arr, .array s) ← nestView? L args[4]! then
        unless (← natLit? args[5]!) == some 0 &&
            (← isDefEq args[6]! (← mkAppM ``Array.size #[args[4]!])) do
          fail m!"`Array.foldl` with bounds{indentExpr e}\nis not supported"
        return ← trNestFoldl L arr s args
    if ← isMatcher c then
      let info ← getConstInfo c
      let v := info.value!.instantiateLevelParams info.levelParams fn.constLevels!
      return ← tr L (← Core.betaReduce (v.beta args))
    if let some (.ctorInfo cinfo) := env.find? c then
      -- a wrapper of one value (`Fin.mk n v h`, `Subtype.mk v h`, `Vector.mk a h`) is erased
      -- to that value, also when its parameters mention locals (`⟨0, h⟩ : Fin c.n`)
      if let some a ← wrapperField? cinfo args then
        unless (← cirOf L (← inferType e) false) matches .data .. do return ← tr L a
      if !((← cirOf L (← inferType e) false) matches .prim _) then
        return ← trCtor L cinfo fn args
    if let some pinfo ← getProjectionFnInfo? c then
      if !pinfo.fromClass then
        if let some e' ← unfoldDefinition? e then return ← tr L e'
    -- a call of a helper definition that cannot be an extern (it takes or returns a value
    -- that is not a leaf, e.g. a function): its own translation, applied
    if !(← isLibraryDecl c) && (← externImpossible L e fn args) then
      if let some (.defnInfo _) := env.find? c then
        return ← trHelperCall L c e args
    trExtern L (toString c) e fn args
  | .proj .. =>
    -- a projection applied to arguments (`c.data i` for a function field)
    let mut r ← tr L fn
    for a in args do r ← `(LeanScript.Term.app $r $(← tr L a))
    return r
  | _ => fail m!"cannot translate the application{indentExpr e}"

/-- `for i in range do body` in `Id` (`forIn range init f`, whose step is `mkBody i r`):
    with `range = [a:b:s]`, the loop runs `n = (b - a + s - 1) / s` times, at `i = a + k * s`.
    It is `Term.nat_rec` on `n` whose answer is a `ForInStep β`: it starts at `yield init`,
    the step at `k` is the body at `i` on the value of a `yield` and keeps a `done` (a `break`
    or a `return`), and the loop is the value in the final step. -/
partial def trRangeFor (L : Loc) (β range init : Expr) (mkBody : Expr → Expr → TM Expr) :
    TM Lean.Term := do
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
  let stepTy ← mkAppM ``ForInStep #[β]
  let ρ ← tyStx L stepTy
  let tn ← tr L n
  let tz ← tr L (← mkAppM ``ForInStep.yield #[init])
  let ts ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `acc stepTy fun acc => do
    let ks ← if s1 then pure k else mkAppM ``HMul.hMul #[k, s]
    let i ← if a0 then pure ks else mkAppM ``HAdd.hAdd #[a, ks]
    let done ← withLocalDeclD `v β fun v => do
      mkLambdaFVars #[v] (← mkAppM ``ForInStep.done #[v])
    let yield ← withLocalDeclD `v β fun v => do mkLambdaFVars #[v] (← mkBody i v)
    let motive ← withLocalDeclD `t stepTy fun t => mkLambdaFVars #[t] stepTy
    let cases ← mkAppOptM ``ForInStep.casesOn #[β, motive, acc, done, yield]
    tr ((L.bind k.fvarId!).bind acc.fvarId!) cases
  let fin ← withLocalDeclD `r stepTy fun r => do
    let idF ← withLocalDeclD `v β fun v => mkLambdaFVars #[v] v
    let motive ← withLocalDeclD `t stepTy fun t => mkLambdaFVars #[t] β
    let cases ← mkAppOptM ``ForInStep.casesOn #[β, motive, r, idF, idF]
    tr (L.bind r.fvarId!) cases
  `(LeanScript.Term.letE (LeanScript.Term.nat_rec (τ := $ρ) $tn $tz $ts) $fin)

/-- Would the call `e` of `fn` to `args` be refused as an extern: does it take or return a
    value that is not of a leaf type? -/
partial def externImpossible (L : Loc) (e fn : Expr) (args : Array Expr) : TM Bool := do
  let leaf (T : Expr) : TM Bool := do
    try pure (← cirOf L T false).isLeaf catch _ => pure false
  unless ← leaf (← inferType e) do return true
  let mut ty ← inferType fn
  for a in args do
    ty ← whnf ty
    let .forallE _ d b bi := ty | return true
    if bi.isExplicit && !(← isProp d) && !(← isType a) && a.hasFVar then
      unless ← leaf (← inferType a) do return true
    ty := b.instantiate1 a
  return false

/-- A call `c a₁ … aₙ` of a helper definition `c`: the translation of `c` (a closed term, so
    its syntax elaborates in any context), applied to the terms of the arguments. -/
partial def trHelperCall (L : Loc) (c : Name) (e : Expr) (args : Array Expr) : TM Lean.Term := do
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
          for _ in xs do body ← `(LeanScript.Term.lam $body)
          let ty ← tyStx L0 info.type
          return ← `(($body : LeanScript.Term _ _ $ty))
        catch ex => if err?.isNone then err? := some ex
      throw err?.get!
    finally
      modify fun s => { s with inlining := saved }
  appStx helper (← args.mapM (tr L))

/-- A term of the default value of the Lean type `T` (its `Inhabited` instance, in head normal
    form), for a branch that Lean proves unreachable but the language does not (`what`). -/
partial def defaultTerm (L : Loc) (T : Expr) (what : MessageData) : TM Lean.Term := do
  let inst ← try synthInstance (← mkAppM ``Inhabited #[T])
    catch _ => fail m!"{what}\nis read through a field `Fin m → _` (as `Nat → Option _`): \
      below `m` it is `some`, but the language needs a value for `none`, and the type{indentExpr T}\n\
      has no `Inhabited` instance"
  tr L (← whnf (← mkAppOptM ``Inhabited.default #[T, inst]))

/-- `Fin.foldl n f z` (of type `α`): `Term.nat_rec n z s`, whose step `s` binds the index `k`
    and the accumulator `acc` and is the translation of `f acc ⟨k, h⟩` (the bound `h` is a
    proof, erased). -/
partial def trFinFoldl (L : Loc) (α n f z : Expr) : TM Lean.Term := do
  discard <| cirOf L α
  let tn ← tr L n
  let tz ← tr L z
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `acc α fun acc => do
    let lt ← mkAppM ``LT.lt #[k, n]
    withLocalDeclD `h lt fun h => do
      let i ← mkAppOptM ``Fin.mk #[n, k, h]
      let body := (mkApp2 f acc i).headBeta
      let L' := (L.bind k.fvarId!).bind acc.fvarId!
      `(LeanScript.Term.nat_rec $tn $tz $(← tr L' body))

/-- `f q` for a function `f` on the carrier of a quotient and a value `q` of the quotient
    (`Quot.lift f h q`), then applied to `extra`.  The value of `q` is a representative: for
    `Quot.mk r a` it is `a`, so the translation is the one of `f a`; otherwise it is bound
    (`letE`) to a local of the carrier, to which `f` is applied. -/
partial def trQuotApp (L : Loc) (f q : Expr) (extra : Array Expr) : TM Lean.Term := do
  let q ← instantiateMVars q
  if q.isAppOfArity ``Quot.mk 3 then return ← tr L (mkAppN f (#[q.appArg!] ++ extra))
  let some α := quotCarrier? (← whnf (← inferType q))
    | fail m!"the value{indentExpr q}\nis not a value of a quotient"
  let tq ← tr L q
  withLocalDeclD `a α fun y => do
    let body ← tr (L.bind y.fvarId!) (mkAppN f (#[y] ++ extra))
    `(LeanScript.Term.letE $tq $body)

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

/-- A call of a function on values of leaf types: `Term.extern`. -/
partial def trExtern (L : Loc) (name : String) (e fn : Expr) (args : Array Expr) :
    TM Lean.Term := do
  -- a value of a quotient is a representative: a call that computes to `Quot.mk r a` is `a`,
  -- any other call returning a quotient has no representative the language could compute
  if (quotCarrier? (← whnf (← inferType e))).isSome then
    let e' ← whnf e
    if e'.isAppOf ``Quot.mk then return ← tr L e'
    fail m!"the call{indentExpr e}\nreturns a value of a quotient, read as its carrier: it \
      cannot be an extern, since the language would need a representative of the class \
      (`Quot.out` is not computable)"
  let τ ← cirOf L (← inferType e) false
  unless τ.isLeaf do
    fail m!"the call{indentExpr e}\nreturns a value of a type that is not a leaf; it cannot \
      be an extern"
  let vs ← valueArgs L m!"`{name}`" fn args
  let tys ← vs.mapM fun i => do externLocal (← inferType args[i]!)
  let g ← withLocalDecls (vs.toList.zipIdx.map fun (_, k) =>
      ((Name.mkSimple s!"x{k}"), .default, fun _ => pure tys[k]!.1)).toArray fun ys => do
    let args' ← vs.zipIdx.foldlM (fun as (i, k) => do return as.set! i (← tys[k]!.2 ys[k]!)) args
    mkLambdaFVars ys (mkAppN fn args')
  externStx L name g (vs.map (args[·]!)) τ

/-- `decide p` of a relation `p` on values of leaf types: `Term.extern`. -/
partial def trDecide (L : Loc) (p : Expr) : TM Lean.Term := do
  let p ← instantiateMVars p
  let fn := p.getAppFn
  let args := p.getAppArgs
  let .const c _ := fn | fail m!"cannot translate the condition{indentExpr p}"
  let vs ← valueArgs L m!"`{c}`" fn args
  let tys ← vs.mapM fun i => do externLocal (← inferType args[i]!)
  let g ← withLocalDecls (vs.toList.zipIdx.map fun (_, k) =>
      ((Name.mkSimple s!"x{k}"), .default, fun _ => pure tys[k]!.1)).toArray fun ys => do
    let args' ← vs.zipIdx.foldlM (fun as (i, k) => do return as.set! i (← tys[k]!.2 ys[k]!)) args
    let p' := mkAppN fn args'
    let inst ← try synthInstance (mkApp (mkConst ``Decidable) p')
      catch _ => fail m!"the condition{indentExpr p}\nis not decidable"
    mkLambdaFVars ys (mkApp2 (mkConst ``Decidable.decide) p' inst)
  externStx L s!"decide {c}" g (vs.map (args[·]!)) (.prim (← `(LeanPrimTy.bool)))

/-- `Term.extern name (fun v => g v.1 v.2.1 …) args`. -/
partial def externStx (L : Loc) (name : String) (g : Expr) (args : Array Expr) (τ : CIR) :
    TM Lean.Term := do
  let v := mkIdent `v
  let mut call ← exprToSyntax g
  let mut comps : Array Lean.Term := #[]
  for k in [0:args.size] do comps := comps.push (← compStx v k)
  call ← `($call $comps*)
  let mut σs : Array Lean.Term := #[]
  for a in args do σs := σs.push (← (← cirOf L (← inferType a) false).stx L.c #[])
  let mut as ← `(LeanScript.Args.nil)
  for a in args.reverse do as ← `(LeanScript.Args.cons $(← tr L a) $as)
  `(LeanScript.Term.extern (σs := [$σs,*]) (τ := $(← τ.stx L.c #[])) $(quote name)
      (fun $v => $call) $as)

/-- A constructor application: `#leanscript_get_ctor` of the constructor, every parameter
    given by name, applied to the terms of the fields kept. -/
partial def trCtor (L : Loc) (cinfo : ConstructorVal) (fn : Expr) (args : Array Expr) :
    TM Lean.Term := do
  unless args.size == cinfo.numParams + cinfo.numFields do
    fail m!"the constructor `{cinfo.name}` is not fully applied"
  let mut ty ← inferType fn
  let mut named : Array (TSyntax ``leanscriptNamedArg) := #[]
  let mut fields : Array Lean.Term := #[]
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
  `((#leanscript_get_ctor $(mkIdent (`_root_ ++ cinfo.name)) $named*) $fields*)

/-- A value `a : Fin m → T` of a field that the language reads as `Nat → Option T`
    (`finOptArrow`): `fun j => if h : j < m then some (a ⟨j, h⟩) else none`, translated (a
    field of an opened constructor is already such a function; `m = 0` is `fun _ => none`). -/
partial def trOptField (L : Loc) (a : Expr) (aTy : Expr) : TM Lean.Term := do
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
partial def trRecCall (L : Loc) (e : Expr) : TM Lean.Term := do
  let args := e.getAppArgs
  let n := L.params.size
  -- a partial application may leave out trailing parameters that the recursion changes: the
  -- answer is then a function of them
  for i in [args.size:n] do
    unless L.vary.contains i do
      fail m!"the recursive call{indentExpr e}\nis not fully applied"
  let mut out? : Option Lean.Term := none
  let mut varyArgs : Array Lean.Term := #[]
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
        out? := some (← `(LeanScript.Term.record_casesOn $t
          (LeanScript.Term.var (DeBruijn.tail DeBruijn.head))))
        continue
      -- a member read through a field `Fin m → X` (as `Nat → Option X`): the answer at the
      -- `Option X` is `none` or `some` of the answer at `X`; below `m` it is `some`, and the
      -- unreachable `none` gets the default of the answer type
      if let some (t, .optHole) ← nestView? L a then
        unless L.vary.isEmpty && args.size == n do
          fail m!"the recursive call{indentExpr e}\non a value read through a field `Fin m → _` \
            must pass the other parameters unchanged"
        let d ← defaultTerm L (← inferType e) m!"the recursive call{indentExpr e}"
        out? := some (← `(LeanScript.Term.union_casesOn (LeanScript.Term.record_casesOn $t
            (LeanScript.Term.var (DeBruijn.tail DeBruijn.head)))
          (LeanScript.Branches.two $d (LeanScript.Term.var DeBruijn.head))))
        continue
    fail m!"the recursive call{indentExpr e}\nis not structural: it must pass the parameters \
      unchanged except the one recursed on, which must be a direct subvalue of it"
  let some t := out? | fail m!"the recursive call{indentExpr e}\ndoes not recurse on a subvalue"
  -- the answer is a function of the parameters that change, then applied to the arguments
  -- beyond the parameters (`ack2 m n` for `ack2 : Nat → (Nat → Nat)`)
  let extra ← args[n:].toArray.mapM (tr L)
  appStx t (varyArgs ++ extra)

/-- A case analysis `T.casesOn motive major minors…`. -/
partial def trCases (L : Loc) (c : Name) (args : Array Expr) (e : Expr) : TM Lean.Term := do
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
      return ← `(LeanScript.Term.nat_rec $(← tr L major) $z $s)
    let ps := vary.map (L.params[·]!)
    let ρ ← tyStx L (← mkForallFVars ps (← inferType e))
    let r ← `(LeanScript.Term.nat_rec (τ := $ρ) $(← tr L major) $z $s)
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
      return ← casesBodyStx plan (← varStx (L.slots.size - 1 - bodySlot)) brs
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
    let mut brs : Array Lean.Term := #[]
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
          brs := brs.push (← `(LeanScript.Term.union_casesOn (LeanScript.Term.var DeBruijn.head)
            (LeanScript.Branches.two (LeanScript.Term.union_mk LeanScript.CtorIx.two₁ LeanScript.Args.nil)
              (LeanScript.Term.record_casesOn (LeanScript.Term.var DeBruijn.head)
                (LeanScript.Term.union_mk LeanScript.CtorIx.two₂
                  (LeanScript.Args.cons (LeanScript.Term.var (DeBruijn.tail DeBruijn.head))
                    LeanScript.Args.nil))))))
          continue
        -- no function of the group recurses on this member: its answers are never read
        ρs := ρs.push (← `(LeanScript.Ty.bool))
        brs := brs.push (← `(LeanScript.Term.lit LeanScript.LeanPrimTy.bool true))
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
    let brFun ← finFunStx brs
    let Δ := mkIdent (prog.name ++ `Δ)
    let r ← if L.depth = 0 then
        `(LeanScript.Term.data_rec (Δ := $Δ) $(← brefStx L.c b) $ρFun $brFun $(quote j)
          $(← tr L major))
      else
        `(LeanScript.Term.data_brec (Δ := $Δ) $(← brefStx L.c b) $ρFun $(quote L.depth)
          $brFun $(quote j) $(← tr L major))
    return ← appStx r (← ps.mapM (tr L))
  -- an ordinary case analysis
  let mut scrut ← tr L major
  if let some (b, j) := plan.data? then
    scrut ← `(LeanScript.Term.data_out $(← brefStx L.c b) $(quote j) $scrut)
  let brs ← (List.range nM).toArray.mapM fun k => openMinor k minors[k]! fun xs erased body => do
    let kept := (xs.zip erased).filter (!·.2) |>.map (·.1)
    let mut L' := L
    for x in kept.reverse do L' := L'.bind x.fvarId!
    tr L' body
  casesBodyStx plan scrut brs

/-- The branch of the fold at one member: the case analysis `c args` of the parameter recursed
    on, at the top of the body of the member's function.  Its fields are opened as windows
    (`openWindows`), and the parameter is the constructor application in each branch. -/
partial def recBranch (L : Loc) (c : Name) (args : Array Expr) : TM Lean.Term := do
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
    casesBodyStx plan (← varStx vps.size) brs

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
partial def nestView? (L : Loc) (e : Expr) : TM (Option (Lean.Term × NShape)) := do
  let e := (← instantiateMVars e).headBeta
  let .fvar x := e.getAppFn | return none
  let some s := L.nest[x]? | return none
  let some i := L.index? x | return none
  let mut t ← varStx i
  let mut s := s
  for a in e.getAppArgs do
    match s with
    | .fn s' =>
      t ← `(LeanScript.Term.app $t $(← tr L a))
      s := s'
    | _ => fail m!"cannot translate the application{indentExpr e}"
  return some (t, s)

/-- `Array.foldl f z xs` over an array `xs` that holds members of the block recursed on (with
    their answers): `Term.array_foldl`, whose step sees each element as the subvalue, with the
    answer at it for the recursive calls. -/
partial def trNestFoldl (L : Loc) (arr : Lean.Term) (s : NShape) (args : Array Expr) :
    TM Lean.Term := do
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
      `(LeanScript.Term.array_foldl $arr $z
          (LeanScript.Term.record_casesOn (LeanScript.Term.var DeBruijn.head) $(← tr L2 body)))
    | s' =>
      let L2 := L1.bind x.fvarId!
      let L2 := { L2 with nest := L2.nest.insert x.fvarId! s' }
      `(LeanScript.Term.array_foldl $arr $z $(← tr L2 body))

end

/-- The values of the parameters of a definition (its locals `xs`) that are the type index of
    a later parameter's type-indexed family (`α` in `Nest.size {α} (n : Nest α)`): the index
    the family is read at (`Nest.Elem Nat`), for the index given by name (`(α := Nat)`) or,
    when not given, the only one at which the program declares the family. -/
def typeIndexValues (f : Name) (xs : Array Expr) (idxParams : Array Nat)
    (named : Array (Ident × Lean.Term)) (prog? : Option ProgInfo) :
    TermElabM (Array (Option Expr)) := do
  let mut out : Array (Option Expr) := Array.replicate xs.size none
  let mut used : Array Name := #[]
  for i in idxParams do
    let x := xs[i]!
    unless (← whnf (← inferType x)).isSort do continue
    let n ← x.fvarId!.getUserName
    -- the binder's name in the type of `f` (the unfolding equation may rename it)
    let n' ← forallTelescope (← getConstInfo f).type fun ys _ =>
      if h : i < ys.size then ys[i].fvarId!.getUserName else pure n
    let shown := if n'.hasMacroScopes then n else n'
    -- the family it is the index of
    let mut fam? : Option (InductiveVal × Array Expr) := none
    for j in [i + 1:xs.size] do
      let t ← whnf (← instantiateMVars (← inferType xs[j]!))
      let some (c, _) := t.getAppFn.const? | continue
      let some (.inductInfo ind) := (← getEnv).find? c | continue
      unless ← typeIndexed ind do continue
      if t.getAppNumArgs == ind.numParams + 1 && t.appArg! == x then
        fam? := some (ind, t.getAppArgs[:ind.numParams].toArray)
        break
    let some (ind, ps) := fam? | fail m!"the parameter `{n}` of `{f}` is a type"
    if ps.any (·.hasFVar) then
      fail m!"the parameters of `{ind.name}` in the type of `{f}` are not closed"
    let v ← match named.find? (fun a => a.1.getId == n || a.1.getId == n') with
      | some (a, stx) =>
        used := used.push a.getId
        let T ← elabType stx
        synthesizeSyntheticMVarsNoPostponing
        pure (← normType (mkAppN (mkConst ind.name) (ps.push (← instantiateMVars T)))).appArg!
      | none =>
        let cands := (prog?.map (·.members.flatten) |>.getD #[]).filter fun m =>
          m.isAppOfArity ind.name (ind.numParams + 1) && m.getAppArgs[:ind.numParams].toArray == ps
        match cands with
        | #[m] => pure m.appArg!
        | _ => fail m!"`{f}` is generic in the type index `{shown}` of `{ind.name}`: give the index \
            as `#leanscript_to_term {f} ({shown} := …)`"
    out := out.set! i (some v)
  for (a, _) in named do
    unless used.contains a.getId do fail m!"`{f}` has no type index named `{a.getId}`"
  return out

/-- Instantiate the binders of a `∀` at the positions given a value. -/
partial def instBinders (e : Expr) (vals : Array (Option Expr)) : Expr :=
  go e 0
where
  go (e : Expr) (i : Nat) : Expr :=
    match e with
    | .forallE n d b bi =>
      match vals[i]?.join with
      | some v => go (b.instantiate1 v) (i + 1)
      | none => .forallE n d (go b (i + 1)) bi
    | e => e

/-- The translation of the definition `f`, elaborated against `expected?`; `named` gives the
    type indices it is generic in (`(α := Nat)`). -/
def translateDef (f : Name) (expected? : Option Expr) (named : Array (Ident × Lean.Term) := #[]) :
    TermElabM Expr := do
  let info ← getConstInfo f
  unless info.levelParams.isEmpty do fail m!"`{f}` is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? f (nonRec := true)
    | fail m!"`{f}` is not a definition that can be unfolded"
  let prog? ← currentProg?
  let eqTy ← inferType (mkConst eqn)
  -- a type index a parameter's family is generic in is fixed first
  let (idxParams, vals) ← forallTelescope eqTy fun xs _ => do
    let idxParams ← indexParams xs
    return (idxParams, ← typeIndexValues f xs idxParams named prog?)
  let eqTy := instBinders eqTy vals
  let stx ← forallTelescope eqTy fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{f}`"
    let params := lhs.getAppArgs
    let given := (List.range params.size).toArray.filter (vals[·]!.isNone) |>.map (params[·]!)
    unless given == xs do
      fail m!"unexpected unfolding equation of `{f}`"
    let group ← mutualGroup f
    let recursive := group.any fun g => (rhs.find? (·.isConstOf g)).isSome
    let kept := (List.range params.size).toArray.filter (!idxParams.contains ·) |>.map (params[·]!)
    let L : Loc := { slots := kept.map (some ·.fvarId!), fns := if recursive then group else #[],
                     params, idxParams, prog?, c := prog?.map (·.members.size) |>.getD 0 }
    let go (L : Loc) : TM (Lean.Term × Lean.Term) := do
      for x in kept do
        if ← isType x then fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is a type"
        if (← isClass? (← inferType x)).isSome then
          fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is an instance"
        discard <| cirOf L (← inferType x)
      let mut body ← tr L rhs
      for _ in kept do body ← `(LeanScript.Term.lam $body)
      -- the type of the translation: the parameters kept, then the result (an index
      -- parameter only occurs in indices, which are erased)
      let ty ← if idxParams.isEmpty then pure info.type
        else mkForallFVars kept (← inferType lhs)
      return (body, ← tyStx L ty)
    -- the depth of the course-of-values recursion: the first that works
    let mut res? := none
    let mut err? : Option Exception := none
    for d in [0:4] do
      if d > 0 && !recursive then break
      try
        res? := some (← (go { L with depth := d }).run { st := St.ofProg #[] prog? })
        break
      catch e => if err?.isNone then err? := some e
    let some ((body, ty), s) := res? | throw err?.get!
    match prog?, s.usesData with
    | some p, true => `(($body : LeanScript.Term $(mkIdent (p.name ++ `Δ)) [] $ty))
    | _, _ =>
      let d? ← match expected? with
        | some t =>
          let t ← whnfR (← instantiateMVars t)
          if t.isAppOfArity ``LeanScript.Term 4 then pure (some t.getAppArgs[1]!) else pure none
        | none => pure none
      match d? with
      | some d => `(($body : LeanScript.Term $(← exprToSyntax d) [] $ty))
      | none =>
        let ks := mkIdent `ks
        let d := mkIdent `Δ
        `(fun {$ks : List Nat} {$d : LeanScript.DSig $ks} => ($body : LeanScript.Term $d [] $ty))
  let v ← elabTerm stx expected?
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars v

/-- `#leanscript_to_term f`: the translation of the Lean definition `f` to a closed
    `LeanScript.Term`. -/
syntax:max (name := leanscriptToTerm)
  "#leanscript_to_term " ident (ppSpace leanscriptNamedArg)* : term

/-- `#leanscript_to_term f`, as a command: show the type of the translation. -/
syntax (name := leanscriptToTermCmd)
  "#leanscript_to_term " ident (ppSpace leanscriptNamedArg)* : command

def resolveDef (id : Ident) : TermElabM Name :=
  try realizeGlobalConstNoOverloadWithInfo id
  catch _ => fail m!"unknown constant `{id.getId}`"

@[term_elab leanscriptToTerm]
def elabToTerm : TermElab := fun stx expected? => do
  translateDef (← resolveDef ⟨stx[1]⟩) expected? (namedArgs stx[2])

@[command_elab leanscriptToTermCmd]
def elabToTermCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let v ← translateDef (← resolveDef ⟨stx[1]⟩) none (namedArgs stx[2])
  logInfo m!"{stx[1]} : {← inferType v}"

end LeanScript.Gen

end
