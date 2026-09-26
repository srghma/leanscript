module

public meta import LeanScript.GetCtor
public meta import Lean.Meta.Eqns

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
| a case analysis (`match`, `casesOn`) | `#leanscript_get_cases`' shape: `ite`, `enum_casesOn`, `letE`, `record_casesOn`, `union_casesOn`; after `data_out` for a recursive type; `nat_rec` for `Nat` |
| a projection of a structure | `record_casesOn` (or the value itself, for one field) |
| structural recursion on a `Nat` parameter | `Term.nat_rec` |
| structural recursion on a parameter of a declared datatype whose block has one member | `Term.data_rec` |
| the same, with recursive calls on subvalues up to four levels down (`f (y :: t)`, `f t` in the branch of `_ :: y :: t`) | `Term.data_brec` of the smallest depth that reaches them |

A recursive definition must recurse directly on one of its parameters, at the top of its
body (`f x = match x with …`), passing the other parameters unchanged; in a branch the
parameter recursed on is the constructor application it was matched against.

Everything else is refused with an error, in particular a type with one value or none
(`Unit`, `Empty`, …: as a parameter, a `let`, a field or a value), a type of two values
other than `Bool` (such a type *is* `bool`), a parameter that is a type or an instance,
recursion through a helper, well-founded recursion, a pattern on a numeral other than
`0`/`n + 1`, and an extern whose argument or result is not a leaf type.
-/

open Lean Meta Elab Term

namespace LeanScript.Gen

/-- The state of a translation: the state of the type translator, and whether a declared
    datatype has been used (then the term is over the current program). -/
structure TS where
  st : St
  usesData : Bool := false

abbrev TM := StateT TS TermElabM

/-- Run a step of the type translator. -/
def lm {α : Type} (x : M α) : TM α := fun s => do
  let (a, st) ← (x.run s.st : MetaM _)
  return (a, { s with st })

/-- The variables in scope and what the translation knows about them. -/
structure Loc where
  /-- The variables of the term's context, outermost first: `some x` a Lean local, `none` a
      variable with no Lean local (the answer of a recursive call, a pair of a subvalue and
      its answer, …). -/
  slots : Array (Option FVarId) := #[]
  /-- A subvalue the recursion reached ↦ the variable holding the answer at it. -/
  ans : Std.HashMap FVarId Nat := {}
  /-- The function translated, when it is recursive. -/
  fn? : Option Name := none
  /-- Its parameters. -/
  params : Array Expr := #[]
  /-- The program. -/
  prog? : Option ProgInfo := none
  /-- The number of visible blocks (those of the program). -/
  c : Nat := 0
  /-- A subvalue whose window has its body ↦ the variable of the body, and the depth of the
      windows in its holes. -/
  win : Std.HashMap FVarId (Nat × Nat) := {}
  /-- The depth of the course-of-values recursion (`0`: `data_rec`). -/
  depth : Nat := 0

def Loc.bind (L : Loc) (x : Option FVarId) : Loc := { L with slots := L.slots.push x }

def Loc.index? (L : Loc) (x : FVarId) : Option Nat :=
  (L.slots.findIdx? (· == some x)).map fun p => L.slots.size - 1 - p

/-- A de Bruijn index. -/
def dbStx : Nat → MetaM Lean.Term
  | 0 => `(DeBruijn.head)
  | n + 1 => do `(DeBruijn.tail $(← dbStx n))

def varStx (i : Nat) : MetaM Lean.Term := do `(LeanScript.Term.var $(← dbStx i))

/-- The closed translation of a type. -/
def cirOf (L : Loc) (T : Expr) : TM CIR := do
  let t ← lm do
    let T ← normType T
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
  match L.fn? with
  | some f => (e.find? (·.isConstOf f)).isSome
  | none => false

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
        try pure (← cirOf L (← inferType a)).isLeaf catch _ => pure false
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
  if L.fn?.isNone || !minors.any L.mentionsFn then none
  else if L.slots.size != L.params.size then none
  else L.params.findIdx? (· == major)

/-- Open the fields of a branch of a recursion on the datatype `T` (their Lean locals `xs`,
    the erased ones marked), the first field kept innermost; a field of type `T` is the
    window of depth `d` of the subvalue (`DSig.Block.win`), which is taken apart: the
    subvalue, the answer at it and, for `d > 0`, its body, whose holes are windows of depth
    `d - 1`. -/
partial def openWindows (L : Loc) (T : Expr) (xs : Array Expr) (erased : Array Bool) (d : Nat)
    (kont : Loc → TM Lean.Term) : TM Lean.Term := do
  let kept := (xs.zip erased).filter (!·.2) |>.map (·.1)
  let holes ← kept.filterM fun x => do isDefEq (← normType (← inferType x)) T
  let mut L' := L
  for x in kept.reverse do
    L' := L'.bind (if holes.contains x then none else some x.fvarId!)
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

mutual

/-- The translation of an expression. -/
partial def tr (L : Loc) (e : Expr) : TM Lean.Term := do
  let e := (← instantiateMVars e).headBeta
  match e with
  | .mdata _ e => tr L e
  | .fvar x =>
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
  | .proj S i s => trProj L S i s
  | _ =>
    let T ← inferType e
    if (← isProp T) || (← isType e) then
      fail m!"the proof or type{indentExpr e}\nhas no value in the language"
    -- a closed value of a leaf type is a literal
    if !e.hasFVar && !e.hasMVar && !L.mentionsFn e then
      if let .prim p ← cirOf L T then
        return ← `(LeanScript.Term.lit $p rfl $(← exprToSyntax e))
    trApp L e

/-- A projection `s.i` of a structure. -/
partial def trProj (L : Loc) (S : Name) (i : Nat) (s : Expr) : TM Lean.Term := do
  let T ← normType (← inferType s)
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
  | .fvar _ =>
    let mut r ← tr L fn
    for a in args do r ← `(LeanScript.Term.app $r $(← tr L a))
    return r
  | .const c _ =>
    let env ← getEnv
    if L.fn? == some c then return ← trRecCall L e
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
    if isCasesOnRecursor env c then return ← trCases L c args
    if ← isMatcher c then
      let info ← getConstInfo c
      let v := info.value!.instantiateLevelParams info.levelParams fn.constLevels!
      return ← tr L (← Core.betaReduce (v.beta args))
    if let some (.ctorInfo cinfo) := env.find? c then
      if !((← cirOf L (← inferType e)) matches .prim _) then
        return ← trCtor L cinfo fn args
    if let some pinfo ← getProjectionFnInfo? c then
      if !pinfo.fromClass then
        if let some e' ← unfoldDefinition? e then return ← tr L e'
    trExtern L (toString c) e fn args
  | _ => fail m!"cannot translate the application{indentExpr e}"

/-- A call of a function on values of leaf types: `Term.extern`. -/
partial def trExtern (L : Loc) (name : String) (e fn : Expr) (args : Array Expr) :
    TM Lean.Term := do
  let τ ← cirOf L (← inferType e)
  unless τ.isLeaf do
    fail m!"the call{indentExpr e}\nreturns a value of a type that is not a leaf; it cannot \
      be an extern"
  let vs ← valueArgs L m!"`{name}`" fn args
  let tys ← vs.mapM fun i => inferType args[i]!
  let g ← withLocalDecls (vs.toList.zipIdx.map fun (_, k) =>
      ((Name.mkSimple s!"x{k}"), .default, fun _ => pure tys[k]!)).toArray fun ys => do
    let args' := vs.zipIdx.foldl (fun as (i, k) => as.set! i ys[k]!) args
    mkLambdaFVars ys (mkAppN fn args')
  externStx L name g (vs.map (args[·]!)) τ

/-- `decide p` of a relation `p` on values of leaf types: `Term.extern`. -/
partial def trDecide (L : Loc) (p : Expr) : TM Lean.Term := do
  let p ← instantiateMVars p
  let fn := p.getAppFn
  let args := p.getAppArgs
  let .const c _ := fn | fail m!"cannot translate the condition{indentExpr p}"
  let vs ← valueArgs L m!"`{c}`" fn args
  let tys ← vs.mapM fun i => inferType args[i]!
  let g ← withLocalDecls (vs.toList.zipIdx.map fun (_, k) =>
      ((Name.mkSimple s!"x{k}"), .default, fun _ => pure tys[k]!)).toArray fun ys => do
    let args' := vs.zipIdx.foldl (fun as (i, k) => as.set! i ys[k]!) args
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
  for a in args do σs := σs.push (← tyStx L (← inferType a))
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
  for i in [0:args.size] do
    ty ← whnf ty
    let .forallE n d b bi := ty | fail m!"bad constructor `{cinfo.name}`"
    let a := args[i]!
    if i < cinfo.numParams then
      if a.hasFVar then fail m!"the parameter `{n}` of `{cinfo.name}` is not closed{indentExpr a}"
      named := named.push (← `(leanscriptNamedArg| ($(mkIdent n) := $(← exprToSyntax a))))
    else if !(← isErasedField bi d) then
      fields := fields.push (← tr L a)
    ty := b.instantiate1 a
  let T ← normType (← inferType (mkAppN fn args))
  if (← cirOf L T).hasData then modify fun s => { s with usesData := true }
  `((#leanscript_get_ctor $(mkIdent (`_root_ ++ cinfo.name)) $named*) $fields*)

/-- A recursive call `f … y …` on a subvalue `y` the recursion reached: the variable of its
    answer. -/
partial def trRecCall (L : Loc) (e : Expr) : TM Lean.Term := do
  let args := e.getAppArgs
  unless args.size == L.params.size do
    fail m!"the recursive call{indentExpr e}\nis not fully applied"
  let mut out? : Option Nat := none
  for i in [0:args.size] do
    let a := args[i]!
    if a == L.params[i]! then continue
    if let .fvar y := a then
      if let some slot := L.ans[y]? then
        if out?.isNone then
          out? := some (L.slots.size - 1 - slot)
          continue
    fail m!"the recursive call{indentExpr e}\nis not structural: it must pass the parameters \
      unchanged except the one recursed on, which must be a direct subvalue of it"
  match out? with
  | some i => varStx i
  | none => fail m!"the recursive call{indentExpr e}\ndoes not recurse on a subvalue"

/-- A case analysis `T.casesOn motive major minors…`. -/
partial def trCases (L : Loc) (c : Name) (args : Array Expr) : TM Lean.Term := do
  let ind ← getConstInfoInduct c.getPrefix
  let nP := ind.numParams
  unless ind.numIndices == 0 do fail m!"`{ind.name}` is an inductive family with indices"
  let nM := ind.ctors.length
  unless args.size ≥ nP + 2 + nM do fail m!"`{c}` is not fully applied"
  let major := args[nP + 1]!
  let extra := args[nP + 2 + nM:].toArray
  let minors := (args[nP + 2 : nP + 2 + nM].toArray).map fun m => m
  let T ← normType (← inferType major)
  let ctorInfos ← ind.ctors.toArray.mapM getConstInfoCtor
  -- open a branch: its fields as locals, the extra arguments pushed inside
  let openMinor {α : Type} (k : Nat) (m : Expr)
      (kont : Array Expr → Array Bool → Expr → TM α) : TM α := do
    let ci := ctorInfos[k]!
    let mTy ← inferType m
    forallBoundedTelescope mTy ci.numFields fun xs _ => do
      let erased ← xs.mapM fun x => do
        let d ← x.fvarId!.getDecl
        isErasedField d.binderInfo d.type
      kont xs erased (mkAppN (mkAppN m xs) extra).headBeta
  let recPos? := L.recParam? major minors
  -- in a branch of the case analysis of a parameter recursed on, the parameter is the
  -- constructor application
  let subst (k : Nat) (xs : Array Expr) (body : Expr) : Expr :=
    if recPos?.isSome then
      body.replaceFVar major (mkAppN (mkAppN (mkConst ctorInfos[k]!.name T.getAppFn.constLevels!)
        T.getAppArgs) xs)
    else body
  if ind.name == ``Nat then
    let z ← openMinor 0 minors[0]! fun _ _ b => tr L (subst 0 #[] b)
    let s ← openMinor 1 minors[1]! fun xs _ b => do
      let m := xs[0]!
      let L' := (L.bind m.fvarId!).bind none
      let L' := if recPos?.isSome then { L' with ans := L'.ans.insert m.fvarId! (L'.slots.size - 1) }
        else L'
      tr L' (subst 1 xs b)
    return ← `(LeanScript.Term.nat_rec $(← tr L major) $z $s)
  let plan ← lm (planType T L.prog?)
  if plan.data?.isSome then modify fun st => { st with usesData := true }
  -- a case analysis of a subvalue inside a window of a course-of-values recursion: its body
  -- is already there, its holes are windows one level shallower
  if let .fvar h := major then
    if let some (bodySlot, d) := L.win[h]? then
      let brs ← (List.range nM).toArray.mapM fun k => openMinor k minors[k]! fun xs erased body => do
        let ctorApp := mkAppN (mkAppN (mkConst ctorInfos[k]!.name T.getAppFn.constLevels!)
          T.getAppArgs) xs
        let body := body.replace fun s => if s == ctorApp then some major else none
        openWindows L T xs erased d (tr · body)
      return ← casesBodyStx plan (← varStx (L.slots.size - 1 - bodySlot)) brs
  -- structural recursion on a declared datatype
  if let (some _, some (b, j)) := (recPos?, plan.data?) then
    let prog := L.prog?.get!
    unless prog.members[b]!.size == 1 do
      fail m!"recursion on{indentExpr T}\nwhose block has several members is not supported"
    let resTy ← inferType (mkAppN (mkConst L.fn?.get!) L.params)
    let ρ ← tyStx L resTy
    let brs ← (List.range nM).toArray.mapM fun k => openMinor k minors[k]! fun xs erased body =>
      openWindows (L.bind none) T xs erased L.depth (tr · (subst k xs body))
    let body ← casesBodyStx plan (← varStx 0) brs
    if L.depth = 0 then
      return ← `(LeanScript.Term.data_rec $(← brefStx L.c b) (fun _ => $ρ)
        (fun ⟨0, _⟩ => $body) $(quote j) $(← tr L major))
    return ← `(LeanScript.Term.data_brec $(← brefStx L.c b) (fun _ => $ρ) $(quote L.depth)
      (fun ⟨0, _⟩ => $body) $(quote j) $(← tr L major))
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

end

/-- The translation of the definition `f`, elaborated against `expected?`. -/
def translateDef (f : Name) (expected? : Option Expr) : TermElabM Expr := do
  let info ← getConstInfo f
  unless info.levelParams.isEmpty do fail m!"`{f}` is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? f (nonRec := true)
    | fail m!"`{f}` is not a definition that can be unfolded"
  let prog? ← currentProg?
  let eqTy ← inferType (mkConst eqn)
  let stx ← forallTelescope eqTy fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{f}`"
    unless lhs.getAppArgs == xs do fail m!"unexpected unfolding equation of `{f}`"
    let recursive := (rhs.find? (·.isConstOf f)).isSome
    let L : Loc := { slots := xs.map (some ·.fvarId!), fn? := if recursive then some f else none,
                     params := xs, prog?, c := prog?.map (·.members.size) |>.getD 0 }
    let go (L : Loc) : TM (Lean.Term × Lean.Term) := do
      for x in xs do
        if ← isType x then fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is a type"
        if (← isClass? (← inferType x)).isSome then
          fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is an instance"
        discard <| cirOf L (← inferType x)
      let mut body ← tr L rhs
      for _ in xs do body ← `(LeanScript.Term.lam $body)
      return (body, ← tyStx L info.type)
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
syntax:max (name := leanscriptToTerm) "#leanscript_to_term " ident : term

/-- `#leanscript_to_term f`, as a command: show the type of the translation. -/
syntax (name := leanscriptToTermCmd) "#leanscript_to_term " ident : command

def resolveDef (id : Ident) : TermElabM Name :=
  try realizeGlobalConstNoOverloadWithInfo id
  catch _ => fail m!"unknown constant `{id.getId}`"

@[term_elab leanscriptToTerm]
def elabToTerm : TermElab := fun stx expected? => do
  translateDef (← resolveDef ⟨stx[1]⟩) expected?

@[command_elab leanscriptToTermCmd]
def elabToTermCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let v ← translateDef (← resolveDef ⟨stx[1]⟩) none
  logInfo m!"{stx[1]} : {← inferType v}"

end LeanScript.Gen

end
