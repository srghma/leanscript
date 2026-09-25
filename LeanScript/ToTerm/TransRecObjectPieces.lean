module

public meta import LeanScript.ToTerm.TransRec
public meta import LeanScript.ToTerm.Brec

@[expose] public section

meta section

/-!
# The translation of a recursion on a recursive record: its pieces

What `LeanScript.ToTerm.TransRecObject` reads a recursive record and its recursion into
(`RecObjInfo`, one `RecObjField` per field), and the pieces it builds the fold's case tree
from: the history handed to the Lean branch, a leaf of the case tree, and the answers at
the subvalues a field of list or array type holds.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- How the fold of a record reads one field of a constructor of a union field. -/
inductive RecObjPayloadField where
  /-- A value that does not mention the record, of this Lean type. -/
  | plain (ty : Expr)
  /-- The record itself. -/
  | self
  /-- A value of a (non-recursive) structure (`Nat × Cell`): its constructor, universe
      levels and parameters, and how each of its fields is read. -/
  | struct (ctor : Name) (lvls : List Level) (params : Array Expr)
      (fields : Array RecObjPayloadField)
  /-- A value of a (non-recursive) union type (`Option Cell`, `Option (Nat × Cell)`): the
      inductive, its universe levels and parameters, and for each constructor its name
      and how each of its fields is read. -/
  | union (ind : Name) (lvls : List Level) (params : Array Expr)
      (ctors : Array (Name × Array RecObjPayloadField))
  /-- An array of the record itself (`Array Tree`), of this Lean type.  Lean folds it
      through two auxiliary motives, one for `Array Tree` and one for `List Tree`, and the
      window of the fold holds the array of the answers at its elements; the answer of
      the array's own motive is the fold of that array (`array_rec`) by the branches of
      those two motives. -/
  | arraySelf (ty : Expr)
  deriving Inhabited

/-- How the fold of a record reads one field of it: a field is read like a field of a
    constructor inside it — a value that does not mention the record, a structure around
    it (`Nat × Option Pair2`, the body of a newtype), or a union around it
    (`Option Cell`). -/
abbrev RecObjField := RecObjPayloadField

/-- What the fold of a record needs to know about it and about the recursion. -/
structure RecObjInfo where
  /-- The inductive type. -/
  ind : Name
  /-- Its constructor, with universe levels and parameters. -/
  ctor : Name
  /-- The universe levels. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- The Lean type of the record, at its parameters. -/
  selfTy : Expr
  /-- How each field is read. -/
  fields : Array RecObjField
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- Is it a recursive **newtype** (`Ty.recAlias`)?  Then the one field is the body, and
      a window is that body itself rather than a record of fields. -/
  isAlias : Bool := false
  /-- The translation, for the branches of the auxiliary motives of an array field. -/
  trans : TransFn := fun _ e => pure e
  /-- The motives of the `brecOn`. -/
  motives : Array Expr := #[]
  /-- The branches of the `brecOn`, one per motive. -/
  brecFs : Array Expr := #[]
  /-- The type each motive is a function of: the record, then the auxiliary types. -/
  motiveDoms : Array Expr := #[]

/-- The key under which `answers` holds the answer of motive `m` at `x`: `x` itself for
    the record's own motive, `x` marked with the motive's number for an auxiliary one
    (the motive of `Array Tree` or `List Tree`). -/
def motiveKey (m : Nat) (x : Expr) : Expr :=
  if m == 0 then x else mkMData (KVMap.empty.insert `leanscriptMotive (.ofNat m)) x

/-- How a field of this Lean type, inside a constructor of a union field of the recursive
    record `ind`, is read: the record itself, a value that does not mention it, or a
    value of a non-recursive structure whose fields are read in the same way. -/
partial def classifyRecObjPayload (ind : Name) (selfTy : Expr) (t : Expr) :
    MetaM RecObjPayloadField := do
  let mentions (t : Expr) : Bool := (t.find? fun s => s.isConstOf ind).isSome
  if ← isDefEq t selfTy then return .self
  if !mentions t then return .plain t
  if t.isAppOfArity ``Array 1 then
    if ← isDefEq t.appArg! selfTy then return .arraySelf t
    throwError "`#leanscript_to_term`: the field of type {t} holds the recursive record \
      {ind} in an array other than as its elements"
  let t' ← whnf t
  let .const j jl := t'.getAppFn
    | throwError "`#leanscript_to_term`: the field of type {t} mentions the recursive \
        record {ind} other than as the record itself"
  let some (.inductInfo ji) := (← getEnv).find? j
    | throwError "`#leanscript_to_term`: the field of type {t} mentions the recursive \
        record {ind} other than as the record itself"
  let jargs := t'.getAppArgs
  unless ji.numIndices == 0 && jargs.size == ji.numParams && !ji.isRec do
    throwError "`#leanscript_to_term`: the field of type {t} mentions the recursive record \
      {ind} other than as the record itself, inside a structure or inside a union"
  let mut ctors : Array (Name × Array RecObjPayloadField) := #[]
  for cn in ji.ctors do
    let ci ← getConstInfoCtor cn
    let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams jl) jargs
    let fs ← forallTelescopeReducing cty fun xs _ => do
      let mut out : Array RecObjPayloadField := #[]
      for x in xs do
        let ft ← inferType x
        if ft.hasAnyFVar (fun f => xs.any (·.fvarId! == f)) then
          throwError "`#leanscript_to_term`: the constructor {cn} has a dependent field"
        if ← LeanScript.Deriving.erasedBinder ft then
          throwError "`#leanscript_to_term`: the constructor {cn} has a field the \
            language erases, which the fold of a record does not read"
        out := out.push (← classifyRecObjPayload ind selfTy ft)
      return out
    ctors := ctors.push (cn, fs)
  if ctors.size == 1 then
    return .struct ctors[0]!.1 jl jargs ctors[0]!.2
  return .union j jl jargs ctors

/-- How a field of this Lean type is read by the fold of the record `info`. -/
def classifyRecObjField (ind : Name) (selfTy : Expr) (fty : Expr) : MetaM RecObjField :=
  classifyRecObjPayload ind selfTy fty

/-- Reduce the reads of a history built out of `PProd.mk`s: its projections, wherever they
    sit in the branch. -/
def reduceHistoryProjs (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun s => do
    match s with
    | .proj .. =>
        let s' ← whnfCore s
        return .done s'
    | _ =>
        if s.isAppOfArity ``PProd.fst 3 || s.isAppOfArity ``PProd.snd 3 then
          return .done (← whnfCore s)
        match ← reduceBranchStep? s with
        | some s' => return .visit s'
        | none => return .done s)

/-- The value of the history of a structural recursion on a record, at a value whose
    shape is known `k + 1` levels down.  `placeholder` is the type of the history with
    each motive replaced by a variable (`motiveVars`), so that the entry of the history
    that is the answer at a subvalue `x` is visibly `motiveVars[0] x`; `real` replaces
    those variables by the actual motives.  The answer at `x` is the variable `answers`
    maps it to; the entries of the other motives must be `PUnit`; anything that is still
    stuck — the history below a frontier subvalue — becomes a fresh metavariable, which
    the branch must not read. -/
partial def buildRecObjHistory (motiveVars : Array Expr) (motives : Array Expr)
    (answers : Array (Expr × Expr)) (placeholder : Expr) : MetaM Expr := do
  let real (t : Expr) : Expr := t.replaceFVars motiveVars motives
  let t ← whnf placeholder
  match t.getAppFn, t.getAppArgs with
  | .const ``PProd ls, #[a, b] =>
      let va ← buildRecObjHistory motiveVars motives answers a
      let vb ← buildRecObjHistory motiveVars motives answers b
      return mkAppN (mkConst ``PProd.mk ls) #[real a, real b, va, vb]
  | .const ``PUnit ls, #[] => return mkConst ``PUnit.unit ls
  | .fvar f, args =>
      if args.isEmpty then return ← mkFreshExprMVar (real t)
      -- the motive's value argument is its last: an indexed family's come before it
      let x := args.back!
      if motiveVars[0]!.fvarId! == f then
        for (s, ans) in answers do
          if s == x then return ans
        for (s, ans) in answers do
          if ← isDefEq s x then return ans
        throwError "`#leanscript_to_term`: internal: no answer for the subvalue {x}"
      else
        -- the answer of an auxiliary motive (of an array of the record), if it is known
        if let some m := motiveVars.findIdx? (·.fvarId! == f) then
          let key := motiveKey m x
          for (s, ans) in answers do
            if s == key then return ans
          for (s, ans) in answers do
            if let .mdata d s' := s then
              if d.getNat `leanscriptMotive == m then
                if ← isDefEq s' x then return ans
        let rt ← whnf (real t)
        match rt with
        | .const ``PUnit ls => return mkConst ``PUnit.unit ls
        | _ => throwError "`#leanscript_to_term`: this recursion on a recursive record \
            also recurses on {x}, which the fold of a record has no answer for"
  | _, _ => mkFreshExprMVar (real t)

/-- The Lean branch `brecF` of a `brecOn` instantiated at the value `shape` and at the
    history in which the answers are the variables `answers` maps them to, reduced.  It
    must read nothing further down, and no frontier subvalue. -/
def recObjBranchBody (info : RecObjInfo) (brecF : Expr) (motives : Array Expr)
    (shape : Expr) (answers : Array (Expr × Expr)) (frontier : Array Expr) :
    MetaM Expr := do
  let fty ← instantiateForall (← inferType brecF) #[shape]
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nP := info.params.size
  let nM := motives.size
  let motiveTys ← motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildRecObjHistory ms motives answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN brecF #[shape, hist])
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    throwError "`#leanscript_to_term`: this recursion on a recursive record reads the \
      value of the function further down than the depth tried"
  for g in frontier do
    if body.containsFVar g.fvarId! then
      throwError "`#leanscript_to_term`: this recursion on a recursive record takes apart \
        a value further down than the depth tried"
  return body

/-- The branch of the fold, at one leaf of the case tree: the Lean branch instantiated at
    the value built from the fields `vals`, reduced, and translated in `c`. -/
def recObjLeaf (trans : TransFn) (info : RecObjInfo) (brecF : Expr) (motives : Array Expr)
    (c : TCtx) (answers : Array (Expr × Expr)) (frontier : Array Expr) (vals : Array Expr) :
    MetaM Expr := do
  let shape := mkAppN (mkConst info.ctor info.lvls) (info.params ++ vals)
  let body ← recObjBranchBody info brecF motives shape answers frontier
  let indName := (← getConstInfoCtor info.ctor).induct
  trans { c with foldInds := c.foldInds.push indName } body

/-- The motive of the auxiliary type `dom` (`Array Tree`, `List Tree`), and the Lean type
    it answers; `none` when it answers `PUnit` — the recursion does not recurse on it. -/
def recObjAuxMotive (info : RecObjInfo) (dom : Expr) : MetaM (Option (Nat × Expr)) := do
  let mut m? : Option Nat := none
  for h : m in [0:info.motiveDoms.size] do
    if m?.isNone then
      if ← isDefEq info.motiveDoms[m] dom then m? := some m
  let some m := m?
    | throwError "`#leanscript_to_term`: internal: no motive of the recursion on {info.ind} \
        is a function of {dom}"
  let mot ← whnf info.motives[m]!
  unless mot.isLambda do
    throwError "`#leanscript_to_term`: internal: the motive of {dom} is not a function"
  lambdaBoundedTelescope mot 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: the recursion on {info.ind} has a dependent motive \
        for {dom}, which the language has no eliminator for"
    if body.isConstOf ``PUnit || body.isAppOf ``PUnit then return none
    return some (m, body)

/-- The answer of the auxiliary motive of an array field `Array Tree` at that field, as a
    term in `c`: the array `win` of the window holds the answer trees of depth `j` at the
    elements, and the answer is the fold of that array, `array_rec 0`, by the branches of
    the motive of `List Tree` — each given the answer at the head and the answer at the
    tail, the head and the tail themselves being frontier values — followed by the branch
    of the motive of `Array Tree`, given the answer at its list. -/
def recObjListAnswer (info : RecObjInfo) (c : TCtx) (win winTy : Expr) (j : Nat)
    (mL : Nat) (τLLean : Expr) : MetaM Expr := do
  let trans := info.trans
  let τL ← tyOfType τLLean
  let .array σ ← tyView winTy
    | throwError "`#leanscript_to_term`: internal: the window of an array field is not an array"
  let u ← getDecLevel info.selfTy
  let listTy := mkApp (mkConst ``List [u]) info.selfTy
  -- the empty list
  let nilV := mkApp (mkConst ``List.nil [u]) info.selfTy
  let nilBody ← recObjBranchBody info info.brecFs[mL]! info.motives nilV #[] #[]
  let nilT ← trans c nilBody
  -- a head and a tail, whose answers the fold of the array gives
  let consT ← withLocalDeclD `head (if j == 0 then info.τLean else mkConst ``Unit) fun hd =>
    withLocalDeclD `tail (mkConst ``Unit) fun tl =>
    withLocalDeclD `ih τLLean fun ih =>
    withLocalDeclD `t info.selfTy fun t =>
    withLocalDeclD `ts listTy fun ts => do
      let cC := c.pushFields #[(hd.fvarId!, σ), (tl.fvarId!, mkApp (mkConst ``LeanScript.TyWf.array) σ),
        (ih.fvarId!, τL)]
      let consV := mkApp3 (mkConst ``List.cons [u]) info.selfTy t ts
      let inner (cB : TCtx) (hdAns : Expr) : MetaM Expr := do
        let body ← recObjBranchBody info info.brecFs[mL]! info.motives consV
          #[(t, hdAns), (motiveKey mL ts, ih)] #[t, ts]
        trans cB body
      if j == 0 then
        inner cC hd
      else
        -- the head is an answer tree: its answer is the first field
        let .record fsT ← tyView σ
          | throwError "`#leanscript_to_term`: internal: an answer tree is not a record"
        let tTys := (← recordFieldTys fsT).toArray
        withLocalDeclD `ans info.τLean fun ans =>
        withLocalDeclD `win (mkConst ``Unit) fun w => do
          let c2 := cC.pushFields #[(ans.fvarId!, tTys[0]!), (w.fvarId!, tTys[1]!)]
          let b ← inner c2 ans
          return mkAppN (mkConst `LeanScript.Term.record_casesOn)
            #[c.sg, cC.gamma, τL, fsT, ← cC.var hd.fvarId!, b]
  let bases := mkAppN (mkConst `LeanScript.ArrayRecBases.nil) #[c.sg, c.gamma, σ, τL, nilT]
  return mkAppN (mkConst `LeanScript.Term.array_rec)
    #[c.sg, c.gamma, σ, τL, mkNatLit 0, win, bases, consT]

/-- The answer of the motive of `Array Tree` at an array field, as a term in `c`: its
    branch at `Array.mk l`, given the answer `ansL` at `l` (a variable of `c`) when the
    recursion has one for lists. -/
def recObjArrAnswer (info : RecObjInfo) (c : TCtx) (mA : Nat) (ansL? : Option (Nat × Expr)) :
    MetaM Expr := do
  let u ← getDecLevel info.selfTy
  let listTy := mkApp (mkConst ``List [u]) info.selfTy
  withLocalDeclD `l listTy fun l => do
    let arrV := mkApp2 (mkConst ``Array.mk [u]) info.selfTy l
    let answers := match ansL? with
      | some (mL, ansL) => #[(motiveKey mL l, ansL)]
      | none => #[]
    let body ← recObjBranchBody info info.brecFs[mA]! info.motives arrV answers #[l]
    info.trans c body

end LeanScript.ToTerm

end

end
