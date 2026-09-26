module

public meta import LeanScript.ToTerm.TransRecObject
public meta import LeanScript.ToTerm.Default

@[expose] public section

meta section

/-!
# The translation of a recursion on a recursive tagged union: its pieces

The data `LeanScript.ToTerm.transRecUnionBrecOn?` reads off a recursive tagged union
(`RecUnionCtor`, `RecUnionInfo`), the leaf translation of a branch, and the builders of the
fold's `FoldKBranch` cases.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- One constructor of a recursive tagged union, as the fold reads it. -/
structure RecUnionCtor where
  /-- The Lean constructor. -/
  name : Name
  /-- Its fields: `none` for a field that is the union itself, `some α` for one of the
      Lean type `α`, which does not mention it. -/
  fields : Array (Option Expr)
  /-- Which fields the language erases (a type, a proof, an instance): bound as Lean
      variables, but not by the branch of the language, and absent from `fsL`.  The type
      `α` of `pair {α β : Type} (a : TExpr α) (b : TExpr β)` is one.  Empty when none is. -/
  erased : Array Bool := #[]
  /-- The list of its field trees, as an expression of type `List (TyWfIn 1)` — the index
      of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- Its type at the parameters, `∀ fields, X params indices`: a field of an indexed
      family's constructor may be typed by the ones before it (`v : Vec α n`). -/
  cty : Expr

/-- The type of the next field of a constructor of type `cty`, after the fields `vals`. -/
def ctorFieldTy (cty : Expr) (vals : Array Expr) : MetaM Expr := do
  let t ← whnf (← instantiateForall cty vals)
  let .forallE _ d _ _ := t
    | throwError "`#leanscript_to_term`: internal: the constructor has no more fields"
  return d

/-- What the fold of a recursive tagged union needs to know about it and the recursion. -/
structure RecUnionInfo where
  /-- The inductive type. -/
  ind : Name
  /-- The universe levels. -/
  lvls : List Level
  /-- The parameters. -/
  params : Array Expr
  /-- The Lean type of the union, at its parameters. -/
  selfTy : Expr
  /-- The constructors, in order. -/
  ctors : Array RecUnionCtor
  /-- The schema of the union. -/
  l : Expr
  /-- The binders of a branch, `TyWf.recBinders ty τ`. -/
  bindE : Expr
  /-- The Lean type of the answers. -/
  τLean : Expr
  /-- The language's type of the answers. -/
  τ : Expr
  /-- The Lean branch of the `brecOn`. -/
  brecF : Expr
  /-- The motives of the `brecOn`. -/
  motives : Array Expr
  /-- The number of indices of the type (`0` unless it is an indexed family). -/
  nI : Nat := 0
  /-- The motive of the `brecOn`, reduced to a `fun`. -/
  motive0 : Expr := .bvar 0

/-- The index lists of the branches of a dispatch on this tagged-union schema of
    `TyWfIn sc`, one per constructor, in order: `fields.toList` for a constructor with a
    non-empty payload, `[]` for one without, as `LeanScript.TaggedUnionFoldKCases` (at
    `sc = 1`) and `LeanScript.FamilyTaggedUnionFoldKCases` are indexed. -/
partial def schemaCtorIndices (sc : Nat) (l : Expr) : MetaM (Array Expr) := do
  let ι := tyWfInE sc
  let toListE (ne : Expr) : Expr :=
    mkApp2 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.toList [Level.zero])
      ι ne
  let nilE := mkApp (mkConst ``List.nil [Level.zero]) ι
  let rec cps (cp : Expr) : MetaM (Array Expr) := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
        return #[toListE fields] ++ (← listOfExpr rest).toArray
    | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
        return #[nilE] ++ (← cps rest)
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      return #[toListE fields, next] ++ (← listOfExpr rest).toArray
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return #[nilE] ++ (← cps rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- Replace the variables descended into by the shapes found for them, in the order they
    were descended into (a shape may mention variables descended into later). -/
def resolveShape (descend : Array (FVarId × Expr)) (e : Expr) : Expr :=
  descend.foldl (init := e) fun acc (f, s) => acc.replaceFVar (.fvar f) s

/-- The branch of the fold at a node of the case tree: the Lean branch instantiated at the
    shape found so far (`top` resolved through `descend`) and at the history in which the
    answer at a bound subvalue is its variable (`answers`), reduced, and translated in
    `c`.

    When the reduced branch still reads something the fold has not given — the history
    below a subvalue that has not been looked into — the result is `.inr` of those of the
    `pending` subvalues (the occurrences not yet looked into, at this node and at the
    nodes above it) whose history it reads: a deeper look into one of them is what the
    branch needs.  It fails when it reads nothing that a deeper look could give. -/
def recUnionLeaf (trans : TransFn) (info : RecUnionInfo) (c : TCtx) (top : Expr)
    (descend : Array (FVarId × Expr)) (answers : Array (Expr × Expr))
    (pending : Array FVarId) : MetaM (Expr ⊕ Array FVarId) := do
  let shape := resolveShape descend top
  let answers := answers.map fun (s, a) => (resolveShape descend s, a)
  let nP := info.params.size
  -- an indexed family's branch takes the value's indices first
  let idx := (← whnf (← inferType shape)).getAppArgs.extract nP (nP + info.nI)
  let fty ← instantiateForall (← inferType info.brecF) (idx.push shape)
  let .forallE _ histTy _ _ ← whnf fty
    | throwError "`#leanscript_to_term`: internal: the branch of the recursion takes no \
        history"
  let (fn, hargs) := histTy.getAppFnArgs
  let nM := info.motives.size
  let motiveTys ← info.motives.mapM inferType
  let decls : Array (Name × (Array Expr → MetaM Expr)) :=
    motiveTys.mapIdx fun i t => (Name.mkSimple s!"motive{i}", fun _ => pure t)
  let hist ← withLocalDeclsD decls fun ms => do
    let lvls := histTy.getAppFn.constLevels!
    let placeholder := mkAppN (mkConst fn lvls)
      (hargs.extract 0 nP ++ ms ++ hargs.extract (nP + nM) hargs.size)
    let h ← buildRecObjHistory ms info.motives answers placeholder
    if ms.any (fun m => h.containsFVar m.fvarId!) then
      throwError "`#leanscript_to_term`: internal: the history mentions its motive"
    pure h
  let body ← reduceBrecBodyDeep (mkAppN info.brecF (idx ++ #[shape, hist]))
  -- a dispatch on an indexed family (another argument, `Vec α n` beside this one) hands
  -- the history through the equations of its `match`: its branches are read first, so
  -- that the history is in plain sight
  let body ← instantiateMVars (← reduceHistoryProjs body)
  let body ← Meta.transform body (pre := fun t => do
    match ← normalizeIndexedCasesOn? t with
    | some t' => return .continue t'
    | none => return .continue t)
  let body ← instantiateMVars (← reduceHistoryProjs body)
  if body.hasExprMVar then
    -- the unknown parts of the history are the histories below the subvalues not looked
    -- into, each a metavariable whose type names its subvalue
    let mut tys : Array Expr := #[]
    for m in ← getMVars body do
      tys := tys.push (← instantiateMVars (← m.getType))
    let needed := pending.filter fun f => tys.any (·.containsFVar f)
    unless needed.isEmpty do return .inr needed
    throwError "`#leanscript_to_term`: this recursion on a recursive tagged union reads \
      the value of the function, or takes a value apart, further down than the fold \
      looks at this depth"
  let indName := (← whnf (← inferType top)).getAppFn.constName?
  return .inl (← trans { c with foldInds := c.foldInds ++ indName.toArray } body)

/-- The pointer at the `p`-th field of this list of field trees, which is an occurrence
    of the union. -/
def mkSelfFieldE (fsL : Array Expr) (p : Nat) : MetaM Expr := do
  let ι := tyWfInE 1
  let mut acc : Option Expr := none
  for r in [0:p + 1] do
    let i := p - r
    let a := fsL[i]!
    let rest ← mkListLit ι (fsL.extract (i + 1) fsL.size).toList
    match acc with
    | none =>
        let h ← mkEqRefl (mkConst ``LeanScript.Ty.self)
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.here)
          #[ι, mkConst ``LeanScript.IsSelfField, a, rest, h])
    | some inner =>
        acc := some (mkAppN (mkConst ``LeanScript.ListAnyT.there)
          #[ι, mkConst ``LeanScript.IsSelfField, a, rest, inner])
  return acc.get!

/-- The branches of a fold over the schema `l`, in its shape: `pre` are the implicit
    arguments every family of the case tree shares (signature, schema, binders, context,
    answer type, depth), and `branches` one `FoldKBranch` per constructor. -/
partial def mkRecUnionFoldKCases (pre : Array Expr) (l : Expr) (branches : Array Expr) :
    MetaM Expr := do
  let rest (from_ : Nat) (fsLists : List Expr) : MetaM Expr := do
    let mut acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.nil) pre
    let n := fsLists.length
    for i in [0:n] do
      let idx := n - 1 - i
      let fs := fsLists[idx]!
      let more ← mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE 1))
        (fsLists.drop (idx + 1))
      acc := mkAppN (mkConst `LeanScript.TaggedUnionFoldKCasesRest.cons)
        (pre ++ #[fs, more, branches[from_ + idx]!, acc])
    return acc
  let rec cpCases (cp : Expr) (i : Nat) : MetaM Expr := do
    match (← whnf cp).getAppFnArgs with
    | (``LeanScript.CtorsWithPayload.here, #[_, fields, restL]) =>
        let rs ← listOfExpr restL
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.here)
          (pre ++ #[fields, restL, branches[i]!, ← rest (i + 1) rs])
    | (``LeanScript.CtorsWithPayload.skip, #[_, more]) =>
        return mkAppN (mkConst `LeanScript.CtorsWithPayloadFoldKCases.skip)
          (pre ++ #[more, branches[i]!, ← cpCases more (i + 1)])
    | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, restL]) =>
      let rs ← listOfExpr restL
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.payloadFirst)
        (pre ++ #[fields, next, restL, branches[0]!, branches[1]!, ← rest 2 rs])
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) =>
      return mkAppN (mkConst `LeanScript.TaggedUnionFoldKCases.skip)
        (pre ++ #[cp, branches[0]!, ← cpCases cp 1])
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- A node of the case tree the fold has dispatched on: its constructor's field trees
    (`fsE`, with elements `fsL`) and, for each of its occurrences of the union, the
    position of the field and the variable bound for the subvalue there. -/
structure RecUnionFrame where
  /-- The list of the constructor's field trees, the index of its branch. -/
  fsE : Expr
  /-- The elements of `fsE`. -/
  fsL : Array Expr
  /-- The occurrences of the union among the fields: position and variable. -/
  subs : Array (Nat × FVarId)
  deriving Inhabited

/-- The nodes above a branch, innermost first, as the expression of type
    `List (List (TyWfIn 1))` the families of the case tree are indexed by. -/
def recUnionOuterE (outer : List RecUnionFrame) : MetaM Expr :=
  mkListLit (mkApp (mkConst ``List [Level.zero]) (tyWfInE 1)) (outer.map (·.fsE))

/-- The pointer `LeanScript.OuterSelfField` at the occurrence `sf` of the `i`-th node
    above (`0` the innermost). -/
def mkOuterSelfFieldE : List RecUnionFrame → Nat → Expr → MetaM Expr
  | f :: rest, 0, sf => do
      return mkAppN (mkConst ``LeanScript.OuterSelfField.here)
        #[f.fsE, ← recUnionOuterE rest, sf]
  | f :: rest, i + 1, sf => do
      return mkAppN (mkConst ``LeanScript.OuterSelfField.there)
        #[f.fsE, ← recUnionOuterE rest, ← mkOuterSelfFieldE rest i sf]
  | [], _, _ => throwError "`#leanscript_to_term`: internal: no node above to look into"

end LeanScript.ToTerm

end

end
