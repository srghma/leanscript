module

public meta import LeanScript.CtorFn.Classify
public meta import LeanScript.ToTerm.Build

@[expose] public section

/-!
# `#leanscript_ctor`: generating the definitions

`ensureCtorFn` generates (or finds in the cache) the layout and the constructor function of
a constructor.
-/

meta section

open Lean Meta Elab Term

namespace LeanScript.CtorFn

open LeanScript.Deriving (erasedBinder isTypeField isExistentialField modelledType?)

/-- Add a reducible definition, compiled when it can be. -/
def addReducibleDef (name : Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwError "`#leanscript_ctor`: internal error, `{name}` still has metavariables"
  let lvls := (collectLevelParams (collectLevelParams {} type) value).params.toList
  addDecl (.defnDecl
    { name := name, levelParams := lvls, type := type, value := value, hints := .abbrev,
      safety := .safe })
  try compileDecls #[name] catch _ => pure ()
  setReducibleAttribute name

/-- The tactic block `by head_ok` of a proof argument of the grammar, as the second argument
    of `autoParam`: read off the type of `LeanScript.Term.recAlias_mk`, whose `hAnf` is
    written by it. -/
def anfAutoParam : MetaM Expr := do
  let ci ← getConstInfoCtor ``LeanScript.Term.recAlias_mk
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      if (← x.fvarId!.getUserName).eraseMacroScopes == `hAnf then
        let ty ← inferType x
        if ty.isAppOfArity ``autoParam 2 then return ty.appArg!
    throwError "`#leanscript_ctor`: internal: no `by head_ok` to reuse"

/-- A spine of the terms `xs`, at the trees `tys`. -/
def mkSpineE (sg γ : Expr) (tys : List Expr) (xs : Array Expr) : MetaM Expr := do
  let mut sp ← LeanScript.ToTerm.buildNode ``LeanScript.Spine.nil #[sg, γ]
  let tysA := tys.toArray
  for i in [0:xs.size] do
    let j := xs.size - 1 - i
    sp := (← LeanScript.ToTerm.buildNode ``LeanScript.Spine.cons
      #[sg, γ, tysA[j]!, ← mkListLit tyWfE (tys.drop (j + 1)), xs[j]!, sp])
  return sp

/-- Does a constructor function of this shape build a constructor node, whose fields are
    operands and so must be atoms (`LeanScript.Head.isAtom`)? -/
def Shape.hasFields : Shape → Bool
  | .record _ | .union _ => true
  | _ => false

/-- The proof that the fields, of heads `ks`, are atoms (`LeanScript.Head.allAtom`), from a
    proof `hs[i]` that the head of field `i` is one. -/
def allAtomProof (ks hs : Array Expr) : MetaM Expr := do
  let headTy := Lean.mkConst ``LeanScript.Head
  let mut prf := Lean.mkConst ``LeanScript.Head.allAtom_nil
  let mut rest ← mkListLit headTy []
  for i in [0:ks.size] do
    let j := ks.size - 1 - i
    prf := mkAppN (Lean.mkConst ``LeanScript.Head.allAtom_cons) #[ks[j]!, rest, hs[j]!, prf]
    rest := mkApp3 (Lean.mkConst ``List.cons [0]) headTy ks[j]! rest
  return prf

/-- The body of the constructor function: the value of shape `shape` built as constructor
    `cidx` from the terms `xs`, of heads `ks`, at the trees `tys`; `hs` are the proofs that
    those heads are atoms. -/
def mkBody (sg γ : Expr) (shape : Shape) (cidx : Nat) (tys : Array Expr) (xs ks hs : Array Expr) :
    MetaM Expr := do
  match shape with
  | .newtype => return xs[0]!
  | .record sch =>
      return (← LeanScript.ToTerm.buildNode ``LeanScript.Term.record_mk
        #[sg, γ, sch, ← mkSpineE sg γ tys.toList xs] #[(`hAnf, ← allAtomProof ks hs)])
  | .union l =>
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyWfE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit cidx, lenE])
      return (← LeanScript.ToTerm.buildNode ``LeanScript.Term.taggedUnion_mk
        #[sg, γ, l, mkNatLit cidx, prf, ← mkSpineE sg γ tys.toList xs]
        #[(`hAnf, ← allAtomProof ks hs)])
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit cidx, nE])
      return (← LeanScript.ToTerm.buildNode ``LeanScript.Term.enum_mk
        #[sg, γ, s, mkAppN (mkConst ``Fin.mk) #[nE, mkNatLit cidx, prf]])
  | .bool =>
      return (← LeanScript.ToTerm.buildNode ``LeanScript.Term.bool_mk #[sg, γ, toExpr (cidx == 1)])

/-- The field names and the trees of the fields a constructor keeps, in the context `c`. -/
def translateFields (c : TrCtx) (xs : Array Expr) : MetaM (Array (Name × Expr)) := do
  let mut out := #[]
  for x in xs do
    let t := (← inferType x).replaceFVars (c.subst.map (·.1)) (c.subst.map (·.2))
    if ← erasedBinder t then continue
    let n ← x.fvarId!.getUserName
    if let some a ← trTy c n t then out := out.push (n, a)
  return out

/-- Declare a `TyWf` local for each type variable, named as it is. -/
def withTyVarHoles {α : Type} [Inhabited α] (vars : Array (Expr × Name)) (erased : Array Bool)
    (k : Array (Expr × Expr) → Array (Expr × Expr) → MetaM α) : MetaM α := do
  let isErased (i : Nat) : Bool := erased.getD i false
  let kept := (vars.zipIdx.filter fun (_, i) => !isErased i).map (·.1)
  let mut subst : Array (Expr × Expr) := #[]
  for (v, i) in vars.zipIdx do
    if isErased i then
      let .sort u ← whnf (← inferType v.1)
        | throwError "`#leanscript_ctor`: {v.1} is not a type"
      subst := subst.push (v.1, mkConst ``PUnit [u])
  let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    kept.map fun (_, n) => (n, .default, fun _ => pure tyWfE)
  withLocalDecls decls fun hs => k (kept.map (·.1) |>.zip hs) subst

/-- Generate the layout and the constructor function once the fields are translated:
    `holes` are the arguments, `shape`/`layout` the layout, `fields` the kept fields of the
    constructor. -/
def emit (cName fnKey layoutKey layoutOwner : Name) (layoutBase : Name) (sfx : String) (c : TrCtx)
    (tyVarHoles : Array Expr) (shape : Shape) (layout : Expr) (cidx : Nat)
    (fields : Array (Name × Expr)) : MetaM (Name × Name) := withHoles c do
  let holeIds := (← c.holes.get).map fun (_, _, id) => Expr.fvar id
  let holes := tyVarHoles ++ holeIds
  -- the layout, shared when it has been generated already
  let layoutName ← match ← cached? layoutKey "layout" with
    | some n => pure n
    | none => do
      let n ← declNameFor layoutOwner layoutBase ("leanScriptLayout" ++ sfx)
      if (← getEnv).contains n then
        throwError "`#leanscript_ctor`: `{n}` is already declared"
      addReducibleDef n (← mkForallFVars holes tyWfE) (← mkLambdaFVars holes layout)
      modifyEnv fun env => ctorFnExt.addEntry env { key := layoutKey, kind := "layout", decl := n }
      pure n
  let layoutC ← mkConstWithLevelParams layoutName
  let layoutApp := mkAppN layoutC holes
  unless ← isDefEq layoutApp layout do
    throwError "`#leanscript_ctor`: the cached layout `{layoutName}` does not match the \
      datatype any more"
  let fnName ← declNameFor layoutOwner cName ("leanScriptCtor" ++ sfx)
  if (← getEnv).contains fnName then
    throwError "`#leanscript_ctor`: `{fnName}` is already declared"
  withLocalDecl `Sg .implicit (mkConst ``LeanScript.Sig) fun sg =>
  withLocalDecl `Γ .implicit (mkConst ``LeanScript.Ctx) fun γ => do
    let usageTy := mkApp (Lean.mkConst ``LeanScript.Usage) γ
    let headTy := Lean.mkConst ``LeanScript.Head
    -- each field is a term of any grade vector and any head: both are implicit
    let idxDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      fields.foldl (init := #[]) fun acc (n, _) =>
        acc.push (n.appendAfter "_usage", .implicit, fun _ => pure usageTy)
          |>.push (n.appendAfter "_head", .implicit, fun _ => pure headTy)
    withLocalDecls idxDecls fun idx => do
    let decls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      fields.mapIdx fun i (n, τ) => (n, .default, fun _ =>
        pure (mkAppN (Lean.mkConst ``LeanScript.Term) #[sg, γ, idx[2 * i]!, τ, idx[2 * i + 1]!]))
    withLocalDecls decls fun xs => do
    -- each field is an operand of the constructor, so an atom (A-normal form): a proof of
    -- it per field, written by `head_ok` by default
    let ks := (List.range fields.size).toArray.map fun i => idx[2 * i + 1]!
    let autoE ← anfAutoParam
    let hDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      if shape.hasFields then
        fields.mapIdx fun i (n, _) => (n.appendAfter "_atom", .default, fun _ =>
          pure (mkApp2 (Lean.mkConst ``autoParam [levelZero])
            (mkApp3 (Lean.mkConst ``Eq [levelOne]) (Lean.mkConst ``Bool)
              (mkApp (Lean.mkConst ``LeanScript.Head.isAtom) ks[i]!) (Lean.mkConst ``Bool.true)) autoE))
      else #[]
    withLocalDecls hDecls fun hs => do
      let body ← mkBody sg γ shape cidx (fields.map (·.2)) xs ks hs
      let binders := #[sg, γ] ++ holes ++ idx ++ xs ++ hs
      -- the result is at the layout, with the grade vector and the head of the body
      let bodyTy ← instantiateMVars (← inferType body)
      let resTy := mkAppN (Lean.mkConst ``LeanScript.Term)
        #[sg, γ, bodyTy.getArg! 2, layoutApp, bodyTy.getArg! 4]
      addReducibleDef fnName (← mkForallFVars binders resTy)
        (← mkLambdaFVars binders body)
  modifyEnv fun env => ctorFnExt.addEntry env { key := fnKey, kind := "fn", decl := fnName }
  return (layoutName, fnName)

/-- The suffix of the names generated for a use at which the type variables marked in
    `erased` are erased types (`Unit`): `""` when none is, `_erased0110` otherwise. -/
def erasedSuffix (erased : Array Bool) : String :=
  if erased.any id then "_erased" ++ String.join (erased.toList.map fun b => if b then "1" else "0")
  else ""

/-- The cache key of a use of `key` at which the type variables marked in `erased` are
    erased. -/
def erasedKey (key : Name) (erased : Array Bool) : Name :=
  let sfx := erasedSuffix erased
  if sfx.isEmpty then key else Name.str key sfx

/-- The layout and the constructor function of the constructor `cName`, generated if they
    have not been.

    `erased` marks the type variables of the constructor function — the parameters of the
    datatype, then its type indices (a datatype without existentials) or the type fields of
    the constructor (one with existentials) — that are erased types (`Unit`) at this use.
    Such a type variable is not an argument of the function: the language has no `Unit` to
    pass.  It is `Unit` in the field types instead, so a field of that type is dropped and a
    binder of that type is dropped from a function field, as everywhere in the language.
    The functions generated for such a use are cached separately, with the suffix
    `erasedSuffix erased`. -/
def ensureCtorFn (cName : Name) (erased : Array Bool := #[]) : MetaM (Name × Name) := do
  let sfx := erasedSuffix erased
  if let some fn ← cached? (erasedKey cName erased) "fn" then
    if let some lay ← cached? (erasedKey cName erased) "layout" then return (lay, fn)
    let ci ← getConstInfoCtor cName
    if let some lay ← cached? (erasedKey ci.induct erased) "layout" then return (lay, fn)
  let ci ← getConstInfoCtor cName
  let ind ← getConstInfoInduct ci.induct
  if ← forallTelescopeReducing ind.type fun _ body => pure body.isProp then
    throwError "`#leanscript_ctor`: `{ind.name}` is a proposition, which carries no value"
  forallBoundedTelescope ind.type ind.numParams fun params indBody => do
    for p in params do
      let s ← whnf (← inferType p)
      unless s.isSort && s != .sort .zero do
        throwError "`#leanscript_ctor`: `{ind.name}` has the parameter `{p}`, which is not a \
          type; only datatypes whose parameters are all types have constructor functions"
    let enumOverride ← builtinModel ind params
    forallTelescopeReducing indBody fun idxs _ => do
      let typeIdx ← idxs.mapM fun x => do isTypeField (← inferType x)
      let cl ← classify ind params typeIdx
      let holesRef ← IO.mkRef #[]
      let paramVars ← params.mapM fun p => do return (p, (← p.fvarId!.getUserName).eraseMacroScopes)
      if cl.whole then
        let mut idxVars : Array (Expr × Name) := #[]
        for k in [0:idxs.size] do
          if typeIdx[k]! then
            let n ← match cl.idxNames[k]! with
              | some n => pure n
              | none => pure (← idxs[k]!.fvarId!.getUserName).eraseMacroScopes
            idxVars := idxVars.push (idxs[k]!, n)
        let vars := paramVars ++ idxVars
        withTyVarHoles vars erased fun tyVars subst => do
          let c : TrCtx := { members := ind.all.toArray, tyVars, holes := holesRef,
                             used := ← IO.mkRef (vars.map (·.2)), subst }
          let mut cls : Array (Array Expr) := #[]
          let mut mine : Array (Name × Expr) := #[]
          for j in [0:ind.ctors.length] do
            let d := ind.ctors[j]!
            let di ← getConstInfoCtor d
            let fs ← withCtorFields di params idxs cl.idxMaps[j]! fun xs => translateFields c xs
            cls := cls.push (fs.map (·.2))
            if d == cName then mine := fs
          let (shape, layout) ← withHoles c (wholeShape ind.name enumOverride cls)
          emit cName (erasedKey cName erased) (erasedKey ind.name erased) ind.name ind.name sfx c
            (tyVars.map (·.2)) shape layout ci.cidx mine
      else
        let di := ci
        withCtorFields di params #[] (cl.idxMaps[ci.cidx]!.map fun _ => none) fun xs => do
          let mut exVars : Array (Expr × Name) := #[]
          for x in xs do
            if ← isTypeField (← inferType x) then
              exVars := exVars.push (x, (← x.fvarId!.getUserName).eraseMacroScopes)
          let vars := paramVars ++ exVars
          withTyVarHoles vars erased fun tyVars subst => do
            let c : TrCtx := { members := ind.all.toArray, tyVars, holes := holesRef,
                               used := ← IO.mkRef (vars.map (·.2)), subst }
            let fs ← translateFields c xs
            let (shape, layout) ← withHoles c
              (singleShape m!"the constructor `{cName}`" (fs.map (·.2)))
            emit cName (erasedKey cName erased) (erasedKey cName erased) ind.name cName sfx c
              (tyVars.map (·.2)) shape layout ci.cidx fs

end LeanScript.CtorFn

end

end
