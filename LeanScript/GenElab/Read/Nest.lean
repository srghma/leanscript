module

public import LeanScript.GenElab.Read.Base

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Reading Lean types: families indexed by a type (`Nest : Type → Type 1`)

A family whose index is a *type* recurses at other indices (`Nest.cons : α → Nest (α × α) →
Nest α`): its instances `Nest Nat`, `Nest (Nat × Nat)`, … are infinitely many, so they cannot
each be a member of a (finite) block.  Like the value indices of `Vec α n`, the type index is
erased, but through an *element type* that holds a value of every index reached:

```
inductive Nest.Elem (α : Type) : Type where
  | leaf : α → Nest.Elem α
  | node : Nest.Elem α → Nest.Elem α → Nest.Elem α   -- from the index `α × α`
```

generated once (`ensureElem`), with one `node` per recursive index `σ(α) ≠ α` (a structure
`σ(α)`, such as `α × α`, is flattened into its fields).  `Nest τ` is then read as the
datatype `Nest (Nest.Elem B)`, where the *base* `B` is `τ` with the recursive indices peeled
off (`canonIndex`: `Nat × Nat` peels to `Nat`), and a field of type `α` holds an
`Nest.Elem B`: `Nest Nat` is `nil | cons (Nest.Elem Nat) Nest`, a list whose `k`-th element is
a tree (in Lean, a perfect tree of depth `k`).  A family whose type index only recurses at
itself needs no element type: `F τ` is read with `α := τ`.
-/

open Lean Meta Elab

namespace LeanScript.Gen

/-- Is the inductive a family with an index that is a type? -/
def typeIndexed (info : InductiveVal) : MetaM Bool := do
  if info.numIndices == 0 then return false
  forallTelescopeReducing info.type fun xs _ =>
    xs[info.numParams:].toArray.anyM fun x => return (← whnf (← inferType x)).isSort

/-- The applications of the constant `c` to `arity` arguments inside `e`. -/
partial def appsOf (c : Name) (arity : Nat) (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.getAppFn.isConstOf c && e.getAppNumArgs == arity then acc.push e else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The position, among the fields of a constructor of a type-indexed family, of the field
    that its result's index is (`α` in `Nest.cons {α} a r : Nest α`). -/
def indexField (info : InductiveVal) (ctor : Name) : MetaM Nat := do
  let cinfo ← getConstInfoCtor ctor
  forallTelescopeReducing cinfo.type fun xs res => do
    let idx := (← whnf res).getAppArgs[info.numParams]!
    let some p := xs[info.numParams:].toArray.idxOf? idx
      | throwError m!"LeanScript: the constructor `{ctor}` of the type-indexed family \
          `{info.name}` builds a value at the index{indentExpr idx}\nwhich is not a variable: \
          only families whose constructors are generic in the index are supported"
    return p

/-- A type-indexed family, checked (one index, of type `Type`, no universe parameters, every
    constructor generic in the index), and the indices `fun ps α => σ` at which it recurses
    (`fun α => α × α` for `Nest`). -/
def typeFamilySteps (info : InductiveVal) : MetaM (Array Expr) := do
  let bad {α : Type} (why : MessageData) : MetaM α :=
    throwError m!"LeanScript: the family `{info.name}` is indexed by a type, and {why}"
  unless info.levelParams.isEmpty do bad m!"is universe polymorphic"
  unless info.numIndices == 1 do bad m!"has {info.numIndices} indices: only one type index is \
    supported"
  forallTelescopeReducing info.type fun xs _ => do
    unless ← isDefEq (← inferType xs[info.numParams]!) (mkSort Level.one) do
      bad m!"its index is not a `Type`"
  let mut steps : Array Expr := #[]
  for ctor in info.ctors do
    let p ← indexField info ctor
    let cinfo ← getConstInfoCtor ctor
    steps ← forallTelescopeReducing cinfo.type fun xs _ => do
      let ps := xs[:info.numParams].toArray
      let a := xs[info.numParams + p]!
      let mut steps := steps
      for x in xs[info.numParams:] do
        if x == a then continue
        for occ in appsOf info.name (info.numParams + 1) (← instantiateMVars (← inferType x)) do
          let σ := occ.getAppArgs[info.numParams]!
          if σ == a || !σ.containsFVar a.fvarId! then continue
          if σ.hasLooseBVars || (appsOf info.name (info.numParams + 1) σ).size > 0 ||
              xs.any (fun y => y != a && !ps.contains y && σ.containsFVar y.fvarId!) then
            bad m!"the constructor `{ctor}` recurses at the index{indentExpr σ}\nwhich is not a \
              type built from the index alone"
          let st ← mkLambdaFVars (ps.push a) σ
          unless steps.contains st do steps := steps.push st
      return steps
  return steps

/-- The fields of a constructor of the element type for the recursive index `s` (a type
    mentioning the local `α`): the fields of `s` when it is a structure (`α × α` gives `α`
    and `α`), with the structure's name; otherwise `s` itself. -/
def stepFields (s : Expr) : MetaM (Option Name × Array Expr) := do
  let s ← whnf s
  let some (c, us) := s.getAppFn.const? | return (none, #[s])
  unless isStructure (← getEnv) c do return (none, #[s])
  let info ← getConstInfoInduct c
  unless info.numIndices == 0 && !info.isRec && s.getAppNumArgs == info.numParams do
    return (none, #[s])
  let cinfo ← getConstInfoCtor info.ctors[0]!
  let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) s.getAppArgs
  forallTelescopeReducing ty fun ys _ => do
    let mut out := #[]
    for y in ys do
      let d ← y.fvarId!.getDecl
      if (← isProp d.type) || d.binderInfo.isInstImplicit ||
          ys.any (d.type.containsFVar ·.fvarId!) then
        return (none, #[s])
      out := out.push d.type
    return if out.isEmpty then (none, #[s]) else (some c, out)

/-- The name of the element type of a type-indexed family. -/
def elemName (info : InductiveVal) : Name := info.name ++ `Elem

/-- The element type of a type-indexed family with the recursive indices `steps` (non-empty),
    declared if it does not exist yet: `leaf : α → Elem α` and one `node` (`node0`, `node1`,
    … when there are several) per recursive index. -/
def ensureElem (info : InductiveVal) (steps : Array Expr) : MetaM Name := do
  let n := elemName info
  if let some c := (← getEnv).find? n then
    unless c matches .inductInfo _ do
      throwError m!"LeanScript: `{n}` is already declared, and is not the element type of the \
        type-indexed family `{info.name}`"
    return n
  let decl ← forallBoundedTelescope info.type info.numParams fun ps _ => do
    withLocalDeclD `α (mkSort Level.one) fun α => do
      let self := mkAppN (mkConst n) (ps.push α)
      let leaf : Constructor :=
        { name := n ++ `leaf, type := ← mkForallFVars (ps.push α) (← mkArrow α self) }
      let mut ctors := #[leaf]
      for k in [0:steps.size] do
        let (_, fs) ← stepFields ((steps[k]!).beta (ps.push α))
        let mut ty := self
        for f in fs.reverse do ty ← mkArrow (f.replaceFVar α self) ty
        let nm := if steps.size = 1 then `node else .mkSimple s!"node{k}"
        ctors := ctors.push { name := n ++ nm, type := ← mkForallFVars (ps.push α) ty }
      let ty ← mkForallFVars ps (.forallE `α (mkSort Level.one) (mkSort Level.one) .default)
      -- the parameters of the constructors are implicit, as in a declared `inductive`
      let rec implicit : Nat → Expr → Expr
        | k + 1, .forallE x d b _ => .forallE x d (implicit k b) .implicit
        | _, e => e
      let cs := ctors.map fun c => { c with type := implicit (info.numParams + 1) c.type }
      return Declaration.inductDecl [] (info.numParams + 1)
        [{ name := n, type := ty, ctors := cs.toList }] false
  try addDecl decl
  catch e => throwError m!"LeanScript: the element type `{n}` of the type-indexed family \
    `{info.name}` is not a valid inductive type: {e.toMessageData}"
  compileDecls #[n]
  mkCasesOn n
  return n

/-- One peeling step: `τ` is the recursive index `st` at `σ`. -/
def matchStep (ps : Array Expr) (st τ : Expr) : MetaM (Option Expr) :=
  withNewMCtxDepth do
    let m ← mkFreshExprMVar (mkSort Level.one)
    unless ← withReducible (isDefEq τ (st.beta (ps.push m))) do return none
    let r ← instantiateMVars m
    return if r.hasMVar then none else some r

/-- The index of the datatype that `I ps τ` is read as: `Elem ps B`, where `B` is `τ` with the
    recursive indices peeled off (`Nat × Nat` peels to `Nat`), or `τ` itself when the family
    recurses only at its index. -/
def canonIndex (info : InductiveVal) (ps : Array Expr) (τ : Expr) : MetaM Expr := do
  let steps ← typeFamilySteps info
  if steps.isEmpty then return τ
  let n ← ensureElem info steps
  let mut τ := τ
  for _ in [0:10000] do
    if τ.isAppOf n then return τ
    let mut next := none
    for st in steps do
      if let some σ ← matchStep ps st τ then
        next := some σ
        break
    let some σ := next | break
    τ := σ
  return mkAppN (mkConst n) (ps.push τ)

/-- For a value `a : τ` of a field of type `α` at the index `τ` of a type-indexed family whose
    datatype has the index `Elem ps B`: the same value in `Elem ps B` (`(2, 3)` at `Nat × Nat`
    is `node (leaf 2) (leaf 3)` over `Nat`), as a Lean expression. -/
partial def injectElem (info : InductiveVal) (ps : Array Expr) (τ a : Expr) : MetaM Expr := do
  let steps ← typeFamilySteps info
  if steps.isEmpty then return a
  let n ← ensureElem info steps
  if (← whnf τ).isAppOf n then return a
  for k in [0:steps.size] do
    let st := steps[k]!
    let some σ ← matchStep ps st τ | continue
    let nm := if steps.size = 1 then `node else .mkSimple s!"node{k}"
    let node := mkAppN (mkConst (n ++ nm)) (ps.push (← canonIndex info ps σ).appArg!)
    -- the fields as `stepFields` splits them: `some true` for a field of type `α` (injected
    -- in turn), `some false` for one that does not mention `α`
    let (str?, kinds) ← withLocalDeclD `α (mkSort Level.one) fun α => do
      let (str?, fs) ← stepFields (st.beta (ps.push α))
      return (str?, fs.map fun f => if f == α then some true
        else if f.containsFVar α.fvarId! then none else some false)
    let vals ← match str? with
      | none => pure #[a]
      | some c =>
        let ctor := getStructureCtor (← getEnv) c
        let a' ← whnfR a
        if a'.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) then
          pure a'.getAppArgs[ctor.numParams:].toArray
        else pure ((List.range kinds.size).toArray.map fun j => mkProj c j a)
    let mut args := #[]
    for j in [0:kinds.size] do
      match kinds[j]! with
      | some true => args := args.push (← injectElem info ps σ vals[j]!)
      | some false => args := args.push vals[j]!
      | none =>
        throwError m!"LeanScript: the value{indentExpr a}\nat the index{indentExpr τ}\nof \
          `{info.name}` cannot be put in `{n}`: the index `{st}` holds the index other than \
          as a field of its own"
    return mkAppN node args
  return mkAppN (mkConst (n ++ `leaf)) (ps.push τ |>.push a)

end LeanScript.Gen

end
