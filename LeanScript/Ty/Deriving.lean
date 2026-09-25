module

public meta import Lean.Elab.Deriving.Basic
public meta import LeanScript.Ty.Deriving.Translate

@[expose] public section

meta section

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

/-!
# `deriving LeanScriptTyWf`

```lean
inductive Tree (α : Type) where
  | leaf
  | node : Tree α → α → Tree α → Tree α
  deriving LeanScriptTyWf
```

The handler reads the declaration, builds the tree that models it, and adds three
declarations:

| name | what it is |
| :-- | :-- |
| `Tree.leanScriptTyOf` | the tree, as a `def` |
| `Tree.leanScriptTyOf_wf` | a `theorem` that it is a type (`LeanScript.Ty.Wf`) |
| `Tree.instLeanScriptTyWf` | the instance, which is those two |

## It only translates the declaration itself

A field whose type is **not** the declaration being derived is not read at all: the
handler asks for a `LeanScriptTyWf` instance for it and uses `tyWfOf` of that instance as the
leaf.  So `deriving LeanScriptTyWf` on a type with a `List Foo` field works exactly when
`Foo` has an instance already, and fails with a message naming `Foo` when it does not.

Three things follow.

* **Nothing is translated twice.**  The tree of `Foo` is not copied into the tree of the
  type that mentions it; the leaf is the constant `Foo.leanScriptTyOf`, behind `Foo`'s
  instance.
* **Nothing is *checked* twice.**  The `theorem` is proved by `LeanScript.Ty.mkWfIn`,
  which closes such a leaf with `Foo`'s own `isWf`.  The work at a declaration is the
  size of its own constructors, whatever its fields' types contain.
* **A type has one model.**  `Ordering` is modelled by its instance, shift and all
  (`LeanScript.Ty.Instances`), so a declaration with an `Ordering` field gets that model
  rather than a second, mechanically derived one.

## What it does with a type it cannot ask an instance for

Two cases, because two kinds of field mention something no instance can answer for.

* **A field whose type mentions the declaration being defined**, such as `Option T`.  The
  tree is the *former's own* model — read off `Option`'s instance — with the occurrence in
  the place of the argument's tree.  `Option`, `×`, `⊕`, `Array`, `Thunk`, `→` and any
  non-recursive wrapper are handled this way.  When the former's model is itself a binder,
  as `List`'s is, the occurrence would land inside that binder and denote the list, so the
  binder is **hoisted** into one more member of a mutual family instead — the nested
  recursion becomes a mutual one, which is what Lean itself does with a nested inductive.
  So `inductive RoseList | node : List RoseList → RoseList` has a tree, and it is the
  family `member 0 = member 1`, `member 1 = nil | cons (member 0) (member 1)`.  See the
  section on hoisting below.
* **A field whose type is a *type*** — `State : Type` in a stream representation, or any
  field whose type ends in `Type`.  Such a declaration hides a type from the language: a
  value of it carries values of a type the model does not name.  The handler refuses the
  declaration as a whole, naming the field — *existential typing is not yet supported* —
  rather than modelling it.  What does work is the parameterised declaration: take the
  hidden type as a parameter of the declaration, and each *choice* of it is a type the
  language has.  A type field that **no value depends on** hides nothing and is erased: the
  `α` of `pair {α β} (a : TExpr α) (b : TExpr β) : TExpr (α × β)` in a family indexed by
  types appears only in indices, which the language erases (`existentialField?`).

## The same tree is stored once

Before adding anything the handler looks the tree up in a table of the trees this project
has already built — the table is an environment extension, so it spans modules.  Two
declarations with the same tree (two `mutual` families that differ only in their names,
say) share one `…leanScriptTyOf` constant and one proof: the second declaration adds an
instance and nothing else.
-/

/-! ## The handler -/

/-- The universe parameters a declaration's type and value use. -/
def usedLevels (type value : Expr) : List Name :=
  (collectLevelParams (collectLevelParams {} type) value).params.toList

/-- Make the first `k` binders of a `∀`/`fun` implicit, and the `m` binders from position
    `from_` on as well (the indices of an indexed family, after its instances). -/
def setImplicitRange (k from_ m : Nat) (e : Expr) : Expr :=
  let rec go (i : Nat) (e : Expr) : Expr :=
    match e with
    | .forallE nm t b bi =>
        let bi' := if i < k || (from_ ≤ i && i < from_ + m) then .implicit else bi
        .forallE nm t (go (i + 1) b) bi'
    | .lam nm t b bi =>
        let bi' := if i < k || (from_ ≤ i && i < from_ + m) then .implicit else bi
        .lam nm t (go (i + 1) b) bi'
    | e => e
  go 0 e

/-- Make the first `k` binders of a `∀`/`fun` implicit, which is what an instance's own
    type parameters are. -/
partial def setImplicit (k : Nat) (e : Expr) : Expr :=
  match k, e with
  | 0, e => e
  | k + 1, .forallE nm t b _ => .forallE nm t (setImplicit k b) .implicit
  | k + 1, .lam nm t b _ => .lam nm t (setImplicit k b) .implicit
  | _, e => e

/-- For a nested inductive block, whose tree is a family with a member for each auxiliary
    type whose own model is a binder (`List T`, any recursive wrapper), the instance of
    each such auxiliary type: the same family, **selecting that member**.  So `List T` is
    a type of the language that *is* the member its values are stored as, and a function
    on `List T` is a function on that member.  The auxiliary types of non-recursive
    wrappers (`Option T`) are members, and get instances, only when the block is a family
    anyway (a `mutual` block, or one nested through `List`); otherwise the occurrence
    stands inside the wrapper's shape and they get none. -/
def mkNestedAuxInstances (n : Name) (ind : InductiveVal) (params binders : Array Expr)
    (tree : Expr) :
    TermElabM Unit := do
  let auxs ← nestedAuxTypes ind params
  if auxs.isEmpty then return
  let t ← whnfD tree
  let (``LeanScript.Ty.mutualRecursiveFamily, #[fam]) := t.getAppFnArgs | return
  let members ← whnfD (mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.members) tyE fam)
  let some ms := members.listLit? | return
  -- the auxiliary types that are members, in order, after the declared members
  let mut hoisted : Array Expr := #[]
  for d in auxs do
    let .const h _ := d.getAppFn | return
    let some (.inductInfo hi) := (← getEnv).find? h | return
    if hi.isRec then hoisted := hoisted.push d
  -- every auxiliary type is a member when one of them is a non-recursive wrapper inside a
  -- family (`Option Q` inside `P`, see `LeanScript.Deriving.hoistAux`)
  if ms.2.length == ind.all.length + auxs.size then hoisted := auxs
  unless ms.2.length == ind.all.length + hoisted.size do return
  for h : j in [0:hoisted.size] do
    let d := hoisted[j]
    let k := ind.all.length + j
    -- the same members, selecting member `k`
    let msA := ms.2.toArray
    let schemaTy := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) tyE
    let listOf (xs : Array Expr) : MetaM Expr := mkListLit schemaTy xs.toList
    let famK ← if k + 1 < msA.size then
        pure (mkAppN (mkConst ``LeanScript.LeanMutualRecFamily.selectedThenMore)
          #[tyE, ← listOf (msA.extract 0 k), msA[k]!, msA[k + 1]!,
            ← listOf (msA.extract (k + 2) msA.size)])
      else
        pure (mkAppN (mkConst ``LeanScript.LeanMutualRecFamily.selectedLast)
          #[tyE, msA[0]!, ← listOf (msA.extract 1 k), msA[k]!])
    let sel := mkApp (mkConst ``LeanScript.Ty.mutualRecursiveFamily) famK
    let defValue ← mkLambdaFVars binders sel
    let defType ← mkForallFVars binders tyE
    let declName := n ++ Name.mkSimple s!"leanScriptTyOfNested{k}"
    let wfName := n ++ Name.mkSimple s!"leanScriptTyOfNested{k}_wf"
    let lvls := usedLevels defType defValue
    addAndCompile (.defnDecl
      { name := declName, levelParams := lvls, type := defType, value := defValue,
        hints := .abbrev, safety := .safe })
    let app := mkAppN (mkConst declName (lvls.map .param)) binders
    let wfProof ←
      try LeanScript.Ty.mkWfIn 0 app
      catch e => throwError "the auxiliary type `{d}` of `{n}` has no `Ty`: {e.toMessageData}"
    let wfValue ← mkLambdaFVars binders wfProof
    let wfType ← mkForallFVars binders
      (mkApp2 (mkConst ``LeanScript.Ty.WfIn) (mkNatLit 0) app)
    addDecl (.thmDecl
      { name := wfName, levelParams := usedLevels wfType wfValue, type := wfType,
        value := wfValue })
    let dlvls := ((← getEnv).find? declName).get!.levelParams.map Level.param
    let wlvls := ((← getEnv).find? wfName).get!.levelParams.map Level.param
    let bundle ← mkAppOptM ``LeanScript.TyWf.mk
      #[some (mkAppN (mkConst declName dlvls) binders),
        some (mkAppN (mkConst wfName wlvls) binders)]
    let instValue ← mkLambdaFVars binders (← mkAppOptM ``LeanScript.LeanScriptTyWf.mk
      #[some d, some bundle])
    let instType ← mkForallFVars binders (← mkAppM ``LeanScript.LeanScriptTyWf #[d])
    let instName := n ++ Name.mkSimple s!"instLeanScriptTyWfNested{k}"
    let nP := params.size
    let instType := setImplicit nP instType
    let instValue := setImplicit nP instValue
    addAndCompile (.defnDecl
      { name := instName, levelParams := usedLevels instType instValue, type := instType,
        value := instValue, hints := .abbrev, safety := .safe })
    setReducibleAttribute instName
    -- above the generic instance of the wrapper (`List α`), which would give the list
    -- of them its own tree rather than the member
    addInstance instName .global (eval_prio high)

/-- Add the instance for the declaration `n`: its tree, the proof that the tree is a
    type, and the instance holding them.  The tree and the proof are shared with any
    declaration that already has the same tree. -/
def mkInstanceFor (n : Name) : TermElabM Unit := do
  let some (.inductInfo ind) := (← getEnv).find? n
    | throwError "`{n}` is not an inductive declaration, so it has no `Ty`"
  -- an indexed family (`Vec α n`) has one tree for every index: the indices are erased,
  -- and a constructor's value index (`{n : Nat}` of `Vec.cons`) is an ordinary field
  if ← forallTelescopeReducing ind.type fun _ body => pure (body == .sort .zero) then
    throwError "the type `{n}` carries no value, so it has no `Ty`"
  forallBoundedTelescope ind.type ind.numParams fun params _ => do
    if let some f ← existentialField? n params then
      throwError "the type `{n}` has no `Ty`: existential typing is not yet supported, \
        `{f}` is an existential"
    for p in params do
      let s ← whnf (← inferType p)
      unless s.isSort && s != .sort .zero do
        throwError "`{n}` has the parameter `{p}`, which is not a type; this handler \
          derives instances for declarations whose parameters are all types"
    let instDecls := params.zipIdx.map fun (p, i) =>
      (Name.mkSimple s!"inst{i}", BinderInfo.instImplicit,
        fun (_ : Array Expr) => mkAppM ``LeanScript.LeanScriptTyWf #[p])
    withLocalDecls instDecls fun insts => do
      let binders := params ++ insts
      -- the indices of an indexed family, bound after the instances: the tree does not
      -- mention them, and the instance is for every index
      let idxTys ← instantiateForall ind.type params
      forallBoundedTelescope idxTys ind.numIndices fun indices _ => do
      let tree ← match ← treeOfDecl n ind params with
        | .ok t => pure t
        | .erased => throwError "the type `{n}` carries no value, so it has no `Ty`"
        | .no r => throwError "the type `{n}` has no `Ty`: {r}"
      let defValue ← mkLambdaFVars binders tree
      let defType ← mkForallFVars binders tyE
      -- the same tree, if some declaration already has it
      let (declName, wfName) ←
        match ← findShared? defValue with
        | some names => pure names
        | none => do
          let declName := n ++ `leanScriptTyOf
          let wfName := n ++ `leanScriptTyOf_wf
          let lvls := usedLevels defType defValue
          addAndCompile (.defnDecl
            { name := declName, levelParams := lvls, type := defType, value := defValue,
              hints := .abbrev, safety := .safe })
          let app := mkAppN (mkConst declName (lvls.map .param)) binders
          -- the conditions that are about the *whole* tree rather than about one node —
          -- that the declaration has values, and that it occurs positively — are the
          -- ones this proof discovers, so its failure is a failure to derive
          let wfProof ←
            try LeanScript.Ty.mkWfIn 0 app
            catch e => throwError "the type `{n}` has no `Ty`: {e.toMessageData}"
          let wfValue ← mkLambdaFVars binders wfProof
          let wfType ← mkForallFVars binders
            (mkApp2 (mkConst ``LeanScript.Ty.WfIn) (mkNatLit 0) app)
          addDecl (.thmDecl
            { name := wfName, levelParams := usedLevels wfType wfValue, type := wfType,
              value := wfValue })
          modifyEnv fun env =>
            sharedTyExt.addEntry env { hash := defValue.hash, declName, wfName }
          pure (declName, wfName)
      -- the instance itself
      let dlvls := ((← getEnv).find? declName).get!.levelParams.map Level.param
      let wlvls := ((← getEnv).find? wfName).get!.levelParams.map Level.param
      let theType := mkAppN (mkConst n (ind.levelParams.map Level.param)) (params ++ indices)
      let bundle ← mkAppOptM ``LeanScript.TyWf.mk
        #[some (mkAppN (mkConst declName dlvls) binders),
          some (mkAppN (mkConst wfName wlvls) binders)]
      let instValue ← mkLambdaFVars (binders ++ indices)
        (← mkAppOptM ``LeanScript.LeanScriptTyWf.mk #[some theType, some bundle])
      let instType ← mkForallFVars (binders ++ indices)
        (← mkAppM ``LeanScript.LeanScriptTyWf #[theType])
      let instName := n ++ `instLeanScriptTyWf
      -- the parameters, and the indices after the instances, are implicit
      let instType := setImplicitRange params.size (binders.size) indices.size instType
      let instValue := setImplicitRange params.size (binders.size) indices.size instValue
      addAndCompile (.defnDecl
        { name := instName, levelParams := usedLevels instType instValue, type := instType,
          value := instValue, hints := .abbrev, safety := .safe })
      setReducibleAttribute instName
      addInstance instName .global (eval_prio default)
      -- a nested inductive: the auxiliary types Lean adds for it (`List T`) are members
      -- of the family too, and get instances selecting those members
      if n == ind.all.headD n then
        mkNestedAuxInstances n ind params binders (mkAppN (mkConst declName dlvls) binders)

/-! ## The `deriving` clause

`deriving LeanScriptTyWf` on a declaration, and `deriving instance LeanScriptTyWf for …`
after it, both add the instance of the declaration named.  A declaration the handler has
no model for is refused with the reason, which is the message `#guard_msgs` pins in the
tests. -/

/-- The handler `deriving LeanScriptTyWf` runs: one instance per declaration named. -/
def leanScriptTyWfHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    -- the tree, its proof and the instance are added with their bodies **exported**
    -- (unless the declaration itself is private): a `deriving instance … for` command
    -- runs outside the exporting scope of the declaration, and a tree whose body is not
    -- exported cannot be unfolded where it is used — in the body of an exposed
    -- definition of the same module, or in another module
    Command.liftTermElabM <| withExporting (isExporting := !isPrivateName n) <|
      mkInstanceFor n
  return true

initialize registerDerivingHandler ``LeanScript.LeanScriptTyWf leanScriptTyWfHandler

end LeanScript.Deriving

end

end
