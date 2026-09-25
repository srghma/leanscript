module

public meta import LeanScript.ToTerm.Trans

@[expose] public section

meta section

/-!
# Functions on a structure with an existential type field

```lean
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

def Unfold.take (u : Unfold α) (fuel : Nat) : List α := …
```

A value of `Unfold α` has no one tree of the language: the tree of its `seed` is the type
the value chose for `State`.  So `Unfold α` has no `LeanScriptTyWf` instance, and there are
two ways a function on it is translated.

* **Specialized to a value.**  A call on a value that is written out (`countdown.take n`,
  `(countFrom k).take n`) is specialized to it: the value is substituted into the function
  (`LeanScript.ToTerm.transSpecialized?`), so `u.State`, `u.seed` and `u.step` are the
  value's own, and the call is an ordinary term.  Such a function cannot be declared in the
  signature (it has no type), so it is specialized whether or not it is `@[inline]`.

* **Generic in the hidden type.**  A function whose argument *is* such a value
  (`#leanscript_to_term (Unfold.take (α := Nat))`) translates to a Lean function of the tree
  of the hidden type:

  ```lean
  fun (State : TyWf) => (… : Term Sg Γ (Unfold.mk.leanScriptLayout (.prim .nat) State ⇒ …))
  ```

  that is, a term **for every** choice of the hidden type — which is what a function out of an
  existential is (`(∃ S, P S) → R` is `∀ S, P S → R`).  The argument is the value built by the
  constructor function of `#leanscript_ctor` (`LeanScript.CtorFn`), its layout; the function
  takes its record apart (`record_casesOn`) and reads the fields as variables, with
  `u.State` the tree `State` (through `LeanScript.TyWf.Hidden`).  Applied to the tree a
  value chose (`f (.prim .nat)`), it is a term that can be applied to that value.

The generic translation is for the leading arguments of the definition translated, since
the tree is a Lean argument and not a value of the language: it stands outside every
`Term.lam`.  It covers a structure (one constructor, no index) with type fields; a datatype
whose existentials sit in several constructors (`Process`) or under its own recursion has
values only, through the constructor functions.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- A structure with an existential type field: one constructor, no index, not recursive, and a
    field that is a type.  The constructor, the arguments of the type, and the universe levels
    of the type. -/
def existentialStructure? (d : Expr) : MetaM (Option (ConstructorVal × Array Expr × List Level)) := do
  let d ← whnf d
  let .const ind lvls := d.getAppFn | return none
  let some (.inductInfo iv) := (← getEnv).find? ind | return none
  unless iv.ctors.length == 1 && iv.numIndices == 0 && !iv.isRec do return none
  let args := d.getAppArgs
  if (← LeanScript.Deriving.existentialField? ind args).isNone then return none
  let ci ← getConstInfoCtor iv.ctors[0]!
  return some (ci, args, lvls)

/-- The universe of a type field: `u` for a field of type `Sort (u + 1)`. -/
def typeFieldLevel? (t : Expr) : MetaM (Option Level) := do
  match ← whnf t with
  | .sort (.succ u) => return some u
  | _ => return none

/-- The type fields of the constructor of an existential structure, instantiated at the
    arguments of the type: their names. -/
def existentialTypeFields (ci : ConstructorVal) (params : Array Expr) : MetaM (Array Name) := do
  let cty ← instantiateForall ci.type (params.extract 0 ci.numParams)
  forallTelescopeReducing cty fun xs _ => do
    let mut out := #[]
    for x in xs do
      if (← typeFieldLevel? (← inferType x)).isSome then
        out := out.push (← x.fvarId!.getUserName)
    return out

/-- The names of the hidden types of the leading arguments of `val` that are existential
    structures, in order. -/
def hiddenTypeNames (val : Expr) : MetaM (Array Name) :=
  lambdaTelescope val fun xs _ => do
    let mut out := #[]
    for x in xs do
      if let some (ci, params, _) ← existentialStructure? (← inferType x) then
        out := out ++ (← existentialTypeFields ci params)
    return out

/-- The value `ctor params fields` whose type fields are the Lean types standing for the trees
    `hidden` (`TyWf.Hidden`) and whose other fields are fresh variables; `k` is given the
    value, the variables of the fields that carry a value of the language (in order), and what
    is left of `hidden`. -/
partial def withGenericValue {α : Type} (ci : ConstructorVal) (params : Array Expr)
    (lvls : List Level) (hidden : List Expr)
    (k : Expr → Array Expr → List Expr → MetaM α) : MetaM α := do
  let cty ← instantiateForall (ci.type.instantiateLevelParams ci.levelParams lvls)
    (params.extract 0 ci.numParams)
  let rec go (ty : Expr) (vals kept : Array Expr) (hidden : List Expr) : MetaM α := do
    match ← whnf ty with
    | .forallE n d b bi =>
        if let some u ← typeFieldLevel? d then
          let some S := hidden.head?
            | throwError "`#leanscript_to_term`: internal: no tree for the hidden type `{n}`"
          let v := mkApp (mkConst ``LeanScript.TyWf.Hidden [u]) S
          go (b.instantiate1 v) (vals.push v) kept hidden.tail
        else
          withLocalDecl n bi d fun x => do
            let kept ← if ← LeanScript.Deriving.erasedBinder d then pure kept
              else pure (kept.push x)
            go (b.instantiate1 x) (vals.push x) kept hidden
    | _ =>
        k (mkAppN (mkConst ci.name lvls) (params.extract 0 ci.numParams ++ vals)) kept hidden
  go cty #[] #[] hidden

/-- The tree of a value of an existential structure whose kept fields have the trees
    `keptTys`: the record of those trees (the one tree, for one field) — which is the layout
    of its constructor function (`#leanscript_layout`), and is written as that layout when the
    two are the same. -/
def layoutOf (c : TCtx) (ci : ConstructorVal) (args : Array Expr) (keptTys : Array Expr) :
    MetaM Expr := do
  let mine ← match keptTys.toList with
    | [t] => pure t
    | a :: b :: rest => do
        let elem := tyWfTyE
        let restE := rest.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem x acc)
          (mkApp (mkConst ``List.nil [Level.zero]) elem)
        pure (mkApp (mkConst ``LeanScript.TyWf.record)
          (mkApp4 (mkConst ``LeanScript.LeanRecordSchema.mk) elem a b restE))
    | [] => throwError "`#leanscript_to_term`: a value of `{ci.induct}` carries no value of \
        the language"
  let layout? ← try
      let vals ← LeanScript.CtorFn.tyVarValues ci args
      let erased ← vals.mapM LeanScript.Deriving.erasedBinder
      let (_, fnName) ← LeanScript.CtorFn.ensureCtorFn ci.name erased
      let kept := (vals.zip erased).filterMap fun (v, er) => if er then none else some v
      let fnC ← mkConstWithFreshMVarLevels fnName
      let mut ty ← instantiateForall (← inferType fnC) #[c.sg, c.gamma]
      for v in kept do
        let .forallE _ _ b _ := ty | failure
        ty := b.instantiate1 (← tyWfOfType v)
      repeat
        let .forallE _ d b _ := ty | break
        if d.isConstOf ``LeanScript.TyWf then
          ty := b.instantiate1 (← mkFreshExprMVar tyWfTyE)
        else
          if b.hasLooseBVars then failure
          ty := b
      let (`LeanScript.Term, #[_, _, resTy]) := ty.getAppFnArgs | failure
      if ← isDefEq resTy mine then
        let resTy ← instantiateMVars resTy
        pure (if resTy.hasExprMVar then none else some resTy)
      else pure none
    catch _ => pure none
  return layout?.getD mine

/-- `Term.lam`, of the tree `σ`, around the body `b` of the tree `τ`. -/
def mkLamE (c : TCtx) (σ τ b : Expr) : Expr :=
  mkAppN (mkConst `LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

/-- The translation of `e`, whose leading arguments that are existential structures read the
    trees `hidden` for their hidden types. -/
partial def transGenericLams (c : TCtx) (e : Expr) (hidden : List Expr) : MetaM Expr := do
  match e.consumeMData with
  | .lam n d b bi =>
      if let some (ci, params, lvls) ← existentialStructure? d then
        return ← withGenericValue ci params lvls hidden fun u kept hidden => do
          -- the tree of the argument: the layout of the constructor function, read off the
          -- constructor applied to the fields as variables
          let keptTys ← kept.mapM fun x => do tyOfTerm x
          let σ ← layoutOf c ci (params.extract 0 ci.numParams ++ u.getAppArgs.extract
            ci.numParams u.getAppArgs.size) keptTys
          let body := b.instantiate1 u
          if kept.size == 1 then
            let c1 := c.push kept[0]!.fvarId! σ
            let t ← transGenericLams c1 body hidden
            return mkLamE c σ (← termTyOf t) t
          let .record fs ← tyView σ
            | throwError "`#leanscript_to_term`: the value of `{d}` is not a record of the \
                language"
          let fieldTys ← recordFieldTys fs
          unless fieldTys.length == kept.size do
            throwError "`#leanscript_to_term`: internal: the layout of `{d}` has \
              {fieldTys.length} fields, not {kept.size}"
          let whole ← mkFreshFVarId
          let c1 := c.push whole σ
          let c2 := c1.pushFields (kept.map (·.fvarId!) |>.zip fieldTys.toArray)
          let t ← transGenericLams c2 body hidden
          let τ ← termTyOf t
          let cases := mkAppN (mkConst `LeanScript.Term.record_casesOn)
            #[c1.sg, c1.gamma, τ, fs, ← c1.var whole, t]
          return mkLamE c σ τ cases
      if ← LeanScript.Deriving.erasedBinder d then
        return ← withLocalDecl n bi d fun x => transGenericLams c (b.instantiate1 x) hidden
      let σ ← tyOfType d
      withLocalDecl n bi d fun x => do
        let t ← transGenericLams (c.push x.fvarId! σ) (b.instantiate1 x) hidden
        return mkLamE c σ (← termTyOf t) t
  | e => trans c e

/-- The translation of a definition some of whose leading arguments are existential
    structures: the Lean function, of the trees of their hidden types, whose value is the term
    of the definition at those trees.  `none` when no leading argument is one. -/
def translateGeneric? (c : TCtx) (val : Expr) : MetaM (Option Expr) := do
  let names ← hiddenTypeNames val
  if names.isEmpty then return none
  let decls := names.map fun n => (n, fun _ => pure tyWfTyE)
  withLocalDeclsD decls fun Ss => do
    let t ← transGenericLams c val Ss.toList
    return some (← mkLambdaFVars Ss (← instantiateMVars t))

end LeanScript.ToTerm

end

end
