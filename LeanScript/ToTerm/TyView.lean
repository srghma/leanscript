module

public meta import LeanScript.ToTerm.ObjectExpr

@[expose] public section

meta section

/-!
# A tree as a view, and the tree of a Lean type

`TyView` is one node of a reduced tree of the language with its children bundled, and
`treeOfType` is the tree of the language that models a given Lean type.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The shapes of a tree, as a view -/

/-- One node of a reduced tree of the language, with its children. -/
inductive TyView where
  /-- A terminal type, with its `LeanScript.LeanPrimTy`. -/
  | prim (p : Expr)
  /-- A function type. -/
  | fn (a b : Expr)
  /-- An array. -/
  | array (a : Expr)
  /-- A memoised delay. -/
  | thunk (a : Expr)
  /-- An unmemoised delay. -/
  | lazy (a : Expr)
  /-- An enum, with its schema. -/
  | enum (s : Expr)
  /-- A record, with its schema. -/
  | record (fs : Expr)
  /-- A tagged union, with its schema. -/
  | taggedUnion (l : Expr)
  /-- A **recursive** tagged union, with its payload — a schema of `TyWfIn 1`, the
      shape of `List α` — and the proof that the binder is a type. -/
  | recTaggedUnion (l hwf : Expr)
  /-- Anything else — another recursive binder or an occurrence. -/
  | other
  deriving BEq, Repr

/-- The node a type of the language is, with the children **bundled**: what the view
    hands back is what the grammar's constructors ask for. -/
def tyView (τ : Expr) : MetaM TyView := do
  let t ← treeOfTyE τ
  match t.getAppFnArgs with
  | (``LeanScript.Ty.shape, #[s]) =>
    match s.getAppFnArgs with
    | (``LeanScript.TyShape.prim, #[_, p]) => return .prim p
    | (``LeanScript.TyShape.fn, #[_, a, b]) =>
        return .fn (← bundleTyE 0 a) (← bundleTyE 0 b)
    | (``LeanScript.TyShape.enum, #[_, e]) => return .enum e
    | (``LeanScript.TyShape.record, #[_, fs]) => return .record (← bundleRecordE 0 fs)
    | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
        return .taggedUnion (← bundleTUE 0 l)
    | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      match c.getAppFnArgs with
      | (``LeanScript.LeanPrimTyCovariant.array, #[_, a]) =>
          return .array (← bundleTyE 0 a)
      | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, a]) =>
          return .thunk (← bundleTyE 0 a)
      | (``LeanScript.LeanPrimTyCovariant.lazy, #[_, a]) =>
          return .lazy (← bundleTyE 0 a)
      | _ => return .other
    | _ => return .other
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      -- the payload is written in the scope the binder opens, so it is bundled at `1`,
      -- and the binder itself carries the proof that it describes a type
      let hwf ← LeanScript.Ty.mkWfIn 0 t
      return .recTaggedUnion (← bundleTUE 1 l) hwf
  | _ => return .other

/-- Is this the terminal type `bool`? -/
def isBoolTy (τ : Expr) : MetaM Bool := do
  match ← tyView τ with
  | .prim p => return p.isConstOf ``LeanScript.LeanPrimTy.bool
  | _ => return false

/-! ## The tree that models a Lean type -/

/-- The tree of the language that models the Lean type `α`, reduced.

    `List α` is the recursive tagged union it is, `Array α` is `Ty.array`; a
    non-dependent function type is `Ty.fn`; everything else is the type's
    `LeanScript.LeanScriptTyWf` instance. -/
partial def treeOfType (α : Expr) : MetaM Expr := do
  let α' ← whnf α
  match α'.getAppFnArgs with
  | (``List, #[β]) =>
      reduceTy (listTyE (← treeOfType β))
  | (``Array, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.array) (← treeOfType β))
  | (``Thunk, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.thunk) (← treeOfType β))
  | _ =>
    match α' with
    | .forallE _ d b _ =>
        if b.hasLooseBVar 0 then
          throwError "`#leanscript_to_term`: the language has no dependent function \
            type, so {α} cannot be translated"
        else
          reduceTy (mkApp2 (mkConst ``LeanScript.Ty.fn) (← treeOfType d)
            (← treeOfType b))
    | _ => do
      let cls ← mkAppM ``LeanScript.LeanScriptTyWf #[α']
      match ← trySynthInstance cls with
      | .some inst => reduceTy (← mkAppOptM ``LeanScript.tyOf #[α', inst])
      | _ =>
        if let .const ind _ := α'.getAppFn then
          if (← getEnv).find? ind matches some (.inductInfo _) then
            if let some f ← LeanScript.Deriving.existentialField? ind α'.getAppArgs then
              throwError "`#leanscript_to_term`: the type {α} has no tree of the \
                language: existential typing is not supported, `{f}` is an existential"
        throwError "`#leanscript_to_term`: the type {α} has no tree of the language \
          (no `LeanScriptTyWf` instance); derive one with `deriving LeanScriptTyWf`"

/-- The type of the language that models the Lean type `α`: its tree, with the proof
    that the tree is a type. -/
def tyOfType (α : Expr) : MetaM Expr := do
  bundleTyE 0 (← treeOfType α)

/-- The tree of the type of `e`. -/
def tyOfTerm (e : Expr) : MetaM Expr := do tyOfType (← inferType e)

end LeanScript.ToTerm

end

end
