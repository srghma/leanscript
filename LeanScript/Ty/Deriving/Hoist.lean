module

public meta import LeanScript.Ty.Deriving.Build

@[expose] public section

meta section

/-!
# `deriving LeanScriptTyWf`: hoisting a recursive wrapper into a member of a family
-/

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

/-! ## Hoisting a recursive wrapper into a member of a family

A field of type `List T`, where `T` is the declaration being defined, cannot be modelled
by `List`'s tree with the occurrence in the place of the argument: the occurrence would
land inside `List`'s *own* binder and would denote the list.  But the declaration is
still a type of the language, because a nested recursion is a mutual one — which is what
Lean itself does with a nested inductive.  `inductive RoseList | node : List RoseList →
RoseList` is the family

```text
member 0 = RoseList = member 1                 -- the declaration
member 1 = nil | cons (_ : member 0) (_ : member 1)   -- the list of them
```

So the binder that would have captured the occurrence is *hoisted*: it becomes one more
member of the family the declaration is translated in, its own `Ty.self` becomes an
occurrence of that member, and the occurrence it holds becomes an occurrence of the
declaration.  Nothing about the wrapper is re-read from Lean — the tree that is taken
apart is the wrapper's own model, from its instance — and a wrapper nested in a wrapper
(`List (List T)`) adds one member per binder on the path to the occurrence.

When the declaration is alone in its block it becomes member `0` of the new family, so
every `Ty.self` in the trees of its own fields becomes `Ty.familyMember 0`; that is
`selfToMember`. -/

/-- Does this tree mention one of the stand-in parameters? -/
def mentionsHole (holes : Array Expr) (e : Expr) : Bool :=
  holes.any fun h => e.containsFVar h.fvarId!

/-- An occurrence of member `i`, as an expression. -/
def familyMemberE (i : Nat) : Expr :=
  mkApp (mkConst ``LeanScript.Ty.familyMember) (mkNatLit i)

/-- Replace every `Ty.self` written in *this* scope — one that does not stand under a
    binder of its own — by `Ty.familyMember i`.  This is what turns the trees of a lone
    declaration's fields into the trees of member `i` of a family. -/
partial def selfToMember (i : Nat) (e : Expr) : Expr :=
  if e.isConstOf ``LeanScript.Ty.self then familyMemberE i
  else if isBinderCtor e then e
  else
    match e with
    | .app f a => .app (selfToMember i f) (selfToMember i a)
    | .lam n t b bi => .lam n (selfToMember i t) (selfToMember i b) bi
    | .forallE n t b bi => .forallE n (selfToMember i t) (selfToMember i b) bi
    | .mdata d b => .mdata d (selfToMember i b)
    | .proj s k b => .proj s k (selfToMember i b)
    | e => e

mutual

/-- The tree of the wrapper's model `e`, written in the scope of the family the
    declaration is being translated in: a stand-in parameter becomes the tree of what
    stands there, a `Ty.self` of the binder being hoisted becomes `selfIdx`, and a binder
    that holds a stand-in is hoisted into a member of its own.  `none` when the model
    holds a shape this cannot hoist. -/
partial def hoistTree (ctx : Ctx) (holes trees : Array Expr) (selfIdx : Option Nat)
    (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if let some k := holes.idxOf? α then
      -- the argument's tree is written in the declaration's own scope, and the
      -- declaration is member `0` of the family being built
      return some (selfToMember 0 trees[k]!)
  if e.isConstOf ``LeanScript.Ty.self then
    match selfIdx with
    | some i => return some (familyMemberE i)
    | none => return none
  if isBinderCtor e then
    -- a binder that holds no stand-in is a closed subtree and is kept as it is
    if !mentionsHole holes e then return some e
    return ← hoistBinder ctx holes trees e
  match e with
  | .app .. =>
      let mut out := e.getAppFn
      for a in e.getAppArgs do
        let some a' ← hoistTree ctx holes trees selfIdx a | return none
        out := mkApp out a'
      return some out
  | .lam n t b i => do
      let some t' ← hoistTree ctx holes trees selfIdx t | return none
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.lam n t' b' i)
  | .forallE n t b i => do
      let some t' ← hoistTree ctx holes trees selfIdx t | return none
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.forallE n t' b' i)
  | .mdata d b => do
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.mdata d b')
  | .proj s i b => do
      let some b' ← hoistTree ctx holes trees selfIdx b | return none
      return some (.proj s i b')
  | _ => return some e

/-- Hoist the binder `e`, which holds a stand-in, into a member of the family: the member
    is numbered next, its payload is the binder's payload with the binder's own `Ty.self`
    reading as that member, and the answer is an occurrence of it. -/
partial def hoistBinder (ctx : Ctx) (holes trees : Array Expr) (e : Expr) :
    MetaM (Option Expr) := do
  let k := ctx.baseCount + (← ctx.extra.get).size
  -- the member's number is taken before its payload is converted, so that a binder
  -- nested inside it gets the next one
  ctx.extra.modify (·.push (mkConst ``LeanScript.Ty.self))
  let asMember (ctor : Name) (payload : Expr) : MetaM (Option Expr) := do
    let some p ← hoistTree ctx holes trees (some k) payload | return none
    return some (← mkAppM ctor #[p])
  let member? ←
    match e.getAppFnArgs with
    | (``LeanScript.Ty.recAlias, #[b]) =>
        asMember ``LeanScript.LeanFamMemberSchema.alias b
    | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
        asMember ``LeanScript.LeanFamMemberSchema.ctors l
    | (``LeanScript.Ty.recObject, #[fs]) =>
        asMember ``LeanScript.LeanFamMemberSchema.record fs
    | _ => pure none
  let some member := member? | return none
  ctx.extra.modify (·.set! (k - ctx.baseCount) member)
  return some (familyMemberE k)

end

end LeanScript.Deriving

end

end
