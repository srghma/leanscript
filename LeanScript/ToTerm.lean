module

public meta import Lean
public meta import LeanScript.Expr.Term
public meta import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving

@[expose] public section

meta section

/-!
# `#leanscript_to_term`: a Lean definition, as a `Term`

```lean
def addOne (n : Nat) : Nat := n + 1   -- with `add` declared in the signature

def addOne_term : Term sg [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term addOne
```

`#leanscript_to_term e` reads the Lean definition `e` and builds the `LeanScript.Term`
that means the same thing.  It is a **term** elaborator, so the type it is checked
against says which signature and which context the term is written in: the expected type
is a `LeanScript.Term Sg Γ τ`, and `Sg` is the signature the translation resolves
top-level names against.

The signature can be named instead of read off the expected type, and then the type of
the translation does not have to be written at all:

```lean
def addOne_term' := #leanscript_to_term (sig := sg) addOne
```

With neither an expected type nor a `(sig := …)`, the empty signature and the empty
context are used.

## What may appear in a translated definition

| Lean | `Term` |
| :-- | :-- |
| `fun x => b`, `f a`, `let x := v; b` | `lam`, `ap`, `letE` |
| a literal of a terminal type | `bool_mk`, `nat_mk`, `int_mk`, `string_mk`, … |
| `if b then t else e` (`b : Bool`), `cond` | `bool_casesOn` |
| a constructor of a record-shaped type | `record_mk` |
| a constructor of a tagged union | `taggedUnion_mk` |
| a constructor of an enum | `enum_mk` |
| an array literal | `array_mk` |
| a constructor of `List` | `recTaggedUnion_mk` |
| `Thunk.mk (fun _ => e)`, `t.get` | `thunk_mk`, `thunk_force` |
| `match`, `X.casesOn`, a projection | `record_casesOn`, `taggedUnion_casesOn`, `enum_casesOn`, `bool_casesOn`, `recTaggedUnion_casesOn`, `nat_casesOn` |
| a `match` that leaves constructors out | `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault`, `recTaggedUnion_casesOnWithDefault` |
| `Nat.rec`, `List.rec` (non-dependent motive), a structural recursion Lean compiled through `Nat.brecOn` / `List.brecOn` | `nat_rec`, `recTaggedUnion_rec` — or `nat_casesOn` / `recTaggedUnion_casesOn`, when the branch does not use the value of the fold |
| a recursion on a `Nat` that descends `k + 1` steps (`fib`, the tribonacci numbers, …) | `nat_rec k` |
| `do` in `Id` — `Id.run`, `pure`, `>>=`, `<$>`, and `let mut` | the `let`s and applications it stands for |
| `for i in [:n] do …` in `Id`, over `Std.Legacy.Range` | `nat_rec`, folding the state of the loop |
| a name of the signature | `global` |

**A list and an array are different types here.**  `Array α` is `Ty.array`, the one
sequence the grammar has an introduction form for: it takes every element at once, so an
array literal translates and a non-literal array does not.  `List α` is the tree its
`LeanScriptTyWf` instance gives it — the recursive tagged union `nil | cons α self` — so
`[]` and `hd :: tl` are `recTaggedUnion_mk`, a `match` on a list is
`recTaggedUnion_casesOn` and `List.rec` is `recTaggedUnion_rec`.  A list therefore does
not have to be written out.

The two are not interchangeable, and neither `Array.toList` nor a `match` on an array has
a term.  Note also that `LeanScript.Ty.Den` gives a recursive tree no values, so a
translated list is outside the fragment `LeanScript.Term.eval` interprets
(`LeanScript.Term.NoRecMk`): it is checked by its type, not run.

## Which calls are allowed

A **constructor is inlinable**: an application of one is built in place, as the
`record_mk`, `taggedUnion_mk`, `enum_mk` or `array_mk` node it denotes.  So are
projections and anything marked `@[inline]`, `@[macro_inline]`, `@[always_inline]` or
`@[reducible]` (an `abbrev`): their definition is translated and cached, and the
translation is used at the call site.

Every **other** top-level function must be declared in the signature: it is translated
to `Term.global`, the reference the signature gives it.  A call of a function that is
neither inlinable nor declared is refused, naming the function — there is no third way
for a term to mention a top-level name.

The definition `#leanscript_to_term` is *applied to* is always unfolded: it is the thing
being translated.

## What is refused

* `partial` and `unsafe` definitions, and `opaque` constants and axioms: they have no
  total value to translate.
* well-founded recursion (`WellFounded.fix`, `Acc.rec`) and partial fixpoints
  (`Lean.Order.fix`).
* a recursion on a `Nat` that does **not** descend by a fixed number of steps: a call at
  `n / 2`, say.  A recursion that descends `k + 1` steps for some fixed `k` — `fib` reads
  its value at `n` and at `n + 1`, the hexanacci numbers at the six previous arguments —
  is translated as `nat_rec k`, and the depth is read off the compiled recursion: it is
  the smallest number of steps at which the *history* the `brecOn` hands the branch is
  fully read.  A recursion on a `List` still descends one step, and a structural
  recursion on any other type is still refused, since those are the only folds.
* a `for` loop that leaves early (`break`, `return`), or over a range that does not start
  at `0` or steps by more than `1`; and `do` in any monad other than `Id`, which is the
  only one that is not an effect.

## Which dispatch a `match` becomes

A `match` is translated by the shape of the type it takes apart and by **which
constructors it names**:

* it names them all, and no branch uses the value of a fold: the exhaustive dispatch,
  `enum_casesOn`, `taggedUnion_casesOn`, `record_casesOn`, `recTaggedUnion_casesOn`,
  `nat_casesOn`, `bool_casesOn`;
* it leaves constructors out (a wildcard, or fewer patterns than constructors): the
  partial dispatch, `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` or
  `recTaggedUnion_casesOnWithDefault`, whose default branch is the one the wildcard
  wrote — the dispatch is *not* expanded into one branch per constructor;
* it is the branch of a recursion whose body uses the value at the smaller argument: the
  fold, `nat_rec` or `recTaggedUnion_rec`.
* a dependent motive, a dependent function type, and any type with no
  `LeanScript.LeanScriptTyWf` instance (an existentially typed structure, for one, has
  no instance: see `LeanScript.Ty.Deriving`).

## The cache

Every closed definition that is inlined is translated **once**: the translation is
stored as a function of the context, `fun Γ => …`, which is what makes one translation
usable at every depth it is called from.

Two definitions that translate to the *same shape* share one entry: the produced tree is
hashed (`Lean.Expr.hash`) and compared against the entries of that hash, and an equal
one is returned as the **same object**, so the duplicate is not built twice and the two
call sites point at one tree in memory.  `#leanscript_to_term_cache_stats` reports how
many entries, cache hits and shape merges there have been, and
`#leanscript_to_term_cache_clear` empties the cache.

`TyTests/ToTermTest.lean` runs all of this: it translates about twenty definitions and
checks, by the kernel, that `LeanScript.Term.eval` gives each translation the value the
Lean definition has — except for the lists, which have no values and are checked by their
types — and it pins what the translation refuses.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## Expressions of the object language -/

/-- The type `LeanScript.TyWf` — a type of the language — as an expression.  This is the
    currency of the translation: `LeanScript.Term` is indexed by it. -/
def tyE : Expr := mkConst ``LeanScript.TyWf

/-- The type `LeanScript.Ty` — a tree — as an expression.  A tree is what a
    `LeanScriptTyWf` instance holds and what `ty_wf` reasons about; it becomes a type of
    the language by being bundled with its proof. -/
def treeE : Expr := mkConst ``LeanScript.Ty

/-- `LeanScript.TyWfIn n`, the trees written in a scope of `n` members, as an
    expression. -/
def tyWfInE (n : Nat) : Expr := mkApp (mkConst ``LeanScript.TyWfIn) (mkNatLit n)

/-- The bundles of a scope: `TyWf` closed, `TyWfIn n` inside a binder. -/
def scopeTyE (n : Nat) : Expr := if n == 0 then tyE else tyWfInE n

/-- The type `LeanScript.Ctx = List TyWf`, as an expression. -/
def ctxE : Expr := mkApp (mkConst ``List [Level.zero]) tyE

/-- The empty context, as an expression. -/
def nilCtxE : Expr := mkApp (mkConst ``List.nil [Level.zero]) tyE

/-- `τ :: Γ`, as an expression. -/
def consCtxE (t rest : Expr) : Expr :=
  mkApp3 (mkConst ``List.cons [Level.zero]) tyE t rest

/-- The context `ts ++ base`, with `ts` innermost first. -/
def mkCtxE (ts : List Expr) (base : Expr) : Expr := ts.foldr consCtxE base

/-- The schema of `List α` as the language sees it, as a schema of **trees**:
    constructor `0` is `nil`, which has no fields, and constructor `1` is `cons`, whose
    fields are an element and the list itself (`Ty.self`).  This is the schema of the
    `LeanScriptTyWf (List α)` instance. -/
def listSchemaE (σ : Expr) : Expr :=
  let nilTys := mkApp (mkConst ``List.nil [Level.zero]) treeE
  let tl := mkApp3 (mkConst ``List.cons [Level.zero]) treeE
    (mkConst ``LeanScript.Ty.self) nilTys
  let ne := mkApp3 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
    [Level.zero]) treeE σ tl
  let nilCtors := mkApp (mkConst ``List.nil [Level.zero])
    (mkApp (mkConst ``List [Level.zero]) treeE)
  let here := mkApp3 (mkConst ``LeanScript.CtorsWithPayload.here) treeE ne nilCtors
  mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.skip) treeE here

/-- The tree of `List α`: the recursive tagged union `nil | cons α self`. -/
def listTyE (σ : Expr) : Expr :=
  mkApp (mkConst ``LeanScript.Ty.recTaggedUnion) (listSchemaE σ)

/-- `@id TyWf`, the projection the variable scopes use. -/
def idTyE : Expr := mkApp (mkConst ``id [Level.one]) tyE

/-! ## From a tree to a type of the language

A tree becomes a **type** by being bundled with the proof that it is one, which
`LeanScript.Ty.mkWfIn` — what `ty_wf` runs — writes.  The bundle keeps the tree it was
given as its `toTy`, so a bundle built here is definitionally the one the grammar's own
constructors build out of the bundled payload, and the proofs never have to agree.
-/

/-- The tree `t`, bundled at scope `n`: `LeanScript.TyWf` closed, `LeanScript.TyWfIn n`
    inside a binder. -/
def bundleTyE (n : Nat) (t : Expr) : MetaM Expr := do
  let prf ← LeanScript.Ty.mkWfIn n t
  if n == 0 then
    return mkApp2 (mkConst ``LeanScript.TyWf.mk) t prf
  else
    return mkApp3 (mkConst ``LeanScript.TyWfIn.mk) (mkNatLit n) t prf

/-- The tree of a bundle: the `toTy` it was built from, or the projection of it. -/
def treeOfTyE (τ : Expr) : MetaM Expr := do
  match τ.getAppFnArgs with
  | (``LeanScript.TyWf.mk, #[t, _]) => return t
  | (``LeanScript.TyWfIn.mk, #[_, t, _]) => return t
  | _ => whnf (mkApp (mkConst ``LeanScript.TyWf.toTy) τ)

/-- Reduce an expression to the constructor tree it denotes.  Trees of the language are
    data, so this is the form every match below is written against. -/
def reduceTy (e : Expr) : MetaM Expr :=
  withTransparency .default <|
    reduce e (explicitOnly := false) (skipTypes := false) (skipProofs := true)

/-- The elements of a fully reduced `List α` expression. -/
partial def listOfExpr (e : Expr) : MetaM (List Expr) := do
  match (← whnf e).getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, a, as]) => return a :: (← listOfExpr as)
  | _ => throwError "`#leanscript_to_term`: not a list of types: {e}"

/-- The value of a fully reduced `Nat` expression. -/
def natOfExpr (e : Expr) : MetaM Nat := do
  let some n ← evalNat (← whnf e) | throwError "`#leanscript_to_term`: not a number: {e}"
  return n

/-! ## Bundling a payload

A schema of the grammar is a schema **of bundles**: the fields of a record are
`LeanRecordSchema TyWf`, the payload of a recursive union is
`LeanTaggedUnionSchema (TyWfIn 1)`.  The functions below rebuild a schema of trees as the
schema of bundles it stands for, one field at a time, so that mapping the result back to
trees gives the schema they were given. -/

/-- A list of bundles, from a list of trees. -/
def bundleListE (n : Nat) (ts : Expr) : MetaM Expr := do
  let xs ← (← listOfExpr ts).mapM (bundleTyE n)
  let elem := scopeTyE n
  return xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) elem)

/-- A non-empty list of bundles, from one of trees. -/
def bundleNEE (n : Nat) (ne : Expr) : MetaM Expr := do
  match (← whnf ne).getAppFnArgs with
  | (``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk, #[_, hd, tl]) =>
      return mkApp3 (mkConst ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
        [Level.zero]) (scopeTyE n) (← bundleTyE n hd) (← bundleListE n tl)
  | _ => throwError "`#leanscript_to_term`: not a non-empty list of types: {ne}"

/-- The constructors a schema leaves unconstrained, bundled. -/
def bundleCtorsE (n : Nat) (cs : Expr) : MetaM Expr := do
  let xs ← (← listOfExpr cs).mapM (bundleListE n)
  let elem := mkApp (mkConst ``List [Level.zero]) (scopeTyE n)
  return xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [Level.zero]) elem a acc)
    (mkApp (mkConst ``List.nil [Level.zero]) elem)

/-- The fields of a record, bundled. -/
def bundleRecordE (n : Nat) (fs : Expr) : MetaM Expr := do
  match (← whnf fs).getAppFnArgs with
  | (``LeanScript.LeanRecordSchema.mk, #[_, a, b, rest]) =>
      return mkAppN (mkConst ``LeanScript.LeanRecordSchema.mk)
        #[scopeTyE n, ← bundleTyE n a, ← bundleTyE n b, ← bundleListE n rest]
  | _ => throwError "`#leanscript_to_term`: not a record schema: {fs}"

mutual

/-- The constructors of a tagged union, bundled. -/
partial def bundleTUE (n : Nat) (l : Expr) : MetaM Expr := do
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      return mkAppN (mkConst ``LeanScript.LeanTaggedUnionSchema.payloadFirst)
        #[scopeTyE n, ← bundleNEE n fields, ← bundleListE n next, ← bundleCtorsE n rest]
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.skip) (scopeTyE n)
        (← bundleCPE n rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- The constructors that follow a field-less one, bundled. -/
partial def bundleCPE (n : Nat) (cp : Expr) : MetaM Expr := do
  match (← whnf cp).getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
      return mkApp3 (mkConst ``LeanScript.CtorsWithPayload.here) (scopeTyE n)
        (← bundleNEE n fields) (← bundleCtorsE n rest)
  | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
      return mkApp2 (mkConst ``LeanScript.CtorsWithPayload.skip) (scopeTyE n)
        (← bundleCPE n rest)
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"

end

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

/-! ## The context a translation runs in -/

/-- One declaration of the signature: the name it is bound to, its tree, and the
    reference that names it. -/
structure GlobalEntry where
  /-- The identifier the declaration is bound to. -/
  name : String
  /-- Its tree. -/
  ty : Expr
  /-- The `LeanScript.GlobalRef` that points at it. -/
  ref : Expr

/-- Where a translation stands: the signature, the context it started in, and the
    binders it has entered since. -/
structure TCtx where
  /-- The signature, as an expression. -/
  sg : Expr
  /-- The declarations of the signature. -/
  globals : Array GlobalEntry
  /-- The context the translation started in, as an expression. -/
  base : Expr
  /-- The binders entered since, **outermost first**, each with its tree. -/
  binders : Array (FVarId × Expr) := #[]

/-- The context of the translation, as an expression: the binders entered, innermost
    first, in front of the context it started in. -/
def TCtx.gamma (c : TCtx) : Expr :=
  c.binders.foldl (init := c.base) fun acc (_, t) => consCtxE t acc

/-- Enter a binder of this tree. -/
def TCtx.push (c : TCtx) (f : FVarId) (t : Expr) : TCtx :=
  { c with binders := c.binders.push (f, t) }

/-- Enter the binders of a branch: `ts` are the trees of the fields it binds, in
    declaration order, so the first field is de Bruijn index `0`. -/
def TCtx.pushFields (c : TCtx) (fs : Array (FVarId × Expr)) : TCtx :=
  { c with binders := c.binders ++ fs.reverse }

/-- The trees of the binders entered, innermost first. -/
def TCtx.binderTys (c : TCtx) : List Expr :=
  (c.binders.map (·.2)).toList.reverse

/-! ## The variables -/

/-- The de Bruijn index `k` of the context `ts ++ base`. -/
partial def mkIndexE (ts : List Expr) (base : Expr) (k : Nat) : MetaM Expr := do
  match ts, k with
  | t :: rest, 0 =>
      return mkAppN (mkConst ``LeanScript.DeBruijnProj.head)
        #[tyE, tyE, idTyE, t, mkCtxE rest base]
  | t :: rest, k + 1 =>
      let some b := rest[k]? | throwError "`#leanscript_to_term`: variable out of range"
      let v ← mkIndexE rest base k
      return mkAppN (mkConst ``LeanScript.DeBruijnProj.tail)
        #[tyE, tyE, idTyE, t, mkCtxE rest base, b, v]
  | [], _ => throwError "`#leanscript_to_term`: variable out of range"

/-- The term that reads the variable `f` of the context. -/
def TCtx.var (c : TCtx) (f : FVarId) : MetaM Expr := do
  let some i := c.binders.findIdx? (fun (g, _) => g == f)
    | throwError "`#leanscript_to_term`: {Expr.fvar f} is not a variable of the \
        translated definition"
  let k := c.binders.size - 1 - i
  let τ := c.binders[i]!.2
  let idx ← mkIndexE c.binderTys c.base k
  return mkAppN (mkConst ``LeanScript.Term.var) #[c.sg, c.gamma, τ, idx]

/-! ## The signature -/

/-- Read the declarations of a signature: their names, their trees and the references
    that point at them. -/
def parseSig (sg : Expr) : MetaM (Array GlobalEntry) := do
  let declsE ← whnf (mkApp (mkConst ``LeanScript.Sig.decls) sg)
  -- the cons cells of the list, outermost first
  let mut cells : Array (Expr × Expr) := #[]   -- (head, tail)
  let mut cur := declsE
  repeat
    match (← whnf cur).getAppFnArgs with
    | (``List.cons, #[_, d, ds]) => cells := cells.push (d, ds); cur := ds
    | (``List.nil, _) => break
    | _ => throwError "`#leanscript_to_term`: the signature's declarations are not a \
        list written out: {declsE}"
  let mut out : Array GlobalEntry := #[]
  for i in [0:cells.size] do
    let (d, ds) := cells[i]!
    let dv ← whnf d
    let some (name, ty) ← pure (match dv.getAppFnArgs with
      | (``LeanScript.GlobalDecl.mk, #[n, t]) => some (n, t)
      | _ => none)
      | throwError "`#leanscript_to_term`: a declaration of the signature is not \
          written out: {d}"
    let some nameStr := (match ← whnf name with | .lit (.strVal s) => some s | _ => none)
      | throwError "`#leanscript_to_term`: the name of a declaration is not a string \
          literal: {name}"
    -- the reference: `i` tails around a head
    let mut ref := mkAppN (mkConst ``LeanScript.DeBruijnProj.head)
      #[mkConst ``LeanScript.GlobalDecl, tyE, mkConst ``LeanScript.GlobalDecl.ty, d, ds]
    let tyR ← reduceTy ty
    for j in [0:i] do
      let (d', ds') := cells[i - 1 - j]!
      ref := mkAppN (mkConst ``LeanScript.DeBruijnProj.tail)
        #[mkConst ``LeanScript.GlobalDecl, tyE, mkConst ``LeanScript.GlobalDecl.ty,
          d', ds', tyR, ref]
    out := out.push { name := nameStr, ty := tyR, ref := ref }
  return out

/-- The declaration of the signature a Lean constant stands for, if it declares one: the
    name is matched in full (`Foo.bar`) and by its last component (`bar`). -/
def TCtx.global? (c : TCtx) (n : Name) : Option GlobalEntry :=
  let full := n.toString
  let short := n.getString!
  (c.globals.find? (·.name == full)).orElse fun _ => c.globals.find? (·.name == short)

/-! ## The cache of translated definitions -/

/-- One definition that has been translated: the value it was translated from, and the
    translation, as a function of the context it is used in. -/
structure CacheEntry where
  /-- The signature it was translated against. -/
  sg : Expr
  /-- The closed Lean value that was translated. -/
  src : Expr
  /-- The translation: `fun (Γ : Ctx) => …`. -/
  fn : Expr
  /-- The hash of the translation, for the shape lookup. -/
  hash : UInt64
  deriving Inhabited

/-- What the cache holds, and what it has done. -/
structure CacheState where
  /-- The definitions translated so far. -/
  entries : Array CacheEntry := #[]
  /-- How often a definition was found already translated. -/
  hits : Nat := 0
  /-- How often a *new* definition turned out to have the shape of one already
      translated, and was replaced by it. -/
  shared : Nat := 0
  deriving Inhabited

/-- The cache of translated definitions.  It survives between calls of
    `#leanscript_to_term`, so a function called from two definitions is translated
    once. -/
initialize cacheRef : IO.Ref CacheState ← IO.mkRef {}

/-! ## What may be translated at all -/

/-- Is this constant part of a well-founded recursion — the fixpoint operator, its
    companions, or a recursion on an accessibility proof? -/
def isWfRecursion (n : Name) : Bool :=
  n.components.any (fun p => p == `WellFounded || p == `WellFoundedRecursion) ||
    n == ``Acc.rec || n == ``invImage

/-- Is this the fixpoint a `partial_fixpoint` definition is built from? -/
def isPartialFixpoint (n : Name) : Bool :=
  n.getString! == "fix" && n.getPrefix == `Lean.Order

/-- Is this the compiled form of a structural recursion — `X.brecOn`, `X.binductionOn`,
    the `below` motive, or the unsafe companion of a `partial` definition?

    `Nat.brecOn` and `List.brecOn` are **not** among them: those two are the compiled form
    of a recursion over the two types the grammar has a fold for, and
    `LeanScript.ToTerm.transBrecOn` turns them into that fold. -/
def isCompiledRecursion (n : Name) : Bool :=
  if n == ``Nat.brecOn || n == ``List.brecOn then false else
  let s := n.getString!
  s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
    s == "_unsafe_rec"

/-- Refuse a constant the language has no total value for. -/
def checkConst (n : Name) : MetaM Unit := do
  if isPartialFixpoint n then
    throwError "`#leanscript_to_term`: a partial fixpoint ({n}) is not supported: the \
      grammar has no fixpoint that does not descend"
  if isWfRecursion n then
    throwError "`#leanscript_to_term`: well-founded recursion ({n}) is not supported — \
      the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so \
      write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive"
  if isCompiledRecursion n then
    throwError "`#leanscript_to_term`: {n} is the compiled form of a recursion the \
      grammar cannot express — write the recursion as `Nat.rec` or `List.rec` with a \
      non-dependent motive, which are `nat_rec` and `recTaggedUnion_rec`"
  match ← getConstInfo n with
  | .defnInfo d =>
      if d.safety == .partial then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      if d.safety == .unsafe then
        throwError "`#leanscript_to_term`: `{n}` is `unsafe`"
  | .opaqueInfo _ =>
      if ((← getEnv).find? (n ++ `_unsafe_rec)).isSome then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      throwError "`#leanscript_to_term`: `{n}` is opaque, so there is nothing to \
        translate"
  | .axiomInfo _ =>
      throwError "`#leanscript_to_term`: `{n}` is an axiom, so there is nothing to \
        translate"
  | _ => pure ()

/-- Is a call of this constant inlined?  A constructor and a projection always are, and
    so is anything the author marked inlinable or reducible. -/
def isInlinable (n : Name) : MetaM Bool := do
  if (← getEnv).find? n matches some (.ctorInfo _) then return true
  if (← getProjectionFnInfo? n).isSome then return true
  if ← Lean.isReducible n then return true
  let env ← getEnv
  return Compiler.hasInlineAttribute env n
    || Compiler.hasMacroInlineAttribute env n
    || Compiler.hasInlineIfReduceAttribute env n

/-! ## Literals -/

/-- The introduction form of a literal of this Lean type. -/
def litCtorFor : Name → Option Name
  | ``Bool => some ``LeanScript.Term.bool_mk
  | ``Nat => some ``LeanScript.Term.nat_mk
  | ``Int => some ``LeanScript.Term.int_mk
  | ``String => some ``LeanScript.Term.string_mk
  | ``Char => some ``LeanScript.Term.char_mk
  | ``UInt8 => some ``LeanScript.Term.uint8_mk
  | ``UInt16 => some ``LeanScript.Term.uint16_mk
  | ``UInt32 => some ``LeanScript.Term.uint32_mk
  | ``UInt64 => some ``LeanScript.Term.uint64_mk
  | ``Int8 => some ``LeanScript.Term.int8_mk
  | ``Int16 => some ``LeanScript.Term.int16_mk
  | ``Int32 => some ``LeanScript.Term.int32_mk
  | ``Int64 => some ``LeanScript.Term.int64_mk
  | ``Float => some ``LeanScript.Term.float_mk
  | ``Float32 => some ``LeanScript.Term.float32_mk
  | _ => none

/-- Is this expression a literal — a numeral, a string, a character, a boolean, or a
    sign in front of one?  A literal is carried into the term as it stands; anything
    else is translated. -/
partial def isLitLike (e : Expr) : Bool :=
  match e with
  | .lit _ => true
  | .mdata _ b => isLitLike b
  | .const n _ => n == ``Bool.true || n == ``Bool.false
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => isLitLike n
    | (``OfScientific.ofScientific, _) => true
    | (``Neg.neg, #[_, _, a]) => isLitLike a
    | (``Int.ofNat, #[a]) => isLitLike a
    | (``Int.negSucc, #[a]) => isLitLike a
    | (``Char.ofNat, #[a]) => isLitLike a
    | (``Char.ofNatAux, #[a, _]) => isLitLike a
    | _ => false

/-! ## Small pieces of the object language -/

/-- A list of trees, as an expression. -/
def mkTyListE (ts : List Expr) : Expr := mkCtxE ts nilCtxE

/-- The field trees of a record schema, in declaration order. -/
def recordFieldTys (fs : Expr) : MetaM (List Expr) := do
  match (← whnf fs).getAppFnArgs with
  | (``LeanScript.LeanRecordSchema.mk, #[_, a, b, rest]) =>
      return a :: b :: (← listOfExpr rest)
  | _ => throwError "`#leanscript_to_term`: not a record schema: {fs}"

/-- The fields of a non-empty list of trees. -/
def nonEmptyTys (ne : Expr) : MetaM (List Expr) := do
  match (← whnf ne).getAppFnArgs with
  | (``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk, #[_, hd, tl]) =>
      return hd :: (← listOfExpr tl)
  | _ => throwError "`#leanscript_to_term`: not a non-empty list of types: {ne}"

mutual

/-- One entry per constructor of a tagged union, each the trees of its fields. -/
partial def taggedUnionCtorTys (l : Expr) : MetaM (List (List Expr)) := do
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      let restL ← (← listOfExpr rest).mapM listOfExpr
      return (← nonEmptyTys fields) :: (← listOfExpr next) :: restL
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      return [] :: (← ctorsWithPayloadTys rest)
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- One entry per constructor a `CtorsWithPayload` holds. -/
partial def ctorsWithPayloadTys (cp : Expr) : MetaM (List (List Expr)) := do
  match (← whnf cp).getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
      let restL ← (← listOfExpr rest).mapM listOfExpr
      return (← nonEmptyTys fields) :: restL
  | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
      return [] :: (← ctorsWithPayloadTys rest)
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"

end

/-- The pieces of the schema of a list: the `CtorsWithPayload` after the field-less
    `nil`, the fields of `cons` and the constructors after it (there are none).  The
    schema is `listSchemaE`, so this is where the element type is read off. -/
def listSchemaParts (l : Expr) : MetaM (Expr × Expr × Expr) := do
  let cp ← match (← whnf l).getAppFnArgs with
    | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) => pure (← whnf cp)
    | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
  match cp.getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) => return (cp, fields, rest)
  | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"

/-- A member of `Fin n`, with the bound proved by computation. -/
def mkFinLit (n : Expr) (i : Nat) : MetaM Expr := do
  let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, n])
  return mkAppN (mkConst ``Fin.mk) #[n, mkNatLit i, prf]

/-- Unfold the head of an application: a matcher, a `casesOn`, or any definition. -/
def unfoldHere? (e : Expr) : MetaM (Option Expr) := do
  if let some e' ← delta? e then return some e'
  withTransparency .all (unfoldDefinition? e)

/-! ## A dispatch that repeats one branch

A `match` whose last pattern is a wildcard is compiled into a dispatch that names *every*
constructor, with the wildcard's body repeated in the branch of each constructor the
earlier patterns did not name.  The grammar has a form for exactly that shape —
`LeanScript.Term.enum_casesOnWithDefault` and
`LeanScript.Term.taggedUnion_casesOnWithDefault`, which name some of the constructors and
send the rest to one default branch — so the repetition is detected here and the partial
form is what is built.

A branch counts as the default only when it **ignores the fields it binds**: a wildcard
whose body mentions the value it matched (`| _ => f x`) is a different body in each
branch, and then the exhaustive form is the honest translation. -/

/-- The body of a branch that binds its constructor's fields and uses none of them, and
    nothing when the branch does use one: only such a branch can be the default of a
    partial dispatch, since the default binds nothing. -/
def branchDefaultBody? (minor : Expr) (ctorName : Name) : MetaM (Option Expr) := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let body := (mkAppN minor xs).headBeta
    if xs.any (fun x => body.containsFVar x.fvarId!) then return none
    return some body

/-- The branch a dispatch repeats, and the constructors that take it: the largest group
    of branches that are the *same* field-free body.  There has to be more than one of
    them — a single branch is no shorter written with a default — and they cannot be all
    of them, since the default of a dispatch that names every constructor is unreachable
    and the grammar refuses it. -/
def repeatedBranch? (minors : Array Expr) (ctors : Array Name) :
    MetaM (Option (Expr × Array Nat)) := do
  let n := ctors.size
  if n < 3 then return none
  if minors.size < n then return none
  let mut bodies : Array (Option Expr) := #[]
  for i in [0:n] do
    bodies := bodies.push (← branchDefaultBody? minors[i]! ctors[i]!)
  let mut best : Option (Expr × Array Nat) := none
  for i in [0:n] do
    if let some b := bodies[i]! then
      let mut idxs : Array Nat := #[]
      for j in [0:n] do
        if let some b' := bodies[j]! then
          if b' == b then idxs := idxs.push j
      if idxs.size ≥ 2 && idxs.size < n then
        match best with
        | some (_, prev) => if prev.size < idxs.size then best := some (b, idxs)
        | none => best := some (b, idxs)
  return best

/-! ## A `match` that Lean compiled with a default

A `match` whose patterns do not name every constructor is compiled into an auxiliary
Lean calls `f._sparseCasesOn_i`: the branches of the constructors the patterns *do* name,
in constructor order, followed by one `else` branch that every other constructor takes.
Which constructors are named is a **bit mask** in the type of that `else` branch
(`Nat.hasNotBit mask t.ctorIdx`), so the shape of the dispatch is read off the auxiliary
rather than guessed, and it is exactly the shape of the grammar's
`xxx_casesOnWithDefault`. -/

/-- Is this the auxiliary a `match` with an incomplete set of patterns compiles to? -/
def isSparseCasesOn (n : Name) : Bool := n.getString!.startsWith "_sparseCasesOn"

/-- What a `_sparseCasesOn_` auxiliary dispatches on: how many arguments it takes, and
    which constructors, by number, have a branch of their own.  The rest go to the
    `else` branch, which is its last argument. -/
def sparseCasesOnInfo? (n : Name) : MetaM (Option (Nat × List Nat)) := do
  let some ci := (← getEnv).find? n | return none
  forallTelescopeReducing ci.type fun xs _ => do
    if xs.size < 3 then return none
    let elseTy ← whnf (← inferType xs[xs.size - 1]!)
    let .forallE _ dom _ _ := elseTy | return none
    let (``Nat.hasNotBit, #[maskE, _]) := dom.getAppFnArgs | return none
    let some mask ← evalNat (← whnf maskE) | return none
    let named := (List.range 64).filter fun i => mask &&& (1 <<< i) != 0
    if named.length != xs.size - 3 then return none
    return some (xs.size, named)

/-! ## The compiled form of a structural recursion

Lean compiles a structurally recursive definition into `X.brecOn`, which hands the branch
the whole **history** of the recursion — the value of the function at every smaller
argument — while the grammar's folds hand the branch a fixed number of the nearest
answers (`LeanScript.Term.nat_rec k`, `LeanScript.Term.recTaggedUnion_rec`).  So a
`brecOn` is translated by *reducing the history away*: the branch is instantiated at a
history whose nearest entries are variables standing for those answers, and the
translation succeeds exactly when nothing else of the history is read. -/

/-- Reduce an application far enough to see the branch it takes: beta, `match`, `casesOn`
    and the auxiliary the compiler names `_f`, and **nothing else** — a call the
    translation has to see is left standing. -/
def isBrecAux (n : Name) : Bool :=
  let s := n.getString!
  s == "_f" || s.startsWith "match_" || s == "casesOn" || s == "brecOn" || s == "_unary"

/-- `whnfCore`, unfolding the auxiliaries of a compiled recursion on the way. -/
partial def reduceBrecBody (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e.getAppFn with
  | .const n _ =>
      if isBrecAux n then
        match ← withTransparency .all (unfoldDefinition? e) with
        | some e' => reduceBrecBody e'
        | none => return e
      else return e
  | _ => return e

/-- `reduceBrecBody`, continued **under the binders** the branch opens.  A recursion that
    takes more than one argument is compiled with the later arguments in the motive, so
    its branch is a function and the `match` that reads the history sits under a lambda;
    reducing there is what lets an accumulator-passing loop be seen as a fold. -/
partial def reduceBrecBodyDeep (e : Expr) : MetaM Expr := do
  let e ← reduceBrecBody e
  match e with
  | .lam .. =>
      lambdaBoundedTelescope e 1 fun xs b => do
        mkLambdaFVars xs (← reduceBrecBodyDeep b)
  | _ => return e

/-- How deep a recursion on a natural number the translation looks for: `fib` descends
    two steps, the hexanacci numbers six, and a definition that descends more steps than
    this is refused rather than searched for indefinitely. -/
def maxNatRecDepth : Nat := 16

/-- One component of a `PProd`, however it is written: `(0, x)` for the first component
    of `x` and `(1, x)` for the second, whether it is a projection or an application of
    `PProd.fst` / `PProd.snd`. -/
def pprodProj? (e : Expr) : Option (Nat × Expr) :=
  match e.consumeMData with
  | .proj ``PProd i x => some (i, x)
  | e' =>
      match e'.getAppFnArgs with
      | (``PProd.fst, #[_, _, x]) => some (0, x)
      | (``PProd.snd, #[_, _, x]) => some (1, x)
      | _ => none

/-- The history `i` steps back: `hist` itself is `0`, and `t.2` is one step further than
    `t`, since `below (n + 1)` is `motive n ×' below n`. -/
partial def histTail? (hist : FVarId) (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .fvar f => if f == hist then some 0 else none
  | e' =>
      match pprodProj? e' with
      | some (1, x) => (histTail? hist x).map (· + 1)
      | _ => none

/-- Which entry of the history does this expression read?  `hist.1` is the value at the
    immediate predecessor, `hist.2.1` the value one step further back, and so on. -/
def histEntry? (hist : FVarId) (e : Expr) : Option Nat :=
  match pprodProj? e with
  | some (0, x) => histTail? hist x
  | _ => none

/-- Read the values of the recursion at the nearest predecessors out of the history:
    entry `i` becomes `ihs[i]`.  Whatever still mentions the history afterwards is a read
    the fold that is being built cannot serve. -/
def substHistory (e : Expr) (hist : FVarId) (ihs : Array Expr) : Expr :=
  e.replace fun s =>
    match histEntry? hist s with
    | some i => ihs[i]?
    | none => none

/-- Read the value of the recursion at the immediate predecessor out of the history:
    `history.1` becomes the variable that stands for it.  Whatever is left of the history
    afterwards is a deeper call, which a one-step fold cannot express. -/
def substHistoryHead (e : Expr) (hist : FVarId) (ih : Expr) : Expr :=
  substHistory e hist #[ih]

/-! ## The translation -/

mutual

/-- The term a Lean expression translates to, in the context `c`. -/
partial def trans (c : TCtx) (e0 : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e0).headBeta
  match e with
  | .mdata _ b => trans c b
  | .fvar f => c.var f
  | .lam .. => transLam c e
  | .letE .. => transLet c e
  | .proj .. => transProj c e
  | .sort .. | .forallE .. =>
      throwError "`#leanscript_to_term`: a type is not a value of the language: {e}"
  | _ =>
      if let some t ← transLit? c e then return t
      transApp c e

/-- `fun x => b`. -/
partial def transLam (c : TCtx) (e : Expr) : MetaM Expr := do
  let fty ← whnf (← inferType e)
  let .forallE _ d _ _ := fty
    | throwError "`#leanscript_to_term`: not a function: {e}"
  let σ ← tyOfType d
  lambdaBoundedTelescope e 1 fun xs body => do
    let c' := c.push xs[0]!.fvarId! σ
    let τ ← tyOfTerm body
    let b ← trans c' body
    return mkAppN (mkConst ``LeanScript.Term.lam) #[c.sg, c.gamma, σ, τ, b]

/-- `let x := v; b`. -/
partial def transLet (c : TCtx) (e : Expr) : MetaM Expr := do
  let .letE n t v b _ := e
    | throwError "`#leanscript_to_term`: internal: not a `let`"
  let σ ← tyOfType t
  let v' ← trans c v
  withLetDecl n t v fun x => do
    let c' := c.push x.fvarId! σ
    let body := b.instantiate1 x
    let τ ← tyOfTerm body
    let b' ← trans c' body
    return mkAppN (mkConst ``LeanScript.Term.letE) #[c.sg, c.gamma, σ, τ, v', b']

/-- A literal of a terminal type, carried into the term as it stands. -/
partial def transLit? (c : TCtx) (e : Expr) : MetaM (Option Expr) := do
  unless isLitLike e do return none
  let t ← whnf (← inferType e)
  let .const n _ := t.getAppFn | return none
  let some ctor := litCtorFor n | return none
  return some (mkAppN (mkConst ctor) #[c.sg, c.gamma, e])

/-- An application, or a bare head. -/
partial def transApp (c : TCtx) (e : Expr) : MetaM Expr := do
  let f := e.getAppFn
  let args := e.getAppArgs
  -- a redex the elaborator left behind (a `match` branch, say) is reduced, not applied
  if f.consumeMData.isLambda && !args.isEmpty then
    return ← trans c ((mkAppN f.consumeMData args).headBeta)
  match f with
  | .const n lvls => transConstApp c e n lvls args
  | .fvar id => applyArgs c (← c.var id) f args
  | .proj .. => applyArgs c (← transProj c f) f args
  | .lam .. | .letE .. => applyArgs c (← trans c f) f args
  | _ => throwError "`#leanscript_to_term`: cannot translate {e}"

/-- Apply a translated function to the arguments it is given, dropping the ones the
    language erases (types, instances and proofs). -/
partial def applyArgs (c : TCtx) (t : Expr) (fn : Expr) (args : Array Expr) : MetaM Expr := do
  let mut t := t
  let mut cur := fn
  for a in args do
    let fty ← whnf (← inferType cur)
    let .forallE _ d _ _ := fty
      | throwError "`#leanscript_to_term`: too many arguments for {cur}"
    let next := mkApp cur a
    if ← LeanScript.Deriving.erasedBinder d then
      cur := next
      continue
    let σ ← tyOfType d
    let τ ← tyOfTerm next
    let a' ← trans c a
    t := mkAppN (mkConst ``LeanScript.Term.ap) #[c.sg, c.gamma, σ, τ, t, a']
    cur := next
  return t

/-- A structure projection: the case analysis that binds every field, followed by the
    field that was asked for. -/
partial def transProj (c : TCtx) (e : Expr) : MetaM Expr := do
  let .proj structName idx s := e
    | throwError "`#leanscript_to_term`: internal: not a projection"
  -- a projection out of a closed value — an instance, for one — is that value's field
  unless s.hasFVar do
    let e' ← whnf e
    unless e' == e do return ← trans c e'
  let sty ← tyOfTerm s
  let scrut ← trans c s
  let ind ← getConstInfoInduct structName
  let [ctorName] := ind.ctors
    | throwError "`#leanscript_to_term`: {structName} is not a structure"
  let ci ← getConstInfoCtor ctorName
  -- which of the fields that are kept is this one?
  let params := (← whnf (← inferType s)).getAppArgs
  let keptIdx? ← forallBoundedTelescope (← instantiateForall ci.type params)
      (some ci.numFields) fun xs _ => do
    let mut kept := 0
    let mut hit := none
    for h : i in [0:xs.size] do
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then continue
      if i == idx then hit := some kept
      kept := kept + 1
    return hit
  let some k := keptIdx?
    | throwError "`#leanscript_to_term`: the field {idx} of {structName} carries no \
        value of the language"
  match ← tyView sty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let τ ← tyOfTerm e
      let ids ← fieldTys.mapM fun t => do return ((← mkFreshFVarId), t)
      let c' := c.pushFields ids.toArray
      let some (fid, _) := ids[k]?
        | throwError "`#leanscript_to_term`: the field {idx} of {structName} is not a \
            field of its tree"
      let body ← c'.var fid
      return mkAppN (mkConst ``LeanScript.Term.record_casesOn)
        #[c.sg, c.gamma, τ, fs, scrut, body]
  | _ =>
      -- a one-field structure is its field: the wrapper is erased
      if k == 0 then return scrut
      throwError "`#leanscript_to_term`: cannot project the field {idx} of \
        {structName}"

/-- `do` in the identity monad is not an effect: `Id.run`, `pure`, `>>=` and `<$>` are
    the plumbing a `do` block leaves behind, and each of them is a `let` or an
    application once the monad is `Id`.  A `for` over a range is the one that is not:
    it is a fold, and `transForInRange?` builds it.  In any other monad this answers
    `none`, and the call is refused as any other undeclared call is. -/
partial def transIdOp? (c : TCtx) (n : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let isId (m : Expr) : MetaM Bool := do return m.consumeMData.isConstOf ``Id
  match n with
  | ``Id.run =>
      let some x := args[1]? | return none
      return some (← trans c x)
  | ``Pure.pure =>
      unless args.size == 4 do return none
      unless ← isId args[0]! do return none
      return some (← trans c args[3]!)
  | ``Bind.bind =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[5]! args[4]!).headBeta)
  | ``Functor.map =>
      unless args.size == 6 do return none
      unless ← isId args[0]! do return none
      return some (← trans c (mkApp args[4]! args[5]!).headBeta)
  | ``ForIn.forIn =>
      unless args.size ≥ 8 do return none
      unless ← isId args[0]! do return none
      transForInRange? c args[1]! args[args.size - 3]! args[args.size - 2]! args[args.size - 1]!
  | _ => return none

/-- `for i in [:n] do …`, in the identity monad: the loop is the fold of `n` whose value
    is the state, so it is `Term.nat_rec` — the branch binds the index (de Bruijn index
    `0`) and the state before the iteration (index `1`), and answers with the state
    after it.

    The range must start at `0` and step by `1`, and the body must always `yield`: a
    `break` or a `return` out of the loop would need a state the grammar's fold does not
    carry, and is refused rather than silently ignored. -/
partial def transForInRange? (c : TCtx) (ρ coll init body : Expr) : MetaM (Option Expr) := do
  unless ρ.consumeMData.isConstOf ``Std.Legacy.Range do return none
  let (``Std.Legacy.Range.mk, #[startE, stopE, stepE, _]) := (← whnf coll).getAppFnArgs
    | throwError "`#leanscript_to_term`: the range of this `for` is not written out"
  let some start ← evalNat (← whnf startE) | throwError
    "`#leanscript_to_term`: the range of this `for` does not start at a known number"
  let some step ← evalNat (← whnf stepE) | throwError
    "`#leanscript_to_term`: the range of this `for` does not step by a known number"
  unless start == 0 && step == 1 do
    throwError "`#leanscript_to_term`: a `for` over a range is the fold of its bound, so \
      the range has to start at `0` and step by `1`; this one starts at {start} and \
      steps by {step}"
  let β ← inferType init
  let τ ← tyOfType β
  let natTy ← tyOfType (mkConst ``Nat)
  let scrut ← trans c stopE
  let z ← trans c init
  let branch ← withLocalDeclD `i (mkConst ``Nat) fun i =>
    withLocalDeclD `state β fun s => do
      let stepBody ← whnf (mkApp2 body i s).headBeta
      let stepBody ← match stepBody.getAppFnArgs with
        | (``Pure.pure, #[_, _, _, v]) => whnf v
        | _ => pure stepBody
      let next ← match stepBody.getAppFnArgs with
        | (``ForInStep.yield, #[_, v]) => pure v
        | (``ForInStep.done, #[_, _]) =>
            throwError "`#leanscript_to_term`: this `for` leaves the loop early (`break` \
              or `return`), which the fold a loop becomes cannot express"
        | _ =>
            throwError "`#leanscript_to_term`: the body of this `for` does not yield the \
              state of the next iteration"
      let c' := c.pushFields #[(i.fvarId!, natTy), (s.fvarId!, τ)]
      trans c' next
  return some <| mkAppN (mkConst ``LeanScript.Term.nat_rec)
    #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], branch]

/-- An application whose head is a constant. -/
partial def transConstApp (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  checkConst n
  if let some t ← transIdOp? c n args then return t
  if n == ``ite then return ← transIte c args
  if n == ``dite then
    throwError "`#leanscript_to_term`: `if h : c then …` binds a proof, which the \
      language erases; write the test as a `Bool`"
  if n == ``cond then
    let some scrut := args[1]? | throwError "`#leanscript_to_term`: `cond` needs its test"
    return ← mkBoolCases c (← trans c scrut) args[2]! args[3]!
  if n == ``Thunk.get then
    let some t := args[1]? | throwError "`#leanscript_to_term`: `Thunk.get` needs a thunk"
    let τ ← tyOfTerm e
    return mkAppN (mkConst ``LeanScript.Term.thunk_force) #[c.sg, c.gamma, τ, ← trans c t]
  if n == ``List.toArray || n == ``Array.mk then
    -- an array literal, written as the list of its elements
    return ← transListLit c e
  if n == ``Array.toList then
    throwError "`#leanscript_to_term`: a list and an array are different types here — \
      `List α` is the recursive tagged union it is and `Array α` is `Ty.array` — and \
      the grammar builds an array from all of its elements at once, so there is no \
      term for `Array.toList`"
  if n == ``Nat.brecOn || n == ``List.brecOn then
    return ← transBrecOn c e n lvls args
  if isSparseCasesOn n then
    if let some t ← transSparseCasesOn? c e n lvls args then return t
    -- a type whose tree has no partial dispatch: the exhaustive one, from the unfolding
    if let some e' ← unfoldHere? e then return ← trans c e'
  match (← getEnv).find? n with
  | some (.ctorInfo ci) => return ← transCtorApp c e ci args
  | some (.recInfo ri) => return ← transRecApp c e ri lvls args
  | _ => pure ()
  if (← Meta.isMatcherApp e) || n.getString! == "casesOn" || n.getString! == "recOn" then
    if let some e' ← unfoldHere? e then
      return ← trans c e'
    throwError "`#leanscript_to_term`: cannot take apart the dispatch {n}"
  if let some g := c.global? n then
    let gt := mkAppN (mkConst ``LeanScript.Term.global) #[c.sg, c.gamma, g.ty, g.ref]
    return ← applyArgs c gt (mkConst n lvls) args
  if ← isInlinable n then
    return ← transInline c e n lvls args
  throwError "`#leanscript_to_term`: `{n}` is not declared in the signature and is not \
    inlinable, so a term cannot call it.  Either add a `GlobalDecl` named \
    \"{n.getString!}\" (or \"{n}\") to the signature, or mark `{n}` `@[inline]`."

/-- `if c then t else e`: the test must be a `Bool`. -/
partial def transIte (c : TCtx) (args : Array Expr) : MetaM Expr := do
  let some cnd := args[1]? | throwError "`#leanscript_to_term`: `ite` needs its test"
  let inst := args[2]!
  let test ← boolOfDecidable c cnd inst
  mkBoolCases c test args[3]! args[4]!

/-- The `Bool` a decidable proposition tests. -/
partial def boolOfDecidable (c : TCtx) (cnd : Expr) (inst : Expr) : MetaM Expr := do
  match cnd.getAppFnArgs with
  | (``Eq, #[α, lhs, rhs]) =>
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.true then
        return ← trans c lhs
      if α.isConstOf ``Bool && rhs.isConstOf ``Bool.false then
        let t ← trans c lhs
        return ← mkBoolCases' c t (mkAppN (mkConst ``LeanScript.Term.bool_mk)
            #[c.sg, c.gamma, mkConst ``Bool.false])
          (mkAppN (mkConst ``LeanScript.Term.bool_mk) #[c.sg, c.gamma, mkConst ``Bool.true])
          (← tyOfType (mkConst ``Bool))
      -- `a = b` at a type with a `BEq`: the test is `a == b`
      match ← trySynthInstance (← mkAppM ``BEq #[α]) with
      | .some _ => return ← trans c (← mkAppM ``BEq.beq #[lhs, rhs])
      | _ => pure ()
      throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`"
  | _ =>
      let d ← whnf (mkApp2 (mkConst ``Decidable.decide) cnd inst)
      if d.find? (fun s => s.isConstOf ``Decidable.rec) |>.isSome then
        throwError "`#leanscript_to_term`: the test {cnd} is not a `Bool`: write the \
          condition as a `Bool`, or declare the decision procedure in the signature"
      trans c d

/-- `bool_casesOn`, from the two Lean branches. -/
partial def mkBoolCases (c : TCtx) (test : Expr) (thenB elseB : Expr) : MetaM Expr := do
  let τ ← tyOfTerm thenB
  mkBoolCases' c test (← trans c thenB) (← trans c elseB) τ

/-- `bool_casesOn`, from the two translated branches. -/
partial def mkBoolCases' (c : TCtx) (test t e τ : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``LeanScript.Term.bool_casesOn) #[c.sg, c.gamma, τ, test, t, e]

/-- A list, or an array, written out: every element of it at once. -/
partial def transListLit (c : TCtx) (e : Expr) : MetaM Expr := do
  let ty ← tyOfTerm e
  let .array σ ← tyView ty
    | throwError "`#leanscript_to_term`: {e} is not an array"
  let mut elems : Array Expr := #[]
  let mut cur := e
  repeat
    match cur.getAppFnArgs with
    | (``List.nil, _) => break
    | (``List.cons, #[_, a, as]) => elems := elems.push a; cur := as
    | (``List.toArray, #[_, l]) => cur := l
    | (``Array.mk, #[_, l]) => cur := l
    | _ =>
        throwError "`#leanscript_to_term`: the grammar builds an array from all of its \
          elements at once, so only a list written out can be translated; {cur} is not \
          one"
  let mut ts := mkAppN (mkConst ``LeanScript.Terms.nil) #[c.sg, c.gamma, σ]
  for i in [0:elems.size] do
    let a := elems[elems.size - 1 - i]!
    ts := mkAppN (mkConst ``LeanScript.Terms.cons) #[c.sg, c.gamma, σ, ← trans c a, ts]
  return mkAppN (mkConst ``LeanScript.Term.array_mk) #[c.sg, c.gamma, σ, ts]

/-- The arguments of a constructor that carry a value. -/
partial def ctorValueArgs (ci : ConstructorVal) (args : Array Expr) :
    MetaM (Array Expr) := do
  let fieldArgs := args.extract ci.numParams args.size
  forallBoundedTelescope (← instantiateForall ci.type (args.extract 0 ci.numParams))
      (some ci.numFields) fun xs _ => do
    let mut out := #[]
    for h : i in [0:fieldArgs.size] do
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]!) then continue
      out := out.push fieldArgs[i]
    return out

/-- A spine of arguments at the given trees. -/
partial def mkSpine (c : TCtx) (tys : List Expr) (vals : Array Expr) : MetaM Expr := do
  unless tys.length == vals.size do
    throwError "`#leanscript_to_term`: this constructor carries {vals.size} values but \
      its tree has {tys.length} fields"
  let mut sp := mkAppN (mkConst ``LeanScript.Spine.nil) #[c.sg, c.gamma]
  let tysA := tys.toArray
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    let t ← trans c vals[j]!
    sp := mkAppN (mkConst ``LeanScript.Spine.cons)
      #[c.sg, c.gamma, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- The base values of a fold, already translated, as a `Spine` at `k` copies of `τ` —
    the type `LeanScript.Term.nat_rec` asks its base values at. -/
partial def mkNatRecBase (c : TCtx) (τ : Expr) (vals : Array Expr) : Expr := Id.run do
  let mut sp := mkAppN (mkConst ``LeanScript.Spine.nil) #[c.sg, c.gamma]
  let mut tys : List Expr := []
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    sp := mkAppN (mkConst ``LeanScript.Spine.cons)
      #[c.sg, c.gamma, τ, mkTyListE tys, vals[j]!, sp]
    tys := τ :: tys
  return sp

/-- An application of a constructor: it is built in place. -/
partial def transCtorApp (c : TCtx) (e : Expr) (ci : ConstructorVal)
    (args : Array Expr) : MetaM Expr := do
  if args.size < ci.numParams + ci.numFields then
    return ← trans c (← etaExpand e)
  if ci.induct == ``Array then
    return ← transListLit c e
  let ty ← tyOfTerm e
  let fields ← ctorValueArgs ci args
  -- a delay
  if let .thunk σ ← tyView ty then
    let some body := fields[0]?
      | throwError "`#leanscript_to_term`: a thunk needs its body"
    let inner := (mkApp body (mkConst ``Unit.unit)).headBeta
    return mkAppN (mkConst ``LeanScript.Term.thunk_mk)
      #[c.sg, c.gamma, σ, ← trans c inner]
  -- a one-field wrapper is its field
  if h : fields.size = 1 then
    let fty ← tyOfTerm fields[0]
    if fty == ty then return ← trans c fields[0]
  match ← tyView ty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let spine ← mkSpine c fieldTys fields
      return mkAppN (mkConst ``LeanScript.Term.record_mk) #[c.sg, c.gamma, fs, spine]
  | .taggedUnion l =>
      let ctys ← taggedUnionCtorTys l
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst ``LeanScript.Term.taggedUnion_mk)
        #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
  | .recTaggedUnion l hwf =>
      -- the fields of a value are the payload **unfolded**: a field that is an
      -- occurrence of the union is a value of the union again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf
      let ctys ← taggedUnionCtorTys (← reduceTy unfE)
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_mk)
        #[c.sg, c.gamma, l, hwf, mkNatLit ci.cidx, prf, spine]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      return mkAppN (mkConst ``LeanScript.Term.enum_mk)
        #[c.sg, c.gamma, s, ← mkFinLit nE ci.cidx]
  | .prim _ =>
      if ← isBoolTy ty then
        return mkAppN (mkConst ``LeanScript.Term.bool_mk)
          #[c.sg, c.gamma, toExpr (ci.cidx == 1)]
      throwError "`#leanscript_to_term`: {ci.name} builds a value of a terminal type, \
        which has no constructor in the language; write it as a literal"
  | _ =>
      throwError "`#leanscript_to_term`: the tree of {ci.induct} has no introduction \
        form in the grammar"

/-- A branch of a dispatch: the fields it binds become the innermost variables, the
    first field at index `0`. -/
partial def transBranch (c : TCtx) (minor : Expr) (ctorName : Name)
    (fieldTys : List Expr) : MetaM Expr := do
  let ci ← getConstInfoCtor ctorName
  forallBoundedTelescope (← inferType minor) (some ci.numFields) fun xs _ => do
    let mut keep : Array Expr := #[]
    for x in xs do
      unless ← LeanScript.Deriving.erasedBinder (← inferType x) do
        keep := keep.push x
    unless keep.size == fieldTys.length do
      throwError "`#leanscript_to_term`: the branch of {ctorName} binds {keep.size} \
        values but its tree has {fieldTys.length} fields"
    let c' := c.pushFields ((keep.zip fieldTys.toArray).map fun (x, t) => (x.fvarId!, t))
    trans c' ((mkAppN minor xs).headBeta)

/-- A `match` that names only some of the constructors, as Lean compiled it: the
    auxiliary `f._sparseCasesOn_i`.  Its branches and its `else` branch are the branches
    and the default of the grammar's partial dispatch, so this is where
    `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` and
    `recTaggedUnion_casesOnWithDefault` are built.

    A type whose tree has no partial dispatch — a record, a terminal type, a one-field
    wrapper — is not handled here: the auxiliary is unfolded and the exhaustive dispatch
    is built instead, which is what `none` means. -/
partial def transSparseCasesOn? (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM (Option Expr) := do
  let some (arity, named) ← sparseCasesOnInfo? n | return none
  if args.size < arity then
    return some (← trans c (← etaExpand e))
  let motive ← whnf args[0]!
  unless motive.isLambda do return none
  let major := args[1]!
  let sty ← tyOfTerm major
  -- the grammar has a partial dispatch for a sum type only
  let view ← tyView sty
  match view with
  | .enum _ | .taggedUnion _ | .recTaggedUnion _ _ => pure ()
  | _ => return none
  let .const indName _ := (← whnf (← inferType major)).getAppFn | return none
  let indInfo ← getConstInfoInduct indName
  let ctors := indInfo.ctors.toArray
  if named.length ≥ ctors.size then return none
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    tyOfType body
  -- the branches, by constructor number, and the default
  let mut minors : Array Expr := ctors.map fun _ => (Lean.mkConst ``True)
  for j in [0:named.length] do
    minors := minors.set! named[j]! args[2 + j]!
  let elseArg := args[2 + named.length]!
  let elseTy ← whnf (← inferType elseArg)
  let .forallE _ dom _ _ := elseTy | return none
  let dflt ← withLocalDeclD `h dom fun hv => do
    let b ← whnfCore (mkApp elseArg hv)
    if b.containsFVar hv.fvarId! then
      throwError "`#leanscript_to_term`: the default branch of this `match` uses the \
        proof that the value is none of the constructors named, which the language \
        erases"
    return b
  let dfltTerm ← trans c dflt
  let scrut ← trans c major
  let kE := mkNatLit named.length
  let core ← match view with
    | .enum s =>
        let cases ← mkEnumSomeCases c τ s named 0 minors ctors
        let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, nE])
        pure <| mkAppN (mkConst ``LeanScript.Term.enum_casesOnWithDefault)
          #[c.sg, c.gamma, τ, s, kE, scrut, cases, dfltTerm, hk]
    | .taggedUnion l =>
        let cases ← mkTaggedUnionSomeCases c τ l named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, kE, scrut, cases, dfltTerm, hk]
    | .recTaggedUnion l hwf =>
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf)
        let cases ← mkTaggedUnionSomeCases c τ unfE named 0 minors ctors
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
        let hk ← mkDecideProof (← mkAppM ``LT.lt #[kE, lenE])
        pure <| mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_casesOnWithDefault)
          #[c.sg, c.gamma, τ, l, hwf, kE, scrut, cases, dfltTerm, hk]
    | _ => return none
  let extra := args.extract arity args.size
  if extra.isEmpty then return some core
  return some (← applyArgs c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra)

/-- A structural recursion as Lean compiled it: `Nat.brecOn` or `List.brecOn`.

    The branch of a `brecOn` is given the **history** of the recursion — the value of the
    function at every smaller argument — and the grammar's folds give it the value at the
    immediate predecessor only.  So the history is reduced away here: the branch is
    instantiated at the two constructors of its type, with the head of the history
    replaced by a variable standing for the value at the predecessor, and what is left is
    the pair of branches of `Nat.rec` / `List.rec`, which
    `LeanScript.ToTerm.transRecCore` turns into `nat_rec` / `recTaggedUnion_rec` (or the
    case analysis, when the branch does not use that value).

    On a `Nat` the depth is not fixed at one.  If the branch at `n + 1` reads more of the
    history than its head, the depths `1, 2, …` are tried in turn: at depth `k` the
    branch is instantiated at `n + k + 1` with the `k + 1` nearest entries of the history
    replaced by variables, and the first depth at which nothing of the history is left is
    the depth of the `nat_rec` that is built — with the answers below it, the branch at
    `0, …, k`, as its base values.  A recursion that reads the history at an argument
    that is not a fixed number of steps back is refused. -/
partial def transBrecOn (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let isNat := n == ``Nat.brecOn
  let mIdx := if isNat then 0 else 1
  let arity := mIdx + 3
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[mIdx]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  let major := args[mIdx + 1]!
  let brecF := args[mIdx + 2]!
  let τLean ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    return body
  let τ ← tyOfType τLean
  let brecFTy ← inferType brecF
  -- the type of the history at a given argument
  let historyTy (t : Expr) : MetaM Expr := do
    return (← whnf (← instantiateForall brecFTy #[t])).bindingDomain!
  -- the branch at a constructor, with the head of the history read as `ih`
  let branchAt (scrutinee : Expr) (ih? : Option Expr) : MetaM Expr := do
    let ht ← historyTy scrutinee
    withLocalDeclD `history ht fun hist => do
      let body ← reduceBrecBodyDeep (mkApp2 brecF scrutinee hist)
      let body := match ih? with
        | some ih => substHistoryHead body hist.fvarId! ih
        | none => body
      if body.containsFVar hist.fvarId! then
        throwError "`#leanscript_to_term`: this recursion reads the value of the \
          function at an argument that is not the immediate predecessor, and the \
          grammar's folds descend one step at a time"
      return body
  -- what to do with the arguments a saturated `brecOn` is applied to on top of its own
  let finish (core : Expr) : MetaM Expr := do
    let extra := args.extract arity args.size
    if extra.isEmpty then return core
    applyArgs c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra
  if isNat then
    -- one step first: that is `Nat.rec`, and `transRecCore` may still turn it into the
    -- case analysis when the branch does not use the value of the fold
    let depth0? : Option (Array Expr) ←
      try
        let z ← branchAt (mkConst ``Nat.zero) none
        let s ← withLocalDeclD `n (mkConst ``Nat) fun nv =>
          withLocalDeclD `ih τLean fun ih => do
            let body ← branchAt (mkApp (mkConst ``Nat.succ) nv) (some ih)
            mkLambdaFVars #[nv, ih] body
        pure (some #[z, s])
      catch _ => pure none
    if let some minors := depth0? then
      let some (.recInfo ri) := (← getEnv).find? ``Nat.rec
        | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
      return ← finish (← transRecCore c ri τ minors major)
    -- more than one step: the branch at `n + k + 1`, with the `k + 1` nearest answers
    -- read out of the history and bound as `ih₀, …, ihₖ` — nearest first
    let stepAt (k : Nat) : MetaM Expr :=
      withLocalDeclD `n (mkConst ``Nat) fun nv => do
        let mut scrutE := nv
        for _ in [0:k + 1] do scrutE := mkApp (mkConst ``Nat.succ) scrutE
        let ihDecls : Array (Name × (Array Expr → MetaM Expr)) :=
          (Array.range (k + 1)).map fun i =>
            (Name.mkSimple s!"ih{i}", fun _ => pure τLean)
        withLocalDeclsD ihDecls fun ihs => do
          let ht ← historyTy scrutE
          withLocalDeclD `history ht fun hist => do
            let body ← reduceBrecBodyDeep (mkApp2 brecF scrutE hist)
            let body := substHistory body hist.fvarId! ihs
            if body.containsFVar hist.fvarId! then
              throwError "`#leanscript_to_term`: this recursion reads the value of the \
                function at an argument that is not one of its {k + 1} nearest \
                predecessors"
            mkLambdaFVars (#[nv] ++ ihs) body
    let mut found : Option (Nat × Expr) := none
    for k in [1:maxNatRecDepth + 1] do
      if found.isNone then
        found ← try pure (some (k, ← stepAt k)) catch _ => pure none
    let some (k, s) := found
      | throwError "`#leanscript_to_term`: this recursion does not descend by a fixed \
          number of steps — the fold of a natural number the grammar has gives its branch \
          the answers at the `k + 1` nearest predecessors, so a call at an argument such \
          as `n / 2` has no term"
    -- the answers below the depth: the branch at `0, …, k`, each one allowed to read the
    -- answers already known
    let mut baseVals : Array Expr := #[]
    for j in [0:k + 1] do
      let mut jE : Expr := mkConst ``Nat.zero
      for _ in [0:j] do jE := mkApp (mkConst ``Nat.succ) jE
      let ht ← historyTy jE
      let v ← withLocalDeclD `history ht fun hist => do
        let body ← reduceBrecBodyDeep (mkApp2 brecF jE hist)
        let body := substHistory body hist.fvarId! baseVals.reverse
        if body.containsFVar hist.fvarId! then
          throwError "`#leanscript_to_term`: the answer at {j} reads the value of the \
            function at an argument the fold has not computed yet"
        pure body
      baseVals := baseVals.push v
    let scrutT ← trans c major
    let natTy ← tyOfType (mkConst ``Nat)
    -- the base values are written nearest first: `(f k, …, f 1, f 0)`
    let baseTerms ← baseVals.reverse.mapM fun v => trans c v
    let base := mkNatRecBase c τ baseTerms
    let core ← lambdaBoundedTelescope s (k + 2) fun xs body => do
      let c' := c.pushFields
        (#[(xs[0]!.fvarId!, natTy)] ++ (xs.extract 1 xs.size).map fun x => (x.fvarId!, τ))
      return mkAppN (mkConst ``LeanScript.Term.nat_rec)
        #[c.sg, c.gamma, τ, mkNatLit k, scrutT, base, ← trans c' body]
    return ← finish core
  let minors ←
    do
      let α := args[0]!
      let listTy := mkApp (mkConst ``List [← getDecLevel α]) α
      let nil := mkApp (mkConst ``List.nil [← getDecLevel α]) α
      let z ← branchAt nil none
      let s ← withLocalDeclD `head α fun hd =>
        withLocalDeclD `tail listTy fun tl =>
          withLocalDeclD `ih τLean fun ih => do
            let cons := mkApp3 (mkConst ``List.cons [← getDecLevel α]) α hd tl
            let body ← branchAt cons (some ih)
            mkLambdaFVars #[hd, tl, ih] body
      pure #[z, s]
  let some (.recInfo ri) := (← getEnv).find? ``List.rec
    | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
  finish (← transRecCore c ri τ minors major)

/-- An application of a recursor. -/
partial def transRecApp (c : TCtx) (e : Expr) (ri : RecursorVal) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  unless ri.numMotives == 1 && ri.numIndices == 0 do
    throwError "`#leanscript_to_term`: {ri.name} is not an eliminator the language has"
  let arity := ri.numParams + 1 + ri.numMinors + 1
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[ri.numParams]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {ri.name} is not a function"
  let τ ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {ri.name} is used with a dependent motive, \
        which the language has no eliminator for"
    tyOfType body
  let minors := args.extract (ri.numParams + 1) (ri.numParams + 1 + ri.numMinors)
  let major := args[ri.numParams + 1 + ri.numMinors]!
  let core ← transRecCore c ri τ minors major
  let extra := args.extract arity args.size
  if extra.isEmpty then return core
  applyArgs c core (mkAppN (mkConst ri.name lvls) (args.extract 0 arity)) extra

/-- The eliminator a recursor becomes. -/
partial def transRecCore (c : TCtx) (ri : RecursorVal) (τ : Expr) (minors : Array Expr)
    (major : Expr) : MetaM Expr := do
  let ind := ri.getMajorInduct

  let scrut ← trans c major
  match ind with
  | ``Nat =>
      -- the fold, or the case analysis when the branch does not use the recursive value
      let natTy ← tyOfType (mkConst ``Nat)
      let z ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 2) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[1]!.fvarId! then
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy), (xs[1]!.fvarId!, τ)]
          return mkAppN (mkConst ``LeanScript.Term.nat_rec)
            #[c.sg, c.gamma, τ, mkNatLit 0, scrut, mkNatRecBase c τ #[z], ← trans c' body]
        else
          let c' := c.pushFields #[(xs[0]!.fvarId!, natTy)]
          return mkAppN (mkConst ``LeanScript.Term.nat_casesOn)
            #[c.sg, c.gamma, τ, scrut, z, ← trans c' body]
  | ``List =>
      let sty ← tyOfTerm major
      let .recTaggedUnion l hwf ← tyView sty
        | throwError "`#leanscript_to_term`: {major} is not a list"
      let (cp, fieldsNE, restL) ← listSchemaParts l
      -- the head of the payload is written in the scope the binder opens; as a *value*
      -- of the language it is that tree, unfolded — which for an element type that is
      -- not an occurrence is the tree itself
      let σ ← match ← nonEmptyTys fieldsNE with
        | [σ, _] => bundleTyE 0 (← treeOfTyE σ)
        | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
      let nil ← trans c minors[0]!
      forallBoundedTelescope (← inferType minors[1]!) (some 3) fun xs _ => do
        let body := (mkAppN minors[1]! xs).headBeta
        if body.containsFVar xs[2]!.fvarId! then
          -- the fold: the branch is given the value of the fold at the tail
          let c' := c.pushFields
            #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty), (xs[2]!.fvarId!, τ)]
          let bindE := mkApp2 (mkConst ``LeanScript.TyWf.recBinders) sty τ
          let ι := tyWfInE 1
          let restCases := mkAppN (mkConst ``LeanScript.TaggedUnionFoldCasesRest.nil)
            #[c.sg, ι, bindE, c.gamma, τ]
          let consCases := mkAppN (mkConst ``LeanScript.CtorsWithPayloadFoldCases.here)
            #[c.sg, ι, bindE, c.gamma, τ, fieldsNE, restL, ← trans c' body, restCases]
          let cases := mkAppN (mkConst ``LeanScript.TaggedUnionFoldCases.skip)
            #[c.sg, ι, bindE, c.gamma, τ, cp, nil, consCases]
          return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_rec)
            #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
        else
          -- the case analysis: the branches are over the unfolded schema, in which the
          -- tail is a list again
          let (cpU, fieldsU, restU) ←
            listSchemaParts (← reduceTy
              (mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf))
          let c' := c.pushFields #[(xs[0]!.fvarId!, σ), (xs[1]!.fvarId!, sty)]
          let restCases := mkAppN (mkConst ``LeanScript.TaggedUnionCasesRest.nil)
            #[c.sg, c.gamma, τ]
          let consCases := mkAppN (mkConst ``LeanScript.CtorsWithPayloadCases.here)
            #[c.sg, c.gamma, τ, fieldsU, restU, ← trans c' body, restCases]
          let cases := mkAppN (mkConst ``LeanScript.TaggedUnionCases.skip)
            #[c.sg, c.gamma, τ, cpU, nil, consCases]
          return mkAppN (mkConst ``LeanScript.Term.recTaggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, hwf, scrut, cases]
  | ``Bool =>
      return mkAppN (mkConst ``LeanScript.Term.bool_casesOn)
        #[c.sg, c.gamma, τ, scrut, ← trans c minors[1]!, ← trans c minors[0]!]
  | _ =>
      let indInfo ← getConstInfoInduct ind
      if indInfo.isRec then
        throwError "`#leanscript_to_term`: {ind} is a recursive type, and the only folds \
          the translation produces are `nat_rec` and `recTaggedUnion_rec`, for `Nat` and \
          `List`"
      let sty ← tyOfTerm major
      let ctors := indInfo.ctors.toArray
      match ← tyView sty with
      | .record fs =>
          let fieldTys ← recordFieldTys fs
          let body ← transBranch c minors[0]! ctors[0]! fieldTys
          return mkAppN (mkConst ``LeanScript.Term.record_casesOn)
            #[c.sg, c.gamma, τ, fs, scrut, body]
      | .taggedUnion l =>
          -- a `match` with a wildcard repeats one branch: that is the partial dispatch
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkTaggedUnionSomeCases c τ l named 0 minors ctors
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, lenE])
            return mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOnWithDefault)
              #[c.sg, c.gamma, τ, l, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkTaggedUnionCases c τ l 0 minors ctors
          return mkAppN (mkConst ``LeanScript.Term.taggedUnion_casesOn)
            #[c.sg, c.gamma, τ, l, scrut, cases]
      | .enum s =>
          if let some (dflt, group) ← repeatedBranch? minors ctors then
            let named := (List.range ctors.size).filter (fun i => !group.contains i)
            let cases ← mkEnumSomeCases c τ s named 0 minors ctors
            let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
            let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit named.length, nE])
            return mkAppN (mkConst ``LeanScript.Term.enum_casesOnWithDefault)
              #[c.sg, c.gamma, τ, s, mkNatLit named.length, scrut, cases,
                ← trans c dflt, hk]
          let cases ← mkEnumCases c τ s minors ctors
          return mkAppN (mkConst ``LeanScript.Term.enum_casesOn)
            #[c.sg, c.gamma, τ, s, scrut, cases]
      | .prim _ =>
          if (← isBoolTy sty) && minors.size == 2 then
            return mkAppN (mkConst ``LeanScript.Term.bool_casesOn)
              #[c.sg, c.gamma, τ, scrut, ← transBranch c minors[1]! ctors[1]! [],
                ← transBranch c minors[0]! ctors[0]! []]
          throwError "`#leanscript_to_term`: a terminal type has no dispatch of its own"
      | _ =>
          if minors.size == 1 then
            -- a one-field wrapper: its case analysis substitutes the value
            return ← transBranch c minors[0]! ctors[0]! [← tyOfTerm major]
          throwError "`#leanscript_to_term`: the tree of {ind} has no dispatch in the \
            grammar"

/-- The branches of a **partial** dispatch on a tagged union: the constructors `named`,
    in increasing order, each binding its fields.  `lo` is the smallest constructor a
    branch may still name, which is what keeps the list in order. -/
partial def mkTaggedUnionSomeCases (c : TCtx) (τ l : Expr) (named : List Nat) (lo : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  let ctys ← taggedUnionCtorTys l
  let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
  let branchOf (t : Nat) : MetaM (Expr × Expr) := do
    let some fieldTys := ctys[t]?
      | throwError "`#leanscript_to_term`: the tree of the dispatched type has no \
          constructor {t}"
    let ht ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit t, lenE])
    return (ht, ← transBranch c minors[t]! ctors[t]! fieldTys)
  match named with
  | [] =>
      throwError "`#leanscript_to_term`: internal: a partial dispatch names no \
        constructor"
  | [t] =>
      let (ht, branch) ← branchOf t
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit t])
      return mkAppN (mkConst ``LeanScript.TaggedUnionSomeCases.last)
        #[c.sg, c.gamma, l, τ, mkNatLit lo, mkNatLit t, ht, branch, hi]
  | t :: rest =>
      let (ht, branch) ← branchOf t
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit t])
      let restCases ← mkTaggedUnionSomeCases c τ l rest (t + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.TaggedUnionSomeCases.cons)
        #[c.sg, c.gamma, l, τ, mkNatLit rest.length, mkNatLit lo, mkNatLit t, ht, branch,
          restCases, hi]

/-- The branches of a **partial** dispatch on an enum: the constructors `named`, in
    increasing order. -/
partial def mkEnumSomeCases (c : TCtx) (τ s : Expr) (named : List Nat) (lo : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
  match named with
  | [] =>
      throwError "`#leanscript_to_term`: internal: a partial dispatch names no \
        constructor"
  | [i] =>
      let iE ← mkFinLit nE i
      let branch ← transBranch c minors[i]! ctors[i]! []
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit i])
      return mkAppN (mkConst ``LeanScript.EnumSomeCases.last)
        #[c.sg, c.gamma, τ, s, mkNatLit lo, iE, branch, hi]
  | i :: rest =>
      let iE ← mkFinLit nE i
      let branch ← transBranch c minors[i]! ctors[i]! []
      let hi ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit lo, mkNatLit i])
      let restCases ← mkEnumSomeCases c τ s rest (i + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.EnumSomeCases.cons)
        #[c.sg, c.gamma, τ, s, mkNatLit rest.length, mkNatLit lo, iE, branch, restCases,
          hi]

/-- The branches of a dispatch on a tagged union, in the shape of its schema. -/
partial def mkTaggedUnionCases (c : TCtx) (τ l : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf l).getAppFnArgs with
  | (``LeanScript.LeanTaggedUnionSchema.payloadFirst, #[_, fields, next, rest]) =>
      let f0 ← nonEmptyTys fields
      let f1 ← listOfExpr next
      let b0 ← transBranch c minors[start]! ctors[start]! f0
      let b1 ← transBranch c minors[start + 1]! ctors[start + 1]! f1
      let restCases ← mkTaggedUnionRest c τ rest (start + 2) minors ctors
      return mkAppN (mkConst ``LeanScript.TaggedUnionCases.payloadFirst)
        #[c.sg, c.gamma, τ, fields, next, rest, b0, b1, restCases]
  | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, rest]) =>
      let b0 ← transBranch c minors[start]! ctors[start]! []
      let restCases ← mkCtorsWithPayloadCases c τ rest (start + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.TaggedUnionCases.skip)
        #[c.sg, c.gamma, τ, rest, b0, restCases]
  | _ => throwError "`#leanscript_to_term`: not a tagged-union schema: {l}"

/-- The branches of the constructors a `CtorsWithPayload` holds. -/
partial def mkCtorsWithPayloadCases (c : TCtx) (τ cp : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf cp).getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) =>
      let b ← transBranch c minors[start]! ctors[start]! (← nonEmptyTys fields)
      let restCases ← mkTaggedUnionRest c τ rest (start + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.CtorsWithPayloadCases.here)
        #[c.sg, c.gamma, τ, fields, rest, b, restCases]
  | (``LeanScript.CtorsWithPayload.skip, #[_, rest]) =>
      let b ← transBranch c minors[start]! ctors[start]! []
      let restCases ← mkCtorsWithPayloadCases c τ rest (start + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.CtorsWithPayloadCases.skip)
        #[c.sg, c.gamma, τ, rest, b, restCases]
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {cp}"

/-- The branches of the constructors a schema leaves as a plain list. -/
partial def mkTaggedUnionRest (c : TCtx) (τ rest : Expr) (start : Nat)
    (minors : Array Expr) (ctors : Array Name) : MetaM Expr := do
  match (← whnf rest).getAppFnArgs with
  | (``List.nil, _) =>
      return mkAppN (mkConst ``LeanScript.TaggedUnionCasesRest.nil) #[c.sg, c.gamma, τ]
  | (``List.cons, #[_, fs, more]) =>
      let b ← transBranch c minors[start]! ctors[start]! (← listOfExpr fs)
      let restCases ← mkTaggedUnionRest c τ more (start + 1) minors ctors
      return mkAppN (mkConst ``LeanScript.TaggedUnionCasesRest.cons)
        #[c.sg, c.gamma, τ, fs, more, b, restCases]
  | _ => throwError "`#leanscript_to_term`: not a list of constructors: {rest}"

/-- The branches of a dispatch on an enum, in the shape of its schema. -/
partial def mkEnumCases (c : TCtx) (τ s : Expr) (minors : Array Expr)
    (ctors : Array Name) : MetaM Expr := do
  let (extra, shift) ← match (← whnf s).getAppFnArgs with
    | (``LeanScript.LeanEnumSchema.mk, #[e, sh]) => pure (← natOfExpr e, sh)
    | _ => throwError "`#leanscript_to_term`: not an enum schema: {s}"
  let rec go (i : Nat) (k : Nat) : MetaM Expr := do
    if k == 0 then
      let b0 ← transBranch c minors[i]! ctors[i]! []
      let b1 ← transBranch c minors[i + 1]! ctors[i + 1]! []
      let b2 ← transBranch c minors[i + 2]! ctors[i + 2]! []
      return mkAppN (mkConst ``LeanScript.EnumCases.three)
        #[c.sg, c.gamma, τ, shift, b0, b1, b2]
    else
      let b ← transBranch c minors[i]! ctors[i]! []
      let rest ← go (i + 1) (k - 1)
      return mkAppN (mkConst ``LeanScript.EnumCases.cons)
        #[c.sg, c.gamma, τ, mkNatLit (k - 1), shift, b, rest]
  go 0 extra

/-- A call of an inlinable function: its definition is translated, once, and used
    here. -/
partial def transInline (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let info ← getConstInfo n
  let some val := info.value? |
    throwError "`#leanscript_to_term`: `{n}` has no definition to inline"
  let val := val.instantiateLevelParams info.levelParams lvls
  -- how many leading arguments does the language erase?
  let nLeading ← forallTelescopeReducing info.type fun xs _ => do
    let mut k := 0
    for h : i in [0:xs.size] do
      if i ≥ args.size then break
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]) then k := k + 1 else break
    return k
  let leading := args.extract 0 nLeading
  let headVal := (mkAppN val leading).headBeta
  if headVal.hasFVar || headVal.hasMVar then
    let some e' ← unfoldHere? e
      | throwError "`#leanscript_to_term`: cannot inline `{n}`"
    return ← trans c e'
  let t ← transClosedCached c headVal
  applyArgs c t (mkAppN (mkConst n lvls) leading) (args.extract nLeading args.size)

/-- Translate a closed definition, once: the translation is stored as a function of the
    context, and two definitions of the same shape share one tree. -/
partial def transClosedCached (c : TCtx) (v : Expr) : MetaM Expr := do
  if v.hasFVar || v.hasMVar then return ← trans c v
  let st ← cacheRef.get
  if let some entry := st.entries.find? fun en => en.sg == c.sg && en.src == v then
    cacheRef.modify fun s => { s with hits := s.hits + 1 }
    return mkApp entry.fn c.gamma
  let fn ← withLocalDeclD `Γ ctxE fun g => do
    let t ← trans { c with base := g, binders := #[] } v
    mkLambdaFVars #[g] t
  let h := fn.hash
  let st ← cacheRef.get
  let shared? := st.entries.find? fun en => en.hash == h && en.fn == fn
  let fn := match shared? with | some en => en.fn | none => fn
  cacheRef.modify fun s =>
    { s with
      entries := s.entries.push { sg := c.sg, src := v, fn := fn, hash := h },
      shared := if shared?.isSome then s.shared + 1 else s.shared }
  return mkApp fn c.gamma

end

/-! ## The elaborator -/

/-- The empty signature, as an expression. -/
def emptySigE : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``LeanScript.GlobalDecl)
  mkApp2 (mkConst ``LeanScript.Sig.mk) nil
    (mkApp2 (mkConst ``rfl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- The signature and the context the expected type asks for. -/
def sigAndCtxOf? (expected? : Option Expr) : MetaM (Expr × Expr) := do
  match expected? with
  | none => return (emptySigE, nilCtxE)
  | some t =>
    match (← whnf (← instantiateMVars t)).getAppFnArgs with
    | (``LeanScript.Term, #[sg, γ, _]) => return (sg, γ)
    | _ => return (emptySigE, nilCtxE)

/-- Translate `e` — the value of a definition, or an expression written out. -/
def translate (sg base : Expr) (e : Expr) : MetaM Expr := do
  let globals ← parseSig sg
  let c : TCtx := { sg := sg, globals := globals, base := base }
  match e with
  | .const n lvls =>
      checkConst n
      let info ← getConstInfo n
      let some val := info.value?
        | throwError "`#leanscript_to_term`: `{n}` has no definition to translate"
      transClosedCached c (val.instantiateLevelParams info.levelParams lvls)
  | _ => trans c e

/-- `#leanscript_to_term e`: the `LeanScript.Term` that means what the Lean definition
    `e` means.  See this module's header.

    The signature the translation resolves top-level names against is the one of the
    expected type; `#leanscript_to_term (sig := s) e` names it instead, which is what
    lets the type of the translation be *inferred* rather than written out. -/
syntax (name := leanscriptToTerm) "#leanscript_to_term " ("(" &"sig" " := " term ")")?
  term : term

@[term_elab leanscriptToTerm]
def elabLeanscriptToTerm : TermElab := fun stx expected? => do
  let sigStx := stx[1]
  let arg := stx[2]
  let e ← instantiateMVars (← elabTerm arg none)
  let (sgOfExpected, base) ← sigAndCtxOf? expected?
  let sg ← if sigStx.isNone then pure sgOfExpected else
    instantiateMVars (← elabTerm sigStx[3] (mkConst ``LeanScript.Sig))
  let t ← translate sg base e
  match expected? with
  | some ty => ensureHasType ty t
  | none => return t

/-- `#leanscript_to_term_cache_stats`: how many definitions the translation cache holds,
    how often one was reused, and how often two definitions turned out to have the same
    shape and were merged into one tree. -/
syntax (name := toTermCacheStats) "#leanscript_to_term_cache_stats" : command

@[command_elab toTermCacheStats]
def elabToTermCacheStats : Command.CommandElab := fun _ => do
  let st ← cacheRef.get
  logInfo m!"entries: {st.entries.size}, hits: {st.hits}, shape merges: {st.shared}"

/-- `#leanscript_to_term_cache_clear`: empty the translation cache. -/
syntax (name := toTermCacheClear) "#leanscript_to_term_cache_clear" : command

@[command_elab toTermCacheClear]
def elabToTermCacheClear : Command.CommandElab := fun _ => cacheRef.set {}

end LeanScript.ToTerm

end

end
