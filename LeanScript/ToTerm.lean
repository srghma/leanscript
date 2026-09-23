module

public meta import Lean
public meta import LeanScript.Expr
public meta import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving

@[expose] public section

meta section

/-!
# `#leanscript_to_term`: a Lean definition, as a `Term`

```lean
def addOne (n : Nat) : Nat := n + 1   -- with `add` declared in the signature

def addOne_term : Term sg [] (Ty.prim .nat ⇒ Ty.prim .nat) :=
  #leanscript_to_term addOne
```

`#leanscript_to_term e` reads the Lean definition `e` and builds the `LeanScript.Term`
that means the same thing.  It is a **term** elaborator, so the type it is checked
against says which signature and which context the term is written in: the expected type
must be a `LeanScript.Term Sg Γ τ`, and `Sg` is the signature the translation resolves
top-level names against.  With no expected type the empty signature and the empty
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
| a list or array literal | `array_mk` |
| `Thunk.mk (fun _ => e)`, `t.get` | `thunk_mk`, `thunk_force` |
| `match`, `X.casesOn`, a projection | `record_casesOn`, `taggedUnion_casesOn`, `enum_casesOn`, `bool_casesOn`, `array_casesOn`, `nat_casesOn` |
| `Nat.rec`, `List.rec` (non-dependent motive) | `nat_rec`, `array_rec` |
| a name of the signature | `global` |

**Lists and arrays are the same type here.**  The grammar's `Ty.array` is the one
sequence it has an introduction form for, so the translator models Lean's `List α` *and*
`Array α` by `Ty.array`.  (The `LeanScriptTyWf (List α)` instance models a list as the
recursive tagged union it is; `Term` has no introduction form for a recursive shape, so
a translated definition uses the array model instead.)

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
* structural recursion compiled through `brecOn`: the two folds the grammar has are
  `nat_rec` and `array_rec`, so a recursive definition is translated when it is written
  as `Nat.rec` or `List.rec` with a non-dependent motive, and refused otherwise.
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
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## Expressions of the object language -/

/-- The type `LeanScript.Ty`, as an expression. -/
def tyE : Expr := mkConst ``LeanScript.Ty

/-- The type `LeanScript.Ctx = List Ty`, as an expression. -/
def ctxE : Expr := mkApp (mkConst ``List [levelZero]) tyE

/-- The empty context, as an expression. -/
def nilCtxE : Expr := mkApp (mkConst ``List.nil [levelZero]) tyE

/-- `τ :: Γ`, as an expression. -/
def consCtxE (t rest : Expr) : Expr :=
  mkApp3 (mkConst ``List.cons [levelZero]) tyE t rest

/-- The context `ts ++ base`, with `ts` innermost first. -/
def mkCtxE (ts : List Expr) (base : Expr) : Expr := ts.foldr consCtxE base

/-- `@id Ty`, the projection the variable scopes use. -/
def idTyE : Expr := mkApp (mkConst ``id [levelOne]) tyE

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
  /-- Anything else — a recursive binder or an occurrence. -/
  | other

/-- The node a reduced tree is. -/
def tyView (t : Expr) : TyView :=
  match t.getAppFnArgs with
  | (``LeanScript.Ty.shape, #[s]) =>
    match s.getAppFnArgs with
    | (``LeanScript.TyShape.prim, #[_, p]) => .prim p
    | (``LeanScript.TyShape.fn, #[_, a, b]) => .fn a b
    | (``LeanScript.TyShape.enum, #[_, e]) => .enum e
    | (``LeanScript.TyShape.record, #[_, fs]) => .record fs
    | (``LeanScript.TyShape.taggedUnion, #[_, l]) => .taggedUnion l
    | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      match c.getAppFnArgs with
      | (``LeanScript.LeanPrimTyCovariant.array, #[_, a]) => .array a
      | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, a]) => .thunk a
      | (``LeanScript.LeanPrimTyCovariant.lazy, #[_, a]) => .lazy a
      | _ => .other
    | _ => .other
  | _ => .other

/-- Is this tree the terminal type `bool`? -/
def isBoolTy (t : Expr) : Bool :=
  match tyView t with
  | .prim p => p.isConstOf ``LeanScript.LeanPrimTy.bool
  | _ => false

/-! ## The tree that models a Lean type -/

/-- The tree of the language that models the Lean type `α`, reduced.

    `List α` and `Array α` are both `Ty.array`; a non-dependent function type is
    `Ty.fn`; everything else is the type's `LeanScript.LeanScriptTyWf` instance. -/
partial def tyOfType (α : Expr) : MetaM Expr := do
  let α' ← whnf α
  match α'.getAppFnArgs with
  | (``List, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.array) (← tyOfType β))
  | (``Array, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.array) (← tyOfType β))
  | (``Thunk, #[β]) =>
      reduceTy (mkApp (mkConst ``LeanScript.Ty.thunk) (← tyOfType β))
  | _ =>
    match α' with
    | .forallE _ d b _ =>
        if b.hasLooseBVar 0 then
          throwError "`#leanscript_to_term`: the language has no dependent function \
            type, so {α} cannot be translated"
        else
          reduceTy (mkApp2 (mkConst ``LeanScript.Ty.fn) (← tyOfType d) (← tyOfType b))
    | _ => do
      let cls ← mkAppM ``LeanScript.LeanScriptTyWf #[α']
      match ← trySynthInstance cls with
      | .some inst => reduceTy (← mkAppOptM ``LeanScript.tyOf #[α', inst])
      | _ =>
        throwError "`#leanscript_to_term`: the type {α} has no tree of the language \
          (no `LeanScriptTyWf` instance); derive one with `deriving LeanScriptTyWf`"

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
  for h : i in [0:cells.size] do
    let (d, ds) := cells[i]!
    let dv ← whnf d
    let some (name, ty) ← pure (match dv.getAppFnArgs with
      | (``LeanScript.GlobalDecl.mk, #[n, t]) => some (n, t)
      | _ => none)
      | throwError "`#leanscript_to_term`: a declaration of the signature is not \
          written out: {d}"
    let some nameStr := (← whnf name).stringLit?
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

/-- What the cache holds, and what it has done. -/
structure CacheState where
  /-- The definitions translated so far. -/
  entries : Array CacheEntry := #[]
  /-- How often a definition was found already translated. -/
  hits : Nat := 0
  /-- How often a *new* definition turned out to have the shape of one already
      translated, and was replaced by it. -/
  shared : Nat := 0

/-- The cache of translated definitions.  It survives between calls of
    `#leanscript_to_term`, so a function called from two definitions is translated
    once. -/
initialize cacheRef : IO.Ref CacheState ← IO.mkRef {}

/-! ## What may be translated at all -/

/-- The constants that stand for a recursion the language does not have. -/
def rejectedRecursion : List (Name × String) :=
  [ (``WellFounded.fix, "well-founded recursion"),
    (``WellFounded.fixF, "well-founded recursion"),
    (``Acc.rec, "recursion on an accessibility proof"),
    (``WellFoundedRecursion.fix, "well-founded recursion") ]

/-- Is this the compiled form of a structural recursion — `X.brecOn`, `X.binductionOn`,
    the `below` motive, or the unsafe companion of a `partial` definition? -/
def isCompiledRecursion (n : Name) : Bool :=
  let s := n.getString!
  s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
    s == "_unsafe_rec" || s == "fix" && n.getPrefix == `Lean.Order

/-- Refuse a constant the language has no total value for. -/
def checkConst (n : Name) : MetaM Unit := do
  if let some (_, what) := rejectedRecursion.find? (·.1 == n) then
    throwError "`#leanscript_to_term`: {what} ({n}) is not supported — the grammar's \
      only folds are `nat_rec` and `array_rec`, so write the recursion as `Nat.rec` or \
      `List.rec` with a non-dependent motive"
  if isCompiledRecursion n then
    throwError "`#leanscript_to_term`: {n} is the compiled form of a recursion the \
      grammar cannot express — write the recursion as `Nat.rec` or `List.rec` with a \
      non-dependent motive, which are `nat_rec` and `array_rec`"
  match ← getConstInfo n with
  | .defnInfo d =>
      if d.safety == .partial then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      if d.safety == .unsafe then
        throwError "`#leanscript_to_term`: `{n}` is `unsafe`"
  | .opaqueInfo _ =>
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
  if (← Meta.getReducibilityStatus n) matches .reducible then return true
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

end LeanScript.ToTerm

end

end
