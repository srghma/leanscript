module

public meta import Lean
public meta import LeanScript.Ty.Class
public meta import LeanScript.Ty.WfTactic

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
  language has.

## The same tree is stored once

Before adding anything the handler looks the tree up in a table of the trees this project
has already built — the table is an environment extension, so it spans modules.  Two
declarations with the same tree (two `mutual` families that differ only in their names,
say) share one `…leanScriptTyOf` constant and one proof: the second declaration adds an
instance and nothing else.
-/

/-! ## The table of trees already built -/

/-- A tree this project has already built, with the constant it was stored in and the
    theorem that it is a type. -/
structure SharedTy where
  /-- The hash of the tree, which is what the lookup is keyed on. -/
  hash : UInt64
  /-- The `def` holding the tree. -/
  declName : Name
  /-- The `theorem` that it is a type. -/
  wfName : Name
  deriving Inhabited, DecidableEq, BEq, ReflBEq, LawfulBEq

/-- Every tree `deriving LeanScriptTyWf` has built, in this module and in every module it
    imports.  Sharing spans modules because this does. -/
initialize sharedTyExt : SimplePersistentEnvExtension SharedTy (Array SharedTy) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.flatten }

/-- The constants holding this tree, if some declaration has already been given it. -/
def findShared? (value : Expr) : MetaM (Option (Name × Name)) := do
  let env ← getEnv
  let h := value.hash
  for e in sharedTyExt.getState env do
    if e.hash == h then
      if let some ci := env.find? e.declName then
        if ci.value? == some value then return some (e.declName, e.wfName)
  return none

/-! ## Reading a Lean declaration -/

/-- What a Lean type translates to: a tree, nothing (it carries no value), or no tree at
    all, with the reason. -/
inductive TransRes where
  /-- A tree of the language. -/
  | ok : Expr → TransRes
  /-- A type the language erases: it carries no value. -/
  | erased
  /-- No shape of the language describes it, for this reason. -/
  | no : MessageData → TransRes

/-- Is this a type the language erases — a proposition, or a one-value type? -/
def isErasedType (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  match (← whnf e).getAppFn with
  | .const n _ => return n == ``Unit || n == ``PUnit
  | _ => return false

/-- Is this binder a **type field** — a field whose value is a type?  The field itself is
    erased, since a type carries no run-time value; a later field that holds a *value of
    it* is what the handler cannot translate. -/
def isTypeField (t : Expr) : MetaM Bool := do
  let t ← whnf t
  return t.isSort && t != .sort .zero

/-- Is this binder a type field, or a *family* of them — `State : Type`, `Elem : State →
    Type`, `f : Nat → Type`?  A declaration with such a field hides a type from the
    language: a value of it is a value of a type the model does not name, which is what
    the language calls an existential, and which it does not model. -/
def isExistentialField (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ body => isTypeField body

/-- The first field of `n` that hides a type, if it has one.  The declaration is refused
    as a whole: `LeanScript` has no existential type, so a declaration whose values carry
    a type of their own is not one it models. -/
def existentialField? (n : Name) (params : Array Expr) : MetaM (Option Name) := do
  let some (.inductInfo ind) := (← getEnv).find? n | return none
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    let cty ← instantiateForall ci.type (params.extract 0 ind.numParams)
    let hit? ← forallTelescopeReducing cty fun xs _ => do
      for x in xs do
        if ← isExistentialField (← inferType x) then
          return some (← x.fvarId!.getUserName)
      return none
    if let some f := hit? then return some f
  return none

/-- Is this a binder the translation drops — a proof, a type, an instance or a one-value
    type? -/
def erasedBinder (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if (← whnf t).isSort then return true
  if ← isErasedType t then return true
  if (← isClass? t).isSome then return true
  return false

/-- The types of the values the declaration `n` **caches** — a `@[computed_field]` is
    stored in the runtime object, so it is one more field of it — in declaration order.

    Lean records a computed field by building a second inductive, `n._impl`, whose
    constructors carry the cached values ahead of the fields, so the types are read off a
    constructor that has a field.  A declaration all of whose constructors are field-less
    stores its cached values nowhere — they are a function of the constructor number —
    and the types are read off the `@[computed_field]` functions instead. -/
def computedFieldTys (n : Name) : MetaM (Except MessageData (List Expr)) := do
  let env ← getEnv
  if (env.find? (n ++ `_impl)).isNone then return .ok []
  let some (.inductInfo ind) := env.find? n | return .ok []
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    if ci.numFields == 0 then continue
    let some (.ctorInfo cimpl) := env.find? (c ++ `_impl)
      | return .error m!"`{n}` caches values in a way this handler cannot read"
    let k := cimpl.numFields - ci.numFields
    if k == 0 then return .ok []
    return ← forallTelescopeReducing cimpl.type fun xs _ => do
      let mut tys : List Expr := []
      for x in xs[ind.numParams:ind.numParams + k] do
        tys := tys ++ [← inferType x]
      return .ok tys
  -- every constructor is field-less: the cached value is a function of the constructor
  -- number and is stored nowhere, so its type is read off the function that computes it.
  -- Lean gives every computed field `f` of `n` a companion `n.f._override`.
  let mut fields : Array (Nat × Name × Expr) := #[]
  for (m, _) in env.constants.toList do
    let .str base "_override" := m | continue
    unless n.isPrefixOf base && base != n do continue
    if ind.ctors.contains base then continue
    if base == n ++ `casesOn || base == n ++ `rec || base == n ++ `recOn then continue
    let some ci := env.find? base | continue
    let res ← forallTelescopeReducing ci.type fun _ body => whnf body
    if res.hasLooseBVars || res.hasFVar then
      return .error m!"`{n}` caches a value whose type this handler cannot read"
    let line := (← findDeclarationRanges? base).map (·.range.pos.line) |>.getD 0
    fields := fields.push (line, base, res)
  let sorted := fields.qsort fun a b =>
    if a.1 == b.1 then Name.lt a.2.1 b.2.1 else a.1 < b.1
  return .ok (sorted.toList.map (·.2.2))

/-! ## The dependency graph of a `mutual` block

Lean's `mutual` blocks are not always *families*: a block whose members do not each reach
the others is several declarations that happen to be written together, and each of its
strongly connected components can be declared on its own, in dependency order. -/

/-- Which members of the block `names` the member `m` mentions in the types of the fields
    it keeps. -/
def blockDeps (names : List Name) (params : Array Expr) (m : Name) :
    MetaM (Except MessageData (List Name)) := do
  let some (.inductInfo mind) := (← getEnv).find? m
    | return .error m!"`{m}` is not an inductive declaration"
  let mut deps : List Name := []
  for c in mind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (params.extract 0 mind.numParams)
    let ds ← forallTelescopeReducing cty fun xs _ => do
      let mut ds : List Name := []
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        for k in t.getUsedConstants do
          if names.contains k && !ds.contains k then ds := ds ++ [k]
      return ds
    for d in ds do
      if !deps.contains d then deps := deps ++ [d]
  return .ok deps

/-- Everything reachable from `start` in the graph `edges`, `start` included. -/
def nameReach (edges : List (Name × List Name)) (start : Name) : List Name :=
  go edges.length [start] [start]
where
  /-- Breadth-first closure: `acc` is what has been reached, `frontier` what was reached
      last, and `fuel` bounds the number of rounds by the number of members. -/
  go : Nat → List Name → List Name → List Name
    | 0, acc, _ => acc
    | _ + 1, acc, [] => acc
    | k + 1, acc, frontier =>
        let next := frontier.flatMap fun m => ((edges.find? (·.1 == m)).map (·.2)).getD []
        let fresh := next.filter fun m => !acc.contains m
        go k (acc ++ fresh) fresh

/-- The members of the block `names` that belong to the same strongly connected component
    as `n`: the ones `n` reaches and that reach `n`, in declaration order. -/
def blockComponent (names : List Name) (edges : List (Name × List Name)) (n : Name) :
    List Name :=
  names.filter fun m => (nameReach edges n).contains m && (nameReach edges m).contains n

/-! ## Building a tree -/

/-- The type `LeanScript.Ty`, as an expression. -/
def tyE : Expr := mkConst ``LeanScript.Ty
/-- The type `List LeanScript.Ty`, as an expression. -/
def listTyE : Expr := mkApp (mkConst ``List [0]) tyE
/-- A list of trees, as an expression. -/
def mkTyList (es : List Expr) : MetaM Expr := mkListLit tyE es
/-- A list of lists of trees — the fields of each constructor — as an expression. -/
def mkTyListList (ess : List (List Expr)) : MetaM Expr := do
  mkListLit listTyE (← ess.mapM mkTyList)
/-- A non-empty list of trees, as an expression. -/
def mkNE (e : Expr) (es : List Expr) : MetaM Expr := do
  mkAppM ``NonEmpty.ListCorrectByConstruction.NonEmptyList.mk #[e, ← mkTyList es]

/-- Does this tree mention the declaration whose scope it is written in? -/
def mentionsScope (e : Expr) : Bool :=
  (e.find? fun x =>
    x.isConstOf ``LeanScript.Ty.self || x.isAppOf ``LeanScript.Ty.familyMember).isSome

/-- The record schema of these fields, of which there must be at least two. -/
def mkRecord? (fs : List Expr) : MetaM (Option Expr) := do
  match fs with
  | a :: b :: rest => return some (← mkAppM ``LeanScript.LeanRecordSchema.mk
      #[a, b, ← mkTyList rest])
  | _ => return none

/-- The constructors of a tagged union from the first that carries a field. -/
partial def mkCtorsWithPayload? : List (List Expr) → MetaM (Option Expr)
  | [] => return none
  | [] :: rest => do
      match ← mkCtorsWithPayload? rest with
      | some r => return some (← mkAppM ``LeanScript.CtorsWithPayload.skip #[r])
      | none => return none
  | (f :: fs) :: rest => do
      return some (← mkAppM ``LeanScript.CtorsWithPayload.here
        #[← mkNE f fs, ← mkTyListList rest])

/-- The tagged-union schema of these constructors: at least two of them, at least one
    with a field. -/
def mkTaggedUnion? : List (List Expr) → MetaM (Option Expr)
  | (f :: fs) :: next :: rest => do
      return some (← mkAppM ``LeanScript.LeanTaggedUnionSchema.payloadFirst
        #[← mkNE f fs, ← mkTyList next, ← mkTyListList rest])
  | [] :: rest => do
      match ← mkCtorsWithPayload? rest with
      | some r => return some (← mkAppM ``LeanScript.LeanTaggedUnionSchema.skip #[r])
      | none => return none
  | _ => return none

/-- The enum with `n` field-less constructors numbered from `0`, or `Ty.prim .bool` for
    two of them. -/
def mkEnumOrBool? (n : Nat) : MetaM (Option Expr) := do
  if n == 2 then return some (← mkAppM ``LeanScript.Ty.prim #[mkConst ``LeanScript.LeanPrimTy.bool])
  if n < 3 then return none
  let e ← mkAppM ``LeanScript.LeanEnumSchema.mk
    #[mkNatLit (n - 3), ← mkAppM ``Int.ofNat #[mkNatLit 0]]
  return some (← mkAppM ``LeanScript.Ty.enum #[e])

/-- The shape a declaration with these constructors has, as a tree.  `rec` says whether
    the declaration mentions itself, which is what tells `Ty.record` from
    `Ty.recObject`. -/
def assembleShape (name : Name) (ctors : List (List Expr)) : MetaM TransRes := do
  let isRec := ctors.any (·.any mentionsScope)
  match ctors with
  | [] => return .no m!"`{name}` has no constructors, so it has no values"
  | [[]] => return .erased
  | [[a]] =>
      -- a newtype: the wrapper is erased into its field
      if isRec then return .ok (← mkAppM ``LeanScript.Ty.recAlias #[a]) else return .ok a
  | [fs] =>
      match ← mkRecord? fs with
      | none => return .no m!"`{name}` is a record the schema refuses"
      | some sch =>
          return .ok (← mkAppM
            (if isRec then ``LeanScript.Ty.recObject else ``LeanScript.Ty.record) #[sch])
  | _ =>
      if ctors.all (·.isEmpty) then
        match ← mkEnumOrBool? ctors.length with
        | some e => return .ok e
        | none => return .no m!"`{name}` is an enum of fewer than two constructors"
      else
        match ← mkTaggedUnion? ctors with
        | none => return .no m!"`{name}` is a tagged union the schema refuses"
        | some sch =>
            return .ok (← mkAppM
              (if isRec then ``LeanScript.Ty.recTaggedUnion else ``LeanScript.Ty.taggedUnion)
              #[sch])

/-- The shape of one member of a mutual family, from its constructors. -/
def assembleFamMember (name : Name) (ctors : List (List Expr)) :
    MetaM (Except MessageData Expr) := do
  match ctors with
  | [[a]] => return .ok (← mkAppM ``LeanScript.LeanFamMemberSchema.alias #[a])
  | [fs] =>
      match ← mkRecord? fs with
      | some sch => return .ok (← mkAppM ``LeanScript.LeanFamMemberSchema.record #[sch])
      | none => return .error m!"`{name}` is a member of a family with fewer than two fields"
  | _ =>
      match ← mkTaggedUnion? ctors with
      | some sch => return .ok (← mkAppM ``LeanScript.LeanFamMemberSchema.ctors #[sch])
      | none => return .error m!"`{name}` is a member of a family the schema refuses"

/-- The family of these members, selecting member `i`. -/
def mkFamily? (ms : List Expr) (i : Nat) : MetaM (Option Expr) := do
  let memberTy := mkApp (mkConst ``LeanScript.LeanFamMemberSchema) tyE
  let lst (es : List Expr) : MetaM Expr := mkListLit memberTy es
  if h : i < ms.length then
    let cur := ms[i]
    if i + 1 < ms.length then
      return some (← mkAppM ``LeanScript.LeanMutualRecFamily.selectedThenMore
        #[← lst (ms.take i), cur, ms[i + 1]!, ← lst (ms.drop (i + 2))])
    else if let first :: before := ms.take i then
      return some (← mkAppM ``LeanScript.LeanMutualRecFamily.selectedLast
        #[first, ← lst before, cur])
    else return none
  else return none

/-! ## Putting an occurrence inside another type's model

A field of type `Option T`, where `T` is the declaration being defined, is not a type that
has an instance — an instance's tree is closed, and this one has to hold an occurrence.
But `Option`'s *model* is a function of the model of its argument, so the tree is the one
`Option` already has, with `Ty.self` where the argument's tree would be.  That is what the
two functions below do, generically, for any type former: the former's own instance is
asked for at a stand-in parameter, and the stand-in's leaf is replaced by the occurrence.

The substitution answers `none` when the leaf sits **inside a binder** of the former's
tree, because there the occurrence would denote the former's own recursion and not the
declaration being defined.  That is exactly the case of `List T`, whose tree is a
`Ty.recTaggedUnion`, while `Option T`, `T × T` and `T ⊕ T` are not; the binder is then
hoisted into a member of a family, which is the section after this one. -/

/-- The bundled tree an instance holds, in each of the ways such a bundle is written; the
    answer is the Lean type it models. -/
def bundleModelledType? (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj ``LeanScript.LeanScriptTyWf 0 inst =>
      return (← whnf (← inferType inst)).getAppArgs[0]?
  | _ =>
    match e.getAppFnArgs with
    | (``LeanScript.LeanScriptTyWf.tyWfOf, #[α, _]) => return some α
    | (``LeanScript.tyWfOf, #[α, _]) => return some α
    | _ => return none

/-- The type an instance's tree is the model of, in each of the ways such a tree is
    written: `tyOf α`, and the projections it abbreviates. -/
def modelledType? (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .proj ``LeanScript.TyWf 0 b => bundleModelledType? b
  | _ =>
    match e.getAppFnArgs with
    | (``LeanScript.TyWf.toTy, #[b]) => bundleModelledType? b
    | (``LeanScript.tyOf, #[α, _]) => return some α
    | _ => return none

/-- Is this node of a tree one of the four binders?  What is under a binder is written in
    the scope the binder opens, not in the scope the binder sits in. -/
def isBinderCtor (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
      n == ``LeanScript.Ty.recTaggedUnion || n == ``LeanScript.Ty.recObject ||
        n == ``LeanScript.Ty.recAlias || n == ``LeanScript.Ty.mutualRecursiveFamily
  | _ => false

/-- Replace the leaf of each stand-in parameter by the tree it stands for, or answer
    `none` if one of them is under a binder — where the occurrence it carries would mean
    something else. -/
partial def substHoles (holes : Array Expr) (trees : Array Expr) (underBinder : Bool)
    (e : Expr) : MetaM (Option Expr) := do
  if let some α ← modelledType? e then
    if let some k := holes.idxOf? α then
      if underBinder then return none else return some trees[k]!
  match e with
  | .app .. =>
      let under := underBinder || isBinderCtor e
      let mut out := e.getAppFn
      for a in e.getAppArgs do
        let some a' ← substHoles holes trees under a | return none
        out := mkApp out a'
      return some out
  | .lam n t b i => do
      let some t' ← substHoles holes trees underBinder t | return none
      let some b' ← substHoles holes trees underBinder b | return none
      return some (.lam n t' b' i)
  | .forallE n t b i => do
      let some t' ← substHoles holes trees underBinder t | return none
      let some b' ← substHoles holes trees underBinder b | return none
      return some (.forallE n t' b' i)
  | .mdata d b => do
      let some b' ← substHoles holes trees underBinder b | return none
      return some (.mdata d b')
  | .proj s i b => do
      let some b' ← substHoles holes trees underBinder b | return none
      return some (.proj s i b')
  | _ => return some e

/-- What a declaration is translated in: the members of its family (itself alone, when it
    is not a family) and the type parameters it is being translated at. -/
structure Ctx where
  /-- The members of the family being defined, in declaration order. -/
  members : Array Name
  /-- The type parameters of the declaration, as local variables. -/
  params : Array Expr
  /-- How many members the family has before any hoisting: the members above, or one when
      the declaration is alone in its block.  A hoisted member is numbered from here. -/
  baseCount : Nat := 1
  /-- The members hoisted out of a recursive wrapper, in the order they were created; see
      the section on hoisting.  They follow the members above in the family. -/
  extra : IO.Ref (Array Expr)

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

mutual

/-- The tree that models the Lean type `e`.

    A type that is **not** the declaration being defined is not read: its instance is, and
    the leaf is that instance's `tyWfOf`.  That is what stops a declaration from being
    translated once per mention of it. -/
partial def tyWfOfType (ctx : Ctx) (e : Expr) : MetaM TransRes := do
  if ← isProp e then return .erased
  let e ← whnf e
  if e.isSort then return .no m!"a type or a proposition, which carries no value"
  if ← isErasedType e then return .erased
  -- a type that *contains* the declaration being defined cannot come from an instance:
  -- an instance's tree is closed, and this one has to hold an occurrence.  The type
  -- formers the language has a shape of its own for are followed into; anything else is
  -- refused, and named in the message.
  let mentionsMember :=
    e.getUsedConstants.any fun c => ctx.members.contains c
  if mentionsMember then
    if e.isForall then
      return ← forallTelescopeReducing e fun xs body => do
        let mut doms : List Expr := []
        for x in xs do
          let d ← inferType x
          if ← erasedBinder d then continue
          match ← tyWfOfType ctx d with
          | .ok a => doms := doms ++ [a]
          | .erased => pure ()
          | .no r => return .no r
        match ← tyWfOfType ctx body with
        | .ok r => return .ok (← doms.foldrM (fun a b => mkAppM ``LeanScript.Ty.fn #[a, b]) r)
        | .erased => return .no m!"a function answering with a type that carries no value"
        | .no r => return .no r
    let args := e.getAppArgs
    if let .const c _ := e.getAppFn then
      if (c == ``Array || c == ``Thunk) && args.size == 1 then
        match ← tyWfOfType ctx args[0]! with
        | .ok a =>
            return .ok (← mkAppM
              (if c == ``Array then ``LeanScript.Ty.array else ``LeanScript.Ty.thunk) #[a])
        | .erased => return .no m!"`{c}` of a type that carries no value"
        | .no r => return .no r
  if let .const m _ := e.getAppFn then
    if let some i := ctx.members.idxOf? m then
      let args := e.getAppArgs
      if args.size ≥ ctx.params.size && args.extract 0 ctx.params.size == ctx.params then
        if ctx.members.size == 1 then
          return .ok (mkConst ``LeanScript.Ty.self)
        else
          return .ok (mkApp (mkConst ``LeanScript.Ty.familyMember) (mkNatLit i))
      else
        return .no m!"`{m}` at other arguments than its own is not a type this handler \
          can name here"
  if mentionsMember then
    -- a type former the language has no shape of its own for: the occurrence goes into
    -- the former's own model, and a binder of it that would capture the occurrence is
    -- hoisted into a member of a family
    if let some res ← tyWfOfWrapper ctx e then return res
    return .no (← addMessageContext
      m!"`{e}` mentions the declaration being defined through a type this handler cannot \
        recurse through: the occurrence goes where the argument's tree would stand in \
        the type former's own model (`Array`, `Thunk`, `Option`, `×`, `⊕`, a function \
        type, any non-recursive wrapper), and a binder that would capture it there is \
        hoisted into a member of a family (`List`, any recursive wrapper) — but the model \
        of this one is a mutual family, or does not hold the argument as one tree")
  match ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[e]) with
  | .some inst =>
      return .ok (← mkAppOptM ``LeanScript.tyOf #[some e, some inst])
  | _ =>
      return .no (← addMessageContext
        m!"`{e}` has no `LeanScriptTyWf` instance; derive or write one for it first")

/-- The tree of a type former applied to the declaration being defined: the former's own
    instance, asked for at a stand-in parameter, with the stand-in's leaf replaced by the
    tree of what stands there.  `none` when the former has no instance, when one of the
    arguments is not a type, or when the occurrence would be captured by a binder of the
    former's own model. -/
partial def tyWfOfWrapper (ctx : Ctx) (e : Expr) : MetaM (Option TransRes) := do
  let fn := e.getAppFn
  unless fn.isConst do return none
  let args := e.getAppArgs
  -- the arguments that mention the declaration being defined; the others keep their own
  -- instances, so nothing about them is re-read
  let mut idxs : Array Nat := #[]
  for i in [0:args.size] do
    if args[i]!.getUsedConstants.any (ctx.members.contains ·) then idxs := idxs.push i
  if idxs.isEmpty then return none
  let mut trees : Array Expr := #[]
  for i in idxs do
    unless ← isTypeField (← inferType args[i]!) do return none
    match ← tyWfOfType ctx args[i]! with
    | .ok a => trees := trees.push a
    | .erased => return some (.no m!"`{e}` holds a type that carries no value")
    | .no r => return some (.no r)
  let holeDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
    idxs.mapIdx fun k _ =>
      (Name.mkSimple s!"hole{k}", BinderInfo.default,
        fun _ => pure (mkSort (Level.succ Level.zero)))
  withLocalDecls holeDecls fun holes => do
    let instDecls : Array (Name × BinderInfo × (Array Expr → MetaM Expr)) :=
      holes.mapIdx fun k h =>
        (Name.mkSimple s!"holeInst{k}", BinderInfo.instImplicit,
          fun _ => mkAppM ``LeanScript.LeanScriptTyWf #[h])
    withLocalDecls instDecls fun _ => do
      let mut args' := args
      for k in [0:idxs.size] do
        args' := args'.set! idxs[k]! holes[k]!
      let e' := mkAppN fn args'
      let .some inst ← trySynthInstance (← mkAppM ``LeanScript.LeanScriptTyWf #[e'])
        | return none
      let tree ← whnf (← mkAppOptM ``LeanScript.tyOf #[some e', some inst])
      -- the occurrence goes where the stand-in is; if it would land inside a binder of
      -- the former's own model, that binder is hoisted into a member of a family instead
      let out? ←
        match ← substHoles holes trees false tree with
        | some out => pure (some out)
        | none => hoistTree ctx holes trees none tree
      let some out := out? | return none
      -- nothing of the stand-ins may be left: an argument that the former's model does
      -- not use as one tree is one this handler cannot put an occurrence into
      if holes.any (fun h => out.containsFVar h.fvarId!) then return none
      return some (.ok out)

end

/-- The field types of each constructor of `ind`, in declaration order, with the erased
    fields dropped and the rest translated. -/
def translateCtors (ctx : Ctx) (ind : InductiveVal) :
    MetaM (Except MessageData (List (List Expr))) := do
  let mut ctors : List (List Expr) := []
  for c in ind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (ctx.params.extract 0 ind.numParams)
    let fields : Except MessageData (List Expr) ← forallTelescopeReducing cty fun xs _ => do
      let mut fs : List Expr := []
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        match ← tyWfOfType ctx t with
        | .ok a => fs := fs ++ [a]
        | .erased => pure ()
        | .no r => return .error r
      return .ok fs
    match fields with
    | .error r => return .error r
    | .ok fs => ctors := ctors ++ [fs]
  return .ok ctors

/-- The shape of `n` followed by the values it caches, which are ordinary fields of a
    record.  A declaration that caches values *is* that record, so an occurrence of the
    declaration inside its own shape denotes the record and the binder is the record. -/
def withComputedFields (n : Name) (isRec : Bool) (base : TransRes) : MetaM TransRes := do
  match base with
  | .no r => return .no r
  | _ =>
    match ← computedFieldTys n with
    | .error r => return .no r
    | .ok [] => return base
    | .ok ctys =>
      let mut cached : List Expr := []
      let closed : Ctx := { members := #[], params := #[], extra := ← IO.mkRef #[] }
      for t in ctys do
        match ← tyWfOfType closed t with
        | .ok a => cached := cached ++ [a]
        | .erased => pure ()
        | .no r => return .no r
      let fields := (match base with | .ok a => [a] | _ => []) ++ cached
      match fields with
      | [] => return .erased
      | [a] => return .ok a
      | fs =>
        match ← mkRecord? fs with
        | none => return .no m!"`{n}` caches values this handler cannot lay out"
        | some sch =>
            return .ok (← mkAppM
              (if isRec then ``LeanScript.Ty.recObject else ``LeanScript.Ty.record) #[sch])

/-- The tree of the declaration `n`, translated at the parameters `params`. -/
def treeOfDecl (n : Name) (ind : InductiveVal) (params : Array Expr) : MetaM TransRes := do
  -- which members of `n`'s `mutual` block are a family with it
  let members : Array Name ←
    if ind.all.length ≤ 1 then pure #[n]
    else do
      let mut edges : List (Name × List Name) := []
      for m in ind.all do
        match ← blockDeps ind.all params m with
        | .error r => return .no r
        | .ok ds => edges := edges ++ [(m, ds)]
      let comp := blockComponent ind.all edges n
      pure (if comp.length ≤ 1 then #[n] else comp.toArray)
  let extra ← IO.mkRef (#[] : Array Expr)
  let ctx : Ctx :=
    { members, params, baseCount := if members.size ≤ 1 then 1 else members.size, extra }
  if members.size ≤ 1 then
    match ← translateCtors ctx ind with
    | .error r => return .no r
    | .ok ctors =>
        let isRec := ctors.any (·.any mentionsScope)
        -- a wrapper was hoisted: the declaration is member `0` of a family whose other
        -- members are the binders the recursion passes through
        if let hoisted@(_ :: _) := (← extra.get).toList then
          match ← computedFieldTys n with
          | .error r => return .no r
          | .ok (_ :: _) =>
              return .no m!"`{n}` recurses through a type whose own model is recursive \
                and caches values, which this handler has no layout for"
          | .ok [] =>
            let ctors := ctors.map (·.map (selfToMember 0))
            match ← assembleFamMember n ctors with
            | .error r => return .no r
            | .ok m0 =>
              match ← mkFamily? (m0 :: hoisted) 0 with
              | none => return .no m!"`{n}` recurses through a type this handler cannot \
                  lay out as a family"
              | some fam =>
                  return .ok (← mkAppM ``LeanScript.Ty.mutualRecursiveFamily #[fam])
        match ← computedFieldTys n with
        | .error r => return .no r
        | .ok [] => return ← assembleShape n ctors
        | .ok _ =>
            -- the cached values are fields of the record the declaration is, and the
            -- shape is one more field of it
            match ← assembleShape n ctors with
            | .no r => return .no r
            | .erased => return ← withComputedFields n false .erased
            | .ok shape =>
                -- the shape must not be its own binder: the binder is the record
                let bare ← if isRec then stripBinder shape else pure shape
                return ← withComputedFields n isRec (.ok bare)
  else
    let mut memberExprs : List Expr := []
    for m in members do
      let some (.inductInfo mind) := (← getEnv).find? m
        | return .no m!"`{m}` is not an inductive declaration"
      match ← translateCtors ctx mind with
      | .error r => return .no r
      | .ok ctors =>
        match ← computedFieldTys m with
        | .error r => return .no r
        | .ok [] =>
            match ← assembleFamMember m ctors with
            | .error r => return .no r
            | .ok sch => memberExprs := memberExprs ++ [sch]
        | .ok _ =>
            return .no m!"`{m}` is a member of a mutual family and caches values, which \
              this handler has no layout for"
    let some i := members.idxOf? n | return .no m!"`{n}` is not a member of its own block"
    -- the members hoisted out of a recursive wrapper follow the declared ones
    memberExprs := memberExprs ++ (← extra.get).toList
    match ← mkFamily? memberExprs i with
    | none => return .no m!"`{n}` is a mutual block of fewer than two members"
    | some fam => return .ok (← mkAppM ``LeanScript.Ty.mutualRecursiveFamily #[fam])
where
  /-- The payload of a recursive binder, which a declaration that caches values wraps in
      a record instead. -/
  stripBinder (e : Expr) : MetaM Expr := do
    match e.getAppFnArgs with
    | (``LeanScript.Ty.recTaggedUnion, #[l]) => mkAppM ``LeanScript.Ty.taggedUnion #[l]
    | (``LeanScript.Ty.recObject, #[fs]) => mkAppM ``LeanScript.Ty.record #[fs]
    | (``LeanScript.Ty.recAlias, #[b]) => return b
    | _ => return e

/-! ## The handler -/

/-- The universe parameters a declaration's type and value use. -/
def usedLevels (type value : Expr) : List Name :=
  (collectLevelParams (collectLevelParams {} type) value).params.toList

/-- Make the first `k` binders of a `∀`/`fun` implicit, which is what an instance's own
    type parameters are. -/
partial def setImplicit (k : Nat) (e : Expr) : Expr :=
  match k, e with
  | 0, e => e
  | k + 1, .forallE nm t b _ => .forallE nm t (setImplicit k b) .implicit
  | k + 1, .lam nm t b _ => .lam nm t (setImplicit k b) .implicit
  | _, e => e

/-- Add the instance for the declaration `n`: its tree, the proof that the tree is a
    type, and the instance holding them.  The tree and the proof are shared with any
    declaration that already has the same tree. -/
def mkInstanceFor (n : Name) : TermElabM Unit := do
  let some (.inductInfo ind) := (← getEnv).find? n
    | throwError "`{n}` is not an inductive declaration, so it has no `Ty`"
  if ind.numIndices != 0 then
    throwError "`{n}` is an indexed family, which the language has no shape for"
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
      let theType := mkAppN (mkConst n (ind.levelParams.map Level.param)) params
      let bundle ← mkAppOptM ``LeanScript.TyWf.mk
        #[some (mkAppN (mkConst declName dlvls) binders),
          some (mkAppN (mkConst wfName wlvls) binders)]
      let instValue ← mkLambdaFVars binders (← mkAppOptM ``LeanScript.LeanScriptTyWf.mk
        #[some theType, some bundle])
      let instType ← mkForallFVars binders (← mkAppM ``LeanScript.LeanScriptTyWf #[theType])
      let instName := n ++ `instLeanScriptTyWf
      let instType := setImplicit params.size instType
      let instValue := setImplicit params.size instValue
      addAndCompile (.defnDecl
        { name := instName, levelParams := usedLevels instType instValue, type := instType,
          value := instValue, hints := .abbrev, safety := .safe })
      setReducibleAttribute instName
      addInstance instName .global (eval_prio default)

/-! ## The `deriving` clause

`deriving LeanScriptTyWf` on a declaration, and `deriving instance LeanScriptTyWf for …`
after it, both add the instance of the declaration named.  A declaration the handler has
no model for is refused with the reason, which is the message `#guard_msgs` pins in the
tests. -/

/-- The handler `deriving LeanScriptTyWf` runs: one instance per declaration named. -/
def leanScriptTyWfHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    Command.liftTermElabM (mkInstanceFor n)
  return true

initialize registerDerivingHandler ``LeanScript.LeanScriptTyWf leanScriptTyWfHandler

end LeanScript.Deriving

end

end
