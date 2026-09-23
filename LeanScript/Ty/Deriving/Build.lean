module

public meta import LeanScript.Ty.Deriving.Read

@[expose] public section

meta section

/-!
# `deriving LeanScriptTyWf`: building a tree

The constructors of the trees the handler builds, and putting an occurrence inside another
type's model.
-/

open Lean Meta Elab Term Command

namespace LeanScript.Deriving

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

end LeanScript.Deriving

end

end
