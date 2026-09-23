module

public meta import Lean
public meta import LeanScript.Ty.Wf

@[expose] public section

meta section

open Lean Meta Elab Tactic

namespace LeanScript.Ty

/-!
# `ty_wf`: the proof that a tree is a type, composed rather than computed

`ty_wf` closes a goal of the form `Ty.Wf t`, `Ty.WfIn n t`, or any of the auxiliary
propositions of `LeanScript.Ty.Wf`, by **writing the derivation directly**: it walks the
tree one node at a time and applies the rule of that node.

The point of the tactic — and the reason `Ty.Wf` is an inductive proposition rather than
a Boolean check — is what it does at a leaf it does *not* walk into:

* a subtree that is the tree of a bundled `LeanScript.TyWf` — `(tyWfOf α).toTy` for some
  instance, say — is closed by that bundle's own `isWf`.  The tree of `α` is never looked
  at, in this module or in any later one: the proof is reused, not recomputed;
* a subtree that is a local variable — the parameter of a generated
  `…leanScriptTyOf (a : Ty)` — is closed by a hypothesis `Ty.Wf a` from the context.

So checking a type costs the size of *its own* layer, not the size of its transitive
content, and importing a module that already checked a type costs nothing at all.
-/

/-- The occurrences a node holds, as a list of terms: `whnf` the spine of a `List Ty`. -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) => return h :: (← listElems t)
  | _ => throwError "ty_wf: not a list of types: {e}"

/-- A natural number argument of a goal, when it is a literal. -/
def natOf? (e : Expr) : MetaM (Option Nat) := do
  let e ← whnf e
  if let some n := e.rawNatLit? then return some n
  return e.nat?

/-- A natural number as an expression. -/
def natE (n : Nat) : Expr := mkNatLit n

/-- A list of natural numbers — the members already known to have values — as an
    expression. -/
def natListE (S : List Nat) : MetaM Expr := mkListLit (mkConst ``Nat) (S.map natE)

/-- The members a goal assumes to have values, when they are literals. -/
partial def natListOf (e : Expr) : MetaM (List Nat) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
      let some i ← natOf? h | throwError "ty_wf: the member number {h} is unknown"
      return i :: (← natListOf t)
  | _ => throwError "ty_wf: not a list of member numbers: {e}"

/-- A proof of `i ∈ S`, for a list of literals. -/
def memProof (i : Nat) (S : List Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``Membership.mem #[← natListE S, natE i])

/-- A proof of `a ≤ b`. -/
def leProof (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LE.le #[natE a, natE b])

/-- A proof of `a < b`. -/
def ltProof (a b : Nat) : MetaM Expr := do
  mkDecideProof (← mkAppM ``LT.lt #[natE a, natE b])

/-! ### The bundled tree, named rather than imported

`LeanScript.TyWf` — a tree together with the proof that it is one — is declared *after*
this module, because the proof it carries is written `by ty_wf`.  So the two projections
it is recognised by are named here as plain `Name`s rather than resolved at compile time;
they are in the environment by the time the tactic runs, which is every module from
`LeanScript.Ty.TyWf` on. -/

/-- The structure of a tree together with its proof, `LeanScript.TyWf`. -/
def tyWfStruct : Name := `LeanScript.TyWf
/-- Its tree, `LeanScript.TyWf.toTy`. -/
def tyWfToTy : Name := `LeanScript.TyWf.toTy
/-- Its proof, `LeanScript.TyWf.isWf`. -/
def tyWfIsWf : Name := `LeanScript.TyWf.isWf

/-- Is `t` the tree of a bundled `LeanScript.TyWf` — the tree of an instance, say?  If so,
    the proof that it is a type, which is that bundle's own field — no tree is
    traversed. -/
def instanceWf? (t : Expr) : MetaM (Option Expr) := do
  let bundle? : Option Expr :=
    match t with
    | .proj s 0 b => if s == tyWfStruct then some b else none
    | _ =>
      match t.getAppFn, t.getAppArgs with
      | .const c _, #[b] => if c == tyWfToTy then some b else none
      | _, _ => none
  let some bundle := bundle? | return none
  return some (mkApp (mkConst tyWfIsWf) bundle)

/-- Is there a hypothesis saying that `t` is a type?  This is what closes the parameters
    of a generated tree, which stand for the trees of the type's own parameters. -/
def hypWf? (t : Expr) : MetaM (Option Expr) := do
  unless t.isFVar do return none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match (← whnfR d.type).getAppFnArgs with
    | (``LeanScript.Ty.WfIn, #[n, x]) =>
        if x == t && (← natOf? n) == some 0 then return some d.toExpr
    | _ => pure ()
  return none

/-- Is the head of `t` a constructor of `LeanScript.Ty`? -/
def isTyCtor (t : Expr) : Bool :=
  match t.getAppFn with
  | .const n _ =>
      n == ``LeanScript.Ty.self || n == ``LeanScript.Ty.familyMember ||
        n == ``LeanScript.Ty.shape || n == ``LeanScript.Ty.recTaggedUnion ||
        n == ``LeanScript.Ty.recObject || n == ``LeanScript.Ty.recAlias ||
        n == ``LeanScript.Ty.mutualRecursiveFamily
  | _ => false

/-- Expose what a tree is at its root, **without** unfolding past a leaf that some
    instance or some hypothesis already answers for.  Ordinary `whnf` would unfold such a
    leaf into the tree behind it, which is exactly the copying this class exists to
    avoid, so the definition at the head is unfolded one step at a time and the leaf is
    looked for before each step. -/
partial def tyHeadNorm (t : Expr) : MetaM Expr := do
  let t ← whnfCore t
  if isTyCtor t then return t
  if (← instanceWf? t).isSome then return t
  if (← hypWf? t).isSome then return t
  match ← unfoldDefinition? t with
  | some t' => tyHeadNorm t'
  | none => return t

mutual

/-- A proof of `Ty.WfIn n t`. -/
partial def mkWfIn (n : Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  -- a checked type, dropped in as a leaf: reuse its proof rather than its tree
  if let some p ← instanceWf? t then
    return ← ifClosed n p
  if let some p ← hypWf? t then
    return ← ifClosed n p
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless n == 1 do
        throwError "ty_wf: `Ty.self` is not a type in a scope of {n} members"
      return mkConst ``LeanScript.Ty.WfIn.self
  | (``LeanScript.Ty.familyMember, #[i]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member number {i} is unknown"
      unless 2 ≤ n && i < n do
        throwError "ty_wf: member {i} is not a member of a scope of {n} members"
      mkAppOptM ``LeanScript.Ty.WfIn.familyMember
        #[some (natE n), some (natE i), some (← leProof 2 n), some (← ltProof i n)]
  | (``LeanScript.Ty.shape, #[s]) =>
      mkAppOptM ``LeanScript.Ty.WfIn.shape
        #[some (natE n), some s, some (← mkWfShapeIn n s)]
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      let tys ← mkAppM ``List.flatten #[ctors]
      mkAppOptM ``LeanScript.Ty.WfIn.recTaggedUnion
        #[some (natE n), some l, some (← mkWfAllIn 1 tys), some (← mkOccursSomeIn 0 tys),
          some (← mkHabSomeIn [] ctors)]
  | (``LeanScript.Ty.recObject, #[fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.WfIn.recObject
        #[some (natE n), some fs, some (← mkWfAllIn 1 tys), some (← mkOccursSomeIn 0 tys),
          some (← mkHabAllIn [] tys)]
  | (``LeanScript.Ty.recAlias, #[b]) =>
      mkAppOptM ``LeanScript.Ty.WfIn.recAlias
        #[some (natE n), some b, some (← mkWfIn 1 b), some (← mkOccursIn 0 b),
          some (← mkHabIn [] b)]
  | (``LeanScript.Ty.mutualRecursiveFamily, #[f]) =>
      let ms ← mkAppM ``LeanScript.LeanMutualRecFamily.members #[f]
      let k := (← listElems ms).length
      let tys ← mkAppM ``LeanScript.Ty.familyTys #[f]
      mkAppOptM ``LeanScript.Ty.WfIn.mutualRecursiveFamily
        #[some (natE n), some f, some (← mkWfAllIn k tys), some (← mkMembersOccur k tys),
          some (← mkFamHab ms)]
  | _ => throwError "ty_wf: not a type of the language: {t}"

/-- A closed type is a type in any scope; in the closed scope the proof is already the
    one that is wanted. -/
partial def ifClosed (n : Nat) (p : Expr) : MetaM Expr := do
  if n == 0 then return p
  let some t := (← whnfR (← inferType p)).getAppArgs[1]?
    | throwError "ty_wf: {← inferType p} is not a well-formedness proof"
  mkAppOptM ``LeanScript.Ty.WfIn.closed #[some (natE n), some t, some p]

/-- A proof of `Ty.WfShapeIn n s`. -/
partial def mkWfShapeIn (n : Nat) (s : Expr) : MetaM Expr := do
  let s ← whnf s
  match s.getAppFnArgs with
  | (``LeanScript.TyShape.prim, #[_, p]) =>
      mkAppOptM ``LeanScript.Ty.WfShapeIn.prim #[some (natE n), some p]
  | (``LeanScript.TyShape.enum, #[_, e]) =>
      mkAppOptM ``LeanScript.Ty.WfShapeIn.enum #[some (natE n), some e]
  | (``LeanScript.TyShape.fn, #[_, a, b]) =>
      -- the domain is checked closed: an occurrence may not stand to the left of an arrow
      mkAppOptM ``LeanScript.Ty.WfShapeIn.fn
        #[some (natE n), some a, some b, some (← mkWfInDomain a), some (← mkWfIn n b)]
  | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      let v ← mkAppM ``LeanScript.LeanPrimTyCovariant.val #[c]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.primCovariant
        #[some (natE n), some c, some (← mkWfIn n v)]
  | (``LeanScript.TyShape.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.record
        #[some (natE n), some fs, some (← mkWfAllIn n tys)]
  | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
      let tys ← mkAppM ``List.flatten #[← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]]
      mkAppOptM ``LeanScript.Ty.WfShapeIn.taggedUnion
        #[some (natE n), some l, some (← mkWfAllIn n tys)]
  | _ => throwError "ty_wf: not a shape of the language: {s}"

/-- A proof of `Ty.WfAllIn n ts`. -/
partial def mkWfAllIn (n : Nat) (ts : Expr) : MetaM Expr := do
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => mkAppOptM ``LeanScript.Ty.WfAllIn.nil #[some (natE n)]
  | (``List.cons, #[_, h, t]) =>
      mkAppOptM ``LeanScript.Ty.WfAllIn.cons
        #[some (natE n), some h, some t, some (← mkWfIn n h), some (← mkWfAllIn n t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.OccursIn i t`. -/
partial def mkOccursIn (i : Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  if (← instanceWf? t).isSome || (← hypWf? t).isSome then
    throwError "ty_wf: a closed type mentions no member of the scope around it"
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless i == 0 do throwError "ty_wf: `Ty.self` is member 0, not member {i}"
      return mkConst ``LeanScript.Ty.OccursIn.self
  | (``LeanScript.Ty.familyMember, #[j]) =>
      let some j := (← natOf? j) | throwError "ty_wf: the member number {j} is unknown"
      unless i == j do throwError "ty_wf: member {j} is not member {i}"
      mkAppOptM ``LeanScript.Ty.OccursIn.familyMember #[some (natE i)]
  | (``LeanScript.Ty.shape, #[s]) =>
      let cs ← mkAppM ``LeanScript.TyShape.children #[s]
      mkAppOptM ``LeanScript.Ty.OccursIn.shape
        #[some (natE i), some s, some (← mkOccursSomeIn i cs)]
  | _ => throwError "ty_wf: {t} does not mention member {i} of the scope around it"

/-- A proof of `Ty.OccursSomeIn i ts`: the first of the types that mentions member `i`. -/
partial def mkOccursSomeIn (i : Nat) (ts : Expr) : MetaM Expr := do
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => throwError "ty_wf: nothing here mentions member {i}"
  | (``List.cons, #[_, h, t]) =>
      try
        mkAppOptM ``LeanScript.Ty.OccursSomeIn.head
          #[some (natE i), some h, some t, some (← mkOccursIn i h)]
      catch _ =>
        mkAppOptM ``LeanScript.Ty.OccursSomeIn.tail
          #[some (natE i), some h, some t, some (← mkOccursSomeIn i t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.MembersOccur k ts`: each of the members below `k` is mentioned. -/
partial def mkMembersOccur (k : Nat) (ts : Expr) : MetaM Expr := do
  match k with
  | 0 => mkAppOptM ``LeanScript.Ty.MembersOccur.zero #[some ts]
  | j + 1 =>
      mkAppOptM ``LeanScript.Ty.MembersOccur.succ
        #[some (natE j), some ts, some (← mkMembersOccur j ts),
          some (← mkOccursSomeIn j ts)]

/-- A proof of `Ty.WfIn 0 a` for the **domain** of a function type, with a message that
    says what the closed scope means there. -/
partial def mkWfInDomain (a : Expr) : MetaM Expr := do
  try
    mkWfIn 0 a
  catch e =>
    let mentionsScope := (a.find? fun x =>
      x.isConstOf ``LeanScript.Ty.self || x.isAppOf ``LeanScript.Ty.familyMember).isSome
    if mentionsScope then
      throwError "ty_wf: the declaration being defined occurs to the left of an arrow, \
        which no type of the language does"
    else
      throw e

/- ### Inhabitation

The same walk, for `LeanScript.Ty.HabIn`: it answers "does this tree have a value, given
that the members listed in `S` do?".  A leaf that some instance or some hypothesis already
answers for is closed by `Ty.HabIn.of_wf` applied to that proof — a checked type has
values — so again no checked tree is looked at. -/

/-- A proof of `Ty.HabIn S t`. -/
partial def mkHabIn (S : List Nat) (t : Expr) : MetaM Expr := do
  let t ← tyHeadNorm t
  if let some p ← instanceWf? t then
    return ← mkAppOptM ``LeanScript.Ty.HabIn.of_wf #[some (← natListE S), none, some p]
  if let some p ← hypWf? t then
    return ← mkAppOptM ``LeanScript.Ty.HabIn.of_wf #[some (← natListE S), none, some p]
  match t.getAppFnArgs with
  | (``LeanScript.Ty.self, _) =>
      unless S.contains 0 do
        throwError "ty_wf: the declaration being defined is assumed to have a value by \
          its own definition, so the definition describes no value"
      mkAppOptM ``LeanScript.Ty.HabIn.self
        #[some (← natListE S), some (← memProof 0 S)]
  | (``LeanScript.Ty.familyMember, #[i]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member number {i} is unknown"
      unless S.contains i do
        throwError "ty_wf: member {i} of the family is not known to have a value here"
      mkAppOptM ``LeanScript.Ty.HabIn.familyMember
        #[some (← natListE S), some (natE i), some (← memProof i S)]
  | (``LeanScript.Ty.shape, #[s]) =>
      mkAppOptM ``LeanScript.Ty.HabIn.shape
        #[some (← natListE S), some s, some (← mkHabShapeIn S s)]
  | (``LeanScript.Ty.recTaggedUnion, #[l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.HabIn.recTaggedUnion
        #[some (← natListE S), some l, some (← mkHabSomeIn [] ctors)]
  | (``LeanScript.Ty.recObject, #[fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.HabIn.recObject
        #[some (← natListE S), some fs, some (← mkHabAllIn [] tys)]
  | (``LeanScript.Ty.recAlias, #[b]) =>
      mkAppOptM ``LeanScript.Ty.HabIn.recAlias
        #[some (← natListE S), some b, some (← mkHabIn [] b)]
  | (``LeanScript.Ty.mutualRecursiveFamily, #[f]) =>
      let ms ← mkAppM ``LeanScript.LeanMutualRecFamily.members #[f]
      mkAppOptM ``LeanScript.Ty.HabIn.mutualRecursiveFamily
        #[some (← natListE S), some f, some (← mkFamHab ms)]
  | _ => throwError "ty_wf: not a type of the language: {t}"

/-- A proof of `Ty.HabShapeIn S s`. -/
partial def mkHabShapeIn (S : List Nat) (s : Expr) : MetaM Expr := do
  let SE ← natListE S
  let s ← whnf s
  match s.getAppFnArgs with
  | (``LeanScript.TyShape.prim, #[_, p]) =>
      mkAppOptM ``LeanScript.Ty.HabShapeIn.prim #[some SE, some p]
  | (``LeanScript.TyShape.enum, #[_, e]) =>
      mkAppOptM ``LeanScript.Ty.HabShapeIn.enum #[some SE, some e]
  | (``LeanScript.TyShape.fn, #[_, a, b]) =>
      -- the constant function: only the result has to have a value
      mkAppOptM ``LeanScript.Ty.HabShapeIn.fn
        #[some SE, some a, some b, some (← mkHabIn S b)]
  | (``LeanScript.TyShape.primCovariant, #[_, c]) =>
      let c ← whnf c
      match c.getAppFnArgs with
      | (``LeanScript.LeanPrimTyCovariant.array, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.array #[some SE, some v]
      | (``LeanScript.LeanPrimTyCovariant.thunk, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.thunk
            #[some SE, some v, some (← mkHabIn S v)]
      | (``LeanScript.LeanPrimTyCovariant.lazy, #[_, v]) =>
          mkAppOptM ``LeanScript.Ty.HabShapeIn.lazy
            #[some SE, some v, some (← mkHabIn S v)]
      | _ => throwError "ty_wf: not an array, a thunk or a lazy value: {c}"
  | (``LeanScript.TyShape.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.HabShapeIn.record
        #[some SE, some fs, some (← mkHabAllIn S tys)]
  | (``LeanScript.TyShape.taggedUnion, #[_, l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.HabShapeIn.taggedUnion
        #[some SE, some l, some (← mkHabSomeIn S ctors)]
  | _ => throwError "ty_wf: not a shape of the language: {s}"

/-- A proof of `Ty.HabAllIn S ts`: every field of one constructor has a value. -/
partial def mkHabAllIn (S : List Nat) (ts : Expr) : MetaM Expr := do
  let SE ← natListE S
  let ts ← whnf ts
  match ts.getAppFnArgs with
  | (``List.nil, _) => mkAppOptM ``LeanScript.Ty.HabAllIn.nil #[some SE]
  | (``List.cons, #[_, h, t]) =>
      mkAppOptM ``LeanScript.Ty.HabAllIn.cons
        #[some SE, some h, some t, some (← mkHabIn S h), some (← mkHabAllIn S t)]
  | _ => throwError "ty_wf: not a list of types: {ts}"

/-- A proof of `Ty.HabSomeIn S cs`: the first constructor all of whose fields have a
    value. -/
partial def mkHabSomeIn (S : List Nat) (cs : Expr) : MetaM Expr := do
  let SE ← natListE S
  let cs ← whnf cs
  match cs.getAppFnArgs with
  | (``List.nil, _) =>
      throwError "ty_wf: no constructor here can be built, so the type has no values"
  | (``List.cons, #[_, h, t]) =>
      try
        mkAppOptM ``LeanScript.Ty.HabSomeIn.head
          #[some SE, some h, some t, some (← mkHabAllIn S h)]
      catch _ =>
        mkAppOptM ``LeanScript.Ty.HabSomeIn.tail
          #[some SE, some h, some t, some (← mkHabSomeIn S t)]
  | _ => throwError "ty_wf: not a list of constructors: {cs}"

/-- A proof of `Ty.MemberHab S m`, for one member of a family. -/
partial def mkMemberHab (S : List Nat) (m : Expr) : MetaM Expr := do
  let SE ← natListE S
  let m ← whnf m
  match m.getAppFnArgs with
  | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
      let ctors ← mkAppM ``LeanScript.LeanTaggedUnionSchema.toList #[l]
      mkAppOptM ``LeanScript.Ty.MemberHab.ctors
        #[some SE, some l, some (← mkHabSomeIn S ctors)]
  | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
      let tys ← mkAppM ``LeanScript.LeanRecordSchema.toList #[fs]
      mkAppOptM ``LeanScript.Ty.MemberHab.record
        #[some SE, some fs, some (← mkHabAllIn S tys)]
  | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
      mkAppOptM ``LeanScript.Ty.MemberHab.alias
        #[some SE, some b, some (← mkHabIn S b)]
  | _ => throwError "ty_wf: not a member of a family: {m}"

/-- A proof of `Ty.FamHab ms`: the least fixpoint, computed.  Members are added to the
    known set one at a time, each on the strength of the ones before it, until no more can
    be added; if one is left over, the family describes a member with no values. -/
partial def mkFamHab (msE : Expr) : MetaM Expr := do
  let ms ← listElems msE
  let n := ms.length
  let mut known : List Nat := []
  let mut proof ← mkAppOptM ``LeanScript.Ty.FamKnown.nil #[some msE]
  let mut progress := true
  while progress && known.length < n do
    progress := false
    for i in [0:n] do
      if known.contains i then continue
      let m := ms[i]!
      let some hm ← (try pure (some (← mkMemberHab known m)) catch _ => pure none)
        | continue
      let hEq ← mkEqRefl (← mkAppOptM ``Option.some
        #[some (mkApp (mkConst ``LeanScript.LeanFamMemberSchema) (mkConst ``LeanScript.Ty)),
          some m])
      proof ← mkAppOptM ``LeanScript.Ty.FamKnown.cons
        #[some msE, some (← natListE known), some (natE i), some m, some proof, some hEq,
          some hm]
      known := i :: known
      progress := true
  unless known.length == n do
    let missing := (List.range n).filter fun i => !known.contains i
    throwError "ty_wf: member {missing.head!} of this family has no values, so the \
      family describes no type"
  let SE ← natListE known
  let lenE ← mkAppM ``List.length #[msE]
  let allTy ← withLocalDeclD `i (mkConst ``Nat) fun i => do
    let body ← mkArrow (← mkAppM ``LT.lt #[i, lenE])
      (← mkAppM ``Membership.mem #[SE, i])
    mkForallFVars #[i] body
  mkAppOptM ``LeanScript.Ty.FamHab.mk
    #[some msE, some SE, some proof, some (← mkDecideProof allTy)]

end

/-- A proof of whichever proposition of `LeanScript.Ty.Wf` the goal is. -/
def mkWfProof (goal : Expr) : MetaM Expr := do
  let goal ← whnfR goal
  match goal.getAppFnArgs with
  | (``LeanScript.Ty.WfIn, #[n, t]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfIn n t
  | (``LeanScript.Ty.WfShapeIn, #[n, s]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfShapeIn n s
  | (``LeanScript.Ty.WfAllIn, #[n, ts]) =>
      let some n := (← natOf? n) | throwError "ty_wf: the scope {n} is unknown"
      mkWfAllIn n ts
  | (``LeanScript.Ty.OccursIn, #[i, t]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member {i} is unknown"
      mkOccursIn i t
  | (``LeanScript.Ty.OccursSomeIn, #[i, ts]) =>
      let some i := (← natOf? i) | throwError "ty_wf: the member {i} is unknown"
      mkOccursSomeIn i ts
  | (``LeanScript.Ty.MembersOccur, #[k, ts]) =>
      let some k := (← natOf? k) | throwError "ty_wf: the number of members {k} is unknown"
      mkMembersOccur k ts
  | (``LeanScript.Ty.HabIn, #[s, t]) => mkHabIn (← natListOf s) t
  | (``LeanScript.Ty.HabShapeIn, #[s, x]) => mkHabShapeIn (← natListOf s) x
  | (``LeanScript.Ty.HabAllIn, #[s, ts]) => mkHabAllIn (← natListOf s) ts
  | (``LeanScript.Ty.HabSomeIn, #[s, cs]) => mkHabSomeIn (← natListOf s) cs
  | (``LeanScript.Ty.MemberHab, #[s, m]) => mkMemberHab (← natListOf s) m
  | (``LeanScript.Ty.FamHab, #[ms]) => mkFamHab ms
  | _ => throwError "ty_wf: the goal is not a well-formedness of a type: {goal}"

/-- `ty_wf` proves that a tree is a type of the language, reusing the proof of every
    subtree that already has one instead of checking it again. -/
syntax (name := tyWfTactic) "ty_wf" : tactic

@[tactic tyWfTactic]
def elabTyWf : Tactic := fun _ => do
  let g ← getMainGoal
  g.withContext do
    let target ← instantiateMVars (← g.getType)
    let proof ← mkWfProof target
    unless ← isDefEq (← inferType proof) target do
      throwError "ty_wf: built a proof of {← inferType proof}, not of {target}"
    g.assign proof
  replaceMainGoal []

end LeanScript.Ty

end

end
