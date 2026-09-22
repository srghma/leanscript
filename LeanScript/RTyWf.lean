module

public import LeanScript.RTy

@[expose] public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# When does a recursive shape describe a type that **exists**?

The *counting* conditions of a shape — an enum has three constructors or more, a record
two fields or more, a family two members — are carried by the schemas of
`LeanScript.Schema`, so they need no check at all.  What is left are the conditions that
mention the type language itself, and they are the decidable predicates of this module:

* a recursive shape **mentions itself** (`RTy.hasSelf`): a wrapper that does not is
  erased into its field;
* every self-reference is one the scope allows (`RTy.selfRefs`, `selfRefsPlain` and
  `selfRefsInFamily`): a declaration that recurses on its own is pointed at by `.self`,
  and a member of a family by `.familyMember i` with `i` a member the family **has**;
* the type **has values** (`famAllInhabited`): `inductive Bad | mk : Bad → Bad` is the
  equation `T = T`, which no value satisfies;
* a mutual family is **strongly connected** (`famStronglyConnected`): declarations that
  do not each reach the other are not one family.

`recTUWf`, `recObjWf`, `recAliasWf` and `famWf` are those conditions for the four
recursive payloads, and `RTy.wf` runs them at every node of a whole payload.  They are
stated here, *before* `LeanScript.Ty`, for one reason: the recursive constructors of `Ty`
take the proof as an argument, so a `Ty` is well formed by construction and there is no
subtype of the well-formed types to carry around.
-/


/-! ## Which members of a recursive declaration a payload mentions -/

mutual

/-- The self-references of the enclosing recursive declaration that this type makes.  A
    *nested* recursive shape is not looked into: its `.self`s are its own. -/
def RTy.selfRefs : RTy → List SelfRef
  | .selfRef s => [s]
  | .fn a b => RTy.selfRefs a ++ RTy.selfRefs b
  | .primCovariant s => RTy.selfRefsCov s
  | .record fs => RTy.selfRefsA2 fs
  | .taggedUnion l => RTy.selfRefsTU l
  | .withComputedFields b _ => RTy.selfRefs b
  | _ => []

/-- `RTy.selfRefs`, on an invariant type former. -/
def RTy.selfRefsCov : LeanPrimTyCovariant RTy → List SelfRef
  | .array a | .thunk a | .lazy a => RTy.selfRefs a

/-- `RTy.selfRefs`, on a list of types. -/
def RTy.selfRefsList : List RTy → List SelfRef
  | [] => []
  | t :: ts => RTy.selfRefs t ++ RTy.selfRefsList ts

/-- `RTy.selfRefs`, on the constructors of a layout. -/
def RTy.selfRefsCtors : List (List RTy) → List SelfRef
  | [] => []
  | fs :: l => RTy.selfRefsList fs ++ RTy.selfRefsCtors l

/-- `RTy.selfRefs`, on the fields of a record. -/
def RTy.selfRefsA2 : LeanRecordSchema RTy → List SelfRef
  | ⟨a, b, rest⟩ => RTy.selfRefs a ++ RTy.selfRefs b ++ RTy.selfRefsList rest

/-- `RTy.selfRefs`, on the fields of a constructor that has at least one. -/
def RTy.selfRefsNE : NonEmptyList RTy → List SelfRef
  | ⟨a, as⟩ => RTy.selfRefs a ++ RTy.selfRefsList as

/-- `RTy.selfRefs`, on the constructors of a tagged union. -/
def RTy.selfRefsTU : LeanTaggedUnionSchema RTy → List SelfRef
  | .payloadFirst f n r => RTy.selfRefsNE f ++ RTy.selfRefsList n ++ RTy.selfRefsCtors r
  | .skip rest => RTy.selfRefsCP rest

/-- `RTy.selfRefs`, on the constructors that follow a field-less one. -/
def RTy.selfRefsCP : CtorsWithPayload RTy → List SelfRef
  | .here f r => RTy.selfRefsNE f ++ RTy.selfRefsCtors r
  | .skip rest => RTy.selfRefsCP rest

end

/-- The self-references one member of a family makes. -/
def LeanFamMemberSchema_RTy.selfRefs : LeanFamMemberSchema RTy → List SelfRef
  | .ctors l => RTy.selfRefsTU l
  | .record fs => RTy.selfRefsA2 fs
  | .alias b => RTy.selfRefs b


/-! ## Does a payload mention the declaration it sits in?

A payload mentions it exactly when it makes a self-reference at all, so these are
`RTy.selfRefs` read as a `Bool` rather than a second traversal of the same shapes. -/

/-- Does this type mention the recursive declaration whose body it sits in?  A *nested*
    recursive shape is not looked into: its `.self`s are its own. -/
def RTy.hasSelf (t : RTy) : Bool := !(RTy.selfRefs t).isEmpty

/-- `RTy.hasSelf`, on an invariant type former. -/
def RTy.hasSelfCov (s : LeanPrimTyCovariant RTy) : Bool := !(RTy.selfRefsCov s).isEmpty

/-- `RTy.hasSelf`, on a list of types. -/
def RTy.hasSelfList (ts : List RTy) : Bool := !(RTy.selfRefsList ts).isEmpty

/-- `RTy.hasSelf`, on the constructors of a layout. -/
def RTy.hasSelfCtors (l : List (List RTy)) : Bool := !(RTy.selfRefsCtors l).isEmpty

/-- `RTy.hasSelf`, on the fields of a record. -/
def RTy.hasSelfA2 (fs : LeanRecordSchema RTy) : Bool := !(RTy.selfRefsA2 fs).isEmpty

/-- `RTy.hasSelf`, on the fields of a constructor that has at least one. -/
def RTy.hasSelfNE (f : NonEmptyList RTy) : Bool := !(RTy.selfRefsNE f).isEmpty

/-- `RTy.hasSelf`, on the constructors of a tagged union. -/
def RTy.hasSelfTU (l : LeanTaggedUnionSchema RTy) : Bool := !(RTy.selfRefsTU l).isEmpty

/-- `RTy.hasSelf`, on the constructors that follow a field-less one. -/
def RTy.hasSelfCP (c : CtorsWithPayload RTy) : Bool := !(RTy.selfRefsCP c).isEmpty

/-- `RTy.hasSelf`, on the constructors of a recursive tagged union. -/
def RTy.hasSelfRecTU (l : LeanTaggedUnionSchema RTy) : Bool := RTy.hasSelfTU l

/-- `RTy.hasSelf`, on the fields of a recursive record. -/
def RTy.hasSelfRecObj (fs : LeanRecordSchema RTy) : Bool := RTy.hasSelfA2 fs

/-- `RTy.hasSelf`, on the body of a recursive newtype. -/
def RTy.hasSelfAlias (b : RTy) : Bool := RTy.hasSelf b

/-- Does this member mention the declaration it belongs to at all? -/
def LeanFamMemberSchema_RTy.hasSelf : LeanFamMemberSchema RTy → Bool
  | .ctors l => RTy.hasSelfTU l
  | .record fs => RTy.hasSelfA2 fs
  | .alias b => RTy.hasSelf b

/-- Are these the self-references of a declaration that **recurses on its own** — each of
    them a bare `.self`, and none of them a reference to a sibling, which it has none of?
    This is what makes `RTy.asWithSelf` total on the payload. -/
def selfRefsPlain (refs : List SelfRef) : Bool := refs.all (· == SelfRef.self)

/-- Are these the self-references of one member of a family of `numMembers` members —
    each of them a member the family has, and none of them a bare `.self`, which says
    nothing inside a family?  This is what makes `RTy.asMutualRef numMembers` total on
    the payload. -/
def selfRefsInFamily (numMembers : Nat) (refs : List SelfRef) : Bool :=
  refs.all fun r => match r with
    | .self => false
    | .familyMember i => i < numMembers

/-- The members of its family that a list of self-references points at. -/
def selfRefMembers (refs : List SelfRef) : List Nat := refs.filterMap SelfRef.member?

/-! ## Which members have values at all -/

mutual

/-- Can a value of this type be built when member `i` of the enclosing recursive
    declaration can be built exactly when `avail[i]!` says so? -/
def RTy.inhabWith (avail : List Bool) : RTy → Bool
  | .selfRef s => (avail[s.slot]?).getD false
  | .prim _ => true
  -- a function needs no argument to exist, only a result
  | .fn _ r => RTy.inhabWith avail r
  | .primCovariant s => RTy.inhabWithCov avail s
  | .enum _ => true
  | .record fs => RTy.inhabWithA2 avail fs
  | .taggedUnion l => RTy.inhabWithTU avail l
  -- a nested recursive shape opens a scope of its own, so it mentions no member of
  -- ours; whether *it* has values is checked where it is
  | .recTaggedUnion _ => true
  | .recObject _ => true
  | .recAlias _ => true
  | .mutualRecursiveFamily _ => true
  -- caching a value computed from the value changes nothing about which values there are
  | .withComputedFields b _ => RTy.inhabWith avail b

/-- `RTy.inhabWith`, on an invariant type former. -/
def RTy.inhabWithCov (avail : List Bool) : LeanPrimTyCovariant RTy → Bool
  -- the empty array and the empty list hold nothing
  | .array _ => true
  | .thunk a | .lazy a => RTy.inhabWith avail a

/-- `RTy.inhabWith`, on the fields of one constructor: it needs all of them. -/
def RTy.inhabWithAll (avail : List Bool) : List RTy → Bool
  | [] => true
  | t :: ts => RTy.inhabWith avail t && RTy.inhabWithAll avail ts

/-- `RTy.inhabWith`, on the constructors of a layout: it needs one of them. -/
def RTy.inhabWithSome (avail : List Bool) : List (List RTy) → Bool
  | [] => false
  | fs :: l => RTy.inhabWithAll avail fs || RTy.inhabWithSome avail l

/-- `RTy.inhabWith`, on the fields of a record: it needs all of them. -/
def RTy.inhabWithA2 (avail : List Bool) : LeanRecordSchema RTy → Bool
  | ⟨a, b, rest⟩ =>
      RTy.inhabWith avail a && RTy.inhabWith avail b && RTy.inhabWithAll avail rest

/-- `RTy.inhabWith`, on the fields of a constructor that has at least one. -/
def RTy.inhabWithNE (avail : List Bool) : NonEmptyList RTy → Bool
  | ⟨a, as⟩ => RTy.inhabWith avail a && RTy.inhabWithAll avail as

/-- `RTy.inhabWith`, on the constructors of a tagged union: it needs one of them. -/
def RTy.inhabWithTU (avail : List Bool) : LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r =>
      RTy.inhabWithNE avail f || RTy.inhabWithAll avail n || RTy.inhabWithSome avail r
  -- the first constructor has no fields at all, so it can always be built
  | .skip _ => true

end

/-- `RTy.inhabWith`, on one member of a family. -/
def LeanFamMemberSchema_RTy.inhabWith (avail : List Bool) : LeanFamMemberSchema RTy → Bool
  | .ctors l => RTy.inhabWithTU avail l
  | .record fs => RTy.inhabWithA2 avail fs
  | .alias b => RTy.inhabWith avail b

/-- One step of the fixed point: which members are buildable, given which were. -/
def famInhabStep (ms : List (LeanFamMemberSchema RTy)) (avail : List Bool) : List Bool :=
  ms.map (LeanFamMemberSchema_RTy.inhabWith avail)

/-- Iterate `famInhabStep`. -/
def famInhabIter : Nat → List (LeanFamMemberSchema RTy) → List Bool → List Bool
  | 0, _, avail => avail
  | n + 1, ms, avail => famInhabIter n ms (famInhabStep ms avail)

/-- Which members of a recursive declaration have values at all.  The step is monotone
    and there are `ms.length` members, so `ms.length` iterations from "none of them"
    reach the fixed point; one more is taken for good measure. -/
def famInhabited (ms : List (LeanFamMemberSchema RTy)) : List Bool :=
  famInhabIter (ms.length + 1) ms (ms.map fun _ => false)

/-- Does every member of this recursive declaration have values? -/
def famAllInhabited (ms : List (LeanFamMemberSchema RTy)) : Bool := (famInhabited ms).all id

/-! ## Strong connectivity -/

/-- Which members each member mentions. -/
def famEdges (ms : List (LeanFamMemberSchema RTy)) : List (List Nat) :=
  ms.map (fun m => selfRefMembers (LeanFamMemberSchema_RTy.selfRefs m))

/-- Add to `acc` everything its members mention. -/
def famReachStep (edges : List (List Nat)) (acc : List Nat) : List Nat :=
  acc.foldl (fun a i => ((edges[i]?).getD []).foldl
    (fun a j => if a.contains j then a else j :: a) a) acc

/-- Iterate `famReachStep`. -/
def famReachIter : Nat → List (List Nat) → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, edges, acc => famReachIter n edges (famReachStep edges acc)

/-- The members reachable from member `i`, `i` itself included. -/
def famReach (ms : List (LeanFamMemberSchema RTy)) (i : Nat) : List Nat :=
  famReachIter (ms.length + 1) (famEdges ms) [i]

/-- Does every member of the block reach every member of the block? -/
def famStronglyConnected (ms : List (LeanFamMemberSchema RTy)) : Bool :=
  (List.range ms.length).all fun i =>
    let r := famReach ms i
    (List.range ms.length).all fun j => r.contains j

/-! ## The four recursive payloads

Each of these is the whole of what makes the shape it names a description of a type that
exists.  They are what the recursive constructors of `LeanScript.Ty` ask a proof of. -/

/-- A recursive tagged union mentions itself — and only itself, since it has one
    member — and has a constructor that can be built without a value of its own type, so
    that it has values at all: `inductive Bad | l : Bad → Bad | r : Bad → Bad` has
    none. -/
def recTUWf (l : LeanTaggedUnionSchema RTy) : Bool :=
  RTy.hasSelfTU l && selfRefsPlain (RTy.selfRefsTU l) && famAllInhabited [.ctors l]

/-- A recursive record mentions itself, points only at itself, and has values:
    `structure S where s : S; n : Nat` has none. -/
def recObjWf (fs : LeanRecordSchema RTy) : Bool :=
  RTy.hasSelfA2 fs && selfRefsPlain (RTy.selfRefsA2 fs) && famAllInhabited [.record fs]

/-- A recursive newtype mentions itself — otherwise the wrapper is erased into its field
    and there is no `recAlias` at all — and does so guardedly, so that the equation it
    stands for has a solution: `recAlias (.self)` is `T = T`, which no value
    satisfies, while `recAlias (.array (.self))` is the empty array and more. -/
def recAliasWf (b : RTy) : Bool :=
  RTy.hasSelf b && selfRefsPlain (RTy.selfRefs b) && famAllInhabited [.alias b]

/-- A family mentions only members it has, is a family rather than a `mutual` block of
    unrelated declarations — each member reaches every member — and every member of it
    has values. -/
def famWf (f : LeanMutualRecFamily RTy) : Bool :=
  f.members.all
      (fun m => selfRefsInFamily f.members.length (LeanFamMemberSchema_RTy.selfRefs m))
    && famStronglyConnected f.members && famAllInhabited f.members

/-! ## Well-formedness of a whole payload

Each recursive shape is checked by the predicate of its payload, and so is each shape
nested in it. -/

mutual

/-- `Ty.wf`, one layer down: this type may mention the declaration it sits in.

    The `.fn` case is where **strict positivity** is imposed: the declaration being
    defined may not occur in the *domain* of a function type.  Without that condition a
    closed, block-free term already diverges — `μX. { f : X → Nat, pad : Nat }` writes
    Curry's `Ω` out of `lam`/`ap`/`ctor`/`proj` alone, which is what
    `LeanScript/DivergeNeg.lean` used to prove.  Nothing a Lean source declaration needs is
    lost: Lean's own inductive types are strictly positive. -/
def RTy.wf : RTy → Bool
  | .selfRef _ => true
  | .prim _ => true
  | .fn a b => !RTy.hasSelf a && RTy.wf a && RTy.wf b
  | .primCovariant s => RTy.wfCov s
  | .enum _ => true
  | .record fs => RTy.wfA2 fs
  | .taggedUnion l => RTy.wfTU l
  | .recTaggedUnion l => recTUWf l && RTy.wfTU l
  | .recObject fs => recObjWf fs && RTy.wfA2 fs
  | .recAlias b => recAliasWf b && RTy.wf b
  | .mutualRecursiveFamily f => famWf f && LeanFamMemberSchema_RTy.wfFamily f
  | .withComputedFields b _ => RTy.wf b

/-- `RTy.wf`, on an invariant type former. -/
def RTy.wfCov : LeanPrimTyCovariant RTy → Bool
  | .array a | .thunk a | .lazy a => RTy.wf a

/-- `RTy.wf`, on a list of types. -/
def RTy.wfList : List RTy → Bool
  | [] => true
  | t :: ts => RTy.wf t && RTy.wfList ts

/-- `RTy.wf`, on the constructors of a layout. -/
def RTy.wfCtors : List (List RTy) → Bool
  | [] => true
  | fs :: l => RTy.wfList fs && RTy.wfCtors l

/-- `RTy.wf`, on the fields of a record. -/
def RTy.wfA2 : LeanRecordSchema RTy → Bool
  | ⟨a, b, rest⟩ => RTy.wf a && RTy.wf b && RTy.wfList rest

/-- `RTy.wf`, on the fields of a constructor that has at least one. -/
def RTy.wfNE : NonEmptyList RTy → Bool
  | ⟨a, as⟩ => RTy.wf a && RTy.wfList as

/-- `RTy.wf`, on the constructors of a tagged union. -/
def RTy.wfTU : LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r => RTy.wfNE f && RTy.wfList n && RTy.wfCtors r
  | .skip rest => RTy.wfCP rest

/-- `RTy.wf`, on the constructors that follow a field-less one. -/
def RTy.wfCP : CtorsWithPayload RTy → Bool
  | .here f r => RTy.wfNE f && RTy.wfCtors r
  | .skip rest => RTy.wfCP rest

/-- `RTy.wf`, on one member of a family. -/
def LeanFamMemberSchema_RTy.wf : LeanFamMemberSchema RTy → Bool
  | .ctors l => RTy.wfTU l
  | .record fs => RTy.wfA2 fs
  | .alias b => RTy.wf b

/-- `RTy.wf`, on the members of a family. -/
def LeanFamMemberSchema_RTy.wfList : List (LeanFamMemberSchema RTy) → Bool
  | [] => true
  | m :: ms => LeanFamMemberSchema_RTy.wf m && LeanFamMemberSchema_RTy.wfList ms

/-- `RTy.wf`, on every member of a family. -/
def LeanFamMemberSchema_RTy.wfFamily : LeanMutualRecFamily RTy → Bool
  | .selectedThenMore before current next after =>
      LeanFamMemberSchema_RTy.wfList before && LeanFamMemberSchema_RTy.wf current && LeanFamMemberSchema_RTy.wf next
        && LeanFamMemberSchema_RTy.wfList after
  | .selectedLast first before current =>
      LeanFamMemberSchema_RTy.wf first && LeanFamMemberSchema_RTy.wfList before && LeanFamMemberSchema_RTy.wf current

end

/-! ## Sealed payloads: a payload that carries its own well-formedness

The recursive shapes of `LeanScript.Ty` used to take *two* arguments, a payload and a
proof about it, with the proof defaulted to `by decide`.  They take one now: a **sealed**
payload, which is the payload together with `h_wf`, the proposition that says the shape
it describes is a type that exists.

Two things follow.  A recursive constructor of `Ty` has one argument again, so a match on
it binds one thing and the proof travels with the payload rather than beside it.  And the
proof field is a `Prop`, so it is irrelevant to equality: two sealed payloads with the
same schema *are* the same sealed payload, and `Ty.beq` never has to look at a proof.

Writing one out costs a `by decide` and nothing else — the field is an auto-bound
`by decide` when the structure is built with `LeanTaggedUnionSchemaSealed.mk l`, and
`⟨l, by decide⟩` in anonymous-constructor notation — whenever `l` is a recursive tagged
union that a value exists of. -/

/-- Well-formedness of a payload, as a proposition: the shape it describes is a type that
    exists.  This is `RTy.wf`, read as a `Prop`, and it is decidable, so a payload written
    out settles it `by decide`. -/
def RTy.Wf (t : RTy) : Prop := RTy.wf t = true

instance (t : RTy) : Decidable (RTy.Wf t) := inferInstanceAs (Decidable (RTy.wf t = true))

/-- A recursive tagged union that carries its own well-formedness: the payload of
    `Ty.recTaggedUnion`. -/
structure LeanTaggedUnionSchemaSealed where
  /-- The constructors of the declaration, in declaration order. -/
  schema : LeanTaggedUnionSchema RTy
  /-- It mentions itself, points only at itself, and has values. -/
  h_wf : RTy.Wf (.recTaggedUnion schema) := by decide

/-- A recursive record that carries its own well-formedness: the payload of
    `Ty.recObject`. -/
structure LeanRecordSchemaSealed where
  /-- The fields of the declaration, in declaration order. -/
  fields : LeanRecordSchema RTy
  /-- It mentions itself, points only at itself, and has values. -/
  h_wf : RTy.Wf (.recObject fields) := by decide

/-- A recursive newtype that carries its own well-formedness: the payload of
    `Ty.recAlias`. -/
structure RTySealed where
  /-- The single field of the declaration, with the wrapper erased. -/
  body : RTy
  /-- It mentions itself, guardedly, so the equation it stands for has a solution. -/
  h_wf : RTy.Wf (.recAlias body) := by decide

/-- A mutual recursive family that carries its own well-formedness: the payload of
    `Ty.mutualRecursiveFamily`. -/
structure LeanMutualRecFamilySealed where
  /-- The members of the family, and which of them this type is. -/
  family : LeanMutualRecFamily RTy
  /-- Every `.self` points at a member the family has, the family is strongly connected,
      and every member has values. -/
  h_wf : RTy.Wf (.mutualRecursiveFamily family) := by decide

/-- Sealed payloads with the same schema are equal: the proof field is a `Prop`. -/
theorem LeanTaggedUnionSchemaSealed.eq_of_schema_eq :
    ∀ {a b : LeanTaggedUnionSchemaSealed}, a.schema = b.schema → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- The same, for a recursive record. -/
theorem LeanRecordSchemaSealed.eq_of_fields_eq :
    ∀ {a b : LeanRecordSchemaSealed}, a.fields = b.fields → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- The same, for a recursive newtype. -/
theorem RTySealed.eq_of_body_eq : ∀ {a b : RTySealed}, a.body = b.body → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- The same, for a mutual family. -/
theorem LeanMutualRecFamilySealed.eq_of_family_eq :
    ∀ {a b : LeanMutualRecFamilySealed}, a.family = b.family → a = b
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-! ## The degenerate recursive declarations, refuted

These are the declarations Lean accepts and no compiled program can hold a value of.
They are `RTy`s — nothing about their *shape* is wrong — and the predicates above refuse
them, so there is no `Ty` for them: the corresponding constructor of `LeanScript.Ty` cannot
be applied. -/

/-- `inductive Bad | mk : Bad → Bad` is read as the recursive newtype whose body is the
    declaration itself, i.e. as the equation `T = T`.  No value satisfies it. -/
theorem not_recAliasWf_selfLoop : recAliasWf (.self) = false := by decide

/-- `structure Worse where w : Worse; n : Nat` is the same mistake one shape along: a
    record needs *all* of its fields, and one of them is the record itself. -/
theorem not_recObjWf_selfField : recObjWf ⟨.self, .prim .nat, []⟩ = false := by decide

/-- A recursive newtype that does *not* mention itself is not one either: its wrapper is
    erased into its field, and the type it describes is just that field. -/
theorem not_recAliasWf_noSelf : recAliasWf (.prim .nat) = false := by decide

/-- A guarded recursive newtype — `structure Rose where kids : Array Rose` — *is* well
    formed: the empty array holds no `Rose`, so a `Rose` can be built. -/
theorem recAliasWf_array : recAliasWf (.array (.self)) = true := by decide

/-- And so is a recursive sum with a base case: `inductive T | leaf | node : T → T → T`. -/
theorem recTUWf_tree : recTUWf (.skip (.here ⟨.self, [.self]⟩ [])) = true := by decide

/-! ### A declaration points back with the reference its scope has

A declaration that recurses on its own is pointed at by `.self`, and a member of a
family by `.familyMember i`.  Neither scope accepts the other's reference, which is what
makes `RTy.asWithSelf` and `RTy.asMutualRef` the readings of a well-formed payload. -/

/-- `mutual inductive Tree | node : Nat → Forest; inductive Forest | nil | cons : Tree →
    Forest → Forest end` is a family of two members that each point at the other by
    number, and it is well formed: `Forest.nil` builds a value without one of either. -/
theorem famWf_treeForest :
    RTy.wf (.mutualRecursiveFamily (.selectedThenMore []
      (.record ⟨.prim .nat, .familyMember 1, []⟩)
      (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
      [])) = true := by decide

/-- The same family with a bare `.self` in place of each member number is **not** well
    formed: inside a family, `.self` does not say which member is meant. -/
theorem not_famWf_treeForest_plainSelf :
    RTy.wf (.mutualRecursiveFamily (.selectedThenMore []
      (.record ⟨.prim .nat, .self, []⟩)
      (.ctors (.skip (.here ⟨.self, [.self]⟩ [])))
      [])) = false := by decide

/-- And a declaration that recurses on its own is not written with a member number: it
    is not a family, so it has no member `0` to point at. -/
theorem not_recTUWf_familyMember :
    recTUWf (.skip (.here ⟨.familyMember 0, [.familyMember 0]⟩ [])) = false := by decide

/-! ## Strict positivity, refuted and permitted

A recursive declaration whose own type occurs to the **left** of an arrow is the one
shape that makes the term language diverge with no loop in it at all: at
`μX. { f : X → Nat, pad : Nat }` the λ-calculus core writes Curry's `Ω`.  `RTy.wf`
refuses it, so there is no such `Ty`. -/

/-- The negative recursive record `μX. { f : X → Nat, pad : Nat }` — the shape Curry's
    `Ω` is written at — is **not** well formed: `.self` stands in the domain of an
    arrow. -/
theorem not_wf_negRecObject :
    RTy.wf (.recObject ⟨.fn (.self) (.prim .nat), .prim .nat, []⟩) = false := by decide

/-- The same shape one level in: a negative occurrence buried under a list is refused
    too, since `RTy.hasSelf` looks through the covariant type formers. -/
theorem not_wf_negRecObject_nested :
    RTy.wf (.recObject ⟨.fn (.array (.self)) (.prim .nat), .prim .nat, []⟩) = false := by
  decide

/-- A **positive** occurrence is untouched: `inductive T | leaf | node : (Nat → T) → T` —
    an infinitely branching tree — has `.self` to the *right* of an arrow, and is well
    formed. -/
theorem wf_posRecTU :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.fn (.prim .nat) (.self), []⟩ []))) = true := by
  decide

/-- The negative counterpart of the same declaration,
    `inductive Bad | leaf | node : (Bad → Nat) → Bad`, is refused. -/
theorem not_wf_negRecTU :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.fn (.self) (.prim .nat), []⟩ []))) = false := by
  decide

/-- And so is the shape every Lean inductive type has: no arrow over `.self` at all. -/
theorem wf_recTU_tree :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.self, [.self]⟩ []))) = true := by decide

end LeanScript

end
