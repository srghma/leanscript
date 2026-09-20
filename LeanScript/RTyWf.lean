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
* every `.self` points at a member the declaration **has** (`RTy.selfIdxs`,
  `selfIdxsOk`);
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

/-! ## Does a payload mention the declaration it sits in? -/

mutual

/-- Does this type mention the recursive declaration whose body it sits in?  A *nested*
    recursive shape is not looked into: its `.self`s are its own. -/
def RTy.hasSelf : RTy → Bool
  | .self _ => true
  | .fn a b => RTy.hasSelf a || RTy.hasSelf b
  | .primCovariant s => RTy.hasSelfCov s
  | .record fs => RTy.hasSelfA2 fs
  | .taggedUnion l => RTy.hasSelfTU l
  | _ => false

/-- `RTy.hasSelf`, on an invariant type former. -/
def RTy.hasSelfCov : LeanPrimTyCovariant RTy → Bool
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => RTy.hasSelf a

/-- `RTy.hasSelf`, on a list of types. -/
def RTy.hasSelfList : List RTy → Bool
  | [] => false
  | t :: ts => RTy.hasSelf t || RTy.hasSelfList ts

/-- `RTy.hasSelf`, on the constructors of a layout. -/
def RTy.hasSelfCtors : List (List RTy) → Bool
  | [] => false
  | fs :: l => RTy.hasSelfList fs || RTy.hasSelfCtors l

/-- `RTy.hasSelf`, on the fields of a record. -/
def RTy.hasSelfA2 : LeanRecordSchema RTy → Bool
  | ⟨a, b, rest⟩ => RTy.hasSelf a || RTy.hasSelf b || RTy.hasSelfList rest

/-- `RTy.hasSelf`, on the fields of a constructor that has at least one. -/
def RTy.hasSelfNE : NonEmptyList RTy → Bool
  | ⟨a, as⟩ => RTy.hasSelf a || RTy.hasSelfList as

/-- `RTy.hasSelf`, on the constructors of a tagged union. -/
def RTy.hasSelfTU : LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r => RTy.hasSelfNE f || RTy.hasSelfList n || RTy.hasSelfCtors r
  | .skip rest => RTy.hasSelfCP rest

/-- `RTy.hasSelf`, on the constructors that follow a field-less one. -/
def RTy.hasSelfCP : CtorsWithPayload RTy → Bool
  | .here f r => RTy.hasSelfNE f || RTy.hasSelfCtors r
  | .skip rest => RTy.hasSelfCP rest

end

/-- `RTy.hasSelf`, on the constructors of a recursive tagged union. -/
def RTy.hasSelfRecTU : LeanTaggedUnionSchema RTy → Bool
  | l => RTy.hasSelfTU l

/-- `RTy.hasSelf`, on the fields of a recursive record. -/
def RTy.hasSelfRecObj : LeanRecordSchema RTy → Bool
  | fs => RTy.hasSelfA2 fs

/-- `RTy.hasSelf`, on the body of a recursive newtype. -/
def RTy.hasSelfAlias : RTy → Bool
  | b => RTy.hasSelf b

/-! ## Which members of a recursive declaration a payload mentions -/

mutual

/-- The members of the enclosing recursive declaration that this type mentions.  A
    *nested* recursive shape is not looked into: its `.self`s are its own. -/
def RTy.selfIdxs : RTy → List Nat
  | .self i => [i]
  | .fn a b => RTy.selfIdxs a ++ RTy.selfIdxs b
  | .primCovariant s => RTy.selfIdxsCov s
  | .record fs => RTy.selfIdxsA2 fs
  | .taggedUnion l => RTy.selfIdxsTU l
  | _ => []

/-- `RTy.selfIdxs`, on an invariant type former. -/
def RTy.selfIdxsCov : LeanPrimTyCovariant RTy → List Nat
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => RTy.selfIdxs a

/-- `RTy.selfIdxs`, on a list of types. -/
def RTy.selfIdxsList : List RTy → List Nat
  | [] => []
  | t :: ts => RTy.selfIdxs t ++ RTy.selfIdxsList ts

/-- `RTy.selfIdxs`, on the constructors of a layout. -/
def RTy.selfIdxsCtors : List (List RTy) → List Nat
  | [] => []
  | fs :: l => RTy.selfIdxsList fs ++ RTy.selfIdxsCtors l

/-- `RTy.selfIdxs`, on the fields of a record. -/
def RTy.selfIdxsA2 : LeanRecordSchema RTy → List Nat
  | ⟨a, b, rest⟩ => RTy.selfIdxs a ++ RTy.selfIdxs b ++ RTy.selfIdxsList rest

/-- `RTy.selfIdxs`, on the fields of a constructor that has at least one. -/
def RTy.selfIdxsNE : NonEmptyList RTy → List Nat
  | ⟨a, as⟩ => RTy.selfIdxs a ++ RTy.selfIdxsList as

/-- `RTy.selfIdxs`, on the constructors of a tagged union. -/
def RTy.selfIdxsTU : LeanTaggedUnionSchema RTy → List Nat
  | .payloadFirst f n r => RTy.selfIdxsNE f ++ RTy.selfIdxsList n ++ RTy.selfIdxsCtors r
  | .skip rest => RTy.selfIdxsCP rest

/-- `RTy.selfIdxs`, on the constructors that follow a field-less one. -/
def RTy.selfIdxsCP : CtorsWithPayload RTy → List Nat
  | .here f r => RTy.selfIdxsNE f ++ RTy.selfIdxsCtors r
  | .skip rest => RTy.selfIdxsCP rest

end

/-- The members of its family that one member mentions. -/
def FamMember.selfIdxs : FamMember → List Nat
  | .ctors l => RTy.selfIdxsTU l
  | .record fs => RTy.selfIdxsA2 fs
  | .alias b => RTy.selfIdxs b

/-- Does this member mention the declaration it belongs to at all? -/
def FamMember.hasSelf : FamMember → Bool
  | .ctors l => RTy.hasSelfTU l
  | .record fs => RTy.hasSelfA2 fs
  | .alias b => RTy.hasSelf b

/-- Does every `.self` here point at a member the declaration has? -/
def selfIdxsOk (numMembers : Nat) (idxs : List Nat) : Bool := idxs.all (· < numMembers)

/-! ## Which members have values at all -/

mutual

/-- Can a value of this type be built when member `i` of the enclosing recursive
    declaration can be built exactly when `avail[i]!` says so? -/
def RTy.inhabWith (avail : List Bool) : RTy → Bool
  | .self i => (avail[i]?).getD false
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

/-- `RTy.inhabWith`, on an invariant type former. -/
def RTy.inhabWithCov (avail : List Bool) : LeanPrimTyCovariant RTy → Bool
  -- the empty array and the empty list hold nothing
  | .array _ | .list _ => true
  | .task a | .promise a | .thunk a | .lazy a => RTy.inhabWith avail a

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
def FamMember.inhabWith (avail : List Bool) : FamMember → Bool
  | .ctors l => RTy.inhabWithTU avail l
  | .record fs => RTy.inhabWithA2 avail fs
  | .alias b => RTy.inhabWith avail b

/-- One step of the fixed point: which members are buildable, given which were. -/
def famInhabStep (ms : List FamMember) (avail : List Bool) : List Bool :=
  ms.map (FamMember.inhabWith avail)

/-- Iterate `famInhabStep`. -/
def famInhabIter : Nat → List FamMember → List Bool → List Bool
  | 0, _, avail => avail
  | n + 1, ms, avail => famInhabIter n ms (famInhabStep ms avail)

/-- Which members of a recursive declaration have values at all.  The step is monotone
    and there are `ms.length` members, so `ms.length` iterations from "none of them"
    reach the fixed point; one more is taken for good measure. -/
def famInhabited (ms : List FamMember) : List Bool :=
  famInhabIter (ms.length + 1) ms (ms.map fun _ => false)

/-- Does every member of this recursive declaration have values? -/
def famAllInhabited (ms : List FamMember) : Bool := (famInhabited ms).all id

/-! ## Strong connectivity -/

/-- Which members each member mentions. -/
def famEdges (ms : List FamMember) : List (List Nat) :=
  ms.map FamMember.selfIdxs

/-- Add to `acc` everything its members mention. -/
def famReachStep (edges : List (List Nat)) (acc : List Nat) : List Nat :=
  acc.foldl (fun a i => ((edges[i]?).getD []).foldl
    (fun a j => if a.contains j then a else j :: a) a) acc

/-- Iterate `famReachStep`. -/
def famReachIter : Nat → List (List Nat) → List Nat → List Nat
  | 0, _, acc => acc
  | n + 1, edges, acc => famReachIter n edges (famReachStep edges acc)

/-- The members reachable from member `i`, `i` itself included. -/
def famReach (ms : List FamMember) (i : Nat) : List Nat :=
  famReachIter (ms.length + 1) (famEdges ms) [i]

/-- Does every member of the block reach every member of the block? -/
def famStronglyConnected (ms : List FamMember) : Bool :=
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
  RTy.hasSelfTU l && selfIdxsOk 1 (RTy.selfIdxsTU l) && famAllInhabited [.ctors l]

/-- A recursive record mentions itself, points only at itself, and has values:
    `structure S where s : S; n : Nat` has none. -/
def recObjWf (fs : LeanRecordSchema RTy) : Bool :=
  RTy.hasSelfA2 fs && selfIdxsOk 1 (RTy.selfIdxsA2 fs) && famAllInhabited [.record fs]

/-- A recursive newtype mentions itself — otherwise the wrapper is erased into its field
    and there is no `recAlias` at all — and does so guardedly, so that the equation it
    stands for has a solution: `recAlias (.self 0)` is `T = T`, which no value
    satisfies, while `recAlias (.array (.self 0))` is the empty array and more. -/
def recAliasWf (b : RTy) : Bool :=
  RTy.hasSelf b && selfIdxsOk 1 (RTy.selfIdxs b) && famAllInhabited [.alias b]

/-- A family mentions only members it has, is a family rather than a `mutual` block of
    unrelated declarations — each member reaches every member — and every member of it
    has values. -/
def famWf (f : LeanMutualRecFamily RTy) : Bool :=
  f.members.all (fun m => selfIdxsOk f.members.length (FamMember.selfIdxs m))
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
  | .self _ => true
  | .prim _ => true
  | .fn a b => !RTy.hasSelf a && RTy.wf a && RTy.wf b
  | .primCovariant s => RTy.wfCov s
  | .enum _ => true
  | .record fs => RTy.wfA2 fs
  | .taggedUnion l => RTy.wfTU l
  | .recTaggedUnion l => recTUWf l && RTy.wfTU l
  | .recObject fs => recObjWf fs && RTy.wfA2 fs
  | .recAlias b => recAliasWf b && RTy.wf b
  | .mutualRecursiveFamily f => famWf f && FamMember.wfFamily f

/-- `RTy.wf`, on an invariant type former. -/
def RTy.wfCov : LeanPrimTyCovariant RTy → Bool
  | .array a | .list a | .task a | .promise a | .thunk a | .lazy a => RTy.wf a

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
def FamMember.wf : FamMember → Bool
  | .ctors l => RTy.wfTU l
  | .record fs => RTy.wfA2 fs
  | .alias b => RTy.wf b

/-- `RTy.wf`, on the members of a family. -/
def FamMember.wfList : List FamMember → Bool
  | [] => true
  | m :: ms => FamMember.wf m && FamMember.wfList ms

/-- `RTy.wf`, on every member of a family. -/
def FamMember.wfFamily : LeanMutualRecFamily RTy → Bool
  | .selectedThenMore before current next after =>
      FamMember.wfList before && FamMember.wf current && FamMember.wf next
        && FamMember.wfList after
  | .selectedLast first before current =>
      FamMember.wf first && FamMember.wfList before && FamMember.wf current

end

/-! ## The degenerate recursive declarations, refuted

These are the declarations Lean accepts and no compiled program can hold a value of.
They are `RTy`s — nothing about their *shape* is wrong — and the predicates above refuse
them, so there is no `Ty` for them: the corresponding constructor of `LeanScript.Ty` cannot
be applied. -/

/-- `inductive Bad | mk : Bad → Bad` is read as the recursive newtype whose body is the
    declaration itself, i.e. as the equation `T = T`.  No value satisfies it. -/
theorem not_recAliasWf_selfLoop : recAliasWf (.self 0) = false := by decide

/-- `structure Worse where w : Worse; n : Nat` is the same mistake one shape along: a
    record needs *all* of its fields, and one of them is the record itself. -/
theorem not_recObjWf_selfField : recObjWf ⟨.self 0, .prim .nat, []⟩ = false := by decide

/-- A recursive newtype that does *not* mention itself is not one either: its wrapper is
    erased into its field, and the type it describes is just that field. -/
theorem not_recAliasWf_noSelf : recAliasWf (.prim .nat) = false := by decide

/-- A guarded recursive newtype — `structure Rose where kids : Array Rose` — *is* well
    formed: the empty array holds no `Rose`, so a `Rose` can be built. -/
theorem recAliasWf_array : recAliasWf (.array (.self 0)) = true := by decide

/-- And so is a recursive sum with a base case: `inductive T | leaf | node : T → T → T`. -/
theorem recTUWf_tree : recTUWf (.skip (.here ⟨.self 0, [.self 0]⟩ [])) = true := by decide

/-! ## Strict positivity, refuted and permitted

A recursive declaration whose own type occurs to the **left** of an arrow is the one
shape that makes the term language diverge with no loop in it at all: at
`μX. { f : X → Nat, pad : Nat }` the λ-calculus core writes Curry's `Ω`.  `RTy.wf`
refuses it, so there is no such `Ty`. -/

/-- The negative recursive record `μX. { f : X → Nat, pad : Nat }` — the shape Curry's
    `Ω` is written at — is **not** well formed: `.self` stands in the domain of an
    arrow. -/
theorem not_wf_negRecObject :
    RTy.wf (.recObject ⟨.fn (.self 0) (.prim .nat), .prim .nat, []⟩) = false := by decide

/-- The same shape one level in: a negative occurrence buried under a list is refused
    too, since `RTy.hasSelf` looks through the covariant type formers. -/
theorem not_wf_negRecObject_nested :
    RTy.wf (.recObject ⟨.fn (.list (.self 0)) (.prim .nat), .prim .nat, []⟩) = false := by
  decide

/-- A **positive** occurrence is untouched: `inductive T | leaf | node : (Nat → T) → T` —
    an infinitely branching tree — has `.self` to the *right* of an arrow, and is well
    formed. -/
theorem wf_posRecTU :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.fn (.prim .nat) (.self 0), []⟩ []))) = true := by
  decide

/-- The negative counterpart of the same declaration,
    `inductive Bad | leaf | node : (Bad → Nat) → Bad`, is refused. -/
theorem not_wf_negRecTU :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.fn (.self 0) (.prim .nat), []⟩ []))) = false := by
  decide

/-- And so is the shape every Lean inductive type has: no arrow over `.self` at all. -/
theorem wf_recTU_tree :
    RTy.wf (.recTaggedUnion (.skip (.here ⟨.self 0, [.self 0]⟩ []))) = true := by decide

end LeanScript

end
