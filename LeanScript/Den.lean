module

public import LeanScript.Ty

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# `Ty.den`: the Lean type a `Ty` describes

The evaluator of `LeanScript.Eval` answers in `τ.den`, so every `Ty` needs a Lean type —
**every** one of them, including the four recursive shapes, and without an escape hatch:
there is no `Option`, no error monad and no default value anywhere below.

The five decisions this file makes:

* **a computed field is derived, not stored.**  `Ty.withComputedFields b cs` denotes
  `b.den`: what a declaration caches is a function of the value (`Lean.Name.hash`), so it
  adds no value and could not be given one independently — storing it here would make a
  `Name` with the wrong `hash` writable.  The cache decides the runtime object, and so
  the JavaScript that is printed, which is why the type language records it at all.

* **the covariant wrappers are the identity.**  `Ty.thunk` and `Ty.lazy` both denote
  their argument (`Ty.task` and `Ty.promise` are commented out of
  `LeanPrimTyCovariant` for now).  A `Thunk` is a value whose computation has not been
  shared, and a delayed
  value of a *pure* language is the value it delays: at this layer they carry no
  information beyond the value, and the distinction between them is a fact about the
  JavaScript that is printed later, not about what is computed.  This is what the
  header of `LeanScript.Expr` means by "`Ty.lazy` is a delay, not a `Thunk`".

* **an enum is a `Fin`.**  A `Ty.enum` with `n` constructors denotes `Fin n`: the
  constructor *number*, which is exactly what the runtime holds.  The `shift` the schema
  carries is how the number prints, not what it is.

* **a record is a tuple and a tagged union is a tagged tuple.**  `Tup` and `TSum` below
  are the positional shapes the `Ty` header describes (`{ tag: 0, _1: …, _2: … }`), with
  the tag a `Fin` into the list of constructors, so a value cannot carry a tag the type
  has no constructor for and cannot carry the wrong number of fields.

* **a recursive declaration is a fixed point, taken once and for all.**  `Mu` below is
  *the* least fixed point of the descriptions of `FDesc`: an ordinary Lean inductive
  family, so a value of a recursive `Ty` is a finite tree and recursion over one
  terminates because Lean's own recursion over `Mu` does.  There is no coinductive
  shape, no `partial` and no `unsafe` in sight.

* **nothing is `Option`-valued.**  `Tup`, `TSum` and `MuArgs` are indexed by the list of
  the types of their components, so reading a field is a projection rather than a lookup
  that might fail.

## What `FDesc` is for

A recursive declaration is a *binder*: its payloads are `RTy`s, and `RTy.self` (or `RTy.familyMember i`) is an
occurrence of member `i`.  A Lean inductive type cannot be built by recursion on a value
at the moment it is needed, so the fixed point is taken once, over a description language
(`FDesc`) that mirrors `RTy` minus the things a description cannot carry:

* a **function field** records its domain as a description too, and the domain of a
  function inside a recursive declaration mentions no member of it (that is what
  `RTy.wf` enforces — strict positivity), so the domain is interpreted by `SDen`, which
  is defined before the fixed point is taken.  `SDen` sends the two shapes that *would*
  need the fixed point — an occurrence of a member, and a nested recursive declaration —
  to `Empty`; those are exactly the domains a well-formed declaration does not have, save
  for a nested declaration in a domain, which is the one shape this file does not model.

* a **nested recursive declaration** is a scope of its own, so it is a description with
  an environment of its own (`FDesc.muD`), and `Mu` takes that environment as an *index*
  rather than as a parameter so that one may sit inside another.
-/

/-! ## Tuples and tagged tuples -/

/-- The product of a list of types, right-nested, with the empty product a unit. -/
def Tup : List Type → Type
  | [] => PUnit
  | a :: as => a × Tup as

/-- A tagged tuple: which constructor, and that constructor's fields.  The tag is a `Fin`
    into the list of constructors, so it is a constructor the type has. -/
def TSum (cs : List (List Type)) : Type := Σ t : Fin cs.length, Tup cs[t]

/-- The `i`-th component of a tuple. -/
def Tup.get : ∀ {as : List Type}, Tup as → (i : Fin as.length) → as[i]
  | _ :: _, (a, _), ⟨0, _⟩ => a
  | _ :: _, (_, r), ⟨i + 1, h⟩ => Tup.get r ⟨i, by simpa using h⟩

/-- Append two tuples. -/
def Tup.append : ∀ {as bs : List Type}, Tup as → Tup bs → Tup (as ++ bs)
  | [], _, _, y => y
  | _ :: _, _, (a, x), y => (a, Tup.append x y)

/-- The first `as.length` components of a tuple of `as ++ bs`. -/
def Tup.take : ∀ {as bs : List Type}, Tup (as ++ bs) → Tup as
  | [], _, _ => PUnit.unit
  | _ :: _, _, (a, x) => (a, Tup.take x)

/-- Everything after the first `as.length` components of a tuple of `as ++ bs`. -/
def Tup.drop : ∀ {as bs : List Type}, Tup (as ++ bs) → Tup bs
  | [], _, x => x
  | _ :: _, _, (_, x) => Tup.drop x

/-! ## `FDesc`: the shapes a payload of a recursive declaration can have -/

/-- A description of the payload of a recursive declaration: `RTy`, with every leaf that
    is a Lean type replaced by the description of that type, so that a description
    carries no `Type` and the fixed point below stays in `Type`. -/
inductive FDesc where
  /-- A terminal type. -/
  | primD : LeanPrimTy → FDesc
  /-- An enum with this many constructors. -/
  | enumD : Nat → FDesc
  /-- An occurrence of member `i` of the declaration this payload belongs to. -/
  | selfD : Nat → FDesc
  /-- An array of a payload. -/
  | arrD : FDesc → FDesc
  /-- A function.  Its domain mentions no member of the declaration, which is what makes
      the fixed point below strictly positive. -/
  | funD : FDesc → FDesc → FDesc
  /-- A record: the descriptions of its fields, in order. -/
  | tupD : List FDesc → FDesc
  /-- A non-recursive sum: one entry per constructor, each the description of that
      constructor's fields. -/
  | sumD : List (List FDesc) → FDesc
  /-- A *nested* recursive declaration, with a scope — and so an environment — of its
      own, and which of its members this payload is. -/
  | muD : List (List (List FDesc)) → Nat → FDesc

/-- The environment of a recursive declaration: one entry per member, each one entry per
    constructor, each the descriptions of that constructor's fields. -/
abbrev FEnv := List (List (List FDesc))

/-- The constructors of member `i`; the empty list when there is no such member, which
    makes that member an empty type. -/
def FEnv.ctors (E : FEnv) (i : Nat) : List (List FDesc) := E.getD i []

/-- The fields of constructor `t` of member `i`; the empty list when there is no such
    constructor, which no value of `Mu` can name. -/
def FEnv.flds (E : FEnv) (i t : Nat) : List FDesc := (E.ctors i).getD t []

namespace FDesc

/-! ### The domain of a function field

A function inside a recursive declaration has a domain that mentions no member of it, so
its domain can be interpreted *before* the fixed point is taken.  The two shapes that
would need the fixed point are sent to `Empty`. -/

mutual

/-- The Lean type a description that mentions no member of its declaration describes. -/
def SDen : FDesc → Type
  | .primD p => p.denote
  | .enumD n => Fin n
  | .selfD _ => Empty
  | .arrD d => Array (SDen d)
  | .funD a b => SDen a → SDen b
  | .tupD ds => Tup (SDenList ds)
  | .sumD cs => TSum (SDenCtors cs)
  | .muD _ _ => Empty

/-- `SDen`, on a list of descriptions. -/
def SDenList : List FDesc → List Type
  | [] => []
  | d :: ds => SDen d :: SDenList ds

/-- `SDen`, on the constructors of a sum. -/
def SDenCtors : List (List FDesc) → List (List Type)
  | [] => []
  | ds :: cs => SDenList ds :: SDenCtors cs

end

end FDesc

/-! ## `Mu`: the fixed point -/

mutual

/-- A value of member `i` of the recursive declaration described by `E`: which
    constructor, and its fields.  The environment is an **index**, not a parameter, so
    that a nested declaration — which has a scope, and so an environment, of its own —
    can be a field of an outer one. -/
inductive Mu : FEnv → Nat → Type where
  /-- Constructor `t` of member `i` — a number **with the proof that the member has
      it**, as `Term.taggedUnion_mk` carries one — with its fields. -/
  | mk : ∀ {E : FEnv} {i : Nat} (t : Nat), t < (E.ctors i).length →
      MuArgs E (E.flds i t) → Mu E i

/-- The fields of one constructor, typed by their descriptions. -/
inductive MuArgs : FEnv → List FDesc → Type where
  /-- No more fields. -/
  | nil : ∀ {E : FEnv}, MuArgs E []
  /-- One more field. -/
  | cons : ∀ {E : FEnv} {d : FDesc} {ds : List FDesc},
      MuArg E d → MuArgs E ds → MuArgs E (d :: ds)

/-- One field of a constructor of a recursive declaration. -/
inductive MuArg : FEnv → FDesc → Type where
  /-- A terminal value. -/
  | primA : ∀ {E : FEnv} {p : LeanPrimTy}, p.denote → MuArg E (.primD p)
  /-- A constructor number of an enum. -/
  | enumA : ∀ {E : FEnv} {n : Nat}, Fin n → MuArg E (.enumD n)
  /-- An occurrence of member `j` of this declaration: the recursion. -/
  | selfA : ∀ {E : FEnv} {j : Nat}, Mu E j → MuArg E (.selfD j)
  /-- An array of fields.  It is a `MuVec` rather than an `Array` because a nested
      inductive occurrence may not mention a locally bound index. -/
  | arrA : ∀ {E : FEnv} {d : FDesc}, MuVec E d → MuArg E (.arrD d)
  /-- A function into a field. -/
  | funA : ∀ {E : FEnv} {a b : FDesc}, (FDesc.SDen a → MuArg E b) → MuArg E (.funD a b)
  /-- A record of fields. -/
  | tupA : ∀ {E : FEnv} {ds : List FDesc}, MuArgs E ds → MuArg E (.tupD ds)
  /-- A tagged value of a non-recursive sum whose fields may mention this declaration. -/
  | sumA : ∀ {E : FEnv} {cs : List (List FDesc)} (t : Nat),
      MuArgs E (cs.getD t []) → MuArg E (.sumD cs)
  /-- A value of a *nested* recursive declaration. -/
  | muA : ∀ {E E' : FEnv} {j : Nat}, Mu E' j → MuArg E (.muD E' j)

/-- A homogeneous list of fields: what an array field of a recursive declaration holds. -/
inductive MuVec : FEnv → FDesc → Type where
  /-- The empty array. -/
  | nil : ∀ {E : FEnv} {d : FDesc}, MuVec E d
  /-- One more element. -/
  | cons : ∀ {E : FEnv} {d : FDesc}, MuArg E d → MuVec E d → MuVec E d

end

/-! ## The size of a value of a recursive type

A recursion of the object language descends in `<` on a `Nat` (`Term.fixAcc`), so a
recursion over a value of a recursive type needs a `Nat` to descend at.  `Mu.size` is
that number: one per constructor node, so every field of a node is strictly smaller than
the node itself, which is exactly what a structural recursion of Lean descends at. -/

mutual

/-- How many constructor nodes a value of a recursive type has. -/
def Mu.size : ∀ {E : FEnv} {i : Nat}, Mu E i → Nat
  | _, _, .mk _ _ args => MuArgs.size args + 1

/-- `Mu.size`, summed over the fields of a constructor. -/
def MuArgs.size : ∀ {E : FEnv} {ds : List FDesc}, MuArgs E ds → Nat
  | _, _, .nil => 0
  | _, _, .cons a r => MuArg.size a + MuArgs.size r

/-- `Mu.size`, on one field. -/
def MuArg.size : ∀ {E : FEnv} {d : FDesc}, MuArg E d → Nat
  | _, _, .primA _ => 0
  | _, _, .enumA _ => 0
  | _, _, .selfA m => Mu.size m
  | _, _, .arrA v => MuVec.size v
  | _, _, .funA _ => 0
  | _, _, .tupA a => MuArgs.size a
  | _, _, .sumA _ a => MuArgs.size a
  | _, _, .muA m => Mu.size m

/-- `Mu.size`, summed over the elements of an array field. -/
def MuVec.size : ∀ {E : FEnv} {d : FDesc}, MuVec E d → Nat
  | _, _, .nil => 0
  | _, _, .cons a r => MuArg.size a + MuVec.size r

end

/-! ## A payload, as a description -/

namespace RTy

mutual

/-- The description of a payload of a recursive declaration. -/
def fdesc : RTy → FDesc
  | .self => .selfD 0
  | .familyMember i => .selfD i
  | .prim p => .primD p
  | .fn a b => .funD (fdesc a) (fdesc b)
  | .primCovariant s => fdescCov s
  | .enum s => .enumD s.nOfConstructors
  | .record fs => .tupD (fdescA2 fs)
  | .taggedUnion l => .sumD (fdescTU l)
  | .recTaggedUnion l => .muD [fdescTU l] 0
  | .recObject fs => .muD [[fdescA2 fs]] 0
  | .recAlias b => .muD [[[fdesc b]]] 0
  | .mutualRecursiveFamily f => .muD (fdescFamily f) f.memberIdx
  -- a cached value is a function of the value, so it is not part of the description:
  -- what it decides is the object the runtime holds, not which values there are
  | .withComputedFields b _ => fdesc b

/-- `RTy.fdesc`, on an invariant type former: the delayed wrappers are the identity. -/
def fdescCov : LeanPrimTyCovariant RTy → FDesc
  | .array a => .arrD (fdesc a)
  -- | .task a => fdesc a
  -- | .promise a => fdesc a
  | .thunk a => fdesc a
  | .lazy a => fdesc a

/-- `RTy.fdesc`, on a list of payloads. -/
def fdescList : List RTy → List FDesc
  | [] => []
  | a :: as => fdesc a :: fdescList as

/-- `RTy.fdesc`, on the constructors of a layout. -/
def fdescCtors : List (List RTy) → List (List FDesc)
  | [] => []
  | fs :: l => fdescList fs :: fdescCtors l

/-- `RTy.fdesc`, on the fields of a record. -/
def fdescA2 : LeanRecordSchema RTy → List FDesc
  | ⟨a, b, rest⟩ => fdesc a :: fdesc b :: fdescList rest

/-- `RTy.fdesc`, on the fields of a constructor that has at least one. -/
def fdescNE : NonEmptyList RTy → List FDesc
  | ⟨a, as⟩ => fdesc a :: fdescList as

/-- `RTy.fdesc`, on the constructors of a tagged union. -/
def fdescTU : LeanTaggedUnionSchema RTy → List (List FDesc)
  | .payloadFirst f n r => fdescNE f :: fdescList n :: fdescCtors r
  | .skip rest => [] :: fdescCP rest

/-- `RTy.fdesc`, on the constructors that follow a field-less one. -/
def fdescCP : CtorsWithPayload RTy → List (List FDesc)
  | .here f r => fdescNE f :: fdescCtors r
  | .skip rest => [] :: fdescCP rest

/-- `RTy.fdesc`, on one member of a mutual family. -/
def fdescFam : LeanFamMemberSchema RTy → List (List FDesc)
  | .ctors l => fdescTU l
  | .record fs => [fdescA2 fs]
  | .alias b => [[fdesc b]]

/-- `RTy.fdesc`, on the members of a mutual family. -/
def fdescFamList : List (LeanFamMemberSchema RTy) → FEnv
  | [] => []
  | m :: ms => fdescFam m :: fdescFamList ms

/-- `RTy.fdesc`, on a whole mutual family: its members, in declaration order. -/
def fdescFamily : LeanMutualRecFamily RTy → FEnv
  | .selectedThenMore before current next after =>
      fdescFamList before ++ fdescFam current :: fdescFam next :: fdescFamList after
  | .selectedLast first before current =>
      fdescFam first :: (fdescFamList before ++ [fdescFam current])

end

end RTy

/-! ## `Ty.den` -/

namespace Ty

mutual

/-- The Lean type a closed type describes. -/
def den : Ty → Type
  | .prim p => p.denote
  | .fn a b => den a → den b
  | .primCovariant s => denCov s
  | .enum s => Fin s.nOfConstructors
  | .record fs => Tup (denA2 fs)
  | .taggedUnion l => TSum (denTU l)
  | .recTaggedUnion l => Mu [RTy.fdescTU l.schema] 0
  | .recObject fs => Mu [[RTy.fdescA2 fs.fields]] 0
  | .recAlias b => Mu [[[RTy.fdesc b.body]]] 0
  | .mutualRecursiveFamily f => Mu (RTy.fdescFamily f.family) f.family.memberIdx
  -- a cached value is a function of the value, so it carries no information: `Lean.Name`
  -- and the same declaration without its `hash` have exactly the same values here, and
  -- the cache is a fact about the JavaScript object that is printed later
  | .withComputedFields b _ => den b

/-- `Ty.den`, on an invariant type former: an array is an `Array`, and the delayed
    wrappers are the identity. -/
def denCov : LeanPrimTyCovariant Ty → Type
  | .array a => Array (den a)
  -- | .task a => den a
  -- | .promise a => den a
  | .thunk a => den a
  | .lazy a => den a

/-- `Ty.den`, on a list of types. -/
def denList : List Ty → List Type
  | [] => []
  | a :: as => den a :: denList as

/-- `Ty.den`, on the constructors of a layout. -/
def denCtors : List (List Ty) → List (List Type)
  | [] => []
  | fs :: l => denList fs :: denCtors l

/-- `Ty.den`, on the fields of a record. -/
def denA2 : LeanRecordSchema Ty → List Type
  | ⟨a, b, rest⟩ => den a :: den b :: denList rest

/-- `Ty.den`, on the fields of a constructor that has at least one. -/
def denNE : NonEmptyList Ty → List Type
  | ⟨a, as⟩ => den a :: denList as

/-- `Ty.den`, on the constructors of a tagged union. -/
def denTU : LeanTaggedUnionSchema Ty → List (List Type)
  | .payloadFirst f n r => denNE f :: denList n :: denCtors r
  | .skip rest => [] :: denCP rest

/-- `Ty.den`, on the constructors that follow a field-less one. -/
def denCP : CtorsWithPayload Ty → List (List Type)
  | .here f r => denNE f :: denCtors r
  | .skip rest => [] :: denCP rest

end

@[simp] theorem denList_length (as : List Ty) : (denList as).length = as.length := by
  induction as with
  | nil => rfl
  | cons _ _ ih => simp [denList, ih]

@[simp] theorem denCtors_length (l : List (List Ty)) : (denCtors l).length = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [denCtors, ih]

@[simp] theorem denList_append (as bs : List Ty) :
    denList (as ++ bs) = denList as ++ denList bs := by
  induction as with
  | nil => rfl
  | cons _ _ ih => simp [denList, ih]

theorem denList_getElem (as : List Ty) (i : Nat) (h : i < as.length) :
    (denList as)[i]'(by simpa using h) = den as[i] := by
  induction as generalizing i with
  | nil => simp at h
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using h)

theorem denCtors_getElem (cs : List (List Ty)) (i : Nat) (h : i < cs.length) :
    (denCtors cs)[i]'(by simpa using h) = denList cs[i] := by
  induction cs generalizing i with
  | nil => simp at h
  | cons c cs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using h)

/-! ### The constructors of a layout, and the tuple its values are

`den` is a structural recursion, so the constructors of a tagged union are walked in the
shape the schema has (`denTU`, `denCP`) rather than by mapping over `toList`.  The two
agree, which is what these lemmas say, and `tsumMk` / `tsumTag` / `tsumFlds` below are
the only places that have to know it. -/

theorem denCP_eq : ∀ (c : CtorsWithPayload Ty), denCP c = denCtors c.toList
  | .here f r => by
      cases f
      simp only [denCP, CtorsWithPayload.toList, denCtors, denNE, denList,
        NonEmptyList.toList]
  | .skip rest => by
      simp only [denCP, CtorsWithPayload.toList, denCtors, denList, denCP_eq rest]

theorem denTU_eq : ∀ (l : LeanTaggedUnionSchema Ty), denTU l = denCtors l.toList
  | .payloadFirst f _ _ => by
      cases f
      simp only [denTU, LeanTaggedUnionSchema.toList, denCtors, denNE, denList,
        NonEmptyList.toList]
  | .skip rest => by
      simp only [denTU, LeanTaggedUnionSchema.toList, denCtors, denList, denCP_eq rest]

/-- The values of a tagged union, seen as a tag into `toList` and the fields at it. -/
theorem tuView (l : LeanTaggedUnionSchema Ty) :
    (Ty.taggedUnion l).den = TSum (denCtors l.toList) := by
  show TSum (denTU l) = _
  rw [denTU_eq]

/-- A tagged value: constructor `t` of the union, with its fields. -/
def tsumMk (l : LeanTaggedUnionSchema Ty) (t : Nat) (ht : t < l.toList.length)
    (flds : Tup (denList (l.toList[t]'ht))) : (Ty.taggedUnion l).den :=
  cast (tuView l).symm
    ⟨⟨t, by simpa using ht⟩,
      cast (congrArg Tup (denCtors_getElem l.toList t ht)).symm flds⟩

/-- Which constructor a tagged value was built with. -/
def tsumTag {l : LeanTaggedUnionSchema Ty} (v : (Ty.taggedUnion l).den) : Nat :=
  (cast (tuView l) v).1.1

theorem tsumTag_lt {l : LeanTaggedUnionSchema Ty} (v : (Ty.taggedUnion l).den) :
    tsumTag v < l.toList.length := by
  have := (cast (tuView l) v).1.2
  simpa [tsumTag] using this

/-- The fields a tagged value carries. -/
def tsumFlds {l : LeanTaggedUnionSchema Ty} (v : (Ty.taggedUnion l).den) :
    Tup (denList (l.toList[tsumTag v]'(tsumTag_lt v))) :=
  cast (congrArg Tup (denCtors_getElem l.toList (tsumTag v) (tsumTag_lt v)))
    (cast (tuView l) v).2

/-- The values of a record are a tuple of its fields, in order. -/
theorem recView (fs : LeanRecordSchema Ty) :
    (Ty.record fs).den = Tup (denList fs.toList) := by
  cases fs
  show Tup (denA2 _) = _
  simp only [denA2, LeanRecordSchema.toList, denList]

/-- A record value, from its fields. -/
def recMk (fs : LeanRecordSchema Ty) (flds : Tup (denList fs.toList)) :
    (Ty.record fs).den := cast (recView fs).symm flds

/-- The fields of a record value. -/
def recFlds {fs : LeanRecordSchema Ty} (v : (Ty.record fs).den) :
    Tup (denList fs.toList) := cast (recView fs) v

/-- The curried function a function of the argument tuple is: this is what a recursion,
    which takes its arguments all at once, is as a value of `Ty.arrows ps τ`. -/
def curryFn : ∀ {ps : List Ty} {τ : Ty}, (Tup (denList ps) → τ.den) → (Ty.arrows ps τ).den
  | [], _, f => f PUnit.unit
  | _ :: _, _, f => fun v => curryFn (fun as => f (v, as))

/-! ### A list of a terminal type, and the value of `Ty.list` it is

`Ty.list α` is a recursive tagged union, so its values are values of `Mu` rather than
Lean lists: `nil` is constructor `0`, which carries nothing, and `cons` is constructor
`1`, which carries the head and — as an occurrence of the declaration — the tail.  These
two functions are that correspondence, for an element type that is terminal, which is
what lets a primitive written at `List String` be applied to a value of `Ty.list
(.prim .string)`. -/

/-- The descriptions of `Ty.list (.prim p)`: `nil`, with no field, and `cons`, with a
    terminal head and a tail that is an occurrence of the declaration. -/
abbrev listEnv (p : LeanPrimTy) : FEnv := [[[], [FDesc.primD p, FDesc.selfD 0]]]

/-- A Lean list, as the value of the recursive declaration `Ty.list (.prim p)`. -/
def muOfList {p : LeanPrimTy} : List p.denote → Mu (listEnv p) 0
  | [] => .mk 0 (show (0 : Nat) < 2 by decide) .nil
  | x :: xs => .mk 1 (show (1 : Nat) < 2 by decide)
      (.cons (.primA x) (.cons (.selfA (muOfList xs)) .nil))

/-- The value of the recursive declaration `Ty.list (.prim p)`, as a Lean list.  There
    are two constructors and no third, which is why the last branch is impossible. -/
def muToList {p : LeanPrimTy} : Mu (listEnv p) 0 → List p.denote
  | .mk 0 _ _ => []
  | .mk 1 _ (.cons (.primA x) (.cons (.selfA t) .nil)) => x :: muToList t
  | .mk (n + 2) h _ => absurd (show n + 2 < 2 from h) (by omega)
  termination_by v => v.size
  decreasing_by simp [Mu.size, MuArgs.size, MuArg.size]

/-- The two are inverse: reading a list back out of the value built from it answers
    with the list itself. -/
theorem muToList_muOfList {p : LeanPrimTy} (xs : List p.denote) :
    muToList (muOfList xs) = xs := by
  induction xs with
  | nil => rw [muOfList, muToList.eq_def]
  | cons x xs ih => rw [muOfList, muToList.eq_def]; exact congrArg (x :: ·) ih

/-- A Lean list of a terminal type, as a value of `Ty.list`. -/
def listOfList {p : LeanPrimTy} (xs : List p.denote) : (Ty.list (.prim p)).den :=
  muOfList xs

/-- A value of `Ty.list` of a terminal type, as a Lean list. -/
def listToList {p : LeanPrimTy} (v : (Ty.list (.prim p)).den) : List p.denote :=
  muToList v

end Ty

/-! ## Runtime environments

The evaluator carries one value per variable in scope, and `Term.fixAcc` mentions the
argument tuple of a recursion in its *type*, so environments are defined here, next to
the denotation they are made of, rather than in the evaluator. -/

/-- The values of the variables of a context, innermost first. -/
abbrev Env (Γ : List Ty) : Type := Tup (Ty.denList Γ)

/-- The empty environment. -/
abbrev Env.nil : Env [] := PUnit.unit

/-- One more value in scope. -/
abbrev Env.cons {τ : Ty} {Γ : List Ty} (v : τ.den) (γ : Env Γ) : Env (τ :: Γ) := (v, γ)

end LeanScript

end
