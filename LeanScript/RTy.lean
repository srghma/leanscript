module

public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
public import LeanScript.Schema

@[expose] public section

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# `RTy`: the type language *inside* a recursive declaration

`RTy` is everything a closed type (`LeanScript.Ty`) can be, and in addition an occurrence of
the declaration being defined (`RTy.self i`).  It is defined **before** `Ty` and does not
mention it, which is what makes the design of `LeanScript.Ty` possible: the conditions that
say a recursive shape describes a type that exists — it mentions itself, its `.self`s
point at members it has, and it has values at all — are decidable predicates on `RTy`
(`LeanScript.RTyWf`), so the recursive constructors of `Ty` can *take the proof as an
argument*.  A `Ty` is therefore well formed by construction, and there is no separate
subtype of the well-formed types.

An `RTy` on its own carries no such guarantee: it is the raw payload language.  Nothing
is compiled from an `RTy` — it only ever appears inside a `Ty`, which does carry the
proof.
-/

/-- A type **inside a recursive declaration**: everything a closed type can be, and in
    addition an occurrence of the declaration being defined.  This is the one layer
    where `.self` is available, which is what keeps a recursive type a *finite* tree. -/
inductive RTy where
  /-- An occurrence of the declaration whose body this type sits in — member `i` of it
      if that declaration is a mutual family, and `.self 0` otherwise. -/
  | self : Nat → RTy
  /-- A terminal type. -/
  | prim : LeanPrimTy → RTy
  /-- A curried function type, `σ ⇒ τ`, over types that may mention `.self`. -/
  | fn : RTy → RTy → RTy
  /-- An array, list, task, promise, thunk or lazy value of a type that may mention
      `.self`. -/
  | primCovariant : LeanPrimTyCovariant RTy → RTy
  /-- A non-recursive enum. -/
  | enum : LeanEnumSchema → RTy
  /-- A single-constructor record, whose fields may mention `.self`. -/
  | record : LeanRecordSchema RTy → RTy
  /-- A non-recursive sum type with fields. -/
  | taggedUnion : LeanTaggedUnionSchema RTy → RTy
  /-- A *nested* recursive sum type: it opens a new scope, so the `.self` of its own
      children is this inner declaration, not the enclosing one. -/
  | recTaggedUnion : LeanTaggedUnionSchema RTy → RTy
  /-- A nested recursive record; it opens a new scope, as `recTaggedUnion` does. -/
  | recObject : LeanRecordSchema RTy → RTy
  /-- A nested recursive newtype; it opens a new scope, as `recTaggedUnion` does. -/
  | recAlias : RTy → RTy
  /-- A nested mutual recursive family; it opens a new scope, as `recTaggedUnion`
      does. -/
  | mutualRecursiveFamily : LeanMutualRecFamily RTy → RTy

-- /-- One member of a mutual recursive family: a member with constructors, a
--     single-constructor member with fields, or a newtype member. -/
-- abbrev LeanFamMemberSchema_RTy := LeanFamMemberSchema RTy

/-! ## Deciding equality

`RTy` holds schemas of types, and schemas of schemas of types, which no `deriving`
handler covers, so the instance is written out: a structural `RTy.beq` over the whole
family, and the two lemmas that make it equality. -/

mutual

/-- Structural equality of two types inside a recursive declaration. -/
def RTy.beq : RTy → RTy → Bool
  | .self i, .self j => i == j
  | .prim p, .prim q => p == q
  | .fn a b, .fn c d => RTy.beq a c && RTy.beq b d
  | .primCovariant s, .primCovariant t => RTy.beqCov s t
  | .enum a, .enum b => a == b
  | .record a, .record b => RTy.beqA2 a b
  | .taggedUnion a, .taggedUnion b => RTy.beqTU a b
  | .recTaggedUnion a, .recTaggedUnion b => RTy.beqTU a b
  | .recObject a, .recObject b => RTy.beqA2 a b
  | .recAlias a, .recAlias b => RTy.beq a b
  | .mutualRecursiveFamily a, .mutualRecursiveFamily b => RTy.beqFamily a b
  | _, _ => false

/-- `RTy.beq`, on an invariant type former. -/
def RTy.beqCov : LeanPrimTyCovariant RTy → LeanPrimTyCovariant RTy → Bool
  | .array a, .array b => RTy.beq a b
  | .task a, .task b => RTy.beq a b
  | .promise a, .promise b => RTy.beq a b
  | .thunk a, .thunk b => RTy.beq a b
  | .lazy a, .lazy b => RTy.beq a b
  | _, _ => false

/-- `RTy.beq`, on a list of types. -/
def RTy.beqList : List RTy → List RTy → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beq a b && RTy.beqList as bs
  | _, _ => false

/-- `RTy.beq`, on the constructors of a layout. -/
def RTy.beqCtors : List (List RTy) → List (List RTy) → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beqList a b && RTy.beqCtors as bs
  | _, _ => false

/-- `RTy.beq`, on the fields of a record. -/
def RTy.beqA2 : LeanRecordSchema RTy → LeanRecordSchema RTy → Bool
  | ⟨a1, a2, as⟩, ⟨b1, b2, bs⟩ => RTy.beq a1 b1 && RTy.beq a2 b2 && RTy.beqList as bs

/-- `RTy.beq`, on the fields of a constructor that has at least one. -/
def RTy.beqNE : NonEmptyList RTy → NonEmptyList RTy → Bool
  | ⟨a, as⟩, ⟨b, bs⟩ => RTy.beq a b && RTy.beqList as bs

/-- `RTy.beq`, on the constructors of a tagged union. -/
def RTy.beqTU : LeanTaggedUnionSchema RTy → LeanTaggedUnionSchema RTy → Bool
  | .payloadFirst f n r, .payloadFirst g m s =>
      RTy.beqNE f g && RTy.beqList n m && RTy.beqCtors r s
  | .skip a, .skip b => RTy.beqCP a b
  | _, _ => false

/-- `RTy.beq`, on the constructors that follow a field-less one. -/
def RTy.beqCP : CtorsWithPayload RTy → CtorsWithPayload RTy → Bool
  | .here f r, .here g s => RTy.beqNE f g && RTy.beqCtors r s
  | .skip a, .skip b => RTy.beqCP a b
  | _, _ => false


/-- Structural equality of two members of a mutual family. -/
def RTy.beqFam : LeanFamMemberSchema RTy → LeanFamMemberSchema RTy → Bool
  | .ctors a, .ctors b => RTy.beqTU a b
  | .record a, .record b => RTy.beqA2 a b
  | .alias a, .alias b => RTy.beq a b
  | _, _ => false

/-- `RTy.beqFam`, on a list of members. -/
def RTy.beqFamList : List (LeanFamMemberSchema RTy) → List (LeanFamMemberSchema RTy) → Bool
  | [], [] => true
  | a :: as, b :: bs => RTy.beqFam a b && RTy.beqFamList as bs
  | _, _ => false

/-- Structural equality of two mutual families, the selected member included. -/
def RTy.beqFamily : LeanMutualRecFamily RTy → LeanMutualRecFamily RTy → Bool
  | .selectedThenMore b c n a, .selectedThenMore b' c' n' a' =>
      RTy.beqFamList b b' && RTy.beqFam c c' && RTy.beqFam n n' && RTy.beqFamList a a'
  | .selectedLast f b c, .selectedLast f' b' c' =>
      RTy.beqFam f f' && RTy.beqFamList b b' && RTy.beqFam c c'
  | _, _ => false

end



mutual

/-- Types inside a recursive declaration that compare equal are equal. -/
theorem RTy.eq_of_beq : ∀ {a b : RTy}, RTy.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beq]
  case fn.fn => exact ⟨RTy.eq_of_beq h.1, RTy.eq_of_beq h.2⟩
  case primCovariant.primCovariant => exact RTy.eq_of_beqCov h
  case record.record => exact RTy.eq_of_beqA2 h
  case taggedUnion.taggedUnion => exact RTy.eq_of_beqTU h
  case recTaggedUnion.recTaggedUnion => exact RTy.eq_of_beqTU h
  case recObject.recObject => exact RTy.eq_of_beqA2 h
  case recAlias.recAlias => exact RTy.eq_of_beq h
  case mutualRecursiveFamily.mutualRecursiveFamily => exact RTy.eq_of_beqFamily h

/-- The same, for an invariant type former. -/
theorem RTy.eq_of_beqCov :
    ∀ {a b : LeanPrimTyCovariant RTy}, RTy.beqCov a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCov] <;> exact RTy.eq_of_beq h

/-- The same, for a list of types. -/
theorem RTy.eq_of_beqList : ∀ {a b : List RTy}, RTy.beqList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqList]
  exact ⟨RTy.eq_of_beq h.1, RTy.eq_of_beqList h.2⟩

/-- The same, for the constructors of a layout. -/
theorem RTy.eq_of_beqCtors : ∀ {a b : List (List RTy)}, RTy.beqCtors a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCtors]
  exact ⟨RTy.eq_of_beqList h.1, RTy.eq_of_beqCtors h.2⟩

/-- The same, for the fields of a record. -/
theorem RTy.eq_of_beqA2 : ∀ {a b : LeanRecordSchema RTy}, RTy.beqA2 a b = true → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [RTy.beqA2]
  exact ⟨RTy.eq_of_beq h.1.1, RTy.eq_of_beq h.1.2, RTy.eq_of_beqList h.2⟩

/-- The same, for the fields of a constructor that has at least one. -/
theorem RTy.eq_of_beqNE : ∀ {a b : NonEmptyList RTy}, RTy.beqNE a b = true → a = b := by
  intro a b h
  cases a
  cases b
  simp_all [RTy.beqNE]
  exact ⟨RTy.eq_of_beq h.1, RTy.eq_of_beqList h.2⟩

/-- The same, for the constructors of a tagged union. -/
theorem RTy.eq_of_beqTU :
    ∀ {a b : LeanTaggedUnionSchema RTy}, RTy.beqTU a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqTU]
  case payloadFirst.payloadFirst =>
    exact ⟨RTy.eq_of_beqNE h.1.1, RTy.eq_of_beqList h.1.2, RTy.eq_of_beqCtors h.2⟩
  case skip.skip => exact RTy.eq_of_beqCP h

/-- The same, for the constructors that follow a field-less one. -/
theorem RTy.eq_of_beqCP : ∀ {a b : CtorsWithPayload RTy}, RTy.beqCP a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqCP]
  case here.here => exact ⟨RTy.eq_of_beqNE h.1, RTy.eq_of_beqCtors h.2⟩
  case skip.skip => exact RTy.eq_of_beqCP h


/-- The same, for one member of a mutual family. -/
theorem RTy.eq_of_beqFam : ∀ {a b : LeanFamMemberSchema RTy}, RTy.beqFam a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFam]
  · exact RTy.eq_of_beqTU h
  · exact RTy.eq_of_beqA2 h
  · exact RTy.eq_of_beq h

/-- The same, for a list of members. -/
theorem RTy.eq_of_beqFamList :
    ∀ {a b : List (LeanFamMemberSchema RTy)}, RTy.beqFamList a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFamList]
  exact ⟨RTy.eq_of_beqFam h.1, RTy.eq_of_beqFamList h.2⟩

/-- The same, for two mutual families. -/
theorem RTy.eq_of_beqFamily :
    ∀ {a b : LeanMutualRecFamily RTy}, RTy.beqFamily a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> simp_all [RTy.beqFamily]
  · exact ⟨RTy.eq_of_beqFamList h.1.1.1, RTy.eq_of_beqFam h.1.1.2, RTy.eq_of_beqFam h.1.2,
      RTy.eq_of_beqFamList h.2⟩
  · exact ⟨RTy.eq_of_beqFam h.1.1, RTy.eq_of_beqFamList h.1.2, RTy.eq_of_beqFam h.2⟩

end



mutual

/-- Every type inside a recursive declaration compares equal to itself. -/
theorem RTy.beq_refl : ∀ (a : RTy), RTy.beq a a = true
  | .self _ => by simp [RTy.beq]
  | .prim _ => by simp [RTy.beq]
  | .fn a b => by simp [RTy.beq, RTy.beq_refl a, RTy.beq_refl b]
  | .primCovariant s => by simp [RTy.beq, RTy.beqCov_refl s]
  | .enum _ => by simp [RTy.beq]
  | .record a => by simp [RTy.beq, RTy.beqA2_refl a]
  | .taggedUnion a => by simp [RTy.beq, RTy.beqTU_refl a]
  | .recTaggedUnion a => by simp [RTy.beq, RTy.beqTU_refl a]
  | .recObject a => by simp [RTy.beq, RTy.beqA2_refl a]
  | .recAlias a => by simp [RTy.beq, RTy.beq_refl a]
  | .mutualRecursiveFamily a => by simp [RTy.beq, RTy.beqFamily_refl a]

/-- The same, for an invariant type former. -/
theorem RTy.beqCov_refl : ∀ (a : LeanPrimTyCovariant RTy), RTy.beqCov a a = true
  | .array a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .task a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .promise a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .thunk a => by simp [RTy.beqCov, RTy.beq_refl a]
  | .lazy a => by simp [RTy.beqCov, RTy.beq_refl a]

/-- The same, for a list of types. -/
theorem RTy.beqList_refl : ∀ (a : List RTy), RTy.beqList a a = true
  | [] => by simp [RTy.beqList]
  | a :: as => by simp [RTy.beqList, RTy.beq_refl a, RTy.beqList_refl as]

/-- The same, for the constructors of a layout. -/
theorem RTy.beqCtors_refl : ∀ (a : List (List RTy)), RTy.beqCtors a a = true
  | [] => by simp [RTy.beqCtors]
  | a :: as => by simp [RTy.beqCtors, RTy.beqList_refl a, RTy.beqCtors_refl as]

/-- The same, for the fields of a record. -/
theorem RTy.beqA2_refl : ∀ (a : LeanRecordSchema RTy), RTy.beqA2 a a = true
  | ⟨a1, a2, as⟩ => by
      simp [RTy.beqA2, RTy.beq_refl a1, RTy.beq_refl a2, RTy.beqList_refl as]

/-- The same, for the fields of a constructor that has at least one. -/
theorem RTy.beqNE_refl : ∀ (a : NonEmptyList RTy), RTy.beqNE a a = true
  | ⟨f, fs⟩ => by simp [RTy.beqNE, RTy.beq_refl f, RTy.beqList_refl fs]

/-- The same, for the constructors of a tagged union. -/
theorem RTy.beqTU_refl : ∀ (a : LeanTaggedUnionSchema RTy), RTy.beqTU a a = true
  | .payloadFirst f n r => by
      simp [RTy.beqTU, RTy.beqNE_refl f, RTy.beqList_refl n, RTy.beqCtors_refl r]
  | .skip a => by simp [RTy.beqTU, RTy.beqCP_refl a]

/-- The same, for the constructors that follow a field-less one. -/
theorem RTy.beqCP_refl : ∀ (a : CtorsWithPayload RTy), RTy.beqCP a a = true
  | .here f r => by simp [RTy.beqCP, RTy.beqNE_refl f, RTy.beqCtors_refl r]
  | .skip a => by simp [RTy.beqCP, RTy.beqCP_refl a]

/-- The same, for one member of a mutual family. -/
theorem RTy.beqFam_refl : ∀ (a : LeanFamMemberSchema RTy), RTy.beqFam a a = true
  | .ctors a => by simp [RTy.beqFam, RTy.beqTU_refl a]
  | .record a => by simp [RTy.beqFam, RTy.beqA2_refl a]
  | .alias a => by simp [RTy.beqFam, RTy.beq_refl a]

/-- The same, for a list of members. -/
theorem RTy.beqFamList_refl : ∀ (a : List (LeanFamMemberSchema RTy)), RTy.beqFamList a a = true
  | [] => by simp [RTy.beqFamList]
  | a :: as => by simp [RTy.beqFamList, RTy.beqFam_refl a, RTy.beqFamList_refl as]

/-- The same, for a mutual family. -/
theorem RTy.beqFamily_refl : ∀ (a : LeanMutualRecFamily RTy), RTy.beqFamily a a = true
  | .selectedThenMore b c n a => by
      simp [RTy.beqFamily, RTy.beqFamList_refl b, RTy.beqFam_refl c, RTy.beqFam_refl n,
        RTy.beqFamList_refl a]
  | .selectedLast f b c => by
      simp [RTy.beqFamily, RTy.beqFam_refl f, RTy.beqFamList_refl b, RTy.beqFam_refl c]

end

instance : DecidableEq RTy := fun a b =>
  decidable_of_iff (RTy.beq a b = true) ⟨RTy.eq_of_beq, fun h => h ▸ RTy.beq_refl a⟩

instance : BEq RTy := ⟨RTy.beq⟩
instance : ReflBEq RTy where
  rfl {a} := RTy.beq_refl a
instance : LawfulBEq RTy where
  eq_of_beq := by intro a b; exact RTy.eq_of_beq

-- instance : Inhabited RTy := ⟨.prim .bool⟩
instance : CoeOut (LeanPrimTy) RTy := ⟨.prim⟩
instance : CoeOut (LeanPrimTyCovariant RTy) RTy := ⟨.primCovariant⟩

namespace RTy

/-! ## The shared type formers, as abbreviations -/

/-- In JS: an array. -/
@[match_pattern] abbrev array (α : RTy) : RTy := .primCovariant (.array α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev task (α : RTy) : RTy := .primCovariant (.task α)
/-- In JS: `Promise<α>`. -/
@[match_pattern] abbrev promise (α : RTy) : RTy := .primCovariant (.promise α)
/-- A thunk. -/
@[match_pattern] abbrev thunk (α : RTy) : RTy := .primCovariant (.thunk α)

/-- The enum with `n` constructors numbered from `shift`, one layer down; `none` unless
    `n` is a number of constructors an enum can have. -/
def enumOfCount? (n : Nat) (shift : Int := 0) : Option RTy :=
  (LeanEnumSchema.ofCount? n shift).map RTy.enum

/-- The type of a field-less sum with `n` constructors, one layer down: `RTy.prim .bool`
    for two of them and an enum for three or more, and `none` for the degenerate
    cases. -/
def enumOrBool? (n : Nat) (shift : Int := 0) : Option RTy :=
  if n == 2 && shift == 0 then some (.prim .bool) else enumOfCount? n shift

end RTy

end LeanScript

end
