module

public import LeanScript.Den.Rec

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# Selecting a member of a mutual recursive family, and its containers

Facts about `LeanMutualRecFamily.select` / `memberIdx`, and the equation
`Ty.den_familyMemberTy` that the values of a family (`LeanScript.Den.Family`) move along.
-/

/-! ## Selecting a member -/

namespace LeanMutualRecFamily

variable {α : Type}

theorem memberIdx_ofMembers? {ms : List (LeanFamMemberSchema α)} {i : Nat}
    {f : LeanMutualRecFamily α} (h : ofMembers? ms i = some f) : f.memberIdx = i := by
  unfold ofMembers? at h
  split at h
  · exact absurd h (by simp)
  · rename_i m hi
    have hlt : i < ms.length := by
      cases Nat.lt_or_ge i ms.length with
      | inl h' => exact h'
      | inr h' =>
          rw [List.getElem?_eq_none_iff.mpr h'] at hi
          simp at hi
    split at h
    · split at h
      · injection h with h
        subst h
        simp [memberIdx, List.length_take]
        omega
      · exact absurd h (by simp)
    · rename_i hd
      cases hb : ms.take i with
      | nil => simp [hb] at h
      | cons first bs =>
          simp only [hb, Option.some.injEq] at h
          subst h
          have := congrArg List.length hb
          simp only [List.length_take, List.length_cons] at this
          simp only [memberIdx]
          omega

theorem ofMembers?_isSome {ms : List (LeanFamMemberSchema α)} {i : Nat}
    (hi : i < ms.length) (h2 : 2 ≤ ms.length) : (ofMembers? ms i).isSome := by
  unfold ofMembers?
  rw [List.getElem?_eq_getElem hi]
  simp only
  split
  · simp [h2]
  · rename_i hd
    cases hb : ms.take i with
    | nil =>
        have := congrArg List.length hb
        have := congrArg List.length hd
        simp only [List.length_take, List.length_drop, List.length_nil] at *
        omega
    | cons first bs => simp

theorem ofMembers?_eq_none {ms : List (LeanFamMemberSchema α)} {i : Nat}
    (hi : ms.length ≤ i) : ofMembers? ms i = none := by
  unfold ofMembers?
  rw [List.getElem?_eq_none_iff.mpr hi]

/-- The member a family selecting `i` selects: `i` if the family has it, and member `0`
    otherwise. -/
theorem memberIdx_select (f : LeanMutualRecFamily α) (i : Nat) :
    (f.select i).memberIdx = selIdx f.members.length i := by
  unfold select selIdx
  split
  · rename_i g h
    have hi : i < f.members.length := by
      cases Nat.lt_or_ge i f.members.length with
      | inl h' => exact h'
      | inr h' => rw [ofMembers?_eq_none h'] at h; cases h
    simp only [hi, ↓reduceIte]
    exact memberIdx_ofMembers? h
  · rename_i h
    have hi : ¬ i < f.members.length := by
      intro hi
      have := ofMembers?_isSome hi f.two_le_members
      rw [h] at this
      cases this
    simp only [hi, ↓reduceIte]
    have h0 := ofMembers?_isSome (ms := f.members) (i := 0) (by have := f.two_le_members; omega)
      f.two_le_members
    cases h' : ofMembers? f.members 0 with
    | none => rw [h'] at h0; cases h0
    | some g => exact memberIdx_ofMembers? h'

theorem current_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).current = f.current.map g := by
  cases f <;> rfl

theorem memberIdx_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).memberIdx = f.memberIdx := by
  cases f <;> simp [map, memberIdx]

theorem members_map {β : Type} (g : α → β) (f : LeanMutualRecFamily α) :
    (f.map g).members = f.members.map (·.map g) := by
  cases f <;> simp [map, members, Functor.map]

end LeanMutualRecFamily

/-! ## The containers of a family -/

namespace IPFunctorFacts

theorem at_map {α : Type} (F : α → IPFunctor) (ms : List α) (i : Nat) (m : α)
    (h : ms[i]? = some m) : IPFunctor.at (ms.map F) i = F m := by
  rw [IPFunctor.at, List.getD_eq_getElem?_getD, List.getElem?_map, h]
  rfl

theorem at_map_of_le {α : Type} (F : α → IPFunctor) (ms : List α) (i : Nat)
    (h : ms.length ≤ i) : IPFunctor.at (ms.map F) i = IPFunctor.const PEmpty := by
  rw [IPFunctor.at, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none h]
  rfl

end IPFunctorFacts

namespace Ty

theorem toIPFMemberList_eq : ∀ ms : List (LeanFamMemberSchema Ty),
    toIPFMemberList ms = ms.map toIPFMember
  | [] => rfl
  | m :: ms => by simp only [toIPFMemberList, List.map_cons, toIPFMemberList_eq ms]

/-- The containers of a family are the containers of its members, in order. -/
theorem toIPFFamily_eq (f : LeanMutualRecFamily Ty) :
    toIPFFamily f = f.members.map toIPFMember := by
  cases f <;> simp [toIPFFamily, LeanMutualRecFamily.members, toIPFMemberList_eq]

theorem length_toIPFFamily (f : LeanMutualRecFamily Ty) :
    (toIPFFamily f).length = f.members.length := by
  rw [toIPFFamily_eq, List.length_map]

/-- The container of the member a family selects. -/
theorem at_toIPFFamily_memberIdx (f : LeanMutualRecFamily Ty) :
    IPFunctor.at (toIPFFamily f) f.memberIdx = toIPFMember f.current := by
  rw [toIPFFamily_eq]
  exact IPFunctorFacts.at_map _ _ _ _ f.getElem?_memberIdx

/-- **A value of member `j` of a family is a node of the family's W-type** rooted at
    `selIdx _ j` — for every `j`, in range or not. -/
theorem den_familyMemberTy (f : LeanMutualRecFamily Ty) (j : Nat) :
    Ty.Den (familyMemberTy f j) = FamW (toIPFFamily f) (selIdx (toIPFFamily f).length j) := by
  show FamW (toIPFFamily (f.select j)) (f.select j).memberIdx = _
  rw [LeanMutualRecFamily.memberIdx_select, toIPFFamily_eq (f.select j),
    LeanMutualRecFamily.members_select, ← toIPFFamily_eq, length_toIPFFamily]

end Ty

end LeanScript

end
