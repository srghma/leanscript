module

public import Std.Data.HashMap.AdditionalOperations
public import Std.Data.HashMap.Lemmas
import all Std.Data.HashMap.Basic
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.AdditionalOperations
import all Std.Data.HashMap.AdditionalOperations
import all Std.Data.DHashMap.Internal.Defs
import all Std.Data.DHashMap.Internal.AssocList.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Mapping a hash map twice

`Std.HashMap.map` maps the values of every bucket (`Std.DHashMap.Internal.AssocList.map`, which
walks a bucket with an accumulator, so it reverses the bucket).  Mapping twice therefore puts
every bucket back in its order: when the second function undoes the first, the hash map is the
one we started from, **equal** and not only equivalent (`Std.HashMap.map_map_of_leftInverse`).
This is what the transports of `Ty.strMap` (`Ty.lift`, `Ty.lower`) need to be inverses.
-/

namespace LeanScript.AssocListMap

open Std.DHashMap.Internal

variable {α : Type}

/-- The walk of `AssocList.map`, spelled out (the library's is private). -/
def go {β γ : α → Type} (f : (a : α) → β a → γ a) : AssocList α γ → AssocList α β → AssocList α γ
  | acc, .nil => acc
  | acc, .cons a b l => go f (.cons a (f a b) acc) l

/-- `l` reversed in front of `acc`. -/
def rev {β : α → Type} : AssocList α β → AssocList α β → AssocList α β
  | .nil, acc => acc
  | .cons a b l, acc => rev l (.cons a b acc)

/-- The map that keeps the order. -/
def mapA {β γ : α → Type} (f : (a : α) → β a → γ a) : AssocList α β → AssocList α γ
  | .nil => .nil
  | .cons a b l => .cons a (f a b) (mapA f l)

theorem map_eq_go {β γ : α → Type} (f : (a : α) → β a → γ a) (l : AssocList α β) :
    AssocList.map f l = go f .nil l := by
  rw [AssocList.map.eq_1]
  generalize (AssocList.nil : AssocList α γ) = acc
  induction l generalizing acc with
  | nil => rfl
  | cons a b l ih => exact ih _

theorem go_eq {β γ : α → Type} (f : (a : α) → β a → γ a) (l : AssocList α β)
    (acc : AssocList α γ) : go f acc l = rev (mapA f l) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a b l ih => exact ih _

theorem mapA_rev {β γ : α → Type} (f : (a : α) → β a → γ a) (l acc : AssocList α β) :
    mapA f (rev l acc) = rev (mapA f l) (mapA f acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons a b l ih => exact ih _

theorem rev_rev {β : α → Type} (l acc : AssocList α β) : rev (rev l acc) .nil = rev acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons a b l ih => exact ih _

theorem mapA_mapA {β γ : α → Type} (f : (a : α) → β a → γ a) (g : (a : α) → γ a → β a)
    (h : ∀ a b, g a (f a b) = b) (l : AssocList α β) : mapA g (mapA f l) = l := by
  induction l with
  | nil => rfl
  | cons a b l ih => simp only [mapA, h, ih]

/-- Mapping a bucket twice, the second function undoing the first, gives the bucket back. -/
theorem map_map {β γ : α → Type} (f : (a : α) → β a → γ a) (g : (a : α) → γ a → β a)
    (h : ∀ a b, g a (f a b) = b) (l : AssocList α β) :
    AssocList.map g (AssocList.map f l) = l := by
  rw [map_eq_go, map_eq_go, go_eq, go_eq, mapA_rev, mapA_mapA f g h]
  exact rev_rev l .nil

end LeanScript.AssocListMap

/-- Mapping the values of a hash map twice, the second function undoing the first, gives the
    hash map back (equal, not only equivalent). -/
theorem Std.HashMap.map_map_of_leftInverse {α β γ : Type} [BEq α] [Hashable α] (f : β → γ)
    (g : γ → β) (h : ∀ x, g (f x) = x) (m : Std.HashMap α β) :
    (m.map (fun _ v => f v)).map (fun _ v => g v) = m := by
  rcases m with ⟨⟨⟨size, buckets⟩, wf⟩⟩
  simp only [Std.HashMap.map, Std.DHashMap.map, Std.DHashMap.Internal.Raw₀.map,
    Std.HashMap.mk.injEq, Std.DHashMap.mk.injEq, Std.DHashMap.Raw.mk.injEq, true_and,
    Array.map_map]
  conv => rhs; rw [← Array.map_id buckets]
  congr 1; funext l
  exact LeanScript.AssocListMap.map_map _ _ (fun _ b => h b) l

namespace LeanScript.StrMapPoints

/-- The empty string-keyed map is empty. -/
theorem isEmpty_empty {β : Type} : (∅ : Std.HashMap String β).isEmpty = true :=
  Std.HashMap.isEmpty_empty

/-- A map with a key is not empty. -/
theorem isEmpty_one {β : Type} (v : β) :
    ((∅ : Std.HashMap String β).insert "" v).isEmpty = false :=
  Std.HashMap.isEmpty_insert

theorem size_empty {β : Type} : (∅ : Std.HashMap String β).size = 0 :=
  Std.HashMap.size_empty

theorem size_one {β : Type} (v : β) : ((∅ : Std.HashMap String β).insert "" v).size = 1 := by
  simp [Std.HashMap.size_insert]

theorem size_two {β : Type} (v : β) :
    (((∅ : Std.HashMap String β).insert "" v).insert "a" v).size = 2 := by
  rw [Std.HashMap.size_insert, size_one]
  simp [Std.HashMap.mem_insert]

end LeanScript.StrMapPoints

end
