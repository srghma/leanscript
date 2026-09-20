module

@[expose] public section

namespace NonEmpty.ArrayUtil

@[simp] theorem flatten_map_singleton (t : Array α) (f : α → β) :
    (t.map (fun a => #[f a])).flatten = t.map f := by
  have H : (t.map (fun a => #[f a])).flatten.toList = (t.map f).toList := by
    simp only [Array.toList_flatten, Array.toList_map, List.map_map, Function.comp_def]
    induction t.toList with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, List.flatten_cons, ih, List.cons_append,
      List.nil_append]
  cases h₁ : (t.map (fun a => #[f a])).flatten with | mk l₁ =>
  cases h₂ : t.map f with | mk l₂ =>
  simp_all

@[simp] theorem flatMap_singleton_eq_map (as : Array α) (f : α → β) :
    as.flatMap (fun a => #[f a]) = as.map f := by
  have H : (as.flatMap (fun a => #[f a])).toList = (as.map f).toList := by
    simp only [Array.toList_flatMap, Array.toList_map]
    induction as.toList
    · simp only [List.flatMap_nil, List.map_nil]
    · simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons, *]
  cases h₁ : as.flatMap (fun a => #[f a])
  cases h₂ : as.map f
  simp_all

@[simp] theorem append_flatten_assoc (a : Array α) (b : Array (Array α)) (c : Array (Array α)) :
    a ++ (b ++ c).flatten = a ++ b.flatten ++ c.flatten := by
  simp only [Array.flatten_append, Array.append_assoc]

@[simp, inline]
def foldMap {α ω} (op : ω → ω → ω) (f : α → ω) (init : ω) (as : Array α) : ω :=
  as.foldl (fun acc x => op acc (f x)) init

/--
Map each element of a structure to an action, evaluate these actions from
left to right, and collect the results. For Applicative functors.
-/
@[simp, inline]
def mapA [Applicative m] (f : α → m β) (as : Array α) : m (Array β) :=
  as.foldl (fun macc x => (fun acc y => acc.push y) <$> macc <*> f x) (pure (Array.emptyWithCapacity as.size))

/-- Evaluate each action in the structure from left to right, and collect the results. -/
@[simp, inline]
def sequence [Applicative m] (as : Array (m α)) : m (Array α) :=
  mapA id as

end NonEmpty.ArrayUtil
