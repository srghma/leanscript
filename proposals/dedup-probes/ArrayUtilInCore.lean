/-! Probe for proposals/DeduplicationProposal.md, section 6.
Plain Lean 4.34.0.  Expected: compiles with no errors.
The two `NonEmpty.ArrayUtil` lemmas follow from core lemmas. -/

theorem a1 (as : Array α) (f : α → β) : as.flatMap (fun a => #[f a]) = as.map f := Array.map_eq_flatMap.symm
theorem a2 (t : Array α) (f : α → β) : (t.map (fun a => #[f a])).flatten = t.map f := by
  simp [← Array.flatMap_def, ← Array.map_eq_flatMap]
#check @Array.flatMap_def
