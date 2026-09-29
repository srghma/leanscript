module

public import JsTerm.Ops.Lookup

public section

set_option autoImplicit false

/-!
# No extern has two candidates at one signature

An extern has several candidates (`JsOp.cands`): one operation for every choice of
representation of the configurable Lean types of its signature (`bigint_nat__lean_nat_div` and
`uint53__lean_nat_div` for `lean_nat_div`), or, for the array operations, one for a generic and
one for a typed array.  They are not duplicates: their signatures are pairwise distinct
(`cands_sig_nodup`).  So a call, whose argument and result types are fixed, has at most one
candidate (`cands_unique`), and the operation `JsOp.lookup` finds is that one
(`lookup_unique`): picking the *first* candidate at the signature never hides another.
-/

namespace MoreJs

namespace JsOp

/-- Distinct signatures in a list of candidates: no two candidates at one signature. -/
private theorem eq_of_sig_nodup {l : List Cand} (h : (l.map Cand.sig).Nodup) :
    ∀ {c₁ c₂ : Cand}, c₁ ∈ l → c₂ ∈ l → c₁.sig = c₂.sig → c₁ = c₂ := by
  induction l with
  | nil => intro _ _ h₁; cases h₁
  | cons c l ih =>
    intro c₁ c₂ h₁ h₂ hs
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hc, hl⟩ := h
    cases h₁ with
    | head =>
      cases h₂ with
      | head => rfl
      | tail _ h₂ => exact absurd ⟨c₂, h₂, hs.symm⟩ hc
    | tail _ h₁ =>
      cases h₂ with
      | head => exact absurd ⟨c₁, h₁, hs⟩ hc
      | tail _ h₂ => exact ih hl h₁ h₂ hs

/-- The candidate `firstOf` finds is one of the list, at the signature asked for. -/
private theorem mem_of_firstOf {σs : List JsTy} {τ : JsTy} :
    ∀ {l : List Cand} {e : Effectfulness} {t : MayThrow} {op : JsOp e t σs τ},
      firstOf σs τ l = some ⟨e, t, op⟩ → (⟨σs, τ, e, t, op⟩ : Cand) ∈ l
  | [], _, _, _, h => by simp [firstOf] at h
  | ⟨σs', τ', e', t', op'⟩ :: rest, e, t, op, h => by
    unfold firstOf at h
    split at h
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_firstOf h)

/-- A property of the candidates of every group holds of the candidates of the first group that
    has the extern. -/
private theorem getD_orElse {P : List Cand → Prop} {a b : Option (List Cand)}
    (ha : P (a.getD [])) (hb : P (b.getD [])) : P ((a <|> b).getD []) := by
  cases a with
  | none => exact hb
  | some _ => exact ha

private theorem nodup_nat (name : String) : (((candsNat? name).getD []).map Cand.sig).Nodup := by
  unfold candsNat?; split <;> decide

private theorem nodup_uint (name : String) :
    (((candsUInt? name).getD []).map Cand.sig).Nodup := by
  unfold candsUInt?; split <;> decide

private theorem nodup_sint (name : String) :
    (((candsSInt? name).getD []).map Cand.sig).Nodup := by
  unfold candsSInt?; split <;> decide

private theorem nodup_float (name : String) :
    (((candsFloat? name).getD []).map Cand.sig).Nodup := by
  unfold candsFloat?; split <;> decide

private theorem nodup_string (name : String) :
    (((candsString? name).getD []).map Cand.sig).Nodup := by
  unfold candsString?; split <;> decide

private theorem nodup_misc (name : String) (σs : List JsTy) (τ : JsTy) :
    (((candsMisc? name σs τ).getD []).map Cand.sig).Nodup := by
  unfold candsMisc?; split <;> (try decide)
  all_goals simp only [Option.getD_some, «cands_lean_array_fset», «cands_lean_array_fswap»,
    «cands_lean_array_get», «cands_lean_array_get_borrowed», «cands_lean_array_get_size»,
    «cands_lean_array_mk», «cands_lean_array_pop», «cands_lean_array_push», «cands_lean_array_set»,
    «cands_lean_array_swap», «cands_lean_array_to_list», «cands_lean_dbg_trace_if_shared»,
    «cands_lean_mk_array», «cands_lean_mk_empty_array_with_capacity__Array_emptyWithCapacity»,
    «cands_lean_mk_empty_array_with_capacity__Array_mkEmpty», «cands_lean_mk_thunk»,
    «cands_lean_thunk_get_own», «cands_lean_thunk_pure»]
  all_goals
    generalize layoutOf? (σs ++ [τ]) = x
    rcases x with _ | ⟨a, e, l⟩ <;> (try cases l) <;> simp [Cand.sig]

private theorem nodup_arrayStd (name : String) (σs : List JsTy) (τ : JsTy) :
    (((candsArrayStd? name σs τ).getD []).map Cand.sig).Nodup := by
  unfold candsArrayStd?; split <;> (try decide)
  all_goals simp only [Option.getD_some, «cands_lean_array_all», «cands_lean_array_any», «cands_lean_array_append», «cands_lean_array_back_opt», «cands_lean_array_contains», «cands_lean_array_count_p», «cands_lean_array_erase_idx», «cands_lean_array_erase_idx_if_in_bounds», «cands_lean_array_extract», «cands_lean_array_filter», «cands_lean_array_find_idx_opt», «cands_lean_array_find_opt», «cands_lean_array_flat_map», «cands_lean_array_flatten», «cands_lean_array_foldr», «cands_lean_array_idx_of_opt», «cands_lean_array_insert_idx», «cands_lean_array_insert_idx_if_in_bounds», «cands_lean_array_map», «cands_lean_array_qsort», «cands_lean_array_reverse», «cands_lean_array_zip», «cands_lean_array_zip_with», «cands_lean_list_append»]
  all_goals (repeat' split) <;> simp [Cand.sig]

/-- The candidates of an extern have pairwise distinct signatures. -/
theorem cands_sig_nodup (name : String) (σs : List JsTy) (τ : JsTy) :
    ((cands name σs τ).map Cand.sig).Nodup := by
  unfold cands
  refine getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_nat name) ?_
  refine getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_uint name) ?_
  refine getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_sint name) ?_
  refine getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_float name) ?_
  refine getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_string name) ?_
  exact getD_orElse (P := fun l => (l.map Cand.sig).Nodup) (nodup_misc name σs τ)
    (nodup_arrayStd name σs τ)

/-- **Only one candidate per signature**: two candidates of an extern at the same signature are
    the same candidate. -/
theorem cands_unique {name : String} {σs : List JsTy} {τ : JsTy} {c₁ c₂ : Cand}
    (h₁ : c₁ ∈ cands name σs τ) (h₂ : c₂ ∈ cands name σs τ) (hs : c₁.sig = c₂.sig) : c₁ = c₂ :=
  eq_of_sig_nodup (cands_sig_nodup name σs τ) h₁ h₂ hs

/-- **The operation found is the only candidate**: when `lookup` finds an operation of the
    extern `name` at the signature `σs → τ`, every candidate of the extern at that signature is
    this operation. -/
theorem lookup_unique {name : String} {σs : List JsTy} {τ : JsTy} {e : Effectfulness}
    {t : MayThrow} {op : JsOp e t σs τ} (h : lookup name σs τ = some ⟨e, t, op⟩)
    {c : Cand} (hc : c ∈ cands name σs τ) (hs : c.sig = (σs, τ)) :
    c = ⟨σs, τ, e, t, op⟩ :=
  cands_unique hc (mem_of_firstOf h) hs

end JsOp

end MoreJs

end
