module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# The new redex checks reject only real redexes

The grammar `LeanScript.Term` rejects a node by a check on the **indices** of its subterms
(their `LeanScript.Head` and `LeanScript.Usage`), not on the subterms themselves.  This
module proves, against the evaluator `Term.eval`, that the checks added for the record
η-redex and for dispatches on numbers whose branches are the same leaf only fire on nodes
whose value is what their reduced form says:

* `Term.eval_of_head_var`, `Term.eval_of_head_bool`: a term whose head is a variable (a
  boolean literal) *is* that variable (that literal) — its value is the variable's value;
* `Term.eval_eq_of_sameLeaf`, `Term.eval_eq_of_sameLeafOver`,
  `Term.eval_eq_of_sameLeafPast` and the dispatch forms `Term.nat_dispatch_eq_of_sameLeafOver`,
  `Term.int_dispatch_eq_of_sameLeafPast`: branches the `hSame` checks of `Term.bool_casesOn`,
  `Term.nat_casesOn` and `Term.int_casesOn` reject have one value, so the dispatch is that
  value;
* `Term.eval_of_isRecordEta`, `Term.record_casesOn_eval_of_isRecordEta`: a body the `hEta`
  check of `Term.record_casesOn` rejects has the record's type and, run with the fields of a
  record bound, gives that record back — the dispatch is its scrutinee;
* `Head.readsScrutinee_var_eq_false_iff`, `Head.ctorOf_eq_rebuild_iff`: what the `hLit`
  check and the head `Head.rebuild` say, exactly.
-/

namespace LeanScript

namespace Head

theorem join_ne_var (a b : Head) (i : Nat) : Head.join a b ≠ .var i := by
  unfold Head.join; split <;> [simp; split <;> simp]

theorem join_ne_bool (a b : Head) (c : Bool) : Head.join a b ≠ .bool c := by
  unfold Head.join; split <;> [simp; split <;> simp]

theorem join_ne_rebuild (a b : Head) (n : Nat) : Head.join a b ≠ .rebuild n := by
  unfold Head.join; split <;> [simp; split <;> simp]

theorem ctorOf_ne_var (ks : List Head) (i : Nat) : Head.ctorOf ks ≠ .var i := by
  unfold Head.ctorOf; split <;> [simp; split <;> simp]

theorem ctorOf_ne_bool (ks : List Head) (c : Bool) : Head.ctorOf ks ≠ .bool c := by
  unfold Head.ctorOf; split <;> [simp; split <;> simp]

end Head

section
variable {Sg : Sig}

theorem EnumCases.head_join {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {s : LeanEnumSchema} {k : Head}
    (c : EnumCases Sg Γ u τ s k) : ∃ a b, k = Head.join a b := by
  cases c <;> exact ⟨_, _, rfl⟩

theorem TaggedUnionCases.head_join {Γ : Ctx} {u : Usage Γ} {l : LeanTaggedUnionSchema TyWf}
    {τ : TyWf} {k : Head} (c : TaggedUnionCases Sg Γ u l τ k) : ∃ a b, k = Head.join a b := by
  cases c <;> exact ⟨_, _, rfl⟩

theorem FamilyMemberCases.head_join {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {m : LeanFamMemberSchema TyWf} {k : Head} (c : FamilyMemberCases Sg Γ u τ m k) :
    ∃ a b, k = Head.join a b := by
  cases c with
  | ctors c => exact TaggedUnionCases.head_join c
  | _ => exact ⟨_, _, rfl⟩

end

theorem Usage.head_single_le {Γ : Ctx} {σ τ : TyWf} (x : (σ :: Γ) ∋ τ) :
    Usage.head (Usage.single x) ≤ 1 := by
  cases x <;> simp [Usage.single, Usage.head, Usage.cons]

theorem Usage.head_zero {Γ : Ctx} {σ : TyWf} : Usage.head (0 : Usage (σ :: Γ)) = 0 := rfl

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

theorem Term.eval_of_head_var_aux (n : Nat) : ∀ {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {hd : Head}
    (t : Term Sg Γ u τ hd), sizeOf t < n → ∀ (i : Nat), hd = .var i →
    ∃ x : Γ ∋ τ, x.index = i ∧ u = Usage.single x ∧
      ∀ (env : Env Γ) (h : Term.NoRecMk t), Term.eval G t env h = Env.get x env := by
  induction n with
  | zero => intro _ _ _ _ _ hn; omega
  | succ n ih =>
  intro Γ u τ hd t hn i hh
  cases t with
  | var x => exact ⟨x, by cases hh; rfl, rfl, fun _ _ => rfl⟩
  | enum_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := EnumCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_var a b i)
  | taggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_var a b i)
  | recTaggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_var a b i)
  | mutualRecursiveFamily_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := FamilyMemberCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_var a b i)
  | _ =>
    exfalso
    first
      | exact Head.join_ne_var _ _ _ hh
      | exact Head.ctorOf_ne_var _ _ hh
      | exact absurd hh (by simp)

theorem Term.eval_of_head_bool_aux (n : Nat) : ∀ {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {hd : Head}
    (t : Term Sg Γ u τ hd), sizeOf t < n → ∀ (c : Bool), hd = .bool c →
    ∃ hτ : τ = .prim .bool, u = 0 ∧
      ∀ (env : Env Γ) (h : Term.NoRecMk t), Term.eval G t env h = hτ ▸ (c : TyWf.Den (.prim .bool)) := by
  induction n with
  | zero => intro _ _ _ _ _ hn; omega
  | succ n ih =>
  intro Γ u τ hd t hn i hh
  cases t with
  | bool_mk c => cases hh; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | enum_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := EnumCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_bool a b i)
  | taggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_bool a b i)
  | recTaggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_bool a b i)
  | mutualRecursiveFamily_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := FamilyMemberCases.head_join cs
    exact absurd (e.symm.trans hh) (Head.join_ne_bool a b i)
  | _ =>
    exfalso
    first
      | exact Head.join_ne_bool _ _ _ hh
      | exact Head.ctorOf_ne_bool _ _ hh
      | exact absurd hh (by simp)

/-- **A term whose head is a variable is that variable**: its grades are one use of it, and
    its value is the variable's value.  (The only other constructor that could have such a
    head, a `let`, cannot: its body would read the `let`'s variable at most once.) -/
theorem Term.eval_of_head_var {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {hd : Head}
    (t : Term Sg Γ u τ hd) (i : Nat) (hh : hd = .var i) :
    ∃ x : Γ ∋ τ, x.index = i ∧ u = Usage.single x ∧
      ∀ (env : Env Γ) (h : Term.NoRecMk t), Term.eval G t env h = Env.get x env :=
  Term.eval_of_head_var_aux G _ t (Nat.lt_succ_self _) i hh

/-- **A term whose head is a boolean literal is that literal.** -/
theorem Term.eval_of_head_bool {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {hd : Head}
    (t : Term Sg Γ u τ hd) (c : Bool) (hh : hd = .bool c) :
    ∃ hτ : τ = .prim .bool, u = 0 ∧
      ∀ (env : Env Γ) (h : Term.NoRecMk t), Term.eval G t env h = hτ ▸ (c : TyWf.Den (.prim .bool)) :=
  Term.eval_of_head_bool_aux G _ t (Nat.lt_succ_self _) c hh

/-- Two variables of one context and one type at the same de Bruijn index are the same. -/
theorem DeBruijnProj.eq_of_index_eq {α : Type} : ∀ {xs : List α} {b : α}
    (x y : DeBruijnProj id xs b), x.index = y.index → x = y
  | _, _, .head, .head, _ => rfl
  | _, _, .tail x, .tail y, h => by
      simp only [DeBruijnProj.index, Nat.add_right_cancel_iff] at h
      rw [DeBruijnProj.eq_of_index_eq x y h]
  | _, _, .head, .tail _, h => by simp [DeBruijnProj.index] at h
  | _, _, .tail _, .head, h => by simp [DeBruijnProj.index] at h

/-! ## Branches that are the same leaf -/

/-- **`hSame` of `Term.bool_casesOn` rejects only real redexes**: two terms whose heads are
    the same leaf (`Head.sameLeaf`) have the same value, so `if c then t else e` is `t`. -/
theorem Term.eval_eq_of_sameLeaf {Γ : Ctx} {τ : TyWf} {u v : Usage Γ} {kt ke : Head}
    (t : Term Sg Γ u τ kt) (e : Term Sg Γ v τ ke) (hs : Head.sameLeaf kt ke = true)
    (env : Env Γ) (ht : Term.NoRecMk t) (he : Term.NoRecMk e) :
    Term.eval G t env ht = Term.eval G e env he := by
  cases kt <;> cases ke <;> simp [Head.sameLeaf] at hs
  case var.var i j =>
    subst hs
    obtain ⟨x, hx, -, hxe⟩ := Term.eval_of_head_var G t i rfl
    obtain ⟨y, hy, -, hye⟩ := Term.eval_of_head_var G e i rfl
    rw [hxe, hye, DeBruijnProj.eq_of_index_eq x y (hx.trans hy.symm)]
  case bool.bool a b =>
    subst hs
    obtain ⟨hτ, -, h1⟩ := Term.eval_of_head_bool G t a rfl
    obtain ⟨hτ', -, h2⟩ := Term.eval_of_head_bool G e a rfl
    rw [h1, h2]

/-- **`hSame` of `Term.nat_casesOn` rejects only real redexes**: when the zero branch `z` and
    the successor branch `s` (which binds the predecessor) are the same leaf of the context
    outside (`Head.sameLeafOver`), the successor branch has the zero branch's value whatever
    the predecessor is. -/
theorem Term.eval_eq_of_sameLeafOver {Γ : Ctx} {σ τ : TyWf} {v : Usage Γ} {w : Usage (σ :: Γ)}
    {kz ks : Head} (z : Term Sg Γ v τ kz) (s : Term Sg (σ :: Γ) w τ ks)
    (hs : Head.sameLeafOver kz ks = true) (k : TyWf.Den σ) (env : Env Γ)
    (hz : Term.NoRecMk z) (hs' : Term.NoRecMk s) :
    Term.eval G s (k, env) hs' = Term.eval G z env hz := by
  unfold Head.sameLeafOver at hs
  split at hs
  · rename_i i j
    simp only [beq_iff_eq] at hs
    subst hs
    obtain ⟨x, hx, -, hxe⟩ := Term.eval_of_head_var G z i rfl
    obtain ⟨y, hy, -, hye⟩ := Term.eval_of_head_var G s (i + 1) rfl
    rw [hxe, hye]
    cases y with
    | head => simp [DeBruijnProj.index] at hy
    | tail y =>
      simp only [DeBruijnProj.index, Nat.add_right_cancel_iff] at hy
      rw [DeBruijnProj.eq_of_index_eq y x (hy.trans hx.symm)]
      rfl
  · rename_i a b
    simp only [beq_iff_eq] at hs
    subst hs
    obtain ⟨hτ, -, h1⟩ := Term.eval_of_head_bool G z a rfl
    obtain ⟨hτ', -, h2⟩ := Term.eval_of_head_bool G s a rfl
    rw [h1, h2]
  · simp at hs

/-- **`hSame` of `Term.nat_casesOn`, as the evaluator reads it**: the dispatch
    `match n with | 0 => z | k + 1 => s` (what `Term.eval` computes for `Term.nat_casesOn`)
    is `z` for every `n`, so the rejected node would be its zero branch. -/
theorem Term.nat_dispatch_eq_of_sameLeafOver {Γ : Ctx} {τ : TyWf} {v : Usage Γ}
    {w : Usage (TyWf.prim .nat :: Γ)} {kz ks : Head} (z : Term Sg Γ v τ kz)
    (s : Term Sg (TyWf.prim .nat :: Γ) w τ ks) (hs : Head.sameLeafOver kz ks = true)
    (env : Env Γ) (hz : Term.NoRecMk z) (hs' : Term.NoRecMk s) (n : Nat) :
    (match n with
      | 0 => Term.eval G z env hz
      | k + 1 => Term.eval G s (k, env) hs') = Term.eval G z env hz := by
  cases n with
  | zero => rfl
  | succ k => exact Term.eval_eq_of_sameLeafOver G z s hs k env hz hs'

/-- **`hSame` of `Term.int_casesOn` rejects only real redexes**: two branches that each bind
    one variable and are the same leaf of the context outside (`Head.sameLeafPast`) have the
    same value, whatever each binds. -/
theorem Term.eval_eq_of_sameLeafPast {Γ : Ctx} {σ τ : TyWf} {v w : Usage (σ :: Γ)}
    {ka kb : Head} (a : Term Sg (σ :: Γ) v τ ka) (b : Term Sg (σ :: Γ) w τ kb)
    (hs : Head.sameLeafPast ka kb = true) (k k' : TyWf.Den σ) (env : Env Γ)
    (ha : Term.NoRecMk a) (hb : Term.NoRecMk b) :
    Term.eval G a (k, env) ha = Term.eval G b (k', env) hb := by
  unfold Head.sameLeafPast at hs
  split at hs
  · rename_i i j
    simp only [beq_iff_eq] at hs
    subst hs
    obtain ⟨x, hx, -, hxe⟩ := Term.eval_of_head_var G a (i + 1) rfl
    obtain ⟨y, hy, -, hye⟩ := Term.eval_of_head_var G b (i + 1) rfl
    rw [hxe, hye]
    cases x with
    | head => simp [DeBruijnProj.index] at hx
    | tail x =>
      cases y with
      | head => simp [DeBruijnProj.index] at hy
      | tail y =>
        simp only [DeBruijnProj.index, Nat.add_right_cancel_iff] at hx hy
        rw [DeBruijnProj.eq_of_index_eq x y (hx.trans hy.symm)]
        rfl
  · rename_i c d
    simp only [beq_iff_eq] at hs
    subst hs
    obtain ⟨hτ, -, h1⟩ := Term.eval_of_head_bool G a c rfl
    obtain ⟨hτ', -, h2⟩ := Term.eval_of_head_bool G b c rfl
    rw [h1, h2]
  · simp at hs

/-- **`hSame` of `Term.int_casesOn`, as the evaluator reads it**: the dispatch
    `match i with | .ofNat k => a | .negSucc k => b` is `a` at `0`, for every `i`. -/
theorem Term.int_dispatch_eq_of_sameLeafPast {Γ : Ctx} {τ : TyWf}
    {v w : Usage (TyWf.prim .nat :: Γ)} {ka kb : Head} (a : Term Sg (TyWf.prim .nat :: Γ) v τ ka)
    (b : Term Sg (TyWf.prim .nat :: Γ) w τ kb) (hs : Head.sameLeafPast ka kb = true)
    (env : Env Γ) (ha : Term.NoRecMk a) (hb : Term.NoRecMk b) (i : Int) :
    (match i with
      | .ofNat k => Term.eval G a (k, env) ha
      | .negSucc k => Term.eval G b (k, env) hb) = Term.eval G a ((0 : Nat), env) ha := by
  cases i with
  | ofNat k => exact Term.eval_eq_of_sameLeafPast G a a (by
      unfold Head.sameLeafPast at hs ⊢; split at hs <;> simp_all) k 0 env ha ha
  | negSucc k => exact (Term.eval_eq_of_sameLeafPast G a b hs 0 k env ha hb).symm

/-! ## The record η-redex -/

/-- The value at position `j` of the values of a list of types. -/
def TyWf.DenList.getAt : {as : List TyWf} → TyWf.DenList as → (j : Nat) → (h : j < as.length) →
    TyWf.Den (as[j])
  | _ :: _, vs, 0, _ => vs.1
  | _ :: _, vs, j + 1, h => TyWf.DenList.getAt vs.2 j (by simp at h; omega)

/-- The values of a list of types, but the first `j`. -/
def TyWf.DenList.dropAt : {as : List TyWf} → TyWf.DenList as → (j : Nat) → TyWf.DenList (as.drop j)
  | _, vs, 0 => vs
  | [], _, _ + 1 => PUnit.unit
  | _ :: _, vs, j + 1 => TyWf.DenList.dropAt vs.2 j

theorem TyWf.DenList.dropAt_heq : ∀ {as : List TyWf} (vs : TyWf.DenList as) (j : Nat)
    (h : j < as.length),
    HEq (TyWf.DenList.dropAt vs j)
      ((TyWf.DenList.getAt vs j h, TyWf.DenList.dropAt vs (j + 1)) :
        TyWf.Den (as[j]) × TyWf.DenList (as.drop (j + 1)))
  | _ :: _, _, 0, _ => by simp only [TyWf.DenList.dropAt, TyWf.DenList.getAt]; rfl
  | _ :: _, vs, j + 1, h => TyWf.DenList.dropAt_heq vs.2 j (by simp at h; omega)

/-- A variable of index `j < as.length`, read in an environment whose innermost values are
    `vs`, is the value at position `j` of `vs`. -/
theorem Env.get_append_of_index : ∀ {as : List TyWf} {Γ : Ctx} {σ : TyWf}
    (x : (as ++ Γ) ∋ σ) (j : Nat) (hj : j < as.length), x.index = j →
    σ = as[j] ∧ ∀ (vs : TyWf.DenList as) (env : Env Γ),
      HEq (Env.get x (Env.append vs env)) (TyWf.DenList.getAt vs j hj)
  | [], _, _, _, _, hj, _ => by simp at hj
  | _ :: _, _, _, .head, j, _, hx => by
      simp [DeBruijnProj.index] at hx; subst hx
      exact ⟨rfl, fun _ _ => HEq.rfl⟩
  | _ :: as, _, _, .tail x, j, hj, hx => by
      cases j with
      | zero => simp [DeBruijnProj.index] at hx
      | succ j =>
        simp only [DeBruijnProj.index, Nat.add_right_cancel_iff] at hx
        obtain ⟨hσ', h⟩ := Env.get_append_of_index (as := as) x j (by simp at hj; omega) hx
        exact ⟨hσ', fun vs env => h vs.2 env⟩

theorem Head.isVarRun_cons {j : Nat} {k : Head} {ks : List Head}
    (h : Head.isVarRun j (k :: ks) = true) : k = .var j ∧ Head.isVarRun (j + 1) ks = true := by
  cases k with
  | var i =>
    simp only [Head.isVarRun, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨by rw [h.1], h.2⟩
  | _ => simp [Head.isVarRun] at h

theorem TyWf.DenList.heq_unit_of_nil {l : List TyWf} (h : l = []) (x : TyWf.DenList l) :
    HEq (PUnit.unit : TyWf.DenList []) x := by
  subst h; rfl

theorem Spine.eval_varRun_aux (n : Nat) : ∀ {as : List TyWf} {Γ : Ctx} {u : Usage (as ++ Γ)}
    {bs : List TyWf} {ks : List Head} (sp : Spine Sg (as ++ Γ) u bs ks), sizeOf sp < n →
    ∀ (j : Nat), Head.isVarRun j ks = true → j + ks.length = as.length →
    bs = as.drop j ∧ ∀ (vs : TyWf.DenList as) (env : Env Γ) (h : Spine.NoRecMk sp),
      HEq (Spine.eval G sp (Env.append vs env) h) (TyWf.DenList.dropAt vs j) := by
  induction n with
  | zero => intro _ _ _ _ _ _ hn; omega
  | succ n ih =>
  intro as Γ u bs ks sp hn j hrun hlen
  cases sp with
  | nil =>
    have hd : as.drop j = [] := List.drop_eq_nil_of_le (by simp at hlen; omega)
    exact ⟨hd.symm, fun vs env h => TyWf.DenList.heq_unit_of_nil hd _⟩
  | cons t rest =>
    obtain ⟨hk, hrun'⟩ := Head.isVarRun_cons hrun
    simp only [List.length_cons] at hlen
    have hj : j < as.length := by omega
    obtain ⟨x, hx, -, hxe⟩ := Term.eval_of_head_var G t j hk
    obtain ⟨hσ, hget⟩ := Env.get_append_of_index x j hj hx
    obtain ⟨hbs, hrest⟩ := ih rest (by simp at hn; omega) (j + 1) hrun' (by omega)
    subst hσ hbs
    refine ⟨(List.drop_eq_getElem_cons hj).symm, fun vs env h => ?_⟩
    refine HEq.trans ?_ (TyWf.DenList.dropAt_heq vs j hj).symm
    show HEq (Term.eval G t (Env.append vs env) h.1, Spine.eval G rest (Env.append vs env) h.2) _
    rw [hxe]
    exact heq_of_eq (Prod.ext (eq_of_heq (hget vs env)) (eq_of_heq (hrest vs env h.2)))

theorem Head.isRecordEta_of_ne {k : Head} (h : ∀ m, k ≠ .rebuild m) (n : Nat) (τ : TyWf) :
    Head.isRecordEta k n τ = false := by
  unfold Head.isRecordEta; split
  · exact absurd rfl (h _)
  · rfl

theorem Head.isRecordEta_ctorOf {ks : List Head} {n : Nat} {τ : TyWf}
    (h : Head.isRecordEta (Head.ctorOf ks) n τ = true) :
    Head.isVarRun 0 ks = true ∧ ks.length = n ∧
      (match τ.toTy with | .shape (.record _) => true | _ => false) = true := by
  unfold Head.ctorOf at h
  split at h
  · simp [Head.isRecordEta] at h
  · split at h
    · rename_i hr
      simp only [Head.isRecordEta, Bool.and_eq_true, beq_iff_eq] at h hr
      exact ⟨hr.2, h.1, h.2⟩
    · simp [Head.isRecordEta] at h

theorem LeanRecordSchema.toList_inj {α : Type} {a b : LeanRecordSchema α}
    (h : a.toList = b.toList) : a = b := by
  cases a; cases b
  simp only [LeanRecordSchema.toList, List.cons.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- The value of a record built from a spine is the spine's values. -/
theorem Term.eval_record_mk_heq {Γ : Ctx} {fs : LeanRecordSchema TyWf} {u : Usage Γ}
    {ks : List Head} (sp : Spine Sg Γ u fs.toList ks) (hAnf : Head.allAtom ks = true)
    (env : Env Γ) (h : Term.NoRecMk (Term.record_mk fs sp hAnf)) :
    HEq (Term.eval G (Term.record_mk fs sp hAnf) env h) (Spine.eval G sp env h) :=
  cast_heq _ _

/-- **The record η-redex, formally**: a body of a dispatch on a record of schema `fs` that
    `Term.record_casesOn` rejects as an η-redex (`Head.isRecordEta`) has the record's own
    type, and, run with the fields of a record value `rv` bound — which is how
    `Term.eval` runs the body of `Term.record_casesOn` — its value is `rv` itself.  So the
    rejected dispatch would be its scrutinee: `match p with | (a, b) => (a, b)` is `p`. -/
theorem Term.eval_of_isRecordEta {Γ : Ctx} {fs : LeanRecordSchema TyWf}
    {v : Usage (fs.toList ++ Γ)} {τ : TyWf} {kb : Head}
    (body : Term Sg (fs.toList ++ Γ) v τ kb)
    (hη : Head.isRecordEta kb fs.toList.length τ = true) :
    τ = .record fs ∧ ∀ (rv : TyWf.Den (.record fs)) (env : Env Γ) (h : Term.NoRecMk body),
      HEq (Term.eval G body (Env.append (cast (Ty.denRecord_eq _) rv) env) h) rv := by
  cases body with
  | record_mk fs' sp hAnf =>
    obtain ⟨hrun, hlen, -⟩ := Head.isRecordEta_ctorOf hη
    obtain ⟨hbs, hsp⟩ := Spine.eval_varRun_aux G _ sp (Nat.lt_succ_self _) 0 hrun (by omega)
    obtain rfl := LeanRecordSchema.toList_inj hbs
    refine ⟨rfl, fun rv env h => ?_⟩
    exact (Term.eval_record_mk_heq G sp hAnf _ h).trans ((hsp _ env h).trans (cast_heq _ _))
  | enum_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := EnumCases.head_join cs
    subst e; simp [Head.isRecordEta_of_ne (Head.join_ne_rebuild a b)] at hη
  | taggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    subst e; simp [Head.isRecordEta_of_ne (Head.join_ne_rebuild a b)] at hη
  | recTaggedUnion_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := TaggedUnionCases.head_join cs
    subst e; simp [Head.isRecordEta_of_ne (Head.join_ne_rebuild a b)] at hη
  | mutualRecursiveFamily_casesOn _ cs =>
    obtain ⟨a, b, e⟩ := FamilyMemberCases.head_join cs
    subst e; simp [Head.isRecordEta_of_ne (Head.join_ne_rebuild a b)] at hη
  | _ =>
    exfalso
    first
      | exact Bool.false_ne_true hη
      | (rw [Head.isRecordEta_of_ne (Head.join_ne_rebuild _ _)] at hη
         exact Bool.false_ne_true hη)
      | exact Bool.false_ne_true (Head.isRecordEta_ctorOf hη).2.2

/-- **The record η-redex, as `Term.eval` reads `Term.record_casesOn`**: with a body that
    `hEta` rejects, the dispatch `match r with | fields => body` would have the value of
    `r`. -/
theorem Term.record_casesOn_eval_of_isRecordEta {Γ : Ctx} {fs : LeanRecordSchema TyWf}
    {u : Usage Γ} {v : Usage (fs.toList ++ Γ)} {τ : TyWf} {kr kb : Head}
    (r : Term Sg Γ u (.record fs) kr) (body : Term Sg (fs.toList ++ Γ) v τ kb)
    (hη : Head.isRecordEta kb fs.toList.length τ = true) (env : Env Γ)
    (hr : Term.NoRecMk r) (hb : Term.NoRecMk body) :
    HEq (Term.eval G body (Env.append (cast (Ty.denRecord_eq _) (Term.eval G r env hr)) env) hb)
      (Term.eval G r env hr) :=
  (Term.eval_of_isRecordEta G body hη).2 _ env hb

/-! ## A read of a scrutinee known to be a literal -/

/-- The grade `Usage.countIdx` gives the index of a variable is that variable's grade. -/
theorem Usage.countIdx_index : ∀ {Γ : Ctx} {τ : TyWf} (u : Usage Γ) (x : Γ ∋ τ),
    u.countIdx x.index = u.count τ x
  | _ :: _, _, _, .head => rfl
  | _ :: _, _, u, .tail x => Usage.countIdx_index (Usage.tail u) x

/-- **What `hLit` asks**: a branch of grades `w` passes the check on a scrutinee that is the
    variable `x` exactly when it does not use `x` at all. -/
theorem Head.readsScrutinee_var_eq_false_iff {Γ : Ctx} {τ : TyWf} (w : Usage Γ) (x : Γ ∋ τ) :
    Head.readsScrutinee (.var x.index) w = false ↔ w.count τ x = 0 := by
  simp [Head.readsScrutinee, Usage.countIdx_index]

/-- **`Head.rebuild`, exactly**: `Head.ctorOf` gives `Head.rebuild n` precisely for at least
    two fields, not all values, that are the innermost variables in order. -/
theorem Head.ctorOf_eq_rebuild_iff (ks : List Head) (n : Nat) :
    Head.ctorOf ks = .rebuild n ↔
      Head.allValue ks = false ∧ 2 ≤ ks.length ∧ Head.isVarRun 0 ks = true ∧ ks.length = n := by
  unfold Head.ctorOf
  split
  · simp_all
  · split
    · rename_i h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      simp only [Head.rebuild.injEq]
      simp_all
    · rename_i h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h2
      simp only [reduceCtorEq, false_iff, not_and]
      intro _ h3 h4
      exact absurd h4 (by simp [h2 h3])

end LeanScript

end
