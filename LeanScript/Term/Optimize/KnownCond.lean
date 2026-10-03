module

public import LeanScript.Term.Optimize.FieldsWalk
public import LeanScript.Term.Optimize.Cond
public import LeanScript.Term.Optimize.CountDce
public import LeanScript.Term.Optimize.Atom
public import LeanScript.Term.Optimize.ShareTest

@[expose] public section

set_option autoImplicit false

/-!
# Known conditions in pure expressions

The facts of `Term.knownTestWalk` (`LeanScript.Term.Optimize.KnownTest`) and what they decide in
a pure expression.

* `BoolFact`: a boolean unknown whose value is known (in an arm of `if x`).
* `Neu.factsOf facts c b`: the facts known when the condition `c` has the value `b`, read
  through the conjunctions, disjunctions and negations that Lean's `&&`, `||` and `!` become:
  `p && q` (`p ? q : false`) true gives `p` and `q` true, `p || q` (`p ? true : q`) false gives
  `p` and `q` false, `!p` (`p ? false : true`) gives `p` the other value
  (`Neu.factsOf_holds`).  So inside `if r.c && r.e then …` both `r.c` and `r.e` are known true.
* `Neu.condSimp facts n`: a boolean unknown a fact gives is its literal, a conditional whose
  condition becomes a literal is the arm it takes, and the arms of any other conditional are
  simplified knowing its condition (`c ? c : false` is `c`, `(!c) || c` is `true`,
  `c && false` is `false`); `Neu.mkCondS` rebuilds the conditional, and a conditional whose two
  arms are written the same way is that arm (`c ? 7 : 7` is `7`) (`Neu.condSimp_eval`: the value does not
  change).  The result may have another level, and is returned with it.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Facts -/

/-- A boolean unknown whose value is known. -/
structure BoolFact (Γ : UCtx ks) where
  lv : Nat
  x : UVar Γ .bool lv
  val : Bool

namespace BoolFact

variable {Γ : UCtx ks}

/-- The fact holds in an environment. -/
def Holds (f : BoolFact Γ) (ρ : UEnv Δ Γ) : Prop := (ρ.get f.x : Bool) = f.val

/-- Under one more binder. -/
def weaken (b : UBinder ks) (f : BoolFact Γ) : BoolFact (b :: Γ) := ⟨f.lv, .tail f.x, f.val⟩

/-- Under the binders `bs`. -/
def weakenN (bs : UCtx ks) (f : BoolFact Γ) : BoolFact (bs ++ Γ) :=
  ⟨f.lv, UVar.weakenN bs f.x, f.val⟩

/-- The value of an unknown, if a fact gives it. -/
def find? : List (BoolFact Γ) → {ℓ : Nat} → UVar Γ .bool ℓ → Option Bool
  | [], _, _ => none
  | f :: fs, _, y => if f.x.index = y.index then some f.val else find? fs y

theorem map_weaken_holds {b : UBinder ks} (v : Ty.Den Δ b.ty) {ρ : UEnv Δ Γ}
    {facts : List (BoolFact Γ)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (BoolFact.weaken b), f.Holds (Tuple.cons v ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  have := h g hg
  simp only [Holds, weaken] at this ⊢
  simpa using this

theorem map_weakenN_holds (bs : UCtx ks) (vs : UEnv Δ bs) {ρ : UEnv Δ Γ}
    {facts : List (BoolFact Γ)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (BoolFact.weakenN bs), f.Holds (Tuple.append vs ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  have := h g hg
  simp only [Holds, weakenN] at this ⊢
  rw [UEnv.get_weakenN]; exact this

theorem find?_holds {ρ : UEnv Δ Γ} : (facts : List (BoolFact Γ)) → (∀ f ∈ facts, f.Holds ρ) →
    {ℓ : Nat} → (y : UVar Γ .bool ℓ) → (b : Bool) → find? facts y = some b →
    (ρ.get y : Bool) = b
  | [], _, _, _, _, hb => by simp [find?] at hb
  | f :: fs, h, _, y, b, hb => by
      simp only [find?] at hb
      split at hb
      · rename_i hi
        cases hb
        have ⟨_, hx⟩ := UVar.eq_of_index_eq (Δ := Δ) f.x y hi
        have := h f (List.mem_cons_self ..)
        simp only [Holds] at this
        rw [← this]; exact (eq_of_heq (hx ρ)).symm
      · exact find?_holds fs (fun g hg => h g (List.mem_cons_of_mem _ hg)) y b hb

end BoolFact

section CondFacts
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The neutral expression a pure expression is, if it is one. -/
def PExpr.neu? {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Option ((ℓ : Nat) × Neu Δ Φ Γ τ ℓ)
  | .neu n => some ⟨_, n⟩
  | _ => none

theorem PExpr.neu?_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o) (ℓ : Nat)
    (n : Neu Δ Φ Γ τ ℓ) (h : e.neu? = some ⟨ℓ, n⟩) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    e.eval κ ρ = n.eval κ ρ := by
  cases e with
  | neu m => simp only [PExpr.neu?, Option.some.injEq, Sigma.mk.injEq] at h
             obtain ⟨rfl, h⟩ := h; cases h; rfl
  | _ => simp [PExpr.neu?] at h

/-- The fact that a boolean unknown has the value `b` (none for an unknown of another type). -/
def BoolFact.ofVar? : {τ : Ty ks} → {ℓ : Nat} → UVar Γ τ ℓ → Bool → Option (BoolFact Γ)
  | .prim .bool, _, x, b => some ⟨_, x, b⟩
  | _, _, _, _ => none

theorem BoolFact.ofVar?_holds {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ) (b : Bool) (f : BoolFact Γ)
    (h : BoolFact.ofVar? x b = some f) (ρ : UEnv Δ Γ) (hτ : τ = .bool) (hv : ρ.get x ≍ b) :
    f.Holds ρ := by
  subst hτ
  simp only [BoolFact.ofVar?, Option.some.injEq] at h
  subst h
  exact eq_of_heq hv

mutual
/-- The facts known when the condition `c` has the value `b`, read through conjunctions,
    disjunctions and negations: `p && q` (`p ? q : false`) true gives `p` and `q` true,
    `p || q` (`p ? true : q`) false gives `p` and `q` false, `!p` (`p ? false : true`) gives
    `p` the other value, and a boolean unknown gives its value. -/
def Neu.factsOf : {τ : Ty ks} → {ℓ : Nat} → List (BoolFact Γ) → Neu Δ Φ Γ τ ℓ → Bool →
    List (BoolFact Γ)
  | _, _, facts, .var x, b => match BoolFact.ofVar? x b with
    | some f => f :: facts
    | none => facts
  | _, _, facts, .cond p q r, b =>
      if q.boolLit? = some false ∧ r.boolLit? = some true then Neu.factsOf facts p (!b)
      else if b = true ∧ r.boolLit? = some false then
        PExpr.factsOf (Neu.factsOf facts p true) q true
      else if b = false ∧ q.boolLit? = some true then
        PExpr.factsOf (Neu.factsOf facts p false) r false
      else facts
  | _, _, facts, .data_out _ _ _, _ => facts
  | _, _, facts, .extern _ _ _, _ => facts
/-- `Neu.factsOf` of a pure expression (none unless it is a neutral expression). -/
def PExpr.factsOf : {τ : Ty ks} → {o : Lvl} → List (BoolFact Γ) → PExpr Δ Φ Γ τ o → Bool →
    List (BoolFact Γ)
  | _, _, facts, .neu n, b => Neu.factsOf facts n b
  | _, _, facts, _, _ => facts
end

/-- The value of a conditional, as an `if`. -/
theorem Neu.eval_cond_ite {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (Neu.cond c a b).eval κ ρ = bif (c.eval κ ρ : Bool) then a.eval κ ρ else b.eval κ ρ := by
  simp only [Neu.eval]; split <;> rename_i h <;> rw [h] <;> rfl

mutual
theorem Neu.factsOf_holds : {τ : Ty ks} → {ℓ : Nat} → (facts : List (BoolFact Γ)) →
    (n : Neu Δ Φ Γ τ ℓ) → (b : Bool) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (∀ f ∈ facts, f.Holds ρ) → τ = .bool → n.eval κ ρ ≍ b →
    ∀ f ∈ Neu.factsOf facts n b, f.Holds ρ
  | _, _, facts, .var x, b, κ, ρ, hf, hτ, hv => by
      intro f hf'
      simp only [Neu.factsOf] at hf'
      split at hf'
      · rename_i g hg
        rcases List.mem_cons.1 hf' with rfl | hf'
        · exact BoolFact.ofVar?_holds x b _ hg ρ hτ hv
        · exact hf f hf'
      · exact hf f hf'
  | _, _, facts, .cond p q r, b, κ, ρ, hf, hτ, hv => by
      have ihp := fun fs b' hfs hv' => Neu.factsOf_holds fs p b' κ ρ hfs rfl hv'
      have ihq := fun fs b' hfs hv' => PExpr.factsOf_holds fs q b' κ ρ hfs hτ hv'
      have ihr := fun fs b' hfs hv' => PExpr.factsOf_holds fs r b' κ ρ hfs hτ hv'
      subst hτ
      replace hv := eq_of_heq hv
      simp only [Neu.factsOf]
      rw [Neu.eval_cond_ite] at hv
      split
      · rename_i hqr
        apply ihp facts (!b) hf (heq_of_eq ?_)
        simp only [PExpr.boolLit?_eval q false hqr.1, PExpr.boolLit?_eval r true hqr.2] at hv
        revert hv; cases (p.eval κ ρ : Bool) <;> cases b <;> first | rfl | (intro _; rfl) | (intro h; cases h <;> rfl)
      · split
        · rename_i _ hb
          obtain ⟨rfl, hr⟩ := hb
          have hp : (p.eval κ ρ : Bool) = true := by
            revert hv; rw [PExpr.boolLit?_eval r false hr]
            cases (p.eval κ ρ : Bool) <;> first | rfl | (intro _; rfl) | (intro h; cases h <;> rfl)
          have hq : (q.eval κ ρ : Bool) = true := by
            revert hv; rw [hp]; simp
          exact ihq _ true (ihp facts true hf (heq_of_eq hp)) (heq_of_eq hq)
        · split
          · rename_i _ _ hb
            obtain ⟨rfl, hq⟩ := hb
            have hp : (p.eval κ ρ : Bool) = false := by
              revert hv; rw [PExpr.boolLit?_eval q true hq]
              cases (p.eval κ ρ : Bool) <;> first | rfl | (intro _; rfl) | (intro h; cases h <;> rfl)
            have hr : (r.eval κ ρ : Bool) = false := by
              revert hv; rw [hp]; simp
            exact ihr _ false (ihp facts false hf (heq_of_eq hp)) (heq_of_eq hr)
          · exact hf
  | _, _, _, .data_out _ _ _, _, _, _, hf, _, _ => hf
  | _, _, _, .extern _ _ _, _, _, _, hf, _, _ => hf
  termination_by structural _ _ _ n => n
theorem PExpr.factsOf_holds : {τ : Ty ks} → {o : Lvl} → (facts : List (BoolFact Γ)) →
    (e : PExpr Δ Φ Γ τ o) → (b : Bool) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (∀ f ∈ facts, f.Holds ρ) → τ = .bool → e.eval κ ρ ≍ b →
    ∀ f ∈ PExpr.factsOf facts e b, f.Holds ρ
  | _, _, facts, .neu n, b, κ, ρ, hf, hτ, hv => Neu.factsOf_holds facts n b κ ρ hf hτ hv
  | _, _, _, .kvar _, _, _, _, hf, _, _ => hf
  | _, _, _, .lit _ _, _, _, _, hf, _, _ => hf
  | _, _, _, .enum_mk _ _, _, _, _, hf, _, _ => hf
  | _, _, _, .record_mk _, _, _, _, hf, _, _ => hf
  | _, _, _, .union_mk _ _, _, _, _, hf, _, _ => hf
  | _, _, _, .array_mk _, _, _, _, hf, _, _ => hf
  | _, _, _, .list_mk _, _, _, _, hf, _, _ => hf
  | _, _, _, .data_in _ _ _, _, _, _, hf, _, _ => hf
  termination_by structural _ _ _ e => e
end

/-- The boolean literal a fact gives to an unknown (none for an unknown of another type). -/
def BoolFact.lookup : {τ : Ty ks} → {ℓ : Nat} → List (BoolFact Γ) → UVar Γ τ ℓ →
    Option (PExpr Δ Φ Γ τ none)
  | .prim .bool, _, facts, x => (BoolFact.find? facts x).map (PExpr.lit .bool ·)
  | _, _, _, _ => none

theorem BoolFact.lookup_eval {τ : Ty ks} {ℓ : Nat} (facts : List (BoolFact Γ)) (x : UVar Γ τ ℓ)
    (e : PExpr Δ Φ Γ τ none) (h : BoolFact.lookup facts x = some e) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hf : ∀ f ∈ facts, f.Holds ρ) : e.eval κ ρ = ρ.get x := by
  unfold BoolFact.lookup at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    exact (BoolFact.find?_holds facts hf x v hv).symm
  · cases h

/-- `c ? a : b` (`Neu.mkCond`), or `a` when both arms are written the same way
    (`PExpr.same`: `c ? 7 : 7` is `7`, `c ? x : x` is `x`). -/
def Neu.mkCondS {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) : (o : Lvl) × PExpr Δ Φ Γ τ o :=
  if a.same b then ⟨_, a⟩ else ⟨_, .neu (Neu.mkCond c a b)⟩

theorem Neu.mkCondS_eval {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (Neu.mkCondS c a b).2.eval κ ρ = (Neu.cond c a b).eval κ ρ := by
  unfold Neu.mkCondS
  by_cases hs : a.same b = true
  · rw [if_pos hs]
    have hab := eq_of_heq ((PExpr.same_eval a b hs).2 κ ρ)
    rw [Neu.eval_cond_ite]
    cases (c.eval κ ρ : Bool)
    · exact hab
    · rfl
  · rw [if_neg hs]; exact Neu.mkCond_eval c a b κ ρ

mutual
/-- **Known conditions in a pure expression**: a boolean unknown that a fact gives is its
    literal, and a conditional `c ? a : b` whose condition becomes a literal is the arm it takes;
    otherwise `a` is simplified knowing that `c` holds and `b` knowing that it does not
    (`Neu.factsOf`), and the conditional is rebuilt (`Neu.mkCondS`: `c ? true : false` is `c`,
    `c ? a : a` is `a`).  Returned with its level. -/
def Neu.condSimp : {τ : Ty ks} → {ℓ : Nat} → List (BoolFact Γ) → Neu Δ Φ Γ τ ℓ →
    (o : Lvl) × PExpr Δ Φ Γ τ o
  | _, _, facts, .var x => match BoolFact.lookup facts x with
    | some e => ⟨_, e⟩
    | none => ⟨_, .neu (.var x)⟩
  | _, _, facts, .cond c a b =>
      let c' := Neu.condSimp facts c
      match c'.2.boolLit? with
      | some true => PExpr.condSimp facts a
      | some false => PExpr.condSimp facts b
      | none => match c'.2.neu? with
        | some ⟨_, n⟩ => Neu.mkCondS n (PExpr.condSimp (Neu.factsOf facts n true) a).2
            (PExpr.condSimp (Neu.factsOf facts n false) b).2
        | none => ⟨_, .neu (.cond c a b)⟩
  | _, _, _, .data_out b j e => ⟨_, .neu (.data_out b j e)⟩
  | _, _, _, .extern e args h => ⟨_, .neu (.extern e args h)⟩
/-- `Neu.condSimp` of a pure expression (only a neutral one changes). -/
def PExpr.condSimp : {τ : Ty ks} → {o : Lvl} → List (BoolFact Γ) → PExpr Δ Φ Γ τ o →
    (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | _, _, facts, .neu n => Neu.condSimp facts n
  | _, _, _, e => ⟨_, e⟩
end

mutual
theorem Neu.condSimp_eval : {τ : Ty ks} → {ℓ : Nat} → (facts : List (BoolFact Γ)) →
    (n : Neu Δ Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) →
    (n.condSimp facts).2.eval κ ρ = n.eval κ ρ
  | _, _, facts, .var x, κ, ρ, hf => by
      simp only [Neu.condSimp]
      split
      · rename_i e he
        exact BoolFact.lookup_eval facts x e he κ ρ hf
      · rfl
  | _, _, facts, .cond c a b, κ, ρ, hf => by
      have ihc := Neu.condSimp_eval facts c κ ρ hf
      have iha := PExpr.condSimp_eval facts a κ ρ hf
      have ihb := PExpr.condSimp_eval facts b κ ρ hf
      have iha' := fun fs (h : ∀ f ∈ fs, BoolFact.Holds f ρ) => PExpr.condSimp_eval fs a κ ρ h
      have ihb' := fun fs (h : ∀ f ∈ fs, BoolFact.Holds f ρ) => PExpr.condSimp_eval fs b κ ρ h
      simp only [Neu.condSimp]
      rw [Neu.eval_cond_ite]
      cases hb : (Neu.condSimp facts c).snd.boolLit? with
      | some v =>
        rw [PExpr.boolLit?_eval _ v hb κ ρ] at ihc
        cases v
        · rw [← ihc]; exact ihb
        · rw [← ihc]; exact iha
      | none =>
        dsimp only
        cases hn : (Neu.condSimp facts c).snd.neu? with
        | some p =>
          obtain ⟨_, n⟩ := p
          rw [PExpr.neu?_eval _ _ n hn κ ρ] at ihc
          dsimp only
          rw [Neu.mkCondS_eval, Neu.eval_cond_ite, ihc]
          cases hv : (c.eval κ ρ : Bool)
          · exact ihb' _ (Neu.factsOf_holds facts n false κ ρ hf rfl (heq_of_eq (ihc.trans hv)))
          · exact iha' _ (Neu.factsOf_holds facts n true κ ρ hf rfl (heq_of_eq (ihc.trans hv)))
        | none =>
          dsimp only
          exact Neu.eval_cond_ite c a b κ ρ
  | _, _, _, .data_out _ _ _, _, _, _ => rfl
  | _, _, _, .extern _ _ _, _, _, _ => rfl
  termination_by structural _ _ _ n => n
theorem PExpr.condSimp_eval : {τ : Ty ks} → {o : Lvl} → (facts : List (BoolFact Γ)) →
    (e : PExpr Δ Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) →
    (e.condSimp facts).2.eval κ ρ = e.eval κ ρ
  | _, _, facts, .neu n, κ, ρ, hf => Neu.condSimp_eval facts n κ ρ hf
  | _, _, _, .kvar _, _, _, _ => rfl
  | _, _, _, .lit _ _, _, _, _ => rfl
  | _, _, _, .enum_mk _ _, _, _, _ => rfl
  | _, _, _, .record_mk _, _, _, _ => rfl
  | _, _, _, .union_mk _ _, _, _, _ => rfl
  | _, _, _, .array_mk _, _, _, _ => rfl
  | _, _, _, .list_mk _, _, _, _ => rfl
  | _, _, _, .data_in _ _ _, _, _, _ => rfl
  termination_by structural _ _ _ e => e
end

end CondFacts

end LeanScript

end
