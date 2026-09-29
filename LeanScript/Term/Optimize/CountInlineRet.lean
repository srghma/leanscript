module

public import LeanScript.Term.Optimize.InlineRet
public import LeanScript.Term.Optimize.CountRename
public import LeanScript.Term.Optimize.CountRelevel

@[expose] public section

set_option autoImplicit false

/-!
# Inlining in tail position never adds calls

`Term.numCalls_inlineRet`: a call is kept, replaced by its answer (a pure expression or a
shared neutral expression, not calls), or dropped with a dead binding.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

theorem Term.numCalls_keepLvl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (r : (o' : Lvl) × Term Δ d Φ Γ τ js o')
    (hr : r.2.numCalls ≤ t.numCalls) : (t.keepLvl r).numCalls ≤ t.numCalls := by
  unfold Term.keepLvl
  split
  · rename_i h
    obtain ⟨o', t'⟩ := r
    simp only at h
    subst h
    exact hr
  · exact Nat.le_refl _

theorem Term.numCalls_substTail {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks}
    {u : Usage01ω} {ℓ : Nat} {op : Lvl} (p : PExpr Δ Φ Γ σ op) :
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (b : Term Δ d Φ (⟨σ, u, ℓ⟩ :: Γ) τ js o) →
    {r : (o' : Lvl) × Term Δ d Φ Γ τ js o'} → Term.substTail p b = some r → r.2.numCalls = 0
  | _, _, _, .ret e, r, h => by
      simp only [Term.substTail, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, .jump j e, r, h => by
      simp only [Term.substTail, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; rfl
  | _, _, _, .letV _ _ _, _, h => by simp [Term.substTail] at h
  | _, _, _, .letE _ _ _, _, h => by simp [Term.substTail] at h
  | _, _, _, .record_casesOn _ _ _, _, h => by simp [Term.substTail] at h
  | _, _, _, .branch _, _, h => by simp [Term.substTail] at h

theorem PExpr.numCalls_shareAny? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} :
    {o : Lvl} → (p : PExpr Δ Φ Γ τ o) → {r : (ℓ : Nat) × Comp Δ d Φ Γ τ ℓ} →
    p.shareAny? = some r → r.2.numCalls = 0 := by
  intro o p r h
  unfold PExpr.shareAny? at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h; rfl
  · cases h

theorem Comp.numCalls_blockCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    {js : JCtx ks} (B : BInfo Δ Φ) (c : Comp Δ d Φ Γ σ ℓ) {r : (o : Lvl) × Term Δ d Φ Γ σ js o}
    (h : c.blockCall? B = some r) : r.2.numCalls = 0 := by
  unfold Comp.blockCall? at h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨f, _, m, _, h⟩ := h
    split at h
    · rename_i h0
      rw [BlockFn.numCalls_applyNeu f m.2 h, h0]
    · cases h
  · cases h

theorem Term.numCalls_blockLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (B : BInfo Δ Φ) (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') {r : (o : Lvl) × Term Δ d Φ Γ τ js o}
    (h : Term.blockLetE B u c b = some r) : r.2.numCalls ≤ b.numCalls := by
  unfold Term.blockLetE at h
  split at h
  · rename_i hh _
    obtain ⟨hh⟩ := hh
    subst hh
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only
    rw [Comp.numCalls_blockCall? B c hr']
    exact Nat.zero_le _
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨r', hr', h⟩ := h
    rw [Term.numCalls_bindRet r'.2 b h, Comp.numCalls_blockCall? B c hr']
    omega

theorem Term.numCalls_retLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (I : RInfo Δ Φ) (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.retLetE I u c b).2.numCalls ≤ c.numCalls + b.numCalls := by
  unfold Term.retLetE
  cases hb : b.rename KRen.id URen.drop JRen.id with
  | some b' =>
      simp only
      rw [Term.numCalls_rename b hb]; omega
  | none =>
      simp only
      cases hc : c.answer? I.e with
      | none =>
          simp only
          cases hbl : Term.blockLetE I.b u c b with
          | none => exact Nat.le_refl _
          | some r =>
              have := Term.numCalls_blockLetE I.b u c b hbl
              simp only [Option.getD_some]; omega
      | some r =>
          obtain ⟨op, p⟩ := r
          simp only
          cases hs : Term.substTail p b with
          | some r =>
              simp only
              rw [Term.numCalls_substTail p b hs]; omega
          | none =>
              simp only
              cases hsh : p.shareAny? (d := d) with
              | none => exact Nat.le_refl _
              | some r =>
                  obtain ⟨ℓ', c'⟩ := r
                  simp only [Term.numCalls]
                  rw [PExpr.numCalls_shareAny? p hsh]; omega

theorem Term.numCalls_retLetV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {o o' : Lvl} (u : Usage1ω) (v : Val Δ d Φ Γ σ o)
    (b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o') :
    (Term.retLetV u v b).2.numCalls ≤ v.numCalls + b.numCalls := by
  unfold Term.retLetV
  cases hb : b.rename KRen.drop URen.id JRen.id with
  | some b' =>
      simp only
      rw [Term.numCalls_rename b hb]; omega
  | none => exact Nat.le_refl _

mutual
theorem Val.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (I : RInfo Δ Φ) → (v.retWalk I).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, I => by
      simp only [Val.retWalk, Val.numCalls]; exact Body.numCalls_retWalk b I
  | _, _, _, _, _, .thunk_mk b, I => by
      simp only [Val.retWalk, Val.numCalls]; exact Body.numCalls_retWalk b I
  | _, _, _, _, _, .lazy_mk b, I => by
      simp only [Val.retWalk, Val.numCalls]; exact Body.numCalls_retWalk b I
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (I : RInfo Δ Φ) → (b.retWalk I).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, I => by
      simp only [Body.retWalk, Body.numCalls]; exact Term.numCalls_retWalk t _
  | _, _, _, _, _, _, .opened t _, I => by
      simp only [Body.retWalk, Body.numCalls]
      exact Term.numCalls_keepLvl t _ (Term.numCalls_retWalk t _)
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (I : RInfo Δ Φ) → (c.retWalk I).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, I => by
      simp only [Comp.retWalk, Comp.numCalls]; exact Body.numCalls_retWalk s I
  | _, _, _, _, _, .array_foldl a z s _, I => by
      simp only [Comp.retWalk, Comp.numCalls]; exact Body.numCalls_retWalk s I
  | _, _, _, _, _, .data_rec b ρt us brs j e _, I => by
      simp only [Comp.retWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_retWalk (brs i) I)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, I => by
      simp only [Comp.retWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_retWalk (brs i) I)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (I : RInfo Δ Φ) →
    (t.retWalk I).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, I => by
      have hv := Val.numCalls_retWalk v I
      have hb := Term.numCalls_retWalk b (RInfo.cons u (v.retWalk I) I)
      have h := Term.numCalls_retLetV u (v.retWalk I)
        (b.retWalk (RInfo.cons u (v.retWalk I) I)).2
      simp only [Term.retWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, I => by
      have hc := Comp.numCalls_retWalk c I
      have hb := Term.numCalls_retWalk b I
      have h := Term.numCalls_retLetE I u (c.retWalk I) (b.retWalk I).2
      simp only [Term.retWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, I => by
      simp only [Term.retWalk, Term.numCalls]; exact Term.numCalls_retWalk b I
  | _, _, _, _, _, _, .branch br, I => by
      simp only [Term.retWalk, Term.numCalls]; exact Branch.numCalls_retWalk br I
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (I : RInfo Δ Φ) →
    (br.retWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, I => by
      have h₁ := Term.numCalls_retWalk t I
      have h₂ := Term.numCalls_retWalk e I
      simp only [Branch.retWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, I => by
      simp only [Branch.retWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_retWalk (bs i) I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => by
      simp only [Branch.retWalk, Branch.numCalls]; exact Branches.numCalls_retWalk bs I
  | _, _, _, _, _, _, .join σ u uₓ body main, I => by
      have h₁ := Term.numCalls_retWalk body I
      have h₂ := Branch.numCalls_retWalk main I
      simp only [Branch.retWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_retWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (I : RInfo Δ Φ) →
    (br.retWalk I).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => by
      have h₁ := Term.numCalls_retWalk b₁ I
      have h₂ := Term.numCalls_retWalk b₂ I
      simp only [Branches.retWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, I => by
      have h₁ := Term.numCalls_retWalk b I
      have h₂ := Branches.numCalls_retWalk bs I
      simp only [Branches.retWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

/-- **Inlining in tail position (and dropping dead bindings) never adds calls.** -/
theorem Term.numCalls_inlineRet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.inlineRet.numCalls ≤ t.numCalls :=
  Term.numCalls_keepLvl t _ (Term.numCalls_retWalk t _)

end LeanScript

end
