module

public import LeanScript.Term.Optimize
public import LeanScript.Term.RenameComp

@[expose] public section

set_option autoImplicit false

/-!
# Rewriting normal-form terms: one step

A normal-form term (`LeanScript.Term`) has no redex that `Term.eval` could compute by
itself: every elimination is stuck on an unknown.  What can still be rewritten is **dead or
redundant sharing**, the rewrites of the optimiser (`LeanScript.Term.Optimize`) and of
dead-code elimination (`LeanScript.Term.Dce`).  `Term.Step t t'` says that `t'` is obtained from
`t` by **one** of them, anywhere in `t` (in a `let`, a body of a closure, a delay or a loop, a
branch, a join point, …):

* `letV_drop`: `val k := v; b` becomes `b` when `b` does not use `k`;
* `letE_drop`: `let x := c; b` becomes `b` when `b` does not use `x`;
* `casesOn_drop`: `record_casesOn us n b` becomes `b` when `b` uses none of the fields;
* `join_drop`: `join j x := body; main` becomes `main` when `main` never jumps to `j`;
* `copy`: `let x := share y; b`, where `y` is an unknown of the level of `x`, becomes `b` with
  `x` renamed to `y` (copy propagation);
* `share_ret`, `share_jump`: `let x := share n; ret x` becomes `ret n`, and
  `let x := share n; jump j x` becomes `jump j n`, when `n` has the level of `x`.

Each rewrite keeps the type and the level index of the statement (the level is an index of
`Term`, and the rules ask for the equation that makes the two sides have the same one).

Every step preserves the value computed by `Term.eval` (`Term.Step.eval`, in this file); the
Church–Rosser property is in `LeanScript.Term.ChurchRosser`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Composing renamings -/

/-- `r₁`, then `r₂`. -/
def URen.comp {Γ₁ Γ₂ Γ₃ : UCtx ks} (r₁ : URen Γ₁ Γ₂) (r₂ : URen Γ₂ Γ₃) : URen Γ₁ Γ₃ :=
  fun x => (r₁ x).bind r₂

/-- `r₁`, then `r₂`. -/
def KRen.comp {Φ₁ Φ₂ Φ₃ : KCtx ks} (r₁ : KRen Φ₁ Φ₂) (r₂ : KRen Φ₂ Φ₃) : KRen Φ₁ Φ₃ :=
  fun x => (r₁ x).bind r₂

/-- `r₁`, then `r₂`. -/
def JRen.comp {js₁ js₂ js₃ : JCtx ks} (r₁ : JRen js₁ js₂) (r₂ : JRen js₂ js₃) : JRen js₁ js₃ :=
  fun x => (r₁ x).bind r₂

section RenFacts

theorem URen.CompOn.comp {Γ₁ Γ₂ Γ₃ : UCtx ks} (r₁ : URen Γ₁ Γ₂) (r₂ : URen Γ₂ Γ₃) :
    URen.CompOn r₁ r₂ (URen.comp r₁ r₂) := by
  intro _ _ x y h; simp [URen.comp, h]

theorem KRen.CompOn.comp {Φ₁ Φ₂ Φ₃ : KCtx ks} (r₁ : KRen Φ₁ Φ₂) (r₂ : KRen Φ₂ Φ₃) :
    KRen.CompOn r₁ r₂ (KRen.comp r₁ r₂) := by
  intro _ _ x y h; simp [KRen.comp, h]

theorem JRen.CompOn.comp {js₁ js₂ js₃ : JCtx ks} (r₁ : JRen js₁ js₂) (r₂ : JRen js₂ js₃) :
    JRen.CompOn r₁ r₂ (JRen.comp r₁ r₂) := by
  intro _ x y h; simp [JRen.comp, h]

theorem URen.CompOn.id_left {Γ₁ Γ₂ : UCtx ks} (r : URen Γ₁ Γ₂) : URen.CompOn URen.id r r := by
  intro _ _ x y h; cases h; rfl

theorem URen.CompOn.id_right {Γ₁ Γ₂ : UCtx ks} (r : URen Γ₁ Γ₂) : URen.CompOn r URen.id r := by
  intro _ _ x y h; simp [URen.id, h]

theorem KRen.CompOn.id_left {Φ₁ Φ₂ : KCtx ks} (r : KRen Φ₁ Φ₂) : KRen.CompOn KRen.id r r := by
  intro _ _ x y h; cases h; rfl

theorem KRen.CompOn.id_right {Φ₁ Φ₂ : KCtx ks} (r : KRen Φ₁ Φ₂) : KRen.CompOn r KRen.id r := by
  intro _ _ x y h; simp [KRen.id, h]

theorem JRen.CompOn.id_left {js₁ js₂ : JCtx ks} (r : JRen js₁ js₂) : JRen.CompOn JRen.id r r := by
  intro _ x y h; cases h; rfl

theorem JRen.CompOn.id_right {js₁ js₂ : JCtx ks} (r : JRen js₁ js₂) :
    JRen.CompOn r JRen.id r := by
  intro _ x y h; simp [JRen.id, h]

theorem URen.Meet.id_left {Γ₁ Γ₂ : UCtx ks} (r : URen Γ₁ Γ₂) : URen.Meet URen.id r r := by
  intro _ _ x _ h; exact h

theorem KRen.Meet.id_left {Φ₁ Φ₂ : KCtx ks} (r : KRen Φ₁ Φ₂) : KRen.Meet KRen.id r r := by
  intro _ _ x _ h; exact h

theorem JRen.Meet.id_left {js₁ js₂ : JCtx ks} (r : JRen js₁ js₂) : JRen.Meet JRen.id r r := by
  intro _ x _ h; exact h

theorem URen.CompOn.lift_drop {Γ Γ' : UCtx ks} (r : URen Γ Γ') (σ : Ty ks) (u : Usage01ω)
    (ℓ : Nat) :
    URen.CompOn (URen.lift r ⟨σ, u, ℓ⟩) URen.drop (URen.comp URen.drop r) := by
  intro _ _ x y h
  cases x with
  | head _ => simp only [URen.lift, Option.some.injEq] at h; subst h; rfl
  | tail x =>
      simp only [URen.lift, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp [URen.drop, URen.comp, hy]

theorem URen.Meet.drop_lift {Γ Γ' : UCtx ks} (r : URen Γ Γ') (σ : Ty ks) (u : Usage01ω)
    (ℓ : Nat) :
    URen.Meet URen.drop (URen.lift r ⟨σ, u, ℓ⟩) (URen.comp URen.drop r) := by
  intro _ _ x h₁ h₂
  cases x with
  | head _ => simp [URen.drop] at h₁
  | tail x => simpa [URen.lift, URen.drop, URen.comp] using h₂

theorem KRen.CompOn.lift_drop {Φ Φ' : KCtx ks} (r : KRen Φ Φ') (b : KBinder ks) :
    KRen.CompOn (KRen.lift r b) KRen.drop (KRen.comp KRen.drop r) := by
  obtain ⟨_, _, _, _⟩ := b
  intro _ _ x y h
  cases x with
  | head => simp only [KRen.lift, Option.some.injEq] at h; subst h; rfl
  | tail x =>
      simp only [KRen.lift, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp [KRen.drop, KRen.comp, hy]

theorem KRen.Meet.drop_lift {Φ Φ' : KCtx ks} (r : KRen Φ Φ') (b : KBinder ks) :
    KRen.Meet KRen.drop (KRen.lift r b) (KRen.comp KRen.drop r) := by
  obtain ⟨_, _, _, _⟩ := b
  intro _ _ x h₁ h₂
  cases x with
  | head => simp [KRen.drop] at h₁
  | tail x => simpa [KRen.lift, KRen.drop, KRen.comp] using h₂

theorem JRen.CompOn.lift_drop {js js' : JCtx ks} (r : JRen js js') (σ : Ty ks) (u : Usage1ω) :
    JRen.CompOn (JRen.lift r ⟨σ, u⟩) JRen.drop (JRen.comp JRen.drop r) := by
  intro _ x y h
  cases x with
  | head => simp only [JRen.lift, Option.some.injEq] at h; subst h; rfl
  | tail x =>
      simp only [JRen.lift, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp [JRen.drop, JRen.comp, hy]

theorem JRen.Meet.drop_lift {js js' : JCtx ks} (r : JRen js js') (σ : Ty ks) (u : Usage1ω) :
    JRen.Meet JRen.drop (JRen.lift r ⟨σ, u⟩) (JRen.comp JRen.drop r) := by
  intro _ x h₁ h₂
  cases x with
  | head => simp [JRen.drop] at h₁
  | tail x => simpa [JRen.lift, JRen.drop, JRen.comp] using h₂

theorem URen.CompOn.lift_subst {Γ Γ' : UCtx ks} (r : URen Γ Γ') {σ : Ty ks} {u : Usage01ω}
    {d : Nat} (x : UVar Γ σ d) (x' : UVar Γ' σ d) (hx : r x = some x') :
    URen.CompOn (URen.lift r ⟨σ, u, d⟩) (URen.subst x' rfl) (URen.comp (URen.subst x rfl) r) := by
  intro _ _ y z h
  cases y with
  | head _ =>
      simp only [URen.lift, Option.some.injEq] at h; subst h
      simp [URen.subst, URen.comp, hx]
  | tail y =>
      simp only [URen.lift, Option.map_eq_some_iff] at h
      obtain ⟨z, hz, rfl⟩ := h
      simp [URen.subst, URen.comp, hz]

theorem URen.Meet.subst_lift {Γ Γ' : UCtx ks} (r : URen Γ Γ') {σ : Ty ks} {u : Usage01ω}
    {d : Nat} (x : UVar Γ σ d) (x' : UVar Γ' σ d) (hx : r x = some x') :
    URen.Meet (URen.subst x rfl) (URen.lift r ⟨σ, u, d⟩) (URen.comp (URen.subst x rfl) r) := by
  intro _ _ y _ h₂
  cases y with
  | head _ => simp [URen.subst, URen.comp, hx]
  | tail y => simpa [URen.lift, URen.subst, URen.comp] using h₂

theorem URen.CompOn.liftN_dropN {Γ Γ' : UCtx ks} (r : URen Γ Γ') : (bs : UCtx ks) →
    URen.CompOn (URen.liftN r bs) (URen.dropN bs) (URen.comp (URen.dropN bs) r)
  | [] => by intro x y h; exact h.symm
  | ⟨_, _, _⟩ :: bs => by
      intro x y h
      cases x with
      | head _ =>
          simp only [URen.liftN, URen.lift, Option.some.injEq] at h; subst h; rfl
      | tail x =>
          simp only [URen.liftN, URen.lift, Option.map_eq_some_iff] at h
          obtain ⟨y, hy, rfl⟩ := h
          have := URen.CompOn.liftN_dropN r bs x y hy
          simpa [URen.dropN, URen.comp] using this

theorem URen.Meet.dropN_liftN {Γ Γ' : UCtx ks} (r : URen Γ Γ') : (bs : UCtx ks) →
    URen.Meet (URen.dropN bs) (URen.liftN r bs) (URen.comp (URen.dropN bs) r)
  | [] => by intro x _ h; simpa [URen.dropN, URen.comp, URen.liftN, URen.id] using h
  | ⟨_, _, _⟩ :: bs => by
      intro x h₁ h₂
      cases x with
      | head _ => simp [URen.dropN] at h₁
      | tail x =>
          simp only [URen.liftN, URen.lift, Option.isSome_map] at h₂
          have := URen.Meet.dropN_liftN r bs x (by simpa [URen.dropN] using h₁) h₂
          simpa [URen.dropN, URen.comp] using this

end RenFacts

/-! ## Renaming and the level casts -/

theorem Term.rename_castLvl {d : Nat} {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {js js' : JCtx ks}
    {τ : Ty ks} {o o' : Lvl} (h : o = o') (t : Term Δ d Φ Γ τ js o) (rk : KRen Φ Φ')
    (ru : URen Γ Γ') (rj : JRen js js') :
    (t.castLvl h).rename rk ru rj = (t.rename rk ru rj).map (Term.castLvl h) := by
  subst h; simp only [Term.castLvl]; cases t.rename rk ru rj <;> rfl

theorem Branch.rename_castLvl {d : Nat} {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {js js' : JCtx ks}
    {τ : Ty ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ') (br : Branch Δ d Φ Γ τ js ℓ) (rk : KRen Φ Φ')
    (ru : URen Γ Γ') (rj : JRen js js') :
    (br.castLvl h).rename rk ru rj = (br.rename rk ru rj).map (Branch.castLvl h) := by
  subst h; simp only [Branch.castLvl]; cases br.rename rk ru rj <;> rfl

/-- A successful renaming can be changed anywhere it was not defined. -/
theorem Term.rename_mono {d : Nat} {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {js js' : JCtx ks}
    {τ : Ty ks} {o : Lvl} {t : Term Δ d Φ Γ τ js o} {rk₁ rk₂ : KRen Φ Φ'} {ru₁ ru₂ : URen Γ Γ'}
    {rj₁ rj₂ : JRen js js'} {t₁ : Term Δ d Φ' Γ' τ js' o} (h : t.rename rk₁ ru₁ rj₁ = some t₁)
    (hk : ∀ {τ o} (x : KVar Φ τ o) y, rk₁ x = some y → rk₂ x = some y)
    (hu : ∀ {τ ℓ} (x : UVar Γ τ ℓ) y, ru₁ x = some y → ru₂ x = some y)
    (hj : ∀ {σ} (x : JVar js σ) y, rj₁ x = some y → rj₂ x = some y) :
    t.rename rk₂ ru₂ rj₂ = some t₁ := by
  have e₁ := Term.rename_comp (KRen.CompOn.id_right rk₁) (URen.CompOn.id_right ru₁)
    (JRen.CompOn.id_right rj₁) t h
  have e₂ := Term.rename_comp (rk₂ := KRen.id) (ru₂ := URen.id) (rj₂ := JRen.id)
    (rk₃ := rk₂) (ru₃ := ru₂) (rj₃ := rj₂)
    (fun x y hxy => (hk x y hxy).symm) (fun x y hxy => (hu x y hxy).symm)
    (fun x y hxy => (hj x y hxy).symm) t h
  rw [← e₂, e₁, h]

/-- The same, for branches. -/
theorem Branch.rename_mono {d : Nat} {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {js js' : JCtx ks}
    {τ : Ty ks} {ℓ : Nat} {t : Branch Δ d Φ Γ τ js ℓ} {rk₁ rk₂ : KRen Φ Φ'} {ru₁ ru₂ : URen Γ Γ'}
    {rj₁ rj₂ : JRen js js'} {t₁ : Branch Δ d Φ' Γ' τ js' ℓ} (h : t.rename rk₁ ru₁ rj₁ = some t₁)
    (hk : ∀ {τ o} (x : KVar Φ τ o) y, rk₁ x = some y → rk₂ x = some y)
    (hu : ∀ {τ ℓ} (x : UVar Γ τ ℓ) y, ru₁ x = some y → ru₂ x = some y)
    (hj : ∀ {σ} (x : JVar js σ) y, rj₁ x = some y → rj₂ x = some y) :
    t.rename rk₂ ru₂ rj₂ = some t₁ := by
  have e₁ := Branch.rename_comp (KRen.CompOn.id_right rk₁) (URen.CompOn.id_right ru₁)
    (JRen.CompOn.id_right rj₁) t h
  have e₂ := Branch.rename_comp (rk₂ := KRen.id) (ru₂ := URen.id) (rj₂ := JRen.id)
    (rk₃ := rk₂) (ru₃ := ru₂) (rj₃ := rj₂)
    (fun x y hxy => (hk x y hxy).symm) (fun x y hxy => (hu x y hxy).symm)
    (fun x y hxy => (hj x y hxy).symm) t h
  rw [← e₂, e₁, h]

/-! ## One step -/

mutual
/-- One rewrite inside a value (in the body of a closure or a delay). -/
inductive Val.Step : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o → Prop where
  | lam {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {u : Usage01ω} {o : Lvl}
      {b b' : Body Δ d Φ Γ [⟨σ, u, d + 1⟩] τ o} :
      Body.Step b b' → Val.Step (.lam b) (.lam b')
  | thunk_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Lvl}
      {b b' : Body Δ d Φ Γ [] τ.relax o} :
      Body.Step b b' → Val.Step (.thunk_mk b) (.thunk_mk b')
  | lazy_mk {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} {o : Lvl}
      {b b' : Body Δ d Φ Γ [] τ.relax o} :
      Body.Step b b' → Val.Step (.lazy_mk b) (.lazy_mk b')

/-- One rewrite inside a body. -/
inductive Body.Step : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o → Prop where
  | closed {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
      {t t' : Term Δ (d + 1) (KCtx.closedOnly Φ) bs τ [] o} :
      Term.Step t t' → Body.Step (Γ := Γ) (.closed t) (.closed t')
  | opened {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {m : Nat}
      {t t' : Term Δ (d + 1) Φ (bs ++ Γ) τ [] (some m)} (h : m ≤ d) :
      Term.Step t t' → Body.Step (.opened t h) (.opened t' h)

/-- One rewrite inside a computation (in the body of a loop). -/
inductive Comp.Step : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ → Prop where
  | nat_rec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage01ω}
      {on oz os : Lvl} {ℓ : Nat} (n : PExpr Δ Φ Γ .nat on) (z : PExpr Δ Φ Γ τ oz)
      {s s' : Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ os}
      (h : Lvl.meet (Lvl.meet on oz) os = some ℓ) :
      Body.Step s s' → Comp.Step (.nat_rec n z s h) (.nat_rec n z s' h)
  | array_foldl {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t ρ : Ty ks} {u₁ u₂ : Usage01ω}
      {oa oz os : Lvl} {ℓ : Nat} (a : PExpr Δ Φ Γ (.array t) oa) (z : PExpr Δ Φ Γ ρ oz)
      {s s' : Body Δ d Φ Γ [⟨t, u₁, d + 1⟩, ⟨ρ, u₂, d + 1⟩] ρ os}
      (h : Lvl.meet (Lvl.meet oa oz) os = some ℓ) :
      Body.Step s s' → Comp.Step (.array_foldl a z s h) (.array_foldl a z s' h)
  | data_rec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks)
      (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (us : Fin ((Δ.block b).k + 1) → Usage01ω)
      {os : Fin ((Δ.block b).k + 1) → Lvl} {oe : Lvl} {ℓ : Nat}
      {brs brs' : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ d Φ Γ [⟨(Δ.block b).recBody ρ i, us i, d + 1⟩] (ρ i) (os i)}
      (j : Fin ((Δ.block b).k + 1)) (e : PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe)
      (h : Lvl.meet oe (Lvl.meetFin _ os) = some ℓ) (i : Fin ((Δ.block b).k + 1)) :
      Body.Step (brs i) (brs' i) → (∀ i', i' ≠ i → brs' i' = brs i') →
      Comp.Step (.data_rec b ρ us brs j e h) (.data_rec b ρ us brs' j e h)
  | data_brec {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} (b : BRef ks)
      (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat) (us : Fin ((Δ.block b).k + 1) → Usage01ω)
      {os : Fin ((Δ.block b).k + 1) → Lvl} {oe : Lvl} {ℓ : Nat}
      {brs brs' : (i : Fin ((Δ.block b).k + 1)) →
        Body Δ d Φ Γ [⟨(Δ.block b).brecBody ρ k i, us i, d + 1⟩] (ρ i) (os i)}
      (j : Fin ((Δ.block b).k + 1)) (e : PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe)
      (h : Lvl.meet oe (Lvl.meetFin _ os) = some ℓ) (i : Fin ((Δ.block b).k + 1)) :
      Body.Step (brs i) (brs' i) → (∀ i', i' ≠ i → brs' i' = brs i') →
      Comp.Step (.data_brec b ρ k us brs j e h) (.data_brec b ρ k us brs' j e h)

/-- **One rewrite of a statement**: one of the rules at the top, or one rewrite inside. -/
inductive Term.Step : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o → Prop where
  /-- `val k := v; b` becomes `b` when `b` does not use `k`. -/
  | letV_drop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
      (u : Usage1ω) (v : Val Δ d Φ Γ σ o) {b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o'}
      {b' : Term Δ d Φ Γ τ js o'} (hb : b.rename KRen.drop URen.id JRen.id = some b')
      (ho : o' = Lvl.meet o o') :
      Term.Step (.letV u v b) (b'.castLvl ho)
  /-- `let x := c; b` becomes `b` when `b` does not use `x`. -/
  | letE_drop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
      {b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o'} {b' : Term Δ d Φ Γ τ js o'}
      (hb : b.rename KRen.id URen.drop JRen.id = some b') (ho : o' = some (Lvl.meetL ℓ o')) :
      Term.Step (.letE u c b) (b'.castLvl ho)
  /-- `let x := share y; b` becomes `b[x := y]` when `y` is an unknown of the level of `x`. -/
  | copy {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl}
      (u : Usage1ω) (x : UVar Γ σ ℓ) (hl : ℓ = d) {b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o'}
      {b' : Term Δ d Φ Γ τ js o'} (hb : b.rename KRen.id (URen.subst x hl) JRen.id = some b')
      (ho : o' = some (Lvl.meetL ℓ o')) :
      Term.Step (.letE u (.share (.var x)) b) (b'.castLvl ho)
  /-- `let x := share n; ret x` becomes `ret n` (`PExpr.substHead` recognises `x`). -/
  | share_ret {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d)
      {e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) τ o'} {e' : PExpr Δ Φ Γ τ o'}
      (he : PExpr.substHead n hl e = some e') (ho : o' = some (Lvl.meetL ℓ o')) :
      Term.Step (js := js) (.letE u (.share n) (.ret e)) ((Term.ret e').castLvl ho)
  /-- `let x := share n; jump j x` becomes `jump j n`. -/
  | share_jump {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ σ' τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o' : Lvl} (u : Usage1ω) (n : Neu Δ Φ Γ σ ℓ) (hl : ℓ = d) (j : JVar js σ')
      {e : PExpr Δ Φ (⟨σ, u, d⟩ :: Γ) σ' o'} {e' : PExpr Δ Φ Γ σ' o'}
      (he : PExpr.substHead n hl e = some e') (ho : o' = some (Lvl.meetL ℓ o')) :
      Term.Step (τ := τ) (.letE u (.share n) (.jump j e)) ((Term.jump j e').castLvl ho)
  /-- `record_casesOn us n b` becomes `b` when `b` uses none of the fields. -/
  | casesOn_drop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
      {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
      (n : Neu Δ Φ Γ (.record t fs) ℓ)
      {b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o'}
      {b' : Term Δ d Φ Γ τ js o'} (hb : b.rename KRen.id (URen.dropN _) JRen.id = some b')
      (ho : o' = some (Lvl.meetL ℓ o')) :
      Term.Step (.record_casesOn us n b) (b'.castLvl ho)
  | letV_val {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
      (u : Usage1ω) {v v' : Val Δ d Φ Γ σ o} (b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o') :
      Val.Step v v' → Term.Step (.letV u v b) (.letV u v' b)
  | letV_body {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
      (u : Usage1ω) (v : Val Δ d Φ Γ σ o) {b b' : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o'} :
      Term.Step b b' → Term.Step (.letV u v b) (.letV u v b')
  | letE_comp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o' : Lvl} (u : Usage1ω) {c c' : Comp Δ d Φ Γ σ ℓ} (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') :
      Comp.Step c c' → Term.Step (.letE u c b) (.letE u c' b)
  | letE_body {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ) {b b' : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o'} :
      Term.Step b b' → Term.Step (.letE u c b) (.letE u c b')
  | casesOn_body {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
      {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
      (n : Neu Δ Φ Γ (.record t fs) ℓ)
      {b b' : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o'} :
      Term.Step b b' → Term.Step (.record_casesOn us n b) (.record_casesOn us n b')
  | branch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {br br' : Branch Δ d Φ Γ τ js ℓ} :
      Branch.Step br br' → Term.Step (.branch br) (.branch br')

/-- One rewrite of a branch. -/
inductive Branch.Step : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ → Prop where
  /-- `join j x := body; main` becomes `main` when `main` never jumps to `j`. -/
  | join_drop {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
      {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
      {main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ} {main' : Branch Δ d Φ Γ τ js ℓ}
      (hm : main.rename KRen.id URen.id JRen.drop = some main') (ho : ℓ = Lvl.meetL ℓ o) :
      Branch.Step (.join σ u uₓ body main) (main'.castLvl ho)
  | ite_then {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) {t t' : Term Δ d Φ Γ τ js o₁}
      (e : Term Δ d Φ Γ τ js o₂) :
      Term.Step t t' → Branch.Step (.ite c t e) (.ite c t' e)
  | ite_else {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
      {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
      {e e' : Term Δ d Φ Γ τ js o₂} :
      Term.Step e e' → Branch.Step (.ite c t e) (.ite c t e')
  | enum_casesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {s : LeanEnumSchema} {τ : Ty ks}
      {js : JCtx ks} {ℓ : Nat} {os : Fin s.nOfConstructors → Lvl} (e : Neu Δ Φ Γ (.enum s) ℓ)
      {bs bs' : (i : Fin s.nOfConstructors) → Term Δ d Φ Γ τ js (os i)} (i : Fin s.nOfConstructors) :
      Term.Step (bs i) (bs' i) → (∀ i', i' ≠ i → bs' i' = bs i') →
      Branch.Step (.enum_casesOn e bs) (.enum_casesOn e bs')
  | union_casesOn {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
      {h : UnionShape bs} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o : Lvl}
      (e : Neu Δ Φ Γ (.union cs (h := h)) ℓ) {brs brs' : Branches Δ d Φ Γ cs τ js o} :
      Branches.Step brs brs' → Branch.Step (.union_casesOn e brs) (.union_casesOn e brs')
  | join_body {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
      {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω)
      {body body' : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o} (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
      Term.Step body body' → Branch.Step (.join σ u uₓ body main) (.join σ u uₓ body' main)
  | join_main {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
      {ℓ : Nat} (σ : Ty ks) (u : Usage1ω) (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
      {main main' : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ} :
      Branch.Step main main' → Branch.Step (.join σ u uₓ body main) (.join σ u uₓ body main')

/-- One rewrite in the branches of a union's case analysis. -/
inductive Branches.Step : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o → Prop where
  | two_left {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a b : Bool} {c₁ : Ctor ks a} {c₂ : Ctor ks b}
      {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us₁ us₂ : List Usage01ω)
      {b₁ b₁' : Term Δ d Φ (UCtx.annot d c₁.binds us₁ ++ Γ) τ js o₁}
      (b₂ : Term Δ d Φ (UCtx.annot d c₂.binds us₂ ++ Γ) τ js o₂) :
      Term.Step b₁ b₁' → Branches.Step (.two us₁ us₂ b₁ b₂) (.two us₁ us₂ b₁' b₂)
  | two_right {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a b : Bool} {c₁ : Ctor ks a} {c₂ : Ctor ks b}
      {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us₁ us₂ : List Usage01ω)
      (b₁ : Term Δ d Φ (UCtx.annot d c₁.binds us₁ ++ Γ) τ js o₁)
      {b₂ b₂' : Term Δ d Φ (UCtx.annot d c₂.binds us₂ ++ Γ) τ js o₂} :
      Term.Step b₂ b₂' → Branches.Step (.two us₁ us₂ b₁ b₂) (.two us₁ us₂ b₁ b₂')
  | cons_head {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {bs : List Bool} {c : Ctor ks a}
      {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us : List Usage01ω)
      {b b' : Term Δ d Φ (UCtx.annot d c.binds us ++ Γ) τ js o₁}
      (brs : Branches Δ d Φ Γ cs τ js o₂) :
      Term.Step b b' → Branches.Step (.cons us b brs) (.cons us b' brs)
  | cons_tail {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {a : Bool} {bs : List Bool} {c : Ctor ks a}
      {cs : Ctors ks bs} {τ : Ty ks} {js : JCtx ks} {o₁ o₂ : Lvl} (us : List Usage01ω)
      (b : Term Δ d Φ (UCtx.annot d c.binds us ++ Γ) τ js o₁)
      {brs brs' : Branches Δ d Φ Γ cs τ js o₂} :
      Branches.Step brs brs' → Branches.Step (.cons us b brs) (.cons us b brs')
end

/-! ## Every step preserves the value -/

mutual
theorem Val.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    {v v' : Val Δ d Φ Γ τ o} → Val.Step v v' → ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ),
    v'.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, _, _, .lam h, κ, ρ => by
      simp only [Val.eval]; funext x; exact Body.Step.eval h κ ρ _
  | _, _, _, _, _, _, _, .thunk_mk h, κ, ρ => by
      simp only [Val.eval]; rw [Body.Step.eval h κ ρ]
  | _, _, _, _, _, _, _, .lazy_mk h, κ, ρ => by
      simp only [Val.eval]; rw [Body.Step.eval h κ ρ]
  termination_by structural _ _ _ _ _ _ _ x _ _ => x
theorem Body.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → {b b' : Body Δ d Φ Γ bs τ o} → Body.Step b b' →
    ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (vs : UEnv Δ bs), b'.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, _, _, .closed h, κ, ρ, vs => by
      simp only [Body.eval]; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, .opened _ h, κ, ρ, vs => by
      simp only [Body.eval]; exact Term.Step.eval h _ _ _
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Comp.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    {c c' : Comp Δ d Φ Γ τ ℓ} → Comp.Step c c' → ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ),
    c'.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, _, _, .nat_rec _ _ _ h, κ, ρ => by
      simp only [Comp.eval]
      congr 1; funext k acc; exact Body.Step.eval h κ ρ _
  | _, _, _, _, _, _, _, .array_foldl _ _ _ h, κ, ρ => by
      simp only [Comp.eval]
      congr 1; funext acc x; exact Body.Step.eval h κ ρ _
  | _, _, _, _, _, _, _, .data_rec (brs := brs) (brs' := brs') _ _ _ _ _ _ i h hs, κ, ρ => by
      have ih := fun x => Body.Step.eval h κ ρ (Tuple.cons x Tuple.nil)
      simp only [Comp.eval]
      congr 1; funext i' x
      by_cases hi : i' = i
      · subst hi; exact ih x
      · rw [hs i' hi]
  | _, _, _, _, _, _, _, .data_brec (brs := brs) (brs' := brs') _ _ _ _ _ _ _ i h hs, κ, ρ => by
      have ih := fun x => Body.Step.eval h κ ρ (Tuple.cons x Tuple.nil)
      simp only [Comp.eval]
      congr 1; funext i' x
      by_cases hi : i' = i
      · subst hi; exact ih x
      · rw [hs i' hi]
  termination_by structural _ _ _ _ _ _ _ x _ _ => x
theorem Term.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {t t' : Term Δ d Φ Γ τ js o} → Term.Step t t' →
    ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js), t'.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, .letV_drop _ v hb _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval]
      exact Term.rename_eval (KRen.Agree.drop _ κ) (URen.Agree.id ρ) (JRen.Agree.id jκ) _ hb
  | _, _, _, _, _, _, _, _, .letE_drop _ c hb _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval]
      exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.drop _ ρ) (JRen.Agree.id jκ) _ hb
  | _, _, _, _, _, _, _, _, .copy _ x hl hb _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval, Comp.eval, Neu.eval]
      exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.subst x hl ρ) (JRen.Agree.id jκ) _ hb
  | _, _, _, _, _, _, _, _, .share_ret _ n hl he _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval, Comp.eval]
      exact PExpr.substHead_eval n hl _ he κ ρ
  | _, _, _, _, _, _, _, _, .share_jump _ n hl _ he _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval, Comp.eval]
      rw [PExpr.substHead_eval n hl _ he κ ρ]
  | _, _, _, _, _, _, _, _, .casesOn_drop _ _ hb _, κ, ρ, jκ => by
      rw [Term.eval_castLvl]
      simp only [Term.eval]
      exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.dropN ρ _ _) (JRen.Agree.id jκ) _ hb
  | _, _, _, _, _, _, _, _, .letV_val _ _ h, κ, ρ, jκ => by
      simp only [Term.eval, Val.Step.eval h κ ρ]
  | _, _, _, _, _, _, _, _, .letV_body _ _ h, κ, ρ, jκ => by
      simp only [Term.eval]; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, .letE_comp _ _ h, κ, ρ, jκ => by
      simp only [Term.eval, Comp.Step.eval h κ ρ]
  | _, _, _, _, _, _, _, _, .letE_body _ _ h, κ, ρ, jκ => by
      simp only [Term.eval]; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, .casesOn_body _ _ h, κ, ρ, jκ => by
      simp only [Term.eval]; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, .branch h, κ, ρ, jκ => by
      simp only [Term.eval]; exact Branch.Step.eval h _ _ _
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Branch.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {b b' : Branch Δ d Φ Γ τ js ℓ} → Branch.Step b b' →
    ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js), b'.eval κ ρ jκ = b.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, .join_drop _ _ _ _ hm _, κ, ρ, jκ => by
      rw [Branch.eval_castLvl]
      simp only [Branch.eval]
      exact Branch.rename_eval (KRen.Agree.id κ) (URen.Agree.id ρ) (JRen.Agree.drop _ jκ) _ hm
  | _, _, _, _, _, _, _, _, .ite_then _ _ h, κ, ρ, jκ => by
      simp only [Branch.eval, Term.Step.eval h κ ρ jκ]
  | _, _, _, _, _, _, _, _, .ite_else _ _ h, κ, ρ, jκ => by
      simp only [Branch.eval, Term.Step.eval h κ ρ jκ]
  | _, _, _, _, _, _, _, _, .enum_casesOn (bs := bs) (bs' := bs') e i h hs, κ, ρ, jκ => by
      have ih := Term.Step.eval h κ ρ jκ
      simp only [Branch.eval]
      generalize e.eval κ ρ = i'
      by_cases hi : i' = i
      · subst hi; exact ih
      · rw [hs i' hi]
  | _, _, _, _, _, _, _, _, .union_casesOn _ h, κ, ρ, jκ => by
      simp only [Branch.eval]; exact Branches.Step.eval h κ ρ jκ _
  | _, _, _, _, _, _, _, _, .join_body _ _ _ _ h, κ, ρ, jκ => by
      simp only [Branch.eval]
      have hf : (fun v => Term.eval _ κ (Tuple.cons v ρ) jκ) = _ :=
        funext fun v => Term.Step.eval h κ (Tuple.cons v ρ) jκ
      rw [hf]
  | _, _, _, _, _, _, _, _, .join_main _ _ _ _ h, κ, ρ, jκ => by
      simp only [Branch.eval]; exact Branch.Step.eval h _ _ _
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Branches.Step.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    {b b' : Branches Δ d Φ Γ cs τ js o} → Branches.Step b b' →
    ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) x, b'.eval κ ρ jκ x = b.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, _, _, .two_left _ _ _ h, κ, ρ, jκ, x => by
      simp only [Branches.eval]
      congr 1; funext v; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, _, _, .two_right _ _ _ h, κ, ρ, jκ, x => by
      simp only [Branches.eval]
      congr 1; funext v; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, _, _, .cons_head _ _ h, κ, ρ, jκ, x => by
      simp only [Branches.eval]
      congr 1; funext v; exact Term.Step.eval h _ _ _
  | _, _, _, _, _, _, _, _, _, _, .cons_tail _ _ h, κ, ρ, jκ, x => by
      simp only [Branches.eval]
      congr 1; funext r; exact Branches.Step.eval h _ _ _ _
  termination_by structural _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

end LeanScript

end
