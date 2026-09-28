module

public import LeanScript.Term.Rename.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Composing renamings

Two facts about `Term.rename` (and the renamings of every other layer), used by the
rewriting theory of `LeanScript.Term.Rewrite.Step`:

* **composition** (`Term.rename_comp`): if `t.rename r₁ = some t₁`, then renaming `t₁` along
  `r₂` is renaming `t` along any `r₃` that agrees with "`r₁` then `r₂`" wherever `r₁` is
  defined (`URen.CompOn`, …);
* **meets** (`Term.rename_meet`): if renaming `t` succeeds along `r₁` and along `r₂`, it
  succeeds along any `r₃` that is defined wherever both are (`URen.Meet`, …).  A renaming
  succeeds exactly when it is defined on every variable the term uses.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Conditions on renamings -/

/-- `r₃` is "`r₁` then `r₂`" wherever `r₁` is defined. -/
def URen.CompOn {Γ₁ Γ₂ Γ₃ : UCtx ks} (r₁ : URen Γ₁ Γ₂) (r₂ : URen Γ₂ Γ₃) (r₃ : URen Γ₁ Γ₃) :
    Prop :=
  ∀ {τ : Ty ks} {ℓ : Nat} (x : UVar Γ₁ τ ℓ) (y : UVar Γ₂ τ ℓ), r₁ x = some y → r₂ y = r₃ x

/-- `r₃` is "`r₁` then `r₂`" wherever `r₁` is defined. -/
def KRen.CompOn {Φ₁ Φ₂ Φ₃ : KCtx ks} (r₁ : KRen Φ₁ Φ₂) (r₂ : KRen Φ₂ Φ₃) (r₃ : KRen Φ₁ Φ₃) :
    Prop :=
  ∀ {τ : Ty ks} {o : Lvl} (x : KVar Φ₁ τ o) (y : KVar Φ₂ τ o), r₁ x = some y → r₂ y = r₃ x

/-- `r₃` is "`r₁` then `r₂`" wherever `r₁` is defined. -/
def JRen.CompOn {js₁ js₂ js₃ : JCtx ks} (r₁ : JRen js₁ js₂) (r₂ : JRen js₂ js₃)
    (r₃ : JRen js₁ js₃) : Prop :=
  ∀ {σ : Ty ks} (x : JVar js₁ σ) (y : JVar js₂ σ), r₁ x = some y → r₂ y = r₃ x

/-- `r₃` is defined wherever `r₁` and `r₂` both are. -/
def URen.Meet {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} (r₁ : URen Γ Γ₁) (r₂ : URen Γ Γ₂) (r₃ : URen Γ Γ₃) :
    Prop :=
  ∀ {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ), (r₁ x).isSome → (r₂ x).isSome → (r₃ x).isSome

/-- `r₃` is defined wherever `r₁` and `r₂` both are. -/
def KRen.Meet {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} (r₁ : KRen Φ Φ₁) (r₂ : KRen Φ Φ₂) (r₃ : KRen Φ Φ₃) :
    Prop :=
  ∀ {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o), (r₁ x).isSome → (r₂ x).isSome → (r₃ x).isSome

/-- `r₃` is defined wherever `r₁` and `r₂` both are. -/
def JRen.Meet {js js₁ js₂ js₃ : JCtx ks} (r₁ : JRen js js₁) (r₂ : JRen js js₂)
    (r₃ : JRen js js₃) : Prop :=
  ∀ {σ : Ty ks} (x : JVar js σ), (r₁ x).isSome → (r₂ x).isSome → (r₃ x).isSome

section Conditions

theorem URen.CompOn.lift {Γ₁ Γ₂ Γ₃ : UCtx ks} {r₁ : URen Γ₁ Γ₂} {r₂ : URen Γ₂ Γ₃}
    {r₃ : URen Γ₁ Γ₃} (h : URen.CompOn r₁ r₂ r₃) (b : UBinder ks) :
    URen.CompOn (URen.lift r₁ b) (URen.lift r₂ b) (URen.lift r₃ b) := by
  obtain ⟨_, _, _⟩ := b
  intro _ _ x y hxy
  cases x with
  | head _ => simp only [URen.lift, Option.some.injEq] at hxy; subst hxy; rfl
  | tail x =>
      simp only [URen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [URen.lift, h x y hy]

theorem URen.CompOn.liftN {Γ₁ Γ₂ Γ₃ : UCtx ks} {r₁ : URen Γ₁ Γ₂} {r₂ : URen Γ₂ Γ₃}
    {r₃ : URen Γ₁ Γ₃} (h : URen.CompOn r₁ r₂ r₃) : (bs : UCtx ks) →
    URen.CompOn (URen.liftN r₁ bs) (URen.liftN r₂ bs) (URen.liftN r₃ bs)
  | [] => h
  | b :: bs => URen.CompOn.lift (URen.CompOn.liftN h bs) b

theorem KRen.CompOn.lift {Φ₁ Φ₂ Φ₃ : KCtx ks} {r₁ : KRen Φ₁ Φ₂} {r₂ : KRen Φ₂ Φ₃}
    {r₃ : KRen Φ₁ Φ₃} (h : KRen.CompOn r₁ r₂ r₃) (b : KBinder ks) :
    KRen.CompOn (KRen.lift r₁ b) (KRen.lift r₂ b) (KRen.lift r₃ b) := by
  obtain ⟨_, _, _, _⟩ := b
  intro _ _ x y hxy
  cases x with
  | head => simp only [KRen.lift, Option.some.injEq] at hxy; subst hxy; rfl
  | tail x =>
      simp only [KRen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [KRen.lift, h x y hy]

theorem KRen.CompOn.closedOnly {Φ₁ Φ₂ Φ₃ : KCtx ks} {r₁ : KRen Φ₁ Φ₂} {r₂ : KRen Φ₂ Φ₃}
    {r₃ : KRen Φ₁ Φ₃} (h : KRen.CompOn r₁ r₂ r₃) :
    KRen.CompOn (KRen.closedOnly r₁) (KRen.closedOnly r₂) (KRen.closedOnly r₃) := by
  intro _ _ x z hxz
  simp only [KRen.closedOnly, Option.bind_eq_some_iff] at hxz
  obtain ⟨y, hy, hz⟩ := hxz
  simp only [KRen.closedOnly, KVar.mask_unmask y hz, h _ y hy]

theorem JRen.CompOn.lift {js₁ js₂ js₃ : JCtx ks} {r₁ : JRen js₁ js₂} {r₂ : JRen js₂ js₃}
    {r₃ : JRen js₁ js₃} (h : JRen.CompOn r₁ r₂ r₃) (b : JBinder ks) :
    JRen.CompOn (JRen.lift r₁ b) (JRen.lift r₂ b) (JRen.lift r₃ b) := by
  obtain ⟨_, _⟩ := b
  intro _ x y hxy
  cases x with
  | head => simp only [JRen.lift, Option.some.injEq] at hxy; subst hxy; rfl
  | tail x =>
      simp only [JRen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [JRen.lift, h x y hy]

theorem URen.CompOn.id {Γ : UCtx ks} : URen.CompOn (URen.id (Γ := Γ)) URen.id URen.id := by
  intro _ _ x y h; cases h; rfl

theorem JRen.CompOn.nil : JRen.CompOn (ks := ks) JRen.nil JRen.nil JRen.nil := by
  intro _ x; exact nomatch x

theorem URen.Meet.lift {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} {r₁ : URen Γ Γ₁} {r₂ : URen Γ Γ₂}
    {r₃ : URen Γ Γ₃} (h : URen.Meet r₁ r₂ r₃) (b : UBinder ks) :
    URen.Meet (URen.lift r₁ b) (URen.lift r₂ b) (URen.lift r₃ b) := by
  obtain ⟨_, _, _⟩ := b
  intro _ _ x h₁ h₂
  cases x with
  | head _ => rfl
  | tail x =>
      simp only [URen.lift, Option.isSome_map] at h₁ h₂ ⊢
      exact h x h₁ h₂

theorem URen.Meet.liftN {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} {r₁ : URen Γ Γ₁} {r₂ : URen Γ Γ₂}
    {r₃ : URen Γ Γ₃} (h : URen.Meet r₁ r₂ r₃) : (bs : UCtx ks) →
    URen.Meet (URen.liftN r₁ bs) (URen.liftN r₂ bs) (URen.liftN r₃ bs)
  | [] => h
  | b :: bs => URen.Meet.lift (URen.Meet.liftN h bs) b

theorem KRen.Meet.lift {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} {r₁ : KRen Φ Φ₁} {r₂ : KRen Φ Φ₂}
    {r₃ : KRen Φ Φ₃} (h : KRen.Meet r₁ r₂ r₃) (b : KBinder ks) :
    KRen.Meet (KRen.lift r₁ b) (KRen.lift r₂ b) (KRen.lift r₃ b) := by
  obtain ⟨_, _, _, _⟩ := b
  intro _ _ x h₁ h₂
  cases x with
  | head => rfl
  | tail x =>
      simp only [KRen.lift, Option.isSome_map] at h₁ h₂ ⊢
      exact h x h₁ h₂

/-- Whether a known variable can be seen from a closed body depends only on its level. -/
theorem KVar.mask_isSome : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} → (y : KVar Φ τ o) →
    (y.mask).isSome = o.isNone
  | ⟨_, _, some _, _⟩ :: _, _, _, .head => rfl
  | ⟨_, _, some _, _⟩ :: _, _, _, .tail y => by
      simp only [KVar.mask]; rw [← KVar.mask_isSome y]; cases y.mask <;> rfl
  | ⟨_, _, none, _⟩ :: _, _, _, .head => rfl
  | ⟨_, _, none, _⟩ :: _, _, _, .tail y => by
      simp only [KVar.mask]; rw [← KVar.mask_isSome y]; cases y.mask <;> rfl

theorem KRen.Meet.closedOnly {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} {r₁ : KRen Φ Φ₁} {r₂ : KRen Φ Φ₂}
    {r₃ : KRen Φ Φ₃} (h : KRen.Meet r₁ r₂ r₃) :
    KRen.Meet (KRen.closedOnly r₁) (KRen.closedOnly r₂) (KRen.closedOnly r₃) := by
  intro _ _ x h₁ h₂
  simp only [KRen.closedOnly] at h₁ h₂ ⊢
  cases hy₁ : r₁ x.unmask with
  | none => simp [hy₁] at h₁
  | some y₁ =>
      cases hy₂ : r₂ x.unmask with
      | none => simp [hy₂] at h₂
      | some y₂ =>
          have h₃ := h x.unmask (by simp [hy₁]) (by simp [hy₂])
          cases hy₃ : r₃ x.unmask with
          | none => simp [hy₃] at h₃
          | some y₃ =>
              simp only [hy₁, Option.bind_some] at h₁
              simp only [Option.bind_some]
              rw [KVar.mask_isSome] at h₁ ⊢
              exact h₁

theorem JRen.Meet.lift {js js₁ js₂ js₃ : JCtx ks} {r₁ : JRen js js₁} {r₂ : JRen js js₂}
    {r₃ : JRen js js₃} (h : JRen.Meet r₁ r₂ r₃) (b : JBinder ks) :
    JRen.Meet (JRen.lift r₁ b) (JRen.lift r₂ b) (JRen.lift r₃ b) := by
  obtain ⟨_, _⟩ := b
  intro _ x h₁ h₂
  cases x with
  | head => rfl
  | tail x =>
      simp only [JRen.lift, Option.isSome_map] at h₁ h₂ ⊢
      exact h x h₁ h₂

theorem URen.Meet.id {Γ : UCtx ks} : URen.Meet (URen.id (Γ := Γ)) URen.id URen.id := by
  intro _ _ x _ _; rfl

theorem JRen.Meet.nil : JRen.Meet (ks := ks) JRen.nil JRen.nil JRen.nil := by
  intro _ x; exact nomatch x

end Conditions

/-! ## `Fin.optAll` -/

theorem Fin.optAll_of_eq_some {n : Nat} {β : Fin n → Type} {f : (i : Fin n) → Option (β i)}
    {g : (i : Fin n) → β i} (h : ∀ i, f i = some (g i)) : Fin.optAll f = some g := by
  unfold Fin.optAll
  have hs : ∀ i, (f i).isSome = true := fun i => by simp [h i]
  rw [dite_eq_left_of_eq_true (eq_true hs)]
  congr 1
  funext i
  simp [h i]

theorem Fin.optAll_isSome {n : Nat} {β : Fin n → Type} {f : (i : Fin n) → Option (β i)}
    (h : ∀ i, (f i).isSome = true) : (Fin.optAll f).isSome = true := by
  unfold Fin.optAll
  rw [dite_eq_left_of_eq_true (eq_true h)]; rfl

/-! ## Composition, layer 1 -/

section Layer1
variable {Φ Φ₁ Φ₂ : KCtx ks} {Γ Γ₁ Γ₂ : UCtx ks}
  {rk₁ : KRen Φ Φ₁} {ru₁ : URen Γ Γ₁} {rk₂ : KRen Φ₁ Φ₂} {ru₂ : URen Γ₁ Γ₂}
  {rk₃ : KRen Φ Φ₂} {ru₃ : URen Γ Γ₂}

mutual
theorem Neu.rename_comp (hk : KRen.CompOn rk₁ rk₂ rk₃) (hu : URen.CompOn ru₁ ru₂ ru₃) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → {n₁ : Neu Δ Φ₁ Γ₁ τ ℓ} →
    n.rename rk₁ ru₁ = some n₁ → n₁.rename rk₂ ru₂ = n.rename rk₃ ru₃
  | _, _, .var x, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp only [Neu.rename, hu x y hy]
  | _, _, .data_out b j n, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [Neu.rename, Neu.rename_comp hk hu n hm]
  | _, _, .cond c a b, _, h => by
      simp only [Neu.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      simp only [Neu.rename, Neu.rename_comp hk hu c hc, PExpr.rename_comp hk hu a ha,
        PExpr.rename_comp hk hu b hb]
  | _, _, .extern e args _, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Neu.rename, Args.rename_comp hk hu args has]
theorem PExpr.rename_comp (hk : KRen.CompOn rk₁ rk₂ rk₃) (hu : URen.CompOn ru₁ ru₂ ru₃) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → {e₁ : PExpr Δ Φ₁ Γ₁ τ o} →
    e.rename rk₁ ru₁ = some e₁ → e₁.rename rk₂ ru₂ = e.rename rk₃ ru₃
  | _, _, .neu n, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [PExpr.rename, Neu.rename_comp hk hu n hm]
  | _, _, .kvar k, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      simp only [PExpr.rename, hk k y hy]
  | _, _, .lit _ _, _, h => by
      simp only [PExpr.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .enum_mk _ _, _, h => by
      simp only [PExpr.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .record_mk args, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.rename, Args.rename_comp hk hu args has]
  | _, _, .union_mk ix args, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.rename, Args.rename_comp hk hu args has]
  | _, _, .array_mk es, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.rename, Elems.rename_comp hk hu es hes]
  | _, _, .list_mk es, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.rename, Elems.rename_comp hk hu es hes]
  | _, _, .data_in b j e, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.rename, PExpr.rename_comp hk hu e he]
theorem Args.rename_comp (hk : KRen.CompOn rk₁ rk₂ rk₃) (hu : URen.CompOn ru₁ ru₂ ru₃) :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) → {as₁ : Args Δ Φ₁ Γ₁ σs o} →
    as.rename rk₁ ru₁ = some as₁ → as₁.rename rk₂ ru₂ = as.rename rk₃ ru₃
  | _, _, .nil, _, h => by
      simp only [Args.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons a as, _, h => by
      simp only [Args.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, as', has, rfl⟩ := h
      simp only [Args.rename, PExpr.rename_comp hk hu a ha, Args.rename_comp hk hu as has]
theorem Elems.rename_comp (hk : KRen.CompOn rk₁ rk₂ rk₃) (hu : URen.CompOn ru₁ ru₂ ru₃) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → {es₁ : Elems Δ Φ₁ Γ₁ t o} →
    es.rename rk₁ ru₁ = some es₁ → es₁.rename rk₂ ru₂ = es.rename rk₃ ru₃
  | _, _, .nil, _, h => by
      simp only [Elems.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Elems.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, es', hes, rfl⟩ := h
      simp only [Elems.rename, PExpr.rename_comp hk hu e he, Elems.rename_comp hk hu es hes]
end

end Layer1

/-! ## Composition, layer 2 -/

mutual
theorem Val.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → {v₁ : Val Δ d Φ₁ Γ₁ τ o} → v.rename rk₁ ru₁ = some v₁ →
    v₁.rename rk₂ ru₂ = v.rename rk₃ ru₃
  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lam b, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Body.rename_comp hk hu b hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .thunk_mk b, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Body.rename_comp hk hu b hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lazy_mk b, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Body.rename_comp hk hu b hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .record_mk args, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Args.rename_comp hk hu args hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .union_mk ix args, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Args.rename_comp hk hu args hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .array_mk es, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Elems.rename_comp hk hu es hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .list_mk es, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, Elems.rename_comp hk hu es hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_in b j e, _, h => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Val.rename, PExpr.rename_comp hk hu e hx]

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (b : Body Δ d Φ Γ bs τ o) → {b₁ : Body Δ d Φ₁ Γ₁ bs τ o} → b.rename rk₁ ru₁ = some b₁ →
    b₁.rename rk₂ ru₂ = b.rename rk₃ ru₃
  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, _, .closed t, _, h => by
      simp only [Body.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Body.rename, Term.rename_comp hk.closedOnly URen.CompOn.id JRen.CompOn.nil t hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, bs, _, _, .opened t _, _, h => by
      simp only [Body.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Body.rename, Term.rename_comp hk (hu.liftN bs) JRen.CompOn.nil t hx]

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Comp.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ d Φ Γ τ ℓ) → {c₁ : Comp Δ d Φ₁ Γ₁ τ ℓ} → c.rename rk₁ ru₁ = some c₁ →
    c₁.rename rk₂ ru₂ = c.rename rk₃ ru₃
  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .app f a _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨f', hf, a', ha, rfl⟩ := h
      simp only [Comp.rename, PExpr.rename_comp hk hu f hf, PExpr.rename_comp hk hu a ha]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .share n, _, h => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Comp.rename, Neu.rename_comp hk hu n hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .nat_rec n z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs, rfl⟩ := h
      simp only [Comp.rename, PExpr.rename_comp hk hu n hn, PExpr.rename_comp hk hu z hz,
        Body.rename_comp hk hu s hs]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .array_foldl n z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs, rfl⟩ := h
      simp only [Comp.rename, PExpr.rename_comp hk hu n hn, PExpr.rename_comp hk hu z hz,
        Body.rename_comp hk hu s hs]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, rfl⟩ := h
      have hf : (fun i => (brs' i).rename rk₂ ru₂) = (fun i => (brs i).rename rk₃ ru₃) :=
        funext fun i => Body.rename_comp hk hu (brs i) (Fin.optAll_eq_some hbrs i)
      simp only [Comp.rename, PExpr.rename_comp hk hu e he, hf]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, rfl⟩ := h
      have hf : (fun i => (brs' i).rename rk₂ ru₂) = (fun i => (brs i).rename rk₃ ru₃) :=
        funext fun i => Body.rename_comp hk hu (brs i) (Fin.optAll_eq_some hbrs i)
      simp only [Comp.rename, PExpr.rename_comp hk hu e he, hf]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .thunk_force e, _, h => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Comp.rename, PExpr.rename_comp hk hu e hx]

  | _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lazy_force e, _, h => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Comp.rename, PExpr.rename_comp hk hu e hx]

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Term.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} → {js js₁ js₂ : JCtx ks} →
    {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} → {rj₂ : JRen js₁ js₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} → {rj₃ : JRen js js₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → JRen.CompOn rj₁ rj₂ rj₃ → {o : Lvl} →
    (t : Term Δ d Φ Γ τ js o) → {t₁ : Term Δ d Φ₁ Γ₁ τ js₁ o} → t.rename rk₁ ru₁ rj₁ = some t₁ →
    t₁.rename rk₂ ru₂ rj₂ = t.rename rk₃ ru₃ rj₃
  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .ret e, _, h => by
      simp only [Term.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Term.rename, PExpr.rename_comp hk hu e hx]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .letV u v b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.rename, Val.rename_comp hk hu v hv, Term.rename_comp (hk.lift _) hu hj b hb]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .letE u c b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.rename, Comp.rename_comp hk hu c hc, Term.rename_comp hk (hu.lift _) hj b hb]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .record_casesOn us n b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, b', hb, rfl⟩ := h
      simp only [Term.rename, Neu.rename_comp hk hu n hn, Term.rename_comp hk (hu.liftN _) hj b hb]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .branch br, _, h => by
      simp only [Term.rename,
        Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      simp only [Term.rename, Branch.rename_comp hk hu hj br hx]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .jump j e, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨j', hj', e', he, rfl⟩ := h
      simp only [Term.rename, PExpr.rename_comp hk hu e he, hj j j' hj']

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} → {js js₁ js₂ : JCtx ks} →
    {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} → {rj₂ : JRen js₁ js₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} → {rj₃ : JRen js js₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → JRen.CompOn rj₁ rj₂ rj₃ → {ℓ : Nat} →
    (br : Branch Δ d Φ Γ τ js ℓ) → {br₁ : Branch Δ d Φ₁ Γ₁ τ js₁ ℓ} →
    br.rename rk₁ ru₁ rj₁ = some br₁ → br₁.rename rk₂ ru₂ rj₂ = br.rename rk₃ ru₃ rj₃
  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .ite c t e, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      simp only [Branch.rename, Neu.rename_comp hk hu c hc, Term.rename_comp hk hu hj t ht,
        Term.rename_comp hk hu hj e he]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .enum_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      have hf : (fun i => (bs' i).rename rk₂ ru₂ rj₂) = (fun i => (bs i).rename rk₃ ru₃ rj₃) :=
        funext fun i => Term.rename_comp hk hu hj (bs i) (Fin.optAll_eq_some hbs i)
      simp only [Branch.rename, Neu.rename_comp hk hu e he, hf]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .union_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Branch.rename, Neu.rename_comp hk hu e he, Branches.rename_comp hk hu hj bs hbs]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .join σ u uₓ body main, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      simp only [Branch.rename, Term.rename_comp hk (hu.lift _) hj body hbody,
        Branch.rename_comp hk hu (hj.lift _) main hmain]

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.rename_comp : {d : Nat} → {Φ Φ₁ Φ₂ : KCtx ks} → {Γ Γ₁ Γ₂ : UCtx ks} → {js js₁ js₂ : JCtx ks} →
    {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ₁ Φ₂} → {ru₂ : URen Γ₁ Γ₂} → {rj₂ : JRen js₁ js₂} →
    {rk₃ : KRen Φ Φ₂} → {ru₃ : URen Γ Γ₂} → {rj₃ : JRen js js₂} →
    KRen.CompOn rk₁ rk₂ rk₃ → URen.CompOn ru₁ ru₂ ru₃ → JRen.CompOn rj₁ rj₂ rj₃ → {bs : List Bool} →
    {cs : Ctors ks bs} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → {br₁ : Branches Δ d Φ₁ Γ₁ cs τ js₁ o} →
    br.rename rk₁ ru₁ rj₁ = some br₁ → br₁.rename rk₂ ru₂ rj₂ = br.rename rk₃ ru₃ rj₃
  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, _, _, .two us₁ us₂ b₁ b₂, _, h => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.rename, Term.rename_comp hk (hu.liftN _) hj b₁ h₁,
        Term.rename_comp hk (hu.liftN _) hj b₂ h₂]

  | _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, _, _, .cons us b bs, _, h => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.rename, Term.rename_comp hk (hu.liftN _) hj b hb,
        Branches.rename_comp hk hu hj bs hbs]

  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
end


/-! ## Meets, layer 1 -/

section MeetLayer1
variable {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} {Γ Γ₁ Γ₂ Γ₃ : UCtx ks}
  {rk₁ : KRen Φ Φ₁} {ru₁ : URen Γ Γ₁} {rk₂ : KRen Φ Φ₂} {ru₂ : URen Γ Γ₂}
  {rk₃ : KRen Φ Φ₃} {ru₃ : URen Γ Γ₃}

mutual
theorem Neu.rename_meet (hk : KRen.Meet rk₁ rk₂ rk₃) (hu : URen.Meet ru₁ ru₂ ru₃) :
    {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) → {n₁ : Neu Δ Φ₁ Γ₁ τ ℓ} →
    {n₂ : Neu Δ Φ₂ Γ₂ τ ℓ} → n.rename rk₁ ru₁ = some n₁ → n.rename rk₂ ru₂ = some n₂ →
    (n.rename rk₃ ru₃).isSome
  | _, _, .var x, _, _, h₁, h₂ => by
      simp only [Neu.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (hu x (by simp [h0₁]) (by simp [h0₂]))
      simp [Neu.rename, h0₃]
  | _, _, .data_out b j n, _, _, h₁, h₂ => by
      simp only [Neu.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu n h0₁ h0₂)
      simp [Neu.rename, h0₃]
  | _, _, .cond c a b, _, _, h₁, h₂ => by
      simp only [Neu.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, y2₁, h2₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, y2₂, h2₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu c h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu a h1₁ h1₂)
      obtain ⟨y2₃, h2₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu b h2₁ h2₂)
      simp [Neu.rename, h0₃, h1₃, h2₃]
  | _, _, .extern e args _, _, _, h₁, h₂ => by
      simp only [Neu.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu args h0₁ h0₂)
      simp [Neu.rename, h0₃]
theorem PExpr.rename_meet (hk : KRen.Meet rk₁ rk₂ rk₃) (hu : URen.Meet ru₁ ru₂ ru₃) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) → {e₁ : PExpr Δ Φ₁ Γ₁ τ o} →
    {e₂ : PExpr Δ Φ₂ Γ₂ τ o} → e.rename rk₁ ru₁ = some e₁ → e.rename rk₂ ru₂ = some e₂ →
    (e.rename rk₃ ru₃).isSome
  | _, _, .neu n, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu n h0₁ h0₂)
      simp [PExpr.rename, h0₃]
  | _, _, .kvar k, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (hk k (by simp [h0₁]) (by simp [h0₂]))
      simp [PExpr.rename, h0₃]
  | _, _, .lit _ _, _, _, h₁, h₂ => by
      simp [PExpr.rename]
  | _, _, .enum_mk _ _, _, _, h₁, h₂ => by
      simp [PExpr.rename]
  | _, _, .record_mk args, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu args h0₁ h0₂)
      simp [PExpr.rename, h0₃]
  | _, _, .union_mk ix args, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu args h0₁ h0₂)
      simp [PExpr.rename, h0₃]
  | _, _, .array_mk es, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Elems.rename_meet hk hu es h0₁ h0₂)
      simp [PExpr.rename, h0₃]
  | _, _, .list_mk es, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Elems.rename_meet hk hu es h0₁ h0₂)
      simp [PExpr.rename, h0₃]
  | _, _, .data_in b j e, _, _, h₁, h₂ => by
      simp only [PExpr.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      simp [PExpr.rename, h0₃]
theorem Args.rename_meet (hk : KRen.Meet rk₁ rk₂ rk₃) (hu : URen.Meet ru₁ ru₂ ru₃) :
    {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) → {as₁ : Args Δ Φ₁ Γ₁ σs o} →
    {as₂ : Args Δ Φ₂ Γ₂ σs o} → as.rename rk₁ ru₁ = some as₁ → as.rename rk₂ ru₂ = some as₂ →
    (as.rename rk₃ ru₃).isSome
  | _, _, .nil, _, _, h₁, h₂ => by
      simp [Args.rename]
  | _, _, .cons a as, _, _, h₁, h₂ => by
      simp only [Args.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu a h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu as h1₁ h1₂)
      simp [Args.rename, h0₃, h1₃]
theorem Elems.rename_meet (hk : KRen.Meet rk₁ rk₂ rk₃) (hu : URen.Meet ru₁ ru₂ ru₃) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → {es₁ : Elems Δ Φ₁ Γ₁ t o} →
    {es₂ : Elems Δ Φ₂ Γ₂ t o} → es.rename rk₁ ru₁ = some es₁ → es.rename rk₂ ru₂ = some es₂ →
    (es.rename rk₃ ru₃).isSome
  | _, _, .nil, _, _, h₁, h₂ => by
      simp [Elems.rename]
  | _, _, .cons e es, _, _, h₁, h₂ => by
      simp only [Elems.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Elems.rename_meet hk hu es h1₁ h1₂)
      simp [Elems.rename, h0₃, h1₃]
end

end MeetLayer1

/-! ## Meets, layer 2 -/

mutual
theorem Val.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → {τ : Ty ks} → {o : Lvl} →
    (v : Val Δ d Φ Γ τ o) → {v₁ : Val Δ d Φ₁ Γ₁ τ o} → {v₂ : Val Δ d Φ₂ Γ₂ τ o} →
    v.rename rk₁ ru₁ = some v₁ → v.rename rk₂ ru₂ = some v₂ → (v.rename rk₃ ru₃).isSome
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lam b, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Body.rename_meet hk hu b h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .thunk_mk b, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Body.rename_meet hk hu b h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lazy_mk b, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Body.rename_meet hk hu b h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .record_mk args, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu args h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .union_mk ix args, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Args.rename_meet hk hu args h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .array_mk es, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Elems.rename_meet hk hu es h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .list_mk es, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Elems.rename_meet hk hu es h0₁ h0₂)
      simp [Val.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_in b j e, _, _, h₁, h₂ => by
      simp only [Val.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      simp [Val.rename, h0₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
theorem Body.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    (b : Body Δ d Φ Γ bs τ o) → {b₁ : Body Δ d Φ₁ Γ₁ bs τ o} → {b₂ : Body Δ d Φ₂ Γ₂ bs τ o} →
    b.rename rk₁ ru₁ = some b₁ → b.rename rk₂ ru₂ = some b₂ → (b.rename rk₃ ru₃).isSome
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, bs, _, _, .closed t, _, _, h₁, h₂ => by
      simp only [Body.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk.closedOnly URen.Meet.id JRen.Meet.nil t h0₁ h0₂)
      simp [Body.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, bs, _, _, .opened t _, _, _, h₁, h₂ => by
      simp only [Body.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.liftN bs) JRen.Meet.nil t h0₁ h0₂)
      simp [Body.rename, h0₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
theorem Comp.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → {τ : Ty ks} → {ℓ : Nat} →
    (c : Comp Δ d Φ Γ τ ℓ) → {c₁ : Comp Δ d Φ₁ Γ₁ τ ℓ} → {c₂ : Comp Δ d Φ₂ Γ₂ τ ℓ} →
    c.rename rk₁ ru₁ = some c₁ → c.rename rk₂ ru₂ = some c₂ → (c.rename rk₃ ru₃).isSome
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .app f a _, _, _, h₁, h₂ => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu f h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu a h1₁ h1₂)
      simp [Comp.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .share n, _, _, h₁, h₂ => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu n h0₁ h0₂)
      simp [Comp.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .nat_rec n z s _, _, _, h₁, h₂ => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, y2₁, h2₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, y2₂, h2₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu n h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu z h1₁ h1₂)
      obtain ⟨y2₃, h2₃⟩ := Option.isSome_iff_exists.mp (Body.rename_meet hk hu s h2₁ h2₂)
      simp [Comp.rename, h0₃, h1₃, h2₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .array_foldl n z s _, _, _, h₁, h₂ => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, y2₁, h2₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, y2₂, h2₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu n h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu z h1₁ h1₂)
      obtain ⟨y2₃, h2₃⟩ := Option.isSome_iff_exists.mp (Body.rename_meet hk hu s h2₁ h2₂)
      simp [Comp.rename, h0₃, h1₃, h2₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_rec b ρt us brs j e _, _, _, h₁, h₂ => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Fin.optAll_isSome fun i => Body.rename_meet hk hu (brs i) (Fin.optAll_eq_some h0₁ i) (Fin.optAll_eq_some h0₂ i))
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h1₁ h1₂)
      simp [Comp.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .data_brec b ρt k us brs j e _, _, _, h₁, h₂ => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Fin.optAll_isSome fun i => Body.rename_meet hk hu (brs i) (Fin.optAll_eq_some h0₁ i) (Fin.optAll_eq_some h0₂ i))
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h1₁ h1₂)
      simp [Comp.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .thunk_force e, _, _, h₁, h₂ => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      simp [Comp.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, rk₁, ru₁, rk₂, ru₂, rk₃, ru₃, hk, hu, _, _, .lazy_force e, _, _, h₁, h₂ => by
      simp only [Comp.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      simp [Comp.rename, h0₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
theorem Term.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {js js₁ js₂ js₃ : JCtx ks} → {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} → {rj₂ : JRen js js₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} → {rj₃ : JRen js js₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → JRen.Meet rj₁ rj₂ rj₃ → {o : Lvl} →
    (t : Term Δ d Φ Γ τ js o) → {t₁ : Term Δ d Φ₁ Γ₁ τ js₁ o} → {t₂ : Term Δ d Φ₂ Γ₂ τ js₂ o} →
    t.rename rk₁ ru₁ rj₁ = some t₁ → t.rename rk₂ ru₂ rj₂ = some t₂ →
    (t.rename rk₃ ru₃ rj₃).isSome
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .ret e, _, _, h₁, h₂ => by
      simp only [Term.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h0₁ h0₂)
      simp [Term.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .letV u v b, _, _, h₁, h₂ => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Val.rename_meet hk hu v h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet (hk.lift _) hu hj b h1₁ h1₂)
      simp [Term.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .letE u c b, _, _, h₁, h₂ => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Comp.rename_meet hk hu c h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.lift _) hj b h1₁ h1₂)
      simp [Term.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .record_casesOn us n b, _, _, h₁, h₂ => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu n h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.liftN _) hj b h1₁ h1₂)
      simp [Term.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .branch br, _, _, h₁, h₂ => by
      simp only [Term.rename,
        Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨y0₁, h0₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Branch.rename_meet hk hu hj br h0₁ h0₂)
      simp [Term.rename, h0₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .jump j e, _, _, h₁, h₂ => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (hj j (by simp [h0₁]) (by simp [h0₂]))
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (PExpr.rename_meet hk hu e h1₁ h1₂)
      simp [Term.rename, h0₃, h1₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
theorem Branch.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {js js₁ js₂ js₃ : JCtx ks} → {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} → {rj₂ : JRen js js₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} → {rj₃ : JRen js js₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → JRen.Meet rj₁ rj₂ rj₃ → {ℓ : Nat} →
    (br : Branch Δ d Φ Γ τ js ℓ) → {br₁ : Branch Δ d Φ₁ Γ₁ τ js₁ ℓ} →
    {br₂ : Branch Δ d Φ₂ Γ₂ τ js₂ ℓ} →
    br.rename rk₁ ru₁ rj₁ = some br₁ → br.rename rk₂ ru₂ rj₂ = some br₂ →
    (br.rename rk₃ ru₃ rj₃).isSome
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .ite c t e, _, _, h₁, h₂ => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, y2₁, h2₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, y2₂, h2₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu c h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk hu hj t h1₁ h1₂)
      obtain ⟨y2₃, h2₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk hu hj e h2₁ h2₂)
      simp [Branch.rename, h0₃, h1₃, h2₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .enum_casesOn e bs, _, _, h₁, h₂ => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu e h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Fin.optAll_isSome fun i => Term.rename_meet hk hu hj (bs i) (Fin.optAll_eq_some h1₁ i) (Fin.optAll_eq_some h1₂ i))
      simp [Branch.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .union_casesOn e bs, _, _, h₁, h₂ => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Neu.rename_meet hk hu e h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Branches.rename_meet hk hu hj bs h1₁ h1₂)
      simp [Branch.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, .join σ u uₓ body main, _, _, h₁, h₂ => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.lift _) hj body h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Branch.rename_meet hk hu (hj.lift _) main h1₁ h1₂)
      simp [Branch.rename, h0₃, h1₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
theorem Branches.rename_meet : {d : Nat} → {Φ Φ₁ Φ₂ Φ₃ : KCtx ks} → {Γ Γ₁ Γ₂ Γ₃ : UCtx ks} →
    {js js₁ js₂ js₃ : JCtx ks} → {τ : Ty ks} →
    {rk₁ : KRen Φ Φ₁} → {ru₁ : URen Γ Γ₁} → {rj₁ : JRen js js₁} →
    {rk₂ : KRen Φ Φ₂} → {ru₂ : URen Γ Γ₂} → {rj₂ : JRen js js₂} →
    {rk₃ : KRen Φ Φ₃} → {ru₃ : URen Γ Γ₃} → {rj₃ : JRen js js₃} →
    KRen.Meet rk₁ rk₂ rk₃ → URen.Meet ru₁ ru₂ ru₃ → JRen.Meet rj₁ rj₂ rj₃ → {bs : List Bool} →
    {cs : Ctors ks bs} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → {br₁ : Branches Δ d Φ₁ Γ₁ cs τ js₁ o} →
    {br₂ : Branches Δ d Φ₂ Γ₂ cs τ js₂ o} →
    br.rename rk₁ ru₁ rj₁ = some br₁ → br.rename rk₂ ru₂ rj₂ = some br₂ →
    (br.rename rk₃ ru₃ rj₃).isSome
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, _, _, .two us₁ us₂ b₁ b₂, _, _, h₁, h₂ => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.liftN _) hj b₁ h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.liftN _) hj b₂ h1₁ h1₂)
      simp [Branches.rename, h0₃, h1₃]
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, rk₁, ru₁, rj₁, rk₂, ru₂, rj₂, rk₃, ru₃, rj₃, hk, hu, hj, _, _, _, .cons us b bs, _, _, h₁, h₂ => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨y0₁, h0₁, y1₁, h1₁, rfl⟩ := h₁
      obtain ⟨y0₂, h0₂, y1₂, h1₂, rfl⟩ := h₂
      obtain ⟨y0₃, h0₃⟩ := Option.isSome_iff_exists.mp (Term.rename_meet hk (hu.liftN _) hj b h0₁ h0₂)
      obtain ⟨y1₃, h1₃⟩ := Option.isSome_iff_exists.mp (Branches.rename_meet hk hu hj bs h1₁ h1₂)
      simp [Branches.rename, h0₃, h1₃]
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

end LeanScript

end
