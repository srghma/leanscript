module

public import LeanScript.NTerm.Rename

@[expose] public section

set_option autoImplicit false

/-!
# Renaming preserves the value

`Term.rename_eval`: if renaming a statement succeeds, the renamed statement has the same
value, in environments that agree along the renamings (`URen.Agree`, `KRen.Agree`,
`JRen.Agree`).  The same holds for every other layer.
-/

namespace LeanScript.NTerm

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Environments -/

@[simp] theorem UEnv.get_cons_head {Γ : UCtx ks} {τ : Ty ks} {u : Usage} (v : Ty.Den Δ τ)
    (ρ : UEnv Δ Γ) (h : u ≠ .zero) :
    UEnv.get (Γ := ⟨τ, u⟩ :: Γ) (Tuple.cons v ρ) (.head h) = v := by
  simp [UEnv.get]

@[simp] theorem UEnv.get_cons_tail {Γ : UCtx ks} {τ : Ty ks} {b : UBinder ks}
    (v : Ty.Den Δ b.ty) (ρ : UEnv Δ Γ) (x : UVar Γ τ) :
    UEnv.get (Γ := b :: Γ) (Tuple.cons v ρ) (.tail x) = ρ.get x := by
  simp [UEnv.get]

@[simp] theorem KEnv.get_cons_head {Φ : KCtx ks} {τ : Ty ks} {u : Usage} {o : Bool}
    (v : Ty.Den Δ τ) (κ : KEnv Δ Φ) (h : u ≠ .zero) :
    KEnv.get (Φ := ⟨τ, u, o⟩ :: Φ) (Tuple.cons v κ) (.head h) = v := by
  simp [KEnv.get]

@[simp] theorem KEnv.get_cons_tail {Φ : KCtx ks} {τ : Ty ks} {o : Bool} {b : KBinder ks}
    (v : Ty.Den Δ b.ty) (κ : KEnv Δ Φ) (x : KVar Φ τ o) :
    KEnv.get (Φ := b :: Φ) (Tuple.cons v κ) (.tail x) = κ.get x := by
  simp [KEnv.get]

@[simp] theorem JEnv.get_cons_head {τ : Ty ks} {js : UCtx ks} {σ : Ty ks} {u : Usage}
    (f : Ty.Den Δ σ → Ty.Den Δ τ) (jκ : JEnv Δ τ js) (h : u ≠ .zero) :
    JEnv.get (js := ⟨σ, u⟩ :: js) (Tuple.cons f jκ) (.head h) = f := by
  simp [JEnv.get]

@[simp] theorem JEnv.get_cons_tail {τ : Ty ks} {js : UCtx ks} {σ : Ty ks} {b : UBinder ks}
    (f : Ty.Den Δ b.ty → Ty.Den Δ τ) (jκ : JEnv Δ τ js) (x : UVar js σ) :
    JEnv.get (js := b :: js) (Tuple.cons f jκ) (.tail x) = jκ.get x := by
  simp [JEnv.get]

/-- The closed view holds the same values. -/
theorem KEnv.closedOnly_get : {Φ : KCtx ks} → (κ : KEnv Δ Φ) → {τ : Ty ks} → {o : Bool} →
    (x : KVar (KCtx.closedOnly Φ) τ o) → (KEnv.closedOnly κ).get x = κ.get x.unmask
  | ⟨_, _, true⟩ :: _, _, _, _, .head h => absurd rfl h
  | ⟨t, _, true⟩ :: _, κ, _, _, .tail x =>
      (KEnv.get_cons_tail (Δ := Δ) (b := ⟨t, .zero, true⟩) κ.head (KEnv.closedOnly κ.tail) x).trans
        (KEnv.closedOnly_get κ.tail x)
  | ⟨_, _, false⟩ :: _, κ, _, _, .head h =>
      KEnv.get_cons_head (Δ := Δ) κ.head (KEnv.closedOnly κ.tail) h
  | ⟨t, u, false⟩ :: _, κ, _, _, .tail x =>
      (KEnv.get_cons_tail (Δ := Δ) (b := ⟨t, u, false⟩) κ.head (KEnv.closedOnly κ.tail) x).trans
        (KEnv.closedOnly_get κ.tail x)

/-- Masking and unmasking are inverse. -/
theorem KVar.mask_unmask : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} → (y : KVar Φ τ o) →
    {z : KVar (KCtx.closedOnly Φ) τ o} → y.mask = some z → z.unmask = y
  | ⟨_, _, true⟩ :: _, _, _, .head _, _, h => by simp [KVar.mask] at h
  | ⟨_, _, true⟩ :: _, _, _, .tail y, _, h => by
      cases hm : y.mask with
      | none => simp only [KVar.mask, hm, Option.map_none] at h; cases h
      | some z =>
          simp only [KVar.mask, hm, Option.map_some] at h
          cases h
          simp [KVar.unmask, KVar.mask_unmask y hm]
  | ⟨_, _, false⟩ :: _, _, _, .head _, _, h => by
      cases h; rfl
  | ⟨_, _, false⟩ :: _, _, _, .tail y, _, h => by
      cases hm : y.mask with
      | none => simp only [KVar.mask, hm, Option.map_none] at h; cases h
      | some z =>
          simp only [KVar.mask, hm, Option.map_some] at h
          cases h
          simp [KVar.unmask, KVar.mask_unmask y hm]

/-! ## Agreement of environments along renamings -/

/-- Two environments of unknowns agree along a renaming. -/
def URen.Agree {Γ Γ' : UCtx ks} (r : URen Γ Γ') (ρ : UEnv Δ Γ) (ρ' : UEnv Δ Γ') : Prop :=
  ∀ {τ : Ty ks} (x : UVar Γ τ) (y : UVar Γ' τ), r x = some y → ρ'.get y = ρ.get x

/-- Two environments of known values agree along a renaming. -/
def KRen.Agree {Φ Φ' : KCtx ks} (r : KRen Φ Φ') (κ : KEnv Δ Φ) (κ' : KEnv Δ Φ') : Prop :=
  ∀ {τ : Ty ks} {o : Bool} (x : KVar Φ τ o) (y : KVar Φ' τ o), r x = some y → κ'.get y = κ.get x

/-- Two environments of join points agree along a renaming. -/
def JRen.Agree {τ : Ty ks} {js js' : UCtx ks} (r : URen js js') (jκ : JEnv Δ τ js)
    (jκ' : JEnv Δ τ js') : Prop :=
  ∀ {σ : Ty ks} (x : UVar js σ) (y : UVar js' σ), r x = some y → jκ'.get y = jκ.get x

theorem URen.Agree.id {Γ : UCtx ks} (ρ : UEnv Δ Γ) : URen.Agree URen.id ρ ρ := by
  intro _ x y h; cases h; rfl

theorem KRen.Agree.id {Φ : KCtx ks} (κ : KEnv Δ Φ) : KRen.Agree KRen.id κ κ := by
  intro _ _ x y h; cases h; rfl

theorem URen.Agree.nil : URen.Agree (Δ := Δ) URen.nil PUnit.unit PUnit.unit := by
  intro _ x; exact nomatch x

theorem JRen.Agree.nil {τ : Ty ks} :
    JRen.Agree (Δ := Δ) (τ := τ) URen.nil PUnit.unit PUnit.unit := by
  intro _ x; exact nomatch x

theorem URen.Agree.lift {Γ Γ' : UCtx ks} {r : URen Γ Γ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}
    (h : URen.Agree r ρ ρ') (b : UBinder ks) (v : Ty.Den Δ b.ty) :
    URen.Agree (URen.lift r b) (Tuple.cons v ρ) (Tuple.cons v ρ') := by
  intro _ x y hxy
  cases x with
  | head hu =>
      simp only [URen.lift, Option.some.injEq] at hxy
      subst hxy; simp
  | tail x =>
      simp only [URen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [h x y hy]

theorem URen.Agree.liftN {Γ Γ' : UCtx ks} {r : URen Γ Γ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}
    (h : URen.Agree r ρ ρ') : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    URen.Agree (URen.liftN r bs) (Tuple.append vs ρ) (Tuple.append vs ρ')
  | [], _ => h
  | b :: bs, vs => by
      rw [Tuple.append_cons, Tuple.append_cons]
      exact URen.Agree.lift (URen.Agree.liftN h bs vs.tail) b vs.head

theorem KRen.Agree.lift {Φ Φ' : KCtx ks} {r : KRen Φ Φ'} {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'}
    (h : KRen.Agree r κ κ') (b : KBinder ks) (v : Ty.Den Δ b.ty) :
    KRen.Agree (KRen.lift r b) (Tuple.cons v κ) (Tuple.cons v κ') := by
  intro _ _ x y hxy
  cases x with
  | head hu =>
      simp only [KRen.lift, Option.some.injEq] at hxy
      subst hxy; simp
  | tail x =>
      simp only [KRen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [h x y hy]

theorem KRen.Agree.closedOnly {Φ Φ' : KCtx ks} {r : KRen Φ Φ'} {κ : KEnv Δ Φ}
    {κ' : KEnv Δ Φ'} (h : KRen.Agree r κ κ') :
    KRen.Agree (KRen.closedOnly r) (KEnv.closedOnly κ) (KEnv.closedOnly κ') := by
  intro _ _ x z hxz
  simp only [KRen.closedOnly, Option.bind_eq_some_iff] at hxz
  obtain ⟨y, hy, hz⟩ := hxz
  rw [KEnv.closedOnly_get, KEnv.closedOnly_get, KVar.mask_unmask y hz, h _ y hy]

theorem JRen.Agree.lift {τ : Ty ks} {js js' : UCtx ks} {r : URen js js'} {jκ : JEnv Δ τ js}
    {jκ' : JEnv Δ τ js'} (h : JRen.Agree r jκ jκ') (b : UBinder ks)
    (f : Ty.Den Δ b.ty → Ty.Den Δ τ) :
    JRen.Agree (URen.lift r b) (Tuple.cons f jκ) (Tuple.cons f jκ') := by
  intro _ x y hxy
  cases x with
  | head hu =>
      simp only [URen.lift, Option.some.injEq] at hxy
      subst hxy; simp
  | tail x =>
      simp only [URen.lift, Option.map_eq_some_iff] at hxy
      obtain ⟨y, hy, rfl⟩ := hxy
      simp [h x y hy]

theorem URen.Agree.comp {Γ₁ Γ₂ Γ₃ : UCtx ks} {r₁ : URen Γ₁ Γ₂} {r₂ : URen Γ₂ Γ₃}
    {ρ₁ : UEnv Δ Γ₁} {ρ₂ : UEnv Δ Γ₂} {ρ₃ : UEnv Δ Γ₃} (h₁ : URen.Agree r₁ ρ₁ ρ₂)
    (h₂ : URen.Agree r₂ ρ₂ ρ₃) : URen.Agree (fun x => (r₁ x).bind r₂) ρ₁ ρ₃ := by
  intro _ x z hxz
  simp only [Option.bind_eq_some_iff] at hxz
  obtain ⟨y, hy, hz⟩ := hxz
  rw [h₂ y z hz, h₁ x y hy]

theorem URen.Agree.drop {Γ : UCtx ks} {σ : Ty ks} {u : Usage} (v : Ty.Den Δ σ)
    (ρ : UEnv Δ Γ) : URen.Agree (URen.drop (σ := σ) (u := u)) (Tuple.cons v ρ) ρ := by
  intro _ x y hxy
  cases x with
  | head _ => simp [URen.drop] at hxy
  | tail x =>
      simp only [URen.drop, Option.some.injEq] at hxy
      subst hxy; simp

theorem KRen.Agree.drop {Φ : KCtx ks} {σ : Ty ks} {u : Usage} {o : Bool} (v : Ty.Den Δ σ)
    (κ : KEnv Δ Φ) : KRen.Agree (KRen.drop (σ := σ) (u := u) (o := o)) (Tuple.cons v κ) κ := by
  intro _ _ x y hxy
  cases x with
  | head _ => simp [KRen.drop] at hxy
  | tail x =>
      simp only [KRen.drop, Option.some.injEq] at hxy
      subst hxy; simp

theorem JRen.Agree.drop {τ : Ty ks} {js : UCtx ks} {σ : Ty ks} {u : Usage}
    (f : Ty.Den Δ σ → Ty.Den Δ τ) (jκ : JEnv Δ τ js) :
    JRen.Agree (URen.drop (σ := σ) (u := u)) (Tuple.cons f jκ) jκ := by
  intro _ x y hxy
  cases x with
  | head _ => simp [URen.drop] at hxy
  | tail x =>
      simp only [URen.drop, Option.some.injEq] at hxy
      subst hxy; simp

theorem URen.Agree.reuse {Γ : UCtx ks} {σ : Ty ks} {u : Usage} (u' : Usage) (v : Ty.Den Δ σ)
    (ρ : UEnv Δ Γ) :
    URen.Agree (URen.reuse (σ := σ) (u := u) u') (Tuple.cons v ρ) (Tuple.cons v ρ) := by
  intro _ x y hxy
  cases x with
  | head _ =>
      simp only [URen.reuse] at hxy
      split at hxy
      · cases hxy
      · simp only [Option.some.injEq] at hxy; subst hxy; simp
  | tail x =>
      simp only [URen.reuse, Option.some.injEq] at hxy
      subst hxy; simp

theorem KRen.Agree.reuse {Φ : KCtx ks} {σ : Ty ks} {u : Usage} {o : Bool} (u' : Usage)
    (v : Ty.Den Δ σ) (κ : KEnv Δ Φ) :
    KRen.Agree (KRen.reuse (σ := σ) (u := u) (o := o) u') (Tuple.cons v κ) (Tuple.cons v κ) := by
  intro _ _ x y hxy
  cases x with
  | head _ =>
      simp only [KRen.reuse] at hxy
      split at hxy
      · cases hxy
      · simp only [Option.some.injEq] at hxy; subst hxy; simp
  | tail x =>
      simp only [KRen.reuse, Option.some.injEq] at hxy
      subst hxy; simp

theorem JRen.Agree.reuse {τ : Ty ks} {js : UCtx ks} {σ : Ty ks} {u : Usage} (u' : Usage)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) (jκ : JEnv Δ τ js) :
    JRen.Agree (URen.reuse (σ := σ) (u := u) u') (Tuple.cons f jκ) (Tuple.cons f jκ) := by
  intro _ x y hxy
  cases x with
  | head _ =>
      simp only [URen.reuse] at hxy
      split at hxy
      · cases hxy
      · simp only [Option.some.injEq] at hxy; subst hxy; simp
  | tail x =>
      simp only [URen.reuse, Option.some.injEq] at hxy
      subst hxy; simp


/-! ## Renaming preserves the value -/

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} {rk : KRen Φ Φ'} {ru : URen Γ Γ'}
  {κ : KEnv Δ Φ} {κ' : KEnv Δ Φ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'}

mutual
theorem Neu.rename_eval (hk : KRen.Agree rk κ κ') (hu : URen.Agree ru ρ ρ') :
    {τ : Ty ks} → (n : Neu Δ Φ Γ τ) → {n' : Neu Δ Φ' Γ' τ} → n.rename rk ru = some n' →
      n'.eval κ' ρ' = n.eval κ ρ
  | _, .var x, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact hu x y hy
  | _, .data_out b j n, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [Neu.eval, Neu.rename_eval hk hu n hm] <;> rfl
  | _, .cond c a b, _, h => by
      simp only [Neu.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, a', ha, b', hb, rfl⟩ := h
      simp only [Neu.eval, Neu.rename_eval hk hu c hc, PExpr.rename_eval hk hu a ha,
        PExpr.rename_eval hk hu b hb] <;> rfl
  | _, .extern e args, _, h => by
      simp only [Neu.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Neu.eval, Args.rename_eval hk hu args has] <;> rfl
theorem PExpr.rename_eval (hk : KRen.Agree rk κ κ') (hu : URen.Agree ru ρ ρ') :
    {τ : Ty ks} → {o : Bool} → (e : PExpr Δ Φ Γ τ o) → {e' : PExpr Δ Φ' Γ' τ o} →
      e.rename rk ru = some e' → e'.eval κ' ρ' = e.eval κ ρ
  | _, _, .neu n, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [PExpr.eval, Neu.rename_eval hk hu n hm] <;> rfl
  | _, _, .kvar k, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact hk k y hy
  | _, _, .lit _ _, _, h => by
      simp only [PExpr.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .enum_mk _ _, _, h => by
      simp only [PExpr.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .record_mk args, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.rename_eval hk hu args has] <;> rfl
  | _, _, .union_mk ix args, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [PExpr.eval, Args.rename_eval hk hu args has] <;> rfl
  | _, _, .array_mk es, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.rename_eval hk hu es hes] <;> rfl
  | _, _, .list_mk es, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [PExpr.eval, Elems.rename_eval hk hu es hes] <;> rfl
  | _, _, .data_in b j e, _, h => by
      simp only [PExpr.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, PExpr.rename_eval hk hu e he] <;> rfl
theorem Args.rename_eval (hk : KRen.Agree rk κ κ') (hu : URen.Agree ru ρ ρ') :
    {σs : List (Ty ks)} → {o : Bool} → (as : Args Δ Φ Γ σs o) → {as' : Args Δ Φ' Γ' σs o} →
      as.rename rk ru = some as' → as'.eval κ' ρ' = as.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Args.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons a as, _, h => by
      simp only [Args.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, as', has, rfl⟩ := h
      simp only [Args.eval, PExpr.rename_eval hk hu a ha, Args.rename_eval hk hu as has] <;> rfl
theorem Elems.rename_eval (hk : KRen.Agree rk κ κ') (hu : URen.Agree ru ρ ρ') :
    {t : Ty ks} → {o : Bool} → (es : Elems Δ Φ Γ t o) → {es' : Elems Δ Φ' Γ' t o} →
      es.rename rk ru = some es' → es'.eval κ' ρ' = es.eval κ ρ
  | _, _, .nil, _, h => by
      simp only [Elems.rename, Option.some.injEq] at h
      subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Elems.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, es', hes, rfl⟩ := h
      simp only [Elems.eval, PExpr.rename_eval hk hu e he, Elems.rename_eval hk hu es hes] <;> rfl
end

end Layer1

mutual
theorem Val.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {rk : KRen Φ Φ'} →
    {ru : URen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → {τ : Ty ks} → {o : Bool} →
    (v : Val Δ Φ Γ τ o) → {v' : Val Δ Φ' Γ' τ o} → v.rename rk ru = some v' →
      v'.eval κ' ρ' = v.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .lam b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval]
      funext x
      exact Body.rename_eval hk hu b hb _
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .thunk_mk b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval, Body.rename_eval hk hu b hb] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .lazy_mk b, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨b', hb, rfl⟩ := h
      simp only [Val.eval, Body.rename_eval hk hu b hb] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .record_mk args, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.rename_eval hk hu args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .union_mk ix args, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨as', has, rfl⟩ := h
      simp only [Val.eval, Args.rename_eval hk hu args has] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .array_mk es, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.rename_eval hk hu es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .list_mk es, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨es', hes, rfl⟩ := h
      simp only [Val.eval, Elems.rename_eval hk hu es hes] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, _, .data_in b j e, _, h => by
      simp only [Val.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Val.eval, PExpr.rename_eval hk hu e he] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Body.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {rk : KRen Φ Φ'} →
    {ru : URen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → {bs : UCtx ks} → {τ : Ty ks} → {o : Bool} →
    (b : Body Δ Φ Γ bs τ o) → {b' : Body Δ Φ' Γ' bs τ o} → b.rename rk ru = some b' →
      ∀ vs : UEnv Δ bs, b'.eval κ' ρ' vs = b.eval κ ρ vs
  | _, _, _, _, _, _, _, _, _, _, hk, _, _, _, _, .closed t, _, h, vs => by
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.eval]
      exact Term.rename_eval hk.closedOnly (URen.Agree.id vs) JRen.Agree.nil t ht
  | _, _, _, [], _, _, _, _, _, _, _, _, _, _, _, .opened _, _, h, _ => by
      simp [Body.rename] at h
  | _, _, _, _ :: _, _, _, _, _, _, _, hk, hu, bs, _, _, .opened t, _, h, vs => by
      simp only [Body.rename, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      simp only [Body.eval]
      exact Term.rename_eval hk (hu.liftN bs vs) JRen.Agree.nil t ht
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
theorem Comp.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {rk : KRen Φ Φ'} →
    {ru : URen Γ Γ'} → {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → {τ : Ty ks} →
    (c : Comp Δ Φ Γ τ) → {c' : Comp Δ Φ' Γ' τ} → c.rename rk ru = some c' →
      c'.eval κ' ρ' = c.eval κ ρ
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .app f a _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨f', hf, a', ha, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu f hf, PExpr.rename_eval hk hu a ha] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .share n, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨n', hn, rfl⟩ := h
      simp only [Comp.eval, Neu.rename_eval hk hu n hn] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .nat_rec n z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, z', hz, s', hs, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu n hn, PExpr.rename_eval hk hu z hz,
        Body.rename_eval hk hu s hs] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .array_foldl a z s _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, z', hz, s', hs, rfl⟩ := h
      simp only [Comp.eval]
      rw [PExpr.rename_eval hk hu a ha, PExpr.rename_eval hk hu z hz]
      simp only [Body.rename_eval hk hu s hs]
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .data_rec b ρt us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu e he,
        fun i => Body.rename_eval hk hu (brs i) (Fin.optAll_eq_some hbrs i)] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .data_brec b ρt k us brs j e _, _, h => by
      simp only [Comp.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨brs', hbrs, e', he, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu e he,
        fun i => Body.rename_eval hk hu (brs i) (Fin.optAll_eq_some hbrs i)] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .thunk_force e, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu e he] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, hk, hu, _, .lazy_force e, _, h => by
      simp only [Comp.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Comp.eval, PExpr.rename_eval hk hu e he] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Term.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} →
    {τ : Ty ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : URen js js'} →
    {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    (t : Term Δ Φ Γ τ js) → {t' : Term Δ Φ' Γ' τ js'} → t.rename rk ru rj = some t' →
      t'.eval κ' ρ' jκ' = t.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, _, .ret e, _, h => by
      simp only [Term.rename, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.rename_eval hk hu e he] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .letV u v b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨v', hv, b', hb, rfl⟩ := h
      simp only [Term.eval, Val.rename_eval hk hu v hv]
      exact Term.rename_eval (hk.lift _ _) hu hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .letE u c b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, b', hb, rfl⟩ := h
      simp only [Term.eval, Comp.rename_eval hk hu c hc]
      exact Term.rename_eval hk (hu.lift _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .record_casesOn us n b, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨n', hn, b', hb, rfl⟩ := h
      simp only [Term.eval, Neu.rename_eval hk hu n hn]
      exact Term.rename_eval hk (hu.liftN _ _) hj b hb
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .branch br, _, h => by
      simp only [Term.rename, Option.map_eq_some_iff] at h
      obtain ⟨br', hbr, rfl⟩ := h
      simp only [Term.eval]
      exact Branch.rename_eval hk hu hj br hbr
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .jump j e, _, h => by
      simp only [Term.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨j', hj', e', he, rfl⟩ := h
      simp only [Term.eval, PExpr.rename_eval hk hu e he, hj j j' hj'] <;> rfl
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branch.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} →
    {τ : Ty ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : URen js js'} →
    {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    (br : Branch Δ Φ Γ τ js) → {br' : Branch Δ Φ' Γ' τ js'} → br.rename rk ru rj = some br' →
      br'.eval κ' ρ' jκ' = br.eval κ ρ jκ
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .ite c t e, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨c', hc, t', ht, e', he, rfl⟩ := h
      simp only [Branch.eval, Neu.rename_eval hk hu c hc, Term.rename_eval hk hu hj t ht,
        Term.rename_eval hk hu hj e he] <;> rfl
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .enum_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Branch.eval, Neu.rename_eval hk hu e he]
      exact Term.rename_eval hk hu hj _ (Fin.optAll_eq_some hbs _)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .union_casesOn e bs, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨e', he, bs', hbs, rfl⟩ := h
      simp only [Branch.eval, Neu.rename_eval hk hu e he]
      exact Branches.rename_eval hk hu hj bs hbs _
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, .join σ u uₓ body main, _, h => by
      simp only [Branch.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨body', hbody, main', hmain, rfl⟩ := h
      simp only [Branch.eval]
      have hf := funext fun v => Term.rename_eval hk (hu.lift ⟨σ, uₓ⟩ v) hj body hbody
      rw [hf]
      exact Branch.rename_eval hk hu (hj.lift _ _) main hmain
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ => x
theorem Branches.rename_eval : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} →
    {τ : Ty ks} → {rk : KRen Φ Φ'} → {ru : URen Γ Γ'} → {rj : URen js js'} →
    {κ : KEnv Δ Φ} → {κ' : KEnv Δ Φ'} → {ρ : UEnv Δ Γ} → {ρ' : UEnv Δ Γ'} →
    {jκ : JEnv Δ τ js} → {jκ' : JEnv Δ τ js'} →
    KRen.Agree rk κ κ' → URen.Agree ru ρ ρ' → JRen.Agree rj jκ jκ' →
    {bs : List Bool} → {cs : Ctors ks bs} →
    (br : Branches Δ Φ Γ cs τ js) → {br' : Branches Δ Φ' Γ' cs τ js'} →
    br.rename rk ru rj = some br' →
      ∀ x, br'.eval κ' ρ' jκ' x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, _, .two us₁ us₂ b₁ b₂, _, h, x => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b₁', h₁, b₂', h₂, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.rename_eval hk (hu.liftN _ _) hj b₁ h₁
      · funext v; exact Term.rename_eval hk (hu.liftN _ _) hj b₂ h₂
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk, hu, hj, _, _, .cons us b bs, _, h, x => by
      simp only [Branches.rename, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨b', hb, bs', hbs, rfl⟩ := h
      simp only [Branches.eval]
      congr 1
      · funext v; exact Term.rename_eval hk (hu.liftN _ _) hj b hb
      · funext r; exact Branches.rename_eval hk hu hj bs hbs r
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ => x
end

end LeanScript.NTerm

end
