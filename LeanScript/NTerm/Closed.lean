module

public import LeanScript.NTerm.Syntax

@[expose] public section

set_option autoImplicit false

/-!
# A statement with nothing unknown is a value

The central property of the normal form, enforced by the types: when there is no unknown in
scope (`Γ = []`) and no usable known value is open (`KCtx.Closed Φ`), there is

* no neutral expression, no computation and no branch (`Neu.not_closed`, `Comp.not_closed`,
  `Branch.not_closed`), and every pure expression, value and body is closed
  (`PExpr.closed`, `Val.closed`, `Body.closed_eq`);
* so a statement is a chain of `letV`s of closed values ending in `ret v` with `v` closed
  (`Term.closed_isValue`): **nothing is left to compute**.

In particular a whole program (`Term Δ [] [] τ []`) is a value (`Term.run_isValue`), and so
is the body of every closed closure, closed delay and closed loop body once its own
parameters are known — the body of a closed delay, which has no parameter, is already a value
(`Term.closedBody_isValue`).
-/

namespace LeanScript.NTerm

variable {ks : List Nat} {Δ : DSig ks}

/-- No usable known value is open. -/
def KCtx.Closed (Φ : KCtx ks) : Prop := ∀ τ : Ty ks, KVar Φ τ true → False

theorem KCtx.Closed.nil : KCtx.Closed ([] : KCtx ks) := fun _ x => nomatch x

theorem KCtx.Closed.cons {Φ : KCtx ks} {σ : Ty ks} {u : Usage} (h : KCtx.Closed Φ) :
    KCtx.Closed (⟨σ, u, false⟩ :: Φ) := fun
  | _, .tail x => h _ x

/-- The known values seen from a closed body are closed. -/
theorem KCtx.Closed.closedOnly (Φ : KCtx ks) : KCtx.Closed (KCtx.closedOnly Φ) :=
  fun _ x => Bool.noConfusion x.closedOnly_closed

theorem KCtx.Closed.ofAllClosed {Φ : KCtx ks} (h : KCtx.AllClosed Φ) : KCtx.Closed Φ :=
  fun _ x => Bool.noConfusion (x.allClosed h)

theorem KVar.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} :
    {o : Bool} → KVar Φ τ o → o = false
  | false, _ => rfl
  | true, x => (hΦ _ x).elim

mutual
/-- There is no neutral expression without an unknown. -/
theorem Neu.not_closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) : {τ : Ty ks} → Neu Δ Φ [] τ → False
  | _, .var x => nomatch x
  | _, .data_out _ _ n => Neu.not_closed hΦ n
  | _, .cond c _ _ => Neu.not_closed hΦ c
  | _, .extern _ args => Bool.noConfusion (Args.closed hΦ args)
/-- A pure expression without an unknown is closed. -/
theorem PExpr.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) : {τ : Ty ks} → {o : Bool} → PExpr Δ Φ [] τ o → o = false
  | _, _, .neu n => (Neu.not_closed hΦ n).elim
  | _, _, .kvar k => k.closed hΦ
  | _, _, .lit _ _ => rfl
  | _, _, .enum_mk _ _ => rfl
  | _, _, .record_mk args => Args.closed hΦ args
  | _, _, .union_mk _ args => Args.closed hΦ args
  | _, _, .array_mk es => Elems.closed hΦ es
  | _, _, .list_mk es => Elems.closed hΦ es
  | _, _, .data_in _ _ e => PExpr.closed hΦ e
/-- Arguments without an unknown are closed. -/
theorem Args.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) : {σs : List (Ty ks)} → {o : Bool} → Args Δ Φ [] σs o → o = false
  | _, _, .nil => rfl
  | _, _, .cons a as => by rw [PExpr.closed hΦ a, Args.closed hΦ as]; rfl
/-- Elements without an unknown are closed. -/
theorem Elems.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) : {t : Ty ks} → {o : Bool} → Elems Δ Φ [] t o → o = false
  | _, _, .nil => rfl
  | _, _, .cons e es => by rw [PExpr.closed hΦ e, Elems.closed hΦ es]; rfl
end

/-- A body without an unknown in scope is closed. -/
theorem Body.closed_eq {Φ : KCtx ks} {bs : UCtx ks} {τ : Ty ks} {o : Bool} : Body Δ Φ [] bs τ o → o = false
  | .closed _ => rfl

/-- A value without an unknown is closed. -/
theorem Val.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} {o : Bool} : Val Δ Φ [] τ o → o = false
  | .lam b => b.closed_eq
  | .thunk_mk b => b.closed_eq
  | .lazy_mk b => b.closed_eq
  | .record_mk args => Args.closed hΦ args
  | .union_mk _ args => Args.closed hΦ args
  | .array_mk es => Elems.closed hΦ es
  | .list_mk es => Elems.closed hΦ es
  | .data_in _ _ e => PExpr.closed hΦ e

/-- There is no computation without an unknown. -/
theorem Comp.not_closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} : Comp Δ Φ [] τ → False
  | .app f a h => by
      rw [PExpr.closed hΦ f, PExpr.closed hΦ a] at h; exact Bool.noConfusion h
  | .share n => Neu.not_closed hΦ n
  | .nat_rec n z s h => by
      rw [PExpr.closed hΦ n, PExpr.closed hΦ z, s.closed_eq] at h; exact Bool.noConfusion h
  | .array_foldl a z s h => by
      rw [PExpr.closed hΦ a, PExpr.closed hΦ z, s.closed_eq] at h; exact Bool.noConfusion h
  | .data_rec _ _ _ brs _ e h => by
      rw [PExpr.closed hΦ e, (brs 0).closed_eq] at h; exact Bool.noConfusion h
  | .data_brec _ _ _ _ brs _ e h => by
      rw [PExpr.closed hΦ e, (brs 0).closed_eq] at h; exact Bool.noConfusion h
  | .thunk_force e => Bool.noConfusion (PExpr.closed hΦ e)
  | .lazy_force e => Bool.noConfusion (PExpr.closed hΦ e)

/-- There is no branch without an unknown. -/
theorem Branch.not_closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} : {js : UCtx ks} → Branch Δ Φ [] τ js → False
  | _, .ite c _ _ => Neu.not_closed hΦ c
  | _, .enum_casesOn e _ => Neu.not_closed hΦ e
  | _, .union_casesOn e _ => Neu.not_closed hΦ e
  | _, .join _ _ _ _ main => Branch.not_closed hΦ main

/-- **A value**: a chain of `letV`s of closed values ending in the answer, a closed pure
    expression. -/
inductive Term.IsValue : {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : UCtx ks} →
    Term Δ Φ Γ τ js → Prop where
  | ret {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : UCtx ks} {o : Bool} (e : PExpr Δ Φ Γ τ o) :
      o = false → Term.IsValue (.ret (js := js) e)
  | letV {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : UCtx ks} {o : Bool} (u : Usage)
      (v : Val Δ Φ Γ σ o) {b : Term Δ (⟨σ, u, o⟩ :: Φ) Γ τ js} :
      o = false → Term.IsValue b → Term.IsValue (.letV u v b)

theorem Term.closed_isValue_aux {τ : Ty ks} :
    {Φ : KCtx ks} → {Γ js : UCtx ks} → KCtx.Closed Φ → Γ = [] → js = [] →
      (t : Term Δ Φ Γ τ js) → t.IsValue
  | _, _, _, hΦ, hΓ, _, .ret e => .ret e (by subst hΓ; exact PExpr.closed hΦ e)
  | _, _, _, hΦ, hΓ, hjs, .letV (o := o) u v b =>
      have h : o = false := by subst hΓ; exact Val.closed hΦ v
      .letV u v h (Term.closed_isValue_aux (h ▸ KCtx.Closed.cons hΦ) hΓ hjs b)
  | _, _, _, hΦ, hΓ, _, .letE _ c _ => by subst hΓ; exact (Comp.not_closed hΦ c).elim
  | _, _, _, hΦ, hΓ, _, .record_casesOn _ n _ => by subst hΓ; exact (Neu.not_closed hΦ n).elim
  | _, _, _, hΦ, hΓ, _, .branch br => by subst hΓ; exact (Branch.not_closed hΦ br).elim
  | _, _, _, _, _, hjs, .jump j _ => by subst hjs; exact nomatch j
  termination_by _ _ _ _ _ _ t => sizeOf t
  decreasing_by simp_wf; omega

/-- **A statement with no unknown and no open known value is a value**: nothing is left to
    compute. -/
theorem Term.closed_isValue {τ : Ty ks} {Φ : KCtx ks} (hΦ : KCtx.Closed Φ)
    (t : Term Δ Φ [] τ []) : t.IsValue :=
  Term.closed_isValue_aux hΦ rfl rfl t

/-- A whole program is a value. -/
theorem Term.run_isValue {τ : Ty ks} (t : Term Δ [] [] τ []) : t.IsValue :=
  t.closed_isValue KCtx.Closed.nil

/-- The body of a closed delay (a closed body with no parameter) is a value. -/
theorem Term.closedBody_isValue {Φ : KCtx ks} {τ : Ty ks}
    (t : Term Δ (KCtx.closedOnly Φ) [] τ []) : t.IsValue :=
  t.closed_isValue (KCtx.Closed.closedOnly Φ)

end LeanScript.NTerm

end
