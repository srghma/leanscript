module

public import LeanScript.Term.Semantics.Eval
public import LeanScript.Term.Extern.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Folding constant pure expressions

The pieces a rewrite needs when it makes a pure expression known:

* `PExpr.cst?`: the pure expression as a constant (in the empty contexts), when it mentions no
  variable at all (`PExpr.cst?_eval`: its value is the value of the constant);
* `PExpr.boolLit?`: the boolean a pure expression is, when it is a literal;
* `PExpr.ofDen?`: the literal of a value of a leaf type;
* `Neu.mkExtern?`: a call of an extern on arguments of any level: the neutral call when an
  argument is open (a `Neu.extern` needs one), the literal of its value when every argument is
  a constant and the result is of a leaf type (`lean_nat_dec_eq 3 3` is `true`), else nothing
  (`Neu.mkExtern?_eval`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Constant pure expressions -/

section Cst
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
/-- The pure expression as a constant (no variable, so in the empty contexts), when it mentions
    no variable at all: a literal, or a literal constructor of constants. -/
def PExpr.cst? : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Option (PExpr Δ [] [] τ none)
  | _, _, .neu _ => none
  | _, _, .kvar _ => none
  | _, _, .lit p v => some (.lit p v)
  | _, _, .enum_mk s i => some (.enum_mk s i)
  | _, _, .record_mk args => args.cst?.map .record_mk
  | _, _, .union_mk ix args => args.cst?.map (.union_mk ix)
  | _, _, .array_mk es => es.cst?.map .array_mk
  | _, _, .list_mk es => es.cst?.map .list_mk
  | _, _, .data_in b j e => e.cst?.map (.data_in b j)
/-- Constant arguments. -/
def Args.cst? : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Option (Args Δ [] [] σs none)
  | _, _, .nil => some .nil
  | _, _, .cons a as =>
    match a.cst?, as.cst? with
    | some a', some as' => some (.cons a' as')
    | _, _ => none
/-- Constant elements. -/
def Elems.cst? : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Option (Elems Δ [] [] t none)
  | _, _, .nil => some .nil
  | _, _, .cons e es =>
    match e.cst?, es.cst? with
    | some e', some es' => some (.cons e' es')
    | _, _ => none
end

mutual
theorem PExpr.cst?_eval : {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) →
    (c : PExpr Δ [] [] τ none) → e.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    e.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .neu _, _, h, _, _ => by simp [PExpr.cst?] at h
  | _, _, .kvar _, _, h, _, _ => by simp [PExpr.cst?] at h
  | _, _, .lit _ _, c, h, _, _ => by simp only [PExpr.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .enum_mk _ _, c, h, _, _ => by
      simp only [PExpr.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .record_mk args, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [PExpr.eval, Args.cst?_eval args a' ha κ ρ] <;> rfl
  | _, _, .union_mk _ args, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨a', ha, rfl⟩ := h
      simp only [PExpr.eval, Args.cst?_eval args a' ha κ ρ] <;> rfl
  | _, _, .array_mk es, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, Elems.cst?_eval es e' he κ ρ] <;> rfl
  | _, _, .list_mk es, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, Elems.cst?_eval es e' he κ ρ] <;> rfl
  | _, _, .data_in _ _ e, c, h, κ, ρ => by
      simp only [PExpr.cst?, Option.map_eq_some_iff] at h
      obtain ⟨e', he, rfl⟩ := h
      simp only [PExpr.eval, PExpr.cst?_eval e e' he κ ρ] <;> rfl
theorem Args.cst?_eval : {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    (c : Args Δ [] [] σs none) → as.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    as.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .nil, c, h, _, _ => by simp only [Args.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons a as, c, h, κ, ρ => by
      simp only [Args.cst?] at h
      split at h
      · rename_i a' as' ha has
        cases h
        simp only [Args.eval, PExpr.cst?_eval a a' ha κ ρ, Args.cst?_eval as as' has κ ρ]
      · cases h
theorem Elems.cst?_eval : {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) →
    (c : Elems Δ [] [] t none) → es.cst? = some c → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    es.eval κ ρ = c.eval Tuple.nil Tuple.nil
  | _, _, .nil, c, h, _, _ => by simp only [Elems.cst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons e es, c, h, κ, ρ => by
      simp only [Elems.cst?] at h
      split at h
      · rename_i e' es' he hes
        cases h
        simp only [Elems.eval, PExpr.cst?_eval e e' he κ ρ, Elems.cst?_eval es es' hes κ ρ]
      · cases h
end

end Cst

/-! ## Literals -/

section Lit
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The boolean a pure expression is, when it is a boolean literal. -/
def PExpr.boolLit? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    PExpr Δ Φ Γ τ o → Option Bool
  | .lit p v => match p, v with
    | .bool, v => some v
    | _, _ => none
  | _ => none

theorem PExpr.boolLit?_eval {Φ : KCtx ks} {Γ : UCtx ks} {o : Lvl} (e : PExpr Δ Φ Γ .bool o)
    (b : Bool) (h : e.boolLit? = some b) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (e.eval κ ρ : Bool) = b := by
  cases e with
  | lit _ v =>
    simp only [PExpr.boolLit?, Option.some.injEq] at h
    exact h
  | _ => simp [PExpr.boolLit?] at h

/-- The literal of a value of a leaf type. -/
def PExpr.ofDen? : (τ : Ty ks) → Ty.Den Δ τ → Option (PExpr Δ Φ Γ τ none)
  | .prim p, v => some (.lit p v)
  | _, _ => none

theorem PExpr.ofDen?_eval (τ : Ty ks) (v : Ty.Den Δ τ) (e : PExpr Δ Φ Γ τ none)
    (h : PExpr.ofDen? τ v = some e) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : e.eval κ ρ = v := by
  cases τ with
  | prim _ => simp only [PExpr.ofDen?, Option.some.injEq] at h; subst h; rfl
  | _ => simp [PExpr.ofDen?] at h

/-- A call of the extern `e` on arguments of any level: the neutral call when an argument is
    open, the literal of its value when every argument is a constant and the result is of a
    leaf type, otherwise nothing. -/
def Neu.mkExtern? {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) :
    {o : Lvl} → Args Δ Φ Γ σs o → Option ((o' : Lvl) × PExpr Δ Φ Γ τ o')
  | some _, args => some ⟨_, .neu (.extern e args rfl)⟩
  | none, args =>
      args.cst?.bind fun c =>
        (PExpr.ofDen? τ (Extern.eval (DSig.refDen Δ) e
          (c.eval (Φ := []) (Γ := []) Tuple.nil Tuple.nil))).map fun l => ⟨none, l⟩

theorem Neu.mkExtern?_eval {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) {o : Lvl}
    (args : Args Δ Φ Γ σs o) (p : (o' : Lvl) × PExpr Δ Φ Γ τ o') (h : Neu.mkExtern? e args = some p)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : p.2.eval κ ρ = Extern.eval (DSig.refDen Δ) e (args.eval κ ρ) := by
  cases o with
  | some _ => simp only [Neu.mkExtern?, Option.some.injEq] at h; subst h; rfl
  | none =>
      simp only [Neu.mkExtern?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, l, hl, rfl⟩ := h
      rw [PExpr.ofDen?_eval τ _ l hl κ ρ, Args.cst?_eval args c hc κ ρ]

end Lit

end LeanScript

end
