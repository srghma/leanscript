module

public import LeanScript.Term.Optimize.Fold
public import LeanScript.Term.Optimize.ShareTest

@[expose] public section

set_option autoImplicit false

/-!
# Constants built from conditionals of constants

A pure expression whose operands are constants, or conditionals `c ? x : y` of constants on one
condition `c`, is a conditional of two constants:

* `Neu.condFold`: a call of an extern, folded on each side when both calls fold to literals
  (`"Hello" ++ ", World"` is a literal): `(c ? "Hello" : "") ++ ", World"` is
  `c ? "Hello, World" : ", World"`;
* `PExpr.liftCond`: an array, list, record or union literal with at least two conditional
  operands (one test instead of several):
  `#[c ? "a" : "b", c ? "x" : "y"]` is `c ? #["a", "x"] : #["b", "y"]`.

Nothing is computed more often than before (exactly one side is evaluated), and both sides are
constants.  The level is checked to be the same (it always is, the condition being the only open
part), otherwise the expression is kept.  `Neu.condFold_eval`, `PExpr.liftCond_eval`: the value
does not change.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

section
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The parts of a conditional `c ? x : y`. -/
def PExpr.asCond? {τ : Ty ks} : {o : Lvl} → PExpr Δ Φ Γ τ o →
    Option ((ℓ : Nat) × Neu Δ Φ Γ .bool ℓ × (oa : Lvl) × PExpr Δ Φ Γ τ oa × (ob : Lvl) ×
      PExpr Δ Φ Γ τ ob)
  | _, .neu (.cond c a b) => some ⟨_, c, _, a, _, b⟩
  | _, _ => none

theorem PExpr.asCond?_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o)
    {r : (ℓ : Nat) × Neu Δ Φ Γ .bool ℓ × (oa : Lvl) × PExpr Δ Φ Γ τ oa × (ob : Lvl) ×
      PExpr Δ Φ Γ τ ob} (h : e.asCond? = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    e.eval κ ρ = match (r.2.1.eval κ ρ : Bool) with
      | true => r.2.2.2.1.eval κ ρ
      | false => r.2.2.2.2.2.eval κ ρ := by
  cases e with
  | neu n =>
      cases n with
      | cond c a b =>
          simp only [PExpr.asCond?, Option.some.injEq] at h
          subst h
          rfl
      | _ => simp [PExpr.asCond?] at h
  | _ => simp [PExpr.asCond?] at h

/-- `e` read where the condition `c` has the value `b`: a conditional on `c` (written the same
    way) is its arm `b`; the result must be a constant. -/
def PExpr.pickCst? {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) : Option ((o' : Lvl) × PExpr Δ Φ Γ τ o') :=
  match e.asCond? with
  | some ⟨_, c', _, x, _, y⟩ =>
      if c'.same c then
        match b with
        | true => if x.cst?.isSome then some ⟨_, x⟩ else none
        | false => if y.cst?.isSome then some ⟨_, y⟩ else none
      else none
  | none => if e.cst?.isSome then some ⟨_, e⟩ else none

theorem PExpr.pickCst?_eval {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) {r : (o' : Lvl) × PExpr Δ Φ Γ τ o'} (h : e.pickCst? c b = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (hc : (c.eval κ ρ : Bool) = b) :
    r.2.eval κ ρ = e.eval κ ρ := by
  unfold PExpr.pickCst? at h
  split at h
  · rename_i ℓ' c' oa x ob y hce
    rw [PExpr.asCond?_eval e hce κ ρ]
    split at h
    · rename_i hs
      have hv : (c'.eval κ ρ : Bool) = c.eval κ ρ := by
        have := (Neu.same_eval c' c hs).2 κ ρ
        exact eq_of_heq this
      simp only
      rw [hv, hc]
      cases b with
      | true =>
          simp only at h
          split at h
          · cases h; rfl
          · cases h
      | false =>
          simp only at h
          split at h
          · cases h; rfl
          · cases h
    · cases h
  · split at h
    · cases h; rfl
    · cases h

/-- `PExpr.pickCst?` on every element. -/
def Elems.pickCst? {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) :
    {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Option ((o' : Lvl) × Elems Δ Φ Γ t o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons e es =>
      match e.pickCst? c b, Elems.pickCst? c b es with
      | some e', some es' => some ⟨_, .cons e'.2 es'.2⟩
      | _, _ => none

theorem Elems.pickCst?_eval {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hc : (c.eval κ ρ : Bool) = b) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) → {r : (o' : Lvl) × Elems Δ Φ Γ t o'} →
    es.pickCst? c b = some r → r.2.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _, h => by simp only [Elems.pickCst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Elems.pickCst?] at h
      split at h
      · rename_i e' es' he hes
        cases h
        simp only [Elems.eval, PExpr.pickCst?_eval c b e he κ ρ hc,
          Elems.pickCst?_eval c b κ ρ hc es hes]
      · cases h

/-- `PExpr.pickCst?` on every argument. -/
def Args.pickCst? {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) :
    {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Option ((o' : Lvl) × Args Δ Φ Γ σs o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons e es =>
      match e.pickCst? c b, Args.pickCst? c b es with
      | some e', some es' => some ⟨_, .cons e'.2 es'.2⟩
      | _, _ => none

theorem Args.pickCst?_eval {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hc : (c.eval κ ρ : Bool) = b) :
    {σs : List (Ty ks)} → {o : Lvl} → (es : Args Δ Φ Γ σs o) →
    {r : (o' : Lvl) × Args Δ Φ Γ σs o'} → es.pickCst? c b = some r → r.2.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _, h => by simp only [Args.pickCst?, Option.some.injEq] at h; subst h; rfl
  | _, _, .cons e es, _, h => by
      simp only [Args.pickCst?] at h
      split at h
      · rename_i e' es' he hes
        cases h
        simp only [Args.eval, PExpr.pickCst?_eval c b e he κ ρ hc,
          Args.pickCst?_eval c b κ ρ hc es hes]
      · cases h

/-- The condition of the first element that is a conditional. -/
def Elems.firstCond? : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    Option ((ℓ : Nat) × Neu Δ Φ Γ .bool ℓ)
  | _, _, .nil => none
  | _, _, .cons e es =>
      match e.asCond? with
      | some r => some ⟨r.1, r.2.1⟩
      | none => Elems.firstCond? es

/-- The condition of the first argument that is a conditional. -/
def Args.firstCond? : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Option ((ℓ : Nat) × Neu Δ Φ Γ .bool ℓ)
  | _, _, .nil => none
  | _, _, .cons e es =>
      match e.asCond? with
      | some r => some ⟨r.1, r.2.1⟩
      | none => Args.firstCond? es

/-- How many elements are conditionals. -/
def Elems.numConds : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Nat
  | _, _, .nil => 0
  | _, _, .cons e es => (if e.asCond?.isSome then 1 else 0) + Elems.numConds es

/-- How many arguments are conditionals. -/
def Args.numConds : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Nat
  | _, _, .nil => 0
  | _, _, .cons e es => (if e.asCond?.isSome then 1 else 0) + Args.numConds es

/-! ## Extern calls -/

/-- The call `e args` where the arguments are constants and conditionals of constants on one
    condition `c`: `c ? (e args[c := true]) : (e args[c := false])`, each folded to a literal. -/
def Neu.condFold? {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) {o : Lvl}
    (args : Args Δ Φ Γ σs o) : Option ((ℓ : Nat) × Neu Δ Φ Γ τ ℓ) :=
  match args.firstCond? with
  | some ⟨_, c⟩ =>
      match args.pickCst? c true, args.pickCst? c false with
      | some aa, some ab =>
          match Neu.mkExtern? e aa.2, Neu.mkExtern? e ab.2 with
          | some la, some lb => some ⟨_, .cond c la.2 lb.2⟩
          | _, _ => none
      | _, _ => none
  | none => none

theorem Neu.condFold?_eval {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) {o : Lvl}
    (args : Args Δ Φ Γ σs o) {r : (ℓ : Nat) × Neu Δ Φ Γ τ ℓ} (h : Neu.condFold? e args = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    r.2.eval κ ρ = Extern.eval (DSig.refDen Δ) e (args.eval κ ρ) := by
  unfold Neu.condFold? at h
  split at h
  · rename_i ℓ c _
    split at h
    · rename_i aa ab ha hb
      split at h
      · rename_i la lb hla hlb
        cases h
        simp only [Neu.eval]
        cases hc : (c.eval κ ρ : Bool) with
        | true =>
            simp only
            rw [Neu.mkExtern?_eval e aa.2 la hla κ ρ, Args.pickCst?_eval c true κ ρ hc args ha]
        | false =>
            simp only
            rw [Neu.mkExtern?_eval e ab.2 lb hlb κ ρ, Args.pickCst?_eval c false κ ρ hc args hb]
      · cases h
    · cases h
  · cases h

/-- `Neu.condFold?` on an extern call, when the level comes out the same. -/
def Neu.condFold {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) : Neu Δ Φ Γ τ ℓ :=
  match n with
  | .extern e args _ =>
      match Neu.condFold? e args with
      | some r => if h : r.1 = ℓ then h ▸ r.2 else n
      | none => n
  | _ => n

theorem Neu.condFold_eval {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : n.condFold.eval κ ρ = n.eval κ ρ := by
  cases n with
  | extern e args _ =>
      simp only [Neu.condFold]
      split
      · rename_i r hr
        split
        · rename_i h
          obtain ⟨ℓ', m⟩ := r
          simp only at h
          subst h
          simp only [Neu.eval]
          exact Neu.condFold?_eval e args hr κ ρ
        · rfl
      · rfl
  | _ => rfl

/-! ## Literals -/

/-- `c ? a : b` in place of `e`, when the level comes out the same. -/
def PExpr.condOr {τ : Ty ks} {ℓ : Nat} {oa ob o : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (a : PExpr Δ Φ Γ τ oa) (b : PExpr Δ Φ Γ τ ob) (e : PExpr Δ Φ Γ τ o) : PExpr Δ Φ Γ τ o :=
  if h : some (Lvl.meetL ℓ (Lvl.meet oa ob)) = o then h ▸ .neu (.cond c a b) else e

theorem PExpr.condOr_eval {τ : Ty ks} {ℓ : Nat} {oa ob o : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (a : PExpr Δ Φ Γ τ oa) (b : PExpr Δ Φ Γ τ ob) (e : PExpr Δ Φ Γ τ o) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (ha : (c.eval κ ρ : Bool) = true → a.eval κ ρ = e.eval κ ρ)
    (hb : (c.eval κ ρ : Bool) = false → b.eval κ ρ = e.eval κ ρ) :
    (PExpr.condOr c a b e).eval κ ρ = e.eval κ ρ := by
  unfold PExpr.condOr
  split
  · rename_i h
    subst h
    simp only [PExpr.eval, Neu.eval]
    cases hc : (c.eval κ ρ : Bool) with
    | true => exact ha hc
    | false => exact hb hc
  · rfl

/-- An array, list, record or union literal whose operands are constants and conditionals of
    constants on one condition `c`: `c ? (literal[c := true]) : (literal[c := false])`. -/
def PExpr.liftCond : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .array_mk es =>
      match if 2 ≤ es.numConds then es.firstCond? else none with
      | some ⟨_, c⟩ =>
          match es.pickCst? c true, es.pickCst? c false with
          | some ea, some eb => PExpr.condOr c (.array_mk ea.2) (.array_mk eb.2) (.array_mk es)
          | _, _ => .array_mk es
      | none => .array_mk es
  | _, _, .list_mk es =>
      match if 2 ≤ es.numConds then es.firstCond? else none with
      | some ⟨_, c⟩ =>
          match es.pickCst? c true, es.pickCst? c false with
          | some ea, some eb => PExpr.condOr c (.list_mk ea.2) (.list_mk eb.2) (.list_mk es)
          | _, _ => .list_mk es
      | none => .list_mk es
  | _, _, .record_mk args =>
      match if 2 ≤ args.numConds then args.firstCond? else none with
      | some ⟨_, c⟩ =>
          match args.pickCst? c true, args.pickCst? c false with
          | some ea, some eb =>
              PExpr.condOr c (.record_mk ea.2) (.record_mk eb.2) (.record_mk args)
          | _, _ => .record_mk args
      | none => .record_mk args
  | _, _, .union_mk ix args =>
      match if 2 ≤ args.numConds then args.firstCond? else none with
      | some ⟨_, c⟩ =>
          match args.pickCst? c true, args.pickCst? c false with
          | some ea, some eb =>
              PExpr.condOr c (.union_mk ix ea.2) (.union_mk ix eb.2) (.union_mk ix args)
          | _, _ => .union_mk ix args
      | none => .union_mk ix args
  | _, _, e => e

theorem PExpr.liftCond_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : e.liftCond.eval κ ρ = e.eval κ ρ := by
  cases e with
  | array_mk es =>
      simp only [PExpr.liftCond]
      split
      · rename_i ℓ c _
        split
        · rename_i ea eb ha hb
          apply PExpr.condOr_eval
          · intro hc; simp only [PExpr.eval]; rw [Elems.pickCst?_eval c true κ ρ hc es ha]
          · intro hc; simp only [PExpr.eval]; rw [Elems.pickCst?_eval c false κ ρ hc es hb]
        · rfl
      · rfl
  | list_mk es =>
      simp only [PExpr.liftCond]
      split
      · rename_i ℓ c _
        split
        · rename_i ea eb ha hb
          apply PExpr.condOr_eval
          · intro hc; simp only [PExpr.eval]; rw [Elems.pickCst?_eval c true κ ρ hc es ha]
          · intro hc; simp only [PExpr.eval]; rw [Elems.pickCst?_eval c false κ ρ hc es hb]
        · rfl
      · rfl
  | record_mk args =>
      simp only [PExpr.liftCond]
      split
      · rename_i ℓ c _
        split
        · rename_i ea eb ha hb
          apply PExpr.condOr_eval
          · intro hc; simp only [PExpr.eval]; rw [Args.pickCst?_eval c true κ ρ hc args ha]
          · intro hc; simp only [PExpr.eval]; rw [Args.pickCst?_eval c false κ ρ hc args hb]
        · rfl
      · rfl
  | union_mk ix args =>
      simp only [PExpr.liftCond]
      split
      · rename_i ℓ c _
        split
        · rename_i ea eb ha hb
          apply PExpr.condOr_eval
          · intro hc; simp only [PExpr.eval]; rw [Args.pickCst?_eval c true κ ρ hc args ha]
          · intro hc; simp only [PExpr.eval]; rw [Args.pickCst?_eval c false κ ρ hc args hb]
        · rfl
      · rfl
  | _ => rfl

end

end LeanScript

end
