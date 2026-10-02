module

public import LeanScript.Term.Optimize.ExternEq
public import LeanScript.Term.Optimize.Cse

@[expose] public section

set_option autoImplicit false

/-!
# Calls of externs on atoms, and replacing them by a name

The pieces of the hoisting rewrite (`LeanScript.Term.Optimize.Hoist`) that live in pure
expressions:

* `ENeu`: a call of an extern whose arguments are all atoms (unknowns or known values by name),
  `lean_int_repr(x)`, recognised in a neutral expression by `ENeu.ofNeu?`, with its value
  (`ENeu.eval`, `ENeu.ofNeu?_eval`);
* `ENeu.test s m`: is the neutral expression `m` a call of the same extern on the same atoms as
  `s` (`Extern.beq`, `Atom.key`)?  Then it has the same type and the same value
  (`ENeu.test_ty`, `ENeu.test_eval`);
* `Neu.abstr x s` / `PExpr.abstr x s` / …: every occurrence of `s` in an expression replaced by
  the unknown `x`, which preserves the value when `x` holds the value of `s`
  (`PExpr.abstr_eval`);
* the counts used by the heuristics of the rewrite (`PExpr.occ`: how many occurrences;
  `PExpr.always`: is `s` computed whenever the expression is, that is outside the arms of the
  conditionals; `PExpr.cands`: the calls of externs on atoms in it).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Arguments that are atoms -/

/-- Arguments that are all atoms. -/
inductive AtomArgs (Φ : KCtx ks) (Γ : UCtx ks) : List (Ty ks) → Type where
  | nil : AtomArgs Φ Γ []
  | cons {σ : Ty ks} {σs : List (Ty ks)} : Atom Φ Γ σ → AtomArgs Φ Γ σs → AtomArgs Φ Γ (σ :: σs)

namespace AtomArgs
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The values of the arguments. -/
def eval {σs : List (Ty ks)} : AtomArgs Φ Γ σs → KEnv Δ Φ → UEnv Δ Γ → DenList (DSig.refDen Δ) σs
  | .nil, _, _ => PUnit.unit
  | .cons a as, κ, ρ => Tuple.cons (a.eval κ ρ) (as.eval κ ρ)

/-- What identifies the arguments. -/
def keys {σs : List (Ty ks)} : AtomArgs Φ Γ σs → List AtomKey
  | .nil => []
  | .cons a as => a.key :: as.keys

theorem eval_eq_of_keys_eq : {σs : List (Ty ks)} → (a b : AtomArgs Φ Γ σs) → a.keys = b.keys →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → a.eval κ ρ = b.eval κ ρ
  | _, .nil, .nil, _, _, _ => rfl
  | _, .cons a as, .cons b bs, h, κ, ρ => by
      simp only [keys, List.cons.injEq] at h
      have e1 := eq_of_heq ((Atom.eq_of_key_eq (Δ := Δ) a b h.1).2 κ ρ)
      simp only [eval, e1, eval_eq_of_keys_eq as bs h.2 κ ρ]

/-- Under one more unknown. -/
def wkU (b : UBinder ks) {σs : List (Ty ks)} : AtomArgs Φ Γ σs → AtomArgs Φ (b :: Γ) σs
  | .nil => .nil
  | .cons a as => .cons (a.wkU b) (as.wkU b)

/-- Under more unknowns. -/
def wkUN (bs : UCtx ks) {σs : List (Ty ks)} : AtomArgs Φ Γ σs → AtomArgs Φ (bs ++ Γ) σs
  | .nil => .nil
  | .cons a as => .cons (a.wkUN bs) (as.wkUN bs)

/-- Under one more known value. -/
def wkK (b : KBinder ks) {σs : List (Ty ks)} : AtomArgs Φ Γ σs → AtomArgs (b :: Φ) Γ σs
  | .nil => .nil
  | .cons a as => .cons (a.wkK b) (as.wkK b)

@[simp] theorem wkU_eval (b : UBinder ks) {σs : List (Ty ks)} (as : AtomArgs Φ Γ σs)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) :
    (as.wkU b).eval κ (Tuple.cons v ρ) = as.eval κ ρ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [wkU, eval, ih]

theorem wkUN_eval (bs : UCtx ks) {σs : List (Ty ks)} (as : AtomArgs Φ Γ σs)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (vs : UEnv Δ bs) :
    (as.wkUN bs).eval κ (Tuple.append vs ρ) = as.eval κ ρ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [wkUN, eval, ih, Atom.wkUN_eval]

@[simp] theorem wkK_eval (b : KBinder ks) {σs : List (Ty ks)} (as : AtomArgs Φ Γ σs)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) :
    (as.wkK b).eval (Tuple.cons v κ) ρ = as.eval κ ρ := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [wkK, eval, ih]

/-- Arguments that are all atoms (unknowns, known values by name, literals), as such. -/
def ofArgs? : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Option (AtomArgs Φ Γ σs)
  | _, _, .nil => some .nil
  | _, _, .cons a as => do
      let a ← Atom.ofArg? false a
      let as ← ofArgs? as
      pure (.cons a as)

theorem ofArgs?_eval : {σs : List (Ty ks)} → {o : Lvl} → (args : Args Δ Φ Γ σs o) →
    {as : AtomArgs Φ Γ σs} → ofArgs? args = some as → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    as.eval κ ρ = args.eval κ ρ
  | _, _, .nil, _, h, _, _ => by cases h; rfl
  | _, _, .cons a as, _, h, κ, ρ => by
      simp only [ofArgs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a', ha, as', has, rfl⟩ := h
      simp only [eval, Args.eval, Atom.ofArg?_eval false a ha, ofArgs?_eval as has κ ρ]

end AtomArgs

/-! ## Calls of externs on atoms -/

/-- A call of an extern whose arguments are all atoms. -/
structure ENeu (Φ : KCtx ks) (Γ : UCtx ks) (τ : Ty ks) where
  σs : List (Ty ks)
  e : Extern ks σs τ
  args : AtomArgs Φ Γ σs

namespace ENeu
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The value of the call. -/
def eval {τ : Ty ks} (s : ENeu Φ Γ τ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : Ty.Den Δ τ :=
  Extern.eval (DSig.refDen Δ) s.e (s.args.eval κ ρ)

/-- Are the two calls recognised as the same call? -/
def beq {τ : Ty ks} : ENeu Φ Γ τ → ENeu Φ Γ τ → Bool
  | ⟨σs, e, a⟩, ⟨σs', e', a'⟩ =>
      if h : σs = σs' then Extern.beq (h ▸ e) e' && (a.keys == a'.keys) else false

theorem beq_eval {τ : Ty ks} (s t : ENeu Φ Γ τ) (h : s.beq t = true) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : s.eval (Δ := Δ) κ ρ = t.eval κ ρ := by
  obtain ⟨σs, e, a⟩ := s
  obtain ⟨σs', e', a'⟩ := t
  simp only [beq] at h
  split at h
  · rename_i hσ
    subst hσ
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    have := Extern.eq_of_beq h1
    subst this
    simp only [eval, AtomArgs.eval_eq_of_keys_eq a a' h2 κ ρ]
  · cases h

/-- A neutral expression that is a call of an extern on atoms, as one. -/
def ofNeu? {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Option (ENeu Φ Γ τ)
  | .extern e args _ => (AtomArgs.ofArgs? args).map fun as => ⟨_, e, as⟩
  | _ => none

theorem ofNeu?_eval {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) {s : ENeu Φ Γ τ}
    (h : ofNeu? n = some s) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : s.eval κ ρ = n.eval κ ρ := by
  cases n with
  | extern e args _ =>
      simp only [ofNeu?, Option.map_eq_some_iff] at h
      obtain ⟨as, has, rfl⟩ := h
      simp only [eval, Neu.eval, AtomArgs.ofArgs?_eval args has κ ρ]
  | _ => simp [ofNeu?] at h

/-- Is the neutral expression `m` a call recognised as `s`? -/
def test {σ τ : Ty ks} {ℓ : Nat} (s : ENeu Φ Γ σ) (m : Neu Δ Φ Γ τ ℓ) : Bool :=
  match ofNeu? m with
  | some s' => if h : σ = τ then (h ▸ s).beq s' else false
  | none => false

theorem test_ty {σ τ : Ty ks} {ℓ : Nat} {s : ENeu Φ Γ σ} {m : Neu Δ Φ Γ τ ℓ}
    (h : s.test m = true) : σ = τ := by
  unfold test at h
  split at h
  · split at h
    · assumption
    · cases h
  · cases h

theorem test_eval {σ τ : Ty ks} {ℓ : Nat} {s : ENeu Φ Γ σ} {m : Neu Δ Φ Γ τ ℓ}
    (h : s.test m = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : HEq (s.eval κ ρ) (m.eval κ ρ) := by
  unfold test at h
  split at h
  · rename_i s' hs
    split at h
    · rename_i hty
      subst hty
      rw [← ofNeu?_eval m hs κ ρ, beq_eval s s' h κ ρ]
    · cases h
  · cases h

/-- Under one more unknown. -/
def wkU {τ : Ty ks} (b : UBinder ks) (s : ENeu Φ Γ τ) : ENeu Φ (b :: Γ) τ :=
  ⟨s.σs, s.e, s.args.wkU b⟩

/-- Under more unknowns. -/
def wkUN {τ : Ty ks} (bs : UCtx ks) (s : ENeu Φ Γ τ) : ENeu Φ (bs ++ Γ) τ :=
  ⟨s.σs, s.e, s.args.wkUN bs⟩

/-- Under one more known value. -/
def wkK {τ : Ty ks} (b : KBinder ks) (s : ENeu Φ Γ τ) : ENeu (b :: Φ) Γ τ :=
  ⟨s.σs, s.e, s.args.wkK b⟩

@[simp] theorem wkU_eval {τ : Ty ks} (b : UBinder ks) (s : ENeu Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (s.wkU b).eval κ (Tuple.cons v ρ) = s.eval κ ρ := by
  simp [wkU, eval]

theorem wkUN_eval {τ : Ty ks} (bs : UCtx ks) (s : ENeu Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (vs : UEnv Δ bs) : (s.wkUN bs).eval κ (Tuple.append vs ρ) = s.eval κ ρ := by
  simp [wkUN, eval, AtomArgs.wkUN_eval]

@[simp] theorem wkK_eval {τ : Ty ks} (b : KBinder ks) (s : ENeu Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (s.wkK b).eval (Tuple.cons v κ) ρ = s.eval κ ρ := by
  simp [wkK, eval]

end ENeu

/-! ## Replacing a call by a name in pure expressions -/

section Abstr
variable {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {d : Nat}

/-- `x` in place of the neutral expression `m` when it is the call `s`, and `dflt` otherwise. -/
def Neu.abstrHere (x : UVar Γ σ d) (s : ENeu Φ Γ σ) {τ : Ty ks} {ℓ : Nat} (m : Neu Δ Φ Γ τ ℓ)
    (dflt : (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ') : (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ' :=
  if ht : s.test m then ⟨d, .var (ENeu.test_ty ht ▸ x)⟩ else dflt

theorem UEnv.get_cast {Γ : UCtx ks} {σ τ : Ty ks} {ℓ : Nat} (h : σ = τ) (x : UVar Γ σ ℓ)
    (ρ : UEnv Δ Γ) : HEq (ρ.get (h ▸ x)) (ρ.get x) := by
  subst h; rfl

theorem Neu.abstrHere_eval (x : UVar Γ σ d) (s : ENeu Φ Γ σ) {τ : Ty ks} {ℓ : Nat}
    (m : Neu Δ Φ Γ τ ℓ) (dflt : (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hx : ρ.get x = s.eval κ ρ) (hd : dflt.2.eval κ ρ = m.eval κ ρ) :
    (Neu.abstrHere x s m dflt).2.eval κ ρ = m.eval κ ρ := by
  by_cases ht : s.test m = true
  · rw [Neu.abstrHere, dite_eq_left ht]
    simp only [Neu.eval]
    exact eq_of_heq ((UEnv.get_cast _ x ρ).trans (hx ▸ ENeu.test_eval ht κ ρ))
  · rw [Neu.abstrHere, dite_eq_right ht]; exact hd

/-- The arguments of an extern call with the calls `s` replaced (`Args.abstr`), or the
    original call when they are closed. -/
def Neu.mkExtern {σs : List (Ty ks)} {τ : Ty ks} {o : Lvl} {ℓ : Nat} (e : Extern ks σs τ)
    (args : Args Δ Φ Γ σs o) (h : o = some ℓ) (r : (o' : Lvl) × Args Δ Φ Γ σs o') :
    (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ' :=
  match hr : r.1 with
  | some ℓ' => ⟨ℓ', .extern e r.2 hr⟩
  | none => ⟨_, .extern e args h⟩

theorem Neu.mkExtern_eval {σs : List (Ty ks)} {τ : Ty ks} {o : Lvl} {ℓ : Nat}
    (e : Extern ks σs τ) (args : Args Δ Φ Γ σs o) (h : o = some ℓ)
    (r : (o' : Lvl) × Args Δ Φ Γ σs o') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hr : r.2.eval κ ρ = args.eval κ ρ) :
    (Neu.mkExtern e args h r).2.eval κ ρ = (Neu.extern e args h).eval κ ρ := by
  unfold Neu.mkExtern
  split
  · simp only [Neu.eval, hr]
  · rfl

mutual
/-- Every occurrence of the call `s` in a neutral expression replaced by the unknown `x`. -/
def Neu.abstr (x : UVar Γ σ d) (s : ENeu Φ Γ σ) : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ'
  | _, _, .var y => Neu.abstrHere x s (.var y) ⟨_, .var y⟩
  | _, _, .data_out b j n =>
      Neu.abstrHere x s (.data_out b j n) ⟨_, .data_out b j (n.abstr x s).2⟩
  | _, _, .cond c a b =>
      Neu.abstrHere x s (.cond c a b) ⟨_, .cond (c.abstr x s).2 (a.abstr x s).2 (b.abstr x s).2⟩
  | _, _, .extern e args h =>
      Neu.abstrHere x s (.extern e args h) (Neu.mkExtern e args h (args.abstr x s))
/-- `Neu.abstr` in a pure expression. -/
def PExpr.abstr (x : UVar Γ σ d) (s : ENeu Φ Γ σ) : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | _, _, .neu n => ⟨_, .neu (n.abstr x s).2⟩
  | _, _, .kvar k => ⟨_, .kvar k⟩
  | _, _, .lit p v => ⟨_, .lit p v⟩
  | _, _, .enum_mk sc i => ⟨_, .enum_mk sc i⟩
  | _, _, .record_mk args => ⟨_, .record_mk (args.abstr x s).2⟩
  | _, _, .union_mk ix args => ⟨_, .union_mk ix (args.abstr x s).2⟩
  | _, _, .array_mk es => ⟨_, .array_mk (es.abstr x s).2⟩
  | _, _, .list_mk es => ⟨_, .list_mk (es.abstr x s).2⟩
  | _, _, .data_in b j e => ⟨_, .data_in b j (e.abstr x s).2⟩
/-- `Neu.abstr` in arguments. -/
def Args.abstr (x : UVar Γ σ d) (s : ENeu Φ Γ σ) : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → (o' : Lvl) × Args Δ Φ Γ σs o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons a as => ⟨_, .cons (a.abstr x s).2 (as.abstr x s).2⟩
/-- `Neu.abstr` in elements. -/
def Elems.abstr (x : UVar Γ σ d) (s : ENeu Φ Γ σ) : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → (o' : Lvl) × Elems Δ Φ Γ t o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons e es => ⟨_, .cons (e.abstr x s).2 (es.abstr x s).2⟩
end

mutual
theorem Neu.abstr_eval (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hx : ρ.get x = s.eval κ ρ) : {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) →
    (n.abstr x s).2.eval κ ρ = n.eval κ ρ
  | _, _, .var y => Neu.abstrHere_eval x s _ _ κ ρ hx rfl
  | _, _, .data_out b j n => Neu.abstrHere_eval x s _ _ κ ρ hx (by
      simp only [Neu.eval, Neu.abstr_eval x s κ ρ hx n])
  | _, _, .cond c a b => Neu.abstrHere_eval x s _ _ κ ρ hx (by
      simp only [Neu.eval, Neu.abstr_eval x s κ ρ hx c, PExpr.abstr_eval x s κ ρ hx a,
        PExpr.abstr_eval x s κ ρ hx b])
  | _, _, .extern e args h => Neu.abstrHere_eval x s _ _ κ ρ hx
      (Neu.mkExtern_eval e args h _ κ ρ (Args.abstr_eval x s κ ρ hx args))
theorem PExpr.abstr_eval (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hx : ρ.get x = s.eval κ ρ) : {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) →
    (e.abstr x s).2.eval κ ρ = e.eval κ ρ
  | _, _, .neu n => by simp only [PExpr.abstr, PExpr.eval, Neu.abstr_eval x s κ ρ hx n]
  | _, _, .kvar _ => rfl
  | _, _, .lit _ _ => rfl
  | _, _, .enum_mk _ _ => rfl
  | _, _, .record_mk args => by
      simp only [PExpr.abstr, PExpr.eval, Args.abstr_eval x s κ ρ hx args] <;> rfl
  | _, _, .union_mk ix args => by
      simp only [PExpr.abstr, PExpr.eval, Args.abstr_eval x s κ ρ hx args] <;> rfl
  | _, _, .array_mk es => by
      simp only [PExpr.abstr, PExpr.eval, Elems.abstr_eval x s κ ρ hx es] <;> rfl
  | _, _, .list_mk es => by
      simp only [PExpr.abstr, PExpr.eval, Elems.abstr_eval x s κ ρ hx es] <;> rfl
  | _, _, .data_in b j e => by
      simp only [PExpr.abstr, PExpr.eval, PExpr.abstr_eval x s κ ρ hx e] <;> rfl
theorem Args.abstr_eval (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hx : ρ.get x = s.eval κ ρ) : {σs : List (Ty ks)} → {o : Lvl} → (as : Args Δ Φ Γ σs o) →
    (as.abstr x s).2.eval κ ρ = as.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons a as => by
      simp only [Args.abstr, Args.eval, PExpr.abstr_eval x s κ ρ hx a,
        Args.abstr_eval x s κ ρ hx as]
theorem Elems.abstr_eval (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hx : ρ.get x = s.eval κ ρ) : {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) →
    (es.abstr x s).2.eval κ ρ = es.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons e es => by
      simp only [Elems.abstr, Elems.eval, PExpr.abstr_eval x s κ ρ hx e,
        Elems.abstr_eval x s κ ρ hx es]
end

end Abstr

/-! ## The counts of the heuristics -/

section Counts
variable {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks}

/-- A neutral expression of some type and level. -/
abbrev SomeNeu (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Type :=
  (τ : Ty ks) × (ℓ : Nat) × Neu Δ Φ Γ τ ℓ

mutual
/-- How many times the call `s` occurs in a neutral expression. -/
def Neu.occ (s : ENeu Φ Γ σ) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Nat
  | _, _, m =>
    if s.test m then 1 else
    match m with
    | .var _ => 0
    | .data_out _ _ n => n.occ s
    | .cond c a b => c.occ s + a.occ s + b.occ s
    | .extern _ args _ => args.occ s
/-- `Neu.occ` in a pure expression. -/
def PExpr.occ (s : ENeu Φ Γ σ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Nat
  | _, _, .neu n => n.occ s
  | _, _, .record_mk args => args.occ s
  | _, _, .union_mk _ args => args.occ s
  | _, _, .array_mk es => es.occ s
  | _, _, .list_mk es => es.occ s
  | _, _, .data_in _ _ e => e.occ s
  | _, _, _ => 0
/-- `Neu.occ` in arguments. -/
def Args.occ (s : ENeu Φ Γ σ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Nat
  | _, _, .nil => 0
  | _, _, .cons a as => a.occ s + as.occ s
/-- `Neu.occ` in elements. -/
def Elems.occ (s : ENeu Φ Γ σ) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Nat
  | _, _, .nil => 0
  | _, _, .cons e es => e.occ s + es.occ s
end

mutual
/-- Is the call `s` computed whenever the neutral expression is (outside the arms of its
    conditionals)? -/
def Neu.always (s : ENeu Φ Γ σ) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Bool
  | _, _, m =>
    s.test m ||
    match m with
    | .var _ => false
    | .data_out _ _ n => n.always s
    | .cond c a b => c.always s || (a.always s && b.always s)
    | .extern _ args _ => args.always s
/-- `Neu.always` in a pure expression. -/
def PExpr.always (s : ENeu Φ Γ σ) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Bool
  | _, _, .neu n => n.always s
  | _, _, .record_mk args => args.always s
  | _, _, .union_mk _ args => args.always s
  | _, _, .array_mk es => es.always s
  | _, _, .list_mk es => es.always s
  | _, _, .data_in _ _ e => e.always s
  | _, _, _ => false
/-- `Neu.always` in arguments: in one of them. -/
def Args.always (s : ENeu Φ Γ σ) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Bool
  | _, _, .nil => false
  | _, _, .cons a as => a.always s || as.always s
/-- `Neu.always` in elements: in one of them. -/
def Elems.always (s : ENeu Φ Γ σ) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Bool
  | _, _, .nil => false
  | _, _, .cons e es => e.always s || es.always s
end

mutual
/-- The calls of externs on atoms in a neutral expression. -/
def Neu.cands : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → List (SomeNeu Δ Φ Γ)
  | _, _, m =>
    match ENeu.ofNeu? m with
    | some _ => [⟨_, _, m⟩]
    | none =>
      match m with
      | .var _ => []
      | .data_out _ _ n => n.cands
      | .cond c a b => c.cands ++ a.cands ++ b.cands
      | .extern _ args _ => args.cands
/-- `Neu.cands` in a pure expression. -/
def PExpr.cands : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → List (SomeNeu Δ Φ Γ)
  | _, _, .neu n => n.cands
  | _, _, .record_mk args => args.cands
  | _, _, .union_mk _ args => args.cands
  | _, _, .array_mk es => es.cands
  | _, _, .list_mk es => es.cands
  | _, _, .data_in _ _ e => e.cands
  | _, _, _ => []
/-- `Neu.cands` in arguments. -/
def Args.cands : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → List (SomeNeu Δ Φ Γ)
  | _, _, .nil => []
  | _, _, .cons a as => a.cands ++ as.cands
/-- `Neu.cands` in elements. -/
def Elems.cands : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → List (SomeNeu Δ Φ Γ)
  | _, _, .nil => []
  | _, _, .cons e es => e.cands ++ es.cands
end

end Counts

end LeanScript

end
