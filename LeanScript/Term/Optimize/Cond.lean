module

public import LeanScript.Term.Semantics.Eval
public import LeanScript.Term.Optimize.Count
public import LeanScript.Term.Optimize.Fold
public import LeanScript.Term.Optimize.StrMap

@[expose] public section

set_option autoImplicit false

/-!
# Boolean conditions

Two rewrites of the pure conditional `Neu.cond` (`c ? a : b`) and of `if`, each proved to
preserve the value (`Term.condWalk_eval`), both target-agnostic (they were done by the
JavaScript backend on its own grammar before, `MoreJs.condNode`, and by its printer):

* `c ? true : false` is `c` (`Neu.mkCond`);
* a condition that is a negation, `c ? false : true`, is `c` with the two branches swapped:
  `(c ? false : true) ? a : b` is `c ? b : a` (`Neu.mkCond`), and
  `if (c ? false : true) then t else e` is `if c then e else t` (`Branch.mkIte`).
* the negation of a conditional one of whose arms is a literal is pushed into its arms:
  `(p ? false : q) ? false : true` is `p ? true : (q ? false : true)` (`Neu.condOfCond?`).

It also answers a test of a key of a hash map with string keys, the case analysis of `m[k]?`
whose arms answer Boolean literals, by `m.contains k` (`Term.ofBranchStrMap`,
`LeanScript.Term.Optimize.StrMap`).

Both keep the level index (a literal is closed, so `c ? true : false` has the level of `c`;
swapping the branches changes the level only up to `Lvl.meet_comm`, which a cast takes care
of).  `Term.condWalk` applies them bottom-up everywhere (in every pure expression, closure,
loop body, branch and join point); it adds no call (`Term.numCalls_condWalk`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Levels -/

theorem Lvl.meet_comm (o₁ o₂ : Lvl) : Lvl.meet o₁ o₂ = Lvl.meet o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp [Lvl.meet, Nat.min_comm]

/-- A neutral expression at an equal level. -/
def Neu.castLvlC {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (n : Neu Δ Φ Γ τ ℓ) : Neu Δ Φ Γ τ ℓ' := h ▸ n

theorem Neu.castLvlC_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (n.castLvlC h).eval κ ρ = n.eval κ ρ := by
  subst h; rfl

/-- A branch at an equal level. -/
def Branch.castLvlC {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ ℓ' : Nat}
    (h : ℓ = ℓ') (b : Branch Δ d Φ Γ τ js ℓ) : Branch Δ d Φ Γ τ js ℓ' := h ▸ b

theorem Branch.castLvlC_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ ℓ' : Nat} (h : ℓ = ℓ') (b : Branch Δ d Φ Γ τ js ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : (b.castLvlC h).eval κ ρ jκ = b.eval κ ρ jκ := by
  subst h; rfl

/-! ## Boolean literals and negations -/

/-- `c` when the condition is `c ? false : true`, the negation of `c`. -/
def Neu.negView? {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} :
    Neu Δ Φ Γ .bool ℓ → Option (Neu Δ Φ Γ .bool ℓ)
  | .cond (o₁ := none) (o₂ := none) c a b =>
    if a.boolLit? = some false ∧ b.boolLit? = some true then some c else none
  | _ => none

theorem Neu.negView?_eval {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} (n c : Neu Δ Φ Γ .bool ℓ)
    (h : n.negView? = some c) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (n.eval κ ρ : Bool) = !(c.eval κ ρ : Bool) := by
  unfold Neu.negView? at h
  split at h
  · rename_i a b
    split at h
    · rename_i hab
      cases h
      simp only [Neu.eval, PExpr.boolLit?_eval a false hab.1, PExpr.boolLit?_eval b true hab.2]
      split <;> simp_all <;> rfl
    · cases h
  · cases h

/-! ## The rewrites -/

/-- `c ? a : b`, with `c ? true : false` as `c`. -/
def Neu.mkCondLit {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} :
    {τ : Ty ks} → {o₁ o₂ : Lvl} → Neu Δ Φ Γ .bool ℓ → PExpr Δ Φ Γ τ o₁ → PExpr Δ Φ Γ τ o₂ →
    Neu Δ Φ Γ τ (Lvl.meetL ℓ (Lvl.meet o₁ o₂))
  | .prim .bool, none, none, c, a, b =>
    if a.boolLit? = some true ∧ b.boolLit? = some false then c else .cond c a b
  | _, _, _, c, a, b => .cond c a b

theorem Neu.mkCondLit_eval {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} {τ : Ty ks} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : (Neu.mkCondLit c a b).eval κ ρ = (Neu.cond c a b).eval κ ρ := by
  cases τ with
  | prim p =>
    cases p
    case bool =>
      cases o₁ <;> cases o₂
      case none.none =>
        by_cases hab : a.boolLit? = some true ∧ b.boolLit? = some false
        · have e : Neu.mkCondLit c a b = c := by simp [Neu.mkCondLit, hab] <;> rfl
          rw [e]
          simp only [Neu.eval, PExpr.boolLit?_eval _ true hab.1, PExpr.boolLit?_eval _ false hab.2]
          split <;> assumption
        · have e : Neu.mkCondLit c a b = .cond c a b := by simp [Neu.mkCondLit, hab] <;> rfl
          rw [e]
      all_goals rfl
    all_goals rfl
  | _ => rfl

/-- `c ? a : b`, with `c ? true : false` as `c`, and a negated condition read as the
    condition with the branches swapped. -/
def Neu.mkCondNeg {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) :
    Neu Δ Φ Γ τ (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) :=
  match c.negView? with
  | some c' => (Neu.cond c' b a).castLvlC (by rw [Lvl.meet_comm])
  | none => Neu.mkCondLit c a b

theorem Neu.mkCondNeg_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : (Neu.mkCondNeg c a b).eval κ ρ = (Neu.cond c a b).eval κ ρ := by
  unfold Neu.mkCondNeg
  split
  · rename_i c' hc
    rw [Neu.castLvlC_eval]
    simp only [Neu.eval, Neu.negView?_eval c c' hc κ ρ]
    split <;> rename_i h <;> simp [h]
  · exact Neu.mkCondLit_eval c a b κ ρ

/-- Is the neutral expression an unknown? -/
def Neu.isVarB {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Bool
  | .var _ => true
  | _ => false

/-- Is the pure expression an unknown? -/
def PExpr.isVarB {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Bool
  | .neu (.var _) => true
  | _ => false

/-- `x ? a : b` for a Boolean `x` that is a literal (its arm) or neutral (`Neu.mkCondLit`). -/
def PExpr.condArm? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ox o₁ o₂ : Lvl}
    (x : PExpr Δ Φ Γ .bool ox) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) :
    Option ((o : Lvl) × PExpr Δ Φ Γ τ o) :=
  match x.boolLit? with
  | some v => some (if v then ⟨_, a⟩ else ⟨_, b⟩)
  | none =>
      match x with
      | .neu n => some ⟨_, .neu (Neu.mkCondLit n a b)⟩
      | _ => none

theorem PExpr.condArm?_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ox o₁ o₂ : Lvl}
    (x : PExpr Δ Φ Γ .bool ox) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂)
    {r : (o : Lvl) × PExpr Δ Φ Γ τ o} (h : x.condArm? a b = some r) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) :
    r.2.eval κ ρ = match (x.eval κ ρ : Bool) with
      | true => a.eval κ ρ
      | false => b.eval κ ρ := by
  unfold PExpr.condArm? at h
  split at h
  · rename_i v hv
    cases h
    rw [PExpr.boolLit?_eval x v hv κ ρ]
    cases v <;> rfl
  · split at h
    · rename_i n _
      cases h
      simp only [PExpr.eval]
      rw [Neu.mkCondLit_eval]
      rfl
    · cases h

/-- The negation `(c₀ ? x : y) ? false : true` of a conditional one of whose arms is a literal:
    `c₀ ? !x : !y`, the literal arm negated (`PExpr.condArm?`).  So the negation of
    `p ? false : q` is `p ? true : !q`, which JavaScript writes `p || !q`: `!(compare a b == .eq)`
    on `Nat` is `a < b || a !== b`.  Not done when the condition and an arm are unknowns, whose
    conditional the JavaScript backend writes as a comparison of booleans (`!(a < b)` on `Bool`
    is `a >= b`, `JsTerm.Lower.BoolCmp`). -/
def Neu.condOfCond? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) :
    Option ((ℓ' : Nat) × Neu Δ Φ Γ τ ℓ') :=
  if a.boolLit? = some false ∧ b.boolLit? = some true then
    match c with
    | .cond c₀ x y =>
        if (x.boolLit?.isSome || y.boolLit?.isSome) && !(c₀.isVarB && (x.isVarB || y.isVarB)) then
          match x.condArm? a b, y.condArm? a b with
          | some ax, some ay => some ⟨_, .cond c₀ ax.2 ay.2⟩
          | _, _ => none
        else none
    | _ => none
  else none

theorem Neu.condOfCond?_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂)
    {r : (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ'} (h : Neu.condOfCond? c a b = some r) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : r.2.eval κ ρ = (Neu.cond c a b).eval κ ρ := by
  unfold Neu.condOfCond? at h
  split at h
  · split at h
    · rename_i c₀ x y
      split at h
      · split at h
        · rename_i ax ay hx hy
          cases h
          simp only [Neu.eval]
          cases hc : (c₀.eval κ ρ : Bool) with
          | true =>
              simp only
              exact PExpr.condArm?_eval x a b hx κ ρ
          | false =>
              simp only
              exact PExpr.condArm?_eval y a b hy κ ρ
        · cases h
      · cases h
    · cases h
  · cases h

/-- `c ? a : b`, with `c ? true : false` as `c`, a negated condition read as the condition with
    the branches swapped (`Neu.mkCondNeg`), and the negation of a conditional with a literal arm
    pushed into its arms (`Neu.condOfCond?`, when the level comes out the same). -/
def Neu.mkCond {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) :
    Neu Δ Φ Γ τ (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) :=
  match Neu.condOfCond? c a b with
  | some r => if h : r.1 = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then h ▸ r.2 else Neu.mkCondNeg c a b
  | none => Neu.mkCondNeg c a b

theorem Neu.mkCond_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} {o₁ o₂ : Lvl}
    (c : Neu Δ Φ Γ .bool ℓ) (a : PExpr Δ Φ Γ τ o₁) (b : PExpr Δ Φ Γ τ o₂) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : (Neu.mkCond c a b).eval κ ρ = (Neu.cond c a b).eval κ ρ := by
  unfold Neu.mkCond
  split
  · rename_i r hr
    split
    · rename_i h
      obtain ⟨ℓ', m⟩ := r
      simp only at h
      subst h
      exact Neu.condOfCond?_eval c a b hr κ ρ
    · exact Neu.mkCondNeg_eval c a b κ ρ
  · exact Neu.mkCondNeg_eval c a b κ ρ

/-- `if c then t else e`, with a negated condition read as the condition with the branches
    swapped. -/
def Branch.mkIte {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) :=
  match c.negView? with
  | some c' => (Branch.ite c' e t).castLvlC (by rw [Lvl.meet_comm])
  | none => .ite c t e

theorem Branch.mkIte_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Branch.mkIte c t e).eval κ ρ jκ = (Branch.ite c t e).eval κ ρ jκ := by
  unfold Branch.mkIte
  split
  · rename_i c' hc
    rw [Branch.castLvlC_eval]
    simp only [Branch.eval, Neu.negView?_eval c c' hc κ ρ]
    split <;> rename_i h <;> simp [h]
  · rfl

/-! ## The walk -/

mutual
/-- `Neu.mkCond` everywhere in a neutral expression, bottom-up. -/
def Neu.condWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j e => .data_out b j e.condWalk
  | _, _, .cond c a b => Neu.mkCond c.condWalk a.condWalk b.condWalk
  | _, _, .extern e args h => .extern e args.condWalk h
/-- `Neu.condWalk` in a pure expression. -/
def PExpr.condWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu n.condWalk
  | _, _, .kvar k => .kvar k
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk args.condWalk
  | _, _, .union_mk ix args => .union_mk ix args.condWalk
  | _, _, .array_mk es => .array_mk es.condWalk
  | _, _, .list_mk es => .list_mk es.condWalk
  | _, _, .data_in b j e => .data_in b j e.condWalk
/-- `Neu.condWalk` in arguments. -/
def Args.condWalk {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons a.condWalk as.condWalk
/-- `Neu.condWalk` in the elements of a literal. -/
def Elems.condWalk {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons e.condWalk es.condWalk
end

mutual
theorem Neu.condWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    (n : Neu Δ Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → n.condWalk.eval κ ρ = n.eval κ ρ
  | _, _, .var _, _, _ => rfl
  | _, _, .data_out b j e, κ, ρ => by
      simp only [Neu.condWalk, Neu.eval, Neu.condWalk_eval e]
  | _, _, .cond c a b, κ, ρ => by
      simp only [Neu.condWalk]
      rw [Neu.mkCond_eval]
      simp only [Neu.eval, Neu.condWalk_eval c, PExpr.condWalk_eval a, PExpr.condWalk_eval b]
  | _, _, .extern e args _, κ, ρ => by
      simp only [Neu.condWalk, Neu.eval, Args.condWalk_eval args] <;> rfl
theorem PExpr.condWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    (e : PExpr Δ Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → e.condWalk.eval κ ρ = e.eval κ ρ
  | _, _, .neu n, κ, ρ => by simp only [PExpr.condWalk, PExpr.eval, Neu.condWalk_eval n]
  | _, _, .kvar _, _, _ => rfl
  | _, _, .lit _ _, _, _ => rfl
  | _, _, .enum_mk _ _, _, _ => rfl
  | _, _, .record_mk args, κ, ρ => by
      simp only [PExpr.condWalk, PExpr.eval, Args.condWalk_eval args] <;> rfl
  | _, _, .union_mk _ args, κ, ρ => by
      simp only [PExpr.condWalk, PExpr.eval, Args.condWalk_eval args] <;> rfl
  | _, _, .array_mk es, κ, ρ => by
      simp only [PExpr.condWalk, PExpr.eval, Elems.condWalk_eval es] <;> rfl
  | _, _, .list_mk es, κ, ρ => by
      simp only [PExpr.condWalk, PExpr.eval, Elems.condWalk_eval es] <;> rfl
  | _, _, .data_in _ _ e, κ, ρ => by
      simp only [PExpr.condWalk, PExpr.eval, PExpr.condWalk_eval e]
theorem Args.condWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    (as : Args Δ Φ Γ σs o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → as.condWalk.eval κ ρ = as.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons a as, κ, ρ => by
      simp only [Args.condWalk, Args.eval, PExpr.condWalk_eval a, Args.condWalk_eval as]
theorem Elems.condWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ Φ Γ t o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → es.condWalk.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons e es, κ, ρ => by
      simp only [Elems.condWalk, Elems.eval, PExpr.condWalk_eval e, Elems.condWalk_eval es] <;> rfl
end

mutual
/-- `Term.condWalk` in a value. -/
def Val.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.condWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.condWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.condWalk
  | _, _, _, _, _, .record_mk args => .record_mk args.condWalk
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args.condWalk
  | _, _, _, _, _, .array_mk es => .array_mk es.condWalk
  | _, _, _, _, _, .list_mk es => .list_mk es.condWalk
  | _, _, _, _, _, .data_in b j e => .data_in b j e.condWalk
/-- `Term.condWalk` in a body. -/
def Body.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.condWalk
  | _, _, _, _, _, _, .opened t h => .opened t.condWalk h
/-- `Term.condWalk` in a computation. -/
def Comp.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f.condWalk a.condWalk h
  | _, _, _, _, _, .share n => .share n.condWalk
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n.condWalk z.condWalk s.condWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a.condWalk z.condWalk s.condWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).condWalk) j e.condWalk h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).condWalk) j e.condWalk h
  | _, _, _, _, _, .thunk_force e => .thunk_force e.condWalk
  | _, _, _, _, _, .lazy_force e => .lazy_force e.condWalk
/-- **Boolean conditions simplified** everywhere in a statement (`Neu.mkCond`,
    `Branch.mkIte`), bottom-up. -/
def Term.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e.condWalk
  | _, _, _, _, _, _, .letV u v b => .letV u v.condWalk b.condWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.condWalk b.condWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n.condWalk b.condWalk
  | _, _, _, _, _, _, .branch br => Term.ofBranchStrMap br.condWalk
  | _, _, _, _, _, _, .jump j e => .jump j e.condWalk
/-- `Term.condWalk` in a branch. -/
def Branch.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => Branch.mkIte c.condWalk t.condWalk e.condWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e.condWalk (fun i => (bs i).condWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e.condWalk bs.condWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.condWalk main.condWalk
/-- `Term.condWalk` in the branches of a union's case analysis. -/
def Branches.condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.condWalk b₂.condWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.condWalk bs.condWalk
end

mutual
theorem Val.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.condWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.condWalk, Val.eval]; funext x; rw [Body.condWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.condWalk, Val.eval]; rw [Body.condWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.condWalk, Val.eval]; rw [Body.condWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk args, κ, ρ => by
      simp only [Val.condWalk, Val.eval, Args.condWalk_eval args] <;> rfl
  | _, _, _, _, _, .union_mk _ args, κ, ρ => by
      simp only [Val.condWalk, Val.eval, Args.condWalk_eval args] <;> rfl
  | _, _, _, _, _, .array_mk es, κ, ρ => by
      simp only [Val.condWalk, Val.eval, Elems.condWalk_eval es] <;> rfl
  | _, _, _, _, _, .list_mk es, κ, ρ => by
      simp only [Val.condWalk, Val.eval, Elems.condWalk_eval es] <;> rfl
  | _, _, _, _, _, .data_in _ _ e, κ, ρ => by
      simp only [Val.condWalk, Val.eval, PExpr.condWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.condWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.condWalk, Body.eval]; exact Term.condWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.condWalk, Body.eval]; exact Term.condWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.condWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a _, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval f, PExpr.condWalk_eval a]
  | _, _, _, _, _, .share n, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, Neu.condWalk_eval n]
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval n, PExpr.condWalk_eval z]
      congr 1; funext k acc; exact Body.condWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval]
      rw [PExpr.condWalk_eval a κ ρ, PExpr.condWalk_eval z κ ρ]
      congr 1; funext acc x; exact Body.condWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval e]
      congr 1; funext i x; exact Body.condWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval e]
      congr 1; funext i x; exact Body.condWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force e, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval e]
  | _, _, _, _, _, .lazy_force e, κ, ρ => by
      simp only [Comp.condWalk, Comp.eval, PExpr.condWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.condWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, κ, ρ, _ => by
      simp only [Term.condWalk, Term.eval, PExpr.condWalk_eval e]
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.condWalk, Term.eval, Val.condWalk_eval v, Term.condWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.condWalk, Term.eval, Comp.condWalk_eval c, Term.condWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.condWalk, Term.eval, Neu.condWalk_eval n, Term.condWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.condWalk, Term.ofBranchStrMap_eval, Term.eval, Branch.condWalk_eval br]
  | _, _, _, _, _, _, .jump _ e, κ, ρ, jκ => by
      simp only [Term.condWalk, Term.eval, PExpr.condWalk_eval e]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.condWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.condWalk]
      rw [Branch.mkIte_eval]
      simp only [Branch.eval, Neu.condWalk_eval c, Term.condWalk_eval t, Term.condWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.condWalk, Branch.eval]; rw [Neu.condWalk_eval e]
      exact Term.condWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.condWalk, Branch.eval, Neu.condWalk_eval e]
      exact Branches.condWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.condWalk, Branch.eval, Branch.condWalk_eval main, Term.condWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.condWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.condWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.condWalk, Branches.eval, Term.condWalk_eval b₁, Term.condWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.condWalk, Branches.eval, Term.condWalk_eval b,
        Branches.condWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

theorem Branch.numCalls_castLvlC {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ ℓ' : Nat} (h : ℓ = ℓ') (b : Branch Δ d Φ Γ τ js ℓ) :
    (b.castLvlC h).numCalls = b.numCalls := by
  subst h; rfl

theorem Branch.numCalls_mkIte {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) (t : Term Δ d Φ Γ τ js o₁)
    (e : Term Δ d Φ Γ τ js o₂) :
    (Branch.mkIte c t e).numCalls = (Branch.ite c t e).numCalls := by
  unfold Branch.mkIte
  split
  · rw [Branch.numCalls_castLvlC]
    simp only [Branch.numCalls]; omega
  · rfl

mutual
theorem Val.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.condWalk.numCalls = v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.condWalk, Val.numCalls, Body.numCalls_condWalk b]
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.condWalk, Val.numCalls, Body.numCalls_condWalk b]
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.condWalk, Val.numCalls, Body.numCalls_condWalk b]
  | _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.condWalk.numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.condWalk, Body.numCalls, Term.numCalls_condWalk t]
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.condWalk, Body.numCalls, Term.numCalls_condWalk t]
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.condWalk.numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.condWalk, Comp.numCalls, Body.numCalls_condWalk s]
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.condWalk, Comp.numCalls, Body.numCalls_condWalk s]
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.condWalk, Comp.numCalls, Body.numCalls_condWalk]
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.condWalk, Comp.numCalls, Body.numCalls_condWalk]
  | _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.condWalk.numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, .letV _ v b => by
      simp only [Term.condWalk, Term.numCalls, Val.numCalls_condWalk v, Term.numCalls_condWalk b]
  | _, _, _, _, _, _, .letE _ c b => by
      simp only [Term.condWalk, Term.numCalls, Comp.numCalls_condWalk c, Term.numCalls_condWalk b]
  | _, _, _, _, _, _, .record_casesOn _ _ b => by
      simp only [Term.condWalk, Term.numCalls, Term.numCalls_condWalk b]
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.condWalk, Term.numCalls_ofBranchStrMap, Term.numCalls, Branch.numCalls_condWalk br]
  | _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → br.condWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.condWalk]
      rw [Branch.numCalls_mkIte]
      simp only [Branch.numCalls, Term.numCalls_condWalk t, Term.numCalls_condWalk e]
  | _, _, _, _, _, _, .enum_casesOn _ bs => by
      simp only [Branch.condWalk, Branch.numCalls, Term.numCalls_condWalk]
  | _, _, _, _, _, _, .union_casesOn _ bs => by
      simp only [Branch.condWalk, Branch.numCalls, Branches.numCalls_condWalk bs]
  | _, _, _, _, _, _, .join _ _ _ body main => by
      simp only [Branch.condWalk, Branch.numCalls, Term.numCalls_condWalk body,
        Branch.numCalls_condWalk main]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_condWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.condWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => by
      simp only [Branches.condWalk, Branches.numCalls, Term.numCalls_condWalk b₁,
        Term.numCalls_condWalk b₂]
  | _, _, _, _, _, _, _, _, .cons _ b bs => by
      simp only [Branches.condWalk, Branches.numCalls, Term.numCalls_condWalk b,
        Branches.numCalls_condWalk bs]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
