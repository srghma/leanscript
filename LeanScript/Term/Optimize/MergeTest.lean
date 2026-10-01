module

public import LeanScript.Term.Optimize.ShareTest

@[expose] public section

set_option autoImplicit false

/-!
# Two tests that end in the same answer, merged into one condition

A decision tree translated from nested `if`s (or from a `match`) often ends two tests in the
same answer: the fall-through of a test inside an arm is also the fall-through of the test
around it.

```
if p then (if q then X else E)        if (p ? q : false) then X      -- p && q
     else E                     ⟹    else E

if p then E                           if (p ? true : q) then E       -- p || q
     else (if q then E else X)  ⟹    else X
```

`Branch.mergeTest p t e` makes these two rewrites, when the shared arm `E` is the same answer
`ret a` or the same jump `jump j a` in both places (`Term.sameTail`, a syntactic comparison
that implies the same value), and the same with `!q` when `E` is the other arm of the inner
test (`if p then (if q then E else X) else E` is `if (p && !q) then X else E`; `Neu.mkNot`).
The inner test may be the conditional answer `ret (q ? a : b)`, read as
`if q then ret a else ret b` (`Term.testView?`): `if a then 1 else (b ? 1 : 2)` is
`if (a || b) then 1 else 2`, which `Term.cseWalk` then writes `ret ((a || b) ? 1 : 2)`.  The condition is the pure conditional `Neu.cond`, which the
JavaScript printer writes `p && q` (`p ? q : false`) and `p || q` (`p ? true : q`).  A chain is
grouped to the left (`Neu.mkAnd`, `Neu.mkOr`): `p && (q₁ && q₂)` is `(p && q₁) && q₂`.

**Why the value is the same.**  The language is pure and total: `q` is evaluated (in
JavaScript, by the operator) exactly when the original evaluated the inner test, and both
programs then end in `X` or in (a copy of) `E`.  No test is added on any path, and a test and
one copy of `E` are dropped.

This is the rewrite the JavaScript backend made on its own grammar (`MoreJs.JsBlock.mergeIte`);
made here, on `Term`, it applies to every target.  The JavaScript pass is kept for the shared
arms that are more than an answer or a jump.

The rewrite is proved to preserve the value (`Branch.mergeTest_eval`) and to add no call
(`Branch.numCalls_mergeTest`).  `Term.mergeTestWalk` applies it at every `if`, bottom-up
(`Term.mergeTestWalk_eval`, `Term.numCalls_mergeTestWalk`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Conjunctions and disjunctions, grouped to the left -/

section Conn
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The neutral expression a pure expression is, if it is one. -/
def PExpr.neu? {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Option ((ℓ : Nat) × Neu Δ Φ Γ τ ℓ)
  | .neu n => some ⟨_, n⟩
  | _ => none

theorem PExpr.neu?_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o) (ℓ : Nat)
    (n : Neu Δ Φ Γ τ ℓ) (h : e.neu? = some ⟨ℓ, n⟩) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    e.eval κ ρ = n.eval κ ρ := by
  cases e with
  | neu n' =>
    simp only [PExpr.neu?, Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl
  | _ => simp [PExpr.neu?] at h

/-- A pair of conditions. -/
abbrev CondPair (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) :=
  (ℓ₁ : Nat) × Neu Δ Φ Γ .bool ℓ₁ × (ℓ₂ : Nat) × Neu Δ Φ Γ .bool ℓ₂

/-- `(q₁, q₂)` when the condition is `q₁ && q₂` (`q₁ ? q₂ : false`, `q₂` neutral). -/
def Neu.andView? {ℓ : Nat} : Neu Δ Φ Γ .bool ℓ → Option (CondPair Δ Φ Γ)
  | .cond q₁ a b =>
    if b.boolLit? = some false then a.neu?.map fun q₂ => ⟨_, q₁, q₂.1, q₂.2⟩ else none
  | _ => none

/-- `(q₁, q₂)` when the condition is `q₁ || q₂` (`q₁ ? true : q₂`, `q₂` neutral). -/
def Neu.orView? {ℓ : Nat} : Neu Δ Φ Γ .bool ℓ → Option (CondPair Δ Φ Γ)
  | .cond q₁ a b =>
    if a.boolLit? = some true then b.neu?.map fun q₂ => ⟨_, q₁, q₂.1, q₂.2⟩ else none
  | _ => none

theorem Neu.andView?_eval {ℓ : Nat} (q : Neu Δ Φ Γ .bool ℓ) (v : CondPair Δ Φ Γ)
    (h : q.andView? = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (q.eval κ ρ : Bool) = ((v.2.1.eval κ ρ : Bool) && (v.2.2.2.eval κ ρ : Bool)) := by
  unfold Neu.andView? at h
  split at h
  · rename_i q₁ a b
    split at h
    · rename_i hl
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨ℓ₂, q₂⟩, hn, rfl⟩ := h
      have en := PExpr.neu?_eval a ℓ₂ q₂ hn κ ρ
      have el := PExpr.boolLit?_eval b false hl κ ρ
      simp only [Neu.eval]
      split <;> simp_all <;> rfl
    · cases h
  · cases h

theorem Neu.orView?_eval {ℓ : Nat} (q : Neu Δ Φ Γ .bool ℓ) (v : CondPair Δ Φ Γ)
    (h : q.orView? = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (q.eval κ ρ : Bool) = ((v.2.1.eval κ ρ : Bool) || (v.2.2.2.eval κ ρ : Bool)) := by
  unfold Neu.orView? at h
  split at h
  · rename_i q₁ a b
    split at h
    · rename_i hl
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨ℓ₂, q₂⟩, hn, rfl⟩ := h
      have en := PExpr.neu?_eval b ℓ₂ q₂ hn κ ρ
      have el := PExpr.boolLit?_eval a true hl κ ρ
      simp only [Neu.eval]
      split <;> simp_all <;> rfl
    · cases h
  · cases h

/-- `p && q` (`p ? q : false`), grouped to the left: `p && (q₁ && q₂)` is `(p && q₁) && q₂`
    (as deep as `fuel`). -/
def Neu.mkAnd {ℓ₁ : Nat} (p : Neu Δ Φ Γ .bool ℓ₁) : Nat → {ℓ₂ : Nat} → Neu Δ Φ Γ .bool ℓ₂ →
    (ℓ : Nat) × Neu Δ Φ Γ .bool ℓ
  | 0, _, q => ⟨_, .cond p (.neu q) (.lit .bool false)⟩
  | fuel + 1, _, q => match q.andView? with
    | some v => ⟨_, .cond (Neu.mkAnd p fuel v.2.1).2 (.neu v.2.2.2) (.lit .bool false)⟩
    | none => ⟨_, .cond p (.neu q) (.lit .bool false)⟩

/-- `p || q` (`p ? true : q`), grouped to the left: `p || (q₁ || q₂)` is `(p || q₁) || q₂`
    (as deep as `fuel`). -/
def Neu.mkOr {ℓ₁ : Nat} (p : Neu Δ Φ Γ .bool ℓ₁) : Nat → {ℓ₂ : Nat} → Neu Δ Φ Γ .bool ℓ₂ →
    (ℓ : Nat) × Neu Δ Φ Γ .bool ℓ
  | 0, _, q => ⟨_, .cond p (.lit .bool true) (.neu q)⟩
  | fuel + 1, _, q => match q.orView? with
    | some v => ⟨_, .cond (Neu.mkOr p fuel v.2.1).2 (.lit .bool true) (.neu v.2.2.2)⟩
    | none => ⟨_, .cond p (.lit .bool true) (.neu q)⟩

theorem Neu.mkAnd_eval {ℓ₁ : Nat} (p : Neu Δ Φ Γ .bool ℓ₁) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (fuel : Nat) → {ℓ₂ : Nat} → (q : Neu Δ Φ Γ .bool ℓ₂) →
    ((p.mkAnd fuel q).2.eval κ ρ : Bool) = ((p.eval κ ρ : Bool) && (q.eval κ ρ : Bool))
  | 0, _, q => by
    simp only [Neu.mkAnd, Neu.eval, PExpr.eval]
    cases (p.eval κ ρ : Bool) <;> rfl
  | fuel + 1, _, q => by
    simp only [Neu.mkAnd]
    split
    · rename_i v hv
      have e := Neu.andView?_eval q v hv κ ρ
      have ih := Neu.mkAnd_eval p κ ρ fuel v.2.1
      simp only [Neu.eval, PExpr.eval, ih, e]
      cases (p.eval κ ρ : Bool) <;> cases (v.2.1.eval κ ρ : Bool) <;> rfl
    · simp only [Neu.eval, PExpr.eval]
      cases (p.eval κ ρ : Bool) <;> rfl

theorem Neu.mkOr_eval {ℓ₁ : Nat} (p : Neu Δ Φ Γ .bool ℓ₁) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (fuel : Nat) → {ℓ₂ : Nat} → (q : Neu Δ Φ Γ .bool ℓ₂) →
    ((p.mkOr fuel q).2.eval κ ρ : Bool) = ((p.eval κ ρ : Bool) || (q.eval κ ρ : Bool))
  | 0, _, q => by
    simp only [Neu.mkOr, Neu.eval, PExpr.eval]
    cases (p.eval κ ρ : Bool) <;> rfl
  | fuel + 1, _, q => by
    simp only [Neu.mkOr]
    split
    · rename_i v hv
      have e := Neu.orView?_eval q v hv κ ρ
      have ih := Neu.mkOr_eval p κ ρ fuel v.2.1
      simp only [Neu.eval, PExpr.eval, ih, e]
      cases (p.eval κ ρ : Bool) <;> cases (v.2.1.eval κ ρ : Bool) <;> rfl
    · simp only [Neu.eval, PExpr.eval]
      cases (p.eval κ ρ : Bool) <;> rfl

end Conn


/-! ## Negations -/

section Not
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- `!q` (`q ? false : true`), or `c` when `q` is `!c` already. -/
def Neu.mkNot {ℓ : Nat} (q : Neu Δ Φ Γ .bool ℓ) : (ℓ' : Nat) × Neu Δ Φ Γ .bool ℓ' :=
  match q.negView? with
  | some c => ⟨_, c⟩
  | none => ⟨_, .cond q (.lit .bool false) (.lit .bool true)⟩

theorem Neu.mkNot_eval {ℓ : Nat} (q : Neu Δ Φ Γ .bool ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    ((Neu.mkNot q).2.eval κ ρ : Bool) = !(q.eval κ ρ : Bool) := by
  unfold Neu.mkNot
  split
  · rename_i c hc
    rw [Neu.negView?_eval q c hc κ ρ]
    cases (c.eval κ ρ : Bool) <;> rfl
  · simp only [Neu.eval, PExpr.eval]
    cases (q.eval κ ρ : Bool) <;> rfl

end Not

/-! ## The rewrite -/

section Rewrite
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- How deep a chain of `&&` (`||`) is grouped to the left. -/
def mergeTestFuel : Nat := 64

/-- `if p then t else E`, when `t` is `if q then X else E` (resp. `if q then E else X`), as
    `if (p && q) then X else E` (resp. `if (p && !q) then X else E`).  The arm `t` may be the
    conditional answer `ret (q ? a : b)`, read as `if q then ret a else ret b`
    (`Term.testView?`). -/
def Branch.mergeAnd? {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    Option (Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) :=
  match t.testView? with
  | some v =>
    if v.e.sameTail e then
      let b := Branch.ite (p.mkAnd mergeTestFuel v.q).2 v.t v.e
      if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then some (b.castLvlC h) else none
    else if v.t.sameTail e then
      let b := Branch.ite (p.mkAnd mergeTestFuel (Neu.mkNot v.q).2).2 v.e v.t
      if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then some (b.castLvlC h) else none
    else none
  | none => none

/-- `if p then E else e`, when `e` is `if q then E else X` (resp. `if q then X else E`), as
    `if (p || q) then E else X` (resp. `if (p || !q) then E else X`).  The arm `e` may be the
    conditional answer `ret (q ? a : b)` (`Term.testView?`). -/
def Branch.mergeOr? {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    Option (Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) :=
  match e.testView? with
  | some v =>
    if t.sameTail v.t then
      let b := Branch.ite (p.mkOr mergeTestFuel v.q).2 t v.e
      if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then some (b.castLvlC h) else none
    else if t.sameTail v.e then
      let b := Branch.ite (p.mkOr mergeTestFuel (Neu.mkNot v.q).2).2 t v.t
      if h : _ = Lvl.meetL ℓ (Lvl.meet o₁ o₂) then some (b.castLvlC h) else none
    else none
  | none => none

/-- `if p then t else e`, with two tests that end in the same answer merged into one condition
    (`Branch.mergeAnd?`, then `Branch.mergeOr?`):
    `if p then (if q then X else E) else E` is `if (p && q) then X else E`, and
    `if p then E else (if q then E else X)` is `if (p || q) then E else X` (and the same with
    `!q` when `E` is the other arm of the inner test). -/
def Branch.mergeTest {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂)) :=
  match Branch.mergeAnd? p t e with
  | some b => b
  | none => match Branch.mergeOr? p t e with
    | some b => b
    | none => .ite p t e

theorem Branch.mergeAnd?_eval {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂)
    (b : Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) (hb : Branch.mergeAnd? p t e = some b)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    b.eval κ ρ jκ = (Branch.ite p t e).eval κ ρ jκ := by
  unfold Branch.mergeAnd? at hb
  split at hb
  · rename_i v hv
    have et := Term.testView?_eval t v hv κ ρ jκ
    split at hb
    · rename_i hs
      have es := Term.sameTail_eval v.e e hs κ ρ jκ
      split at hb
      · cases hb
        rw [Branch.castLvlC_eval]
        simp only [Branch.eval] at et ⊢
        rw [et, Neu.mkAnd_eval]
        cases (p.eval κ ρ : Bool) <;> cases (v.q.eval κ ρ : Bool) <;> simp [es]
      · cases hb
    · split at hb
      · rename_i _ hs
        have es := Term.sameTail_eval v.t e hs κ ρ jκ
        split at hb
        · cases hb
          rw [Branch.castLvlC_eval]
          simp only [Branch.eval] at et ⊢
          rw [et, Neu.mkAnd_eval, Neu.mkNot_eval]
          cases (p.eval κ ρ : Bool) <;> cases (v.q.eval κ ρ : Bool) <;> simp [es]
        · cases hb
      · cases hb
  · cases hb

theorem Branch.mergeOr?_eval {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂)
    (b : Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) (hb : Branch.mergeOr? p t e = some b)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    b.eval κ ρ jκ = (Branch.ite p t e).eval κ ρ jκ := by
  unfold Branch.mergeOr? at hb
  split at hb
  · rename_i v hv
    have ee := Term.testView?_eval e v hv κ ρ jκ
    split at hb
    · rename_i hs
      have es := Term.sameTail_eval t v.t hs κ ρ jκ
      split at hb
      · cases hb
        rw [Branch.castLvlC_eval]
        simp only [Branch.eval] at ee ⊢
        rw [ee, Neu.mkOr_eval]
        cases (p.eval κ ρ : Bool) <;> cases (v.q.eval κ ρ : Bool) <;> simp [es]
      · cases hb
    · split at hb
      · rename_i _ hs
        have es := Term.sameTail_eval t v.e hs κ ρ jκ
        split at hb
        · cases hb
          rw [Branch.castLvlC_eval]
          simp only [Branch.eval] at ee ⊢
          rw [ee, Neu.mkOr_eval, Neu.mkNot_eval]
          cases (p.eval κ ρ : Bool) <;> cases (v.q.eval κ ρ : Bool) <;> simp [es]
        · cases hb
      · cases hb
  · cases hb

theorem Branch.mergeTest_eval {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) :
    (Branch.mergeTest p t e).eval κ ρ jκ = (Branch.ite p t e).eval κ ρ jκ := by
  unfold Branch.mergeTest
  split
  · rename_i b hb
    exact Branch.mergeAnd?_eval p t e b hb κ ρ jκ
  · split
    · rename_i b hb
      exact Branch.mergeOr?_eval p t e b hb κ ρ jκ
    · rfl

theorem Branch.numCalls_mergeAnd? {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂)
    (b : Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) (hb : Branch.mergeAnd? p t e = some b) :
    b.numCalls ≤ (Branch.ite p t e).numCalls := by
  unfold Branch.mergeAnd? at hb
  split at hb
  · rename_i v hv
    have ht := Term.testView?_numCalls t v hv
    split at hb
    · split at hb
      · cases hb
        rw [Branch.numCalls_castLvlC]
        simp only [Branch.numCalls]; omega
      · cases hb
    · split at hb
      · split at hb
        · cases hb
          rw [Branch.numCalls_castLvlC]
          simp only [Branch.numCalls]; omega
        · cases hb
      · cases hb
  · cases hb

theorem Branch.numCalls_mergeOr? {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂)
    (b : Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meet o₁ o₂))) (hb : Branch.mergeOr? p t e = some b) :
    b.numCalls ≤ (Branch.ite p t e).numCalls := by
  unfold Branch.mergeOr? at hb
  split at hb
  · rename_i v hv
    have he := Term.testView?_numCalls e v hv
    split at hb
    · split at hb
      · cases hb
        rw [Branch.numCalls_castLvlC]
        simp only [Branch.numCalls]; omega
      · cases hb
    · split at hb
      · split at hb
        · cases hb
          rw [Branch.numCalls_castLvlC]
          simp only [Branch.numCalls]; omega
        · cases hb
      · cases hb
  · cases hb

theorem Branch.numCalls_mergeTest {ℓ : Nat} {o₁ o₂ : Lvl} (p : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    (Branch.mergeTest p t e).numCalls ≤ (Branch.ite p t e).numCalls := by
  unfold Branch.mergeTest
  split
  · rename_i b hb
    exact Branch.numCalls_mergeAnd? p t e b hb
  · split
    · rename_i b hb
      exact Branch.numCalls_mergeOr? p t e b hb
    · exact Nat.le_refl _

end Rewrite

/-! ## The walk -/

mutual
/-- `Term.mergeTestWalk` in a value. -/
def Val.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.mergeTestWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.mergeTestWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.mergeTestWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.mergeTestWalk` in a body. -/
def Body.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.mergeTestWalk
  | _, _, _, _, _, _, .opened t h => .opened t.mergeTestWalk h
/-- `Term.mergeTestWalk` in a computation. -/
def Comp.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.mergeTestWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.mergeTestWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).mergeTestWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).mergeTestWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Two tests that end in the same answer are merged into one condition**
    (`Branch.mergeTest`), at every `if` of a statement, bottom-up. -/
def Term.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.mergeTestWalk b.mergeTestWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.mergeTestWalk b.mergeTestWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.mergeTestWalk
  | _, _, _, _, _, _, .branch br => .branch br.mergeTestWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.mergeTestWalk` in a branch. -/
def Branch.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => Branch.mergeTest c t.mergeTestWalk e.mergeTestWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).mergeTestWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.mergeTestWalk
  | _, _, _, _, _, _, .join σ u uₓ body main =>
      .join σ u uₓ body.mergeTestWalk main.mergeTestWalk
/-- `Term.mergeTestWalk` in the branches of a union's case analysis. -/
def Branches.mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ =>
      .two us₁ us₂ b₁.mergeTestWalk b₂.mergeTestWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.mergeTestWalk bs.mergeTestWalk
end

mutual
theorem Val.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.mergeTestWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.mergeTestWalk, Val.eval]; funext x; rw [Body.mergeTestWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.mergeTestWalk, Val.eval]; rw [Body.mergeTestWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.mergeTestWalk, Val.eval]; rw [Body.mergeTestWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.mergeTestWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.mergeTestWalk, Body.eval]; exact Term.mergeTestWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.mergeTestWalk, Body.eval]; exact Term.mergeTestWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.mergeTestWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.mergeTestWalk, Comp.eval]
      congr 1; funext k acc; exact Body.mergeTestWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.mergeTestWalk, Comp.eval]
      congr 1; funext acc x; exact Body.mergeTestWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.mergeTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.mergeTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.mergeTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.mergeTestWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
/-- **Merging two tests that end in the same answer does not change the value of a
    statement.** -/
theorem Term.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.mergeTestWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.mergeTestWalk, Term.eval, Val.mergeTestWalk_eval v,
        Term.mergeTestWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.mergeTestWalk, Term.eval, Comp.mergeTestWalk_eval c,
        Term.mergeTestWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.mergeTestWalk, Term.eval, Term.mergeTestWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.mergeTestWalk, Term.eval, Branch.mergeTestWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.mergeTestWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.mergeTestWalk]
      rw [Branch.mergeTest_eval]
      simp only [Branch.eval, Term.mergeTestWalk_eval t, Term.mergeTestWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.mergeTestWalk, Branch.eval]
      exact Term.mergeTestWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.mergeTestWalk, Branch.eval]
      exact Branches.mergeTestWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.mergeTestWalk, Branch.eval, Branch.mergeTestWalk_eval main,
        Term.mergeTestWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.mergeTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.mergeTestWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.mergeTestWalk, Branches.eval, Term.mergeTestWalk_eval b₁,
        Term.mergeTestWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.mergeTestWalk, Branches.eval, Term.mergeTestWalk_eval b,
        Branches.mergeTestWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.mergeTestWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.mergeTestWalk, Val.numCalls]; exact Body.numCalls_mergeTestWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.mergeTestWalk, Val.numCalls]; exact Body.numCalls_mergeTestWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.mergeTestWalk, Val.numCalls]; exact Body.numCalls_mergeTestWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.mergeTestWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.mergeTestWalk, Body.numCalls]; exact Term.numCalls_mergeTestWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.mergeTestWalk, Body.numCalls]; exact Term.numCalls_mergeTestWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.mergeTestWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.mergeTestWalk, Comp.numCalls]; exact Body.numCalls_mergeTestWalk s
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.mergeTestWalk, Comp.numCalls]; exact Body.numCalls_mergeTestWalk s
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.mergeTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_mergeTestWalk (brs i))
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.mergeTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_mergeTestWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    t.mergeTestWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV _ v b => by
      have := Val.numCalls_mergeTestWalk v
      have := Term.numCalls_mergeTestWalk b
      simp only [Term.mergeTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE _ c b => by
      have := Comp.numCalls_mergeTestWalk c
      have := Term.numCalls_mergeTestWalk b
      simp only [Term.mergeTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn _ _ b => by
      simp only [Term.mergeTestWalk, Term.numCalls]; exact Term.numCalls_mergeTestWalk b
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.mergeTestWalk, Term.numCalls]; exact Branch.numCalls_mergeTestWalk br
  | _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.mergeTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have := Branch.numCalls_mergeTest c t.mergeTestWalk e.mergeTestWalk
      have := Term.numCalls_mergeTestWalk t
      have := Term.numCalls_mergeTestWalk e
      simp only [Branch.mergeTestWalk, Branch.numCalls] at *; omega
  | _, _, _, _, _, _, .enum_casesOn _ bs => by
      simp only [Branch.mergeTestWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_mergeTestWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn _ bs => by
      simp only [Branch.mergeTestWalk, Branch.numCalls]; exact Branches.numCalls_mergeTestWalk bs
  | _, _, _, _, _, _, .join _ _ _ body main => by
      have := Term.numCalls_mergeTestWalk body
      have := Branch.numCalls_mergeTestWalk main
      simp only [Branch.mergeTestWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_mergeTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.mergeTestWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => by
      have := Term.numCalls_mergeTestWalk b₁
      have := Term.numCalls_mergeTestWalk b₂
      simp only [Branches.mergeTestWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons _ b bs => by
      have := Term.numCalls_mergeTestWalk b
      have := Branches.numCalls_mergeTestWalk bs
      simp only [Branches.mergeTestWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
