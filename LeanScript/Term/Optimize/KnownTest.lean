module

public import LeanScript.Term.Optimize.SameJump
public import LeanScript.Term.Optimize.ZipTest
public import LeanScript.Term.Optimize.InlineSubstEval
public import LeanScript.Term.Optimize.CountSubst

@[expose] public section

set_option autoImplicit false

/-!
# Tests whose answer is already known

`if c then (if c then X else Y) else (if c then Z else W)`: inside an arm of `if c` the value of
`c` is known, so the inner tests can be dropped, and the statement is
`if c then X else W`.  Lean writes such repeated tests when a condition is read again after an
`if` on it: `let r := { c := c, d := x }; if r.c then (if r.c then x else 0) else …`
(`Tests/SnapshotsMy/IfThenElseKnownField.lean`, the variants of
`Tests/SnapshotsPBOPure/InlineReferenceIfThenElse.lean`).

`Term.knownTestWalk facts t` walks a statement knowing, for some boolean unknowns, their value
(`BoolFact`: an unknown `x : UVar Γ .bool ℓ` and a boolean).  At `if c then t else e`:

* when `c` is a known unknown (or the negation `!x` of one, `Neu.negView?`), the `if` is replaced
  by the arm it takes (`Term.knownTestWalk` answers a statement of *another* level: the walk
  returns the level with the statement);
* otherwise `c` is first simplified under the facts (`Neu.condSimp`: `c && false`, `c || true`,
  `c && c`, `!c || c`, `c ? a : a`, known unknowns), then `t` is walked knowing what `c` holding
  tells (`Neu.factsOf`: both operands of `p && q`, the negated facts of `!p`) and `e` knowing what
  `c` failing tells (both operands of `p || q` false).

At type `Bool`, `if c then jump j a else jump j b` is `jump j (c ? a : b)` (`Term.mkIteJ`), and a
join point whose main statement is then `jump j v` is the value `v`, substituted when its
parameter is used once (`Term.joinOrLet`, `Term.letEOrSubst`): `&&` and `||` that Lean compiles
into join points become operators (`Tests/SnapshotsMy/PrimOpBooleanKnownField.lean`).

At any type, a join point whose main statement is `if c then (…; jump j a) else (…; jump j a)`,
both arms jumping with the same argument, possibly behind case analyses of records whose fields
are not used (`Branch.sameJumpArg?`, `LeanScript.Term.Optimize.SameJump`), is its body with `a`
for its parameter; and when both arms are the same statement ending in the jump
(`Term.zipTest`), the join point is written at that jump (`Term.inlineTailJump`,
`Term.joinViaZip`).  Both only when the parameter is used at most once (`Term.joinSame`): this is
what the sign test of the derived `Repr Int` becomes
(`Tests/SnapshotsPBOPure/KnownConstructor07.lean`, `Tests/SnapshotsMy/ReprSameJump.lean`).

The conditional answer `ret (c ? a : b)` on a known `c` is the answer `ret a` (or `ret b`).  The
facts are weakened under binders (`BoolFact.weaken`, `BoolFact.weakenN`), carried into open
bodies (whose environment extends the one where the facts hold) and dropped in closed bodies.  A
body or a value must keep its level (it is recorded in the known context, or in the side
conditions of a computation): when the walked body has another level, the original body is kept.

**Proved:** `Term.knownTests_eval` (the value does not change) and `Term.numCalls_knownTests` (no
call is added: an arm is dropped, nothing is copied).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Both arms jump to the same join point -/

section Jumps
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}

/-- `if c then jump j a else jump j b` is `jump j (c ? a : b)`, for a boolean parameter. -/
def Term.mergeJumps? {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ) :
    Term Δ d Φ Γ τ js o₁ → Term Δ d Φ Γ τ js o₂ → Option ((o : Lvl) × Term Δ d Φ Γ τ js o)
  | .jump (σ := σ) j₁ a, .jump j₂ b => match JVar.sameK? j₁ j₂ with
    | some h => if σ = .bool then some ⟨_, .jump j₂ (.neu (Neu.mkCond c (h.down ▸ a) b))⟩
      else none
    | none => none
  | _, _ => none

theorem Term.mergeJumps?_eval {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) (r : (o : Lvl) × Term Δ d Φ Γ τ js o)
    (h : Term.mergeJumps? c t e = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = (Branch.ite c t e).eval κ ρ jκ := by
  cases t <;> cases e <;> simp only [Term.mergeJumps?, reduceCtorEq] at h
  rename_i σ₁ j₁ a σ₂ j₂ b
  split at h
  · rename_i hh hs
    split at h
    · cases h
      obtain ⟨hσ⟩ := hh
      subst hσ
      have hj := JVar.sameK?_eq j₁ j₂ hs
      simp only at hj
      subst hj
      simp only [Term.eval, PExpr.eval, Neu.mkCond_eval, Branch.eval]
      rw [Neu.eval_cond_ite]
      cases (c.eval κ ρ : Bool) <;> rfl
    · cases h
  · cases h

/-- The argument of a jump to the innermost join point, if the statement is one. -/
def Term.jumpHead? {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} :
    Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o → Option ((o' : Lvl) × PExpr Δ Φ Γ σ o')
  | .jump j a => match JVar.sameK? j (JVar.head (u := u) (js := js)) with
    | some h => some ⟨_, h.down ▸ a⟩
    | none => none
  | _ => none

theorem Term.jumpHead?_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl}
    (t : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o) {o' : Lvl} (a : PExpr Δ Φ Γ σ o')
    (h : t.jumpHead? = some ⟨o', a⟩) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    t.eval κ ρ (Tuple.cons f jκ) = f (a.eval κ ρ) := by
  cases t <;> simp only [Term.jumpHead?, reduceCtorEq] at h
  rename_i σ₁ j₁ a₁
  split at h
  · rename_i hh hs
    simp only [Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨hσ⟩ := hh
    subst hσ
    cases h
    have hj := JVar.sameK?_eq _ _ hs
    simp only at hj
    subst hj
    simp only [Term.eval, JEnv.get, Tuple.head_cons]
  · cases h

/-- The main part of a join point of a boolean parameter when it is
    `if c then jump j a else jump j b`, `j` the join point: the argument `c ? a : b` it is jumped
    to with (what `p && q` and `p || q` become when an operand computes something first).  Only at
    `bool`: a test whose arms jump with constructors is better left to `Term.joinCtor` and
    `Term.knownSizes`. -/
def Branch.jumpArg? {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {ℓ : Nat} :
    Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ → Option ((ℓ' : Nat) × Neu Δ Φ Γ σ ℓ')
  | .ite c t e => if σ = .bool then
      match t.jumpHead?, e.jumpHead? with
      | some ⟨_, a⟩, some ⟨_, b⟩ => some ⟨_, Neu.mkCond c a b⟩
      | _, _ => none
    else none
  | _ => none

theorem Branch.jumpArg?_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {ℓ : Nat}
    (br : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {ℓ' : Nat} (n : Neu Δ Φ Γ σ ℓ')
    (h : br.jumpArg? = some ⟨ℓ', n⟩) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    br.eval κ ρ (Tuple.cons f jκ) = f (n.eval κ ρ) := by
  cases br <;> simp only [Branch.jumpArg?, reduceCtorEq] at h
  rename_i c t e
  split at h
  · split at h
    · rename_i o₁ a o₂ b ha hb
      simp only [Option.some.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      simp only [Branch.eval, Neu.mkCond_eval]
      rw [Neu.eval_cond_ite]
      cases (c.eval κ ρ : Bool)
      · exact Term.jumpHead?_eval e b hb κ ρ jκ f
      · exact Term.jumpHead?_eval t a ha κ ρ jκ f
    · cases h
  · cases h

/-- `if c then t else e`, or `jump j (c ? a : b)` when both arms jump to `j`
    (`Term.mergeJumps?`). -/
def Term.mkIteJ {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) : (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match Term.mergeJumps? c t e with
  | some r => r
  | none => ⟨_, .branch (.ite c t e)⟩

theorem Term.mkIteJ_eval {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : (Term.mkIteJ c t e).2.eval κ ρ jκ = (Branch.ite c t e).eval κ ρ jκ := by
  unfold Term.mkIteJ
  split
  · rename_i r hr; exact Term.mergeJumps?_eval c t e r hr κ ρ jκ
  · rfl

theorem Term.numCalls_mkIteJ {js : JCtx ks} {ℓ : Nat} {o₁ o₂ : Lvl} (c : Neu Δ Φ Γ .bool ℓ)
    (t : Term Δ d Φ Γ τ js o₁) (e : Term Δ d Φ Γ τ js o₂) :
    (Term.mkIteJ c t e).2.numCalls ≤ t.numCalls + e.numCalls := by
  unfold Term.mkIteJ
  split
  · rename_i r hr
    cases t <;> cases e <;> simp only [Term.mergeJumps?, reduceCtorEq] at hr
    split at hr
    · split at hr
      · cases hr; simp [Term.numCalls]
      · cases hr
    · cases hr
  · simp [Term.numCalls, Branch.numCalls]

/-- A renaming that may change levels, followed by a weakening under the binders `bs`. -/
def ULRen.wkAfter {Γ₀ Γ : UCtx ks} (bs : UCtx ks) (w : ULRen Γ₀ Γ) : ULRen Γ₀ (bs ++ Γ) :=
  fun x => (w x).map fun p => ⟨p.1, UVar.weakenN bs p.2⟩

theorem ULRen.Agree.wkAfter {Γ₀ Γ : UCtx ks} {w : ULRen Γ₀ Γ} {ρ₀ : UEnv Δ Γ₀} {ρ : UEnv Δ Γ}
    (h : ULRen.Agree w ρ₀ ρ) (bs : UCtx ks) (vs : UEnv Δ bs) :
    ULRen.Agree (ULRen.wkAfter bs w) ρ₀ (Tuple.append vs ρ) := by
  intro _ _ x p hp
  simp only [ULRen.wkAfter, Option.map_eq_some_iff] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [UEnv.get_weakenN ρ bs vs q.2]
  exact h x q hq

/-- `let ⟨…⟩ := n₁; …; let ⟨…⟩ := nₖ; jump j a`, `j` the innermost join point (of parameter `x`
    and body `body`, seen from here along `w`), with `body[x := a]` in place of the jump: the join
    point inlined at its jump, under the case analyses. -/
def Term.inlineTailJump {Γ₀ : UCtx ks} {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {uₓ : Usage01ω}
    {ob : Lvl} (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ₀) τ js ob) :
    {Γ : UCtx ks} → ULRen Γ₀ Γ → {o : Lvl} → Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o →
    Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | _, w, _, .jump j a => match JVar.sameK? j (JVar.head (u := u) (js := js)) with
    | some h => body.subst (D' := d) KLRen.id (USub.cons ⟨_, h.down ▸ a⟩ (USub.ofRen w)) JRen.id
    | none => none
  | _, w, _, .record_casesOn (t := t) (fs := fs) us n b =>
    (Term.inlineTailJump body (ULRen.wkAfter (UCtx.annot d (t :: fs.toList) us) w) b).map
      fun r => ⟨_, .record_casesOn us n r.2⟩
  | _, _, _, .ret _ => none
  | _, _, _, .letV _ _ _ => none
  | _, _, _, .letE _ _ _ => none
  | _, _, _, .branch _ => none

theorem Term.inlineTailJump_eval {Γ₀ : UCtx ks} {js : JCtx ks} {σ : Ty ks} {u : Usage1ω}
    {uₓ : Usage01ω} {ob : Lvl} (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ₀) τ js ob) (κ : KEnv Δ Φ)
    (ρ₀ : UEnv Δ Γ₀) (jκ : JEnv Δ τ js) :
    {Γ : UCtx ks} → (w : ULRen Γ₀ Γ) → {o : Lvl} → (t : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o) →
    (r : (o' : Lvl) × Term Δ d Φ Γ τ js o') → Term.inlineTailJump body w t = some r →
    (ρ : UEnv Δ Γ) → ULRen.Agree w ρ₀ ρ →
    r.2.eval κ ρ jκ =
      t.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ₀) jκ) jκ)
  | _, w, _, .jump j a, r, h, ρ, hw => by
    simp only [Term.inlineTailJump] at h
    split at h
    · rename_i hh hs
      obtain ⟨hσ⟩ := hh
      subst hσ
      have hj := JVar.sameK?_eq _ _ hs
      simp only at hj h
      subst hj
      simp only [Term.eval, JEnv.get, Tuple.head_cons]
      exact Term.subst_eval (KLRen.Agree.id κ) (USub.Agree.cons (USub.Agree.ofRen hw) _)
        (JRen.Agree.id jκ) body h
    · cases h
  | _, w, _, .record_casesOn (t := t) (fs := fs) us n b, r, h, ρ, hw => by
    simp only [Term.inlineTailJump, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.eval]
    exact Term.inlineTailJump_eval body κ ρ₀ jκ _ b r' hr' _ (ULRen.Agree.wkAfter hw _ _)
  | _, _, _, .ret _, _, h, _, _ => by simp [Term.inlineTailJump] at h
  | _, _, _, .letV _ _ _, _, h, _, _ => by simp [Term.inlineTailJump] at h
  | _, _, _, .letE _ _ _, _, h, _, _ => by simp [Term.inlineTailJump] at h
  | _, _, _, .branch _, _, h, _, _ => by simp [Term.inlineTailJump] at h

theorem Term.numCalls_inlineTailJump {Γ₀ : UCtx ks} {js : JCtx ks} {σ : Ty ks} {u : Usage1ω}
    {uₓ : Usage01ω} {ob : Lvl} (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ₀) τ js ob) :
    {Γ : UCtx ks} → (w : ULRen Γ₀ Γ) → {o : Lvl} → (t : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o) →
    (r : (o' : Lvl) × Term Δ d Φ Γ τ js o') → Term.inlineTailJump body w t = some r →
    r.2.numCalls ≤ body.numCalls
  | _, w, _, .jump j a, r, h => by
    simp only [Term.inlineTailJump] at h
    split at h
    · exact Term.numCalls_subst body h
    · cases h
  | _, w, _, .record_casesOn (t := t) (fs := fs) us n b, r, h => by
    simp only [Term.inlineTailJump, Option.map_eq_some_iff] at h
    obtain ⟨r', hr', rfl⟩ := h
    simp only [Term.numCalls]
    exact Term.numCalls_inlineTailJump body _ b r' hr'
  | _, _, _, .ret _, _, h => by simp [Term.inlineTailJump] at h
  | _, _, _, .letV _ _ _, _, h => by simp [Term.inlineTailJump] at h
  | _, _, _, .letE _ _ _, _, h => by simp [Term.inlineTailJump] at h
  | _, _, _, .branch _, _, h => by simp [Term.inlineTailJump] at h

/-- The join point `join j x := body; if p then t else e` inlined, when both arms are the same
    statement (`Term.zipTest`: the same case analyses, and the same jump to `j`), which ends in a
    jump to `j` after case analyses of records (`Term.inlineTailJump`). -/
def Term.joinViaZip {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {uₓ : Usage01ω} {o : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) {ℓ : Nat} :
    Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ → Option ((o' : Lvl) × Term Δ d Φ Γ τ js o')
  | .ite p t e => match Term.zipTest Term.zipFuel p t e with
    | some r => Term.inlineTailJump body ULRen.idL r.2
    | none => none
  | _ => none

theorem Term.joinViaZip_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {uₓ : Usage01ω} {o : Lvl}
    (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) (r : (o' : Lvl) × Term Δ d Φ Γ τ js o')
    (h : Term.joinViaZip body main = some r) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  cases main <;> simp only [Term.joinViaZip, reduceCtorEq] at h
  rename_i p t e
  split at h
  · rename_i r' hz
    rw [Term.inlineTailJump_eval body κ ρ jκ ULRen.idL r'.2 r h ρ (ULRen.Agree.idL ρ),
      Term.zipTest_eval _ p t e r' hz κ ρ]
    rfl
  · cases h

theorem Term.numCalls_joinViaZip {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {uₓ : Usage01ω}
    {o : Lvl} (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o) {ℓ : Nat}
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) (r : (o' : Lvl) × Term Δ d Φ Γ τ js o')
    (h : Term.joinViaZip body main = some r) : r.2.numCalls ≤ body.numCalls := by
  cases main <;> simp only [Term.joinViaZip, reduceCtorEq] at h
  split at h
  · exact Term.numCalls_inlineTailJump body _ _ r h
  · cases h

/-- `join j (x : σ) := body; main`, or `body[x := a]` when both arms of the test `main` jump to
    `j` with the same argument `a` (`Branch.sameJumpArg?`, through case analyses whose fields are
    not used), or, when both arms are the same statement ending in a jump to `j`, that statement
    with the jump replaced by `body[x := a]` (`Term.joinViaZip`); only when `x` is used at most
    once (`Term.countU`, so that `a` is not copied; the usage annotation may not be up to date). -/
def Term.joinSame {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat}
    (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) : (o' : Lvl) × Term Δ d Φ Γ τ js o' :=
  go main.sameJumpArg? (body.countU 0).atMostOnce
where
  /-- `Term.joinSame`, the argument and the count given. -/
  go : Option ((o : Lvl) × PExpr Δ Φ Γ σ o) → Bool → (o' : Lvl) × Term Δ d Φ Γ τ js o'
    | some a, true =>
      match body.subst (D' := d) KLRen.id (USub.cons a (USub.ofRen ULRen.idL)) JRen.id with
      | some r => r
      | none => ⟨_, .branch (.join σ u uₓ body main)⟩
    | none, true => (Term.joinViaZip body main).getD ⟨_, .branch (.join σ u uₓ body main)⟩
    | _, false => ⟨_, .branch (.join σ u uₓ body main)⟩

theorem Term.joinSame_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat}
    (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.joinSame uₓ body main).2.eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  unfold Term.joinSame
  generalize ha : main.sameJumpArg? = r
  generalize (body.countU 0).atMostOnce = c
  cases c with
  | false => cases r <;> rfl
  | true =>
    cases r with
    | none =>
      simp only [Term.joinSame.go]
      cases hz : Term.joinViaZip body main with
      | none => rfl
      | some r => exact Term.joinViaZip_eval body main r hz κ ρ jκ
    | some a =>
      simp only [Term.joinSame.go]
      cases hs : body.subst (D' := d) KLRen.id (USub.cons a (USub.ofRen ULRen.idL)) JRen.id with
      | none => rfl
      | some r =>
        simp only [Branch.eval]
        rw [Branch.sameJumpArg?_eval main a.2 ha κ ρ jκ]
        exact Term.subst_eval (KLRen.Agree.id κ)
          (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) body hs

theorem Term.numCalls_joinSame {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat}
    (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (Term.joinSame uₓ body main).2.numCalls ≤ body.numCalls + main.numCalls := by
  unfold Term.joinSame
  generalize main.sameJumpArg? = r
  generalize (body.countU 0).atMostOnce = c
  cases c with
  | false => cases r <;> simp [Term.joinSame.go, Term.numCalls, Branch.numCalls]
  | true =>
    cases r with
    | none =>
      simp only [Term.joinSame.go]
      cases hz : Term.joinViaZip body main with
      | none => simp [Term.numCalls, Branch.numCalls]
      | some r =>
        have := Term.numCalls_joinViaZip body main r hz
        simp only [Option.getD]; omega
    | some a =>
      simp only [Term.joinSame.go]
      cases hs : body.subst (D' := d) KLRen.id (USub.cons a (USub.ofRen ULRen.idL)) JRen.id with
      | none => simp [Term.numCalls, Branch.numCalls]
      | some r =>
        have := Term.numCalls_subst body hs
        simp only; omega

/-- `join j (x : σ) := body; main`, or `let x := c ? a : b; body` when `main` is
    `if c then jump j a else jump j b` (`Branch.jumpArg?`; not when `x` is unused).  When `x` is
    used once, `c ? a : b` is written in its place (`Term.subst`), so that the tests of `x` are
    tests of `c ? a : b`, whose operands the walk then knows in the arms (`Neu.factsOf`). -/
def Term.joinOrLet {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat} :
    (uₓ : Usage01ω) → Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o → Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | .one, body, main => match main.jumpArg? with
    | some ⟨_, n⟩ =>
      (body.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL)) JRen.id).getD
        ⟨_, .letE .one (.share n) body⟩
    | none => Term.joinSame .one body main
  | .many, body, main => match main.jumpArg? with
    | some ⟨_, n⟩ => ⟨_, .letE .many (.share n) body⟩
    | none => Term.joinSame .many body main
  | .zero, body, main => Term.joinSame .zero body main

theorem Term.joinOrLet_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat}
    (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.joinOrLet uₓ body main).2.eval κ ρ jκ = (Branch.join σ u uₓ body main).eval κ ρ jκ := by
  cases uₓ with
  | zero => exact Term.joinSame_eval _ body main κ ρ jκ
  | one =>
    simp only [Term.joinOrLet]
    split
    · rename_i n hn
      simp only [Branch.eval]
      rw [Branch.jumpArg?_eval main n hn]
      cases hs : body.subst (D' := d) KLRen.id (USub.cons ⟨_, .neu n⟩ (USub.ofRen ULRen.idL))
          JRen.id with
      | some r =>
        exact Term.subst_eval (KLRen.Agree.id κ)
          (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) body hs
      | none => rfl
    · exact Term.joinSame_eval _ body main κ ρ jκ
  | many =>
    simp only [Term.joinOrLet]
    split
    · rename_i n hn
      simp only [Term.eval, Comp.eval, Branch.eval]
      rw [Branch.jumpArg?_eval main n hn]; rfl
    · exact Term.joinSame_eval _ body main κ ρ jκ

theorem Term.numCalls_joinOrLet {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {o : Lvl} {ℓ : Nat}
    (uₓ : Usage01ω) (body : Term Δ d Φ (⟨σ, uₓ, d⟩ :: Γ) τ js o)
    (main : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) :
    (Term.joinOrLet uₓ body main).2.numCalls ≤ body.numCalls + main.numCalls := by
  cases uₓ with
  | zero => exact Term.numCalls_joinSame _ body main
  | one =>
    simp only [Term.joinOrLet]
    split
    · simp only [Option.getD]
      split
      · rename_i r hs
        have := Term.numCalls_subst body hs
        dsimp only; omega
      · simp [Term.numCalls, Comp.numCalls]
    · exact Term.numCalls_joinSame _ body main
  | many =>
    simp only [Term.joinOrLet]
    split
    · simp [Term.numCalls, Comp.numCalls]
    · exact Term.numCalls_joinSame _ body main

/-- The neutral expression a computation shares, if it is `share n`. -/
def Comp.share? {σ : Ty ks} {ℓ : Nat} : Comp Δ d Φ Γ σ ℓ → Option (Neu Δ Φ Γ σ ℓ)
  | .share n => some n
  | _ => none

theorem Comp.share?_eval {σ : Ty ks} {ℓ : Nat} (c : Comp Δ d Φ Γ σ ℓ) (n : Neu Δ Φ Γ σ ℓ)
    (h : c.share? = some n) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : c.eval κ ρ = n.eval κ ρ := by
  cases c <;> simp only [Comp.share?, Option.some.injEq, reduceCtorEq] at h
  subst h; rfl

/-- `let x := c; b`, or `b[x := n]` when `c` is `share n`, a boolean used once
    (`Term.subst`): a condition `x` bound by `let` is tested as `n`, whose operands the walk then
    knows in the arms (`Neu.factsOf`).  (`Term.joinOrLet` writes such `let`s.)  A comparison of
    an operand with itself (`x == x`, `x < x`, `Neu.reflFold`) is substituted as its literal,
    however many times it is used. -/
def Term.letEOrSubst {js : JCtx ks} {σ : Ty ks} {ℓ : Nat} {o' : Lvl}
    (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') :
    (o : Lvl) × Term Δ d Φ Γ τ js o :=
  match c.share? with
  | some n =>
    if σ = .bool && (u == .one || n.reflFold.1 == none) then
      (b.subst (D' := d) KLRen.id (USub.cons n.reflFold (USub.ofRen ULRen.idL)) JRen.id).getD
        ⟨_, .letE u c b⟩
    else ⟨_, .letE u c b⟩
  | none => ⟨_, .letE u c b⟩

theorem Term.letEOrSubst_eval {js : JCtx ks} {σ : Ty ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Term.letEOrSubst u c b).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  simp only [Term.letEOrSubst]
  cases hn : c.share? with
  | none => rfl
  | some n =>
    dsimp only
    by_cases hc : (decide (σ = Ty.bool) && (u == Usage1ω.one || n.reflFold.fst == none)) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Option.getD]
      split
      · rename_i r hs
        rw [Term.subst_eval (KLRen.Agree.id κ)
          (USub.Agree.cons (USub.Agree.ofRen (ULRen.Agree.idL ρ)) _) (JRen.Agree.id jκ) b hs]
        simp only [Term.eval, Comp.share?_eval c n hn κ ρ, Neu.reflFold_eval]
      · rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]

theorem Term.numCalls_letEOrSubst {js : JCtx ks} {σ : Ty ks} {ℓ : Nat} {o' : Lvl} (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ ℓ) (b : Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ js o') :
    (Term.letEOrSubst u c b).2.numCalls ≤ c.numCalls + b.numCalls := by
  simp only [Term.letEOrSubst]
  cases c.share? with
  | none => simp [Term.numCalls]
  | some n =>
    dsimp only
    by_cases hc : (decide (σ = Ty.bool) && (u == Usage1ω.one || n.reflFold.fst == none)) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Option.getD]
      split
      · rename_i r hs
        have := Term.numCalls_subst b hs
        dsimp only; omega
      · simp [Term.numCalls]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; simp [Term.numCalls]

end Jumps

/-! ## The walk -/

mutual
/-- `Term.knownTestWalk` inside the bodies of a value (the value keeps its level). -/
def Val.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    List (BoolFact Γ) → Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, facts, .lam b => .lam (b.knownTestWalk facts)
  | _, _, _, _, _, facts, .thunk_mk b => .thunk_mk (b.knownTestWalk facts)
  | _, _, _, _, _, facts, .lazy_mk b => .lazy_mk (b.knownTestWalk facts)
  | _, _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.knownTestWalk` in a body: a closed body starts with no fact, an open one with the
    facts of its context; an open body keeps its level (or is kept as it is). -/
def Body.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → List (BoolFact Γ) → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, _, .closed t => .closed (t.knownTestWalk []).2
  | _, _, _, bs, _, _, facts, .opened (m := m) t h =>
      let r := t.knownTestWalk (facts.map (BoolFact.weakenN bs))
      if hr : r.1 = some m then .opened (r.2.castLvl hr) h else .opened t h
/-- `Term.knownTestWalk` inside the bodies of a computation. -/
def Comp.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    List (BoolFact Γ) → Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, facts, .nat_rec n z s h => .nat_rec n z (s.knownTestWalk facts) h
  | _, _, _, _, _, facts, .array_foldl a z s h => .array_foldl a z (s.knownTestWalk facts) h
  | _, _, _, _, _, facts, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).knownTestWalk facts) j e h
  | _, _, _, _, _, facts, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).knownTestWalk facts) j e h
  | _, _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Known tests**: walk a statement knowing the values of some boolean unknowns; an `if` on a
    known condition is replaced by the arm it takes, and the arms of any other `if` on an
    unknown know its value.  The result may have another level, and is returned with it. -/
def Term.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → List (BoolFact Γ) → Term Δ d Φ Γ τ js o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, facts, .ret e => ⟨_, .ret (e.condSimp facts).2⟩
  | _, _, _, _, _, _, facts, .letV u v b =>
      ⟨_, .letV u (v.knownTestWalk facts) (b.knownTestWalk facts).2⟩
  | _, _, _, _, _, _, facts, .letE u c b =>
      Term.letEOrSubst u (c.knownTestWalk facts)
        (b.knownTestWalk (facts.map (BoolFact.weaken _))).2
  | _, _, _, _, _, _, facts, .record_casesOn us n b =>
      ⟨_, .record_casesOn us n (b.knownTestWalk (facts.map (BoolFact.weakenN _))).2⟩
  | _, _, _, _, _, _, facts, .branch (.ite c t e) =>
      match (c.condSimp facts).2.boolLit? with
      | some true => t.knownTestWalk facts
      | some false => e.knownTestWalk facts
      | none => match (c.condSimp facts).2.neu? with
        | some ⟨_, n⟩ => Term.mkIteJ n (t.knownTestWalk (Neu.factsOf facts n true)).2
            (e.knownTestWalk (Neu.factsOf facts n false)).2
        | none => ⟨_, .branch (.ite c (t.knownTestWalk facts).2 (e.knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, facts, .branch (.enum_casesOn e bs) =>
      ⟨_, .branch (.enum_casesOn e (fun i => ((bs i).knownTestWalk facts).2))⟩
  | _, _, _, _, _, _, facts, .branch (.union_casesOn e bs) =>
      ⟨_, .branch (.union_casesOn e (bs.knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, facts, .branch (.join σ u uₓ body main) =>
      Term.joinOrLet uₓ (body.knownTestWalk (facts.map (BoolFact.weaken _))).2
        (main.knownTestWalk facts).2
  | _, _, _, _, _, _, facts, .jump j e => ⟨_, .jump j (e.condSimp facts).2⟩
/-- `Term.knownTestWalk` in a branch that must stay a branch (the main part of a join point):
    no `if` is dropped at its head. -/
def Branch.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → List (BoolFact Γ) → Branch Δ d Φ Γ τ js ℓ →
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, facts, .ite c t e =>
      match (c.condSimp facts).2.neu? with
      | some ⟨_, n⟩ => ⟨_, .ite n (t.knownTestWalk (Neu.factsOf facts n true)).2
          (e.knownTestWalk (Neu.factsOf facts n false)).2⟩
      | none => ⟨_, .ite c (t.knownTestWalk (Neu.factsOf facts c true)).2
          (e.knownTestWalk (Neu.factsOf facts c false)).2⟩
  | _, _, _, _, _, _, facts, .enum_casesOn e bs =>
      ⟨_, .enum_casesOn e (fun i => ((bs i).knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, facts, .union_casesOn e bs => ⟨_, .union_casesOn e (bs.knownTestWalk facts).2⟩
  | _, _, _, _, _, _, facts, .join σ u uₓ body main =>
      ⟨_, .join σ u uₓ (body.knownTestWalk (facts.map (BoolFact.weaken _))).2
        (main.knownTestWalk facts).2⟩
/-- `Term.knownTestWalk` in the branches of a union's case analysis. -/
def Branches.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → List (BoolFact Γ) →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, facts, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (b₁.knownTestWalk (facts.map (BoolFact.weakenN _))).2
        (b₂.knownTestWalk (facts.map (BoolFact.weakenN _))).2⟩
  | _, _, _, _, _, _, _, _, facts, .cons us b bs =>
      ⟨_, .cons us (b.knownTestWalk (facts.map (BoolFact.weakenN _))).2
        (bs.knownTestWalk facts).2⟩
end

/-! ## The value does not change -/

mutual
theorem Val.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) → (v.knownTestWalk facts).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; funext x
      rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .thunk_mk b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .lazy_mk b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Body.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (∀ f ∈ facts, f.Holds ρ) →
    (b.knownTestWalk facts).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _, _, _ => by
      simp only [Body.knownTestWalk, Body.eval]
      exact Term.knownTestWalk_eval t [] _ _ _ (fun _ h => nomatch h)
  | _, _, _, _, _, _, .opened t _, facts, κ, ρ, vs, h => by
      simp only [Body.knownTestWalk]
      split
      · simp only [Body.eval]
        exact (Term.eval_castLvl _ _ _ _ _).trans
          (Term.knownTestWalk_eval t _ _ _ _ (BoolFact.map_weakenN_holds _ vs h))
      · rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Comp.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) → (c.knownTestWalk facts).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext k acc; exact Body.knownTestWalk_eval s facts κ ρ _ h
  | _, _, _, _, _, .array_foldl a z s _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext acc x; exact Body.knownTestWalk_eval s facts κ ρ _ h
  | _, _, _, _, _, .data_rec b ρt us brs j e _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.knownTestWalk_eval (brs i) facts κ ρ _ h
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.knownTestWalk_eval (brs i) facts κ ρ _ h
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Term.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (t.knownTestWalk facts).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, facts, κ, ρ, _, h => by
      simp only [Term.knownTestWalk, Term.eval]; exact PExpr.condSimp_eval facts e κ ρ h
  | _, _, _, _, _, _, .letV u v b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Val.knownTestWalk_eval v facts κ ρ h]
      exact Term.knownTestWalk_eval b facts _ ρ jκ h
  | _, _, _, _, _, _, .letE u c b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk]
      rw [Term.letEOrSubst_eval]
      simp only [Term.eval, Comp.knownTestWalk_eval c facts κ ρ h]
      exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weaken_holds _ h)
  | _, _, _, _, _, _, .record_casesOn us n b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval]
      exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
  | _, _, _, _, _, _, .branch (.ite c t e), facts, κ, ρ, jκ, h => by
      have ihc := Neu.condSimp_eval facts c κ ρ h
      have iht := fun fs (hf : ∀ f ∈ fs, BoolFact.Holds f ρ) => Term.knownTestWalk_eval t fs κ ρ jκ hf
      have ihe := fun fs (hf : ∀ f ∈ fs, BoolFact.Holds f ρ) => Term.knownTestWalk_eval e fs κ ρ jκ hf
      simp only [Term.knownTestWalk]
      cases hb : (c.condSimp facts).2.boolLit? with
      | some v =>
        rw [PExpr.boolLit?_eval _ v hb κ ρ] at ihc
        cases v
        · dsimp only; rw [ihe facts h]; simp only [Term.eval, Branch.eval, ← ihc]
        · dsimp only; rw [iht facts h]; simp only [Term.eval, Branch.eval, ← ihc]
      | none =>
        dsimp only
        cases hn : (c.condSimp facts).2.neu? with
        | some p =>
          obtain ⟨_, n⟩ := p
          rw [PExpr.neu?_eval _ _ n hn κ ρ] at ihc
          dsimp only
          rw [Term.mkIteJ_eval]
          simp only [Term.eval, Branch.eval, ihc]
          split
          · rename_i hv
            exact iht _ (Neu.factsOf_holds facts n true κ ρ h rfl (heq_of_eq (ihc.trans hv)))
          · rename_i hv
            exact ihe _ (Neu.factsOf_holds facts n false κ ρ h rfl (heq_of_eq (ihc.trans hv)))
        | none =>
          dsimp only
          simp only [Term.eval, Branch.eval, iht facts h, ihe facts h]
  | _, _, _, _, _, _, .branch (.enum_casesOn e bs), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Branch.eval]
      exact Term.knownTestWalk_eval _ facts κ ρ jκ h
  | _, _, _, _, _, _, .branch (.union_casesOn e bs), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Branch.eval]
      exact Branches.knownTestWalk_eval bs facts κ ρ jκ h _
  | _, _, _, _, _, _, .branch (.join σ u uₓ body main), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk]
      rw [Term.joinOrLet_eval]
      simp only [Term.eval, Branch.eval, Branch.knownTestWalk_eval main facts κ ρ _ h]
      congr 2
      funext v
      exact Term.knownTestWalk_eval body _ κ _ jκ
        (BoolFact.map_weaken_holds (b := ⟨σ, uₓ, _⟩) v h)
  | _, _, _, _, _, _, .jump j e, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, PExpr.condSimp_eval facts e κ ρ h]
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branch.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (br.knownTestWalk facts).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, facts, κ, ρ, jκ, h => by
      have ihc := Neu.condSimp_eval facts c κ ρ h
      have iht := fun fs (hf : ∀ f ∈ fs, BoolFact.Holds f ρ) => Term.knownTestWalk_eval t fs κ ρ jκ hf
      have ihe := fun fs (hf : ∀ f ∈ fs, BoolFact.Holds f ρ) => Term.knownTestWalk_eval e fs κ ρ jκ hf
      simp only [Branch.knownTestWalk]
      cases hn : (c.condSimp facts).2.neu? with
      | some p =>
        obtain ⟨_, n⟩ := p
        rw [PExpr.neu?_eval _ _ n hn κ ρ] at ihc
        dsimp only
        simp only [Branch.eval, ihc]
        split
        · rename_i hv
          exact iht _ (Neu.factsOf_holds facts n true κ ρ h rfl (heq_of_eq (ihc.trans hv)))
        · rename_i hv
          exact ihe _ (Neu.factsOf_holds facts n false κ ρ h rfl (heq_of_eq (ihc.trans hv)))
      | none =>
        dsimp only
        simp only [Branch.eval]
        split
        · rename_i hv
          exact iht _ (Neu.factsOf_holds facts c true κ ρ h rfl (heq_of_eq hv))
        · rename_i hv
          exact ihe _ (Neu.factsOf_holds facts c false κ ρ h rfl (heq_of_eq hv))
  | _, _, _, _, _, _, .enum_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval]
      exact Term.knownTestWalk_eval _ facts κ ρ jκ h
  | _, _, _, _, _, _, .union_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval]
      exact Branches.knownTestWalk_eval bs facts κ ρ jκ h _
  | _, _, _, _, _, _, .join σ u uₓ body main, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval, Branch.knownTestWalk_eval main facts κ ρ _ h]
      congr 2
      funext v
      exact Term.knownTestWalk_eval body _ κ _ jκ
        (BoolFact.map_weaken_holds (b := ⟨σ, uₓ, _⟩) v h)
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branches.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
      ∀ x, (br.knownTestWalk facts).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.knownTestWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.knownTestWalk_eval b₁ _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
      · funext v
        exact Term.knownTestWalk_eval b₂ _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
  | _, _, _, _, _, _, _, _, .cons us b bs, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.knownTestWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
      · funext r
        exact Branches.knownTestWalk_eval bs facts κ ρ jκ h r
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (facts : List (BoolFact Γ)) →
    (v.knownTestWalk facts).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .thunk_mk b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .lazy_mk b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Body.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (facts : List (BoolFact Γ)) →
    (b.knownTestWalk facts).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, _ => by
      simp only [Body.knownTestWalk, Body.numCalls]; exact Term.numCalls_knownTestWalk t []
  | _, _, _, _, _, _, .opened t _, facts => by
      simp only [Body.knownTestWalk]
      split
      · simp only [Body.numCalls, Term.numCalls_castLvl]
        exact Term.numCalls_knownTestWalk t _
      · exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Comp.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (facts : List (BoolFact Γ)) →
    (c.knownTestWalk facts).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]; exact Body.numCalls_knownTestWalk s facts
  | _, _, _, _, _, .array_foldl a z s _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]; exact Body.numCalls_knownTestWalk s facts
  | _, _, _, _, _, .data_rec b ρt us brs j e _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_knownTestWalk (brs i) facts)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_knownTestWalk (brs i) facts)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Term.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (facts : List (BoolFact Γ)) → (t.knownTestWalk facts).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, facts => by
      have h₁ := Val.numCalls_knownTestWalk v facts
      have h₂ := Term.numCalls_knownTestWalk b facts
      simp only [Term.knownTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, facts => by
      have h₁ := Comp.numCalls_knownTestWalk c facts
      have h₂ := Term.numCalls_knownTestWalk b (facts.map (BoolFact.weaken _))
      have h₃ := Term.numCalls_letEOrSubst u (c.knownTestWalk facts)
        (b.knownTestWalk (facts.map (BoolFact.weaken _))).2
      simp only [Term.knownTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, facts => by
      simp only [Term.knownTestWalk, Term.numCalls]
      exact Term.numCalls_knownTestWalk b _
  | _, _, _, _, _, _, .branch (.ite c t e), facts => by
      have iht := fun fs => Term.numCalls_knownTestWalk t fs
      have ihe := fun fs => Term.numCalls_knownTestWalk e fs
      have h₁ := iht facts
      have h₂ := ihe facts
      simp only [Term.knownTestWalk]
      cases (c.condSimp facts).2.boolLit? with
      | some v => cases v <;> simp only [Term.numCalls, Branch.numCalls] <;> omega
      | none =>
        dsimp only
        cases (c.condSimp facts).2.neu? with
        | some p =>
          obtain ⟨_, n⟩ := p
          dsimp only
          have h₃ := Term.numCalls_mkIteJ n (t.knownTestWalk (Neu.factsOf facts n true)).2
            (e.knownTestWalk (Neu.factsOf facts n false)).2
          have h₄ := iht (Neu.factsOf facts n true)
          have h₅ := ihe (Neu.factsOf facts n false)
          simp only [Term.numCalls, Branch.numCalls]; omega
        | none => dsimp only; simp only [Term.numCalls, Branch.numCalls]; omega
  | _, _, _, _, _, _, .branch (.enum_casesOn e bs), facts => by
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_knownTestWalk (bs i) facts)
  | _, _, _, _, _, _, .branch (.union_casesOn e bs), facts => by
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]
      exact Branches.numCalls_knownTestWalk bs facts
  | _, _, _, _, _, _, .branch (.join σ u uₓ body main), facts => by
      have h₁ := Term.numCalls_knownTestWalk body (facts.map (BoolFact.weaken _))
      have h₂ := Branch.numCalls_knownTestWalk main facts
      have h₃ := Term.numCalls_joinOrLet uₓ
        (body.knownTestWalk (facts.map (BoolFact.weaken _))).2 (main.knownTestWalk facts).2
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]; omega
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branch.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (facts : List (BoolFact Γ)) → (br.knownTestWalk facts).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, facts => by
      have iht := fun fs => Term.numCalls_knownTestWalk t fs
      have ihe := fun fs => Term.numCalls_knownTestWalk e fs
      simp only [Branch.knownTestWalk]
      cases (c.condSimp facts).2.neu? with
      | some p =>
        obtain ⟨_, n⟩ := p
        have h₁ := iht (Neu.factsOf facts n true)
        have h₂ := ihe (Neu.factsOf facts n false)
        dsimp only; simp only [Branch.numCalls]; omega
      | none =>
        have h₁ := iht (Neu.factsOf facts c true)
        have h₂ := ihe (Neu.factsOf facts c false)
        dsimp only; simp only [Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, facts => by
      simp only [Branch.knownTestWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_knownTestWalk (bs i) facts)
  | _, _, _, _, _, _, .union_casesOn e bs, facts => by
      simp only [Branch.knownTestWalk, Branch.numCalls]
      exact Branches.numCalls_knownTestWalk bs facts
  | _, _, _, _, _, _, .join σ u uₓ body main, facts => by
      have h₁ := Term.numCalls_knownTestWalk body (facts.map (BoolFact.weaken _))
      have h₂ := Branch.numCalls_knownTestWalk main facts
      simp only [Branch.knownTestWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branches.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (BoolFact Γ)) →
    (br.knownTestWalk facts).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts => by
      have h₁ := Term.numCalls_knownTestWalk b₁ (facts.map (BoolFact.weakenN _))
      have h₂ := Term.numCalls_knownTestWalk b₂ (facts.map (BoolFact.weakenN _))
      simp only [Branches.knownTestWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, facts => by
      have h₁ := Term.numCalls_knownTestWalk b (facts.map (BoolFact.weakenN _))
      have h₂ := Branches.numCalls_knownTestWalk bs facts
      simp only [Branches.knownTestWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x _ => x
end

/-- **The known tests of a statement**, dropped (`Term.knownTestWalk` with no fact), when this
    keeps the level of the statement. -/
def Term.knownTests {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  if h : (t.knownTestWalk []).1 = o then (t.knownTestWalk []).2.castLvl h else t

/-- **Dropping the known tests does not change the value.** -/
theorem Term.knownTests_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.knownTests.eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.knownTests
  split
  · rw [Term.eval_castLvl]
    exact Term.knownTestWalk_eval t [] κ ρ jκ (fun _ h => nomatch h)
  · rfl

/-- The same for a whole program. -/
theorem Term.knownTests_run {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    t.knownTests.run = t.run :=
  t.knownTests_eval _ _ _

/-- **Dropping the known tests adds no call.** -/
theorem Term.numCalls_knownTests {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.knownTests.numCalls ≤ t.numCalls := by
  unfold Term.knownTests
  split
  · rw [Term.numCalls_castLvl]; exact Term.numCalls_knownTestWalk t []
  · exact Nat.le_refl _

end LeanScript

end
