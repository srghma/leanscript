module

public import LeanScript.Term.Optimize.KnownCond

@[expose] public section

set_option autoImplicit false

/-!
# Both arms of an `if` jump to a join point with the same argument

Lean's derived `Repr` instances read a field again in each arm of the test it makes on it (the
`Repr Int` instance tests the sign), and the known-fields pass (`Term.reuseFields`) can only make
the repeated case analysis *unused*, not drop it, since dropping it would change the level of the
arm:

```
join j (x : σ) := body                     body[x := a]
if c then (let ⟨_, _⟩ := r; jump j a)  ⟹
     else (let ⟨_, _⟩ := r; jump j a)
```

`Term.deadJumpHead?` reads the argument of a jump to the innermost join point through case
analyses of records whose fields the argument does not use (`URen.strN`: the argument moved out of
the fields), and `Branch.sameJumpArg?` recognises the `if` above (`PExpr.same`).  The join point
is then its body with `a` for its parameter (`Term.joinSame`, `LeanScript.Term.Optimize.KnownTest`).
The language is pure and total, so the test and the case analyses need not be made.

**Proved:** `Term.deadJumpHead?_eval` and `Branch.sameJumpArg?_eval`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- Strengthening: the unknowns of `Γ`, seen without the binders `bs` in front (an unknown of `bs`
    has no image). -/
def URen.strN {Γ : UCtx ks} : (bs : UCtx ks) → URen (bs ++ Γ) Γ
  | [], _, _, x => some x
  | ⟨_, _, _⟩ :: _, _, _, .head _ => none
  | _ :: bs, _, _, .tail y => URen.strN bs y

theorem URen.Agree.strN {Γ : UCtx ks} (ρ : UEnv Δ Γ) :
    (bs : UCtx ks) → (vs : UEnv Δ bs) → URen.Agree (URen.strN bs) (Tuple.append vs ρ) ρ
  | [], _ => URen.Agree.id ρ
  | b :: bs, vs => by
      intro x y h
      cases x with
      | head _ => simp [URen.strN] at h
      | tail x =>
        simp only [URen.strN] at h
        rw [Tuple.append_cons]
        simp only [UEnv.get, Tuple.tail_cons]
        exact URen.Agree.strN ρ bs vs.tail x y h

section Jumps
variable {d : Nat} {Φ : KCtx ks} {τ : Ty ks}

/-- Is it the same join point (then its parameter has the same type)? -/
def JVar.sameK? : {js : JCtx ks} → {σ' σ : Ty ks} → JVar js σ' → JVar js σ →
    Option (PLift (σ' = σ))
  | _, _, _, .head, .head => some ⟨rfl⟩
  | _, _, _, .tail a, .tail b => JVar.sameK? a b
  | _, _, _, _, _ => none

theorem JVar.sameK?_eq : {js : JCtx ks} → {σ' σ : Ty ks} → (a : JVar js σ') → (b : JVar js σ) →
    {h : PLift (σ' = σ)} → JVar.sameK? a b = some h → h.down ▸ a = b
  | _, _, _, .head, .head, _, _ => rfl
  | _, _, _, .tail a, .tail b, h, hs => by
      simp only [JVar.sameK?] at hs
      have := JVar.sameK?_eq a b hs
      obtain ⟨hh⟩ := h
      subst hh
      simp only at this ⊢
      rw [this]
  | _, _, _, .head, .tail _, _, hs => by simp [JVar.sameK?] at hs
  | _, _, _, .tail _, .head, _, hs => by simp [JVar.sameK?] at hs


/-- The argument of a jump to the innermost join point, seen through case analyses of records
    whose fields the argument does not use. -/
def Term.deadJumpHead? {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} :
    {Γ : UCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o →
    Option ((o' : Lvl) × PExpr Δ Φ Γ σ o')
  | _, _, .jump j a => match JVar.sameK? j (JVar.head (u := u) (js := js)) with
    | some h => some ⟨_, h.down ▸ a⟩
    | none => none
  | _, _, .record_casesOn (t := t) (fs := fs) us _ b =>
    match Term.deadJumpHead? b with
    | some ⟨_, a⟩ =>
      (a.rename KRen.id (URen.strN (UCtx.annot d (t :: fs.toList) us))).map fun a' => ⟨_, a'⟩
    | none => none
  | _, _, .ret _ => none
  | _, _, .letV _ _ _ => none
  | _, _, .letE _ _ _ => none
  | _, _, .branch _ => none

theorem Term.deadJumpHead?_eval {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} :
    {Γ : UCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ (⟨σ, u⟩ :: js) o) → {o' : Lvl} →
    (a : PExpr Δ Φ Γ σ o') → t.deadJumpHead? = some ⟨o', a⟩ → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (f : Ty.Den Δ σ → Ty.Den Δ τ) →
    t.eval κ ρ (Tuple.cons f jκ) = f (a.eval κ ρ)
  | _, _, .jump j a₁, _, a, h, κ, ρ, jκ, f => by
    simp only [Term.deadJumpHead?] at h
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
  | _, _, .record_casesOn (t := t) (fs := fs) us n b, _, a, h, κ, ρ, jκ, f => by
    simp only [Term.deadJumpHead?] at h
    split at h
    · rename_i o₁ a₁ hb
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨a', ha', h⟩ := h
      simp only [Sigma.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      cases h
      simp only [Term.eval]
      rw [Term.deadJumpHead?_eval b a₁ hb κ _ jκ f]
      congr 1
      exact (PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.strN ρ _ _) a₁ ha').symm
    · cases h
  | _, _, .ret _, _, _, h, _, _, _, _ => by
    simp [Term.deadJumpHead?] at h
  | _, _, .letV _ _ _, _, _, h, _, _, _, _ => by
    simp [Term.deadJumpHead?] at h
  | _, _, .letE _ _ _, _, _, h, _, _, _, _ => by
    simp [Term.deadJumpHead?] at h
  | _, _, .branch _, _, _, h, _, _, _, _ => by
    simp [Term.deadJumpHead?] at h

/-- The main part of a join point when it is `if c then jump j a else jump j a`, `j` the join
    point, both arms with the same argument (`PExpr.same`), possibly behind case analyses whose
    fields are not used (`Term.deadJumpHead?`): the argument `a`. -/
def Branch.sameJumpArg? {Γ : UCtx ks} {js : JCtx ks} {σ : Ty ks} {u : Usage1ω} {ℓ : Nat} :
    Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ → Option ((o : Lvl) × PExpr Δ Φ Γ σ o)
  | .ite _ t e =>
    match t.deadJumpHead?, e.deadJumpHead? with
    | some a, some b => if a.2.same b.2 then some a else none
    | _, _ => none
  | _ => none

theorem Branch.sameJumpArg?_eval {Γ : UCtx ks} {js : JCtx ks} {σ : Ty ks} {u : Usage1ω}
    {ℓ : Nat} (br : Branch Δ d Φ Γ τ (⟨σ, u⟩ :: js) ℓ) {o : Lvl} (a : PExpr Δ Φ Γ σ o)
    (h : br.sameJumpArg? = some ⟨o, a⟩) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js)
    (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    br.eval κ ρ (Tuple.cons f jκ) = f (a.eval κ ρ) := by
  cases br <;> simp only [Branch.sameJumpArg?, reduceCtorEq] at h
  rename_i c t e
  cases ha : t.deadJumpHead? with
  | none => simp [ha] at h
  | some a₁ =>
    cases hb : e.deadJumpHead? with
    | none => simp [ha, hb] at h
    | some b₁ =>
      simp only [ha, hb] at h
      split at h
      · rename_i hs
        cases h
        have hab := eq_of_heq ((PExpr.same_eval a b₁.2 hs).2 κ ρ)
        simp only [Branch.eval]
        cases (c.eval κ ρ : Bool)
        · rw [Term.deadJumpHead?_eval e b₁.2 hb κ ρ jκ f, ← hab]
        · exact Term.deadJumpHead?_eval t a ha κ ρ jκ f
      · cases h

end Jumps

end LeanScript

end
