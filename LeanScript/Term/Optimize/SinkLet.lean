module

public import LeanScript.Term.Optimize.Dce
public import LeanScript.Term.Optimize.CountDce
public import LeanScript.Term.Optimize.CountRename
public import LeanScript.Term.Optimize.InlineBlockEval

@[expose] public section

set_option autoImplicit false

/-!
# A computation used once is made right before its use

`Term.sinkWalk`: in a chain of `let`s, a computation whose result is used once (`let x [1] := c`)
is moved down past the computations that follow it and do not read it, as long as they are not
themselves used once:

```
let x [1] := f 1          let y [ω] := f 2
let y [ω] := f 2     ⟹    let x [1] := f 1
ret ⟨x, y, y⟩             ret ⟨x, y, y⟩
```

The language is pure and total, so two independent computations can be swapped
(`Term.sinkLet_eval`); the number of calls does not change (`Term.numCalls_sinkLet`).  The
computation used once now comes right before the statement that reads it, so the JavaScript
printer writes it at its use (`const y = f(2); return { _1: f(1), _2: y, _3: y };`, as
purescript-backend-optimizer does), where before it had to be named, since moving the call
`f(1)` past the call `f(2)` is not something the printer may do on its own (a JavaScript call
may have an effect).

The `let`s used once keep their order among themselves (a `let` used once stops at the next
`let` used once), so that the printer can write all of them at their uses, in order.  Moving
stops at anything that is not a `let` of a computation (a `val`, a case analysis, a branch,
the answer), and after `Term.sinkFuel` steps.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Renamings -/

/-- The renaming swapping the two innermost unknowns. -/
def URen.swap {Γ : UCtx ks} : (b₁ b₂ : UBinder ks) → URen (b₂ :: b₁ :: Γ) (b₁ :: b₂ :: Γ)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, _, _, .head h => some (.tail (.head h))
  | ⟨_, _, _⟩, ⟨_, _, _⟩, _, _, .tail (.head h) => some (.head h)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, _, _, .tail (.tail x) => some (.tail (.tail x))

theorem URen.Agree.swap {Γ : UCtx ks} (b₁ b₂ : UBinder ks) (v₁ : Ty.Den Δ b₁.ty)
    (v₂ : Ty.Den Δ b₂.ty) (ρ : UEnv Δ Γ) :
    URen.Agree (URen.swap b₁ b₂) (Tuple.cons v₂ (Tuple.cons v₁ ρ))
      (Tuple.cons v₁ (Tuple.cons v₂ ρ)) := by
  obtain ⟨σ₁, u₁, ℓ₁⟩ := b₁
  obtain ⟨σ₂, u₂, ℓ₂⟩ := b₂
  intro _ _ x y hxy
  cases x with
  | head h =>
      simp only [URen.swap, Option.some.injEq] at hxy
      subst hxy; simp
  | tail x =>
      cases x with
      | head h =>
          simp only [URen.swap, Option.some.injEq] at hxy
          subst hxy; simp
      | tail x =>
          simp only [URen.swap, Option.some.injEq] at hxy
          subst hxy; simp

/-! ## Moving one computation down -/

theorem Lvl.meetL_swap (ℓ₁ ℓ₂ : Nat) (o : Lvl) :
    some (Lvl.meetL ℓ₂ (some (Lvl.meetL ℓ₁ o))) = some (Lvl.meetL ℓ₁ (some (Lvl.meetL ℓ₂ o))) := by
  cases o <;> simp only [Lvl.meetL, Option.some.injEq, Nat.min_def] <;> split <;> split <;>
    (try split) <;> (try split) <;> omega

/-- How many `let`s a computation is moved past, at most. -/
def Term.sinkFuel : Nat := 64

/-- `let x [u] := c; b`, with the computation moved down past the `let`s of `b` that do not
    read `x` and are not used once (at most `fuel` of them). -/
def Term.sinkLet : Nat → {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {σ τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {o : Lvl} → (u : Usage1ω) → Comp Δ d Φ Γ σ ℓ →
    Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o → Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o))
  | 0, _, _, _, _, _, _, _, _, u, c, b => .letE u c b
  | fuel + 1, _, _, _, _, _, _, _, _, u, c, .letE (ℓ := ℓ₂) (o' := o₂) u₂ c₂ b₂ =>
      if u₂ = .one then .letE u c (.letE u₂ c₂ b₂) else
      match c₂.rename KRen.id URen.drop, c.rename KRen.id URen.wk1,
        b₂.rename KRen.id (URen.swap _ _) JRen.id with
      | some c₂', some c', some b₂' =>
          (Term.letE u₂ c₂' (Term.sinkLet fuel u c' b₂')).castLvl (Lvl.meetL_swap _ ℓ₂ o₂)
      | _, _, _ => .letE u c (.letE u₂ c₂ b₂)
  | _ + 1, _, _, _, _, _, _, _, _, u, c, b => .letE u c b

/-- **What `sinkLet` does**: in front of a `let` that is not used once, whose computation does
    not read `x` (`c₂.rename … URen.drop = some c₂'`), the computation `c` moves past it, and
    keeps moving in what follows (the two innermost unknowns swapped). -/
theorem Term.sinkLet_letE {fuel : Nat} {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ σ₂ τ : Ty ks}
    {js : JCtx ks} {ℓ ℓ₂ : Nat} {o₂ : Lvl} (u u₂ : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (c₂ : Comp Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) σ₂ ℓ₂)
    (b₂ : Term Δ d Φ (⟨σ₂, u₂.toUsage01ω, d⟩ :: ⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o₂)
    (hu₂ : u₂ ≠ .one) {c₂' : Comp Δ d Φ Γ σ₂ ℓ₂}
    {c' : Comp Δ d Φ (⟨σ₂, u₂.toUsage01ω, d⟩ :: Γ) σ ℓ}
    {b₂' : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: ⟨σ₂, u₂.toUsage01ω, d⟩ :: Γ) τ js o₂}
    (hc₂ : c₂.rename KRen.id URen.drop = some c₂') (hc : c.rename KRen.id URen.wk1 = some c')
    (hb₂ : b₂.rename KRen.id (URen.swap _ _) JRen.id = some b₂') :
    Term.sinkLet (fuel + 1) u c (.letE u₂ c₂ b₂) =
      (Term.letE u₂ c₂' (Term.sinkLet fuel u c' b₂')).castLvl (Lvl.meetL_swap _ ℓ₂ o₂) := by
  simp only [Term.sinkLet, hu₂, ite_false, hc₂, hc, hb₂]

/-- `sinkLet` stops at a `let` used once: the `let`s used once keep their order. -/
theorem Term.sinkLet_letE_one {fuel : Nat} {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks}
    {σ σ₂ τ : Ty ks} {js : JCtx ks} {ℓ ℓ₂ : Nat} {o₂ : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (c₂ : Comp Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) σ₂ ℓ₂)
    (b₂ : Term Δ d Φ (⟨σ₂, Usage1ω.one.toUsage01ω, d⟩ :: ⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o₂) :
    Term.sinkLet (fuel + 1) u c (.letE .one c₂ b₂) = .letE u c (.letE .one c₂ b₂) := by
  simp only [Term.sinkLet, ite_true]

theorem Term.sinkLet_eval : (fuel : Nat) → {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {σ τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → {o : Lvl} → (u : Usage1ω) →
    (c : Comp Δ d Φ Γ σ ℓ) → (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    (Term.sinkLet fuel u c b).eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ
  | 0, _, _, _, _, _, _, _, _, u, c, b, κ, ρ, jκ => by simp only [Term.sinkLet]
  | fuel + 1, _, _, _, _, _, _, _, _, u, c, b, κ, ρ, jκ => by
      cases b with
      | letE u₂ c₂ b₂ =>
          simp only [Term.sinkLet]
          split
          · rfl
          · split
            · rename_i c₂' c' b₂' hc₂ hc hb₂
              rw [Term.eval_castLvl]
              simp only [Term.eval]
              rw [Term.sinkLet_eval fuel u c' b₂' κ _ jκ]
              simp only [Term.eval]
              have e₂ : c₂'.eval κ ρ = c₂.eval κ (Tuple.cons (c.eval κ ρ) ρ) :=
                Comp.rename_eval (KRen.Agree.id κ) (URen.Agree.drop _ ρ) c₂ hc₂
              have e₁ : c'.eval κ (Tuple.cons (c₂'.eval κ ρ) ρ) = c.eval κ ρ :=
                Comp.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) c hc
              rw [e₁]
              rw [Term.rename_eval (KRen.Agree.id κ) (URen.Agree.swap _ _ _ _ ρ)
                (JRen.Agree.id jκ) b₂ hb₂, e₂]
            · rfl
      | _ => simp only [Term.sinkLet]

theorem Term.numCalls_sinkLet : (fuel : Nat) → {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {σ τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → {o : Lvl} → (u : Usage1ω) →
    (c : Comp Δ d Φ Γ σ ℓ) → (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o) →
    (Term.sinkLet fuel u c b).numCalls = (Term.letE u c b).numCalls
  | 0, _, _, _, _, _, _, _, _, u, c, b => by simp only [Term.sinkLet]
  | fuel + 1, _, _, _, _, _, _, _, _, u, c, b => by
      cases b with
      | letE u₂ c₂ b₂ =>
          simp only [Term.sinkLet]
          split
          · rfl
          · split
            · rename_i c₂' c' b₂' hc₂ hc hb₂
              rw [Term.numCalls_castLvl]
              simp only [Term.numCalls]
              rw [Term.numCalls_sinkLet fuel u c' b₂']
              simp only [Term.numCalls]
              rw [Comp.numCalls_rename c₂ hc₂, Comp.numCalls_rename c hc,
                Term.numCalls_rename b₂ hb₂]
              omega
            · rfl
      | _ => simp only [Term.sinkLet]

/-- `let x [u] := c; b`, moved down when it is used once (`Term.sinkLet`). -/
def Term.sinkLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o) : Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ o)) :=
  if u = .one then Term.sinkLet Term.sinkFuel u c b else .letE u c b

theorem Term.sinkLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : (Term.sinkLetE u c b).eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  unfold Term.sinkLetE
  split
  · exact Term.sinkLet_eval _ u c b κ ρ jκ
  · rfl

theorem Term.numCalls_sinkLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o) :
    (Term.sinkLetE u c b).numCalls = (Term.letE u c b).numCalls := by
  unfold Term.sinkLetE
  split
  · exact Term.numCalls_sinkLet _ u c b
  · rfl

/-! ## The walk -/

mutual
/-- `Term.sinkWalk` inside the bodies of a value. -/
def Val.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.sinkWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.sinkWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.sinkWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.sinkWalk` in a body. -/
def Body.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.sinkWalk
  | _, _, _, _, _, _, .opened t h => .opened t.sinkWalk h
/-- `Term.sinkWalk` inside the bodies of a computation. -/
def Comp.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.sinkWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.sinkWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).sinkWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).sinkWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Computations used once moved to their use**, bottom-up (`Term.sinkLetE`). -/
def Term.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.sinkWalk b.sinkWalk
  | _, _, _, _, _, _, .letE u c b => Term.sinkLetE u c.sinkWalk b.sinkWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.sinkWalk
  | _, _, _, _, _, _, .branch br => .branch br.sinkWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.sinkWalk` in a branch. -/
def Branch.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.sinkWalk e.sinkWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).sinkWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.sinkWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.sinkWalk main.sinkWalk
/-- `Term.sinkWalk` in the branches of a union's case analysis. -/
def Branches.sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.sinkWalk b₂.sinkWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.sinkWalk bs.sinkWalk
end

mutual
theorem Val.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.sinkWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.sinkWalk, Val.eval]; funext x; rw [Body.sinkWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.sinkWalk, Val.eval]; rw [Body.sinkWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.sinkWalk, Val.eval]; rw [Body.sinkWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.sinkWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.sinkWalk, Body.eval]; exact Term.sinkWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.sinkWalk, Body.eval]; exact Term.sinkWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.sinkWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.sinkWalk, Comp.eval]
      congr 1; funext k acc; exact Body.sinkWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.sinkWalk, Comp.eval]
      congr 1; funext acc x; exact Body.sinkWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.sinkWalk, Comp.eval]
      congr 1; funext i x; exact Body.sinkWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.sinkWalk, Comp.eval]
      congr 1; funext i x; exact Body.sinkWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
/-- **Moving the computations used once to their uses does not change the value.** -/
theorem Term.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.sinkWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, _, _, _ => rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.sinkWalk, Term.eval, Val.sinkWalk_eval v, Term.sinkWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.sinkWalk]
      rw [Term.sinkLetE_eval]
      simp only [Term.eval, Comp.sinkWalk_eval c, Term.sinkWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.sinkWalk, Term.eval, Term.sinkWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.sinkWalk, Term.eval, Branch.sinkWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.sinkWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.sinkWalk, Branch.eval, Term.sinkWalk_eval t, Term.sinkWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.sinkWalk, Branch.eval]; exact Term.sinkWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.sinkWalk, Branch.eval]; exact Branches.sinkWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.sinkWalk, Branch.eval, Branch.sinkWalk_eval main,
        Term.sinkWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.sinkWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (jκ : JEnv Δ τ js) → ∀ x, br.sinkWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.sinkWalk, Branches.eval, Term.sinkWalk_eval b₁, Term.sinkWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.sinkWalk, Branches.eval, Term.sinkWalk_eval b,
        Branches.sinkWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

mutual
theorem Val.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.sinkWalk.numCalls = v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.sinkWalk, Val.numCalls]; exact Body.numCalls_sinkWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.sinkWalk, Val.numCalls]; exact Body.numCalls_sinkWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.sinkWalk, Val.numCalls]; exact Body.numCalls_sinkWalk b
  | _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.sinkWalk.numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.sinkWalk, Body.numCalls]; exact Term.numCalls_sinkWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.sinkWalk, Body.numCalls]; exact Term.numCalls_sinkWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.sinkWalk.numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.sinkWalk, Comp.numCalls]; exact Body.numCalls_sinkWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.sinkWalk, Comp.numCalls]; exact Body.numCalls_sinkWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.sinkWalk, Comp.numCalls]
      exact congrArg _ (funext fun i => Body.numCalls_sinkWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.sinkWalk, Comp.numCalls]
      exact congrArg _ (funext fun i => Body.numCalls_sinkWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ x => x
/-- **Moving the computations used once to their uses does not change the number of calls.** -/
theorem Term.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.sinkWalk.numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, .letV u v b => by
      simp only [Term.sinkWalk, Term.numCalls, Val.numCalls_sinkWalk v, Term.numCalls_sinkWalk b]
  | _, _, _, _, _, _, .letE u c b => by
      simp only [Term.sinkWalk]
      rw [Term.numCalls_sinkLetE]
      simp only [Term.numCalls, Comp.numCalls_sinkWalk c, Term.numCalls_sinkWalk b]
  | _, _, _, _, _, _, .record_casesOn us n b => by
      simp only [Term.sinkWalk, Term.numCalls, Term.numCalls_sinkWalk b]
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.sinkWalk, Term.numCalls, Branch.numCalls_sinkWalk br]
  | _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.sinkWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.sinkWalk, Branch.numCalls, Term.numCalls_sinkWalk t,
        Term.numCalls_sinkWalk e]
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.sinkWalk, Branch.numCalls]
      exact congrArg _ (funext fun i => Term.numCalls_sinkWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.sinkWalk, Branch.numCalls]; exact Branches.numCalls_sinkWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      simp only [Branch.sinkWalk, Branch.numCalls, Branch.numCalls_sinkWalk main,
        Term.numCalls_sinkWalk body]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_sinkWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.sinkWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      simp only [Branches.sinkWalk, Branches.numCalls, Term.numCalls_sinkWalk b₁,
        Term.numCalls_sinkWalk b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      simp only [Branches.sinkWalk, Branches.numCalls, Term.numCalls_sinkWalk b,
        Branches.numCalls_sinkWalk bs]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
