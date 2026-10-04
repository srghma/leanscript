module

public import LeanScript.Term.Optimize.HoistExpr
public import LeanScript.Term.Optimize.InlineBlockEval
public import LeanScript.Term.Optimize.CountDce

@[expose] public section

set_option autoImplicit false

/-!
# Hoisting a call that every path computes

`Term.hoistAt t`: when a call of an extern on atoms `s` (`lean_int_repr(x)`, an `ENeu`)

* is **computed on every path** of the statement `t` at its depth (`Term.always`: in the
  answer, outside the arms of the conditionals; in a `let … := share …`; in the condition of a
  branch, or on every path of its arms; …), and
* **occurs at least twice** in `t` at its depth (`Term.occ`),

then `t` becomes `let x := s; t[x/s]`: the call is computed once, in front, and every
occurrence of it at the same depth — in answers, jumps, conditions, scrutinees, shared
expressions, the operands of calls (`let y := share s` is dropped, `y` renamed to `x`) — is replaced by `x`
(`Term.abstr`).  No path computes more than before (each already computed `s`), and the code
is shorter.  This shares

* a call repeated in one expression: `toString a ++ toString a` is `let x := toString a; x ++ x`;
* a call made by all the arms of a branch: `if c then f (toString n) else g (toString n)` is
  `let x := toString n; if c then f x else g x` (the case analyses of `match` often repeat it).

The call and its arguments are known to be the same by `Extern.beq` and `Atom.key`
(`ENeu.test`), so the language being pure and total, the second computation always gives the
value of the first: `Term.hoistAt_eval`.  `Term.hoistWalk` applies it at every statement,
bottom-up (`Term.hoistWalk_eval`).  It adds no call (`Term.numCalls_hoistWalk`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Replacing a call by a name in statements -/

section Abstr
variable {σ : Ty ks}

/-- `let y := c; b` where the calls `s` of `b` are already replaced (`r`): when `c` is
    `share s` itself, `b` with `y` renamed to `x`; otherwise `c` with its calls `s`
    replaced, and `r`. -/
def Term.abstrLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ' τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (u : Usage1ω) (c : Comp Δ d Φ Γ σ' ℓ)
    (r : (o' : Lvl) × Term Δ d Φ (⟨σ', u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (o' : Lvl) × Term Δ d Φ Γ τ js o' :=
  match c with
  | .share m =>
    if h : s.test m then
      match r.2.rename KRen.id (URen.subst (ENeu.test_ty h ▸ x) rfl) JRen.id with
      | some b' => ⟨_, b'⟩
      | none => ⟨_, .letE u (.share (m.abstr x s).2) r.2⟩
    else ⟨_, .letE u (.share (m.abstr x s).2) r.2⟩
  | .app f a h =>
    match Lvl.some? (Lvl.meet (f.abstr x s).1 (a.abstr x s).1) with
    | some h' => ⟨_, .letE u (.app (f.abstr x s).2 (a.abstr x s).2 h'.2) r.2⟩
    | none => ⟨_, .letE u (.app f a h) r.2⟩
  | c => ⟨_, .letE u c r.2⟩

theorem Term.abstrLetE_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ' τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ' ℓ) (b : Term Δ d Φ (⟨σ', u.toUsage01ω, d⟩ :: Γ) τ js o')
    (r : (o' : Lvl) × Term Δ d Φ (⟨σ', u.toUsage01ω, d⟩ :: Γ) τ js o')
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) (hx : ρ.get x = s.eval κ ρ)
    (hr : r.2.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ = b.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ) :
    (Term.abstrLetE x s u c r).2.eval κ ρ jκ = (Term.letE u c b).eval κ ρ jκ := by
  cases c with
  | share m =>
    simp only [Comp.eval] at hr
    simp only [Term.abstrLetE]
    by_cases h : s.test m = true
    · rw [dite_eq_left h]
      have hm : ρ.get (ENeu.test_ty h ▸ x) = m.eval κ ρ :=
        eq_of_heq ((UEnv.get_cast _ x ρ).trans (hx ▸ ENeu.test_eval h κ ρ))
      split
      · rename_i b' hb'
        rw [Term.rename_eval (KRen.Agree.id κ) (URen.Agree.subst _ rfl ρ) (JRen.Agree.id jκ) _ hb']
        simp only [Term.eval, Comp.eval]
        rw [hm]; exact hr
      · simp only [Term.eval, Comp.eval, Neu.abstr_eval x s κ ρ hx m]; exact hr
    · rw [dite_eq_right h]
      simp only [Term.eval, Comp.eval, Neu.abstr_eval x s κ ρ hx m]; exact hr
  | app f a h =>
    simp only [Comp.eval] at hr
    simp only [Term.abstrLetE]
    split
    · simp only [Term.eval, Comp.eval, PExpr.abstr_eval x s κ ρ hx f,
        PExpr.abstr_eval x s κ ρ hx a]; exact hr
    · simp only [Term.eval, Comp.eval]; exact hr
  | _ => simp only [Term.abstrLetE, Term.eval]; exact hr

mutual
/-- Every occurrence of the call `s` at the depth of the statement (in its answers, jumps,
    conditions, scrutinees and shared expressions) replaced by the unknown `x`. -/
def Term.abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → UVar Γ σ d → ENeu Φ Γ σ → Term Δ d Φ Γ τ js o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, x, s, .ret e => ⟨_, .ret (e.abstr x s).2⟩
  | _, _, _, _, _, _, x, s, .letV u v b => ⟨_, .letV u v (Term.abstr x (s.wkK _) b).2⟩
  | _, _, _, _, _, _, x, s, .letE u c b =>
      Term.abstrLetE x s u c (Term.abstr x.tail (s.wkU _) b)
  | _, _, _, _, _, _, x, s, .record_casesOn us n b =>
      ⟨_, .record_casesOn us (n.abstr x s).2 (Term.abstr (x.wkN _) (s.wkUN _) b).2⟩
  | _, _, _, _, _, _, x, s, .branch br => ⟨_, .branch (Branch.abstr x s br).2⟩
  | _, _, _, _, _, _, x, s, .jump j e => ⟨_, .jump j (e.abstr x s).2⟩
/-- `Term.abstr` in a branch. -/
def Branch.abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → UVar Γ σ d → ENeu Φ Γ σ → Branch Δ d Φ Γ τ js ℓ →
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, x, s, .ite c t e =>
      ⟨_, .ite (c.abstr x s).2 (Term.abstr x s t).2 (Term.abstr x s e).2⟩
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs =>
      ⟨_, .enum_casesOn (e.abstr x s).2 (fun i => (Term.abstr x s (bs i)).2)⟩
  | _, _, _, _, _, _, x, s, .union_casesOn e bs =>
      ⟨_, .union_casesOn (e.abstr x s).2 (Branches.abstr x s bs).2⟩
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main =>
      ⟨_, .join σ' u uₓ (Term.abstr x.tail (s.wkU _) body).2 (Branch.abstr x s main).2⟩
/-- `Term.abstr` in the branches of a union's case analysis. -/
def Branches.abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    UVar Γ σ d → ENeu Φ Γ σ → Branches Δ d Φ Γ cs τ js o →
    (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (Term.abstr (x.wkN _) (s.wkUN _) b₁).2
        (Term.abstr (x.wkN _) (s.wkUN _) b₂).2⟩
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs =>
      ⟨_, .cons us (Term.abstr (x.wkN _) (s.wkUN _) b).2 (Branches.abstr x s bs).2⟩
end

mutual
theorem Term.abstr_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) →
    (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    ρ.get x = s.eval κ ρ → (Term.abstr x s t).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, x, s, .ret e, κ, ρ, _, hx => by
      simp only [Term.abstr, Term.eval, PExpr.abstr_eval x s κ ρ hx e]
  | _, _, _, _, _, _, x, s, .letV u v b, κ, ρ, jκ, hx => by
      simp only [Term.abstr, Term.eval]
      exact Term.abstr_eval x (s.wkK _) b _ ρ jκ (by simp [hx])
  | _, _, _, _, _, _, x, s, .letE u c b, κ, ρ, jκ, hx =>
      Term.abstrLetE_eval x s u c b _ κ ρ jκ hx
        (Term.abstr_eval x.tail (s.wkU _) b κ _ jκ (by simp [hx]))
  | _, _, _, _, _, _, x, s, .record_casesOn us n b, κ, ρ, jκ, hx => by
      simp only [Term.abstr, Term.eval, Neu.abstr_eval x s κ ρ hx n]
      exact Term.abstr_eval (x.wkN _) (s.wkUN _) b κ _ jκ
        (by rw [UVar.wkN_get, ENeu.wkUN_eval, hx])
  | _, _, _, _, _, _, x, s, .branch br, κ, ρ, jκ, hx => by
      simp only [Term.abstr, Term.eval]
      exact Branch.abstr_eval x s br κ ρ jκ hx
  | _, _, _, _, _, _, x, s, .jump j e, κ, ρ, _, hx => by
      simp only [Term.abstr, Term.eval, PExpr.abstr_eval x s κ ρ hx e]
  termination_by structural _ _ _ _ _ _ _ _ t => t
theorem Branch.abstr_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) →
    (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
    ρ.get x = s.eval κ ρ → (Branch.abstr x s br).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, x, s, .ite c t e, κ, ρ, jκ, hx => by
      simp only [Branch.abstr, Branch.eval, Neu.abstr_eval x s κ ρ hx c,
        Term.abstr_eval x s t κ ρ jκ hx, Term.abstr_eval x s e κ ρ jκ hx]
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs, κ, ρ, jκ, hx => by
      simp only [Branch.abstr, Branch.eval]
      have he := Neu.abstr_eval x s κ ρ hx e
      generalize (Neu.abstr x s e).snd.eval κ ρ = i at he ⊢
      subst he
      exact Term.abstr_eval x s _ κ ρ jκ hx
  | _, _, _, _, _, _, x, s, .union_casesOn e bs, κ, ρ, jκ, hx => by
      simp only [Branch.abstr, Branch.eval, Neu.abstr_eval x s κ ρ hx e]
      exact Branches.abstr_eval x s bs κ ρ jκ hx _
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main, κ, ρ, jκ, hx => by
      simp only [Branch.abstr, Branch.eval]
      rw [Branch.abstr_eval x s main κ ρ _ hx]
      congr 2
      funext v
      exact Term.abstr_eval x.tail (s.wkU _) body κ _ jκ (by simp [hx])
  termination_by structural _ _ _ _ _ _ _ _ br => br
theorem Branches.abstr_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → ρ.get x = s.eval κ ρ →
    ∀ v, (Branches.abstr x s br).2.eval κ ρ jκ v = br.eval κ ρ jκ v
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, hx, v => by
      simp only [Branches.abstr, Branches.eval]
      congr 1 <;> funext w <;>
        exact Term.abstr_eval (x.wkN _) (s.wkUN _) _ κ _ jκ
          (by rw [UVar.wkN_get, ENeu.wkUN_eval, hx])
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs, κ, ρ, jκ, hx, v => by
      simp only [Branches.abstr, Branches.eval]
      congr 1
      · funext w
        exact Term.abstr_eval (x.wkN _) (s.wkUN _) _ κ _ jκ
          (by rw [UVar.wkN_get, ENeu.wkUN_eval, hx])
      · funext r
        exact Branches.abstr_eval x s bs κ ρ jκ hx r
  termination_by structural _ _ _ _ _ _ _ _ _ _ br => br
end

end Abstr

/-! ## The counts of the heuristics, in statements -/

section Counts
variable {σ : Ty ks}

/-- Is `f i` true for every `i : Fin n`? -/
def Fin.allB : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && Fin.allB n (fun i => f i.succ)

/-- The lists `f i`, for every `i : Fin n`, one after the other. -/
def Fin.concatL {α : Type} : (n : Nat) → (Fin n → List α) → List α
  | 0, _ => []
  | n + 1, f => f 0 ++ Fin.concatL n (fun i => f i.succ)

/-- The occurrences of the call `s` in a computation that `Term.abstr` replaces (in a shared
    expression). -/
def Comp.occS {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (s : ENeu Φ Γ σ) :
    Comp Δ d Φ Γ τ ℓ → Nat
  | .share m => m.occ s
  | .app f a _ => f.occ s + a.occ s
  | _ => 0

/-- Does the computation compute the call `s` (in a shared expression)? -/
def Comp.alwaysS {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} (s : ENeu Φ Γ σ) :
    Comp Δ d Φ Γ τ ℓ → Bool
  | .share m => m.always s
  | .app f a _ => f.always s || a.always s
  | _ => false

/-- The calls of externs on atoms in a shared expression. -/
def Comp.candsS {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ τ ℓ → List (SomeNeu Δ Φ Γ)
  | .share m => m.cands
  | .app f a _ => f.cands ++ a.cands
  | _ => []

mutual
/-- How many times the call `s` occurs at the depth of the statement (where `Term.abstr`
    replaces it). -/
def Term.occ : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → ENeu Φ Γ σ → Term Δ d Φ Γ τ js o → Nat
  | _, _, _, _, _, _, s, .ret e => e.occ s
  | _, _, _, _, _, _, s, .letV _ _ b => Term.occ (s.wkK _) b
  | _, _, _, _, _, _, s, .letE _ c b => c.occS s + Term.occ (s.wkU _) b
  | _, _, _, _, _, _, s, .record_casesOn _ n b => n.occ s + Term.occ (s.wkUN _) b
  | _, _, _, _, _, _, s, .branch br => Branch.occ s br
  | _, _, _, _, _, _, s, .jump _ e => e.occ s
/-- `Term.occ` in a branch. -/
def Branch.occ : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → ENeu Φ Γ σ → Branch Δ d Φ Γ τ js ℓ → Nat
  | _, _, _, _, _, _, s, .ite c t e => c.occ s + Term.occ s t + Term.occ s e
  | _, _, _, _, _, _, s, .enum_casesOn e bs => e.occ s + Fin.sumNat _ (fun i => Term.occ s (bs i))
  | _, _, _, _, _, _, s, .union_casesOn e bs => e.occ s + Branches.occ s bs
  | _, _, _, _, _, _, s, .join _ _ _ body main => Term.occ (s.wkU _) body + Branch.occ s main
/-- `Term.occ` in the branches of a union's case analysis. -/
def Branches.occ : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    ENeu Φ Γ σ → Branches Δ d Φ Γ cs τ js o → Nat
  | _, _, _, _, _, _, _, _, s, .two _ _ b₁ b₂ => Term.occ (s.wkUN _) b₁ + Term.occ (s.wkUN _) b₂
  | _, _, _, _, _, _, _, _, s, .cons _ b bs => Term.occ (s.wkUN _) b + Branches.occ s bs
end

mutual
/-- Is the call `s` computed, at the depth of the statement, on every path of it (before it
    ends, or jumps)? -/
def Term.always : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → ENeu Φ Γ σ → Term Δ d Φ Γ τ js o → Bool
  | _, _, _, _, _, _, s, .ret e => e.always s
  | _, _, _, _, _, _, s, .letV _ _ b => Term.always (s.wkK _) b
  | _, _, _, _, _, _, s, .letE _ c b => c.alwaysS s || Term.always (s.wkU _) b
  | _, _, _, _, _, _, s, .record_casesOn _ n b => n.always s || Term.always (s.wkUN _) b
  | _, _, _, _, _, _, s, .branch br => Branch.always s br
  | _, _, _, _, _, _, s, .jump _ e => e.always s
/-- `Term.always` in a branch: in the condition or scrutinee, or on every path of every arm
    (of the statement of a join point: a jump computes it only if its argument does). -/
def Branch.always : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → ENeu Φ Γ σ → Branch Δ d Φ Γ τ js ℓ → Bool
  | _, _, _, _, _, _, s, .ite c t e => c.always s || (Term.always s t && Term.always s e)
  | _, _, _, _, _, _, s, .enum_casesOn e bs =>
      e.always s || Fin.allB _ (fun i => Term.always s (bs i))
  | _, _, _, _, _, _, s, .union_casesOn e bs => e.always s || Branches.always s bs
  | _, _, _, _, _, _, s, .join _ _ _ _ main => Branch.always s main
/-- `Term.always` in every branch of a union's case analysis. -/
def Branches.always : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    ENeu Φ Γ σ → Branches Δ d Φ Γ cs τ js o → Bool
  | _, _, _, _, _, _, _, _, s, .two _ _ b₁ b₂ =>
      Term.always (s.wkUN _) b₁ && Term.always (s.wkUN _) b₂
  | _, _, _, _, _, _, _, _, s, .cons _ b bs => Term.always (s.wkUN _) b && Branches.always s bs
end

mutual
/-- The calls of externs on atoms of the statement that are in its own context (not under a
    binder): the candidates of `Term.hoistAt`. -/
def Term.cands : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → List (SomeNeu Δ Φ Γ)
  | _, _, _, _, _, _, .ret e => e.cands
  | _, _, _, _, _, _, .letV _ _ _ => []
  | _, _, _, _, _, _, .letE _ c _ => c.candsS
  | _, _, _, _, _, _, .record_casesOn _ n _ => n.cands
  | _, _, _, _, _, _, .branch br => Branch.cands br
  | _, _, _, _, _, _, .jump _ e => e.cands
/-- `Term.cands` in a branch. -/
def Branch.cands : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → List (SomeNeu Δ Φ Γ)
  | _, _, _, _, _, _, .ite c t e => c.cands ++ Term.cands t ++ Term.cands e
  | _, _, _, _, _, _, .enum_casesOn e bs => e.cands ++ Fin.concatL _ (fun i => Term.cands (bs i))
  | _, _, _, _, _, _, .union_casesOn e _ => e.cands
  | _, _, _, _, _, _, .join _ _ _ _ main => Branch.cands main
end

end Counts

/-! ## The rewrite -/

/-- Is the call a conversion between a fixed-width unsigned integer and its bit vector
    (`UInt32.ofBitVec`, `UInt32.toBitVec`)?  It is the identity in JavaScript, so naming it
    would only add a copy (`const x$1 = a;`): it is never hoisted. -/
def Neu.isUIntBitVecConv {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ Γ τ ℓ → Bool
  | .extern (.preludeExtern .lean_uint8_of_nat_mk) _ _
  | .extern (.preludeExtern .lean_uint16_of_nat_mk) _ _
  | .extern (.preludeExtern .lean_uint32_of_nat_mk) _ _
  | .extern (.preludeExtern .lean_uint64_of_nat_mk) _ _
  | .extern (.preludeExtern .lean_uint8_to_nat__UInt8_toBitVec) _ _
  | .extern (.preludeExtern .lean_uint16_to_nat__UInt16_toBitVec) _ _
  | .extern (.preludeExtern .lean_uint32_to_nat__UInt32_toBitVec) _ _
  | .extern (.preludeExtern .lean_uint64_to_nat__UInt64_toBitVec) _ _ => true
  | _ => false

/-- The first candidate call that every path of `t` computes and that occurs at least twice
    (a conversion that is the identity in JavaScript excepted, `Neu.isUIntBitVecConv`). -/
def Term.pickHoist {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Option (SomeNeu Δ Φ Γ) :=
  t.cands.find? fun ⟨_, _, n⟩ =>
    !n.isUIntBitVecConv &&
    match ENeu.ofNeu? n with
    | some s => decide (2 ≤ Term.occ s t) && Term.always s t
    | none => false

/-- `let x := s; t[x/s]` for the call `s` chosen by `Term.pickHoist` (when the level comes out
    the same), and `t` otherwise. -/
def Term.hoistAt {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  match t.pickHoist with
  | some ⟨σ, ℓ, n⟩ =>
    match ENeu.ofNeu? n with
    | some s =>
      match t.rename KRen.id (URen.wk1 (b := ⟨σ, Usage1ω.many.toUsage01ω, d⟩)) JRen.id with
      | some t' =>
        let r := Term.abstr (.head (Usage1ω.toUsage01ω_ne_zero .many)) (s.wkU _) t'
        if h : some (Lvl.meetL ℓ r.1) = o then (Term.letE .many (.share n) r.2).castLvl h
        else t
      | none => t
    | none => t
  | none => t

theorem Term.hoistAt_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.hoistAt.eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.hoistAt
  split
  · rename_i σ ℓ n _
    split
    · rename_i s hs
      split
      · rename_i t' ht'
        simp only
        by_cases h : some (Lvl.meetL ℓ (Term.abstr (.head (Usage1ω.toUsage01ω_ne_zero .many))
            (s.wkU ⟨σ, Usage1ω.many.toUsage01ω, d⟩) t').1) = o
        · rw [dite_eq_left h, Term.eval_castLvl]
          simp only [Term.eval, Comp.eval]
          rw [Term.abstr_eval _ _ t' κ _ jκ (by
            rw [ENeu.wkU_eval, UEnv.get_cons_head, ENeu.ofNeu?_eval n hs κ ρ])]
          exact Term.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) (JRen.Agree.id jκ) t ht'
        · rw [dite_eq_right h]
      · rfl
    · rfl
  · rfl

/-! ## The walk -/

mutual
/-- `Term.hoistWalk` inside the bodies of a value. -/
def Val.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.hoistWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.hoistWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.hoistWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.hoistWalk` in a body. -/
def Body.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.hoistWalk
  | _, _, _, _, _, _, .opened t h => .opened t.hoistWalk h
/-- `Term.hoistWalk` inside the bodies of a computation. -/
def Comp.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.hoistWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.hoistWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).hoistWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).hoistWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The hoisting walk**: bottom-up, `Term.hoistAt` at every statement. -/
def Term.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => Term.hoistAt (.ret e)
  | _, _, _, _, _, _, .letV u v b => Term.hoistAt (.letV u v.hoistWalk b.hoistWalk)
  | _, _, _, _, _, _, .letE u c b => Term.hoistAt (.letE u c.hoistWalk b.hoistWalk)
  | _, _, _, _, _, _, .record_casesOn us n b => Term.hoistAt (.record_casesOn us n b.hoistWalk)
  | _, _, _, _, _, _, .branch br => Term.hoistAt (.branch br.hoistWalk)
  | _, _, _, _, _, _, .jump j e => Term.hoistAt (.jump j e)
/-- `Term.hoistWalk` in a branch. -/
def Branch.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.hoistWalk e.hoistWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e (fun i => (bs i).hoistWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.hoistWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.hoistWalk main.hoistWalk
/-- `Term.hoistWalk` in the branches of a union's case analysis. -/
def Branches.hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.hoistWalk b₂.hoistWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.hoistWalk bs.hoistWalk
end

mutual
theorem Val.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.hoistWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.hoistWalk, Val.eval]; funext x; rw [Body.hoistWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.hoistWalk, Val.eval]; rw [Body.hoistWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.hoistWalk, Val.eval]; rw [Body.hoistWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.hoistWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.hoistWalk, Body.eval]; exact Term.hoistWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.hoistWalk, Body.eval]; exact Term.hoistWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.hoistWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.hoistWalk, Comp.eval]
      congr 1; funext k acc; exact Body.hoistWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.hoistWalk, Comp.eval]
      congr 1; funext acc x; exact Body.hoistWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.hoistWalk, Comp.eval]
      congr 1; funext i x; exact Body.hoistWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.hoistWalk, Comp.eval]
      congr 1; funext i x; exact Body.hoistWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.hoistWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
      simp only [Term.eval, Val.hoistWalk_eval v, Term.hoistWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
      simp only [Term.eval, Comp.hoistWalk_eval c, Term.hoistWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
      simp only [Term.eval, Term.hoistWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
      simp only [Term.eval, Branch.hoistWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, κ, ρ, jκ => by
      simp only [Term.hoistWalk]; rw [Term.hoistAt_eval]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.hoistWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.hoistWalk, Branch.eval, Term.hoistWalk_eval t, Term.hoistWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.hoistWalk, Branch.eval]; exact Term.hoistWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.hoistWalk, Branch.eval]; exact Branches.hoistWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.hoistWalk, Branch.eval, Branch.hoistWalk_eval main,
        Term.hoistWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.hoistWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.hoistWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.hoistWalk, Branches.eval, Term.hoistWalk_eval b₁,
        Term.hoistWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.hoistWalk, Branches.eval, Term.hoistWalk_eval b,
        Branches.hoistWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

section Count
variable {σ : Ty ks}

theorem Term.numCalls_abstrLetE {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ' τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} (x : UVar Γ σ d) (s : ENeu Φ Γ σ) (u : Usage1ω)
    (c : Comp Δ d Φ Γ σ' ℓ) (r : (o' : Lvl) × Term Δ d Φ (⟨σ', u.toUsage01ω, d⟩ :: Γ) τ js o') :
    (Term.abstrLetE x s u c r).2.numCalls ≤ c.numCalls + r.2.numCalls := by
  cases c with
  | share m =>
    simp only [Term.abstrLetE]
    by_cases h : s.test m = true
    · rw [dite_eq_left h]
      split
      · rename_i b' hb'
        rw [Term.numCalls_rename _ hb']; simp only [Comp.numCalls]; omega
      · simp only [Term.numCalls, Comp.numCalls]; omega
    · rw [dite_eq_right h]; simp only [Term.numCalls, Comp.numCalls]; omega
  | app f a h =>
    simp only [Term.abstrLetE]
    split <;> simp only [Term.numCalls, Comp.numCalls] <;> omega
  | _ => simp only [Term.abstrLetE, Term.numCalls]; omega

mutual
theorem Term.numCalls_abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) →
    (t : Term Δ d Φ Γ τ js o) → (Term.abstr x s t).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, _, _, .ret _ => Nat.le_refl _
  | _, _, _, _, _, _, x, s, .letV u v b => by
      have := Term.numCalls_abstr x (s.wkK _) b
      simp only [Term.abstr, Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .letE u c b => by
      have hb := Term.numCalls_abstr x.tail (s.wkU _) b
      have := Term.numCalls_abstrLetE x s u c (Term.abstr x.tail (s.wkU _) b)
      simp only [Term.abstr, Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .record_casesOn us n b => by
      have := Term.numCalls_abstr (x.wkN _) (s.wkUN _) b
      simp only [Term.abstr, Term.numCalls]; omega
  | _, _, _, _, _, _, x, s, .branch br => by
      simp only [Term.abstr, Term.numCalls]; exact Branch.numCalls_abstr x s br
  | _, _, _, _, _, _, _, _, .jump _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ _ _ t => t
theorem Branch.numCalls_abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) →
    (br : Branch Δ d Φ Γ τ js ℓ) → (Branch.abstr x s br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, x, s, .ite c t e => by
      have ht := Term.numCalls_abstr x s t
      have he := Term.numCalls_abstr x s e
      simp only [Branch.abstr, Branch.numCalls]; omega
  | _, _, _, _, _, _, x, s, .enum_casesOn e bs => by
      simp only [Branch.abstr, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_abstr x s (bs i))
  | _, _, _, _, _, _, x, s, .union_casesOn e bs => by
      simp only [Branch.abstr, Branch.numCalls]; exact Branches.numCalls_abstr x s bs
  | _, _, _, _, _, _, x, s, .join σ' u uₓ body main => by
      have hb := Term.numCalls_abstr x.tail (s.wkU _) body
      have hm := Branch.numCalls_abstr x s main
      simp only [Branch.abstr, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ br => br
theorem Branches.numCalls_abstr : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (x : UVar Γ σ d) → (s : ENeu Φ Γ σ) → (br : Branches Δ d Φ Γ cs τ js o) →
    (Branches.abstr x s br).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, x, s, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_abstr (x.wkN _) (s.wkUN _) b₁
      have h₂ := Term.numCalls_abstr (x.wkN _) (s.wkUN _) b₂
      simp only [Branches.abstr, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, x, s, .cons us b bs => by
      have h₁ := Term.numCalls_abstr (x.wkN _) (s.wkUN _) b
      have h₂ := Branches.numCalls_abstr x s bs
      simp only [Branches.abstr, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ _ _ br => br
end

end Count

theorem Term.numCalls_hoistAt {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) : t.hoistAt.numCalls ≤ t.numCalls := by
  unfold Term.hoistAt
  split
  · rename_i σ ℓ n _
    split
    · rename_i s hs
      split
      · rename_i t' ht'
        simp only
        by_cases h : some (Lvl.meetL ℓ (Term.abstr (.head (Usage1ω.toUsage01ω_ne_zero .many))
            (s.wkU ⟨σ, Usage1ω.many.toUsage01ω, d⟩) t').1) = o
        · rw [dite_eq_left h, Term.numCalls_castLvl]
          have := Term.numCalls_abstr (.head (Usage1ω.toUsage01ω_ne_zero .many))
            (s.wkU ⟨σ, Usage1ω.many.toUsage01ω, d⟩) t'
          rw [Term.numCalls_rename t ht'] at this
          simp only [Term.numCalls, Comp.numCalls]; omega
        · rw [dite_eq_right h]; exact Nat.le_refl _
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  · exact Nat.le_refl _

mutual
theorem Val.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.hoistWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.hoistWalk, Val.numCalls]; exact Body.numCalls_hoistWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.hoistWalk, Val.numCalls]; exact Body.numCalls_hoistWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.hoistWalk, Val.numCalls]; exact Body.numCalls_hoistWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.hoistWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.hoistWalk, Body.numCalls]; exact Term.numCalls_hoistWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.hoistWalk, Body.numCalls]; exact Term.numCalls_hoistWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.hoistWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.hoistWalk, Comp.numCalls]; exact Body.numCalls_hoistWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.hoistWalk, Comp.numCalls]; exact Body.numCalls_hoistWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.hoistWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_hoistWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.hoistWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_hoistWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **The hoisting walk does not add calls.** -/
theorem Term.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.hoistWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret e => by
      simp only [Term.hoistWalk]; exact Term.numCalls_hoistAt _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_hoistWalk v
      have hb := Term.numCalls_hoistWalk b
      have := Term.numCalls_hoistAt (.letV u v.hoistWalk b.hoistWalk)
      simp only [Term.hoistWalk, Term.numCalls] at this ⊢; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_hoistWalk c
      have hb := Term.numCalls_hoistWalk b
      have := Term.numCalls_hoistAt (.letE u c.hoistWalk b.hoistWalk)
      simp only [Term.hoistWalk, Term.numCalls] at this ⊢; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      have hb := Term.numCalls_hoistWalk b
      have := Term.numCalls_hoistAt (.record_casesOn us n b.hoistWalk)
      simp only [Term.hoistWalk, Term.numCalls] at this ⊢; omega
  | _, _, _, _, _, _, .branch br => by
      have hb := Branch.numCalls_hoistWalk br
      have := Term.numCalls_hoistAt (.branch br.hoistWalk)
      simp only [Term.hoistWalk, Term.numCalls] at this ⊢; omega
  | _, _, _, _, _, _, .jump j e => by
      simp only [Term.hoistWalk]; exact Term.numCalls_hoistAt _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.hoistWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have ht := Term.numCalls_hoistWalk t
      have he := Term.numCalls_hoistWalk e
      simp only [Branch.hoistWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      simp only [Branch.hoistWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_hoistWalk (bs i))
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.hoistWalk, Branch.numCalls]; exact Branches.numCalls_hoistWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have hb := Term.numCalls_hoistWalk body
      have hm := Branch.numCalls_hoistWalk main
      simp only [Branch.hoistWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_hoistWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.hoistWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_hoistWalk b₁
      have h₂ := Term.numCalls_hoistWalk b₂
      simp only [Branches.hoistWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_hoistWalk b
      have h₂ := Branches.numCalls_hoistWalk bs
      simp only [Branches.hoistWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
