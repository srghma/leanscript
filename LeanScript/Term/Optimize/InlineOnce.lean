module

public import LeanScript.Term.Optimize.InlineSubst

@[expose] public section

set_option autoImplicit false

/-!
# Inlining a closure at its only call

`Term.retWalk` (`LeanScript.Term.Optimize.InlineRet`) inlines a known closure at a call only when
its body makes no call, so that inlining never adds calls even if the closure is called several
times.  A closure whose body makes calls can still be inlined when it is called **once**: its
body replaces the call and the closure disappears, so the calls of the body are moved, not
copied.

`Term.inlineAt` does it for the known closure described by a target (`InlTgt`): it walks the
statement and succeeds only when the closure is mentioned exactly once, by a call `let y := k a`
in a position the walk reaches (a `let`, a case analysis of a record, one arm of an `if` or of
a join point — not a body of a closure, a delay or a loop, which could run the call several
times or not at all); everything else is renamed to drop the closure.  At the call, the body is
put in place as in `Term.blockLetE` (`BlockFn.applyP`, `Term.bindRet`).

**Proved** (`LeanScript.Term.Optimize.InlineOnceEval`, `CountInlineOnce`): the value does not
change, and the result has the calls of the statement minus the call, plus those of the body.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The closure to inline: the renaming that drops it (and keeps everything else), and its body
    (seen from the target). -/
structure InlTgt (Δ : DSig ks) (Φ Φ' : KCtx ks) : Type where
  rk : KRen Φ Φ'
  get : ∀ {ty : Ty ks} {o : Lvl}, KVar Φ ty o → Option (BlockFn Δ Φ' ty)

/-- The closure bound by the innermost `val`. -/
def InlTgt.single {Φ : KCtx ks} {b : KBinder ks} (f : BlockFn Δ Φ b.ty) : InlTgt Δ (b :: Φ) Φ :=
  ⟨KRen.drop, fun {_ _} k => match k with
    | .head => some f
    | .tail _ => none⟩

/-- Under one more `val`. -/
def InlTgt.lift {Φ Φ' : KCtx ks} (T : InlTgt Δ Φ Φ') (b : KBinder ks) :
    InlTgt Δ (b :: Φ) (b :: Φ') :=
  ⟨KRen.lift T.rk b, fun {_ _} k => match k with
    | .head => none
    | .tail k => (T.get k).bind (·.rename KRen.wk1)⟩

/-- The body of the target at a call `c`, when `c` calls it. -/
def Comp.tgtCall? {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat} {js : JCtx ks}
    (T : InlTgt Δ Φ Φ') : Comp Δ d Φ Γ σ ℓ → Option ((o : Lvl) × Term Δ d Φ' Γ σ js o)
  | .app (.kvar k) a _ =>
      (T.get k).bind fun f => (a.rename T.rk URen.id).bind fun a' => f.applyP a'
  | _ => none

/-- `let y := c; b` where `c` calls the target: its body in place of the call. -/
def Term.tgtLetE {d : Nat} {Φ Φ' : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    {o' : Lvl} (T : InlTgt Δ Φ Φ') (u : Usage1ω) (c : Comp Δ d Φ Γ σ ℓ)
    (b : Term Δ d Φ (⟨σ, u.toUsage01ω, d⟩ :: Γ) τ js o') : Option ((o : Lvl) × Term Δ d Φ' Γ τ js o) :=
  (b.rename T.rk URen.id JRen.id).bind fun b' =>
    match b'.retHead? with
    | some h => (c.tgtCall? T (js := js)).map fun r => ⟨r.1, h.down ▸ r.2⟩
    | none => (c.tgtCall? T (js := [])).bind fun r => Term.bindRet r.2 b'

mutual
/-- **Inline the target at its only call** (`none` when it is not mentioned exactly once, by a
    call the walk reaches). -/
def Term.inlineAt : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → InlTgt Δ Φ Φ' → Term Δ d Φ Γ τ js o →
    Option ((o' : Lvl) × Term Δ d Φ' Γ τ js o')
  | _, _, _, _, _, _, _, _, .ret _ => none
  | _, _, _, _, _, _, _, _, .jump _ _ => none
  | _, _, _, _, _, _, _, T, .letV (σ := σ) (o := o) u v b =>
      (v.rename T.rk URen.id).bind fun v' =>
        (b.inlineAt (T.lift ⟨σ, u, o, true⟩)).map fun r => ⟨_, .letV u v' r.2⟩
  | _, _, _, _, _, _, _, T, .letE u c b =>
      match Term.tgtLetE T u c b with
      | some r => some r
      | none =>
          (c.rename T.rk URen.id).bind fun c' =>
            (b.inlineAt T).map fun r => ⟨_, .letE u c' r.2⟩
  | _, _, _, _, _, _, _, T, .record_casesOn us n b =>
      (n.rename T.rk URen.id).bind fun n' =>
        (b.inlineAt T).map fun r => ⟨_, .record_casesOn us n' r.2⟩
  | _, _, _, _, _, _, _, T, .branch br => (br.inlineAt T).map fun r => ⟨_, .branch r.2⟩
/-- `Term.inlineAt` in a branch: in exactly one arm. -/
def Branch.inlineAt : {d : Nat} → {Φ Φ' : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → InlTgt Δ Φ Φ' → Branch Δ d Φ Γ τ js ℓ →
    Option ((ℓ' : Nat) × Branch Δ d Φ' Γ τ js ℓ')
  | _, _, _, _, _, _, _, T, .ite c t e =>
      (c.rename T.rk URen.id).bind fun c' =>
        match t.rename T.rk URen.id JRen.id with
        | some t' => (e.inlineAt T).map fun r => ⟨_, .ite c' t' r.2⟩
        | none =>
            (t.inlineAt T).bind fun r =>
              (e.rename T.rk URen.id JRen.id).map fun e' => ⟨_, .ite c' r.2 e'⟩
  | _, _, _, _, _, _, _, _, .enum_casesOn _ _ => none
  | _, _, _, _, _, _, _, _, .union_casesOn _ _ => none
  | _, _, _, _, _, _, _, T, .join σ u uₓ body main =>
      match body.rename T.rk URen.id JRen.id with
      | some body' => (main.inlineAt T).map fun r => ⟨_, .join σ u uₓ body' r.2⟩
      | none =>
          (body.inlineAt T).bind fun r =>
            (main.rename T.rk URen.id JRen.id).map fun main' => ⟨_, .join σ u uₓ r.2 main'⟩
end

end LeanScript

end
