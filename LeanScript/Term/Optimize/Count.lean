module

public import LeanScript.Term.Syntax.Term

@[expose] public section

set_option autoImplicit false

/-!
# Counting the calls of a statement

`Term.numCalls t` is the number of *calls* written in `t`: the computations `f a` (`Comp.app`),
`t.get` (`Comp.thunk_force`) and `t ()` (`Comp.lazy_force`), counted syntactically everywhere,
including inside closures, delays, loop bodies, branches and join points.  It measures what
the optimiser saves: `Tests/TermTests/Optimize/CseTest.lean` states, for instance, that the
optimiser takes the translation of `EsPrecedence01.test1`, which calls its lazy argument five
times, to a statement that calls it once.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The sum of `f i` over `i : Fin n`. -/
def Fin.sumNat : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + Fin.sumNat n (fun i => f i.succ)

mutual
/-- The calls inside the bodies of a value. -/
def Val.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Nat
  | _, _, _, _, _, .lam b => b.numCalls
  | _, _, _, _, _, .thunk_mk b => b.numCalls
  | _, _, _, _, _, .lazy_mk b => b.numCalls
  | _, _, _, _, _, .record_mk _ => 0
  | _, _, _, _, _, .union_mk _ _ => 0
  | _, _, _, _, _, .array_mk _ => 0
  | _, _, _, _, _, .list_mk _ => 0
  | _, _, _, _, _, .data_in _ _ _ => 0
/-- The calls in a body. -/
def Body.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Nat
  | _, _, _, _, _, _, .closed t => t.numCalls
  | _, _, _, _, _, _, .opened t _ => t.numCalls
/-- The calls of a computation: one for a call, plus those in its bodies. -/
def Comp.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Nat
  | _, _, _, _, _, .app _ _ _ => 1
  | _, _, _, _, _, .share _ => 0
  | _, _, _, _, _, .nat_rec _ _ s _ => s.numCalls
  | _, _, _, _, _, .array_foldl _ _ s _ => s.numCalls
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => Fin.sumNat _ (fun i => (brs i).numCalls)
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => Fin.sumNat _ (fun i => (brs i).numCalls)
  | _, _, _, _, _, .thunk_force _ => 1
  | _, _, _, _, _, .lazy_force _ => 1
/-- **The number of calls written in a statement.** -/
def Term.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Nat
  | _, _, _, _, _, _, .ret _ => 0
  | _, _, _, _, _, _, .letV _ v b => v.numCalls + b.numCalls
  | _, _, _, _, _, _, .letE _ c b => c.numCalls + b.numCalls
  | _, _, _, _, _, _, .record_casesOn _ _ b => b.numCalls
  | _, _, _, _, _, _, .branch br => br.numCalls
  | _, _, _, _, _, _, .jump _ _ => 0
/-- The calls in a branch (all its arms and join points). -/
def Branch.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Nat
  | _, _, _, _, _, _, .ite _ t e => t.numCalls + e.numCalls
  | _, _, _, _, _, _, .enum_casesOn _ bs => Fin.sumNat _ (fun i => (bs i).numCalls)
  | _, _, _, _, _, _, .union_casesOn _ bs => bs.numCalls
  | _, _, _, _, _, _, .join _ _ _ body main => body.numCalls + main.numCalls
/-- The calls in the branches of a union's case analysis. -/
def Branches.numCalls : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Nat
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => b₁.numCalls + b₂.numCalls
  | _, _, _, _, _, _, _, _, .cons _ b bs => b.numCalls + bs.numCalls
end

end LeanScript

end
