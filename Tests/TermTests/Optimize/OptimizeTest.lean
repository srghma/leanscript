module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The optimiser (`Term.optimize`)

Each rewrite of `LeanScript.Term.Optimize.Basic` on a small hand-written statement (the result is
checked by `rfl`), and the optimiser on translated programs: the value does not change
(`Term.optimize_run`), which is also checked on values.
-/

namespace OptimizeTest

open LeanScript

/-- Statements at depth `d` over the empty signature. -/
abbrev T (d : Nat) (Φ : KCtx []) (Γ : UCtx []) (τ : Ty []) (o : Lvl) : Type :=
  Term DSig.nil d Φ Γ τ [] o

/-- The innermost unknown, used. -/
abbrev x0 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage01ω} {ℓ : Nat}
    (h : u ≠ .zero := by decide) : PExpr DSig.nil Φ (⟨τ, u, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.head h))

/-- The unknown two binders further out. -/
abbrev x2 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage01ω} {ℓ : Nat} {b c : UBinder []}
    (h : u ≠ .zero := by decide) : PExpr DSig.nil Φ (b :: c :: ⟨τ, u, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.tail (.tail (.head h))))

/-! ## A shared answer is the answer -/

/-- `fun n => let a := share (n * 7); a`. -/
def sharedTail : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letE .one (.share (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil)) rfl))
        (.ret (x0 (τ := .nat))))))
    (.ret (.kvar .head))

/-- `fun n => n * 7`. -/
def sharedTailOpt : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil)) rfl)))))
    (.ret (.kvar .head))

example : sharedTail.optimize = sharedTailOpt := by rfl
example : sharedTail.optimize.run (6 : Nat) = (42 : Nat) := by rw [sharedTail.optimize_run]; rfl

/-! ## Copy propagation -/

/-- `fun n => let a := share n; a + a`, `a` used ω times. -/
def copy : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letE .many (.share (.var (.head (by decide))))
        (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil)) rfl))))))
    (.ret (.kvar .head))

/-- `fun n => n * 2`: after copy propagation the body is `n + n`, and the two copies of `n` in
    the sum are counted (`Term.arithWalk`); the parameter is now used once (recounted by
    `dce`). -/
def copyOpt : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat (2 : Nat)) .nil)) rfl)))))
    (.ret (.kvar .head))

example : copy.optimize = copyOpt := by rfl
example : copy.optimize.run (21 : Nat) = (42 : Nat) := by rw [copy.optimize_run]; rfl

/-! ## Dead case analysis -/

/-- `fun (p : Nat × Nat) => match p with | (_, _) => p`: the fields are never read. -/
def deadCases : T 0 [] [] (.fn (.record .nat (.one .nat)) (.record .nat (.one .nat))) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.record_casesOn (t := .nat) (fs := .one .nat) [.zero, .zero] (.var (.head (by decide)))
        (.ret (x2 (τ := .record .nat (.one .nat)))))))
    (.ret (.kvar .head))

/-- `fun p => p`. -/
def deadCasesOpt : T 0 [] [] (.fn (.record .nat (.one .nat)) (.record .nat (.one .nat))) none :=
  .letV .one
    (.lam (u := .one) (.closed (.ret (x0 (τ := .record .nat (.one .nat))))))
    (.ret (.kvar .head))

example : deadCases.optimize = deadCasesOpt := by rfl

/-! ## Nothing to do -/

/-- A term that has none of the patterns is unchanged. -/
def addOne : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (.lit .nat 1) .nil)) rfl)))))
    (.ret (.kvar .head))

example : addOne.optimize = addOne := by rfl

/-! ## Translated programs -/

def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

def sumToT := #leanscript_to_term sumTo

/-- The optimised translation computes the same function (for all inputs). -/
theorem sumToT_optimize (n : Nat) :
    (sumToT (Δ := DSig.nil)).optimize.run n = (sumToT (Δ := DSig.nil)).run n := by
  rw [Term.optimize_run]

example : ((sumToT (Δ := DSig.nil)).optimizeN 3).run (5 : Nat) = (10 : Nat) := by
  rw [Term.optimizeN_run]; kernel_rfl

end OptimizeTest

end
