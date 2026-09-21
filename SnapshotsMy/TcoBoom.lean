import LeanScript.Term.Elab
-- Without the proof this function triples n at every step and diverges for every
-- input.  With h : Safe n the else-branch is dead code: omega derives False from
-- h (which unfolds to n = 1) and hn (n ≠ 1), so the impossible recursive call
-- `boom (3 * n)` never executes and Lean still accepts the termination proof.

/-- Only n = 1 is a safe starting point; every other value diverges. -/
def Safe (n : Nat) : Prop := n = 1

/-- Triples its argument at every step — obviously diverges for n ≠ 1.
    The proof `h : Safe n` rules out all other inputs:
    the else-branch is unreachable, proven by contradiction. -/
def boom (n : Nat) (h : Safe n) : Nat :=
  if hn : n = 1 then
    0                              -- the one terminating case
  else
    boom (3 * n)                   -- blatant divergence: 1 → 3 → 9 → 27 → …
      (by simp [Safe] at h; omega) -- h : n = 1, hn : n ≠ 1 ⊢ False → anything
termination_by n
decreasing_by
  simp [Safe] at h  -- h : n = 1
  omega             -- n = 1 ∧ n ≠ 1 ⊢ False ⊢ 3 * n < n

example : boom 1 (by simp [Safe]) = 0 := by grind only [boom]

/-! ## Generated `LeanFunction`s

One report per public function of this file; see `LeanScript.Term.Elab`. -/

/--
info: LeanFunction boom
  signature   : (n : Nat) → Safe n → Nat
  argTy       : nat
  resTy       : nat
  recursion   : well-founded       (encoded as Term.wfFix: relation and Acc proof sealed inside)
  status      : representable in Term
  primitives  : -
  context     : -
-/
#guard_msgs in
#leanjs_generate_term_and_ctx_for boom
