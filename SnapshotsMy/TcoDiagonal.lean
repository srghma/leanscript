/-
`diagonal`, a tail-recursive version `diagonal_tr`, and an imperative `while`-loop
version `diagonalWhile`, together with proofs that all three agree.

This file is written for **Lean v4.34.0** (toolchain `leanprover/lean4:v4.34.0`) and
uses the experimental `mvcgen` verification-condition generator from `Std.Tactic.Do`.
It only needs the Lean core library / `Std`; no external packages are required.
-/
import Std.Tactic.Do

def diagonal : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     n + 1 => diagonal n 0 + 1
  | m + 1, n     => diagonal m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals omega

/-! ### Unfolding lemmas for `diagonal` -/

@[simp] theorem diagonal_zero_zero : diagonal 0 0 = 0 := by rw [diagonal]

@[simp] theorem diagonal_zero_succ (n : Nat) : diagonal 0 (n + 1) = diagonal n 0 + 1 := by
  rw [diagonal]

@[simp] theorem diagonal_succ (m n : Nat) : diagonal (m + 1) n = diagonal m (n + 1) + 1 := by
  rw [diagonal]

def diagonal_tr (m n acc : Nat) : Nat :=
  match m, n with
  | 0,     0     => acc
  | 0,     n + 1 => diagonal_tr n 0 (acc + 1)
  | m + 1, n     => diagonal_tr m (n + 1) (acc + 1)
  termination_by (m + n, m)
  decreasing_by all_goals omega

def diagonalWhile (m n : Nat) : Nat := Id.run do
  let mut m := m
  let mut n := n
  let mut acc := 0

  while m != 0 || n != 0 do
    acc := acc + 1
    if m > 0 then
      m := m - 1
      n := n + 1
    else
      -- Here m == 0 and n > 0
      m := n - 1
      n := 0

  return acc

-- Lemma: Generalized accumulator invariant
theorem diagonal_tr_eq (m n acc : Nat) :
    diagonal_tr m n acc = diagonal m n + acc := by
  induction m, n using diagonal.induct generalizing acc with
  | case1 =>
    -- Base case: m = 0, n = 0
    unfold diagonal diagonal_tr
    omega
  | case2 n ih =>
    -- Step: m = 0, n + 1
    unfold diagonal diagonal_tr
    rw [ih (acc + 1)]
    omega
  | case3 m n ih =>
    -- Step: m + 1, n
    unfold diagonal diagonal_tr
    rw [ih (acc + 1)]
    omega

-- Main Theorem: diagonal_tr with acc = 0 equals diagonal
theorem diagonal_tr_zero_eq_diagonal (m n : Nat) :
    diagonal_tr m n 0 = diagonal m n := by
  rw [diagonal_tr_eq]
  omega

open Std Do in
/-- The imperative `while`-loop version computes `diagonal`.

The loop state is the triple `(m, n, acc)`.
* The termination measure (`inv1`) is `diagonal m n`, which strictly decreases at each
  iteration.
* The loop invariant (`inv2`) is `acc + diagonal m n = diagonal m₀ n₀` while the loop is
  running, and `acc = diagonal m₀ n₀` once it has exited. -/
theorem diagonalWhile_eq (m n : Nat) : diagonalWhile m n = diagonal m n := by
  generalize h : diagonalWhile m n = r
  apply Id.of_wp_run_eq h
  mvcgen
  -- 1. Variant: `diagonal m n` decreases at every step
  case inv1 =>
    exact fun s => ⟨diagonal s.1 s.2.1⟩

  -- 2. Invariant: running state (`.inl`) vs exit state (`.inr`)
  case inv2 =>
    refine (fun s => match s with
      | .inl s => ⌜s.2.2 + diagonal s.1 s.2.1 = diagonal m n⌝
      | .inr s => ⌜s.2.2 = diagonal m n⌝, ())

  -- 3. Verification conditions (vc1 through vc5)

  -- Iteration with `m > 0`: `(m, n, acc) ↦ (m - 1, n + 1, acc + 1)`.
  case vc1.step.isTrue.isTrue =>
    rename_i b mb _ _ _ _ _ _ hpos hinv
    obtain ⟨M, N, A⟩ := b
    simp +zetaDelta only [SVal.evalsTo_nil, ULift.up.injEq, SPred.down_pure_nil] at hinv hpos ⊢
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    obtain ⟨hvar, hacc⟩ := hinv
    exact ⟨diagonal k (N + 1), by simp, by simp at hvar ⊢; omega, by simp at hacc ⊢; omega⟩

  -- Iteration with `m = 0` (hence `n > 0`): `(0, n, acc) ↦ (n - 1, 0, acc + 1)`.
  case vc2.step.isTrue.isFalse =>
    rename_i b mb _ _ _ _ hcond _ hpos hinv
    obtain ⟨M, N, A⟩ := b
    simp +zetaDelta only [SVal.evalsTo_nil, ULift.up.injEq, SPred.down_pure_nil, gt_iff_lt,
      Nat.not_lt, Nat.le_zero_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at hinv hpos hcond ⊢
    subst hpos
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    obtain ⟨hvar, hacc⟩ := hinv
    exact ⟨diagonal k 0, by simp, by simp at hvar ⊢; omega, by simp at hacc ⊢; omega⟩

  -- Loop exit: `m = n = 0`, so the invariant gives `acc = diagonal m₀ n₀`.
  case vc3.step.isFalse =>
    rename_i b mb _ _ _ _ hcond hinv
    obtain ⟨M, N, A⟩ := b
    simp +zetaDelta only [SVal.evalsTo_nil, ULift.up.injEq, SPred.down_pure_nil, bne_iff_ne, ne_eq,
      Bool.or_eq_true, not_or, Decidable.not_not] at hinv hcond ⊢
    obtain ⟨hM, hN⟩ := hcond
    subst hM; subst hN
    simpa using hinv.2

  -- The invariant holds initially (`acc = 0`).
  case vc4.pre =>
    simp

  -- The invariant at exit implies the postcondition.
  case vc5.post.success =>
    rename_i r2 hinv
    simpa using hinv

-- #print axioms diagonalWhile_eq
-- #print axioms diagonal_tr_zero_eq_diagonal
