import Aesop

-- ============================================================================
-- 1. Reference Specification
-- ============================================================================

def mc91 (n : Nat) : Nat :=
  if n > 100 then
    n - 10
  else
    91

-- Closed-form characterization of McCarthy 91
theorem mc91_spec (n : Nat) : mc91 n = if n > 100 then n - 10 else 91 := by
  rfl

-- ============================================================================
-- 2. Tail-Recursive Implementation
-- ============================================================================

-- Tail-recursive loop helper:
-- `c` is the number of pending calls to evaluate.
-- When c = 0, all calls have completed.
def mc91Loop : Nat → Nat → Nat
  | 0,     n => n
  | c + 1, n =>
    if h : n > 100 then
      mc91Loop c (n - 10)
    else
      mc91Loop (c + 1 + 1) (n + 11)
termination_by c n => 2 * (111 - n) + 21 * c
decreasing_by
  all_goals omega

-- Tail-recursive entry point (starts with 1 pending call)
def mc91TR (n : Nat) : Nat :=
  mc91Loop 1 n

-- ============================================================================
-- 3. While-loop / Imperative Implementation
-- ============================================================================

def mc91While (n : Nat) : Nat := Id.run do
  let mut c : Nat := 1
  let mut cur : Nat := n

  while c != 0 do
    if cur > 100 then
      cur := cur - 10
      c := c - 1
    else
      cur := cur + 11
      c := c + 1

  return cur

-- ============================================================================
-- 4. Equivalence Proof: mc91TR n = mc91 n
-- ============================================================================

-- Simple function iteration helper without Mathlib
def iter (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | c + 1, x => iter f c (f x)

-- Step 1: Characterize single step when n > 100
theorem mc91_step_gt {n : Nat} (h : n > 100) : mc91 n = n - 10 := by
  unfold mc91
  split
  · rfl
  · omega

-- Step 2: Characterize nested double-step when n ≤ 100
-- `repeat (first | split | omega)` safely splits ifs and closes arithmetic leaves
theorem mc91_step_le {n : Nat} (h : n ≤ 100) : mc91 (mc91 (n + 11)) = mc91 n := by
  unfold mc91
  repeat (first | split | omega)

-- Step 3: Loop invariant for arbitrary pending call count `c`
theorem mc91Loop_eq (c n : Nat) : mc91Loop c n = iter mc91 c n := by
  induction c, n using mc91Loop.induct with
  | case1 n =>
    grind => instantiate only [mc91Loop, iter]
  | case2 c n hgt ih =>
    unfold mc91Loop
    split
    · rw [ih, ← mc91_step_gt hgt]
      rfl
    · omega
  | case3 c n hle ih =>
    unfold mc91Loop
    split
    · omega
    · rw [ih]
      dsimp [iter]
      simp_all only [gt_iff_lt, not_false_eq_true, Nat.not_lt]
      grind [= iter, = mc91]

-- Main Theorem: mc91TR n = mc91 n
theorem mc91TR_eq_mc91 (n : Nat) : mc91TR n = mc91 n := by
  unfold mc91TR
  rw [mc91Loop_eq 1 n]
  rfl

-- ============================================================================
-- Sanity Checks
-- ============================================================================

-- #eval mc91TR 99     -- 91
-- #eval mc91While 99  -- 91
-- #eval mc91TR 105    -- 95
-- #eval mc91While 105 -- 95
