-- mutual
--   def test1 (n : Nat) : Nat :=
--     if n ≤ 1 then n else test2 (n - 1)

--   def test2 (m : Nat) : Nat :=
--     if m ≤ 2 then m else test1 (m - 2)
-- end

def Valid1 (n : Int) : Prop := n ≥ 1 ∧ (n % 3 = 0 ∨ n % 3 = 1)
def Valid2 (m : Int) : Prop := m ≥ 2 ∧ (m % 3 = 0 ∨ m % 3 = 2)

theorem test1_step {n : Int} (h : Valid1 n) (hn : n ≠ 1) : Valid2 (n - 1) := by
  unfold Valid1 Valid2 at *
  omega

theorem test2_step {m : Int} (h : Valid2 m) (hm : m ≠ 2) : Valid1 (m - 2) := by
  unfold Valid1 Valid2 at *
  omega

mutual
def test1 (n : Int) (h : Valid1 n) : Int :=
  if hn : n = 1 then
    n
  else
    test2 (n - 1) (test1_step h hn)
termination_by n.toNat
decreasing_by
  simp_wf
  grind only [Valid1]

def test2 (m : Int) (h : Valid2 m) : Int :=
  if hm : m = 2 then
    m
  else
    test1 (m - 2) (test2_step h hm)
termination_by m.toNat
decreasing_by
  simp_wf
  grind only [Valid2, = Int.max_def]
end

example : test1 7 (by grind only [Valid1]) = 1 := by
  grind only [test1, test2]
