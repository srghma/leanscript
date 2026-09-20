mutual
def go (n : Nat) : Nat :=
  if h1 : n = 0 then n
  else if h2 : n ≤ 100 then go (n - 1)
  else k (n - 1) (by omega)
termination_by n
decreasing_by all_goals omega

def k (m : Nat) (h : m ≥ 100) : Nat :=
  if h1 : m = 100 then go (m - 1)
  else if h2 : m = 900 then 42
  else k (m - 1) (by omega)
termination_by m
decreasing_by all_goals omega
end
