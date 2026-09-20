import Aesop

-- 1. Original recursive definition
def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

-- Base value for each operation level at b = 0
def hyperBase : Nat → Nat → Nat
  | 0,     _ => 1
  | 1,     a => a
  | 2,     _ => 0
  | _ + 3, _ => 1

-- 2. Tail-recursive loop helper: applies `f` to `acc`, `b` times.
-- Automatically verified terminating structurally on `b`.
def hyperLoop (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     acc => acc
  | b + 1, acc => hyperLoop f b (f acc)

-- 2. Staged TCO evaluator: structurally recursive on `n`.
def hyperTCO : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a)

-- 3. Imperative evaluator using a stateful loop over level n
def hyperWhile : Nat → Nat → Nat → Nat
  | 0,     _, b => b + 1
  | n + 1, a, b => Id.run do
    let mut acc := hyperBase (n + 1) a
    for _ in [0:b] do
      acc := hyperWhile n a acc
    return acc

-------------------------------------------------------------------------------
-- Verification / Proofs
-------------------------------------------------------------------------------

-- Key property of `hyperLoop`: pulling `f` outside the loop
theorem hyperLoop_step (f : Nat → Nat) (b acc : Nat) :
    hyperLoop f (b + 1) acc = f (hyperLoop f b acc) := by
  induction b generalizing acc with
  | zero => rfl
  | succ b ih => exact ih (f acc)

-- Base values match at b = 0
theorem hyperBase_eq (n a : Nat) : hyperBase (n + 1) a = hyper (n + 1) a 0 := by
  cases n with
  | zero => simp [hyperBase, hyper]
  | succ n =>
    cases n with
    | zero => simp [hyperBase, hyper]
    | succ n => simp [hyperBase, hyper]

-- Main equivalence theorem: hyperTCO n a b = hyper n a b
theorem hyperTCO_eq : ∀ n a b, hyperTCO n a b = hyper n a b := by
  intro n
  induction n with
  | zero =>
    intro a b
    simp [hyperTCO, hyper]
  | succ n ih =>
    intro a b
    have hfun : hyperTCO n a = hyper n a := funext fun x => ih a x
    have hbase : hyperBase (n + 1) a = hyper (n + 1) a 0 := hyperBase_eq n a
    have hloop : ∀ b, hyperLoop (hyper n a) b (hyper (n + 1) a 0) = hyper (n + 1) a b := by
      intro b
      induction b with
      | zero => rfl
      | succ b ihb =>
        rw [hyperLoop_step, ihb]
        simp [hyper]
    show hyperLoop (hyperTCO n a) b (hyperBase (n + 1) a) = hyper (n + 1) a b
    rw [hfun, hbase, hloop]

-------------------------------------------------------------------------------
-- Sanity Checks
-------------------------------------------------------------------------------

-- #eval hyper 3 2 4      -- 2^4 = 16
-- #eval hyperTCO 3 2 4   -- 16
-- #eval hyperWhile 3 2 4 -- 16
