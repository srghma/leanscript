-- The Ackermann function: the standard example of a function that is terminating,
-- but not by any single `Nat`-valued argument going down.  It terminates on the
-- *lexicographic* order of the pair `(m, n)`: the outer argument `m` decreases in
-- the two `ack m …` calls, and when `m` stays the same (`ack (m + 1) n`) the inner
-- argument `n` decreases.  There is no primitive-recursive bound on the number of
-- iterations, and one of the recursive calls is *nested* — its argument is itself a
-- recursive call.

def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def ack999 := ack 999 1
