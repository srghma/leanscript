/-! Calls of a function parameter on literal and computed arguments, each used once.

* Literal arguments are passed as they are, not bound to constants first
  (`op(true, false)`, not `const x = true; … op(x, …)`).
* Every call read once, in the order the calls are made, is written at its use, however many
  there are (`chain6`, `chainVars`).
* Calls read in another order than the one they are made in stay named, so that they are still
  made in that order (`swapped`). -/

@[inline] def boolValues (op : Bool → Bool → Bool) : Array Bool :=
  #[ op true true, op true false, op false true, op false false ]

def chain6 (op : Nat → Nat → Nat) : Array Nat :=
  #[ op 1 2, op 3 4, op 5 6, op 7 8, op 9 10, op 11 12 ]

def chainVars (op : Nat → Nat → Nat) (a b : Nat) : Array Nat :=
  #[ op a b, op b a, op a a, op b b, op (a + 1) b, op 11 12, op b 0, op 0 a ]

def chainStr (f : String → Nat) (g : Nat → String) : Array Nat :=
  #[ f "a", f (g 1), f "b", f (g 2), f "c" ]

def swapped (op : Nat → Nat → Nat) : Array Nat :=
  let x := op 1 2
  let y := op 3 4
  let z := op 5 6
  #[ z, y, x ]
