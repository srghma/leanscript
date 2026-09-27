module

public import LeanScript.Term.Eval
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TermElab.Notation

/-!
# The examples of proposal B (companion of `proposals/NormalFormProposals.md`, §B)

Not part of the Lake build; check with

```
lake env lean proposals/NormalFormBExamples.lean
```

Each example is a Lean definition translated by `#leanscript_to_term` with **today's**
grammar and normaliser.  The `#print` shows the output that the document quotes as "before".
The "after" forms in the document are derived by hand, because proposal B is not implemented.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NFBEx
open LeanScript

/-! ## 1. Lets used 0, 1 and 2 times -/

def lets (n : Nat) : Nat :=
  let dead := n * 7      -- used 0 times
  let once := n * 2      -- used 1 time
  let twice := n + 1     -- used 2 times
  once + twice * twice

def letsT := #leanscript_to_term lets
#print letsT

/-- The same with computations (calls of an unknown function) instead of extern calls. -/
def letsApp (f : Nat → Nat) (n : Nat) : Nat :=
  let dead := f n
  let once := f (n + 1)
  let twice := f (n + 2)
  once + twice * twice

def letsAppT := #leanscript_to_term letsApp
#print letsAppT

/-- Lets of closed values (known at elaboration time). -/
def letsClosed (n : Nat) : Nat :=
  let dead := 3 + 4
  let once := 10 * 10
  let twice := 2 + 3
  n + once + twice * twice

def letsClosedT := #leanscript_to_term letsClosed
#print letsClosedT

/-! ## 2. Closed arithmetic -/

def seven : Nat := 3 + 4
def sevenT := #leanscript_to_term seven
#print sevenT

/-! ## 3. Ackermann, in the structural (higher-order) form -/

def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)

def ack : Nat → Nat → Nat
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack m)

def ackT := #leanscript_to_term ack
#print ackT

/-- A closed call of `ack`. -/
def ack23 : Nat := ack 2 3
def ack23T := #leanscript_to_term ack23
#print ack23T

/-! ## 4. A recursive function that changes a record every iteration -/

structure St where
  a : Nat
  b : Nat
  steps : Nat

def fibLoop : Nat → St → St
  | 0,     s => s
  | n + 1, s => fibLoop n { a := s.b, b := s.a + s.b, steps := s.steps + 1 }

def fibLoopT := #leanscript_to_term fibLoop
#print fibLoopT

/-- The same loop, taking the state apart once with a pattern. -/
def fibLoopM : Nat → St → St
  | 0,     s => s
  | n + 1, ⟨a, b, k⟩ => fibLoopM n ⟨b, a + b, k + 1⟩

def fibLoopMT := #leanscript_to_term fibLoopM
#print fibLoopMT

/-- A caller that starts from a record literal (a known value). -/
def fib (n : Nat) : Nat := (fibLoop n { a := 0, b := 1, steps := 0 }).a
def fibT := #leanscript_to_term fib
#print fibT

def fib10 : Nat := fib 10
def fib10T := #leanscript_to_term fib10
#print fib10T

/-! ## 4b. A record value used twice, and a closed condition -/

structure P2 where
  a : Nat
  b : Nat

def pairTwice (n : Nat) : P2 × P2 :=
  let p := { a := n, b := n + 1 }
  (p, p)

def pairTwiceT := #leanscript_to_term pairTwice
#print pairTwiceT

def closedCond (n : Nat) : Nat := if 1 < 2 then n else 0
def closedCondT := #leanscript_to_term closedCond
#print closedCondT

/-! ## 5. A closure used twice: called, and passed on -/

def callTwice (n : Nat) : Nat :=
  let f := fun x => x * n + 1
  f (f n)

def callTwiceT := #leanscript_to_term callTwice
#print callTwiceT

def passTwice (g : (Nat → Nat) → Nat) (n : Nat) : Nat :=
  let f := fun x => x + n
  g f + g f

def passTwiceT := #leanscript_to_term passTwice
#print passTwiceT

/-! ## 6. A memoised delay forced twice -/

def thunkTwice (n : Nat) : Nat :=
  let t := Thunk.mk (fun _ => n * n)
  t.get + t.get

def thunkTwiceT := #leanscript_to_term thunkTwice
#print thunkTwiceT

end NFBEx

end
