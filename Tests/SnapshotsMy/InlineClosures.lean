/-!
Calls the backend inlines once the functions are translated (`JsTerm.Passes.InlineConsts`,
`JsTerm.Passes.Cleanup`):

* the closures of the module that only compute an expression are inlined where they are
  called (the base case of a loop, a helper Lean inlined only partly), and a closure passed to
  one of them that is only called is inlined into its calls;
* a closure whose body is a block, called once in tail position, is that block (a loop that
  builds an array then updates it in place);
* a record built for a call and only taken apart there is not built;
* `if x != c then x else c` is `x`;
* a chain of list appends is one literal.
-/

/-- The loop's base case (`a + b` for `fuel = 0`) is inlined after the loop. -/
def addAfter (fuel a b : Nat) : Nat :=
  match fuel with
  | 0 => a + b
  | fuel + 1 => addAfter fuel (a + 2) (b + 3)

/-- A helper that calls its argument three times, handed a closure: the closure is inlined
    into each call. -/
@[noinline] private def sum3 (f : Nat → Nat) : Nat := f 1 + f 2 + f 3

def sumShifted (k : Nat) : Nat := sum3 (fun x => x * k)

/-- A helper that builds an array in a loop, called once: the loop is inlined, and the array
    is then pushed to in place. -/
@[noinline] private def countDown (n : Nat) (acc : Array Nat) : Array Nat :=
  match n with
  | 0 => acc
  | n + 1 => countDown n (acc.push n)

def downFrom (n : Nat) : Array Nat := countDown n #[]

/-- A helper taking a pair apart, called once with a pair built for the call. -/
@[noinline] private def order (p : Nat × Nat) : Nat × Nat :=
  if p.1 ≤ p.2 then p else (p.2, p.1)

def ordered (a b : Nat) : Nat × Nat := order (a, b)

/-- Both branches give `x`. -/
def keep (x : Int) : Int := if x != 7 then x else 7

/-- Appends of list literals and a list. -/
def around (xs : List String) : List String := ["<"] ++ (xs ++ ([","] ++ (xs ++ [">"])))
