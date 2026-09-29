import LeanScript.Term.Elab

/-!
Programs where updating an array in place would be wrong: the array is still used afterwards,
or shared between two calls. Their node checks compare every answer with Lean's, so an update
in place that another part of the program can observe makes them fail
(`LeanScript.Term.Ownership`).
-/

/-- The argument of the local function is used again afterwards: the call copies it. -/
def alias1 (n : Nat) : Array Nat :=
  let a := Array.replicate n 1
  let f := fun (b : Array Nat) (k : Nat) => b.push k
  f a n ++ a

/-- A partial application holding an array is called twice: neither call may update it. -/
def alias2 (n : Nat) : Array Nat :=
  let f := fun (b : Array Nat) (k : Nat) => (b.push k).push n
  let g := f (Array.replicate n 0)
  g 1 ++ g 2

private def fill : Nat → Array Nat → Array Nat
  | 0, a => a
  | n + 1, a => fill n (a.push n)

/-- The owning closure a recursion answers is given the same array twice: it is copied for
    each call. -/
def alias3 (n : Nat) : Array Nat :=
  let g := fill n
  let b := Array.replicate n 3
  g b ++ g b ++ b

/-- The owning closure is called inside another closure, itself called twice, and on an array
    used afterwards. -/
def alias4 (n : Nat) : Array Nat :=
  let g := fill n
  let h := fun (k : Nat) => g (Array.replicate k 5)
  let b := Array.replicate n 3
  h 1 ++ h 2 ++ g b ++ b

/-- The same array reaches both arms of a conditional and is used after it. -/
def alias5 (a : Array Nat) (c : Bool) : Array Nat :=
  let b := a.push 1
  (if c then b.push 2 else b.push 3) ++ b

/-- The answer of a local function that returns its (borrowed) argument is not owned. -/
def alias6 (a : Array Nat) (n : Nat) : Array Nat :=
  let b := Array.replicate n 4
  let id' := fun (x : Array Nat) (k : Nat) => if k = 0 then x else x.push k
  let c := id' b n
  c.push 9 ++ b ++ a

/-- A list of arrays: a fold over it may update its own answers at the tails in place, never
    the arrays the list holds. -/
inductive Bag where
  | nil
  | cons (items : Array Nat) (rest : Bag)

leanscript_signature BagSig where
  bag := Bag

/-- A bag of arrays: for each `x` of `xs`, `x` copies of `x`, and `xs` itself. -/
def Bag.ofArray (xs : Array Nat) : Bag :=
  xs.foldl (fun b x => .cons (Array.replicate x x) b) (.cons xs .nil)

/-- The answer at the tail is updated in place; the arrays of the bag are only read. -/
def Bag.collect : Bag → Array Nat
  | .nil => #[]
  | .cons items rest => (Bag.collect rest).push items.size ++ items

/-- An array of the bag is answered updated: it is copied. -/
def Bag.firstItems : Bag → Array Nat
  | .nil => #[]
  | .cons items rest =>
    if items.size > 2 then items.push (Bag.firstItems rest).size else Bag.firstItems rest

/-- The answer at the tail is used twice. -/
def Bag.twice : Bag → Array Nat
  | .nil => #[1]
  | .cons items rest =>
    let r := Bag.twice rest
    r.push items.size ++ r

def bag1 (xs : Array Nat) : Array Nat :=
  let b := Bag.ofArray xs
  Bag.collect b ++ Bag.collect b ++ xs

def bag2 (xs : Array Nat) : Array Nat :=
  let b := Bag.ofArray xs
  Bag.firstItems b ++ Bag.collect b ++ xs

def bag3 (xs : Array Nat) : Array Nat :=
  let b := Bag.ofArray (xs.extract 0 4)
  Bag.twice b ++ Bag.collect b
