/-!
Mutually tail-recursive functions: each of these calls the next in tail position, so
none of them may grow the JavaScript stack. The group is compiled into a single
function with a dispatch loop (`_mut$…`), and each member keeps a declaration of its
own that enters it with the member's tag.

`test1`/`test2` are a two-member group of one argument each; `test3`/`test4`/`test5`
are a three-member group of *different* arities, so the merged function takes as many
arguments as the widest member.
-/

mutual

def test1 : Nat → Bool
  | 0 => true
  | n + 1 => test2 n

def test2 : Nat → Bool
  | 0 => false
  | n + 1 => test1 n

end

mutual

def test3 (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test4 n (acc + 1) 2

def test4 (n acc k : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test5 n (acc + k)

def test5 (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | n + 1 => test3 n (acc + 3)

end
