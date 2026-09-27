-- @js_export: Color, RedBlackTree, test1
inductive Color where
  | Red
  | Black

inductive RedBlackTree (α : Type) where
  | Leaf
  | Node
    (color : Color)
    (l : RedBlackTree α)
    (val : α)
    (r : RedBlackTree α)

structure Result where
  i : Nat
  a : RedBlackTree Nat
  x : Nat
  b : RedBlackTree Nat
  y : Nat
  c : RedBlackTree Nat
  z : Nat
  d : RedBlackTree Nat

instance : Inhabited Result where
  default := { i := 0, a := .Leaf, x := 0, b := .Leaf, y := 0, c := .Leaf, z := 0, d := .Leaf }

def test1 (t : RedBlackTree Nat) : Result :=
  match t with
  | .Node .Black (.Node .Red (.Node .Red a x b) y c) z d => { i := 1, a, x, b, y, c, z, d }
  | .Node .Black (.Node .Red a x (.Node .Red b y c)) z d => { i := 2, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red (.Node .Red b y c) z d) => { i := 3, a, x, b, y, c, z, d }
  | .Node .Black a x (.Node .Red b y (.Node .Red c z d)) => { i := 4, a, x, b, y, c, z, d }
  | _ => panic! "unmatched"
