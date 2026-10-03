/-! Results of recursive datatypes compared with Lean by the checks (`--check`): a list and a
binary tree of the source, inside a structure of one field (unboxed) and a structure of two, a
lazy parameter answering one, and a value deeper than the depth the checks print
(`treeShowDepth`, cut on both sides). -/

inductive MyList (α : Type) where
  | Cons : α → MyList α → MyList α
  | Nil  : MyList α

def MyList.app : MyList Int → MyList Int → MyList Int
  | .Cons x xs, ys => .Cons x (MyList.app xs ys)
  | .Nil, ys => ys

def countdown : Nat → MyList Int
  | 0 => .Nil
  | n + 1 => .Cons n (countdown n)

def long : MyList Int := countdown 40

inductive Tree where
  | leaf : Tree
  | node : Tree → Int → Tree → Tree

def Tree.mirror : Tree → Tree
  | .leaf => .leaf
  | .node l x r => .node r.mirror x l.mirror

def Tree.insert (t : Tree) (y : Int) : Tree :=
  match t with
  | .leaf => .node .leaf y .leaf
  | .node l x r => if y < x then .node (l.insert y) x r else .node l x (r.insert y)

structure Wrapped where
  t : Tree

def wrapMirror (w : Wrapped) : Wrapped := ⟨w.t.mirror⟩

structure Both where
  l : MyList Int
  t : Tree

def both (n : Nat) (y : Int) : Both := ⟨countdown n, Tree.leaf.insert y⟩

def consForced (f : Unit → MyList Int) : MyList Int := .Cons 7 (f ())
