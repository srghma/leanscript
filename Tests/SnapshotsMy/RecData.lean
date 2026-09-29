import LeanScript.Term.Elab

/-! Recursive datatypes declared by the user (`leanscript_signature`): literals, constructors,
case analyses and structural recursion (folds, `data_rec`), with checked wrappers over arrays. -/
namespace RecData

inductive MyList where
  | nil
  | cons (h : Nat) (t : MyList)

inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

/-- A rose tree: recursion through an array (its fold is tested in `Tests/Main.lean`: the
    structural recursion over it does not reach this tool). -/
inductive Rose where
  | node (kids : Array Rose)

/-- A rose tree whose children are a function on `Fin m`. -/
inductive RoseF where
  | node : (m : Nat) → (Fin m → RoseF) → RoseF

leanscript_signature Prog where
  myList := MyList
  tree := Tree
  rose := Rose
  roseF := RoseF

def two : MyList := .cons 1 (.cons 2 .nil)

def push (x : Nat) (l : MyList) : MyList := .cons x l

def head (l : MyList) : Nat :=
  match l with
  | .nil => 0
  | .cons h _ => h

def sum : MyList → Nat
  | .nil => 0
  | .cons h t => h + sum t

def ofArray (xs : Array Nat) : MyList := xs.foldl (fun l x => .cons x l) .nil

def toArray : MyList → Array Nat
  | .nil => #[]
  | .cons h t => (toArray t).push h

def size : Tree → Nat
  | .leaf => 0
  | .node l _ r => size l + 1 + size r

def insert (x : Nat) : Tree → Tree
  | .leaf => .node .leaf x .leaf
  | .node l v r => if x < v then .node (insert x l) v r else .node l v (insert x r)

def inorder : Tree → Array Nat
  | .leaf => #[]
  | .node l v r => (inorder l).push v ++ inorder r

def ofArrayT (xs : Array Nat) : Tree := xs.foldl (fun t x => insert x t) .leaf

def sumTwo : Nat := sum two

def sumArray (xs : Array Nat) : Nat := sum (ofArray xs)

def reverse (xs : Array Nat) : Array Nat := toArray (ofArray xs)

def sort (xs : Array Nat) : Array Nat := inorder (ofArrayT xs)

def sizeArray (xs : Array Nat) : Nat := size (ofArrayT xs)

def roseOf (x : Nat) : Rose :=
  .node (if x > 2 then #[.node #[], .node #[.node #[]]] else #[.node #[.node #[], .node #[]]])

/-- The number of children of the root: a case analysis, no recursion. -/
def roseKids : Rose → Nat
  | .node kids => kids.size

def roseKidsTest (x : Nat) : Nat := roseKids (roseOf x)

/-- Children as a function on `Fin m`: the fold maps a function field. -/
def RoseF.size : RoseF → Nat
  | .node m f => Fin.foldl m (fun acc i => acc + (f i).size) 1

def roseFOf (n : Nat) : RoseF := .node n (fun _ => .node 2 (fun _ => .node 0 Fin.elim0))

def roseFTest (n : Nat) : Nat := (roseFOf n).size

end RecData
