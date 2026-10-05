/-! Comparisons of an `Ordering` with a constructor (the neighbours of
`Tests/SnapshotsPBOPure/PrimOpBooleanNotRegression.lean`, `comp a b != Ordering.eq`).

* A comparator passed as an argument: `comp(a, b) !== 0` (`Ordering` numbers from `-1`).
* `compare` on `Nat` and `Int`, inlined to `if a < b then .lt else if a = b then .eq else .gt`:
  the case analysis of that conditional is made on its conditions (`Branch.enumCaseCond`, in the
  `Term` optimiser), and the comparison of its position with a literal is pushed into its arms
  (`Neu.condFoldDeep?`), so no `Ordering` is built: `a < b`.
* A case analysis whose arms answer Boolean literals, one differently from the others:
  one comparison, `comp(a, b) !== 1` (in the conversion).
* `!=` of an enum (`BEq` derived, `Nat.decEq` of `toCtorIdx`): `a !== b`. -/

inductive Shade where
  | light
  | medium
  | dark
  deriving BEq

def cmpNe {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := comp a b != Ordering.eq
def cmpEqLt {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := comp a b == Ordering.lt
def cmpNeGt {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := comp a b != Ordering.gt
def cmpNotEq {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := !(comp a b == Ordering.eq)
def cmpDecide {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := decide (comp a b ≠ Ordering.eq)
def cmpIsLE {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := (comp a b).isLE
def cmpIsGE {α : Type} (comp : α → α → Ordering) (a b : α) : Bool := (comp a b).isGE
def cmpBoth {α : Type} (comp : α → α → Ordering) (a b : α) : Bool :=
  comp a b != Ordering.eq && comp b a != Ordering.eq

def natLt (a b : Nat) : Bool := compare a b == Ordering.lt
def natGt (a b : Nat) : Bool := compare a b == Ordering.gt
def natNe (a b : Nat) : Bool := compare a b != Ordering.eq
def natIsLE (a b : Nat) : Bool := (compare a b).isLE
def intLt (a b : Int) : Bool := compare a b == Ordering.lt
def intNe (a b : Int) : Bool := compare a b != Ordering.eq

def natCompare (a b : Nat) : Ordering := compare a b

def shadeNe (a b : Shade) : Bool := a != b
def shadeEq (a b : Shade) : Bool := a == b
