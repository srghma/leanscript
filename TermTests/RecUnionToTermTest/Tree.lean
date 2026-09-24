module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k` on a binary tree (two recursive points)

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked.

`Tree` is the recursive tagged union `leaf | node self nat self`.  A branch of
`recTaggedUnion_rec k` is given a node's subtrees, its label, and the answers at both
subtrees; a deeper look goes into **one** subtree — the programs at `k ≥ 1` below read
`k + 1` levels down the left spine (`.here`) or the right spine (`.there (.there .here)`),
while still using the answers at the other subtrees. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-- A binary tree with a label at each node. -/
inductive Tree where
  | leaf
  | node (left : Tree) (val : Nat) (right : Tree)
  deriving LeanScriptTyWf

/-- The type of a tree, in the language. -/
abbrev treeT : TyWf := tyWfOf Tree

-- The derived tree is a recursive tagged union with two occurrences of itself.
example :
    tyOf Tree = .recTaggedUnion (.skip (.here ⟨.self, [.prim .nat, .self]⟩ [])) := rfl

namespace Tree

/-- The complete tree of height `n`, the root labelled `n`. -/
def full : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (full n) (n + 1) (full n)

/-- A left spine of `n` nodes labelled `n, …, 1`, each with a leaf on the right. -/
def leftSpine : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (leftSpine n) (n + 1) .leaf

/-- A right spine of `n` nodes labelled `n, …, 1`, each with a one-node tree on the left
    labelled like it. -/
def rightSpine : Nat → Tree
  | 0 => .leaf
  | n + 1 => .node (.node .leaf (n + 1) .leaf) (n + 1) (rightSpine n)

end Tree

/-- `Tree.full`, as a term: a `nat_rec` whose branch builds a node with
    `recTaggedUnion_mk`. -/
def full_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.full

/-- `Tree.leftSpine`, as a term. -/
def leftSpine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.leftSpine

/-- `Tree.rightSpine`, as a term. -/
def rightSpine_term : Term sigAdd [] (natT ⇒ treeT) := #leanscript_to_term Tree.rightSpine

/-- A tree written out. -/
def tree7 : Tree :=
  .node (.node (.node .leaf 4 .leaf) 2 (.node .leaf 5 .leaf)) 1
    (.node (.node .leaf 6 .leaf) 3 (.node (.node .leaf 8 .leaf) 7 .leaf))

/-- `tree7`, as a term: nested `recTaggedUnion_mk`s. -/
def tree7_term : Term sigAdd [] treeT := #leanscript_to_term tree7

/-! ## `k = 0`: the sum of the labels, the number of leaves, and an accumulator loop -/

def treeSum_with_k0 : Tree → Nat
  | .leaf => 0
  | .node l v r => treeSum_with_k0 l + v + treeSum_with_k0 r

def treeSum_with_k0_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeSum_with_k0

example : recUnionRecDepth? treeSum_with_k0_term = some 0 := by kernel_rfl
example : runAdd treeSum_with_k0_term (runAdd tree7_term) = 36 := by kernel_rfl
example : runAdd treeSum_with_k0_term (runAdd full_term 3) = 11 := by kernel_rfl
example : runAdd treeSum_with_k0_term (runAdd full_term 5) =
    treeSum_with_k0 (Tree.full 5) := by kernel_rfl

def treeLeaves_with_k0 : Tree → Nat
  | .leaf => 1
  | .node l _ r => treeLeaves_with_k0 l + treeLeaves_with_k0 r

def treeLeaves_with_k0_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term treeLeaves_with_k0

example : recUnionRecDepth? treeLeaves_with_k0_term = some 0 := by kernel_rfl
example : runAdd treeLeaves_with_k0_term (runAdd full_term 4) = 16 := by kernel_rfl
example : runAdd treeLeaves_with_k0_term (runAdd tree7_term) = treeLeaves_with_k0 tree7 := by
  kernel_rfl

/-- The labels in order, summed from the left with an accumulator: the fold returns a
    function. -/
def treeSumAcc_with_k0 : Tree → Nat → Nat
  | .leaf, acc => acc
  | .node l v r, acc => treeSumAcc_with_k0 r (treeSumAcc_with_k0 l acc + v)

def treeSumAcc_with_k0_term : Term sigAdd [] (treeT ⇒ natT ⇒ natT) :=
  #leanscript_to_term treeSumAcc_with_k0

example : recUnionRecDepth? treeSumAcc_with_k0_term = some 0 := by kernel_rfl
example : runAdd treeSumAcc_with_k0_term (runAdd tree7_term) 100 = 136 := by kernel_rfl
example : runAdd treeSumAcc_with_k0_term (runAdd full_term 4) 3 =
    treeSumAcc_with_k0 (Tree.full 4) 3 := by kernel_rfl

/-! ## `k = 1`: `fib` down the left spine, and down the right spine -/

/-- `fib` of the length of the left spine. -/
def leftFib_with_k1 : Tree → Nat
  | .leaf => 0
  | .node .leaf _ _ => 1
  | .node (.node ll v lr) _ _ => leftFib_with_k1 ll + leftFib_with_k1 (.node ll v lr)

def leftFib_with_k1_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftFib_with_k1

example : recUnionRecDepth? leftFib_with_k1_term = some 1 := by kernel_rfl
example : runAdd leftFib_with_k1_term (runAdd leftSpine_term 1) = 1 := by kernel_rfl
example : runAdd leftFib_with_k1_term (runAdd leftSpine_term 10) = 55 := by kernel_rfl
example : runAdd leftFib_with_k1_term (runAdd full_term 6) = leftFib_with_k1 (Tree.full 6) := by
  kernel_rfl
example : runAdd leftFib_with_k1_term (runAdd tree7_term) = leftFib_with_k1 tree7 := by
  kernel_rfl

/-- Down the right spine: the label of each node times the label of its right child, plus
    the answers at the left subtree and at the right child.  The deeper look goes into the
    *second* occurrence of the tree. -/
def rightProducts_with_k1 : Tree → Nat
  | .leaf => 0
  | .node l _ .leaf => rightProducts_with_k1 l
  | .node l v (.node rl w rr) =>
      v * w + rightProducts_with_k1 l + rightProducts_with_k1 (.node rl w rr)

def rightProducts_with_k1_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term rightProducts_with_k1

example : recUnionRecDepth? rightProducts_with_k1_term = some 1 := by kernel_rfl
example : runAdd rightProducts_with_k1_term (runAdd tree7_term) = 34 := by kernel_rfl
example : runAdd rightProducts_with_k1_term (runAdd rightSpine_term 4) = 20 := by kernel_rfl
example : runAdd rightProducts_with_k1_term (runAdd full_term 5) =
    rightProducts_with_k1 (Tree.full 5) := by kernel_rfl

/-! ## `k = 2`: the tribonacci numbers down the left spine, plus the right subtrees -/

def leftTrib_with_k2 : Tree → Nat
  | .leaf => 0
  | .node .leaf _ r => leftTrib_with_k2 r
  | .node (.node .leaf _ _) _ r => 1 + leftTrib_with_k2 r
  | .node (.node (.node a x b) y c) _ r =>
      leftTrib_with_k2 a + leftTrib_with_k2 (.node a x b) +
        leftTrib_with_k2 (.node (.node a x b) y c) + leftTrib_with_k2 r

def leftTrib_with_k2_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftTrib_with_k2

example : recUnionRecDepth? leftTrib_with_k2_term = some 2 := by kernel_rfl
example : runAdd leftTrib_with_k2_term (runAdd leftSpine_term 10) = 81 := by kernel_rfl
example : runAdd leftTrib_with_k2_term (runAdd tree7_term) = leftTrib_with_k2 tree7 := by
  kernel_rfl
example : runAdd leftTrib_with_k2_term (runAdd full_term 6) =
    leftTrib_with_k2 (Tree.full 6) := by kernel_rfl

/-! ## `k = 3`: the tetranacci numbers down the right spine -/

def rightTetra_with_k3 : Tree → Nat
  | .leaf => 0
  | .node _ _ .leaf => 0
  | .node _ _ (.node _ _ .leaf) => 0
  | .node _ _ (.node _ _ (.node _ _ .leaf)) => 1
  | .node _ _ (.node l1 v1 (.node l2 v2 (.node a x b))) =>
      rightTetra_with_k3 b + rightTetra_with_k3 (.node a x b) +
        rightTetra_with_k3 (.node l2 v2 (.node a x b)) +
        rightTetra_with_k3 (.node l1 v1 (.node l2 v2 (.node a x b)))

def rightTetra_with_k3_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term rightTetra_with_k3

example : recUnionRecDepth? rightTetra_with_k3_term = some 3 := by kernel_rfl
example : runAdd rightTetra_with_k3_term (runAdd rightSpine_term 4) = 1 := by kernel_rfl
example : runAdd rightTetra_with_k3_term (runAdd rightSpine_term 10) =
    rightTetra_with_k3 (Tree.rightSpine 10) := by kernel_rfl
example : runAdd rightTetra_with_k3_term (runAdd full_term 7) =
    rightTetra_with_k3 (Tree.full 7) := by kernel_rfl

/-! ## `k = 4`: the pentanacci numbers down the left spine, reading the labels -/

def leftPenta_with_k4 : Tree → Nat
  | .leaf => 0
  | .node .leaf v _ => v
  | .node (.node .leaf _ _) _ _ => 0
  | .node (.node (.node .leaf _ _) _ _) _ _ => 0
  | .node (.node (.node (.node .leaf _ _) _ _) _ _) _ _ => 1
  | .node (.node (.node (.node (.node a x b) y c) z d) w e) _ _ =>
      leftPenta_with_k4 a + leftPenta_with_k4 (.node a x b) +
        leftPenta_with_k4 (.node (.node a x b) y c) +
        leftPenta_with_k4 (.node (.node (.node a x b) y c) z d) +
        leftPenta_with_k4 (.node (.node (.node (.node a x b) y c) z d) w e)

def leftPenta_with_k4_term : Term sigAdd [] (treeT ⇒ natT) :=
  #leanscript_to_term leftPenta_with_k4

example : recUnionRecDepth? leftPenta_with_k4_term = some 4 := by kernel_rfl
example : runAdd leftPenta_with_k4_term (runAdd leftSpine_term 1) = 1 := by kernel_rfl
example : runAdd leftPenta_with_k4_term (runAdd leftSpine_term 12) =
    leftPenta_with_k4 (Tree.leftSpine 12) := by kernel_rfl
example : runAdd leftPenta_with_k4_term (runAdd full_term 7) =
    leftPenta_with_k4 (Tree.full 7) := by kernel_rfl

/-! ## Refused: a look into both subtrees at once

The sum of the labels at even levels reads the answers at the grandchildren below **both**
children.  A deeper look of `recTaggedUnion_rec k` goes into one subvalue, and inside it
the other child's subtrees are out of reach, so this program is not a fold of this kind at
any depth, and the translation refuses it. -/

def evenLevelSum : Tree → Nat
  | .leaf => 0
  | .node .leaf v .leaf => v
  | .node .leaf v (.node rl _ rr) => v + evenLevelSum rl + evenLevelSum rr
  | .node (.node ll _ lr) v .leaf => v + evenLevelSum ll + evenLevelSum lr
  | .node (.node ll _ lr) v (.node rl _ rr) =>
      v + evenLevelSum ll + evenLevelSum lr + evenLevelSum rl + evenLevelSum rr

example : Term sigAdd [] (treeT ⇒ natT) := by
  fail_if_success exact #leanscript_to_term evenLevelSum
  exact treeSum_with_k0_term

end TermTests.RecUnionToTerm

end
