module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k` on a ternary tree (three recursive points)

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked.

`Tree3` is the recursive tagged union `leaf nat | node self self self` — its first
constructor carries a field, so its schema starts with `payloadFirst`, unlike `List` and
`Tree`.  A branch of `recTaggedUnion_rec k` is given a node's three subtrees and the
answers at all three; a deeper look goes into **one** of them — the programs at `k ≥ 1`
below descend the first child (`.here`), the middle child (`.there .here`) or the last
child (`.there (.there .here)`). -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-- A ternary tree with a label at each leaf. -/
inductive Tree3 where
  | leaf (val : Nat)
  | node (a b c : Tree3)
  deriving LeanScriptTyWf

/-- The type of a ternary tree, in the language. -/
abbrev tree3T : TyWf := tyWfOf Tree3

-- The derived tree is a recursive tagged union with three occurrences of itself.
example :
    tyOf Tree3 = .recTaggedUnion (.payloadFirst ⟨.prim .nat, []⟩ [.self, .self, .self] []) :=
  rfl

namespace Tree3

/-- The complete ternary tree of height `n`, with leaves labelled `1`. -/
def full : Nat → Tree3
  | 0 => .leaf 1
  | n + 1 => .node (full n) (full n) (full n)

/-- A spine of `n` nodes down the first child, the other children leaves labelled by the
    level. -/
def firstSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (firstSpine n) (.leaf (n + 1)) (.leaf (n + 1))

/-- A spine of `n` nodes down the middle child. -/
def midSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (.leaf (n + 1)) (midSpine n) (.leaf (n + 1))

/-- A spine of `n` nodes down the last child. -/
def lastSpine : Nat → Tree3
  | 0 => .leaf 0
  | n + 1 => .node (.leaf (n + 1)) (.leaf (n + 1)) (lastSpine n)

end Tree3

/-- `Tree3.full`, as a term: a `nat_rec` whose branch builds a node with
    `recTaggedUnion_mk`. -/
def full3_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.full

/-- `Tree3.firstSpine`, as a term. -/
def firstSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.firstSpine

/-- `Tree3.midSpine`, as a term. -/
def midSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.midSpine

/-- `Tree3.lastSpine`, as a term. -/
def lastSpine_term : Term sigAdd [] (natT ⇒ tree3T) := #leanscript_to_term Tree3.lastSpine

/-- A ternary tree written out. -/
def tree3a : Tree3 :=
  .node (.leaf 1) (.node (.leaf 2) (.leaf 3) (.node (.leaf 4) (.leaf 5) (.leaf 6))) (.leaf 7)

/-- `tree3a`, as a term: nested `recTaggedUnion_mk`s. -/
def tree3a_term : Term sigAdd [] tree3T := #leanscript_to_term tree3a

/-! ## `k = 0`: the sum of the leaves, and the number of nodes -/

def leafSum_with_k0 : Tree3 → Nat
  | .leaf v => v
  | .node a b c => leafSum_with_k0 a + leafSum_with_k0 b + leafSum_with_k0 c

def leafSum_with_k0_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term leafSum_with_k0

example : recUnionRecDepth? leafSum_with_k0_term = some 0 := by kernel_rfl
example : runAdd leafSum_with_k0_term (runAdd tree3a_term) = 28 := by kernel_rfl
example : runAdd leafSum_with_k0_term (runAdd full3_term 4) = 81 := by kernel_rfl
example : runAdd leafSum_with_k0_term (runAdd midSpine_term 6) =
    leafSum_with_k0 (Tree3.midSpine 6) := by kernel_rfl

def nodes_with_k0 : Tree3 → Nat
  | .leaf _ => 0
  | .node a b c => nodes_with_k0 a + nodes_with_k0 b + nodes_with_k0 c + 1

def nodes_with_k0_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term nodes_with_k0

example : recUnionRecDepth? nodes_with_k0_term = some 0 := by kernel_rfl
example : runAdd nodes_with_k0_term (runAdd full3_term 3) = 13 := by kernel_rfl
example : runAdd nodes_with_k0_term (runAdd tree3a_term) = nodes_with_k0 tree3a := by
  kernel_rfl

/-! ## `k = 1`: `fib` down the middle child, and the sum of the leaves through the last
grandchildren -/

def midFib_with_k1 : Tree3 → Nat
  | .leaf _ => 0
  | .node _ (.leaf _) _ => 1
  | .node _ (.node a b c) _ => midFib_with_k1 b + midFib_with_k1 (.node a b c)

def midFib_with_k1_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term midFib_with_k1

example : recUnionRecDepth? midFib_with_k1_term = some 1 := by kernel_rfl
example : runAdd midFib_with_k1_term (runAdd midSpine_term 1) = 1 := by kernel_rfl
example : runAdd midFib_with_k1_term (runAdd midSpine_term 10) = 55 := by kernel_rfl
example : runAdd midFib_with_k1_term (runAdd tree3a_term) = midFib_with_k1 tree3a := by
  kernel_rfl
example : runAdd midFib_with_k1_term (runAdd full3_term 4) =
    midFib_with_k1 (Tree3.full 4) := by kernel_rfl

/-- The sum of the leaves again, but a node whose last child is a node adds up the answers
    at that child's own children: the deeper look goes into the *third* occurrence. -/
def lastGrandSum_with_k1 : Tree3 → Nat
  | .leaf v => v
  | .node a b (.leaf v) => lastGrandSum_with_k1 a + lastGrandSum_with_k1 b + v
  | .node a b (.node x y z) =>
      lastGrandSum_with_k1 a + lastGrandSum_with_k1 b +
        (lastGrandSum_with_k1 x + lastGrandSum_with_k1 y + lastGrandSum_with_k1 z)

def lastGrandSum_with_k1_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term lastGrandSum_with_k1

example : recUnionRecDepth? lastGrandSum_with_k1_term = some 1 := by kernel_rfl
example : runAdd lastGrandSum_with_k1_term (runAdd tree3a_term) = 28 := by kernel_rfl
example : runAdd lastGrandSum_with_k1_term (runAdd lastSpine_term 7) =
    lastGrandSum_with_k1 (Tree3.lastSpine 7) := by kernel_rfl
example : runAdd lastGrandSum_with_k1_term (runAdd full3_term 4) =
    lastGrandSum_with_k1 (Tree3.full 4) := by kernel_rfl

/-! ## `k = 2`: the tribonacci numbers down the first child -/

def firstTrib_with_k2 : Tree3 → Nat
  | .leaf _ => 0
  | .node (.leaf _) _ _ => 0
  | .node (.node (.leaf _) _ _) _ _ => 1
  | .node (.node (.node a b c) y z) _ _ =>
      firstTrib_with_k2 a + firstTrib_with_k2 (.node a b c) +
        firstTrib_with_k2 (.node (.node a b c) y z)

def firstTrib_with_k2_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term firstTrib_with_k2

example : recUnionRecDepth? firstTrib_with_k2_term = some 2 := by kernel_rfl
example : runAdd firstTrib_with_k2_term (runAdd firstSpine_term 2) = 1 := by kernel_rfl
example : runAdd firstTrib_with_k2_term (runAdd firstSpine_term 10) = 81 := by kernel_rfl
example : runAdd firstTrib_with_k2_term (runAdd full3_term 5) =
    firstTrib_with_k2 (Tree3.full 5) := by kernel_rfl

/-! ## `k = 3`: the tetranacci numbers down the middle child, plus the leaves beside it -/

def midTetra_with_k3 : Tree3 → Nat
  | .leaf _ => 0
  | .node _ (.leaf _) _ => 0
  | .node _ (.node _ (.leaf _) _) _ => 0
  | .node a (.node _ (.node _ (.leaf _) _) _) c => 1 + midTetra_with_k3 a + midTetra_with_k3 c
  | .node _ (.node p (.node q (.node x y z) r) s) _ =>
      midTetra_with_k3 y + midTetra_with_k3 (.node x y z) +
        midTetra_with_k3 (.node q (.node x y z) r) +
        midTetra_with_k3 (.node p (.node q (.node x y z) r) s)

def midTetra_with_k3_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term midTetra_with_k3

example : recUnionRecDepth? midTetra_with_k3_term = some 3 := by kernel_rfl
example : runAdd midTetra_with_k3_term (runAdd midSpine_term 3) = 1 := by kernel_rfl
example : runAdd midTetra_with_k3_term (runAdd midSpine_term 10) = 56 := by kernel_rfl
example : runAdd midTetra_with_k3_term (runAdd tree3a_term) = midTetra_with_k3 tree3a := by
  kernel_rfl
example : runAdd midTetra_with_k3_term (runAdd full3_term 5) =
    midTetra_with_k3 (Tree3.full 5) := by kernel_rfl

/-! ## `k = 4`: the pentanacci numbers down the last child, reading the leaves -/

def lastPenta_with_k4 : Tree3 → Nat
  | .leaf v => v
  | .node _ _ (.leaf _) => 0
  | .node _ _ (.node _ _ (.leaf _)) => 0
  | .node _ _ (.node _ _ (.node _ _ (.leaf _))) => 0
  | .node _ _ (.node _ _ (.node _ _ (.node _ _ (.leaf _)))) => 1
  | .node _ _ (.node p1 q1 (.node p2 q2 (.node p3 q3 (.node a b c)))) =>
      lastPenta_with_k4 c + lastPenta_with_k4 (.node a b c) +
        lastPenta_with_k4 (.node p3 q3 (.node a b c)) +
        lastPenta_with_k4 (.node p2 q2 (.node p3 q3 (.node a b c))) +
        lastPenta_with_k4 (.node p1 q1 (.node p2 q2 (.node p3 q3 (.node a b c))))

def lastPenta_with_k4_term : Term sigAdd [] (tree3T ⇒ natT) :=
  #leanscript_to_term lastPenta_with_k4

example : recUnionRecDepth? lastPenta_with_k4_term = some 4 := by kernel_rfl
example : runAdd lastPenta_with_k4_term (runAdd lastSpine_term 4) = 1 := by kernel_rfl
example : runAdd lastPenta_with_k4_term (runAdd lastSpine_term 12) =
    lastPenta_with_k4 (Tree3.lastSpine 12) := by kernel_rfl
example : runAdd lastPenta_with_k4_term (runAdd full3_term 5) =
    lastPenta_with_k4 (Tree3.full 5) := by kernel_rfl

end TermTests.RecUnionToTerm

end
