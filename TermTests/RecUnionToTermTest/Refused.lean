module

public import TermTests.RecUnionToTermTest.K0
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k`: what has no term at any depth

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked and for the datatypes.
A deeper look follows one path, so a recursion that reads under two subvalues at once is
refused. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

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
