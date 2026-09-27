module

public import LeanScript.Ty
public import LeanScript.TySchema

@[expose] public section

/-!
# The `Ty` of `ExamplesValidData.ForestPair`'s data

The specimen is a genuinely mutual block

```lean
mutual
  inductive Node   | node (label : Nat) (flag : Nat) (kids : Forest)
  inductive Forest | nil | cons (hd : Node) (tl : Forest)
end
```

This file writes both members down in `LeanScript.Ty` and checks, by `decide`, that the
family is well formed — i.e. that the *data* of the specimen is representable in the
backend's type language, independently of any question about recursion or termination.
-/

namespace LeanScript.ExamplesValidData

open LeanScript

/-- `Node`: one constructor, three fields — `Nat`, `Nat` and member `1` of the family. -/
def nodeMember : Ty.FamMember :=
  .record ⟨.prim .nat, .prim .nat, [.self 1]⟩

/-- `Forest`: `nil` carries nothing, `cons` carries member `0` and member `1`. -/
def forestMember : Ty.FamMember :=
  .ctors (.skip (.here ⟨.self 0, [.self 1]⟩ []))

/-- Both members, in declaration order. -/
def forestFamily : List Ty.FamMember := [nodeMember, forestMember]

/-! The block is genuinely mutual, every member is inhabited, and the family passes
`RTy.wf`'s family check. -/

example : famStronglyConnected forestFamily = true := by decide

example : (LeanMutualRecFamily.ofMembers? forestFamily 0).map famWf = some true := by decide

/-- The type of `Node`: member `0` of the family. -/
def nodeTy : Ty := .mutualRecursiveFamily (.selectedThenMore [] nodeMember forestMember [])

/-- The type of `Forest`: member `1` of the same family. -/
def forestTy : Ty := .mutualRecursiveFamily (.selectedLast nodeMember [] forestMember)

example : nodeTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 0 := rfl
example : forestTy.mutualRecFamily?.map LeanMutualRecFamily.memberIdx = some 1 := rfl

/-! ## The refined data of `ExamplesValidData.ForestRefined`

```lean
mutual
  inductive MNode   | node (label : Nat) (kids : MForest)
  inductive MForest | nil | cons2 (a b : MNode) (rest : MForest)
end
```

The two conjuncts "every node is marked" and "the length is even" are conditions on the
*shape*, so they can be moved into the type: the flag field disappears (a field fixed to
one value carries no information) and the elements are stored two at a time.  The family
is well formed, so the refined data is representable too — and its runtime
representation is strictly smaller than `nodeTy`'s. -/

/-- `MNode`: a label and the children; no flag field. -/
def mnodeMember : Ty.FamMember :=
  .record ⟨.prim .nat, .self 1, []⟩

/-- `MForest`: `nil`, or two nodes and a tail. -/
def mforestMember : Ty.FamMember :=
  .ctors (.skip (.here ⟨.self 0, [.self 0, .self 1]⟩ []))

/-- Both refined members, in declaration order. -/
def mforestFamily : List Ty.FamMember := [mnodeMember, mforestMember]

example : famStronglyConnected mforestFamily = true := by decide

example : (LeanMutualRecFamily.ofMembers? mforestFamily 0).map famWf = some true := by decide

/-- The type of `MForest`: member `1` of the refined family. -/
def mforestTy : Ty := .mutualRecursiveFamily (.selectedLast mnodeMember [] mforestMember)

/-! The refined node has one field fewer than the plain one — the flag is gone, because a
field that can hold only one value carries no information.  `mforestTy` is therefore a
*different* runtime type from `forestTy`, which is the whole point and also the cost: a
caller holding a plain forest cannot pass it here without converting. -/

example : nodeMember.toCtors.map List.length = [3] := by decide
example : mnodeMember.toCtors.map List.length = [2] := by decide
example : forestMember.toCtors.map List.length = [0, 2] := by decide
example : mforestMember.toCtors.map List.length = [0, 3] := by decide

end LeanScript.ExamplesValidData
