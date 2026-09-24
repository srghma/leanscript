module

public import TermTests.RecUnionToTermTest.Common
public meta import LeanScript.KernelRfl
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-! # `recTaggedUnion_rec k` on `List Nat` (one recursive point)

Part of the `recTaggedUnion_rec k` translation tests; see
`TermTests/RecUnionToTermTest/Common.lean` for what is checked.

`List Nat` is the recursive tagged union `nil | cons nat self`.  A program that matches
`k + 1` conses deep is `recTaggedUnion_rec k`: each deeper look goes into the tail. -/

namespace TermTests.RecUnionToTerm

open LeanScript TermTests.NatRecDepth

/-- A list of the language, from a Lean list. -/
abbrev natList (l : List Nat) : TyWf.Den (tyWfOf (List Nat)) := Ty.DenRec.ofList (.prim .nat) l

/-! ## `k = 0`: the sum of a list, and the same sum with an accumulator -/

def listSum_with_k0 : List Nat → Nat
  | [] => 0
  | x :: xs => x + listSum_with_k0 xs

def listSum_with_k0_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listSum_with_k0

example : recUnionRecDepth? listSum_with_k0_term = some 0 := by kernel_rfl
example : runAdd listSum_with_k0_term (natList []) = 0 := by kernel_rfl
example : runAdd listSum_with_k0_term (natList [3, 1, 4, 1, 5]) = 14 := by kernel_rfl
example : runAdd listSum_with_k0_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) =
    listSum_with_k0 [3, 1, 4, 1, 5, 9, 2, 6] := by kernel_rfl

def listSumAcc_with_k0 : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => listSumAcc_with_k0 xs (acc + x)

def listSumAcc_with_k0_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT ⇒ natT) :=
  #leanscript_to_term listSumAcc_with_k0

example : recUnionRecDepth? listSumAcc_with_k0_term = some 0 := by kernel_rfl
example : runAdd listSumAcc_with_k0_term (natList [3, 1, 4]) 10 = 18 := by kernel_rfl
example : runAdd listSumAcc_with_k0_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) 7 =
    listSumAcc_with_k0 [3, 1, 4, 1, 5, 9, 2, 6] 7 := by kernel_rfl

/-! ## `k = 1`: `fib` of the length, and the sum of the products of neighbours -/

def listFib_with_k1 : List Nat → Nat
  | [] => 0
  | [_] => 1
  | _ :: y :: rest => listFib_with_k1 rest + listFib_with_k1 (y :: rest)

def listFib_with_k1_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listFib_with_k1

example : recUnionRecDepth? listFib_with_k1_term = some 1 := by kernel_rfl
example : runAdd listFib_with_k1_term (natList []) = 0 := by kernel_rfl
example : runAdd listFib_with_k1_term (natList [7]) = 1 := by kernel_rfl
example : runAdd listFib_with_k1_term (natList (List.replicate 10 0)) = 55 := by kernel_rfl
example : runAdd listFib_with_k1_term (natList (List.range 12)) =
    listFib_with_k1 (List.range 12) := by kernel_rfl

def listNeighbourProducts_with_k1 : List Nat → Nat
  | x :: y :: rest => x * y + listNeighbourProducts_with_k1 (y :: rest)
  | _ => 0

def listNeighbourProducts_with_k1_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listNeighbourProducts_with_k1

example : recUnionRecDepth? listNeighbourProducts_with_k1_term = some 1 := by kernel_rfl
example : runAdd listNeighbourProducts_with_k1_term (natList [7]) = 0 := by kernel_rfl
example : runAdd listNeighbourProducts_with_k1_term (natList [1, 2, 3, 4]) = 20 := by
  kernel_rfl
example : runAdd listNeighbourProducts_with_k1_term (natList [3, 1, 4, 1, 5, 9, 2, 6]) =
    listNeighbourProducts_with_k1 [3, 1, 4, 1, 5, 9, 2, 6] := by kernel_rfl

/-! ## `k = 2`: the tribonacci numbers of the length -/

def listTrib_with_k2 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 1
  | _ :: y :: z :: rest =>
      listTrib_with_k2 rest + listTrib_with_k2 (z :: rest) + listTrib_with_k2 (y :: z :: rest)

def listTrib_with_k2_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listTrib_with_k2

example : recUnionRecDepth? listTrib_with_k2_term = some 2 := by kernel_rfl
example : runAdd listTrib_with_k2_term (natList [5, 5]) = 1 := by kernel_rfl
example : runAdd listTrib_with_k2_term (natList (List.replicate 10 0)) = 81 := by kernel_rfl
example : runAdd listTrib_with_k2_term (natList (List.range 12)) =
    listTrib_with_k2 (List.range 12) := by kernel_rfl

/-! ## `k = 3`: the tetranacci numbers of the length -/

def listTetra_with_k3 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 0
  | [_, _, _] => 1
  | _ :: y :: z :: w :: rest =>
      listTetra_with_k3 rest + listTetra_with_k3 (w :: rest) +
        listTetra_with_k3 (z :: w :: rest) + listTetra_with_k3 (y :: z :: w :: rest)

def listTetra_with_k3_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listTetra_with_k3

example : recUnionRecDepth? listTetra_with_k3_term = some 3 := by kernel_rfl
example : runAdd listTetra_with_k3_term (natList [1, 2, 3]) = 1 := by kernel_rfl
example : runAdd listTetra_with_k3_term (natList (List.replicate 10 0)) = 56 := by kernel_rfl
example : runAdd listTetra_with_k3_term (natList (List.range 12)) =
    listTetra_with_k3 (List.range 12) := by kernel_rfl

/-! ## `k = 4`: the pentanacci numbers of the length -/

def listPenta_with_k4 : List Nat → Nat
  | []  => 0
  | [_] => 0
  | [_, _] => 0
  | [_, _, _] => 0
  | [_, _, _, _] => 1
  | _ :: y :: z :: w :: v :: rest =>
      listPenta_with_k4 rest + listPenta_with_k4 (v :: rest) +
        listPenta_with_k4 (w :: v :: rest) + listPenta_with_k4 (z :: w :: v :: rest) +
        listPenta_with_k4 (y :: z :: w :: v :: rest)

def listPenta_with_k4_term : Term sigAdd [] (tyWfOf (List Nat) ⇒ natT) :=
  #leanscript_to_term listPenta_with_k4

example : recUnionRecDepth? listPenta_with_k4_term = some 4 := by kernel_rfl
example : runAdd listPenta_with_k4_term (natList [1, 2, 3, 4]) = 1 := by kernel_rfl
example : runAdd listPenta_with_k4_term (natList (List.replicate 10 0)) = 31 := by
  kernel_rfl
example : runAdd listPenta_with_k4_term (natList (List.range 13)) =
    listPenta_with_k4 (List.range 13) := by kernel_rfl

end TermTests.RecUnionToTerm

end
