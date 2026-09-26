module

public import LeanScript.Two
public import LeanScript.Eval
public meta import LeanScript.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# `leanscript_signature`: declaring the datatypes of a program once

Each requested Lean type becomes a `Ty` over one shared signature; every recursive SCC of
Lean type instances becomes one block, declared once, in grounding order.
-/

namespace SignatureTest

open LeanScript

inductive Color where
  | red | green | blue

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

/-- A rose tree whose children are a nested `List`: `List Rose` is on the cycle, so it is
    a member of the block. -/
inductive Rose where
  | node : Nat → List Rose → Rose

mutual
inductive Even where
  | zero : Even
  | succ : Odd → Even
inductive Odd where
  | succ : Even → Odd
end

/-- A rose tree of arrays with a `List Nat` label: `List Nat` is an older block. -/
inductive RoseA where
  | node : List Nat → Array RoseA → RoseA

structure Point where
  x : Nat
  y : Int

leanscript_signature Prog where
  listNat := List Nat
  tree := Tree
  rose := Rose
  even := Even
  roseA := RoseA
  color := Color
  point := Point
  optNat := Option Nat
  fn := Nat → Bool
  pair := Nat × String

/-! ## The blocks -/

/-- Five blocks: `List Nat`, `Tree`, `Rose` with `List Rose`, `Even`/`Odd`, `RoseA`. -/
example : Prog.ks.length = 5 := rfl

/-- Every recursive type is a name; the non-recursive ones are structural. -/
example : Prog.color = .enum ⟨0, 0⟩ := rfl
example : Prog.point = .record .nat (.one .int) := rfl
example : Prog.optNat = Ty.option .nat := rfl
example : Prog.fn = .fn .nat .bool := rfl
example : Prog.pair = .record .nat (.one .string) := rfl
example : ∃ r, Prog.listNat = .data r := ⟨_, rfl⟩
example : ∃ r, Prog.tree = .data r := ⟨_, rfl⟩
example : ∃ r, Prog.rose = .data r := ⟨_, rfl⟩
example : ∃ r, Prog.roseA = .data r := ⟨_, rfl⟩

/-- The meaning of a structural type is the Lean type. -/
example : Ty.Den Prog.Δ Prog.point = (Nat × Int) := rfl
example : Ty.Den Prog.Δ Prog.optNat = Option Nat := rfl

/-- The block sizes, newest first: `RoseA`, `Even`/`Odd`, `List Rose`/`Rose`, `Tree`,
    `List Nat`. -/
example : Prog.ks = [0, 1, 1, 0, 0] := rfl

/-- `List Rose` is on `Rose`'s cycle, so it is a member of the block; it comes first in the
    grounding order (`nil` is its base), then `Rose`. -/
example : Prog.rose = .data (.there (.there (.here 1))) := rfl

/-- Canonical forms: the `List Nat` field of `RoseA` is the name of the oldest block, the same
    datatype as the requested `List Nat`. -/
example : Prog.block4 =
    .cons (.record (.old (.data (.there (.there (.there (.here 0))))))
      (.one (.array (.hole 0 (by decide))))) .nil := rfl
example : Prog.listNat = .data (.there (.there (.there (.there (.here 0))))) := rfl

/-- Values of a declared type are built with `DSig.dataIn`, and folded with `DSig.dataRec`. -/
def leaf : Ty.Den Prog.Δ Prog.tree := Prog.Δ.dataIn (.there (.there (.there .here))) 0 none
def node (l : Ty.Den Prog.Δ Prog.tree) (n : Nat) (r : Ty.Den Prog.Δ Prog.tree) :
    Ty.Den Prog.Δ Prog.tree :=
  Prog.Δ.dataIn (.there (.there (.there .here))) 0 (some (l, n, r))

def treeSum (t : Ty.Den Prog.Δ Prog.tree) : Nat :=
  Prog.Δ.dataRec (.there (.there (.there .here))) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option ((Ty.Den Prog.Δ Prog.tree × Nat) × Nat ×
          (Ty.Den Prog.Δ Prog.tree × Nat))) with
        | none => 0
        | some ((_, a), n, (_, b)) => Nat.add (Nat.add a n) b
      r) 0 t

example : treeSum (node (node leaf 1 leaf) 2 (node leaf 3 leaf)) = 6 := rfl

/-- Every constructor of a declared type is reached through `#leanscript_get_ctor`, which is
    `data_in` of the constructor's fields. -/
def treeT : Term Prog.Δ [] Prog.tree :=
  (#leanscript_get_ctor Tree.node)
    ((#leanscript_get_ctor Tree.node) (#leanscript_get_ctor Tree.leaf) (.lit .nat rfl 1)
      (#leanscript_get_ctor Tree.leaf))
    (.lit .nat rfl 2) (#leanscript_get_ctor Tree.leaf)

example : treeT.run = node (node leaf 1 leaf) 2 leaf := rfl
example : treeSum treeT.run = 3 := rfl

def listT : Term Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 7)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 8)
      (#leanscript_get_ctor List.nil (α := Nat)))

/-- `Even`/`Odd` are one block. -/
example : Term Prog.Δ [] Prog.even := #leanscript_get_ctor Even.zero
example : Term Prog.Δ [] Prog.even :=
  (#leanscript_get_ctor Even.succ) ((#leanscript_get_ctor Odd.succ) (#leanscript_get_ctor Even.zero))

/-- `Rose`'s children are a `List Rose`, the other member of its block. -/
example : Term Prog.Δ [] Prog.rose :=
  (#leanscript_get_ctor Rose.node) (.lit .nat rfl 1) (#leanscript_get_ctor List.nil (α := Rose))

/-- Every type of the program has two different values. -/
example : ∃ x y : Ty.Den Prog.Δ Prog.rose, x ≠ y := Ty.den_exists_ne _ _
example : ∃ x y : Ty.Den Prog.Δ Prog.even, x ≠ y := Ty.den_exists_ne _ _

/-! ## Refusals -/

/-- A recursive type with no finite value. -/
inductive Loop where
  | mk : Loop → Loop

/--
error: LeanScript: these recursive types have no finite value (no grounding order): [Loop]
-/
#guard_msgs in
leanscript_signature Bad₁ where
  loop := Loop

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₂ where
  u := Unit

-- A `Unit` field is not erased: `Unit` has one value, so `Option Unit` (two points, which are
-- only ever `bool`) is refused like `Unit` itself.
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₄ where
  u := Option Unit

/-- A type of two field-less constructors is the leaf `bool`. -/
inductive Switch where
  | off | on

leanscript_signature Ok₂ where
  s := Option Switch

example : Ok₂.s = Ty.option .bool := rfl

/--
error: LeanScript: the type
  Empty
has no constructor (it has no value)
-/
#guard_msgs in
leanscript_signature Bad₃ where
  e := Empty

end SignatureTest

end
