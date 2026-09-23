import TyTests.InductiveTypesTest.Basic

/-!
# `deriving LeanScriptTyWf`: type parameters, recursion through a shape, refusals

Part of the `deriving LeanScriptTyWf` suite that starts in `TyTests.InductiveTypesTest.Basic`; like it, this
file deliberately does not start with `module`.
-/

open LeanScript

namespace InductiveTypesTest

/-! ## Type parameters -/

-- `Box` is a newtype, so it is optimised away: a `Box α` *is* an `α`.
inductive Box (α : Type) where
  | mk : α → Box α
  deriving LeanScriptTyWf

example : tyOf (Box Nat) = .prim .nat := by rfl

inductive Box2 (α : Type) where
  | mk : α → α → Box2 α
  deriving LeanScriptTyWf

example : tyOf (Box2 Nat) = .record ⟨.prim .nat, .prim .nat, []⟩ := by rfl

inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero
  deriving LeanScriptTyWf

example :
    tyOf Expr
      = .recTaggedUnion (.payloadFirst ⟨.self, [.self]⟩ [.self, .self] [[.self], []]) := by rfl

inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α
  | Mul : α → α → ExprF α
  deriving LeanScriptTyWf

example :
    tyOf (ExprF Bool)
      = .taggedUnion (.payloadFirst ⟨.prim .int, []⟩ [.prim .bool, .prim .bool]
          [[.prim .bool, .prim .bool]]) := by rfl

-- A parametric *recursive* declaration is a tree with a hole for each parameter, and the
-- hole is filled with the parameter's own tree.
inductive PTree (α : Type) where
  | leaf
  | node : PTree α → α → PTree α → PTree α
  deriving LeanScriptTyWf

example :
    tyOf (PTree Nat)
      = .recTaggedUnion (.skip (.here ⟨.self, [.prim .nat, .self]⟩ [])) := by rfl

/-! ## Recursion through a type former that is a shape

The children of a *shape* are written in the same scope as the shape, so a shape may hold
an occurrence of the declaration being defined: `Option`, `×` and `⊕` can be recursed
through, as `Array`, `Thunk` and `→` already could.  A *binder* — `List`, or any other
recursive declaration — cannot; see the last section. -/

/-- A list written the other way round: `T = Option (Nat × T)`. -/
inductive Chain where
  | mk : Option (Nat × Chain) → Chain
  deriving LeanScriptTyWf

example :
    tyOf Chain
      = .recAlias (.taggedUnion (.skip (.here ⟨.record ⟨.prim .nat, .self, []⟩, []⟩ [])))
  := by rfl

/-- The model the handler builds for `Option` of the declaration is the model `Option`
    has everywhere else, with the occurrence in the place of the argument's tree. -/
example : tyOf (Option Nat) = .taggedUnion (.skip (.here ⟨tyOf Nat, []⟩ [])) := rfl
example : tyOf (Nat × Bool) = .record ⟨tyOf Nat, tyOf Bool, []⟩ := rfl
example : tyOf (Nat ⊕ Bool) = .taggedUnion (.payloadFirst ⟨tyOf Nat, []⟩ [tyOf Bool] []) :=
  rfl

/-- A binary tree whose children are one value of a sum. -/
inductive SumTree where
  | mk : String ⊕ (SumTree × SumTree) → SumTree
  deriving LeanScriptTyWf

example :
    tyOf SumTree
      = .recAlias (.taggedUnion
          (.payloadFirst ⟨.prim .string, []⟩ [.record ⟨.self, .self, []⟩] [])) := by rfl

/-! ### A wrapper of one's own

Nothing about this is special to the library's type formers: the tree is the wrapper's own
instance with the occurrence in the place of its parameter's tree, so a wrapper the user
wrote works exactly as `Option` does — as long as the wrapper is not itself recursive. -/

/-- A non-recursive wrapper: its model is a record, which is a shape. -/
structure Labelled (α : Type) where
  label : String
  value : α
  deriving LeanScriptTyWf

inductive LabelledTree where
  | leaf
  | node : Labelled LabelledTree → LabelledTree
  deriving LeanScriptTyWf

example :
    tyOf LabelledTree
      = .recTaggedUnion
          (.skip (.here ⟨.record ⟨.prim .string, .self, []⟩, []⟩ [])) := by rfl

/-- A recursive wrapper of one's own: its model is a binder, so an occurrence inside it
    would be an occurrence of *it*.  The binder is therefore hoisted into a member of a
    family — exactly as `List` is, and for the same reason. -/
inductive Bag (α : Type) where
  | nil
  | cons : α → Bag α → Bag α
  deriving LeanScriptTyWf

inductive BagTree where
  | node : Bag BagTree → BagTree
  deriving LeanScriptTyWf

example :
    tyOf BagTree
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.alias (.familyMember 1))
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            []) := by rfl

structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

-- `deriving LeanScriptTyWf` on the declaration itself is refused for the same reason as
-- the `deriving instance` below, which pins the message; a `deriving` clause cannot carry
-- a `#guard_msgs`, so it is written out here instead.

/--
error: the type `InductiveTypesTest.Unfold` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Unfold

/-! ## What cannot be derived -/

-- 1. A field whose type has no instance: the handler names it and stops, rather than
--    translating a second copy of it.
structure NeedsInstance where
  x : Nat
  y : Except String Nat

/--
error: the type `InductiveTypesTest.NeedsInstance` has no `Ty`: `Except String
  Nat` has no `LeanScriptTyWf` instance; derive or write one for it first
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NeedsInstance

deriving instance LeanScriptTyWf for Except

deriving instance LeanScriptTyWf for NeedsInstance -- now should pass

-- 2. A declaration one of whose fields has no `Ty` at all: a function *answering* with a
--    type has no instance either, and the handler names what it could not model.
structure NoValue where
  f : Nat → Type

/--
error: the type `InductiveTypesTest.NoValue` has no `Ty`: existential typing is not yet supported, `f` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for NoValue

end InductiveTypesTest
