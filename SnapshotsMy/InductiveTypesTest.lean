import Lean
import LeanScript.Term.Elab
import LeanScript.Term.Compile
open Lean Elab Command

example : #leanscript_ty_for (Nat → Bool) = .fn .nat .bool

/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev expected_ty_option (α : Ty) : Ty := .taggedUnion (.skip (.here ⟨α, []⟩ [])) -- TODO: derive using elab

example : #leanscript_ty_for Option = expected_ty_option

example : #leanscript_ty_for (Option Nat) = expected_ty_option .nat

-- 5. Option Nat  (Option is built in; scanned separately).  `Opt` is a fresh copy of it,
--    so that the generated constants can be seen without the core library around them.
inductive Opt (α : Type) where
  | none
  | some : α → Opt α

example : #leanscript_ty_for Opt = expected_ty_option

example : #leanscript_ty_for (Opt Nat) = expected_ty_option .nat

---------------------------------------------------------------

/-- `α × β`: one constructor with two fields. -/
abbrev expected_ty_prod (α β : Ty) : Ty := .record ⟨α, β, []⟩ -- TODO: derive using elab

example : #leanscript_ty_for Prod = expected_ty_prod
example : #leanscript_ty_for PProd = expected_ty_prod

structure MProd (α : Type u) (β : Type v) where
  fst : α
  snd : β

example : #leanscript_ty_for MProd = expected_ty_prod

/- error: TODO: good error about that Props are erased
-/
#guard_msgs #leanscript_ty_for And

structure Pair (α β : Type) where
  first  : α
  second : β

example : #leanscript_ty_for Pair = expected_ty_prod

inductive Tuple2 (α β : Type) where
  | mk : α → β → Tuple2 α β

example : #leanscript_ty_for Tuple2 = expected_ty_prod

structure Entry (α β : Type) where
  key : α
  val : β

example : #leanscript_ty_for Entry = expected_ty_prod

---------------------------------------------------------------

example : #leanscript_ty_for Bool = .bool

inductive BoolWithComputed where
  | mk : Bool → BoolWithComputed
  with
  @[computed_field] foo : BoolWithComputed → Nat
    | .mk b => if b then 0 else 1

example : #leanscript_ty_for BoolWithComputed = .record ⟨.bool, .nat⟩

inductive MyUnit where
  | mk : Unit → MyUnit

example : should throw erorr Term doesnt allow eliminated points in grammar

inductive UnitWithComputed where
  | mk : Unit → BoolWithComputed
  with
  @[computed_field] foo : UnitWithComputed → Nat
    | .mk b => if b then 0 else 1

example : #leanscript_ty_for UnitWithComputed = .nat

-- 1. two-constructor enum
inductive Dir where
  | north
  | south

example : #leanscript_ty_for Dir = .bool

inductive DirWithComputed where
  | north
  | south
  with
  @[computed_field] foo : DirWithComputed → Nat
    | .north => 0
    | .south => 1

example : #leanscript_ty_for DirWithComputed = .record ⟨.bool, .nat⟩

-- 2. three-constructor enum
inductive Dir3 where
  | n
  | s
  | e

example : #leanscript_ty_for Dir3 = .enum -- ⟨0, 0⟩

example : #leanscript_ty_for Dir3WithComputed = .record ⟨.enum, .nat⟩ -- ⟨0, 0⟩

-- 3. record
structure Point where
  x : Nat
  y : Nat

example : #leanscript_ty_for Dir = .record sorry

-- 4. newtype
structure Wrap where
  v : Nat

example : #leanscript_ty_for Wrap = .prim .nat

-- 6. recursive tagged union
inductive T where
  | leaf
  | node : T → T → T

example : #leanscript_ty_for T = .recTaggedUnion sorry

-- 7. recursive object (nested through Array)
structure Tree where
  n : Nat
  kids : Array Tree

example : #leanscript_ty_for ...

-- 8. recursive alias (newtype, nested through Array)
structure Rose where
  kids : Array Rose

example : #leanscript_ty_for ...

-- 9. mutual family
mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

example : #leanscript_ty_for ...

-- 10. the original example
inductive Foo where
  | a : Foo
  | b : Nat → Foo → Foo

example : #leanscript_ty_for ...

/-- A list of numbers that caches its own sum and its own length. -/
inductive NatList where
  | nil
  | cons : Nat → NatList → NatList
with
  /-- The sum of the elements, cached in every `cons`. -/
  @[computed_field] sum : NatList → Nat
    | .nil => 0
    | .cons x l => x + l.sum
  /-- How many elements there are, cached in every `cons`. -/
  @[computed_field] length : NatList → Nat
    | .nil => 0
    | .cons _ l => l.length + 1

example : #leanscript_ty_for ...

/-- A pair of numbers, which caches nothing. -/
structure Pt where
  /-- The first coordinate. -/
  x : Nat
  /-- The second coordinate. -/
  y : Nat

example : #leanscript_ty_for ...

-- The `Ty` the translation gives `Lean.Name` is the one written out as `Ty.name`: the
-- recursive tagged union `anonymous | str | num`, caching a `UInt64`.
example : #leanscript_ty_for Lean.Name = .record ⟨recTaggedUnion , .uint64⟩ := by rfl

-- Should be optimized out, bc its newtype
inductive Box (α : Type) where
  | mk : α → Box α

-- eliminated
example : ∀ (α : Type) . #leanscript_ty_for Box α = α

inductive Box2 (α : Type) where
  | mk : α → α → Box2 α

inductive Expr where
  | add (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | succ (a : Expr)
  | zero

inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α
  | Mul : α → α → ExprF α

-- 1. Stream Representation
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x -- erased

example : ∀ (α : Type) . #leanscript_ty_for Unfold α = .record ⟨3fields⟩ := by rfl
