/-
# `deriving LeanScriptTyWf`: the `Ty` of a Lean inductive type

Every `example` below is checked by the kernel, so this file *is* the expectation: what
`LeanScript.tyWfOf α` is for each shape of Lean declaration, and what the handler says about
the declarations it refuses.

Two notes.

* The file deliberately does **not** start with `module`.  An inductive with
  `@[computed_field]`s cannot be declared inside a module-system file (its automatic
  `_impl` machinery lives in a private namespace the module header rejects), and computed
  fields are one of the things this test is about.

* Everything is declared inside `namespace InductiveTypesTest` so that names such as
  `MProd` do not collide with the ones the core library already has.
-/
import LeanScript.Ty.Ty
import LeanScript.Ty.Wf
import LeanScript.Ty.WfFacts
import LeanScript.Ty.TyWf
import LeanScript.Ty.Class
import LeanScript.Ty.WfTactic
import LeanScript.Ty.Instances
import LeanScript.Ty.Deriving

open LeanScript

namespace InductiveTypesTest

/-! ## Functions -/

example : tyOf (Nat → Bool) = .fn (.prim .nat) (.prim .bool) := by rfl

/-! ## `Option`: a non-recursive sum -/

/-- `Option α`: a non-recursive sum whose constructor `0` (`none`) carries nothing and
    whose constructor `1` (`some`) carries the value. -/
abbrev expected_ty_option (α : Ty) : Ty := .taggedUnion (.skip (.here ⟨α, []⟩ []))

example : tyOf (Option Nat) = expected_ty_option (.prim .nat) := by rfl

-- `Opt` is a fresh copy of `Option`, and `deriving LeanScriptTyWf` gives it the same tree —
-- the *same constant*, in fact, because the handler stores one tree per shape.
inductive Opt (α : Type) where
  | none
  | some : α → Opt α
  deriving LeanScriptTyWf

example : tyOf (Opt Nat) = expected_ty_option (.prim .nat) := by rfl

/-! ## Pairs: one constructor with two fields -/

/-- `α × β`: one constructor with two fields. -/
abbrev expected_ty_prod (α β : Ty) : Ty := .record ⟨α, β, []⟩

example : tyOf (Nat × Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

structure MProd (α : Type u) (β : Type v) where
  fst : α
  snd : β
  deriving LeanScriptTyWf

example : tyOf (MProd Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

structure Pair (α β : Type) where
  first  : α
  second : β
  deriving LeanScriptTyWf

example : tyOf (Pair Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

inductive Tuple2 (α β : Type) where
  | mk : α → β → Tuple2 α β
  deriving LeanScriptTyWf

example : tyOf (Tuple2 Nat Bool) = expected_ty_prod (.prim .nat) (.prim .bool) := by rfl

-- `And` is a `Prop`: its proofs carry nothing at run time, so it has no `Ty` at all —
-- which the handler says rather than inventing a type for it.
/--
error: the type `And` carries no value, so it has no `Ty`
-/
#guard_msgs in
deriving instance LeanScriptTyWf for And

/-! ## Computed fields are ordinary fields

A `@[computed_field]` is a value the runtime representation *stores*, so it is one more
field of the object: the tree of the declaration is a record holding the shape the
declaration would otherwise have, followed by the terminal types of the cached values, in
declaration order.  When the shape itself is erased — a single-constructor, field-less
declaration — only the cached values are left. -/

example : tyOf Bool = .prim .bool := by rfl

-- A computed field needs at least two constructors (with one constructor there is no tag
-- to store the cached value beside), which is why this is a two-constructor declaration.
inductive BoolWithComputed where
  | mk : Bool → BoolWithComputed
  | mk2 : Bool → BoolWithComputed
with
  @[computed_field] foo : BoolWithComputed → Nat
    | .mk b => if b then 0 else 1
    | .mk2 _ => 2

deriving instance LeanScriptTyWf for BoolWithComputed

example :
    tyOf BoolWithComputed
      = .record ⟨.taggedUnion (.payloadFirst ⟨.prim .bool, []⟩ [.prim .bool] []),
                 .prim .nat, []⟩ := by rfl

-- A `Unit` field carries nothing, so `MyUnit` has exactly one value and no `Ty`.
inductive MyUnit where
  | mk : Unit → MyUnit

/--
error: the type `InductiveTypesTest.MyUnit` carries no value, so it has no `Ty`
-/
#guard_msgs in
deriving instance LeanScriptTyWf for MyUnit

-- 1. two-constructor enum
inductive Dir where
  | north
  | south
  deriving LeanScriptTyWf

example : tyOf Dir = .prim .bool := by rfl

inductive DirWithComputed where
  | north
  | south
with
  @[computed_field] foo : DirWithComputed → Nat
    | .north => 0
    | .south => 1

deriving instance LeanScriptTyWf for DirWithComputed

example : tyOf DirWithComputed = .record ⟨.prim .bool, .prim .nat, []⟩ := by rfl

-- 2. three-constructor enum
inductive Dir3 where
  | n
  | s
  | e
  deriving LeanScriptTyWf

example : tyOf Dir3 = .enum ⟨0, 0⟩ := by rfl

inductive Dir3WithComputed where
  | n
  | s
  | e
with
  @[computed_field] foo : Dir3WithComputed → Nat
    | .n => 0
    | .s => 1
    | .e => 2

deriving instance LeanScriptTyWf for Dir3WithComputed

example : tyOf Dir3WithComputed = .record ⟨.enum ⟨0, 0⟩, .prim .nat, []⟩ := by rfl

/-! ## A model that is a decision, not a translation

`Ordering` is mechanically a field-less sum of three constructors, so a translation would
number them `0`, `1`, `2`.  Its instance says otherwise — the enum is shifted, so that
`lt`, `eq` and `gt` are `-1`, `0` and `1` — and because the answer lives in an instance,
every declaration that mentions an `Ordering` gets *that* model. -/

example : tyOf Ordering = .enum ⟨0, -1⟩ := by rfl

structure Comparison where
  how : Ordering
  weight : Nat
  deriving LeanScriptTyWf

example : tyOf Comparison = .record ⟨.enum ⟨0, -1⟩, .prim .nat, []⟩ := by rfl

/-! ## Records and newtypes -/

-- 3. record
structure Point where
  x : Nat
  y : Nat
  deriving LeanScriptTyWf

example : tyOf Point = .record ⟨.prim .nat, .prim .nat, []⟩ := by rfl

-- 4. newtype: the wrapper is erased, so a `Wrap` *is* a `Nat`.
structure Wrap where
  v : Nat
  deriving LeanScriptTyWf

example : tyOf Wrap = .prim .nat := by rfl

/-! ## Recursive declarations -/

-- 6. recursive tagged union
inductive T where
  | leaf
  | node : T → T → T
  deriving LeanScriptTyWf

example : tyOf T = .recTaggedUnion (.skip (.here ⟨.self, [.self]⟩ [])) := by rfl

-- 7. recursive object (nested through `Array`)
structure Tree where
  n : Nat
  kids : Array Tree
  deriving LeanScriptTyWf

example : tyOf Tree = .recObject ⟨.prim .nat, .array .self, []⟩ := by rfl

-- 8. recursive alias (newtype, nested through `Array`)
structure Rose where
  kids : Array Rose
  deriving LeanScriptTyWf

example : tyOf Rose = .recAlias (.array .self) := by rfl

-- 9. mutual family.  Member `0` is `Ev`, member `1` is `Od`, and inside the bodies
--    `Ty.familyMember i` is an occurrence of member `i`.
mutual
  inductive Ev where
    | zero
    | succ : Od → Ev
  inductive Od where
    | succ : Ev → Od
end

deriving instance LeanScriptTyWf for Ev
deriving instance LeanScriptTyWf for Od

/-- Member `0`: `Ev`, the two-constructor sum `zero | succ (_ : Od)`. -/
abbrev evMember : LeanFamMemberSchema Ty :=
  .ctors (.skip (.here ⟨.familyMember 1, []⟩ []))
/-- Member `1`: `Od`, a newtype around an `Ev`. -/
abbrev odMember : LeanFamMemberSchema Ty := .alias (.familyMember 0)

example : tyOf Ev = .mutualRecursiveFamily (.selectedThenMore [] evMember odMember []) := by rfl

example : tyOf Od = .mutualRecursiveFamily (.selectedLast evMember [] odMember) := by rfl

-- 10. the original example
inductive Foo where
  | a : Foo
  | b : Nat → Foo → Foo
  deriving LeanScriptTyWf

example : tyOf Foo = .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])) := by rfl

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

deriving instance LeanScriptTyWf for NatList

-- The cached values are *part of* a `NatList`, so the tail a `cons` holds is a whole
-- `NatList` — the union together with its sum and length — and not the bare union.  The
-- binder is therefore the record: `self` inside the union denotes the record it is a
-- field of.
example :
    tyOf NatList
      = .recObject ⟨.taggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])),
                    .prim .nat, [.prim .nat]⟩ := by rfl

-- `Lean.Name` is the recursive tagged union `anonymous | str | num` caching a `UInt64`,
-- so it is the recursive record of that union and the cached value; the `self`s inside
-- the union are occurrences of the record, which is what a `Name` field holds.
deriving instance LeanScriptTyWf for Lean.Name

example :
    tyOf Lean.Name
      = .recObject
          ⟨.taggedUnion (.skip (.here ⟨.self, [.prim .string]⟩ [[.self, .prim .nat]])),
           .prim .uint64, []⟩ := by rfl

/-! ## The same declaration at two different arguments

A list is modelled by its instance, so `List (List Nat)` holds the tree of `List Nat`
**by reference** — the leaf is that instance's own `tyOf`, and the inner list is not
translated, copied or checked again. -/

example : tyOf (List Nat) = .recTaggedUnion (.skip (.here ⟨.prim .nat, [.self]⟩ [])) := by rfl

example :
    tyOf (List (List Nat))
      = .recTaggedUnion (.skip (.here ⟨tyOf (List Nat), [.self]⟩ [])) := by rfl

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

/-! ## Recursion through a type whose own model is recursive

`inductive RoseList | node : List RoseList → RoseList` and
`structure Rose where kids : Array Rose` describe the same values — a node holds a
sequence of nodes — so both have a model, and the difference is only in *how* the
sequence is written.

* `Array`'s model is a shape, so the occurrence can stand inside it directly:
  `Rose = μX. Array X`.
* `List`'s model is a binder of its own (`nil | cons α self`), so an occurrence placed
  inside it would read as an occurrence of the *list*.  The binder is therefore hoisted
  into a member of a mutual family — the nested recursion becomes a mutual one, which is
  what Lean itself does with a nested inductive:

  ```text
  member 0 = RoseList = member 1
  member 1 = nil | cons (_ : member 0) (_ : member 1)
  ```
-/

/-- `Rose` (declared above) holds its children in an `Array`, whose model is a shape, so
    the occurrence stands inside it and no family is needed. -/
theorem tyWfOf_rose : tyOf Rose = .recAlias (.array .self) := by rfl

inductive RoseList where
  | node : List RoseList → RoseList
  deriving LeanScriptTyWf

/-- `RoseList` is modelled by the family its nested recursion unfolds to: member `0` is
    the declaration, member `1` is the list of them. -/
theorem tyWfOf_roseList :
    tyOf RoseList
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.alias (.familyMember 1))
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            []) := by rfl

-- A wrapper inside a wrapper adds one member per binder on the path to the occurrence.
inductive RoseListList where
  | node : List (List RoseListList) → RoseListList
  deriving LeanScriptTyWf

example :
    tyOf RoseListList
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.alias (.familyMember 2))
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            [.ctors (.skip (.here ⟨.familyMember 1, [.familyMember 2]⟩ []))]) := by rfl

-- The declaration keeps its own shape: here a sum with a base case, whose recursive
-- constructor holds the list.
inductive Forest where
  | tip : Nat → Forest
  | branch : List Forest → Forest
  deriving LeanScriptTyWf

example :
    tyOf Forest
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.ctors (.payloadFirst ⟨.prim .nat, []⟩ [.familyMember 1] []))
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            []) := by rfl

-- A parameter is no obstacle: the list is of the declaration at *its own* arguments.
inductive TreeL (α : Type) where
  | node : α → List (TreeL α) → TreeL α
  deriving LeanScriptTyWf

example :
    tyOf (TreeL Nat)
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.record ⟨.prim .nat, .familyMember 1, []⟩)
            (.ctors (.skip (.here ⟨.familyMember 0, [.familyMember 1]⟩ [])))
            []) := by rfl

-- What is still refused: a wrapper whose *own* model is a mutual family.  Hoisting turns
-- one binder into one member, and there is no member a whole family can become.
mutual
inductive ListA (α : Type) where
  | nil
  | cons : α → ListB α → ListA α
inductive ListB (α : Type) where
  | mk : ListA α → Nat → ListB α
end

deriving instance LeanScriptTyWf for ListA, ListB

inductive ViaFamily where
  | node : ListA ViaFamily → ViaFamily

/--
error: the type `InductiveTypesTest.ViaFamily` has no `Ty`: `ListA
  ViaFamily` mentions the declaration being defined through a type this handler cannot recurse through: the occurrence goes where the argument's tree would stand in the type former's own model (`Array`, `Thunk`, `Option`, `×`, `⊕`, a function type, any non-recursive wrapper), and a binder that would capture it there is hoisted into a member of a family (`List`, any recursive wrapper) — but the model of this one is a mutual family, or does not hold the argument as one tree
-/
#guard_msgs in
deriving instance LeanScriptTyWf for ViaFamily

-- A `mutual` family may recurse through a wrapper too: the hoisted members follow the
-- declared ones.
mutual
inductive EvList where
  | mk : List OdList → EvList
inductive OdList where
  | mk : List EvList → OdList
end

deriving instance LeanScriptTyWf for EvList, OdList

example :
    tyOf EvList
      = .mutualRecursiveFamily
          (.selectedThenMore []
            (.alias (.familyMember 2))
            (.alias (.familyMember 3))
            [.ctors (.skip (.here ⟨.familyMember 1, [.familyMember 2]⟩ [])),
             .ctors (.skip (.here ⟨.familyMember 0, [.familyMember 3]⟩ []))]) := by rfl

end InductiveTypesTest

-- 1. recursive tagged union with existential in both constructors and different

mutual
  inductive Process (α : Type) : Type 1 where
    | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat) : Process α
    | step (State : Type)
           (seed  : State)
           (trans : State → ProcessOption α State) : Process α
           -- same as `(trans : State → Option (State × α × Process α)) : Process α`

  inductive ProcessOption (α : Type) : Type → Type 1 where
    | none {State : Type} : ProcessOption α State
    | some {State : Type} (nextState : State)
                          (value : α)
                          (proc : Process α) : ProcessOption α State
end

/--
error: the type `Process` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Process, ProcessOption

-- TODO: we should be able to model using Term
def mixedProcess : Process Nat :=
  -- Top level: State is Nat
  Process.step Nat 0 (fun n =>
    -- We must return `ProcessOption Nat Nat`
    ProcessOption.some (n + 1) 42 (
      -- Next level: State is String
      Process.step String "hello" (fun s =>
        -- We must return `ProcessOption Nat String`
        ProcessOption.some (s ++ "!") 99 (
          -- Leaf level: a `Process Nat`
          Process.halt Bool (fun b => if b then 1 else 0)
        )
      )
    )
  )

def varyingProcess : Process Nat :=
  Process.step Nat 0 (fun n =>
    if n = 0 then
      ProcessOption.some 1 7 (Process.step Unit () (fun _ => ProcessOption.none))
    else
      ProcessOption.some 1 7 (Process.step Bool true (fun _ => ProcessOption.none)))

-- 2. recursive tagged union with existential in both constructors and different

inductive ProcessHaltIsOut (α : Type) : Type 1 where
  | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat)
  | step (State : Type) (seed : State)
         (emit : State → Option (State × α)) -- no recursion here
         (next : State → ProcessHaltIsOut α) -- no nesting here

/--
error: the type `ProcessHaltIsOut` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for ProcessHaltIsOut

-- 3. recursive tagged union with existential in both constructors and different

mutual
  /-- A Client hides its `ClientState` and emits a request to a `Server`. -/
  inductive Client (Req Resp : Type) : Type 1 where
    | stop (ServerState : Type) (get : ServerState -> Nat) : Client Req Resp
    | mk   (ClientState : Type)
           (seed        : ClientState)
           (send        : ClientState → Req × Server Req Resp)
           : Client Req Resp

  /-- A Server hides its `ServerState`, processes a request,
      produces a response, and transitions to a `Client`. -/
  inductive Server (Req Resp : Type) : Type 1 where
    | stop (ClientState : Type) (get : ClientState -> Nat) : Server Req Resp
    | mk   (ServerState : Type)
           (seed        : ServerState)
           (receive     : ServerState → Req → Resp × Client Req Resp)
           : Server Req Resp
end

/--
error: the type `Client` has no `Ty`: existential typing is not yet supported, `ServerState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Client, Server

-- but this can
mutual
  /-- The twin of `Client`, at client states `C` and server states `S`. -/
  inductive ClientTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : C) (send : C → Req × ServerTwin C S Req Resp)

  /-- The twin of `Server`, at the same two choices. -/
  inductive ServerTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : S) (receive : S → Req → Resp × ClientTwin C S Req Resp)
end

deriving instance LeanScriptTyWf for ClientTwin, ServerTwin

/-- Hides two types: the state and an intermediate token type. -/
structure StreamPipeline (α : Type) (β : Type) where
  State : Type
  Inter : Type
  seed  : State
  feed  : State → α → State × Option Inter
  emit  : State → Inter → State × Option β

/--
error: the type `StreamPipeline` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for StreamPipeline

/-- Hides three types: the lexer's state, the syntax tree and the evaluator's environment. -/
structure CompilerEngine (α : Type) (β : Type) where
  LexState : Type
  AstType  : Type
  EvalEnv  : Type
  start    : LexState
  lex      : LexState → α → LexState
  parse    : LexState → AstType
  eval     : EvalEnv → AstType → β

-- as with `Unfold`: the refusal is pinned by the `deriving instance` below.

/--
error: the type `CompilerEngine` has no `Ty`: existential typing is not yet supported, `LexState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for CompilerEngine

structure Keyed where
  State : Type
  Elem  : State → Type
  seed  : State
  get   : (s : State) → Elem s

/--
error: the type `Keyed` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Keyed

structure Layered (α : Type) where
  State : Type
  seed  : State
  subs  : List (Layered α)
  tag   : α
