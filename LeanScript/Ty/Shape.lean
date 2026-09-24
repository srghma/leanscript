module

public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
public import LeanScript.Ty.Schema

@[expose] public section

namespace LeanScript

/-!
# `TyShape`: one node of the type language, with its children abstracted

`TyShape α` is one node whose children are `α`s: everything a type can be except an
occurrence of the declaration it sits inside and the four recursive binders.

`LeanScript.Ty` is `TyShape Ty` plus exactly those — `Ty.self`, `Ty.familyMember i` and
the binders.  Keeping the shapes in a functor of their own is what lets a traversal,
a renderer or a backend say what it does at *a node* once, without repeating the six
cases; it is also what the earlier two-language representation shared between its
layers, and the only part of that arrangement worth keeping now that there is one
language.
-/

/-- One node of the type language whose children are `α`s: everything except an
    occurrence of the declaration being defined and the four recursive binders, which
    `LeanScript.Ty` adds. -/
inductive TyShape (α : Type) where
  /-- A terminal type: a scalar or other built-in leaf.  See `LeanPrimTy`. -/
  | prim : LeanPrimTy → TyShape α
  /-- A function type, `σ ⇒ τ`: **one** parameter and **one** result, since every
      function of the language is curried. -/
  | fn : α → α → TyShape α
  /-- A built-in type former that carries one type: an array, a thunk or a lazy value. -/
  | primCovariant : LeanPrimTyCovariant α → TyShape α
  /-- A sum whose constructors all have no fields, of which there are at least three. -/
  | enum : LeanEnumSchema → TyShape α
  /-- A single-constructor type with at least two fields, in declaration order. -/
  | record : LeanRecordSchema α → TyShape α
  /-- A non-recursive sum type with fields: one entry per constructor, in declaration
      order, each holding the types of that constructor's fields. -/
  | taggedUnion : LeanTaggedUnionSchema α → TyShape α
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

/-- An array, a thunk or a lazy value is a node.  (There is no such instance for
    `LeanPrimTy`: the type it would be coerced into does not mention `LeanPrimTy`, so the
    children of the node are not determined by the source of the coercion.) -/
instance {α : Type} : CoeOut (LeanPrimTyCovariant α) (TyShape α) := ⟨.primCovariant⟩
/-- A record schema is a node. -/
instance {α : Type} : CoeOut (LeanRecordSchema α) (TyShape α) := ⟨.record⟩
/-- A tagged-union schema is a node. -/
instance {α : Type} : CoeOut (LeanTaggedUnionSchema α) (TyShape α) := ⟨.taggedUnion⟩

/-- `LeanPrimTyCovariant.map` obeys the functor laws. -/
instance : LawfulFunctor LeanPrimTyCovariant where
  map_const := rfl
  id_map c := by cases c <;> rfl
  comp_map _ _ c := by cases c <;> rfl

namespace TyShape

variable {α β : Type}

/-- Rebuild a node with every child mapped. -/
def map (f : α → β) : TyShape α → TyShape β
  | .prim p => .prim p
  | .fn a b => .fn (f a) (f b)
  | .primCovariant s => .primCovariant (s.map f)
  | .enum e => .enum e
  | .record fs => .record (fs.map f)
  | .taggedUnion l => .taggedUnion (l.map f)

/-- The children of a node, in order. -/
def children : TyShape α → List α
  | .prim _ => []
  | .fn a b => [a, b]
  | .primCovariant s => [s.val]
  | .enum _ => []
  | .record fs => fs.toList
  | .taggedUnion l => l.toList.flatten

@[simp] theorem map_id (s : TyShape α) : s.map id = s := by
  cases s with
  | primCovariant c => cases c <;> rfl
  | _ => simp [map]

theorem map_comp {γ : Type} (g : β → γ) (h : α → β) (s : TyShape α) :
    s.map (fun x => g (h x)) = (s.map h).map g := by
  cases s with
  | primCovariant c => cases c <;> rfl
  | _ => simp [map, LeanRecordSchema.map_comp, LeanTaggedUnionSchema.map_comp]

/-- `<$>` is `TyShape.map`: it applies a function to every child and keeps the node. -/
instance : Functor TyShape where
  map := map

instance : LawfulFunctor TyShape where
  map_const := rfl
  id_map := map_id
  comp_map g h s := map_comp h g s

end TyShape

end LeanScript

end
