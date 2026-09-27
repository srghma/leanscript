/-
# Proof-carrying *bundles*: classes with laws, inherited structures, `autoParam` fields

A type class is a structure, so everything in `ExamplesProofFields/Variants.lean` applies
to it — but classes are where proof fields are most common in practice ("lawful"
classes), and where they most often erase the whole dictionary away.  Structure
inheritance and `autoParam` fields are here for the same reason: they are ways of writing
a field that are easy to forget when counting what survives.

`ExamplesProofFields/Classes-Shapes.txt` is the computed shape of every declaration
below.
-/

namespace ExamplesProofFields.Classes

/-! ## Classes -/

/-- One operation and one law: the law is erased, so the dictionary is a **newtype** for
    the operation — an instance is the function itself, with no object around it. -/
class Semi (α : Type) where
  op : α → α → α
  assoc : ∀ a b c : α, op (op a b) c = op a (op b c)

/-- Two operations and a law: a `record` of two fields. -/
class SemiUnit (α : Type) where
  op : α → α → α
  unit : α
  leftUnit : ∀ a : α, op unit a = a

/-- Laws only: the dictionary carries nothing, so it is erased entirely — an instance
    argument of this class is dropped from every signature that takes one. -/
class Lawful (α : Type) [Semi α] where
  comm : ∀ a b : α, Semi.op a b = Semi.op b a

/-! ## Inheritance -/

structure Base where
  n : Nat
  h : 0 < n

/-- A structure extending another: the parent is a field, and here the parent has one
    surviving field, so the parent is itself a newtype — this child is a `record` of the
    parent's `Nat` and its own `Bool`. -/
structure Child extends Base where
  flag : Bool
  hflag : flag = true

/-- Extending a parent that erases away completely.  `OnlyProof` has no surviving field,
    so `ChildOfProof` keeps only `v`: a newtype. -/
structure OnlyProof (cap : Nat) where
  h : 0 < cap

structure ChildOfProof (cap : Nat) extends OnlyProof cap where
  v : Nat

/-! ## `autoParam` and `optParam` fields

An `autoParam` field is an ordinary field whose value the elaborator supplies; what
matters for the shape is only its *type*.  `hle` below is a `Prop`, so it is erased like
any other proof; `step` is a `Nat` with a default, so it survives. -/

structure Range where
  lo : Nat
  hi : Nat
  step : Nat := 1
  hle : lo ≤ hi := by omega

end ExamplesProofFields.Classes
