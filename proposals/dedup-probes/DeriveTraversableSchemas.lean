import Mathlib.Tactic.DeriveTraversable
import Mathlib.Control.Traversable.Instances

/-! Probe for proposals/DeduplicationProposal.md, section 1.
Needs Mathlib v4.34.0.  Expected: compiles with no errors.
Stand-in copies of the schema types; the `rfl` examples check that the derived `map`
unfolds to the same terms as the hand-written `map`s. -/

structure NEL (α : Type) where
  head : α
  tail : List α
  deriving DecidableEq, Traversable, LawfulTraversable

structure Rec2 (α : Type) where
  fst : α
  snd : α
  rest : List α
  deriving DecidableEq, Traversable, LawfulTraversable

inductive CWP (α : Type) where
  | here (fields : NEL α) (rest : List (List α))
  | skip (rest : CWP α)
  deriving DecidableEq, Traversable, LawfulTraversable

inductive TU (α : Type) where
  | payloadFirst (fields : NEL α) (next : List α) (rest : List (List α))
  | skip (rest : CWP α)
  deriving DecidableEq, Traversable, LawfulTraversable

inductive Cov (α : Type) where
  | array : α → Cov α
  | thunk : α → Cov α
  deriving Traversable, LawfulTraversable

inductive Fam (α : Type) where
  | ctors (s : TU α)
  | record (s : Rec2 α)
  | alias (b : α)
  deriving Traversable, LawfulTraversable

inductive MRF (α : Type) where
  | selectedThenMore (before : List (Fam α)) (current : Fam α) (next : Fam α) (after : List (Fam α))
  | selectedLast (first : Fam α) (before : List (Fam α)) (current : Fam α)
  deriving Traversable, LawfulTraversable

inductive Prim where | nat | bool deriving DecidableEq
structure Enum where
  n : Nat
  deriving DecidableEq

inductive Shape (α : Type) where
  | prim : Prim → Shape α
  | fn : α → α → Shape α
  | primCovariant : Cov α → Shape α
  | enum : Enum → Shape α
  | record : Rec2 α → Shape α
  | taggedUnion : TU α → Shape α
  deriving Traversable, LawfulTraversable

-- map is structural? check reduction & defeq
example : (Functor.map (· + 1) (TU.payloadFirst ⟨1, [2]⟩ [3] [[4]]) : TU Nat) = TU.payloadFirst ⟨2, [3]⟩ [4] [[5]] := rfl
example (f : Nat → Nat) (a : Nat) (l : List Nat) : (Functor.map f (NEL.mk a l)) = NEL.mk (f a) (l.map f) := rfl
example (f : Nat → Nat) (a b : Nat) (l : List Nat) : (Functor.map f (Rec2.mk a b l)) = Rec2.mk (f a) (f b) (l.map f) := rfl
example (f : Nat → Nat) (c : CWP Nat) : Functor.map f (CWP.skip c) = CWP.skip (Functor.map f c) := rfl
#check @TU.traverse
#print TU.map
example {α β γ : Type} (g : α → β) (h : β → γ) (x : TU α) : (h ∘ g) <$> x = h <$> g <$> x := comp_map g h x
