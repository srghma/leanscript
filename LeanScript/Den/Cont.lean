module

@[expose] public section

set_option autoImplicit false

namespace LeanScript

/-!
# Containers and their W-trees

What `LeanScript.Ty.Den` needs to give a **recursive** tagged union its values: the least
fixpoint of the functor the union's payload describes.  Every former of a payload is a
*container* — a type of shapes and, for each shape, a type of holes where an occurrence
of the binder sits — and the least fixpoint of a container is its **W-type**, a tree
whose nodes are shapes and whose children are indexed by the holes.

Nothing here is specific to the language; the names avoid Mathlib's `WType`.
-/

/-- A container: a type of shapes and, for each shape, the type of its holes. -/
structure Cont where
  /-- The shapes. -/
  S : Type
  /-- The holes of a shape. -/
  P : S → Type

/-- The W-type of a container: a node is a shape, with one subtree per hole. -/
inductive WTree (S : Type) (P : S → Type) : Type
  | mk (s : S) (f : P s → WTree S P)

/-- A constant: every value is a shape, and no shape has a hole. -/
@[reducible] def Cont.const (A : Type) : Cont := ⟨A, fun _ => PEmpty⟩

/-- A product: a shape of each, and the holes of both. -/
@[reducible] def Cont.prod (c d : Cont) : Cont := ⟨c.S × d.S, fun p => c.P p.1 ⊕ d.P p.2⟩

/-- A sum over `I`: an index and a shape of that summand, with its holes. -/
@[reducible] def Cont.sigma (I : Type) (c : I → Cont) : Cont :=
  ⟨(i : I) × (c i).S, fun p => (c p.1).P p.2⟩

/-- An exponent: a function from `A` to shapes; a hole is an argument and a hole of the
    shape at it. -/
@[reducible] def Cont.pi (A : Type) (c : Cont) : Cont :=
  ⟨A → c.S, fun f => (a : A) × c.P (f a)⟩

/-- The holes of a list of shapes: the holes of each element, in order. -/
@[reducible] def ListPos {S : Type} (P : S → Type) : List S → Type
  | [] => PEmpty
  | s :: ss => P s ⊕ ListPos P ss

/-- A list: a list of shapes, with the holes of each. -/
@[reducible] def Cont.list (c : Cont) : Cont := ⟨List c.S, ListPos c.P⟩

/-- The least fixpoint, which has no holes left: it is closed. -/
@[reducible] def Cont.mu (c : Cont) : Cont := Cont.const (WTree c.S c.P)

/-- The extension of a container at `X`: a shape, and a value of `X` in each hole. -/
@[reducible] def Cont.Ext (c : Cont) (X : Type) : Type := (s : c.S) × (c.P s → X)

namespace Cont.Ext

/-- Pair two extensions. -/
def pair {c d : Cont} {Y : Type} (x : c.Ext Y) (y : d.Ext Y) : (Cont.prod c d).Ext Y :=
  ⟨(x.1, y.1), fun | .inl p => x.2 p | .inr q => y.2 q⟩

/-- The first component of an extension of a product. -/
def fst {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) : c.Ext Y := ⟨x.1.1, fun p => x.2 (.inl p)⟩

/-- The second component of an extension of a product. -/
def snd {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) : d.Ext Y := ⟨x.1.2, fun p => x.2 (.inr p)⟩

/-- Put an extension in front of an extension of a list. -/
def consExt {c : Cont} {Y : Type} (h : c.Ext Y) (t : (Cont.list c).Ext Y) :
    (Cont.list c).Ext Y :=
  ⟨h.1 :: t.1, fun | .inl p => h.2 p | .inr q => t.2 q⟩

/-- A list of extensions, from a list of values and a way to turn each into one. -/
def list {c : Cont} {Y : Type} {α : Type} (f : α → c.Ext Y) : List α → (Cont.list c).Ext Y
  | [] => ⟨[], fun p => PEmpty.elim p⟩
  | x :: xs => consExt (f x) (list f xs)

/-- The other direction of `Cont.Ext.list`. -/
def unlist {c : Cont} {Y : Type} {α : Type} (h : c.Ext Y → α) : (xs : List c.S) → (ListPos c.P xs → Y) → List α
  | [], _ => []
  | s :: ss, g => h ⟨s, fun p => g (.inl p)⟩ :: unlist h ss (fun q => g (.inr q))

/-- An extension of an exponent, pointwise. -/
def pi {c : Cont} {Y : Type} {A : Type} (g : A → c.Ext Y) : (Cont.pi A c).Ext Y :=
  ⟨fun y => (g y).1, fun q => (g q.1).2 q.2⟩

theorem pair_fst_snd {c d : Cont} {Y : Type} (x : (Cont.prod c d).Ext Y) : Cont.Ext.pair x.fst x.snd = x := by
  obtain ⟨⟨s, t⟩, f⟩ := x
  exact congrArg (Sigma.mk (s, t)) (funext fun | .inl _ => rfl | .inr _ => rfl)

theorem const_eta {Y : Type} {A : Type} (s : A) (f : (Cont.const A).P s → Y) :
    (⟨s, fun p => PEmpty.elim p⟩ : (Cont.const A).Ext Y) = ⟨s, f⟩ :=
  congrArg (Sigma.mk s) (funext fun p => PEmpty.elim p)

theorem unlist_list {c : Cont} {Y : Type} {α : Type} (f : α → c.Ext Y) (h : c.Ext Y → α)
    (hr : ∀ x, h (f x) = x) : ∀ xs : List α,
    Cont.Ext.unlist h (Cont.Ext.list f xs).1 (Cont.Ext.list f xs).2 = xs
  | [] => rfl
  | x :: xs => by
      show h ⟨(f x).1, fun p => (f x).2 p⟩ :: _ = x :: xs
      rw [List.cons.injEq]
      exact ⟨hr x, unlist_list f h hr xs⟩

theorem list_unlist {c : Cont} {Y : Type} {α : Type} (f : α → c.Ext Y) (h : c.Ext Y → α)
    (hr : ∀ e, f (h e) = e) : ∀ (ss : List c.S) (g : ListPos c.P ss → Y),
    Cont.Ext.list f (Cont.Ext.unlist h ss g) = ⟨ss, g⟩
  | [], g => congrArg (Sigma.mk []) (funext fun p => PEmpty.elim p)
  | s :: ss, g => by
      have ih := list_unlist f h hr ss (fun q => g (.inr q))
      have hx := hr ⟨s, fun p => g (.inl p)⟩
      show (⟨_, _⟩ : (Cont.list c).Ext Y) = _
      generalize f (h ⟨s, fun p => g (.inl p)⟩) = A at hx ⊢
      generalize Cont.Ext.list f (Cont.Ext.unlist h ss fun q => g (.inr q)) = B at ih ⊢
      subst hx ih
      exact congrArg (Sigma.mk (s :: ss)) (funext fun | .inl _ => rfl | .inr _ => rfl)

end Cont.Ext

/-! ## Folding a W-tree, remembering every answer

A depth-`k` fold looks at the answers of the fold at subtrees up to `k` levels down.
Rather than recomputing them, the fold stores its answer at every node: `WTree.memo`
turns a tree into the same tree with the answer at each node beside its shape, bottom-up,
so a branch that looks further down reads answers that are already there. -/

/-- A tree with the fold's answer stored at every node. -/
abbrev Memo (S : Type) (P : S → Type) (β : Type) := WTree (S × β) (fun p => P p.1)

/-- The answer stored at the root. -/
def Memo.answer {S : Type} {P : S → Type} {β : Type} : Memo S P β → β
  | .mk (_, b) _ => b

/-- The tree with the answer at every node: first the children's memos, then the answer
    at this node, from its shape and its children's memos (which hold every answer
    below it). -/
def WTree.memo {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) : WTree S P → Memo S P β
  | .mk s f =>
      let kids := fun p => WTree.memo step (f p)
      .mk (s, step s kids) kids

/-- The answer of the memoised fold at the root. -/
def WTree.memoFold {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (v : WTree S P) : β :=
  (WTree.memo step v).answer

/-- The plain fold of a W-tree: the answer at a node from its shape, its subtrees and the
    answers at them. -/
def WTree.fold {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → WTree S P) → (P s → β) → β) : WTree S P → β
  | .mk s f => step s f (fun p => WTree.fold step (f p))

/-- Forgetting the answers of a memo gives back the tree. -/
def Memo.tree {S : Type} {P : S → Type} {β : Type} : Memo S P β → WTree S P
  | .mk (s, _) f => .mk s (fun p => Memo.tree (f p))

theorem WTree.memo_mk {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (s : S) (f : P s → WTree S P) :
    WTree.memo step (.mk s f) =
      .mk (s, step s (fun p => WTree.memo step (f p))) (fun p => WTree.memo step (f p)) :=
  rfl

theorem WTree.memoFold_mk {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) (s : S) (f : P s → WTree S P) :
    WTree.memoFold step (.mk s f) = step s (fun p => WTree.memo step (f p)) :=
  rfl

/-- The memo of a tree is that tree, with answers. -/
theorem WTree.memo_tree {S : Type} {P : S → Type} {β : Type}
    (step : (s : S) → (P s → Memo S P β) → β) : ∀ v : WTree S P,
    (WTree.memo step v).tree = v
  | .mk s f => by
      show WTree.mk s (fun p => (WTree.memo step (f p)).tree) = _
      exact congrArg (WTree.mk s) (funext fun p => WTree.memo_tree step (f p))

end LeanScript

end
