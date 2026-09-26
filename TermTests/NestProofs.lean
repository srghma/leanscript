module

public import TermTests.NestTest

@[expose] public section

set_option autoImplicit false

/-!
# Proofs about the translation of `Nest`

`TermTests/NestTest.lean` checks the translation of the type-indexed family `Nest` on sample
values.  This file proves, for **every** input:

* the encoding of a Lean `Nest α` into the declared datatype (`nestEnc`, built with the
  generated constructors `Prog.Nest.cons`, `Prog.Elem.node`, …) is the one the translator
  uses (`n3T_run`, `m2T_run`);
* **erasing the index loses nothing**: two values of `Nest Nat` with the same value in the
  language are equal (`nestEnc_injective`); more generally, at every index, when the elements
  are put in `Nest.Elem Nat` injectively (`nestEnc_injective_at`);
* the translated `Nest.length` returns `Nest.length` on every value, at every index
  (`lengthT_correct`, `lengthT_correct_at`).
-/

namespace NestTest
open LeanScript

/-- The element type `Nest.Elem Nat`, an older block of `Prog`. -/
abbrev ElemTy : Ty Prog.ks := .data (.there (.here 0))

/-- `Nest.Elem.leaf a` in the language. -/
def leafEnc (a : Nat) : Ty.Den Prog.Δ ElemTy :=
  (Prog.Elem.leaf (Γ := [.nat]) (.var .head)).eval (a, ())

/-- `Nest.Elem.node x y` in the language. -/
def nodeEnc (x y : Ty.Den Prog.Δ ElemTy) : Ty.Den Prog.Δ ElemTy :=
  (Prog.Elem.node (Γ := [ElemTy, ElemTy]) (.var .head) (.var (.tail .head))).eval (x, y, ())

/-- `Nest.cons x c` in the language. -/
def consEnc (x : Ty.Den Prog.Δ ElemTy) (c : Ty.Den Prog.Δ Prog.nest) : Ty.Den Prog.Δ Prog.nest :=
  (Prog.Nest.cons (Γ := [ElemTy, Prog.nest]) (.var .head) (.var (.tail .head))).eval (x, c, ())

/-- `Nest.nil` in the language. -/
def nilEnc : Ty.Den Prog.Δ Prog.nest := (Prog.Nest.nil (Γ := [])).run

/-- The value of the datatype `Nest Nat` a Lean `Nest α` translates to, when its elements (of
    the index `α`) are put in `Nest.Elem Nat` by `f`: the elements one level down, pairs, are
    put there by `node`. -/
def nestEnc : {α : Type} → (α → Ty.Den Prog.Δ ElemTy) → Nest α → Ty.Den Prog.Δ Prog.nest
  | _, _, .nil => nilEnc
  | _, f, .cons a r => consEnc (f a) (nestEnc (fun p => nodeEnc (f p.1) (f p.2)) r)

/-- The encodings agree with the values the translator builds for the samples of the tests. -/
theorem n3T_run : n3T.run = nestEnc leafEnc n3 := rfl
theorem m2T_run : m2T.run = nestEnc (fun p => nodeEnc (leafEnc p.1) (leafEnc p.2)) m2 := rfl

/-! ## Erasing the index loses nothing -/

/-- One layer out of a value of `Nest.Elem Nat`. -/
def elemOut (c : Ty.Den Prog.Δ ElemTy) :=
  Prog.Δ.dataOut BRef.here.there 0 c

/-- One layer out of a value of `Nest Nat`. -/
def nestOut (c : Ty.Den Prog.Δ Prog.nest) :=
  Prog.Δ.dataOut BRef.here 0 c

theorem elemOut_leaf (a : Nat) : elemOut (leafEnc a) = Sum.inl a :=
  DSig.dataOut_dataIn _ _ _ _

theorem elemOut_node (x y : Ty.Den Prog.Δ ElemTy) : elemOut (nodeEnc x y) = Sum.inr (x, y) :=
  DSig.dataOut_dataIn _ _ _ _

theorem leafEnc_injective : Function.Injective leafEnc := by
  intro a b h
  have h' := congrArg elemOut h
  rw [elemOut_leaf, elemOut_leaf] at h'
  exact Sum.inl.inj h'

theorem nodeEnc_injective {x y x' y' : Ty.Den Prog.Δ ElemTy} (h : nodeEnc x y = nodeEnc x' y') :
    x = x' ∧ y = y' := by
  have h' := congrArg elemOut h
  rw [elemOut_node, elemOut_node] at h'
  have h2 := Sum.inr.inj h'
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

theorem nestOut_nil : nestOut nilEnc = none := DSig.dataOut_dataIn _ _ _ _

theorem nestOut_cons (x : Ty.Den Prog.Δ ElemTy) (c : Ty.Den Prog.Δ Prog.nest) :
    nestOut (consEnc x c) = some (x, c) := DSig.dataOut_dataIn _ _ _ _

/-- **Erasing the index loses nothing**, at every index: when the elements are put in
    `Nest.Elem Nat` injectively, two values with the same value in the language are equal. -/
theorem nestEnc_injective_at {α : Type} (f : α → Ty.Den Prog.Δ ElemTy) (hf : Function.Injective f)
    (n m : Nest α) (h : nestEnc f n = nestEnc f m) : n = m := by
  induction n with
  | nil =>
    cases m with
    | nil => rfl
    | cons b m =>
      have h' := congrArg nestOut h
      rw [nestEnc, nestEnc, nestOut_nil, nestOut_cons] at h'
      cases h'
  | cons a r ih =>
    cases m with
    | nil =>
      have h' := congrArg nestOut h
      rw [nestEnc, nestEnc, nestOut_nil, nestOut_cons] at h'
      cases h'
    | cons b s =>
      have h' := congrArg nestOut h
      rw [nestEnc, nestEnc, nestOut_cons, nestOut_cons] at h'
      have h2 := Option.some.inj h'
      have hab : a = b := hf (congrArg Prod.fst h2)
      have hg : Function.Injective (fun p : _ × _ => nodeEnc (f p.1) (f p.2)) := by
        intro p q hpq
        obtain ⟨h1, h2⟩ := nodeEnc_injective hpq
        exact Prod.ext (hf h1) (hf h2)
      rw [hab, ih _ hg s (congrArg Prod.snd h2)]

/-- **Erasing the index of `Nest Nat` loses nothing**: two values with the same value in the
    language are the same `Nest Nat`. -/
theorem nestEnc_injective : Function.Injective (nestEnc leafEnc : Nest Nat → _) :=
  fun n m h => nestEnc_injective_at leafEnc leafEnc_injective n m h

/-! ## `Nest.length` is translated correctly -/

/-- A natural number of the language is a `Nat`. -/
def natOf {ks : List Nat} {Δ : DSig ks} (x : Ty.Den Δ .nat) : Nat := x

/-- The block of `Nest Nat` in `Prog`. -/
abbrev NB := Prog.Δ.block BRef.here

/-- A fold over `Nest Nat` whose branch sees the value `W` of the enclosing `fun`. -/
def foldNest {τ : Ty Prog.ks}
    (brs : (i : Fin (NB.k + 1)) → Term Prog.Δ (NB.recBody (fun _ => τ) i :: [Prog.nest]) τ)
    (W c : Ty.Den Prog.Δ Prog.nest) : Ty.Den Prog.Δ τ :=
  Prog.Δ.dataRec BRef.here (fun _ => τ) (fun i x => (brs i).eval (x, W, ())) 0 c

/-- The translated `Nest.length` is a fold, with one step per constructor. -/
theorem length_facts :
    ∃ brs : (i : Fin (NB.k + 1)) → Term Prog.Δ (NB.recBody (fun _ => .nat) i :: [Prog.nest]) .nat,
    (∀ c, lengthT.run c = foldNest brs c c) ∧
    (∀ W x c, natOf (foldNest brs W (consEnc x c)) = 1 + natOf (foldNest brs W c)) ∧
    (∀ W, natOf (foldNest brs W nilEnc) = 0) := by
  refine ⟨_, fun c => rfl, ?_, fun W => rfl⟩
  intro W x c
  unfold natOf foldNest
  refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
  rfl

/-- **`Nest.length` is translated correctly**, at every index: on the value of every
    `Nest α`, the translated program returns its length. -/
theorem lengthT_correct_at {α : Type} (f : α → Ty.Den Prog.Δ ElemTy) (n : Nest α) :
    natOf (lengthT.run (nestEnc f n)) = n.length := by
  obtain ⟨brs, hrun, hcons, hnil⟩ := length_facts
  have key : ∀ W {β : Type} (g : β → Ty.Den Prog.Δ ElemTy) (n : Nest β),
      natOf (foldNest brs W (nestEnc g n)) = n.length := by
    intro W β g n
    induction n with
    | nil => exact hnil W
    | cons a r ih => simp only [nestEnc, hcons, ih, Nest.length]
  exact (congrArg natOf (hrun _)).trans (key _ f n)

/-- **`Nest.length` is translated correctly** on every `Nest Nat`. -/
theorem lengthT_correct (n : Nest Nat) : natOf (lengthT.run (nestEnc leafEnc n)) = n.length :=
  lengthT_correct_at leafEnc n

end NestTest
