module

public import TermTests.QuotientTest

@[expose] public section

set_option autoImplicit false

/-!
# Proofs about the translation of quotients and proof-carrying data

`TermTests/QuotientTest.lean` checks the translation of `QT` (a datatype with a quotient
field) and `Pos` (a structure with a proof field) on sample values.  A quotient is read as its
carrier, so a value of `QT` in the language holds one *representative* of each class.  This
file proves, for **every** input:

* the relation `Represents c t` (the value `c` of the language holds representatives of the
  classes of `t`) relates the value the translator builds for the sample `q3` to `q3`
  (`q3T_represents`);
* **every `QT` has a value in the language** (`exists_represents`): reading the quotient as
  its carrier loses no value of `QT`;
* the translated `QT.odds` returns `QT.odds` on **every representative** of every `QT`
  (`oddsT_correct`), so its answer does not depend on the representatives chosen
  (`oddsT_rep_independent`);
* the translated `Pos.pred` and `Pos.succ` compute `Pos.pred` and `Pos.succ` on the number
  a `Pos` is erased to (`predT_correct`, `succT_correct`).
-/

namespace QuotientTest
open LeanScript

/-- A natural number of the language is a `Nat`. -/
def natOf {ks : List Nat} {Δ : DSig ks} (x : Ty.Den Δ .nat) : Nat := x

/-- `QT.leaf` in the language. -/
def leafEnc : Ty.Den Prog.Δ Prog.qt := (Prog.QT.leaf (Γ := [])).run

/-- `QT.node` in the language, with the representative `n` of the class of its first field. -/
def nodeEnc (n : Nat) (c : Ty.Den Prog.Δ Prog.qt) : Ty.Den Prog.Δ Prog.qt :=
  (Prog.QT.node (Γ := [.nat, Prog.qt]) (.var .head) (.var (.tail .head))).eval (n, c)

/-- `Represents c t`: the value `c` of the language is `t` with each class given by one of
    its representatives. -/
inductive Represents : Ty.Den Prog.Δ Prog.qt → QT → Prop where
  | leaf : Represents leafEnc .leaf
  | node (n : Nat) {c : Ty.Den Prog.Δ Prog.qt} {t : QT} :
      Represents c t → Represents (nodeEnc n c) (.node (Quot.mk _ n) t)

/-- The translator builds, for the sample `q3`, a value that represents it. -/
theorem q3T_represents : Represents q3T.run q3 :=
  .node 3 (.node 4 .leaf)

/-- **Every `QT` has a value in the language**: each class has a representative. -/
theorem exists_represents (t : QT) : ∃ c, Represents c t := by
  induction t with
  | leaf => exact ⟨_, .leaf⟩
  | node q t ih =>
    obtain ⟨c, hc⟩ := ih
    induction q using Quot.ind with
    | mk n => exact ⟨_, .node n hc⟩

/-- The block of `QT` in `Prog`. -/
abbrev QB := Prog.Δ.block BRef.here

/-- A fold over `QT` whose branch sees the value `W` of the enclosing `fun`. -/
def foldQT {τ : Ty Prog.ks}
    (brs : (i : Fin (QB.k + 1)) → Term Prog.Δ (QB.recBody (fun _ => τ) i :: [Prog.qt]) τ [])
    (W c : Ty.Den Prog.Δ Prog.qt) : Ty.Den Prog.Δ τ :=
  Prog.Δ.dataRec BRef.here (fun _ => τ) (fun i x => (brs i).eval (x, W) ()) 0 c

/-- The translated `QT.odds` is a fold, with one step per constructor; the step of `node`
    adds the parity of the representative. -/
theorem odds_facts :
    ∃ brs : (i : Fin (QB.k + 1)) → Term Prog.Δ (QB.recBody (fun _ => .nat) i :: [Prog.qt]) .nat [],
    (∀ c, oddsT.run c = foldQT brs c c) ∧
    (∀ W n c, natOf (foldQT brs W (nodeEnc n c)) = n % 2 + natOf (foldQT brs W c)) ∧
    (∀ W, natOf (foldQT brs W leafEnc) = 0) := by
  refine ⟨_, fun c => rfl, ?_, fun W => ?_⟩
  · intro W n c
    unfold natOf foldQT
    refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
    rfl
  · unfold natOf foldQT
    refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
    rfl

/-- **`QT.odds` is translated correctly**: on every value of the language that represents a
    `QT`, whichever representatives it holds, the translated program returns `QT.odds`. -/
theorem oddsT_correct {c : Ty.Den Prog.Δ Prog.qt} {t : QT} (h : Represents c t) :
    natOf (oddsT.run c) = t.odds := by
  obtain ⟨brs, hrun, hnode, hleaf⟩ := odds_facts
  have key : ∀ W {c : Ty.Den Prog.Δ Prog.qt} {t : QT}, Represents c t →
      natOf (foldQT brs W c) = t.odds := by
    intro W c t h
    induction h with
    | leaf => exact hleaf W
    | node n _ ih => rw [hnode, ih]; rfl
  exact (congrArg natOf (hrun _)).trans (key _ h)

/-- The answer of the translated `QT.odds` does not depend on the representatives. -/
theorem oddsT_rep_independent {c c' : Ty.Den Prog.Δ Prog.qt} {t : QT} (h : Represents c t)
    (h' : Represents c' t) : natOf (oddsT.run c) = natOf (oddsT.run c') :=
  (oddsT_correct h).trans (oddsT_correct h').symm

/-! ## `Pos`: the proof is erased -/

/-- **`Pos.pred` is translated correctly**: on the number of every `Pos`. -/
theorem predT_correct (p : Pos) : natOf ((predT (Δ := Prog.Δ)).run p.n) = p.pred := rfl

/-- **`Pos.succ` is translated correctly**: it returns the number of `Pos.succ n`. -/
theorem succT_correct (n : Nat) : natOf ((succT (Δ := Prog.Δ)).run n) = (Pos.succ n).n := rfl

end QuotientTest
