module

public import TermTests.Datatypes.RoseVariantsTest

@[expose] public section

set_option autoImplicit false

namespace RoseVariantsTest
open LeanScript

/-!
# Proofs about the translation of `RoseF`

`TermTests/Datatypes/RoseVariantsTest.lean` checks the translation of the rose tree
`RoseF := node (m : Nat) (Fin m → RoseF)` on sample values.  Its children are read as a
function `Nat → Option RoseF` (`some` below `m`, `none` from `m` on).  This file proves, for
**every** input:

* the encoding of a Lean `RoseF` in the language (`roseFEnc`, built with the generated
  constructors of `RoseF` and `Option RoseF`) **loses nothing**: two trees with the same value
  in the language are equal (`roseFEnc_injective`);
* the translated `RoseF.fan n` builds `roseFEnc (RoseF.fan n)` (`roseFFanT_correct`);
* the translated `RoseF.size` returns `RoseF.size` on every tree (`roseFSizeT_correct`).
-/

/-- The generated member `Option RoseF` of `RoseF`'s block. -/
abbrev OptTy : Ty Prog.ks := .data (.there (.there (.there (.there (.here 0)))))

/-- `some x` in the member `Option RoseF`. -/
def someEnc (x : Ty.Den Prog.Δ Prog.roseF) : Ty.Den Prog.Δ OptTy :=
  ((#leanscript_get_ctor Option.some (α := RoseF)) (.neu (.var (.head (by decide)))) :
    PExpr Prog.Δ [] [⟨Prog.roseF, .many, 0⟩] OptTy (some 0)).eval PUnit.unit (x)

/-- `none` in the member `Option RoseF`. -/
def noneEnc : Ty.Den Prog.Δ OptTy :=
  ((#leanscript_get_ctor Option.none (α := RoseF)) : PExpr Prog.Δ [] [] OptTy none).run

/-- `RoseF.node m g` in the language, for a number of children `m` and children `g`. -/
def nodeEnc (m : Nat) (g : Nat → Ty.Den Prog.Δ OptTy) : Ty.Den Prog.Δ Prog.roseF :=
  ((#leanscript_get_ctor RoseF.node) (.neu (.var (.head (by decide)))) (.neu (.var (.tail (.head (by decide))))) :
    PExpr Prog.Δ [] [⟨.nat, .many, 0⟩, ⟨.fn .nat OptTy, .many, 0⟩] Prog.roseF (some 0)).eval PUnit.unit (m, g)

/-- The value of the language a Lean `RoseF` translates to: the child at `j` is `some` of the
    encoding of `f ⟨j, _⟩` below `m`, and `none` from `m` on. -/
def roseFEnc : RoseF → Ty.Den Prog.Δ Prog.roseF
  | .node m f => nodeEnc m (fun j => if h : j < m then someEnc (roseFEnc (f ⟨j, h⟩)) else noneEnc)

/-- One layer out of a value of `Option RoseF`. -/
def optOut (c : Ty.Den Prog.Δ OptTy) := Prog.Δ.dataOut BRef.here.there.there.there.there 0 c
/-- One layer out of a value of `RoseF`. -/
def roseFOut (c : Ty.Den Prog.Δ Prog.roseF) := Prog.Δ.dataOut BRef.here.there.there.there.there 1 c

theorem optOut_some (x : Ty.Den Prog.Δ Prog.roseF) : optOut (someEnc x) = some x :=
  DSig.dataOut_dataIn _ _ _ _
theorem roseFOut_node (m : Nat) (g : Nat → Ty.Den Prog.Δ OptTy) :
    roseFOut (nodeEnc m g) = (m, g) :=
  DSig.dataOut_dataIn _ _ _ _

theorem someEnc_injective {x y : Ty.Den Prog.Δ Prog.roseF} (h : someEnc x = someEnc y) :
    x = y := by
  have h' := congrArg optOut h
  rw [optOut_some, optOut_some] at h'
  exact Option.some.inj h'

/-- **Reading `Fin m → RoseF` as `Nat → Option RoseF` loses nothing**: two trees with the
    same value in the language are equal. -/
theorem roseFEnc_injective (r s : RoseF) (h : roseFEnc r = roseFEnc s) : r = s := by
  induction r generalizing s with
  | node m f ih =>
    cases s with
    | node m' f' =>
      have h' := congrArg roseFOut h
      rw [roseFEnc, roseFEnc, roseFOut_node, roseFOut_node] at h'
      obtain ⟨rfl, hg⟩ := Prod.mk.inj h'
      have hf : f = f' := by
        funext i
        have := congrFun hg i.val
        simp only [i.isLt, dite_true] at this
        exact ih i _ (someEnc_injective this)
      rw [hf]

/-! ## The translation of `RoseF.fan` builds the encoding, for every `n` -/

/-- The value the translated `RoseF.fan n` computes, as the translator writes it: the child at
    `v` is tested with `decide (v < n)`. -/
theorem roseFFanT_run' (n : Nat) : roseFFanT.run n =
    nodeEnc n (fun v => bif decide (v < n) then someEnc (nodeEnc 0 fun _ => noneEnc) else noneEnc) := by
  kernel_rfl

/-- **`RoseF.fan` is translated correctly**: for every `n`, the translated program builds the
    encoding of `RoseF.fan n`. -/
theorem roseFFanT_correct (n : Nat) : roseFFanT.run n = roseFEnc (RoseF.fan n) := by
  rw [roseFFanT_run']
  simp only [roseFEnc, RoseF.fan]
  congr 1
  funext v
  by_cases h : v < n <;> simp [h]

/-! ## `RoseF.size` is translated correctly, for every tree -/

/-- A value of `nat` is a `Nat`. -/
def natOf {ks : List Nat} {Δ : DSig ks} (x : Ty.Den Δ .nat) : Nat := x

/-- A value of `Option nat` is an `Option Nat`. -/
def optOf {ks : List Nat} {Δ : DSig ks} (x : Ty.Den Δ (Ty.option .nat)) : Option Nat := x

/-- The block of `RoseF` (and `Option RoseF`). -/
abbrev FR : BRef Prog.ks := BRef.here.there.there.there.there

/-- The answer types of the translated `RoseF.size`: `Option Nat` at `Option RoseF`, `Nat` at
    `RoseF`. -/
def ρF : Fin ((Prog.Δ.block FR).k + 1) → Ty Prog.ks
  | ⟨0, _⟩ => Ty.option .nat
  | ⟨1, _⟩ => .nat

/-- The fold of `RoseF`'s block with the answer types `ρF`, whose branches see the value `W`
    of the enclosing `fun`. -/
noncomputable def foldF (brs : Ty.Den Prog.Δ Prog.roseF → (i : Fin ((Prog.Δ.block FR).k + 1)) →
      Ty.Den Prog.Δ ((Prog.Δ.block FR).recBody ρF i) → Ty.Den Prog.Δ (ρF i))
    (W : Ty.Den Prog.Δ Prog.roseF) (j : Fin ((Prog.Δ.block FR).k + 1))
    (c : Ty.Den Prog.Δ (.data ((Prog.Δ.block FR).ref j))) : Ty.Den Prog.Δ (ρF j) :=
  Prog.Δ.dataRec FR ρF (brs W) j c

/-- The translated `RoseF.size` is a fold, with one step per member: at `RoseF`, a
    `nat_rec` on the number of children adding the answers at them (the addition is the join
    point after the case analysis of the answer, so it is in both branches); at `Option RoseF`, `none`
    or `some` of the answer at the `RoseF` inside. -/
theorem size_facts : ∃ brs, (∀ c, roseFSizeT.run c = foldF brs c 1 c) ∧
    (∀ W m g, natOf (foldF brs W 1 (nodeEnc m g)) =
      natIter 1 (fun k acc => match optOf (foldF brs W 0 (g k)) with
        | none => acc + 0
        | some v => acc + v) m) ∧
    (∀ W x, optOf (foldF brs W 0 (someEnc x)) = some (natOf (foldF brs W 1 x))) ∧
    (∀ W, optOf (foldF brs W 0 noneEnc) = none) := by
  refine ⟨?brs, fun c => ?run, ?_, ?_, ?_⟩
  case run => exact rfl
  · intro W m g
    unfold natOf optOf foldF
    refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
    kernel_rfl
  · intro W x
    unfold natOf optOf foldF
    refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
    kernel_rfl
  · intro W
    unfold optOf foldF
    refine (DSig.dataRec_dataIn _ _ _ _ _ _).trans ?_
    kernel_rfl


/-- `nat_rec` adding `H k` is `Fin.foldl` adding `H i`. -/
theorem natIter_add_eq_finFoldl (H : Nat → Nat) (z : Nat) (n : Nat) :
    natIter z (fun k acc => acc + H k) n = Fin.foldl n (fun acc i => acc + H i.val) z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← ih]
    rfl

/-- **`RoseF.size` is translated correctly**: on every tree, the translated program returns
    the number of its nodes. -/
theorem roseFSizeT_correct (r : RoseF) : natOf (roseFSizeT.run (roseFEnc r)) = r.size := by
  obtain ⟨brs, hrun, hnode, hsome, hnone⟩ := size_facts
  have key : ∀ W, natOf (foldF brs W 1 (roseFEnc r)) = r.size := by
    intro W
    induction r with
    | node m f ih =>
      rw [roseFEnc, hnode]
      let H : Nat → Nat := fun k => if h : k < m then (f ⟨k, h⟩).size else 0
      have hH : (fun k acc => match optOf (foldF brs W 0
          ((fun j => if h : j < m then someEnc (roseFEnc (f ⟨j, h⟩)) else noneEnc) k)) with
            | none => acc + 0
            | some v => acc + v) =
          (fun k acc => acc + H k) := by
        funext k acc
        by_cases h : k < m
        · simp only [h, dite_true, hsome, H, ← ih]
        · simp only [h, dite_false, hnone, H]
      rw [hH, natIter_add_eq_finFoldl, RoseF.size]
      congr 1
      funext acc i
      simp only [H, i.isLt, dite_true]
  exact (congrArg natOf (hrun (roseFEnc r))).trans (key _)

end RoseVariantsTest

end
