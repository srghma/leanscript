module

public import LeanScript.DenFacts

@[expose] public section

set_option autoImplicit false

/-!
# Course-of-values recursion over a block: `DSig.dataBrec`

`DSig.dataRec` hands the branch of member `j` the body of `j` in which every hole is the pair
of the subvalue and the answer at it: the answers **one** level down.  A course-of-values
recursion (what Lean compiles a structural recursion to, through `brecOn`) may also look at
the answers further down: `fib (n + 2) = fib n + fib (n + 1)` reads two levels.

`DSig.dataBrec b ρ k` is the fold that hands the branch the answers `k + 1` levels down.  The
information about a subvalue of member `i` that a branch sees is its *window* of depth `d`
(`DSig.Block.win ρ d i`), a closed type:

* depth `0`: the pair of the subvalue and the answer at it (what `dataRec` hands over);
* depth `d + 1`: the subvalue, the answer at it, and its own body in which every hole is the
  window of depth `d` of the sub-subvalue.

The branch of member `j` binds `j`'s body with every hole filled by the window of depth `k`
(`DSig.Block.brecBody ρ k j`), so `k = 0` is `dataRec`.  `dataBrec` is one `IW.fold` whose
answer at a value is the value's own window of depth `k`; the window of a node is built from
the windows of its children, cut down by one level (`DSig.Block.winTrunc`).  Everything is
structural and computes by `rfl`; there is no fuel and no cast.
-/

namespace LeanScript

namespace DSig.Block
variable {ks : List Nat} {Δ : DSig ks} (B : Δ.Block)

/-- The window of depth `d` of a subvalue of member `i`, for a fold with answer types `ρ`. -/
def win (ρ : Fin (B.k + 1) → Ty ks) : Nat → Fin (B.k + 1) → Ty ks
  | 0, i => Ty.pair (.data (B.ref i)) (ρ i)
  | d + 1, i => .record (.data (B.ref i)) (.cons (ρ i) (.one (B.inst (win ρ d) i)))

/-- The body of member `j` for a course-of-values fold of depth `k`: every hole is the
    window of depth `k` of the subvalue. -/
abbrev brecBody (ρ : Fin (B.k + 1) → Ty ks) (k : Nat) (j : Fin (B.k + 1)) : Ty ks :=
  B.inst (B.win ρ k) j

/-- A body of member `j` whose holes are rewritten one by one: the structural action of the
    body on the values in its holes. -/
def mapInst {σ σ' : Fin (B.k + 1) → Ty ks}
    (f : (i : Fin (B.k + 1)) → Ty.Den Δ (σ i) → Ty.Den Δ (σ' i)) (j : Fin (B.k + 1))
    (x : Ty.Den Δ (B.inst σ j)) : Ty.Den Δ (B.inst σ' j) :=
  Mems.unrollMember B.old (DSig.refDen Δ) σ' B.bs j.val (Fin.zero_add_lt' j)
    ((Mems.rollMember B.old (DSig.refDen Δ) σ B.bs j.val (Fin.zero_add_lt' j) x).map f)

variable {B}

/-- The answer at a subvalue, read off its window. -/
def winAnswer {ρ : Fin (B.k + 1) → Ty ks} : (d : Nat) → (i : Fin (B.k + 1)) →
    Ty.Den Δ (B.win ρ d i) → Ty.Den Δ (ρ i)
  | 0, _, w => w.2
  | _ + 1, _, w => w.2.1

/-- The subvalue, read off its window. -/
def winValue {ρ : Fin (B.k + 1) → Ty ks} : (d : Nat) → (i : Fin (B.k + 1)) →
    Ty.Den Δ (B.win ρ d i) → Ty.Den Δ (.data (B.ref i))
  | 0, _, w => w.1
  | _ + 1, _, w => w.1

/-- A window cut down by one level. -/
def winTrunc {ρ : Fin (B.k + 1) → Ty ks} : (d : Nat) → (i : Fin (B.k + 1)) →
    Ty.Den Δ (B.win ρ (d + 1) i) → Ty.Den Δ (B.win ρ d i)
  | 0, _, w => (w.1, w.2.1)
  | d + 1, i, w => (w.1, w.2.1, B.mapInst (winTrunc d) i w.2.2)

/-- The window of depth `k` of a node, from the node, the answer at it and its body in which
    every hole is the pair of the child and the child's window of depth `k`. -/
def mkWin {ρ : Fin (B.k + 1) → Ty ks} : (k : Nat) → (i : Fin (B.k + 1)) →
    Ty.Den Δ (.data (B.ref i)) → Ty.Den Δ (ρ i) →
    Ty.Den Δ (B.inst (fun i' => Ty.pair (.data (B.ref i')) (B.win ρ k i')) i) →
    Ty.Den Δ (B.win ρ k i)
  | 0, _, v, a, _ => (v, a)
  | d + 1, i, v, a, full =>
      (v, a, B.mapInst (σ := fun i' => Ty.pair (.data (B.ref i')) (B.win ρ (d + 1) i'))
        (σ' := B.win ρ d) (fun i' p => winTrunc d i' p.2) i full)

theorem winAnswer_mkWin {ρ : Fin (B.k + 1) → Ty ks} (k : Nat) (i : Fin (B.k + 1))
    (v : Ty.Den Δ (.data (B.ref i))) (a : Ty.Den Δ (ρ i))
    (full : Ty.Den Δ (B.inst (fun i' => Ty.pair (.data (B.ref i')) (B.win ρ k i')) i)) :
    winAnswer k i (mkWin k i v a full) = a := by
  cases k <;> rfl

end DSig.Block

section DataBrec
variable {ks : List Nat} (Δ : DSig ks)

/-- The window of depth `k` of every value of a block, by one fold: a node's window is built
    from its children's windows (cut down by one level) and the branch's answer, which sees
    the children's full windows. -/
def DSig.dataWin (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
    (branch : (j : Fin ((Δ.block b).k + 1)) → Ty.Den Δ ((Δ.block b).brecBody ρ k j) →
      Ty.Den Δ (ρ j))
    (j : Fin ((Δ.block b).k + 1)) (v : Ty.Den Δ (.data ((Δ.block b).ref j))) :
    Ty.Den Δ ((Δ.block b).win ρ k j) :=
  let B := Δ.block b
  IW.fold (C := fun i => Ty.Den Δ (B.win ρ k i))
    (fun i x =>
      let full : Ty.Den Δ (B.inst (fun i' => Ty.pair (.data (B.ref i')) (B.win ρ k i')) i) :=
        Mems.unrollMember B.old (DSig.refDen Δ)
          (fun i' => Ty.pair (.data (B.ref i')) (B.win ρ k i')) B.bs i.val (Fin.zero_add_lt' i)
          (x.map (fun i' y => (B.ofIW i' y.1, y.2)))
      let a := branch i (B.mapInst (σ := fun i' => Ty.pair (.data (B.ref i')) (B.win ρ k i'))
        (σ' := B.win ρ k) (fun _ p => p.2) i full)
      let v : Ty.Den Δ (.data (B.ref i)) := B.ofIW i (IW.mk i x.1 (fun p => (x.2 p).1))
      DSig.Block.mkWin k i v a full)
    (B.toIW j v)

/-- Course-of-values recursion over block `b`, looking `k + 1` levels down: the branch of
    member `j` gets `j`'s body with every hole filled by the window of depth `k` of the
    subvalue.  At `k = 0` it is `DSig.dataRec`. -/
def DSig.dataBrec (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
    (branch : (j : Fin ((Δ.block b).k + 1)) → Ty.Den Δ ((Δ.block b).brecBody ρ k j) →
      Ty.Den Δ (ρ j))
    (j : Fin ((Δ.block b).k + 1)) (v : Ty.Den Δ (.data ((Δ.block b).ref j))) : Ty.Den Δ (ρ j) :=
  DSig.Block.winAnswer k j (Δ.dataWin b ρ k branch j v)

/-- **The computation rule of course-of-values recursion**: on a value built by `dataIn`, the
    fold is the branch applied to the body in which every child is replaced by its window
    of depth `k`. -/
theorem DSig.dataBrec_dataIn (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
    (branch : (j : Fin ((Δ.block b).k + 1)) → Ty.Den Δ ((Δ.block b).brecBody ρ k j) →
      Ty.Den Δ (ρ j))
    (j : Fin ((Δ.block b).k + 1)) (x : Ty.Den Δ ((Δ.block b).unfold j)) :
    Δ.dataBrec b ρ k branch j (Δ.dataIn b j x) =
      branch j ((Δ.block b).mapInst (fun i c => Δ.dataWin b ρ k branch i c) j x) := by
  simp only [DSig.dataBrec, DSig.dataWin, DSig.dataIn]
  rw [DSig.Block.toIW_ofIW]
  simp only [IW.fold]
  refine (DSig.Block.winAnswer_mkWin _ _ _ _ _).trans ?_
  congr 1
  unfold DSig.Block.mapInst
  rw [Mems.rollMember_unrollMember]
  rfl

end DataBrec

end LeanScript

end
