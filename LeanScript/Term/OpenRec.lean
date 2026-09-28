module

public import LeanScript.Term.Optimize

@[expose] public section

set_option autoImplicit false

/-!
# Recursive functions as fixed points of open definitions

`leanscript` translates a function `f` defined by well-founded recursion (or a member of a
`mutual` block) through its *open definition*: the right-hand side of its unfolding equation,
with every recursive call made a call of a new parameter `f_rec`.  That gives a functional
`F : (α → β) → α → β`, translated to a `Term`, and `f` is its fixed point, `f = F f` (the
unfolding equation).  The JavaScript runs `f` by passing `f` itself for `f_rec`.

This file states why that is a faithful reading:

* `OpenRec.fix_unique`: when the recursive calls of `F` are all on smaller arguments of a
  well-founded relation (`OpenRec.Respects`, which is what Lean's termination proof
  establishes), `F` has **at most one** fixed point.  So a function that satisfies the
  unfolding equation is `f`; in particular the translation cannot pick another solution.
* `OpenRec.fix_exists`, `OpenRec.fix_isFix`: such an `F` has a fixed point, built with
  `WellFounded.fix` (for a type of answers with a value).
* `Term.optimizeN_isFix_iff`, `Term.optimizeN_fix_eq`: the optimiser, run on the translated
  open definition, keeps the functional it denotes, so the optimised term has exactly the same
  fixed points, and its fixed point is `f` again.
* `natIter_of_ignoresAcc`: a `Comp.nat_rec` whose step ignores the accumulator (how the
  translation reads a case analysis `0` / `k + 1`) is the value of its last step on the
  initial value: `natIter z s (k + 1) = s k z`.  This is the `if (0n < n) { const i = n - 1n;
  … }` the JavaScript prints instead of a loop.
-/

namespace LeanScript

namespace OpenRec

variable {α β : Type}

/-- `F` makes its recursive calls only on arguments smaller for `r`: the answer of `F f` at
    `x` depends only on the values of `f` below `x`. -/
def Respects (r : α → α → Prop) (F : (α → β) → α → β) : Prop :=
  ∀ (f g : α → β) (x : α), (∀ y, r y x → f y = g y) → F f x = F g x

/-- `f` is a fixed point of `F`: it satisfies the unfolding equation `f x = F f x`. -/
def IsFix (F : (α → β) → α → β) (f : α → β) : Prop :=
  ∀ x, f x = F f x

/-- **Uniqueness.**  A functional whose recursive calls go down a well-founded relation has at
    most one fixed point. -/
theorem fix_unique {r : α → α → Prop} (wf : WellFounded r) {F : (α → β) → α → β}
    (hF : Respects r F) {f g : α → β} (hf : IsFix F f) (hg : IsFix F g) : f = g := by
  funext x
  induction x using wf.induction with
  | h x ih => rw [hf x, hg x]; exact hF f g x ih

/-- The fixed point, by well-founded recursion: at `x`, `F` applied to the values already
    computed below `x` (and anything elsewhere, which `F` does not look at). -/
noncomputable def fix {r : α → α → Prop} (wf : WellFounded r) [Nonempty β]
    (F : (α → β) → α → β) : α → β :=
  wf.fix fun x rec => F (fun y => open Classical in
    if h : r y x then rec y h else Classical.choice inferInstance) x

/-- The function built by `fix` satisfies the unfolding equation. -/
theorem fix_isFix {r : α → α → Prop} (wf : WellFounded r) [Nonempty β]
    {F : (α → β) → α → β} (hF : Respects r F) : IsFix F (fix wf F) := by
  intro x
  unfold fix
  rw [WellFounded.fix_eq]
  apply hF
  intro y hy
  simp only [hy, dite_true]

/-- **Existence.**  Such a functional has a fixed point. -/
theorem fix_exists {r : α → α → Prop} (wf : WellFounded r) [Nonempty β]
    {F : (α → β) → α → β} (hF : Respects r F) : ∃ f, IsFix F f :=
  ⟨fix wf F, fix_isFix wf hF⟩

/-- So the fixed point is **the** function whose unfolding equation `F` is. -/
theorem eq_fix_of_isFix {r : α → α → Prop} (wf : WellFounded r) [Nonempty β]
    {F : (α → β) → α → β} (hF : Respects r F) {f : α → β} (hf : IsFix F f) : f = fix wf F :=
  fix_unique wf hF hf (fix_isFix wf hF)

end OpenRec

/-! ## The optimiser keeps the fixed points of a translated open definition -/

section
variable {ks : List Nat} {Δ : DSig ks}

/-- The functional a closed program of type `(σ → τ) → σ → τ` denotes. -/
abbrev Term.functional {σ τ : Ty ks} {o : Lvl}
    (t : Term Δ 0 [] [] (.fn (.fn σ τ) (.fn σ τ)) [] o) :
    (Ty.Den Δ σ → Ty.Den Δ τ) → Ty.Den Δ σ → Ty.Den Δ τ :=
  t.run

/-- The optimised open definition denotes the same functional. -/
theorem Term.optimizeN_functional {σ τ : Ty ks} {o : Lvl} (k : Nat)
    (t : Term Δ 0 [] [] (.fn (.fn σ τ) (.fn σ τ)) [] o) :
    (t.optimizeN k).functional = t.functional :=
  Term.optimizeN_run k t

/-- The optimised open definition has exactly the fixed points of the translated one. -/
theorem Term.optimizeN_isFix_iff {σ τ : Ty ks} {o : Lvl} (k : Nat)
    (t : Term Δ 0 [] [] (.fn (.fn σ τ) (.fn σ τ)) [] o) (f : Ty.Den Δ σ → Ty.Den Δ τ) :
    OpenRec.IsFix (t.optimizeN k).functional f ↔ OpenRec.IsFix t.functional f := by
  rw [Term.optimizeN_functional]

/-- **The optimised open definition runs the same function.**  If the translated open
    definition `t` makes its recursive calls on smaller arguments of a well-founded relation,
    and `f` satisfies its unfolding equation, then any fixed point of the *optimised* term is
    `f`. -/
theorem Term.optimizeN_fix_eq {σ τ : Ty ks} {o : Lvl} (k : Nat)
    (t : Term Δ 0 [] [] (.fn (.fn σ τ) (.fn σ τ)) [] o)
    {r : Ty.Den Δ σ → Ty.Den Δ σ → Prop} (wf : WellFounded r)
    (hF : OpenRec.Respects r t.functional) {f g : Ty.Den Δ σ → Ty.Den Δ τ}
    (hf : OpenRec.IsFix t.functional f) (hg : OpenRec.IsFix (t.optimizeN k).functional g) :
    g = f :=
  OpenRec.fix_unique wf hF ((Term.optimizeN_isFix_iff k t g).mp hg) hf

end

/-! ## A recursion on `Nat` whose step ignores the accumulator is a case analysis -/

/-- A step that does not look at the accumulator. -/
def IgnoresAcc {α : Type} (s : Nat → α → α) : Prop :=
  ∀ k a b, s k a = s k b

/-- `natIter` with a step that ignores the accumulator is the last step, on anything (the
    initial value, as the JavaScript does): `natIter z s 0 = z`, `natIter z s (k + 1) = s k z`. -/
theorem natIter_of_ignoresAcc {α : Type} (z : α) (s : Nat → α → α) (hs : IgnoresAcc s) :
    (n : Nat) → natIter z s n = (match n with | 0 => z | k + 1 => s k z)
  | 0 => rfl
  | k + 1 => hs k _ _

/-- The same, in the form the JavaScript prints: `if (0 < n) { i = n - 1; step } else z`. -/
theorem natIter_of_ignoresAcc' {α : Type} (z : α) (s : Nat → α → α) (hs : IgnoresAcc s)
    (n : Nat) : natIter z s n = if 0 < n then s (n - 1) z else z := by
  rw [natIter_of_ignoresAcc z s hs n]
  cases n with
  | zero => rfl
  | succ k => simp

end LeanScript

end
