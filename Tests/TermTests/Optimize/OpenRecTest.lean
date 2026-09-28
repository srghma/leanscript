module

public import LeanScript.Term.Optimize.OpenRec
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Open definitions of snapshot functions, and why their fixed point is the function

Two functions of the snapshots defined by well-founded recursion, with the open definition
`leanscript` builds for them (`LeanScriptCli/Frontend.lean`, `openDef`: the right-hand side of
the unfolding equation, the recursive calls made calls of a parameter `rec`), here written by
hand on the uncurried arguments:

* `mc91Loop` (`Tests/SnapshotsMy/TcoMc91.lean`), decreasing along `2 * (111 - n) + 21 * c`;
* `ack` (`Tests/SnapshotsMy/TcoAck.lean`), decreasing lexicographically.

For each: the function satisfies the unfolding equation of its open definition (`…_isFix`),
the open definition calls `rec` only on smaller arguments (`…_respects`), and so **every**
function satisfying that equation is the Lean function (`…_unique`) — the JavaScript, which
runs the open definition with the function itself for `rec`, computes nothing else.
-/

namespace LeanScript.OpenRecTest

open LeanScript.OpenRec

/-! ## McCarthy's 91 loop -/

/-- As in `Tests/SnapshotsMy/TcoMc91.lean`. -/
def mc91Loop : Nat → Nat → Nat
  | 0,     n => n
  | c + 1, n =>
    if n > 100 then
      mc91Loop c (n - 10)
    else
      mc91Loop (c + 1 + 1) (n + 11)
termination_by c n => 2 * (111 - n) + 21 * c
decreasing_by all_goals omega

/-- Its open definition, on the pair of its arguments. -/
def mc91LoopOpen (rec : Nat × Nat → Nat) : Nat × Nat → Nat
  | (0, n) => n
  | (c + 1, n) => if n > 100 then rec (c, n - 10) else rec (c + 1 + 1, n + 11)

/-- The measure of its termination proof. -/
def mc91Measure (p : Nat × Nat) : Nat := 2 * (111 - p.2) + 21 * p.1

theorem mc91Loop_isFix : IsFix mc91LoopOpen (fun p => mc91Loop p.1 p.2) := by
  rintro ⟨c, n⟩
  cases c with
  | zero => simp [mc91LoopOpen, mc91Loop]
  | succ c => simp only [mc91LoopOpen]; rw [mc91Loop.eq_2]

theorem mc91LoopOpen_respects :
    Respects (fun p q => mc91Measure p < mc91Measure q) mc91LoopOpen := by
  rintro f g ⟨c, n⟩ h
  cases c with
  | zero => rfl
  | succ c =>
    simp only [mc91LoopOpen]
    split
    · exact h _ (by simp [mc91Measure]; omega)
    · exact h _ (by simp [mc91Measure]; omega)

/-- Every solution of the unfolding equation of `mc91Loop` is `mc91Loop`. -/
theorem mc91Loop_unique (g : Nat × Nat → Nat) (hg : IsFix mc91LoopOpen g) :
    g = fun p => mc91Loop p.1 p.2 :=
  fix_unique (measure mc91Measure).wf mc91LoopOpen_respects hg mc91Loop_isFix

/-! ## End to end: the translated open definition of `mc91Loop`

The open definition exactly as `leanscript` builds it (curried, the recursive calls through
`rec`), translated by `#leanscript_to_term` as the tool does.  Its `Term` computes the open
definition (`mc91LoopOpenT_run`), and so every fixed point of the translated term — optimised
any number of times — is `mc91Loop` (`mc91LoopOpenT_optimizeN_fix`). -/

/-- `mc91Loop.leanscript_open`. -/
def mc91LoopOpenC (rec : Nat → Nat → Nat) : Nat → Nat → Nat
  | 0,     n => n
  | c + 1, n => if n > 100 then rec c (n - 10) else rec (c + 1 + 1) (n + 11)

def mc91LoopOpenT := #leanscript_to_term mc91LoopOpenC

theorem mc91LoopOpenT_run (rec : Nat → Nat → Nat) (c n : Nat) :
    (mc91LoopOpenT (Δ := DSig.nil)).run rec c n = mc91LoopOpenC rec c n := by
  cases c with
  | zero => rfl
  | succ c =>
    -- the translation: a `nat_rec` on `c` whose step ignores the accumulator, testing the
    -- extern `lean_nat_dec_lt` (checked by the kernel)
    have h : (mc91LoopOpenT (Δ := DSig.nil)).run rec (c + 1) n =
        cond (ExternBool.toBool (Nat.decLt 100 n)) (rec c (n - 10)) (rec (c + 1 + 1) (n + 11)) := by
      kernel_rfl
    rw [h]
    by_cases hn : 100 < n <;> simp [hn, mc91LoopOpenC, ExternBool.toBool] <;> rfl

/-- Every fixed point of the translated open definition of `mc91Loop`, optimised `k` times,
    is `mc91Loop`. -/
theorem mc91LoopOpenT_optimizeN_fix (k : Nat) (g : Nat → Nat → Nat)
    (hg : ∀ c n, g c n = ((mc91LoopOpenT (Δ := DSig.nil)).optimizeN k).run g c n) :
    g = mc91Loop := by
  have hfix : IsFix mc91LoopOpen (fun p => g p.1 p.2) := by
    rintro ⟨c, n⟩
    show g c n = _
    rw [hg c n, Term.optimizeN_run, mc91LoopOpenT_run]
    cases c <;> rfl
  have := mc91Loop_unique _ hfix
  funext c n
  exact congrFun this (c, n)

/-! ## Ackermann's function -/

/-- As in `Tests/SnapshotsMy/TcoAck.lean`. -/
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

/-- Its open definition, on the pair of its arguments (the nested call too goes through
    `rec`). -/
def ackOpen (rec : Nat × Nat → Nat) : Nat × Nat → Nat
  | (0, n) => n + 1
  | (m + 1, 0) => rec (m, 1)
  | (m + 1, n + 1) => rec (m, rec (m + 1, n))

theorem ack_isFix : IsFix ackOpen (fun p => ack p.1 p.2) := by
  rintro ⟨m, n⟩
  cases m with
  | zero => simp [ackOpen, ack]
  | succ m =>
    cases n with
    | zero => simp [ackOpen, ack]
    | succ n => simp [ackOpen, ack]

/-- `ackOpen` calls `rec` only on smaller pairs of the lexicographic order of the termination
    proof of `ack`. -/
theorem ackOpen_respects : Respects (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).rel ackOpen := by
  rintro f g ⟨m, n⟩ h
  cases m with
  | zero => rfl
  | succ m =>
    cases n with
    | zero => exact h _ (Prod.Lex.left _ _ (Nat.lt_succ_self m))
    | succ n =>
      simp only [ackOpen]
      rw [h (m + 1, n) (Prod.Lex.right _ (Nat.lt_succ_self n))]
      exact h _ (Prod.Lex.left _ _ (Nat.lt_succ_self m))

/-- Every solution of the unfolding equation of `ack` is `ack`. -/
theorem ack_unique (g : Nat × Nat → Nat) (hg : IsFix ackOpen g) : g = fun p => ack p.1 p.2 :=
  fix_unique (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf ackOpen_respects hg ack_isFix

/-! ## A case analysis read as a recursion -/

/-- `match c with | 0 => z | k + 1 => s k` read as a `nat_rec` whose step ignores the
    accumulator: the JavaScript `if` computes the same thing. -/
example (z : Nat) (s : Nat → Nat) (n : Nat) :
    natIter z (fun k _ => s k) n = if 0 < n then s (n - 1) else z :=
  natIter_of_ignoresAcc' z (fun k _ => s k) (fun _ _ _ => rfl) n

end LeanScript.OpenRecTest

end
