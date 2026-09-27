/-
# A recursive function whose argument is a proof-carrying enum

The question: `Status` is three constructors carrying nothing but proofs, so the backend
sees an `enum` — two numbers in the type language and a tag at run time.  If a recursive
Lean function takes such a value, what is left to make it terminate?

This file is the smallest specimen that makes the issue bite.  `Step n` is a
proof-carrying enum of three constructors:

* `stop`  — only for `n = 0`;
* `half`  — only for `0 < n`;
* `boom`  — whose two proof fields contradict each other, so **`boom` has no values at
  all**, yet after erasure it is a perfectly ordinary third tag.

`run` halves `n` in the `half` branch and *loops on the spot* in the `boom` branch.  Lean
accepts it, because `decreasing_by` discharges the `boom` obligation from the
contradictory proofs — this is `SnapshotsPBOPure/Tco07.lean`'s `boom`, moved from a
precondition argument into the constructor of the data.

Erasure now makes a difference that matters: the erased twin can be *called with tag 2*,
which Lean's `run` can never be, and then it diverges.  `runErased` shows that (no answer
at any fuel), and `runRanked` — the shape the grammar gives it, a single loop whose
counter is initialised to the `termination_by` measure and decremented once per
iteration — shows the repair:

* `runRanked_agrees`: started with a counter at least the measure, the ranked loop
  returns exactly what Lean's `run` returns.  Nothing a real caller can do is refused or
  altered.
* `runRanked_bad_tag`: on the tag no Lean value has, it stops at the counter and answers
  something.  It cannot hang.

So the answer to "how can it terminate, if the proofs are gone?" is: termination never
rested on the proofs in the first place.  It rests on the measure, which is an expression
over runtime data (`n`), and the grammar turns that expression into a counter.  The
proofs decide which runtime values are *reachable*, and reachability is exactly what the
grammar is allowed to be pessimistic about.
-/

namespace ExamplesProofFields

/-! ## The data: a proof-carrying enum, one of whose constructors is empty -/

inductive Step (n : Nat) where
  /-- `n` is finished. -/
  | stop (h : n = 0)
  /-- `n` can be halved. -/
  | half (h : 0 < n)
  /-- Nothing satisfies both proofs, so this constructor has no values — but it does
      have a tag. -/
  | boom (h1 : n = 0) (h2 : 0 < n)

/-- The classifier a caller uses: for every `n` there is exactly one sensible `Step n`,
    and it is never `boom`. -/
def Step.of (n : Nat) : Step n :=
  if h : n = 0 then .stop h else .half (Nat.pos_of_ne_zero h)

theorem Step.no_boom {n : Nat} (s : Step n) : ∀ h1 h2, s ≠ .boom h1 h2 := by
  intro h1 h2 _
  omega

/-! ## The Lean function: it terminates, and one of its branches is a bare self-loop -/

def run (n : Nat) (s : Step n) : Nat :=
  match s with
  | .stop _ => 0
  | .half _ => 1 + run (n / 2) (Step.of (n / 2))
  | .boom h1 h2 => 1 + run n (.boom h1 h2)
termination_by n
decreasing_by
  · omega
  · omega

example : run 8 (Step.of 8) = 4 := by native_decide
example : run 0 (Step.of 0) = 0 := by native_decide
example : run 1 (Step.of 1) = 1 := by native_decide

/-! ## The erased twin: the same bodies with the proof fields deleted

The tag is now an ordinary number, so `tag = 2` is a callable input.  A step counter
stands in for "does this terminate?": `none` means it had not answered yet. -/

def runErased (fuel n tag : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match tag with
    | 0 => some 0
    | 1 => (runErased fuel (n / 2) (if n / 2 = 0 then 0 else 1)).map (1 + ·)
    | _ => (runErased fuel n 2).map (1 + ·)

/-- On the tags a Lean value can have, the erased twin answers, and answers the same. -/
example : runErased 100 8 1 = some 4 := by native_decide
example : runErased 100 0 0 = some 0 := by native_decide

/-- On the tag no Lean value has, it does not answer — at any fuel. -/
example : runErased 100 8 2 = none := by native_decide
example : runErased 5000 8 2 = none := by native_decide

/-! ## The ranked loop: what the grammar makes of it

One loop; its counter is initialised, at entry, to the `termination_by` measure (`n`),
computed from the runtime arguments; each iteration is allowed to jump back only with the
predecessor of the counter, which is not a value the body can name.  When the counter is
exhausted the loop answers the canonical inhabitant of the result type. -/

def runRanked : (rank n tag : Nat) → Nat
  | 0, _, _ => 0
  | rank + 1, n, tag =>
    match tag with
    | 0 => 0
    | 1 => 1 + runRanked rank (n / 2) (if n / 2 = 0 then 0 else 1)
    | _ => 1 + runRanked rank n 2

/-- The tag `Step.of n` erases to. -/
def tagOf (n : Nat) : Nat := if n = 0 then 0 else 1

/-- **The loop is faithful.**  Started with a counter at least the measure — which is
    what the loop's entry does, since it initialises the counter *to* the measure — the
    ranked loop returns exactly what Lean's `run` returns.  No reachable call is cut
    short. -/
theorem runRanked_agrees : ∀ (rank n : Nat), n ≤ rank → runRanked rank n (tagOf n) = run n (Step.of n) := by
  intro rank
  induction rank with
  | zero =>
      intro n hn
      have : n = 0 := Nat.le_zero.mp hn
      subst this
      simp [runRanked, run, Step.of]
  | succ rank ih =>
      intro n hn
      by_cases h : n = 0
      · subst h
        simp [runRanked, run, Step.of, tagOf]
      · have hpos : 0 < n := Nat.pos_of_ne_zero h
        have hhalf : n / 2 < n := Nat.div_lt_self hpos (by omega)
        have hle : n / 2 ≤ rank := by omega
        have hrun : run n (Step.of n) = 1 + run (n / 2) (Step.of (n / 2)) := by
          simp [run, Step.of, h]
        simp only [tagOf, h, ite_false, runRanked, hrun]
        exact congrArg (1 + ·) (ih (n / 2) hle)

/-- **The loop cannot hang.**  On the tag that no Lean value has — the one the erased
    twin diverges on — the ranked loop stops at the counter and answers.  The answer is
    not Lean's (Lean has no answer here, because it has no such input); the point is that
    there is one. -/
theorem runRanked_bad_tag : ∀ (rank n : Nat), runRanked rank n 2 = rank := by
  intro rank
  induction rank with
  | zero => intro n; rfl
  | succ rank ih => intro n; simp only [runRanked, ih n]; omega

/-! ## What this says about the schemas

`Step`'s three constructors carry five proof fields between them and no data.  Recording
those fields in `LeanEnumSchema` would change nothing above: the measure is `n`, a
*function argument*, and `n` survives erasure because it is a `Nat`, not because it is
mentioned by a proof.  A schema that also carried `h : 0 < n` could not be used to
compute anything — by `ExamplesProofFields.measure_indep_of_proof`, every function of a
proof is constant — so the loop's counter would be the same counter.

What the proofs do buy Lean is the *elimination of the `boom` branch*, and the grammar
buys the same outcome differently: it keeps the branch and bounds it. -/

end ExamplesProofFields
