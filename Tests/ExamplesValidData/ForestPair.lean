/-
`Tco04`, but the argument is data rather than a number.

Two mutually recursive functions over a *mutual* inductive (`Node` / `Forest`, a
forest being an inductive list of nodes).  Neither function recurses on a
syntactic sub-term, so Lean uses well-founded recursion with the measure
`xs.len`, and neither function terminates for every input:

* the "shrink" branches drop one resp. two elements from the front, and
  `Forest.tail Forest.nil = Forest.nil`, so a run that misses its base case
  spins on the empty forest for ever — exactly the way `Tco04`'s `n - 1`
  walks off into the negative integers;
* the "grow" branch of `test1` *prepends* an element, which diverges outright,
  and is ruled out only by the data part of the precondition.

The preconditions therefore carry two very different kinds of fact:

* an arithmetic one on the *length* (`len % 3`), which is what makes the base
  case reachable — the direct analogue of `Tco04`'s `n % 3`;
* a *structural* one on the elements (`Forest.marked`: every node's second
  field is `2`), which is what kills the divergent branch — the analogue of
  `Tco07`'s `Safe`.

This file is a specimen of data whose validity is structural; it is not part of
the snapshot corpus and nothing is compiled to JavaScript from it.
-/

namespace ExamplesValidData

/-! ## The data: a mutual inductive, with an inductive list inside it -/

mutual

/-- A node: a label, a flag (the "second field" of the question), and children. -/
inductive Node where
  | node (label : Nat) (flag : Nat) (kids : Forest) : Node
  deriving Repr

/-- A forest: an inductive list of `Node`s, mutually inductive with `Node`. -/
inductive Forest where
  | nil : Forest
  | cons (hd : Node) (tl : Forest) : Forest
  deriving Repr

end

/-- Number of top-level elements. -/
def Forest.len : Forest → Nat
  | .nil => 0
  | .cons _ t => t.len + 1

/-- Drop the first element (and stay put on the empty forest — the source of
    divergence). -/
def Forest.tail : Forest → Forest
  | .nil => .nil
  | .cons _ t => t

/-- The flag of the first element, `0` if there is none. -/
def Forest.headFlag : Forest → Nat
  | .nil => 0
  | .cons (.node _ f _) _ => f

/-- Every top-level node carries flag `2`. A `Prop`-valued structural recursion. -/
def Forest.marked : Forest → Prop
  | .nil => True
  | .cons (.node _ f _) t => f = 2 ∧ t.marked

/-! ## The preconditions -/

/-- Callable domain of `test1`: non-empty, length ≢ 2 (mod 3), all nodes marked. -/
def Valid1 (xs : Forest) : Prop :=
  xs.len ≥ 1 ∧ (xs.len % 3 = 0 ∨ xs.len % 3 = 1) ∧ xs.marked

/-- Callable domain of `test2`: at least two elements, length ≢ 1 (mod 3), all nodes marked. -/
def Valid2 (xs : Forest) : Prop :=
  xs.len ≥ 2 ∧ (xs.len % 3 = 0 ∨ xs.len % 3 = 2) ∧ xs.marked

/-! ## Facts about the two steps -/

theorem Forest.len_tail (xs : Forest) : xs.tail.len = xs.len - 1 := by
  cases xs with
  | nil => rfl
  | cons h t => simp [Forest.tail, Forest.len]

theorem Forest.marked_tail {xs : Forest} (h : xs.marked) : xs.tail.marked := by
  cases xs with
  | nil => exact h
  | cons hd t =>
    cases hd with
    | node _ _ _ => exact h.2

/-- On a non-empty marked forest the head flag is `2`: this is what makes
    `test1`'s growing branch dead code. -/
theorem Forest.headFlag_of_marked {xs : Forest} (hlen : xs.len ≥ 1) (h : xs.marked) :
    xs.headFlag = 2 := by
  cases xs with
  | nil => simp [Forest.len] at hlen
  | cons hd t =>
    cases hd with
    | node _ _ _ => exact h.1

theorem test1_step {xs : Forest} (h : Valid1 xs) (h1 : xs.len ≠ 1) : Valid2 xs.tail := by
  obtain ⟨hne, hmod, hm⟩ := h
  refine ⟨?_, ?_, Forest.marked_tail hm⟩ <;> rw [Forest.len_tail] <;> omega

theorem test2_step {xs : Forest} (h : Valid2 xs) (h2 : xs.len ≠ 2) : Valid1 xs.tail.tail := by
  obtain ⟨hne, hmod, hm⟩ := h
  refine ⟨?_, ?_, Forest.marked_tail (Forest.marked_tail hm)⟩ <;>
    rw [Forest.len_tail, Forest.len_tail] <;> omega

/-! ## The pair -/

mutual

/-- Terminates only on `Valid1` inputs: the `len % 3` part makes the base case
    reachable, the `marked` part makes the growing branch unreachable. -/
def test1 (xs : Forest) (h : Valid1 xs) : Nat :=
  if h1 : xs.len = 1 then
    1
  else if hf : xs.headFlag = 2 then
    test2 xs.tail (test1_step h h1)
  else
    -- dead code: `h` says the forest is marked and non-empty, so `hf` is absurd
    test1 (.cons (.node 0 0 .nil) xs)
      (absurd (Forest.headFlag_of_marked h.1 h.2.2) hf)
termination_by xs.len
decreasing_by
  · rw [Forest.len_tail]
    have := h.1
    omega
  · exact absurd (Forest.headFlag_of_marked h.1 h.2.2) hf

/-- Terminates only on `Valid2` inputs. -/
def test2 (xs : Forest) (h : Valid2 xs) : Nat :=
  if h2 : xs.len = 2 then
    2
  else
    test1 xs.tail.tail (test2_step h h2)
termination_by xs.len
decreasing_by
  rw [Forest.len_tail, Forest.len_tail]
  have := h.1
  omega

end

/-! ## A concrete input -/

/-- A marked forest of length 4 (`4 % 3 = 1`, so `Valid1` holds). -/
def sample4 : Forest :=
  .cons (.node 0 2 .nil)
    (.cons (.node 1 2 (.cons (.node 10 2 .nil) .nil))
      (.cons (.node 2 2 .nil)
        (.cons (.node 3 2 .nil) .nil)))

theorem sample4_valid1 : Valid1 sample4 := by
  refine ⟨by decide, by decide, ?_⟩
  simp [sample4, Forest.marked]

/-- A forest of length 4 whose third node is unmarked: `Valid1` fails. -/
def sample4bad : Forest :=
  .cons (.node 0 2 .nil)
    (.cons (.node 1 2 .nil)
      (.cons (.node 2 7 .nil)
        (.cons (.node 3 2 .nil) .nil)))

theorem sample4bad_not_valid1 : ¬ Valid1 sample4bad := by
  intro h
  have := h.2.2
  simp [sample4bad, Forest.marked] at this

/-- A forest of length 5 (`5 % 3 = 2`): `Valid1` fails on the arithmetic side. -/
def sample5 : Forest :=
  .cons (.node 0 2 .nil) sample4

theorem sample5_not_valid1 : ¬ Valid1 sample5 := by
  intro h
  have := h.2.1
  simp [sample5, sample4, Forest.len] at this

/-! ## Running it -/

/-- `sample4` (length 4) → `test2` (length 3) → `test1` (length 1) → `1`. -/
theorem test1_sample4 : test1 sample4 sample4_valid1 = 1 := by
  simp [test1, test2, sample4, Forest.len, Forest.tail, Forest.headFlag]

-- The same answer by evaluation (the proof argument is erased at run time):
--   #eval test1 sample4 sample4_valid1   -- 1

/-! Calls outside the domain do not elaborate — they fail at the *proof* argument,
before anything runs:

```lean
#check test1 sample5 (by
  refine ⟨by decide, by decide, ?_⟩
  simp [sample5, sample4, Forest.marked])
-- error: Tactic `decide` proved that the proposition
--   sample5.len % 3 = 0 ∨ sample5.len % 3 = 1
-- is false

#check test1 sample4bad (by
  refine ⟨by decide, by decide, ?_⟩
  simp [sample4bad, Forest.marked])
-- error: unsolved goals ⊢ False
```
-/

/-! ## A decidable version of the precondition, and a checked entry point -/

/-- `Forest.marked` as a `Bool`-valued structural recursion. -/
def Forest.markedB : Forest → Bool
  | .nil => true
  | .cons (.node _ f _) t => f == 2 && t.markedB

theorem Forest.marked_iff_markedB : ∀ xs : Forest, xs.marked ↔ xs.markedB = true
  | .nil => by simp [Forest.marked, Forest.markedB]
  | .cons (.node _ _ _) t => by
      simp [Forest.marked, Forest.markedB, Forest.marked_iff_markedB t]

/-- `Valid1` as a `Bool`-valued test on the data. -/
def Valid1B (xs : Forest) : Bool :=
  1 ≤ xs.len && (xs.len % 3 == 0 || xs.len % 3 == 1) && xs.markedB

theorem valid1_of_valid1B {xs : Forest} (h : Valid1B xs = true) : Valid1 xs := by
  simp [Valid1B] at h
  exact ⟨h.1.1, by omega, (Forest.marked_iff_markedB xs).2 h.2⟩

/-- The run-time-checked entry point: `none` outside the domain, and the real answer
    inside it.  Everything here — the test, the dispatch and `test1` itself — is
    ordinary compiled code. -/
def test1Checked (xs : Forest) : Option Nat :=
  if h : Valid1B xs = true then some (test1 xs (valid1_of_valid1B h)) else none

/-- A length-4 forest whose *first* node is unmarked.  `test1` would take the growing
    branch on it, and the growing branch prepends an unmarked node, so the erased
    function runs for ever. -/
def sampleBadHead : Forest :=
  .cons (.node 0 7 .nil)
    (.cons (.node 1 2 .nil)
      (.cons (.node 2 2 .nil)
        (.cons (.node 3 2 .nil) .nil)))

/-! ## The erased twin: what the compiled code would do without the precondition

`test1Fuel`/`test2Fuel` are `test1`/`test2` with the proof argument deleted — i.e. what
survives erasure — run under a fuel counter so that the divergent cases can be observed
instead of hanging.  `none` means "had not finished within the fuel". -/

mutual

def test1Fuel : Nat → Forest → Option Nat
  | 0, _ => none
  | fuel + 1, xs =>
    if xs.len = 1 then some 1
    else if xs.headFlag = 2 then test2Fuel fuel xs.tail
    else test1Fuel fuel (.cons (.node 0 0 .nil) xs)

def test2Fuel : Nat → Forest → Option Nat
  | 0, _ => none
  | fuel + 1, xs =>
    if xs.len = 2 then some 2
    else test1Fuel fuel xs.tail.tail

end

/-- Inside the domain, the erased twin agrees with `test1`. -/
theorem test1Fuel_sample4 : test1Fuel 1000 sample4 = some 1 := by native_decide

/-- Outside the domain it may still stop — the precondition is not a termination test,
    it is what makes termination *provable*. -/
theorem test1Fuel_sample5 : test1Fuel 1000 sample5 = some 1 := by native_decide

/-- And it may run for ever: the growing branch keeps prepending unmarked nodes. -/
theorem test1Fuel_sampleBadHead : test1Fuel 1000 sampleBadHead = none := by native_decide
theorem test1Fuel_sampleBadHead' : test1Fuel 5000 sampleBadHead = none := by native_decide

theorem test1Checked_sample4 : test1Checked sample4 = some 1 := by native_decide
theorem test1Checked_sample5 : test1Checked sample5 = none := by native_decide
theorem test1Checked_sample4bad : test1Checked sample4bad = none := by native_decide
theorem test1Checked_sampleBadHead : test1Checked sampleBadHead = none := by native_decide

end ExamplesValidData
