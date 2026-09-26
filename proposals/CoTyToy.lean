module

/-!
# Toy facts for the final-coalgebra section of `proposals/NominalTyProposal.md`

Self-contained (no imports, not part of the Lake build).  Check it with the bare compiler:

```
lean proposals/CoTyToy.lean
```

What it checks:

* `CoList α`, the final coalgebra of `X ↦ Option (α × X)`, represented without quotients or
  casts as prefix-closed sequences.  `CoList.corec` and `CoList.dest` compute by `rfl`.
* **A final coalgebra loses folds**: no `sum : CoList Nat → Nat` satisfies the two equations
  of `List.sum` (`CoList.no_sum`), because the infinite colist `ones = 1 :: ones` exists.  So
  a Lean `inductive` cannot be given a `ν` meaning without losing structural recursion.
* **`νX. X` is a one-point type** (`IdNu.subsingleton`): the grounding discipline of the
  inductive designs must be replaced, not dropped, under a coinductive meaning.
* **`Unfold` needs no existential for its behaviour**: `Unfold.behaviour u` is a `CoList`
  (the state is gone), it is finite (`Unfold.behaviour_finite`, from the erased `decreasing`
  field), and it is exactly `Unfold.toList u`, computed by `Nat` recursion on `measure seed`
  with no fuel (`Unfold.behaviour_eq_toList`).
-/

@[expose] public section

namespace CoTyToy

/-- Possibly infinite lists: a sequence that, once it stops, stays stopped. -/
def CoList (α : Type) : Type :=
  { f : Nat → Option α // ∀ n, f n = none → f (n + 1) = none }

namespace CoList
variable {α : Type}

def nil : CoList α := ⟨fun _ => none, fun _ _ => rfl⟩

def cons (a : α) (xs : CoList α) : CoList α :=
  ⟨fun | 0 => some a | n + 1 => xs.1 n,
   fun | 0, h => nomatch h | n + 1, h => xs.2 n h⟩

/-- One step of observation. -/
def dest (xs : CoList α) : Option (α × CoList α) :=
  match xs.1 0 with
  | none => none
  | some a => some (a, ⟨fun n => xs.1 (n + 1), fun n h => xs.2 (n + 1) h⟩)

/-- Element `n` of the run of a step function from a state. -/
def run {S : Type} (step : S → Option (S × α)) : Nat → S → Option α
  | 0, s => (step s).map Prod.snd
  | n + 1, s => match step s with
    | none => none
    | some (s', _) => run step n s'

theorem run_stop {S : Type} (step : S → Option (S × α)) :
    ∀ n s, run step n s = none → run step (n + 1) s = none
  | 0, s, h => by
    simp only [run] at h ⊢
    cases hs : step s with
    | none => rfl
    | some p => rw [hs] at h; exact nomatch h
  | n + 1, s, h => by
    simp only [run] at h ⊢
    cases hs : step s with
    | none => rfl
    | some p => rw [hs] at h; exact run_stop step n p.1 h

/-- The final-coalgebra map: the behaviour of a state. -/
def corec {S : Type} (step : S → Option (S × α)) (s : S) : CoList α :=
  ⟨fun n => run step n s, fun n h => run_stop step n s h⟩

/-- The infinite colist of ones. -/
def ones : CoList Nat := corec (fun _ : Unit => some ((), 1)) ()

example : (ones.dest.map Prod.fst) = some 1 := rfl
example : (cons 3 nil).dest.map Prod.fst = some 3 := rfl

theorem ones_eq : ones = cons 1 ones :=
  Subtype.ext (funext fun n => match n with | 0 => rfl | _ + 1 => rfl)

/-- **No fold on the final coalgebra**: `List.sum`'s equations have no solution on colists. -/
theorem no_sum : ¬ ∃ s : CoList Nat → Nat, s nil = 0 ∧ ∀ x xs, s (cons x xs) = x + s xs := by
  intro ⟨s, _, hcons⟩
  have h := hcons 1 ones
  rw [← ones_eq] at h
  omega

end CoList

/-- The final coalgebra of a polynomial functor with a single shape is the type of its infinite
    sequences of shapes.  For `X ↦ X` (one shape, one position) that is `Nat → PUnit`. -/
abbrev IdNu : Type := Nat → PUnit

/-- The coalgebra structure: one step of observation, and the map from any `c : S → S`. -/
def IdNu.dest (x : IdNu) : IdNu := fun n => x (n + 1)
def IdNu.corec {S : Type} (_c : S → S) (_s : S) : IdNu := fun _ => PUnit.unit

/-- **`νX. X` has one point**, so it is unit-like: under a coinductive meaning the grounding
    index cannot simply be dropped. -/
theorem IdNu.subsingleton (x y : IdNu) : x = y := funext fun _ => rfl

/-! ## `Unfold`: the behaviour needs no existential -/

structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

namespace Unfold
variable {α : Type}

/-- What an observer that only steps from the seed can see: a colist, with the state gone. -/
def behaviour (u : Unfold α) : CoList α := CoList.corec u.step u.seed

/-- The behaviour as a list, by `Nat` recursion on a bound: no fuel beyond `measure seed`. -/
def go (u : Unfold α) : Nat → u.State → List α
  | 0, _ => []
  | m + 1, s => match u.step s with
    | none => []
    | some (s', a) => a :: go u m s'

def toList (u : Unfold α) : List α := go u (u.measure u.seed + 1) u.seed

theorem run_none (u : Unfold α) : ∀ n s, u.measure s ≤ n → CoList.run u.step n s = none
  | 0, s, h => by
    simp only [CoList.run]
    cases hs : u.step s with
    | none => rfl
    | some p => have := u.decreasing s p.1 p.2 hs; omega
  | n + 1, s, h => by
    simp only [CoList.run]
    cases hs : u.step s with
    | none => rfl
    | some p =>
      have := u.decreasing s p.1 p.2 hs
      exact run_none u n p.1 (by omega)

/-- The erased `decreasing` field makes every behaviour finite. -/
theorem behaviour_finite (u : Unfold α) : ∃ n, (behaviour u).1 n = none :=
  ⟨u.measure u.seed, run_none u _ _ (Nat.le_refl _)⟩

theorem run_eq_go (u : Unfold α) :
    ∀ m n s, u.measure s < m → CoList.run u.step n s = (go u m s)[n]?
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, n, s, h => by
    cases hs : u.step s with
    | none =>
      cases n with
      | zero => simp [CoList.run, go, hs]
      | succ n => simp [CoList.run, go, hs]
    | some p =>
      have := u.decreasing s p.1 p.2 hs
      cases n with
      | zero => simp [CoList.run, go, hs]
      | succ n =>
        simp only [CoList.run, go, hs, List.getElem?_cons_succ]
        exact run_eq_go u m n p.1 (by omega)

/-- **The behaviour of an `Unfold` is exactly a list**, computed without fuel. -/
theorem behaviour_eq_toList (u : Unfold α) (n : Nat) : (behaviour u).1 n = (toList u)[n]? :=
  run_eq_go u _ n u.seed (Nat.lt_succ_self _)

/-- Countdown from `3`. -/
def countdown : Unfold Nat where
  State := Nat
  seed := 3
  step := fun | 0 => none | k + 1 => some (k, k)
  measure := id
  decreasing := fun x x' a h => by
    cases x with
    | zero => exact nomatch h
    | succ k => cases h; exact Nat.lt_succ_self _

example : toList countdown = [2, 1, 0] := rfl

end Unfold

end CoTyToy
end
