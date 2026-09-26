module

public import LeanScript.Expr.While
public import Init.Internal.Order.While

@[expose] public section

set_option autoImplicit false

/-!
# The model of a `while` loop agrees with Lean's loop

`while c do body` in the identity monad is `forIn Lean.Loop.mk init f`, with
`f : Unit → β → Id (ForInStep β)`.  Its model in the term language is
`LeanScript.whileIter (fun s => f () s) whileFuel init` (`LeanScript.Expr.While`).

* `LeanScript.loop_forIn_eq_of_whileIter?`: if the loop stops within `n` iterations with
  the state `r`, Lean's loop is `r`.
* `LeanScript.whileIter_eq_of_whileIter?`: then the model run with any fuel `m ≥ n` is `r`
  too.
* `LeanScript.loop_forIn_eq_whileIter`: so whenever the loop stops within `whileFuel`
  iterations, Lean's loop and its model are equal.

A loop that never stops has no computable value in Lean (it is `repeatM`, implemented by a
`partial` function), and no statement is made about it.
-/

namespace LeanScript

variable {β : Type}

/-- If the loop stops within `n` iterations with `r`, the model run with any fuel
    `m ≥ n` stops with `r`. -/
theorem whileIter_eq_of_whileIter? (step : β → ForInStep β) :
    ∀ (n m : Nat) (s r : β), whileIter? step n s = some r → n ≤ m → whileIter step m s = r
  | 0, _, _, _, h, _ => by simp [whileIter?] at h
  | n + 1, 0, _, _, _, hm => by omega
  | n + 1, m + 1, s, r, h, hm => by
      unfold whileIter? at h
      unfold whileIter
      cases hs : step s with
      | done s' => simp only [hs, Option.some.injEq] at h ⊢; exact h
      | yield s' =>
          simp only [hs] at h ⊢
          exact whileIter_eq_of_whileIter? step n m s' r h (by omega)

/-- If the loop stops within `n` iterations with `r`, Lean's loop over `Lean.Loop.mk` —
    what `while`, `repeat` and `repeat … until` elaborate to — is `r`. -/
theorem loop_forIn_eq_of_whileIter? (f : Unit → β → Id (ForInStep β)) :
    ∀ (n : Nat) (s r : β), whileIter? (fun b => (f () b).run) n s = some r →
      (forIn Lean.Loop.mk s f : Id β).run = r
  | 0, _, _, h => by simp [whileIter?] at h
  | n + 1, s, r, h => by
      unfold whileIter? at h
      show (Lean.Loop.forIn Lean.Loop.mk s f).run = r
      rw [Lean.Loop.forIn_eq_of_monadTail]
      cases hs : (f () s).run with
      | done s' =>
          simp only [hs, Option.some.injEq] at h
          simp only [bind, Id.run] at hs ⊢
          rw [hs]; exact h
      | yield s' =>
          simp only [hs] at h
          simp only [bind, Id.run] at hs ⊢
          rw [hs]
          exact loop_forIn_eq_of_whileIter? f n s' r h

/-- **The model of a `while` loop is Lean's loop**, whenever the loop stops within
    `whileFuel = 2 ^ 64` iterations: `forIn Lean.Loop.mk init f` in `Id` equals
    `whileIter (fun s => f () s) whileFuel init`. -/
theorem loop_forIn_eq_whileIter (f : Unit → β → Id (ForInStep β)) (init : β)
    (h : ∃ n, n ≤ whileFuel ∧ (whileIter? (fun b => (f () b).run) n init).isSome) :
    (forIn Lean.Loop.mk init f : Id β).run =
      whileIter (fun b => (f () b).run) whileFuel init := by
  obtain ⟨n, hn, hs⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  rw [loop_forIn_eq_of_whileIter? f n init r hr,
    whileIter_eq_of_whileIter? _ n whileFuel init r hr hn]

end LeanScript

end
