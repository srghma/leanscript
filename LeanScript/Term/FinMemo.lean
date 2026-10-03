module

@[expose] public section

set_option autoImplicit false

/-!
# Functions of a position, their values computed once

The branches of an enum's case analysis and of a fold are functions of the position of the
branch (`Fin n → …`).  A walk that rebuilds them as a closure (`fun i => (bs i).walk`)
computes the branch again each time it is read; `Fin.optAll` (the renamings and substitutions)
read each branch several times, so nested case analyses made them exponential
(`Fin.optAllMemo`).  Written `let a := Fin.memoArr f; … fun i => Fin.memoGet a i …`, the function `f` is computed
once at each position and stored in the array `a`; `Fin.memoGet a i` is `f i`
(`Fin.memoGet_eq`).

The array must be bound by the caller, outside the closure: the compiler moves a computation
used only inside a closure into it (so a helper `memo f := let a := …; fun i => …` would compute
the array again at each call), but keeps one bound outside of it.  `Fin.memoArr` is
`@[noinline]` so that it stays one value.
-/

namespace LeanScript

/-- The values of `f`, each with its position. -/
@[noinline] def Fin.memoArr {n : Nat} {β : Fin n → Type} (f : (i : Fin n) → β i) :
    {a : Array ((j : Fin n) × β j) // a = Array.ofFn fun i => ⟨i, f i⟩} :=
  ⟨Array.ofFn fun i => ⟨i, f i⟩, rfl⟩

/-- The value at position `i` of the values of `f`. -/
def Fin.memoGet {n : Nat} {β : Fin n → Type} {f : (i : Fin n) → β i}
    (a : {a : Array ((j : Fin n) × β j) // a = Array.ofFn fun i => ⟨i, f i⟩}) (i : Fin n) : β i :=
  have h : i.val < a.1.size := by simp [a.2]
  have e : (a.1[i.val]'h).1 = i := by simp [a.2]
  e ▸ (a.1[i.val]'h).2

theorem Fin.memoGet_eq {n : Nat} {β : Fin n → Type} {f : (i : Fin n) → β i}
    (a : {a : Array ((j : Fin n) × β j) // a = Array.ofFn fun i => ⟨i, f i⟩}) (i : Fin n) :
    Fin.memoGet a i = f i := by
  have key : ∀ (s : (j : Fin n) × β j) (e : s.1 = i), s = ⟨i, f i⟩ → e ▸ s.2 = f i := by
    intro s e hs; subst hs; rfl
  apply key
  simp [a.2]

end LeanScript

end
