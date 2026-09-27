-- 1. Stream Representation
structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x

-- 2. Conversions: fromArray
@[inline]
def fromArray (arr : Array α) : Unfold α where
  State := Nat
  seed  := 0
  step ix :=
    if h : ix < arr.size then
      some (ix + 1, arr[ix])
    else
      none
  measure ix := arr.size - ix
  decreasing := by
    intro x x' a hx
    split at hx
    · injection hx with h1
      simp_all only [Prod.mk.injEq]
      obtain ⟨left, right⟩ := h1
      subst left right
      grind only
    · contradiction

-- 3. Conversions: toArray
@[inline]
def toArrayLoop (u : Unfold α) (s : u.State) (acc : Array α) : Array α :=
  match _h : u.step s with
  | none => acc
  | some (s', a) => toArrayLoop u s' (acc.push a)
termination_by u.measure s
decreasing_by exact u.decreasing s s' a _h

@[inline]
def toArray (u : Unfold α) : Array α :=
  toArrayLoop u u.seed #[]

-- 4. Stream combinators: mapU
@[inline]
def mapU (f : α → β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step s :=
    match u.step s with
    | none => none
    | some (s', a) => some (s', f a)
  measure := u.measure
  decreasing := by
    intro x x' b hx
    cases hstep : u.step x with
    | none =>
      rw [hstep] at hx
      contradiction
    | some pair =>
      obtain ⟨s_next, a⟩ := pair
      rw [hstep] at hx
      injection hx with h1
      simp_all only [Prod.mk.injEq]
      obtain ⟨left, right⟩ := h1
      subst left right
      grind only [Nat.le_antisymm, Nat.le_of_lt, Unfold.decreasing]

-- 5. Stream combinators: filterMapU
@[inline]
def filterMapStep (u : Unfold α) (f : α → Option β) (s : u.State) : Option (u.State × β) :=
  match _h : u.step s with
  | none => none
  | some (s', a) =>
    match f a with
    | some b => some (s', b)
    | none   => filterMapStep u f s'
termination_by u.measure s
decreasing_by exact u.decreasing s s' a _h

theorem filterMapStep_decreasing_aux (u : Unfold α) (f : α → Option β) (n : Nat) :
    ∀ s, u.measure s ≤ n → ∀ s' b, filterMapStep u f s = some (s', b) → u.measure s' < u.measure s := by
  induction n with
  | zero =>
    intro s hs s' b h
    have hdec_all := u.decreasing s
    rw [filterMapStep] at h
    split at h
    · contradiction
    · have := hdec_all _ _ (by assumption)
      omega
  | succ n ih =>
    intro s hs s' b h
    have hdec_all := u.decreasing s
    rw [filterMapStep] at h
    split at h
    · contradiction
    · split at h
      · injection h with h1
        simp_all only [Option.some.injEq, Prod.mk.injEq, and_imp, forall_apply_eq_imp_iff,
          forall_eq', gt_iff_lt]
      · have hdec := hdec_all _ _ (by assumption)
        have := ih _ (by omega) s' b h
        omega

theorem filterMapStep_decreasing (u : Unfold α) (f : α → Option β) (s s' : u.State) (b : β)
    (h : filterMapStep u f s = some (s', b)) : u.measure s' < u.measure s :=
  filterMapStep_decreasing_aux u f (u.measure s) s (Nat.le_refl _) s' b h

@[inline]
def filterMapU (f : α → Option β) (u : Unfold α) : Unfold β where
  State := u.State
  seed  := u.seed
  step  := filterMapStep u f
  measure := u.measure
  decreasing := fun x x' b h => filterMapStep_decreasing u f x x' b h

@[inline]
def filterU (p : α → Bool) (u : Unfold α) : Unfold α :=
  filterMapU (fun a => if p a then some a else none) u

-- 6. Helper combinators
@[inline]
def overArray (f : Unfold α → Unfold β) (arr : Array α) : Array β :=
  toArray (f (fromArray arr))

@[inline]
def dropPrefix1 (s : String) : Option String :=
  if s.startsWith "1" then some (s.drop 1).toString else none

-- 7. Test pipeline
def test (arr : Array Int) : Array String :=
  flip overArray arr fun u =>
    u
      |> mapU (· + 1)
      |> mapU toString
      |> filterMapU dropPrefix1
      |> mapU ("2" ++ ·)
      |> filterU (· != "wat")
      |> mapU (· ++ "1")

-- #eval test #[0, 9, 10, 1]
-- Output: #["21", "201", "211"]
