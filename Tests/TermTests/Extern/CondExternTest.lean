module

public import LeanScript.Term.Build
public import LeanScript.TermElab.Notation
public import LeanScript.Term.Extern.Shorthands
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The pure conditional, calls of externs, and externs that take a proof

* The pure conditional `Neu.cond` and the calls of externs `Neu.extern` (every extern is an entry
  of the catalogue `LeanInitPureExtern`, called on pure expressions), written in the notation
  (`cond c a b`, `extern ‹.lean_nat_sub› a b`) and produced by `#leanscript_to_term`: an `if`
  that is an operand and whose branches are pure is a `Neu.cond`, and a call of a library
  function that is the Lean function of an entry is a `Neu.extern`, so
  `(if b then n * 2 else 0) + 1` is one pure expression (see also `TermTests/ToTerm/ToTermTest.lean`).
* Externs that take a proof (`a[i]'h`, `UInt16.ofNatLT n h`): the language erases proofs, so
  the evaluator of the extern decides the proposition on the values of the arguments
  (`if h : n < UInt16.size then UInt16.ofNatLT n h else default`; `a[i]'h` is read as
  `Array.get!Internal`, which takes the default of the element type).  The correctness
  theorems show, for every input, that the translation computes the Lean function: the
  `default` is never reached.
-/

namespace CondExternTest

open LeanScript

/-- The innermost unknown. -/
abbrev x0 {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    PExpr Δ Φ (⟨τ, .many, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.head (by decide)))

/-- The unknown one binder further out. -/
abbrev x1 {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    {b : UBinder ks} : PExpr Δ Φ (b :: ⟨τ, .many, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.tail (.head (by decide))))

/-- The unknown two binders further out. -/
abbrev x2 {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    {b b' : UBinder ks} : PExpr Δ Φ (b :: b' :: ⟨τ, .many, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.tail (.tail (.head (by decide)))))

/-! ## The notation -/

/-- `cond` is a pure expression (a neutral one: its condition is an unknown). -/
def pick : PExpr DSig.nil [] [⟨.bool, .many, 0⟩] .nat (some 0) := [Term| cond #0 1 2]
example : pick.eval PUnit.unit true = (1 : Nat) := rfl
example : pick.eval PUnit.unit false = (2 : Nat) := rfl

/-- A call of an extern with an open argument is a pure expression too. -/
def addOne : PExpr DSig.nil [] [⟨.nat, .many, 0⟩] .nat (some 0) := [Term| extern ‹.lean_nat_add› #0 1]
example : addOne.eval PUnit.unit (41 : Nat) = (42 : Nat) := rfl

/-- Both in operand position, with no `let` and no join point. -/
def absDiff : Term DSig.nil 0 [] [⟨.nat, .many, 0⟩, ⟨.nat, .many, 0⟩] .nat [] (some 0) :=
  [Term| cond (extern ‹.lean_nat_dec_lt› #0 #1) (extern ‹.lean_nat_sub› #1 #0)
    (extern ‹.lean_nat_sub› #0 #1)]
example : absDiff = .ret (.neu (.cond (Neu.lean_nat_dec_lt x0 x1)
    (PExpr.lean_nat_sub x1 x0) (PExpr.lean_nat_sub x0 x1))) :=
  rfl
example : absDiff.eval PUnit.unit ((3 : Nat), (10 : Nat)) PUnit.unit = (7 : Nat) := rfl

/-- On known values the condition and the calls are computed. -/
example : ([Term| cond (extern ‹.lean_nat_dec_lt› 3 10) (extern ‹.lean_nat_sub› 10 3)
    (extern ‹.lean_nat_sub› 3 10)] : Term DSig.nil 0 [] [] .nat [] none) = .ret (.lit .nat 7) := rfl

/-! ## Calls of externs and `cond` from the translator -/

/-- A clamp: two nested `if`s in operand position, on comparisons (calls of externs). -/
def clampAdd (lo hi n : Nat) : Nat := (if n < lo then lo else if hi < n then hi else n) + 1
def clampAddT := #leanscript_to_term clampAdd
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (0 : Nat) = (3 : Nat) := rfl
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (9 : Nat) = (6 : Nat) := rfl
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (4 : Nat) = (5 : Nat) := rfl

/-- The body of `clampAdd` is one pure expression: no `let`, no join point.  The three
    curried closures are known values; the two inner ones are open (they mention the outer
    parameters). -/
example {ks : List Nat} {Δ : DSig ks} : clampAddT (Δ := Δ) =
    .letV .many (.lam (u := .many) (.closed
      (.letV .many (.lam (u := .many) (.opened
        (.letV .many (.lam (u := .many) (.opened
          (.ret (PExpr.lean_nat_add
            (.neu (.cond (Neu.lean_nat_dec_lt x0 x2) x2
              (.neu (.cond (Neu.lean_nat_dec_lt x1 x0) x1 x0))))
            (.lit .nat 1)))
          (show 1 ≤ 2 by decide)))
          (.ret (.kvar .head)))
        (Nat.le_refl 1)))
        (.ret (.kvar .head)))))
      (.ret (.kvar .head)) := rfl

/-- **The translation of `clampAdd` computes `clampAdd`**, on every input. -/
theorem clampAddT_correct (lo hi n : Nat) :
    (clampAddT (Δ := DSig.nil)).run lo hi n = clampAdd lo hi n := by
  have run : (clampAddT (Δ := DSig.nil)).run lo hi n =
      cond (decide (n < lo)) lo (cond (decide (hi < n)) hi n) + 1 := by kernel_rfl
  rw [run]
  unfold clampAdd
  by_cases h1 : n < lo <;> by_cases h2 : hi < n <;> simp [h1, h2] <;> rfl

/-! ## Externs that take a proof -/

/-- `a[i]` under `if h : i < a.size`: the proof `h` is a local hypothesis, erased. -/
def safeGet (a : Array Nat) (i : Nat) : Nat := if h : i < a.size then a[i] else 0
def safeGetT := #leanscript_to_term safeGet
example : (safeGetT (Δ := DSig.nil)).run (#[5, 6, 7] : Array Nat) (1 : Nat) = (6 : Nat) := rfl
example : (safeGetT (Δ := DSig.nil)).run (#[5, 6, 7] : Array Nat) (5 : Nat) = (0 : Nat) := rfl

/-- The array access is the call of `lean_array_get` (`Array.get!Internal`), whose arguments
    are the default of the element type, the array and the index: out of bounds it is the
    default. -/
example {ks : List Nat} {Δ : DSig ks} : safeGetT (Δ := Δ) =
    .letV .many (.lam (u := .many) (.closed
      (.letV .many (.lam (u := .many) (.opened
        (.branch (.ite (Neu.lean_nat_dec_lt x0 (PExpr.lean_array_get_size .nat x1))
          (.ret (PExpr.lean_array_get .nat (.lit .nat 0) x1 x0))
          (.ret (.lit .nat 0))))
        (Nat.le_refl 1)))
        (.ret (.kvar .head)))))
      (.ret (.kvar .head)) := rfl

/-- **The translation of `safeGet` computes `safeGet`**, on every input: where the program
    reads `a[i]`, the extern's own decision of `i < a.size` holds, so its `default` is never
    the value. -/
theorem safeGetT_correct (a : Array Nat) (i : Nat) :
    (safeGetT (Δ := DSig.nil)).run a i = safeGet a i := by
  have run : (safeGetT (Δ := DSig.nil)).run a i =
      cond (decide (i < a.size)) (if h : i < a.size then a[i]'h else default) 0 := by kernel_rfl
  rw [run]
  unfold safeGet
  by_cases h : i < a.size <;> simp [h] <;> rfl

/-- A conversion that takes a proof, `UInt16.ofNatLT n h`: the call of the extern
    `lean_uint16_of_nat__UInt16_ofNatLT` on `n` (the proof erased), a pure expression. -/
def toU16 (n : Nat) : UInt16 := if h : n < UInt16.size then UInt16.ofNatLT n h else 0
def toU16T := #leanscript_to_term toU16
example : (toU16T (Δ := DSig.nil)).run (300 : Nat) = (300 : UInt16) := rfl
example : (toU16T (Δ := DSig.nil)).run (70000 : Nat) = (0 : UInt16) := rfl

example {ks : List Nat} {Δ : DSig ks} : toU16T (Δ := Δ) =
    .letV .many (.lam (u := .many) (.closed
      (.branch (.ite (Neu.lean_nat_dec_lt x0 (.lit .nat UInt16.size))
        (.ret (PExpr.lean_uint16_of_nat__UInt16_ofNatLT x0))
        (.ret (.lit .uint16 0))))))
      (.ret (.kvar .head)) := rfl

/-- **The translation of `toU16` computes `toU16`**, on every input. -/
theorem toU16T_correct (n : Nat) : (toU16T (Δ := DSig.nil)).run n = toU16 n := by
  have run : (toU16T (Δ := DSig.nil)).run n = cond (decide (n < UInt16.size))
      (if h : n < UInt16.size then UInt16.ofNatLT n h else default) 0 := by kernel_rfl
  rw [run]
  unfold toU16
  by_cases h : n < UInt16.size <;> simp [h] <;> rfl

end CondExternTest

end
