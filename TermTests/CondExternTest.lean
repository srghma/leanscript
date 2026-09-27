module

public import LeanScript.Term.Eval
public import LeanScript.TermElab.Notation
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The pure conditional, calls of externs, and externs that take a proof

* `PExpr.cond` (proposal 4d) and the calls of externs `PExpr.extern` (every extern is an entry
  of the catalogue `LeanInitPureExtern`, called on pure expressions), written in the notation
  (`cond c a b`, `extern ‹.lean_nat_sub› a b`) and produced by `#leanscript_to_term`: an `if`
  that is an operand and whose branches are pure is a `PExpr.cond`, and a call of a library
  function that is the Lean function of an entry is a `PExpr.extern`, so
  `(if b then n * 2 else 0) + 1` is one pure expression (see also `TermTests/ToTermTest.lean`).
* Externs that take a proof (`a[i]'h`, `UInt16.ofNatLT n h`): the language erases proofs, so
  the evaluator of the extern decides the proposition on the values of the arguments
  (`if h : n < UInt16.size then UInt16.ofNatLT n h else default`; `a[i]'h` is read as
  `Array.get!Internal`, which takes the default of the element type).  The correctness
  theorems show, for every input, that the translation computes the Lean function: the
  `default` is never reached.
-/

namespace CondExternTest

open LeanScript

/-! ## The notation -/

/-- `cond` is a pure expression. -/
def pick : PExpr DSig.nil [.bool] .nat := [Term| cond #0 1 2]
example : pick.eval true = (1 : Nat) := rfl
example : pick.eval false = (2 : Nat) := rfl

/-- A call of an extern is a pure expression too. -/
def addOne : PExpr DSig.nil [.nat] .nat := [Term| extern ‹.lean_nat_add› #0 1]
example : addOne.eval (41 : Nat) = (42 : Nat) := rfl

/-- Both in operand position, with no `let` and no join point. -/
def absDiff : Term DSig.nil [.nat, .nat] .nat [] :=
  [Term| cond (extern ‹.lean_nat_dec_lt› #0 #1) (extern ‹.lean_nat_sub› #1 #0)
    (extern ‹.lean_nat_sub› #0 #1)]
example : absDiff = .ret (.cond (.lean_nat_dec_lt (.bvar 0) (.bvar 1))
    (.lean_nat_sub (.bvar 1) (.bvar 0)) (.lean_nat_sub (.bvar 0) (.bvar 1))) :=
  rfl
example : absDiff.eval ((3 : Nat), (10 : Nat)) PUnit.unit = (7 : Nat) := rfl

-- The notation prints them back.
/--
info: @[expose] def CondExternTest.absDiff : Term DSig.nil [[Ty| Nat], [Ty| Nat]] [Ty| Nat] [] :=
[Term| cond (extern ‹.lean_nat_dec_lt› #0 #1) (extern ‹.lean_nat_sub› #1 #0) (extern ‹.lean_nat_sub› #0 #1)]
-/
#guard_msgs in
#print absDiff

/-! ## Calls of externs and `cond` from the translator -/

/-- A clamp: two nested `if`s in operand position, on comparisons (calls of externs). -/
def clampAdd (lo hi n : Nat) : Nat := (if n < lo then lo else if hi < n then hi else n) + 1
def clampAddT := #leanscript_to_term clampAdd
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (0 : Nat) = (3 : Nat) := rfl
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (9 : Nat) = (6 : Nat) := rfl
example : (clampAddT (Δ := DSig.nil)).run (2 : Nat) (5 : Nat) (4 : Nat) = (5 : Nat) := rfl

/-- The body of `clampAdd` is one pure expression: no `let`, no join point. -/
theorem clampAddT_pure {ks : List Nat} {Δ : DSig ks} :
    ∃ e, clampAddT (Δ := Δ) = .ofComp (.lam (.ofComp (.lam (.ofComp (.lam (.ret e)))))) :=
  ⟨_, rfl⟩

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
    .ofComp (.lam (.ofComp (.lam
      (.ite (.lean_nat_dec_lt (.bvar 0) (.lean_array_get_size .nat (.bvar 1)))
        (.ret (.lean_array_get .nat (.lit .nat 0) (.bvar 1) (.bvar 0)))
        (.ret (.lit .nat 0)))))) := rfl

/--
info: @[expose] def CondExternTest.safeGetT : {ks : List Nat} → {Δ : DSig ks} → Term Δ [] [Ty| Array Nat → Nat → Nat] [] :=
fun {ks} {Δ} =>
  [Term|
    fun _ _ =>
      if extern ‹.lean_nat_dec_lt› #0 (extern ‹.lean_array_get_size [Ty| Nat]› #1) then
        extern ‹.lean_array_get [Ty| Nat]› 0 #1 #0 else 0]
-/
#guard_msgs in
#print safeGetT

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
    .ofComp (.lam
      (.ite (.lean_nat_dec_lt (.bvar 0) (.lit .nat UInt16.size))
        (.ret (.lean_uint16_of_nat__UInt16_ofNatLT (.bvar 0)))
        (.ret (.lit .uint16 0)))) := rfl

/--
info: @[expose] def CondExternTest.clampAddT : {ks : List Nat} → {Δ : DSig ks} → Term Δ [] [Ty| Nat → Nat → Nat → Nat] [] :=
fun {ks} {Δ} =>
  [Term|
    fun _ _ _ =>
      extern ‹.lean_nat_add› (cond (extern ‹.lean_nat_dec_lt› #0 #2) #2 (cond (extern ‹.lean_nat_dec_lt› #1 #0) #1 #0))
        1]
-/
#guard_msgs in
#print clampAddT

/-- **The translation of `toU16` computes `toU16`**, on every input. -/
theorem toU16T_correct (n : Nat) : (toU16T (Δ := DSig.nil)).run n = toU16 n := by
  have run : (toU16T (Δ := DSig.nil)).run n = cond (decide (n < UInt16.size))
      (if h : n < UInt16.size then UInt16.ofNatLT n h else default) 0 := by kernel_rfl
  rw [run]
  unfold toU16
  by_cases h : n < UInt16.size <;> simp [h] <;> rfl

end CondExternTest

end
