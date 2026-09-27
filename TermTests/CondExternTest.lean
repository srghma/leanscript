module

public import LeanScript.Term.Eval
public import LeanScript.TermElab.Notation
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The pure conditional, cheap externs, and externs that take a proof

* `PExpr.cond` (proposal 4d) and the cheap externs `PExpr.extern` (proposal 4h), written in
  the notation (`cond c a b`, `pextern "name" f a b`) and produced by `#leanscript_to_term`: an
  `if` that is an operand and whose branches are pure is a `PExpr.cond`, and an arithmetic
  operator on scalars is a `PExpr.extern`, so `(if b then n * 2 else 0) + 1` is one pure
  expression (see also `TermTests/ToTermTest.lean`).
* Externs that take a proof (`a[i]'h`, `UInt16.ofNatLT n h`): the language erases proofs, so
  the function of the extern decides the proposition on the values of the arguments
  (`if h : i < a.size then a[i]'h else default`).  The correctness theorems show, for every
  input, that the translation computes the Lean function: the `default` is never reached.
-/

namespace CondExternTest

open LeanScript

/-! ## The notation -/

/-- `cond` is a pure expression. -/
def pick : PExpr DSig.nil [.bool] .nat := [Term| cond #0 1 2]
example : pick.eval true = (1 : Nat) := rfl
example : pick.eval false = (2 : Nat) := rfl

/-- A cheap extern is a pure expression too. -/
def addOne : PExpr DSig.nil [.nat] .nat :=
  [Term| pextern "Nat.add" ‹fun v => Nat.add v.1 v.2› (#0 : Nat) (1 : Nat)]
example : addOne.eval (41 : Nat) = (42 : Nat) := rfl

/-- Both in operand position, with no `let` and no join point. -/
def absDiff : Term DSig.nil [.nat, .nat] .nat [] :=
  [Term| cond (pextern "Nat.blt" ‹fun v => Nat.blt v.1 v.2› (#0 : Nat) (#1 : Nat))
    (pextern "Nat.sub" ‹fun v => Nat.sub v.1 v.2› (#1 : Nat) (#0 : Nat))
    (pextern "Nat.sub" ‹fun v => Nat.sub v.1 v.2› (#0 : Nat) (#1 : Nat))]
example : absDiff = .ret (.cond
    (.extern (σs := [.nat, .nat]) "Nat.blt" (fun v => Nat.blt v.1 v.2)
      (.cons (.bvar 0) (.cons (.bvar 1) .nil)))
    (.extern (σs := [.nat, .nat]) "Nat.sub" (fun v => Nat.sub v.1 v.2)
      (.cons (.bvar 1) (.cons (.bvar 0) .nil)))
    (.extern (σs := [.nat, .nat]) "Nat.sub" (fun v => Nat.sub v.1 v.2)
      (.cons (.bvar 0) (.cons (.bvar 1) .nil)))) :=
  rfl
example : absDiff.eval ((3 : Nat), (10 : Nat)) PUnit.unit = (7 : Nat) := rfl

-- The notation prints them back.
/--
info: @[expose] def CondExternTest.absDiff : Term DSig.nil [[Ty| Nat], [Ty| Nat]] [Ty| Nat] [] :=
[Term|
  cond (pextern "Nat.blt" ‹fun v => Nat.blt v.fst v.snd› #0 #1) (pextern "Nat.sub" ‹fun v => Nat.sub v.fst v.snd› #1 #0)
    (pextern "Nat.sub" ‹fun v => Nat.sub v.fst v.snd› #0 #1)]
-/
#guard_msgs in
#print absDiff

/-! ## Cheap externs and `cond` from the translator -/

/-- A clamp: two nested `if`s in operand position, on cheap comparisons. -/
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

/-- The extern decides `i < a.size` again, and builds `a[i]'h` from the proof `h` it gets. -/
example {ks : List Nat} {Δ : DSig ks} : safeGetT (Δ := Δ) =
    .ofComp (.lam (.ofComp (.lam
      (.letE (.extern (σs := [.array .nat]) (τ := .nat) "Array.size"
          (fun v => (fun x0 : Array Nat => x0.size) v) (.cons (.bvar 1) .nil))
        (.ite (.extern (σs := [.nat, .nat]) (τ := .bool) "decide LT.lt"
            (fun v => (fun x0 x1 : Nat => decide (x0 < x1)) v.1 v.2)
            (.cons (.bvar 1) (.cons (.bvar 0) .nil)))
          (.ofComp (.extern (σs := [.array .nat, .nat]) (τ := .nat) "GetElem.getElem"
            (fun v => (fun (x0 : Array Nat) (x1 : Nat) =>
              if h : x1 < x0.size then x0[x1]'h else default) v.1 v.2)
            (.cons (.bvar 2) (.cons (.bvar 1) .nil))))
          (.ret (.lit .nat 0))))))) := rfl

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

/-- A conversion that takes a proof, `UInt16.ofNatLT n h`: a cheap extern (a function of a
    fixed-width type, on scalars), so a pure expression. -/
def toU16 (n : Nat) : UInt16 := if h : n < UInt16.size then UInt16.ofNatLT n h else 0
def toU16T := #leanscript_to_term toU16
example : (toU16T (Δ := DSig.nil)).run (300 : Nat) = (300 : UInt16) := rfl
example : (toU16T (Δ := DSig.nil)).run (70000 : Nat) = (0 : UInt16) := rfl

example {ks : List Nat} {Δ : DSig ks} : toU16T (Δ := Δ) =
    .ofComp (.lam
      (.ite (.extern (σs := [.nat, .nat]) (τ := .bool) "decide LT.lt"
          (fun v => (fun x0 x1 : Nat => decide (x0 < x1)) v.1 v.2)
          (.cons (.bvar 0) (.cons (.lit .nat UInt16.size) .nil)))
        (.ret (.extern (Δ := Δ) (σs := [.nat]) (τ := .prim .uint16) "UInt16.ofNatLT"
          (fun v => (fun x0 : Nat => if h : x0 < UInt16.size then UInt16.ofNatLT x0 h else default) v)
          (.cons (.bvar 0) .nil)))
        (.ret (.lit .uint16 0)))) := rfl

/-- **The translation of `toU16` computes `toU16`**, on every input. -/
theorem toU16T_correct (n : Nat) : (toU16T (Δ := DSig.nil)).run n = toU16 n := by
  have run : (toU16T (Δ := DSig.nil)).run n = cond (decide (n < UInt16.size))
      (if h : n < UInt16.size then UInt16.ofNatLT n h else default) 0 := by kernel_rfl
  rw [run]
  unfold toU16
  by_cases h : n < UInt16.size <;> simp [h] <;> rfl

end CondExternTest

end
