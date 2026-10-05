module

public import LeanScript.Term.Optimize.Basic
public import LeanScript.Term.Pretty
public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.Term.Pretty
public meta import LeanScript.Term.Optimize.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Comparisons of an operand with itself, formally

`Tests/SnapshotsMy/CharCmpSelf.lean` (variations of `Tests/SnapshotsPBOPure/PrimOpChar02.lean`):
`charValues op c` with an unknown character `c` compares `c` with itself, `op c c`.  The
optimiser folds such a comparison to its literal (`Neu.reflFold`, in `Neu.condSimp` and
`Term.letEOrSubst`): `x == x` and `x ≤ x` are `true`, `x < x` is `false`, on `Char`, `String`,
`Nat`, `Int` and the fixed-width integers; never on `Float` (`NaN`).

In the body of a function of several parameters (`selfMixed`) the comparisons stay: folding
them would change the level of an open body, which `Body.knownTestWalk` keeps.  The conversion
to JavaScript folds them there (`JsTerm.Lower.FromTerm`, `Neu.extern`).

* `…_optimized_run`: the optimised translation computes the Lean function, for every input.
* `…_optimized_pretty`: the optimised statements.
-/

namespace ReflCmpTest

open LeanScript

@[inline] def charValuesAt (op : Char → Char → Bool) (c : Char) : Array Bool :=
  #[op c 'a', op c c]

def selfChar (c : Char) : Array Bool := #[c == c, c < c, c ≤ c, c == 'a', 'a' < c]

def selfCharAt (c : Char) : Array Bool := charValuesAt (fun a b => a == b) c

def selfMixed (s : String) (n : Nat) (i : Int) (x : UInt8) : Array Bool :=
  #[s == s, s < s, n == n, n < n, n ≤ n, i < i, i ≤ i, x == x, x < x]

def selfFloat (x : Float) : Array Bool := #[x == x]

def selfCharT := #leanscript_to_term selfChar
def selfCharAtT := #leanscript_to_term selfCharAt
def selfMixedT := #leanscript_to_term selfMixed
def selfFloatT := #leanscript_to_term selfFloat

/-! ## The optimiser keeps the value -/

theorem selfMixed_optimized_run (s : String) (n : Nat) (i : Int) (x : UInt8) :
    (((selfMixedT (Δ := DSig.nil)).optimizeN 3).run s n i x : Array Bool) =
      selfMixed s n i x := by
  rw [Term.optimizeN_run]; rfl

/-! ## The optimised statements -/

/-- `c == c`, `c < c` and `c ≤ c` are literals; `c == 'a'` and `'a' < c` stay. -/
theorem selfChar_optimized_pretty : ((selfCharT (Δ := DSig.nil)).optimizeN 3).pretty =
    "\n".intercalate [
      "val k1 [1] : (Char → (Array Bool)) := fun x2 [1] : Char => (closed)",
      "  let x3 [ω] : String := share lean_string_push(\"\", x2)",
      "  ret #[true, false, true, lean_string_dec_eq(x3, \"a\"), lean_string_dec_lt(\"a\", x3)]",
      "ret k1"] := by
  native_decide

/-- `charValuesAt` inlined: `op c c` is `true`. -/
theorem selfCharAt_optimized_pretty : ((selfCharAtT (Δ := DSig.nil)).optimizeN 3).pretty =
    "\n".intercalate [
      "val k1 [1] : (Char → (Array Bool)) := fun x2 [1] : Char => (closed)",
      "  ret #[lean_string_dec_eq(lean_string_push(\"\", x2), \"a\"), true]",
      "ret k1"] := by
  native_decide

/-- `x == x` on `Float` is not folded: it is `false` for `NaN`. -/
theorem selfFloat_optimized_pretty : ((selfFloatT (Δ := DSig.nil)).optimizeN 3).pretty =
    "\n".intercalate [
      "val k1 [1] : (Float → (Array Bool)) := fun x2 [ω] : Float => (closed)",
      "  ret #[lean_float_beq(x2, x2)]",
      "ret k1"] := by
  native_decide

end ReflCmpTest
