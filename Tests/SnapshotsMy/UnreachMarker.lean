-- An unreachable branch, and what the translation writes in its place.
--
-- `DESIGN.md` §6 is about the front end's treatment of a branch Lean
-- has *proved* impossible (an LCNF `.unreach`): the proof was thrown away and the branch
-- became `retTy.dflt`, an ordinary value of the result type, indistinguishable from a
-- value the program meant to compute.  Until the grammar can carry the contradiction
-- itself (§2's path condition), the note asks for the minimum repair — say that the point
-- is a failure rather than a value — and this module is its end-to-end test:
--
--   * `small` and `headOf` each have a branch Lean proved unreachable; the terms the
--     command generates for them mention a **partial** primitive, so the strict-mode
--     check `Term.usesPartialExtern` reports them (`small_marks_unreachable`,
--     `headOf_marks_unreachable`);
--   * `total` has no such branch, and its term is *not* flagged (`total_is_total`), so
--     the flag says something;
--   * the marker does not disturb what the program computes: the generated terms agree
--     with the Lean functions at every reachable argument (`small_agrees`,
--     `total_agrees`).
--
-- The *value* of the marker is still `Ty.dflt`: Lean's `panic!` literally is `@default`,
-- so a translation that answered anything else would be unfaithful.  What changed is that
-- an emitter may now compile the point to a `throw` instead of a constant.
import LeanScript.GenerateProgram

/-- Three cases, and the fourth is impossible because `n < 3`. -/
def small (n : Nat) (h : n < 3) : Nat :=
  match n, h with
  | 0, _ => 10
  | 1, _ => 20
  | 2, _ => 30

/-- The head of a list the caller proved non-empty: the `nil` branch is unreachable. -/
def headOf (xs : List Nat) (h : xs ≠ []) : Nat :=
  match xs, h with
  | x :: _, _ => x

/-- A function with no unreachable branch at all. -/
def total (n : Nat) : Nat := n + 1

#leanjs_generate_program_from_all_public_defs_in_current_file

namespace SnapshotsMy.UnreachMarkerCheck

open LeanScript LeanScript.Expr ProgramSnapshotsMyUnreachMarker

/-! ## The unreachable branches are marked -/

/-- `small`'s impossible fourth case is a call of Lean's `panic!`, which the catalogue
    flags as partial. -/
theorem small_marks_unreachable : tm_small.usesPartialExtern = true := rfl

/-- The same for `headOf`'s `nil` branch. -/
theorem headOf_marks_unreachable : tm_headOf.usesPartialExtern = true := rfl

/-- And a function with no unreachable branch mentions no partial primitive, so the flag
    is not vacuous. -/
theorem total_is_total : tm_total.usesPartialExtern = false := rfl

/-! ## The marker changes nothing a reachable run can see -/

/-- The declarations `small` is written against, as a program (`headOf` is the first
    declaration in name order, so it is the one `small`'s signature lists). -/
def pSmall : Program sig_small.decls := .cons d_headOf (by decide) tm_headOf .nil

/-- `small`, as the generated term computes it. -/
def runSmall (n : Nat) : Nat := Program.run pSmall tm_small n

/-- The declarations `total` is written against, as a program. -/
def pTotal : Program sig_total.decls := .cons d_small (by decide) tm_small pSmall

/-- `total`, as the generated term computes it. -/
def runTotal (n : Nat) : Nat := Program.run pTotal tm_total n

theorem small_agrees :
    runSmall 0 = small 0 (by omega) ∧ runSmall 1 = small 1 (by omega) ∧
      runSmall 2 = small 2 (by omega) := by native_decide

theorem total_agrees :
    ((List.range 20).all fun n => runTotal n == total n) = true := by native_decide

-- Nothing the command generated rests on an unproved claim.
/-- info: 'ProgramSnapshotsMyUnreachMarker.tm_small' depends on axioms: [propext] -/
#guard_msgs in
#print axioms tm_small

end SnapshotsMy.UnreachMarkerCheck
