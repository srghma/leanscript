-- The *other* place the front end knew a point could not be reached.
--
-- A mutual clique is still merged into a single recursion that answers with a tagged
-- union, one tag per member, and each member reads its own answer back out of that union
-- (`unwrapMemberAnswer`).  The branch for any other member's tag cannot be taken — a
-- member's answer is wrapped at that member's own tag — and the front end used to fill it
-- in with `rty.dflt`, an ordinary value.  It now writes the same marker an unreachable
-- LCNF branch gets (`LeanScript.Expr.Ops.unreachableAt`, i.e. Lean's `panic!`), so the point
-- is flagged as a failure rather than pretending to be a value.
--
-- `DESIGN.md` §8 asks for the union to go away altogether, which
-- needs a first-class mutual-recursion node in the grammar; that is not done.  This file
-- checks the part that is: the unreachable point is marked (`f1_marks_unreachable`,
-- `f2_marks_unreachable`) and the clique still computes what it computed before
-- (`f1_agrees`, `f2_agrees`).
import LeanScript.GenerateProgram

mutual

/-- One member of a two-member clique, answering with a `Bool`. -/
def f1 : Nat → Bool
  | 0 => true
  | n + 1 => f2 n == 0

/-- The other, answering with a `Nat` — so the merged recursion really does need a union
    to answer with, and each member really does have to unwrap it. -/
def f2 : Nat → Nat
  | 0 => 7
  | n + 1 => if f1 n then 0 else 1

end

#leanjs_generate_program_from_all_public_defs_in_current_file

namespace SnapshotsMy.MutualUnreachMarkerCheck

open LeanScript LeanScript.Expr ProgramSnapshotsMyMutualUnreachMarker

/-- Reading `f1`'s answer out of the union has a branch that cannot be taken, and it is
    marked. -/
theorem f1_marks_unreachable : tm_f1.usesPartialExtern = true := rfl

/-- The same for `f2`. -/
theorem f2_marks_unreachable : tm_f2.usesPartialExtern = true := rfl

/-- The declarations `f1` is written against, as a program: the merged clique. -/
def pF1 : Program sig_f1.decls :=
  .cons d_f1___f2__clique_ (by decide) tm_f1___f2__clique_ .nil

/-- `f1`, as the generated term computes it. -/
def runF1 (n : Nat) : Bool := Program.run pF1 tm_f1 n

/-- The declarations `f2` is written against, as a program. -/
def pF2 : Program sig_f2.decls := .cons d_f1 (by decide) tm_f1 pF1

/-- `f2`, as the generated term computes it. -/
def runF2 (n : Nat) : Nat := Program.run pF2 tm_f2 n

theorem f1_agrees : ((List.range 20).all fun n => runF1 n == f1 n) = true := by
  native_decide

theorem f2_agrees : ((List.range 20).all fun n => runF2 n == f2 n) = true := by
  native_decide

end SnapshotsMy.MutualUnreachMarkerCheck
