-- Four shapes of recursion, one function each, all in the one grammar.
--
-- The grammar has a **single** recursion node, `Term.fixAcc`, carrying an order, a
-- subject, accessibility evidence for that subject, an invariant and a body.  What used
-- to be a choice between four constructors is now two separate things:
--
--   * *how it descends* is a choice of **subject**, not of node: `Term.fixStruct` when
--     the subject is one named argument in the order the language fixes, and
--     `Term.fixNatWith` when it is the subject Lean's `termination_by` names.  Both are
--     the same node;
--   * *where the self call stands* is not carried at all: it is a decidable property of
--     the body, reported after the fact by `Term.schemeOf` / `Term.schemes` of
--     `LeanScript/SchemeCensus.lean` as `"tail"` or `"deep"`.
--
-- This module is the end-to-end test of that arrangement: four Lean functions, covering
-- both kinds of subject and both self-call positions, translated **in this file** by
-- `#leanjs_generate_program_from_all_public_defs_in_current_file`, then
--
--   * checked to have got the self-call verdict they should (`*_position`), and
--   * run against the Lean functions they were translated from (`*_agrees`).
--
-- Which subject a recursion gets is not guessed from the shape of its measure: it is what
-- Lean itself recorded (`Lean.Elab.Structural.eqnInfoExt` for a structural recursion, the
-- packed `termination_by` for a well-founded one).  `gcdT` below is the function that
-- tells the two readings apart: its `termination_by` names the bare parameter `m`, but
-- its subject `n % m` is *computed*, so Lean elaborated it by well-founded recursion and
-- the generated node is a `Term.fixNatWith`.
import LeanScript.GenerateProgram

-- 🟦 structural subject, tail call: the accumulator loop.  Lean recurses on the pattern variable of
-- `n + 1`, and the self call is the whole answer of its branch, so this is a `while`.
def sumAcc : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => sumAcc n (a + n + 1)

-- 🟦 structural subject, deep call: the self call stands under a multiplication, so it needs a frame,
-- and the depth is the subject itself.
def factD : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factD n

-- 🟥 well-founded subject, tail call: the subject `n % m` is computed, not matched, and the call is in
-- tail position.
def gcdT : Nat → Nat → Nat
  | 0,      n => n
  | m' + 1, n => gcdT (n % (m' + 1)) (m' + 1)
termination_by m => m
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos m')

-- 🟥 well-founded subject, deep call: the subject `n - 2` is computed, and the self call stands under
-- an addition.
def stepsDown (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 1 + stepsDown (n - 2)
termination_by n
decreasing_by omega

#leanjs_generate_program_from_all_public_defs_in_current_file

namespace SnapshotsMy.FourSchemesCheck

open LeanScript LeanScript.Expr ProgramSnapshotsMyFourSchemes

-- where a term's self calls stand is read off the term by `Term.schemeOf` (the node at
-- its head) and `Term.schemes` (every recursion node of it), from
-- `LeanScript/SchemeCensus.lean`

theorem sumAcc_position : Term.schemeOf tm_sumAcc = "tail" := rfl

theorem factD_position : Term.schemeOf tm_factD = "deep" := rfl

theorem gcdT_position : Term.schemeOf tm_gcdT = "tail" := rfl

theorem stepsDown_position : Term.schemeOf tm_stepsDown = "deep" := rfl

/-- None of these four functions has a nested recursion, so each term holds exactly one
    recursion node — and between them the four terms cover both self-call positions, at
    both kinds of subject. -/
theorem module_schemes :
    Term.schemes tm_factD ++ Term.schemes tm_gcdT ++ Term.schemes tm_stepsDown ++
        Term.schemes tm_sumAcc =
      ["deep", "tail", "deep", "tail"] := rfl

/-- `factD` is the first declaration of the module in name order, so it is written
    against the empty signature. -/
def runFactD (n : Nat) : Nat := Term.run tm_factD n

/-- The declarations `gcdT` is written against, as a program. -/
def pGcdT : Program sig_gcdT.decls := .cons d_factD (by decide) tm_factD .nil

/-- `gcdT`, as the generated term computes it. -/
def runGcdT (m n : Nat) : Nat := Program.run pGcdT tm_gcdT m n

/-- The declarations `stepsDown` is written against, as a program. -/
def pStepsDown : Program sig_stepsDown.decls := .cons d_gcdT (by decide) tm_gcdT pGcdT

/-- `stepsDown`, as the generated term computes it. -/
def runStepsDown (n : Nat) : Nat := Program.run pStepsDown tm_stepsDown n

/-- The declarations `sumAcc` is written against, as a program. -/
def pSumAcc : Program sig_sumAcc.decls :=
  .cons d_stepsDown (by decide) tm_stepsDown pStepsDown

/-- `sumAcc`, as the generated term computes it. -/
def runSumAcc (n a : Nat) : Nat := Program.run pSumAcc tm_sumAcc n a

theorem sumAcc_agrees :
    ((List.range 20).all fun n => (List.range 5).all fun a =>
      runSumAcc n a == sumAcc n a) = true := by native_decide

theorem factD_agrees :
    ((List.range 12).all fun n => runFactD n == factD n) = true := by native_decide

theorem gcdT_agrees :
    ((List.range 30).all fun m => (List.range 30).all fun n =>
      runGcdT m n == gcdT m n) = true := by native_decide

theorem stepsDown_agrees :
    ((List.range 40).all fun n => runStepsDown n == stepsDown n) = true := by native_decide

end SnapshotsMy.FourSchemesCheck
