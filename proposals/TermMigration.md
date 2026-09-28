# Migration: the normal-form grammar becomes `LeanScript.Term`

Status notes for the replacement of the old A-normal `Term` by the normal-form grammar
(formerly `LeanScript.NTerm`).

## Decisions

* The old grammar (`LeanScript/Term/Syntax/Term.lean`, `LeanScript/Term/PExpr.lean`, its evaluator,
  `TermSubst`, `Elim`) is deleted. The normal-form grammar lives in `LeanScript/Term/` under
  the namespace `LeanScript` (`LeanScript.Term`, `LeanScript.PExpr`, `LeanScript.Neu`, …).
* Usages: `Usage01ω` for pattern binders, `Usage1ω` for definition binders (`letV`, `letE`,
  join points).
* Levels (`Lvl := Option Nat`) make the openness of bodies exact: `Body.opened` needs a level
  `m ≤ d`, i.e. a mention of something bound outside the body.
* Counting takes the maximum across the arms of a branch.
* The elaborators (`#leanscript_to_term`, the `[Term| …]` notation, `#leanscript_get_ctor`)
  produce normal-form terms directly: the A-normaliser (`LeanScript.TermElab.Anf`) becomes a
  normaliser by evaluation at elaboration time, over a semantic source tree.

## Steps

1. Core library moved and renamed (grammar, evaluator, renaming, weakening, levels,
   occurrence counts, dead-code elimination, closed terms are values).
2. Extern shorthands for the new `PExpr`/`Neu`.
3. The normaliser (`Anf`) over a semantic source tree.
4. `#leanscript_get_ctor`, the notation and `#leanscript_to_term` on top of it.
5. The tests and the proofs about translated programs.
