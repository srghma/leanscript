# No `JsTerm → JsTerm` optimisation stage: is it possible?

> **Status (current tree): there is no `JsTerm → JsTerm` stage at all.**  Everything below
> describes an intermediate state.  Since then `JsTerm/Passes/` and `JsTerm/Lower/Emit.lean`
> were deleted: `termToJs` builds each block directly (`JsTerm/Lower/FromTerm.lean`, with
> `JsTerm/Lower/Tail.lean` for returns as loop assignments or jumps), `inPlace` is gone (array
> updates are the copying `…_immutable` operations), and `mkModule` (`JsTerm/Lower/Module.lean`)
> only collects the imports.  `JsTerm` is used only to print the JavaScript and to connect it to
> `runtime.js`; every optimisation is on `Term` (`Term.optimize`, proved by `Term.optimize_eval`).
> The generated JavaScript is larger than with the former passes; all the snapshot checks pass.
> The pipeline is now
>
> ```
> Lean ─elab/translate→ Term ─Term.optimizeN (proved: Term.optimizeN_eval)→ Term
>      ─termToJs→ JsTerm ─mkModule (imports)→ JsModule ─toMini→ MiniJs ─print→ string
> ```

Short answer: **mostly yes, and it is now done for the function level.**  The JavaScript of a
function is emitted in normal form while `Term → JsTerm` builds it; no pass rewrites a finished
function except `inPlace`.  What still runs over finished `JsTerm` is (1) `inPlace` and (2) the
module assembly `mkModule`.  Neither can be removed today without losing an optimisation; the
reasons and the way to remove them are below.  No optimisation was dropped: every generated
`.js` snapshot is byte-identical to the one the former pipeline produced, and the Term-level
optimiser gained one proven pass.

## The pipeline now

```
Lean ─elab/translate→ Term ─Term.optimizeN (proved: Term.optimizeN_eval)→ Term
     ─termToJs (emits normal-form JsTerm: all function-level rules applied during generation)→ JsTerm
     ─inPlace (whole-function ownership analysis)→ JsTerm
     ─mkModule (hoisting / module-constant inlining / sharing = building the module)→ JsModule
     ─toMini→ MiniJs ─print→ string
```

### What changed

1. **`JsTerm/Lower/Emit.lean` (new).**  `JsBlock.emit` is a *smart constructor*: every block
   the conversion builds (`JsTerm/Lower/FromTerm.lean`) is passed through it.  Its children
   are already in normal form, so it only applies the rules at the new node; when a rule
   rewrites it (copy propagation or a constant used once substitutes into the rest of the
   block, which can enable further rules there) the rewritten statement is renormalised
   (`JsBlock.normalize`, to a fixpoint).  The rules are exactly the former function-level
   passes, now as node rules:
   * `emitExprRules` — array-literal flattening and β-reduction of returned closures
     (`flattenNode`, `betaNode`);
   * `emitBlockRules` — `cleanupNode` (copy propagation, self-assignments, rebuilt unions,
     unused pattern fields, constants used once right away), `peepholeNode`,
     `inlineArrayNode`, and `tidyStep` (unboxing / scalar replacement of accumulators,
     join-point flattening, contification, dead constants, coalescing, hoisting assignments,
     closure-chain TCO, narrowing, arithmetic).
   A few rules are only valid when no closure of the function reads a mutable variable
   (`noCapture`).  That is a property of the whole function, so `termToJs` first runs the
   conversion once with no rules (`EmitCfg.rules := false`) to decide it, then runs the real
   conversion.
2. **`termToJs`** no longer calls `cleanup`, `peephole`, `inlineArrays`, `tidy`; the unused
   whole-function drivers `tidy` (`Contify.lean`) and `inlineArrays` (`Simplify.lean`) were
   deleted.
3. **Term level:** `LeanScript/Term/Optimize/Cond.lean` adds `Term.condWalk` to
   `Term.optimize` (`… .cseWalk.condWalk.dce`): `c ? true : false` is `c`, and a conditional
   (value or `if` branch) on a negation `c ? false : true` swaps its arms.  Proved:
   `*.condWalk_eval` (value preserved, hence `Term.optimize_eval` / `Term.optimizeN_eval`
   still hold, axioms: `propext`, `Classical.choice`, `Quot.sound`) and `*.numCalls_condWalk`
   (never adds calls).  It improves `Term-optimized.txt` snapshots (e.g.
   `cond(cond(cond(cond(x2,false,true),x4,false),true,false),true,false)` → `cond(x2,false,x4)`
   in `PrimOpBoolean01`, `InlineClosures`, `InlineReferencePrimOpInt`); the JavaScript was
   already simplified by the JsTerm rules, so it is unchanged.

Verification: `lake build leanscript tests JsTerm TermTests TyTests` succeeds; all JavaScript
snapshots in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` regenerate byte-identically
(only the three `Term-optimized.txt` files above change, all improvements); the test runner
passes 61/61.

A single bottom-up pass *without* renormalisation was also tried: it changed 21 snapshot
files (missed optimisations), so renormalising a rewritten node is necessary to keep "none
missed".

## Placement of each optimisation

How often each rule fired (instrumented run over the whole snapshot corpus, both presets,
before the change; counts are rewrites):

| Rule | fired | Kind | Where it lives now | Could it move to `Term`? |
| :--- | ---: | :--- | :--- | :--- |
| `inlineOnce` (constant used once) | 512 | lowering cleanup | at generation | partly: Term `dce`/`simp` already do it for Term lets; the JsTerm ones come from lowering (ANF temporaries, join points) |
| array-literal `flatten` | 195 | lowering cleanup (appends → spreads) | at generation | no: spreads exist only in JS |
| `inlineArrayNode` | 191 | lowering cleanup | at generation | no (same) |
| copy propagation | 181 | lowering cleanup | at generation | Term copies are already removed by `Term.simp`; these are copies the lowering creates |
| `peephole` | 172 | lowering cleanup | at generation | no: `return`/`break`/join-point shapes |
| self-assignment | 38 | imperative | at generation | no |
| rebuilt union | 36 | lowering cleanup | at generation | no (union representation is JS-specific) |
| `narrow` | 36 | target-specific | at generation | no |
| β of returned closure | 36 | functional | at generation | yes in principle (needs a Term inliner, see below) |
| `unbox` accumulator | 32 | imperative/loops | at generation | the idea yes (ForInStep accumulator), the result is a mutable variable: no |
| `copyMut` | 29 | imperative | at generation | no |
| closure-chain TCO | 22 | loops | at generation | the recognition is Term-expressible (function-accumulator `nat_rec`), the loop is not |
| contification | 18 | join points | at generation | no (targets JS labelled blocks) |
| `retBeta`, `flattenJoin`, `deadConst`, cond, `coalesce` | 16 each | mixed | at generation | the cond rule is now also at Term level (`condWalk`) |
| scalar replacement | 14 | imperative | at generation | no |
| arithmetic | 10 | target-specific | at generation | no |
| `unionKnown`, `destructKnown` | 0 | — | at generation | — |
| `inPlace` | 4 functions (`ArrayInPlace`) | ownership | after generation | see below |
| module `hoistConsts` | 44 modules | module sharing | `mkModule` | no (module scope) |
| module `inlineConsts` | 33 functions (`AppArity`, `ArrayInPlace`, `AssignSteps`, `InlineClosures`, `InlineDemo`, `LoopClosure`, `ScalarRepl`, `TcoAck`) | β-inlining across definitions | `mkModule` | **yes, belongs in Term** (see below) |
| module `shareFuns` | 51 | module sharing | `mkModule` | no (module scope) |
| module re-`peephole`/`cleanup`/`simplifyExprs` after hoisting | 0 changes on the corpus | cleanup | `mkModule` | kept for safety; they only clean what hoisting/inlining leave |

## What still runs over finished `JsTerm`, and why

1. **`inPlace`** (arrays nothing else refers to are updated in place).  It needs an
   ownership/liveness analysis of the *whole* function (every later read of the array), so it
   cannot be a local rule at a node.  To remove it from JsTerm, `Term` needs a uniqueness
   analysis (the usage annotations `[1]`/`[ω]` already carry most of this) that marks array
   operations as in-place, which the conversion would then emit directly.  This is a feature
   to add, not a missing optimisation.
2. **`mkModule`.**  `hoistConsts` and `shareFuns` operate across the functions of one `.js`
   module; they *are* the construction of the module (which constants exist at the top, which
   exports alias others), so they are part of generation, not a JsTerm→JsTerm stage in the
   sense of the table's "module-level sharing" row.  `inlineConsts` is different: it inlines
   known closures of the module into their call sites and re-cleans the result.  That is a
   functional optimisation that belongs in `Term.optimize`.  Moving it requires a Term-level
   inliner (substituting a closed `Val.lam` into its calls across levels/join-point contexts,
   with re-leveling and an `_eval` proof) — the one remaining piece of work to make the JsTerm
   stage purely "build the module".

## Conclusion

* All function-level JsTerm optimisations (lowering cleanups, loops/accumulators,
  target-specific rules) now happen **during** Term → JsTerm generation, with identical
  output.
* Purely functional optimisations are in `Term.optimize` with proofs against `Term.eval`;
  one new one (`condWalk`) was added.
* Remaining post-generation work: `inPlace` (needs Term-level uniqueness analysis) and the
  module-constant inliner `inlineConsts` (needs a proven Term inliner).  Removing either today
  would lose optimisations, so they were kept.
