# No `JsTerm → JsTerm` optimisation stage: is it possible?

> **Status (current tree): there is no `JsTerm → JsTerm` stage at all.**  Everything below
> describes an intermediate state.  Since then `JsTerm/Passes/` and `JsTerm/Lower/Emit.lean`
> were deleted: `termToJs` builds each block directly (`JsTerm/Lower/FromTerm.lean`, with
> `JsTerm/Lower/Tail.lean` for returns as loop assignments or jumps), `inPlace` is gone (array
> updates are the copying `…_immutable` operations), and `mkModule` (`JsTerm/Lower/Module.lean`)
> only collects the imports.  `JsTerm` is used only to print the JavaScript and to connect it to
> `runtime.js`; every optimisation is on `Term` (`Term.optimize`, proved by `Term.optimize_eval`).
> The generated JavaScript is larger than with the former passes; all the snapshot checks pass.
>
> **Update: `inPlace` is back, at the `Term` level.**  The whole-function uniqueness analysis
> this document asked for now exists on `Term` (`LeanScript/Term/Ownership/Basic.lean`,
> `Walk.lean`): it tracks owned/borrowed arrays through the optimised `Term`, and `termToJs`
> emits `…_mutable` updates directly where the array is owned and dead afterwards (no pass
> over the finished `JsTerm`).  It also chooses, per function, versions owning some
> array parameters (`OwnedTerm`, generated as extra exports `f$$mut_i_j`), and loop
> accumulators that are copied once before the loop instead of once per iteration.  On
> `ArrayInPlace`, `test1`/`test5` update in place, `test3` copies its parameter once before
> the loop, and `test3$$mut_0` does not copy at all.  The analysis is unproved (it does not
> change `Term.eval`; the snapshot checks run every version).  The module-constant inliner
> `inlineConsts` stays out: a proven Term-level inliner across definitions is still the open
> piece of work described below.
> **Update: the analysis now reaches inside functions.**  Local functions that are not
> inlined get versions too (`Own.lamPlan`: one constant per way their calls give up array
> arguments, the call choosing the version owning the most, and owned answers when the version
> answers new arrays); loops whose accumulator is a function build *owning closures*
> (`Own.AccMode.ownFn`: the closures of a structural recursion with an array accumulator own
> their argument, and a call copies an argument its caller keeps); folds over declared
> datatypes own the answers at the holes of their layers (`Own.dataRecOwns`); a conditional
> consumes an array in either arm.  `ArrayInPlace.test6`, `InlineClosures.downFrom`,
> `RecData.toArray`/`inorder`/`reverse`/`sort`, `MapFilter.test5` and `ArrayFSet` now update
> in place where they copied before.
> **Update: a first Term-level inliner.**  `Term.inlineKnown`
> (`LeanScript/Term/Optimize/Inline.lean`, run first in `Term.optimize`) inlines a known
> closure whose body is closed and only computes a pure expression of its parameter
> (`val k := fun x => ret e[x]`) at its calls: `let y := k a` becomes `let y := share e[a]`
> when `e[a]` is a neutral expression of the call's level; `Term.dce` then drops `k`.  It
> walks the term with what is known about every known variable in scope (`KInfo`, moved
> along `val`s by weakening and into closed bodies by masking).  Proved:
> `Term.inlineKnown_eval` (value preserved, so `Term.optimize_eval`/`Term.optimizeN_eval`
> still hold) and `Term.numCalls_inlineKnown` (no call added).  This is the first case of the
> former `inlineConsts`; on the snapshots it removes the helper closures of
> `InlineDemo.useScale`/`useTriple` and `LocalFnInPlace` (6 calls).  Still missing (the rest of
> `inlineConsts`): calls whose result is not neutral (a literal, `fun _ => "a"` in
> `FunctionCompose01`; a data literal in `OptionUnbox`, `RecData`), closures whose body is a
> block, and closures passed to closures (`InlineClosures.sumShifted`), which need
> substitution of *known* values with renormalisation and re-levelling.
> **Update: inlining in tail position and of single-use closures.**  `Term.inlineRet`
> (`LeanScript/Term/Optimize/InlineRet.lean`, `InlineBlock.lean`, run after `Term.condWalk`
> in `Term.optimize`) walks the term letting the level index change (a re-levelling renaming
> `Term.relvl`, `LeanScript/Term/Rename/Relevel.lean`, proved by `Term.relvl_eval`).  It
> rewrites a tail call `let y := k a; ret y` of a known closure `fun x => ret e` into
> `ret e[a]` whatever `e[a]` is (literals, constants and data literals included), drops dead
> bindings whatever their level, and inlines a known closure *used once* whose closed body
> makes no call at a call on a neutral argument: the body is re-levelled, and its answer bound
> to the call's result (through a new join point when the body ends in a branch).  Proved:
> `Term.inlineRet_eval` (so `Term.optimize_eval` still holds) and `Term.numCalls_inlineRet`.
> On the snapshots `FunctionCompose01` collapses to `(a) => "a"`, and the helper closures of
> `RecData` (`sumArray`, `reverse`, `sort`), `OwnershipAliasing`, `BranchSpecialization01`
> and `KnownConstructors` are inlined.  Still missing from the former `inlineConsts`: calls
> on non-neutral arguments (record literals), bodies that make calls, closures used several
> times whose body is not a single `ret e`, closures returning closures (`AppArity`) and
> closures passed to closures (`InlineClosures.sumShifted`).  Fusion, constructor
> specialisation and unboxing of parameters are not done.
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
