# Build speed: what was implemented

This follows `proposals/BuildSpeedProposals.md`. It lists which proposals are now in the
code, what each one changed, and the measurements. **Proposal 3** (one indexed inductive
instead of the 28-type `mutual` block) was left out, as you asked.

## Result

All times were measured on the same machine as the proposals. Mathlib was already
downloaded, and the project's own `.lake/build` was deleted before each run.

| | before | after |
| :--- | ---: | ---: |
| full `lake build` (clean), wall | **10 min 06 s** | **5 min 43 s** |
| full `lake build` (clean), CPU (user) | 31 min 18 s | 23 min 03 s |
| slowest module after `Expr.Term` | `ArrayRecToTermTest` 117 s | `ArrayRecToTermTest/Tetra` 28 s |
| modules loaded by `import LeanScript.Ty.Instances` | 2 356 + Aesop | 932 |

Times on this machine are noisy, so treat differences of a few seconds as noise.
The build is still clean: no errors, no warnings and no `sorry`. The only `sorry`s are in
comments in `Expr/Term.lean` and `Expr/Design.lean`, and they were there before.

Today's longest chain of imports is:
`NonEmpty.* → Ty.* → Den → Den.Rec → Expr.Extern → Expr.Term (74 s) → Eval.Env → Eval.NoRecMk
→ Eval → FibWindowTest → RecUnionRecDepthTest.Programs → RecUnionRecDepthTest →
RecUnionRecDepthTest/RunFibToPenta`. `Expr.Term` is now the largest single piece of it,
and proposal 3 is what would shrink it.

## Implemented

### 1a. Heavy test files split, one file per program

- `TermTests/ArrayRecToTermTest.lean` became `TermTests/ArrayRecToTermTest/`: `Common`
  (`sig0`, `run`, `arrayRecDepth?` and the module doc), plus `Sum`, `Fib`, `Trib`, `Tetra`,
  `Penta` and `Acc`. `Acc` also holds the refused `adjArr`.
- `TermTests/NatRecDepthTest.lean` became `TermTests/NatRecDepthTest/`: `Common`
  (`sigAdd`, `envAdd`, `runAdd`), `Written` (`fibTerm` and its proof), `Fib` (`fibDef` and
  the refused `fibFastAux`), `FibLoops` (`fibLoopTR`, `fibTR`, `fibPair`, `fibLoop`),
  `Tribonacci`, `Tetranacci`, `Pentanacci` and `Hexanacci`.
- The same idea was applied to `TermTests/RecUnionRecDepthTest.lean`, the new last module
  of the chain (53 s). Its seven `∀ n, n < 10 → …` checks moved to
  `TermTests/RecUnionRecDepthTest/RunFibToPenta.lean` and `…/RunHexaLoopPair.lean`, which
  are checked in parallel. The bounds are unchanged.
- The `run`/`runAdd`/`runP` shorthands are now `scoped macro`s, so every file that
  opens the test's namespace can use them. No check was removed or weakened. Each split file
  imports only its own dependencies, and there is no umbrella file.
- Measured: the old 117 s and 77 s files became pieces of 18–28 s each, built in parallel.
  `RecUnionRecDepthTest` went from 53 s to 17 s, plus two pieces of about 20 s.

### 1b. `ToTerm/*` imports only what each module uses

Each translator module now imports the modules it uses, not simply the one before it.
There was one hidden use the name scan missed: `TransRec` uses `cacheRef` from `Cache`.
The chain went from 13 modules to 9: `ObjectExpr → TyView → Ctx → Pieces → Cases → TransRec
→ TransBrec → Trans → Elab`. `Cache`, `Match`, `Brec`, `Existential` and `Extern` now build
beside it. `LeanScript/ToTerm/Overview.lean` explains this rule.

### 1c. The translator no longer waits for `Expr.Term`

- `ToTerm/ObjectExpr.lean` and `CtorFn/Cache.lean` no longer import `LeanScript.Expr.Term`.
  They import only the modules below it (`Expr.Extern`, `ExprCtx`, …).
- In the translator and in `CtorFn/Emit.lean`, the names of the 28 types of `Expr/Term.lean`
  and of their constructors are now written with a single backquote
  (`` `LeanScript.Term.lam ``). All other names keep the checked double backquote.
- To keep the check on those names, there is a new test,
  `TermTests/ToTermTest/TermNames.lean`. It reads the translator's source files and fails
  if any such name is not a declaration of `Expr.Term`. It imports `LeanScript.ToTerm.Elab`,
  so it is rebuilt whenever the translator changes. I tested it by misspelling a name: it
  reported the file and the name.
- The convention is documented at the top of `ToTerm/ObjectExpr.lean`.
- Now everything from `ObjectExpr` to `TransBrec`, plus `CtorFn.Cache` … `Emit` and
  `Existential`, builds while `Expr.Term` (74 s) is still being checked. Only `CtorFn` and
  `ToTerm.Elab` still wait for it.

### 2a. Cheaper imports

- **Removed unused imports.** `import Aesop` appeared in 8 `NonEmpty/*CorrectByConstruction/*`
  files, and none of them used it. Because of those imports, every module above `NonEmpty`
  loaded Aesop's 500-odd modules. A non-public `import Lean` in 4 `NonEmpty` files was
  also unused.
- **Narrowed `public meta import Lean`:**
  - `Ty/WfTactic/Leaves.lean` now imports `Lean.Meta.AppBuilder` and
    `Lean.Elab.Tactic.Basic`.
  - `Ty/Deriving/Read.lean`, `CtorTag.lean` and `ToTerm/ObjectExpr.lean` now import
    `Lean.Elab.Command`.
  - `Ty/Deriving/Translate.lean` gains `Lean.Meta.Tactic.Delta` (for `deltaExpand`), and
    `Ty/Deriving.lean` gains `Lean.Elab.Deriving.Basic` (for `registerDerivingHandler`).
- **Measured, loading only the imports:**
  - `import LeanScript.Ty.Ty`: about 3 s and 771 modules, instead of pulling in Aesop.
  - `LeanScript.Ty.Instances`: 932 modules. `LeanScript.Ty.Deriving`: 1 030 modules.
  - Before, every one of these loaded more than all of `Lean` (2 356 modules, about 7 s).
  - The effect is on the `NonEmpty.*`/`Ty.*` part of the chain, where the modules now take
    1–6 s each. Modules above `Den` still load Mathlib, so they gain little.
- **Not possible here:** making `public meta import`s non-public. `ctor_tag` and `ty_wf`
  are the default tactics of arguments (`:= by ctor_tag`, `:= by ty_wf`). So every module
  that writes a `Term` or a `TyWf` must see them, and those imports have to stay public.

### 4a. Kernel-only value checks

- In `TermTests`, 297 closed `example … := rfl` checks now use `:= by kernel_rfl`, and 31
  `:= by decide` checks now use `:= by decide +kernel`. They are still proofs, checked by
  the kernel. Only the error message on a failure changes (a kernel type mismatch).
- Every test file that uses `kernel_rfl` imports `LeanScript.KernelRfl`.
- I checked that a false `example : 2 + 2 = 5 := by kernel_rfl` is rejected.
- Docs that said "checked by `rfl`" were updated.
- Measured: `EvalTest` went from 43 s to 29 s, `FibWindowTest` from 42 s to 29 s and
  `NatRecDepthTest/FibLoops` from 51 s to 23 s. Other files changed within the noise.

## Not implemented

- **3 (indexed inductive):** left out, as you asked.
- **2b (Mathlib):** not changed, per your answer. `lake-manifest.json` still has no
  Mathlib entry, so a fresh checkout needs `lake update mathlib` first. I added the entry
  locally to build and did **not** commit it.
- **4b (`#guard` samples) and 4c (smaller bounds):** not done, per your answer. Every
  check is still a proof, with the same arguments and bounds.
- **2c (merging light test files):** not done.
  - After 2a, the light test files (`TyTests/*`) load their imports in about 3 s, and none
    of them is on the longest chain. So merging them would save about 1 % of CPU and nothing
    in wall time.
  - Merging would also give up the per-topic files. `TyTests/CrossModuleSharingTest` has
    to stay a separate module, because that is what it tests.
- **5 (`@[expose]` only where needed):** tried and measured. It does not apply, so all
  files were left as they were:
  - Lake does skip downstream rebuilds when only a non-exposed part changes. Changing a
    proof in `Ty/WfFacts.lean` rebuilt that file only.
  - For **meta** modules (`ToTerm/*`, `Ty/Deriving/*`, `Ty/WfTactic/*`, `CtorFn/*`),
    removing `@[expose]` does not help. A `meta import` also depends on the compiled
    code, so changing a body in `ToTerm/Brec.lean` still rebuilt `TransBrec`, `Trans` and
    `Elab`.
  - The `…Facts` files need their definitions exposed. Without `@[expose]`, their own
    `rfl` lemmas and projections fail (`ArrayRecFacts`, `RecUnionEvalFacts`, `WfFacts`),
    and so do downstream tests (`NatRecKTest`). `RecAliasRecFacts` and `RecObjectRecFacts`
    contain no definitions, so the attribute has no effect there.
- **6 (workflow tips):** these are not code changes. The tips still apply.
