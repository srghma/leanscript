# More proposals to make the build and the checks faster

This follows `proposals/ExternCatalogueSpeed.md`. The two-level extern catalogue described
there is already in place. **This file only proposes changes.** Most of them have since been
implemented. For what was done, what was not, and the measurements, see
`proposals/BuildSpeedResults.md`.
Each section says what was measured, what could change, and what it would cost.

**How it was measured.** A machine with 8 cores and 64 GB, Lean v4.34.0, and Mathlib from
`lake exe cache get`. Absolute times on this machine are high and noisy. Even a file with no
imports takes about 2 s. The *ratios* are what matter. Two scripts reproduce the numbers:

- `scripts/profile_modules.sh` runs `lean -Dprofiler=true` on every module and prints a
  table of wall, import, elaboration, kernel and tactic time;
- `scripts/bench_mutual_vs_indexed.py` is the stand-alone benchmark for section 3.

Where a number is an estimate rather than a measurement, the text says so.

---

## 0. Where the time goes today

| what | measured |
| :--- | ---: |
| `lake update mathlib && lake exe cache get` (one-time setup) | 8 min, 5.8 GB of Mathlib `.olean`s |
| full `lake build` of the project (Mathlib already downloaded) | **16 min 42 s wall**, 57 min CPU |
| longest chain of imports (the *critical path*), 36 modules | ≈ 957 s of the ≈ 1000 s wall |
| share of per-module time spent *importing* (all 131 modules, 4 at a time) | **81 %** (2616 s of 3218 s) |
| modules whose own work (everything except importing) is under 5 s | 106 of 131 |

Three facts follow from this:

1. **The build is limited by its critical path, not by the number of cores.** The wall time
   is almost exactly the length of one chain of imports:
   `NonEmpty.* → LeanScript.Ty.* → Den → Den.Rec → Expr.Extern → Expr.Term →` the 13
   modules of `ToTerm/*` `→ TermTests.ArrayRecToTermTest`. Anything that shortens that
   chain shortens the build; anything off the chain barely matters.
2. **Most of each module's time is spent importing.** Without other load, a module that
   imports `LeanScript.Den` spends about 7 s importing. Measured examples:
   `ToTerm/Brec` 6.9 s, `ToTerm/Cache` 7.2 s, `CtorFn/Emit` 7.9 s, `Den` 7.0 s. By
   contrast, `Ty/Ty`, which imports neither `Lean` nor Mathlib, spends 1.6 s. Under the load
   of a parallel build the same imports took 40–60 s per module. For example,
   `ToTerm/Brec` took 62 s, of which 60.5 s was import and 0.2 s its own work.
3. **Only a few modules do much real work:**

| module | wall | import | elaboration | kernel | tactics |
| :--- | ---: | ---: | ---: | ---: | ---: |
| `TermTests/ArrayRecToTermTest` | 128 s | 8 s | 86 s | 28 s | 32 s |
| `LeanScript/Expr/Term` | 86 s | 49 s | 16 s | 30 s | 0 s |
| `TermTests/NatRecDepthTest` | 78 s | 12 s | 51 s | 13 s | 11 s |
| `LeanScript/Eval` | 71 s | 53 s | 7 s | 8 s | 0 s |
| `TermTests/RecUnionRecDepthTest` | 53 s | 18 s | 1 s | 28 s | 10 s |

(The columns overlap, because tactic time is counted inside elaboration. These runs were
4 at a time, so import times vary with the load.)

The proposals below are ordered by expected gain for the cost.

---

## 1. Shorten the critical path

### 1a. Split the two heavy test files at the end of the chain *(cheap, large gain)*

`TermTests/ArrayRecToTermTest` (128 s) is the last module on the critical path, and
`TermTests/NatRecDepthTest` (78 s) is close behind. Both are lists of independent blocks,
one per program (`sumArr`, `fibArr`, `tribArr`, `tetraArr`, `pentaArr`, and `fib`, `trib`, …
for `nat_rec`). If each block moved to its own file (`TermTests/ArrayRecToTermTest/Sum.lean`,
`…/Fib.lean`, …), the blocks would build in parallel. Each piece would pay its own import
(about 8 s without load), and the slowest block would set the time.

*Estimate, not measured:* the tail of the build drops from about 128 s to the slowest
block plus one import, roughly 30–40 s. This does not conflict with importing children one
by one, because the pieces are leaves and nothing imports them.

### 1b. Let the `ToTerm/*` modules build in parallel *(cheap to try, medium gain)*

The 13 modules of the translator form a strict chain: every file imports exactly the one
before it (`ObjectExpr → TyView → Ctx → Cache → Pieces → Match → Brec → Cases →
Existential → TransRec → TransBrec → Trans → Elab`). A name-based scan of which earlier
file's declarations each file actually mentions gives a much shallower graph:

| file | mentions declarations of |
| :--- | :--- |
| `TyView` | `ObjectExpr` |
| `Ctx` | `ObjectExpr`, `TyView` |
| `Cache` | *(none of the chain)* |
| `Pieces` | `ObjectExpr`, `Ctx` |
| `Match` | `Ctx` |
| `Brec` | *(none of the chain)* |
| `Cases` | `ObjectExpr`, `Ctx`, `Pieces` |
| `Existential` | `TyView`, `Ctx` |
| `TransRec` | `ObjectExpr`, `TyView`, `Ctx`, `Pieces`, `Match`, `Cases` |
| `TransBrec` | `TyView`, `Ctx`, `Pieces`, `Brec`, `TransRec` |
| `Trans` | `ObjectExpr`, `TyView`, `Ctx`, `Cache`, `Pieces`, `Match`, `Existential`, `TransRec`, `TransBrec` |
| `Elab` | `ObjectExpr`, `Ctx`, `Cache`, `TransRec`, `Trans` |

**This scan is a heuristic.** It matches names as text, so it misses instances and
notation, and a match can be a coincidence. If it holds, each file could import only
what it uses. `Cache`, `Brec`, `Match` and `Existential` would then leave the chain, and
its depth would drop from 13 to 9 (`ObjectExpr → TyView → Ctx → Pieces → Cases → TransRec
→ TransBrec → Trans → Elab`). That saves four imports plus their own work on the critical
path. Their own work is small, so the gain is mostly the four imports: about 30 s without
load and a few minutes under a parallel build. To check, change the imports and see
whether it still builds.

### 1c. Start the translator before `Expr.Term` is built *(riskier)*

`ToTerm/ObjectExpr` has `public meta import LeanScript.Expr.Term`, so the whole translator
waits for `Expr/Term.lean` (86 s, on the critical path). The translator is meta code. It
mostly needs `Term`'s constructor *names*, written as ``` ``Term.lam ``` (the double
backquote checks that the constant exists). If the names were written with a single
backquote (`` `LeanScript.Term.lam ``), the translator could build in parallel with
`Expr.Term`. A single test in `TermTests` would then check that every name the translator
emits exists. The cost is losing the compile-time check on names, and the translator's use
of `Term` may go beyond names. Try this only after 1a and 1b.

---

## 2. Make importing cheaper

Every module pays for its imports, and with 131 modules that is most of the build (section 0).

### 2a. Import only the parts of `Lean` that are needed *(cheap)*

Four library files have `public meta import Lean`: `CtorTag.lean`, `ToTerm/ObjectExpr.lean`,
`Ty/Deriving/Read.lean` and `Ty/WfTactic/Leaves.lean`. Because the import is `public`, every
module downstream of them loads all of `Lean`. Module counts and import times (no load,
two runs each):

| import | modules loaded | import time |
| :--- | ---: | ---: |
| nothing (only `Init`) | — | 1.8–2.1 s |
| `Lean.Elab.Command` | 996 | 2.3–3.5 s |
| `Lean.Elab.Tactic` | 2043 | 5.8–6.1 s |
| `Lean` | 2356 | 6.1–7.9 s |
| `LeanScript.Eval` (today) | 3120 | 7.7–11.7 s |

Where a file only defines commands or elaborators, `Lean.Elab.Command` (plus a few
`Lean.Meta.*` modules) is enough, and the import is two to three times cheaper. Files that
define tactics (`ty_wf`) need `Lean.Elab.Tactic`, so the saving there is small.

A second, independent step: make these imports non-`public` wherever the modules
downstream only use the *results* (the definitions the elaborators produce), not the
elaborators themselves. Then those modules do not load the meta code at all.

### 2b. Reconsider the Mathlib dependency *(your call)*

Only `LeanScript/Den/PFunctor.lean` imports Mathlib (`Mathlib.Data.PFunctor.Univariate.Basic`,
for `PFunctor` and `WType`). That one import brings in 722 modules: Mathlib 466,
Aesop 132, Batteries 73, Qq 14, Plausible 13, ProofWidgets 10, ImportGraph 10 and
LeanSearchClient 4. That is almost a quarter of what `LeanScript.Eval` loads.
- **Per-module import time:** the difference between `import Lean` and `import Lean` +
  that Mathlib module was within the noise here (6.1–7.9 s against 6.7–8.8 s). So this is
  not the main cost per module.
- **Setup and disk:** a fresh checkout needs about 8 minutes of `lake exe cache get` and
  5.8 GB before anything builds.
- **The manifest:** `lakefile.toml` requires `mathlib`, but the committed
  `lake-manifest.json` has no entry for it. So a fresh checkout does not build until
  `lake update mathlib` is run. Earlier sessions had to add the entry each time. For this
  report I added it only locally and did not commit the change.

Options: (i) keep Mathlib and commit the manifest entry; (ii) define the few pieces used
(`PFunctor` with `A`/`B`/`Obj`/`map`, and `WType` with `mk` and its recursor, about 40–60
lines) in the project and drop Mathlib, Batteries and Aesop from `lakefile.toml`. You chose
Mathlib's `PFunctor` on purpose earlier, so this is only a suggestion.

### 2c. Fewer, larger *light* test files *(cheap)*

Each module pays at least about 2 s here even with no imports, and about 7 s with the
project's usual imports. Of the 131 modules, 106 do less than 5 s of their own work. Merging
small test files that are *not* on the critical path saves one import per merge. This can
be done without an umbrella file, since each merged file still imports its own
dependencies directly. It pulls the opposite way from 1a: split the heavy files at the end
of the chain, and merge the light ones elsewhere.

---

## 3. Replace the 28-type `mutual` block with one indexed inductive *(large refactor, large gain for `Expr/Term.lean`)*

`LeanScript/Expr/Term.lean` declares **28 mutually recursive inductives with 136
constructors** (`Term`, `Terms`, `Spine`, `TaggedUnionCases`, …, `FamilyFoldKCases`). The
module is on the critical path, and its own work is about 45 s (16 s elaboration, 30 s
kernel). A trace of it shows:

| part of `mutual … end` in `Expr/Term.lean` | time |
| :--- | ---: |
| whole block | 29.9 s |
| kernel check of the 28 `….brecOn.go` (one per type) | 17.0 s |
| the inductive itself, `brecOn.eq`, `noConfusion` | ≈ 1.7 s |

Lean builds `brecOn` for every type in a mutual block, and each one carries a motive for
*all* 28 types. So the cost grows with the square of the block size. I tried two options
that turn off other generated declarations, `genInjectivity false` and `genSizeOfSpec
false`. Neither gave a measurable gain; that was a direct measurement on a copy of the
file. `brecOn` cannot be turned off.

**Proposal.** Declare one inductive, indexed by which family a node belongs to:

```lean
inductive Kind (Sg : Sig) where
  | term  (Γ : Ctx) (τ : TyWf)
  | terms (Γ : Ctx) (τ : TyWf)
  | spine (Γ : Ctx) (σs : List TyWf)
  | …                                -- one per current type, holding that type's indices
inductive Node (Sg : Sig) : Kind Sg → Type 1
  | lam … : Node Sg (.term (σ :: Γ) τ) → Node Sg (.term Γ (σ ⇒ τ))
  | …                                -- all 136 constructors
abbrev Term  Sg Γ τ  := Node Sg (.term Γ τ)
abbrev Terms Sg Γ τ  := Node Sg (.terms Γ τ)
…
```

**Synthetic measurement** (`scripts/bench_mutual_vs_indexed.py`, 28 types × 5 constructors,
no imports):

| | 28 mutual types | one indexed type |
| :--- | ---: | ---: |
| declaration: elaboration / kernel | 6.1 s / 16.3 s | 1.9 s / 2.5 s |
| declaration plus a structurally recursive `sz` and a builder (whole file) | 24.5 s | 13.8 s |
| the structural `sz` itself | 7–8 s per `mutual` block | 2.0 s |
| **evaluating** `sz` of a depth-10 tree with `decide +kernel` | **0.12 s** | **0.27 s** |

The declaration and every structural definition over the block get several times cheaper.
In the project, that means `Expr/Term.lean` and each `mutual` definition over `Term`: `Term.eval`
(5 s of pre-definition processing in `Eval.lean`), the `…RecFacts` files and `ToTerm/Brec`.
**Evaluation got slower, however.** Matching now also has to decide the index. The value
checks in `TermTests` are mostly evaluation, so they could lose some of the gain. Measure
on one test file before committing to this.

Cost: every `match` on a case family and every name like `TaggedUnionCases.cons` goes
through the abbreviations. Pattern matching on an indexed family usually works, but the
equation compiler and the translator's `` ``Term.x `` names all need checking. This is a
large refactor, and it could be combined with C3 of `proposals/ImprovementProposals.md` (unifying the
depth-indexed folds).

---

## 4. Faster value checks in the tests

### 4a. Use `decide +kernel` / `kernel_rfl` for all closed value checks *(cheap, measured)*

This was measured earlier and is recorded in `proposals/ExternCatalogueSpeed.md`. In a trial run,
switching every value check in `ArrayRecToTermTest.lean` to `kernel_rfl`/`decide +kernel`
took that file from about 105 s to about 49 s. Today only the three slowest checks use it.
Section 0 shows why the rest would help too: that file spends 86 s elaborating and only
28 s in the kernel, and `rfl` is checked by the elaborator first. The cost is error
messages: a wrong check is reported as a kernel type mismatch instead of `rfl`'s message.
A middle way is to keep `rfl` for the equations of the form `run f_term x = f x` and use
`decide +kernel` for the literal samples (`= 21`).

### 4b. Check bulk samples by compiled evaluation *(optional, not a proof)*

Now that every catalogue entry can be compiled (the "tag too big" fix), numeric samples can
be written as `#guard run fibArr_term #[1, 2, 3, 4] == 21`. These run compiled code and
cost almost nothing, but they are tests, not proofs. Keep a few proved checks per
program, and move the rest of the samples to `#guard`. Not measured.

### 4c. The `∀ n < 10` checks in `RecUnionRecDepthTest`

Each `example : ∀ n, n < 10 → runP … = …` takes about 4 s under `decide +kernel`, and the four such checks account for more than half of that
file's 28 s of kernel time. A smaller bound (for example `n < 6`) still passes
through every depth, and the cost grows quickly with `n` for these recursions. Whether the
larger range is worth it is up to you.

---

## 5. Faster *incremental* rebuilds: expose less

70 of the 72 files in `LeanScript/` start with `@[expose] public section`. Under the module system,
`@[expose]` makes every definition's *body* part of the module's interface. Changing any
body, even without changing its type, therefore rebuilds everything downstream. For the
lowest modules that is up to 116 of the 131 (`NonEmpty.DowngradeMap`, the
`NonEmpty.ListCorrectByConstruction.*` modules, `LeanScript.Ty.Schema.*`).

**Proposal.** Expose only what downstream modules need to reduce. That covers the
definitions behind `rfl`/`decide` checks (`Ty.Den`, `Term.eval`, `Extern.eval`, the
`…Den` functions) and anything the kernel must unfold. Everything else, such as meta-level
helpers, the tactic implementations and the `…Facts` files, could use a plain
`public section`. Test files that no other test imports need neither `public` nor
`@[expose]`. The `…/Programs.lean`, `…/Cont.lean` and similar test files that other tests
import need only what those tests reduce. Not measured. The gain is in edit–rebuild cycles, not in a build from scratch.

---

## 6. Workflow tips (no code change)

- **`lake env` costs about 5 s per call here.** A file with no imports took 7.4 s through
  `lake env lean` and 2.1 s through `lean` with `LEAN_PATH` set. Scripts that run many
  files should read `LEAN_PATH=$(lake env printenv LEAN_PATH)` once, as
  `scripts/profile_modules.sh` does.
- **Build only what you are working on.** `lake build LeanScript` skips the 39 test modules. `lake build TermTests.FibWindowTest` builds one test and what it imports. The
  default target builds all four libraries.
- **Find the slow declaration** with `lean -Dtrace.profiler=true
  -Dtrace.profiler.threshold=500 File.lean`. On a large test file this itself is very slow
  (over 15 minutes for `ArrayRecToTermTest` here), so use it on one small file at a time.

---

## Summary

| # | proposal | cost | expected gain | measured? |
| :- | :--- | :--- | :--- | :--- |
| 1a | split `ArrayRecToTermTest` and `NatRecDepthTest` into per-program files | small | tail of the build ≈ 128 s → ≈ 30–40 s | estimate |
| 1b | each `ToTerm/*` file imports only what it uses | small | chain 13 → 9 modules | heuristic scan |
| 1c | translator does not import `Expr.Term` | medium | translator builds in parallel with `Expr.Term` (86 s) | no |
| 2a | narrow `import Lean`; fewer `public meta` imports | small | about 2–3× cheaper import where it applies | import times measured |
| 2b | commit the Mathlib manifest entry, or drop Mathlib | small / medium | fresh checkout builds; drop saves 8 min, 5.8 GB and 722 modules | yes (setup); per-module effect within the noise |
| 2c | merge small light test files | small | ≈ 2–7 s of import per merged file | fixed cost measured |
| 3 | one indexed inductive instead of the 28-type `mutual` | large | `Expr/Term.lean` kernel 30 s → a few s; cheaper mutual definitions; evaluation possibly slower | synthetic |
| 4a | `decide +kernel`/`kernel_rfl` for closed checks | small | `ArrayRecToTermTest` ≈ 105 s → ≈ 49 s | yes (earlier trial) |
| 4b | `#guard` for bulk samples | small | almost free samples, but not proofs | no |
| 4c | smaller bounds in `∀ n < 10` checks | trivial | about 4 s per check, shrinking with the bound | per-check time measured |
| 5 | `@[expose]` only where reduction needs it | medium | fewer rebuilds after editing | no |
