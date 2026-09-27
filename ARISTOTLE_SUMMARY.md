# Summary of changes for run 7e4d2587-f0c8-4b3a-8042-c199d13f7ae9
I implemented `MoreJsTy`, a configurable Term→MoreJsTy converter, a printer that goes through `LanguageJavascriptMini`, and the `leanscript` executable. I ran it on every `Tests/SnapshotsMy/*.lean`. Many functions in those files can't be translated yet (see below), so several files export nothing. For every function that was translated, the generated JavaScript gives the same answers as Lean on sample inputs.

**What was built**
- **`MoreJsTy/`**
  - `Config.lean`: `JsConfig`, with a setting per type: `Nat`, `Int`, `UInt64`, `Int64` and wide `BitVec` become either a `number` or a `BigInt`; arrays can be typed or generic. There are two presets, `faithful` (the default) and `pbo`.
  - `Ty.lean`: the `MoreJsTy` layouts. With `nat=num`, a `Nat` is a `uint53` that throws on overflow; with `bigint` it is a JS `BigInt`. The type conversion uses `lowerScalarPrim`, `lowerArrayPrim` and `lowerTy`.
  - `Syntax.lean`: the JavaScript grammar and the `-MoreJsTy.txt` dump.
  - `Extern.lean`: externs become inline JS or runtime helpers.
  - `FromTerm.lean`: the converter `termToJs`.
  - `PrintMini.lean`: the printer.
- **`leanscript`**: set it up with `scripts/install-leanscript.sh`, which builds it and links `./.lake/bin/leanscript`. It takes a file path or a module name such as `SnapshotsMy.TcoAck`.
  - It elaborates the file and keeps the public, structurally total, computable definitions. For each one it reads the `Expr`, translates it to a `Term`, optimises it with the proved-correct `Term.optimizeN`, converts it to `MoreJsTy` and prints it.
  - It writes `FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`, `FILE-MoreJsTy.txt` and `FILE.js` (runtime helpers, then `export function …`).
  - Each output starts with the configuration and lists every definition it didn't translate, with the reason.
  - With `--check` it also writes `FILE.check.mjs`, which calls each exported function on sample arguments and compares the result with Lean's own answer.
  - `scripts/leanscript-snapshots.sh` runs everything on `Tests/SnapshotsMy` and runs the checks with node.

**Results**
- 21 of the 46 `Tests/SnapshotsMy` files export at least one function.
- Every generated `.js` file passes `node --check`.
- All differential checks pass, under both the `faithful` and the `pbo` preset (AppArity 129, PrimOpFloat 135, SafeGuards 51, …).
- Under `pbo`, an overflowing multiplication throws as intended.
- For `TcoAck`, only `pair` is translated. `ack`, `ack2` and `ack999` are refused as partial (`ack999` is a value that can't be computed at compile time). `ackWhile` needs `List` and is refused. The Cantor-pairing `while` loops are refused because the translator can't see that they terminate.
- `lake build` succeeds, and `lake exe tests` passes 38/38, including 7 new `MoreJsTy` specs.

**Fixes along the way**
- `Float`/`Float32` are now leaf types in `LeanScript/GenElab/Read.lean`. Before this, every Float function failed to translate.
- I added JS implementations for `String.Pos.Raw.set` and `extract`, and an array-index conversion that never throws.

**Things to be aware of**
- The old backend's snapshot files (`GcdEntry.js`, the `*.test.js` files, `Html-test*`, …) would have been overwritten or no longer matched the new output. They are kept unchanged in `Tests/SnapshotsMy/legacy-backend/`.
- None of the converter, printer or CLI is formally proved; it is covered by tests only. The Properties table lists `MoreJsTy`, `JsConfig`, `termToJs` and `JsModule.toJs` as definitions.

**Not done yet** (listed in `NOT_IMPLEMENTED.md` §4, with a new section in `README.md`)
- Declared datatypes (`List`, user inductives) aren't converted to JavaScript. This is the most common reason a snapshot function isn't translated.
- Some externs are emitted as helpers that throw when called.
- String `<` compares UTF-16 code units, where Lean compares code points.
- Functions whose body isn't a plain chain of lambdas are exported curried, e.g. `ack2(m)(n)`.
- The translator reports "invalid scope" on `ScalarRepl.test6`; I didn't look into it.

# Summary of changes for run 87949201-4522-467b-b735-28c81c558794
I proved Church–Rosser for rewriting under `Term.eval`. Everything builds with no `sorry`, and the main theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

**How I read the request.** `Term.eval` is a function, not a reduction relation. In a normal-form `Term` every elimination is stuck on an unknown, so there is no beta-reduction whose confluence could be proved. So I defined a rewrite relation, `Term.Step`, made of the optimiser's and dead-code elimination's rewrites, and proved Church–Rosser for that relation.

**The rewrite relation** (`LeanScript/Term/Step.lean`). `Term.Step t t'` means one rewrite applied anywhere inside `t` (inside `let`s, closure bodies, delays, loops, branches and join points). The rules are:
- drop a dead `val`, `let`, `record_casesOn` or `join`;
- copy propagation: `let x := share y; b` becomes `b[x := y]`;
- `let x := share n; ret x` becomes `ret n`, and the same for `jump`.

`Term.Step.eval` proves that every step leaves `Term.eval` unchanged, in every environment.

**Main results** (`LeanScript/Term/ChurchRosser.lean`):
- `Term.Step.diamond` / `Term.Step.stronglyConfluent`: when two single steps diverge, each side reaches a common term in at most one step.
- `Term.Step.confluent` and `Term.Step.churchRosser`.
- `Term.eval_churchRosser`: two terms connected by rewrites in either direction both rewrite to a common term with the same `eval` value. `Term.eval_confluent` and `Term.run_churchRosser` (for whole programs) are variants.
- `Term.Step.normal_unique`: normal forms are unique.

**Link to the optimiser** (`LeanScript/Term/SimpStep.lean`). `Term.simp_star` shows that the optimiser's rewriting pass `Term.simp` is a sequence of `Term.Step`s. From that, `Term.simp_joinable` follows: its result can be joined with any other sequence of rewrites, at a term with the original value.

**Supporting files:**
- `LeanScript/Term/RenameComp.lean`: composing renamings.
- `LeanScript/Term/StepRename.lean`: steps commute with renaming.
- `LeanScript/Term/StepInv.lean`: case analysis on steps.
- `LeanScript/Term/Rewriting.lean`: generic confluence theory, including "strongly confluent implies confluent".

There are example checks in `Tests/TermTests/ChurchRosserTest.lean`, the README has a new row describing these files, and the Properties table lists the definition and the proved theorems.

**Build problem.** `lakefile.toml` requires `mathlib`, but `lake-manifest.json` has no entry for it, so `lake` refuses to build ("dependency 'mathlib' not in manifest"). To build and check the work I removed that `require` block locally. I have put the lakefile back exactly as it was and did not commit that change. Because of this I can't list build targets as verified in the current configuration. To build, either remove the unused `mathlib` requirement or add it to the manifest (`lake update`).

# Summary of changes for run 47efb8f5-ae35-4622-8e9a-7f818a4a8859
I proved that `Term.eval` on a closed term, with every variable known, always returns a completely normalised value. The new file is `LeanScript/Term/NormalValue.lean`. It builds with no errors or warnings and contains no `sorry`. Both theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

**How I made the claim precise.** `Term.eval` returns a Lean value (`Ty.Den Δ τ`), not a term. So I defined what a completely normalised value is, and a way to read one back as a Lean value:
- `NVal` (with `NArgs`, `NElems` and `NEnv` for its parts) is built from constructors at every level:
  - literals, enum constructors, records, union constructors, arrays, lists and datatype layers, whose parts are all completely normalised;
  - delays (thunk or lazy) that already hold their completely normalised value;
  - closures (`lam`): a closed body in the existing normal-form grammar, together with completely normalised values for every known value it can see.
- `NVal.den` turns one into a Lean value, the same way `Term.eval` does.

**Theorems (proved):**
- `Term.eval_normal`: take a term with no unknown in scope, no open known value and no join point, whose known values are themselves completely normalised (`nκ`). Then there is an `n : NVal Δ τ` with `n.den = t.eval nκ.den PUnit.unit PUnit.unit`.
- `Term.run_normal`: as a special case, the result of every whole program `t.run` is the Lean value of some `NVal`.

The proof goes through each form of pure expression, value, body and term. The cases that could not be normalised (neutral expressions, computations, branches and jumps) cannot occur in a closed term, which the existing lemmas in `Closed.lean` already show.

**What the statement does and does not say.** At a type with no function inside, every Lean value can be written as some `NVal`, so there the theorem adds nothing. What it adds is about functions, including functions inside records, unions, arrays and datatypes: every function `Term.eval` returns in this setting comes from a syntactic closure over completely normalised values. It does not normalise inside a closure's body. That body is kept as a term, but it is already in the normal-form grammar.

`README.md` has a new row for this file. I added three entries to the Properties table.

**Build problem you need to fix.** `lakefile.toml` requires Mathlib, but `lake-manifest.json` has no entry for it, so `lake build` fails immediately with "dependency 'mathlib' not in manifest". I did not change your lakefile. To build here I removed the Mathlib requirement temporarily, then restored it before committing. Running `lake update mathlib`, or removing that requirement, would make the project build again. Because of this I am not listing any build targets as checked.

# Summary of changes for run 49a7f4b1-69fb-4629-98c0-1b1ab067b6a7
All requested items are done and committed. The full `lake build` passes with no errors or warnings. `lake test` passes 31/31. There is no `sorry`, `axiom` or `implemented_by`. `Term.optimize_eval` uses only `propext`, `Classical.choice` and `Quot.sound`.

**HashableFloat and Mathlib**
- The three files moved from `LeanScript/HashableFloat/` to `HashableFloat/`, which is now its own library (added to `lakefile.toml` and the default targets). Imports are updated.
- The Mathlib `v4.34.0` requirement is back in `lakefile.toml`, and `lake-manifest.json` has matching entries.
- Using Mathlib to remove duplication: `LeanScript/Term/UsageAlgebra.lean` gives usages Mathlib's `AddCommMonoid` and `LinearOrder` instances. The hand-proved `add_comm`, `add_assoc`, `max_comm`, `max_assoc` and `max_self` are now one-line uses of Mathlib's lemmas.
- This module is deliberately not imported by the rest of the project. When I imported Mathlib into the core, many `#guard_msgs` snapshots broke (`Nat` prints as `ℕ`) and Mathlib's linters added 46 warnings.
- I checked other candidates and left them: `Tuple` has no trailing `PUnit`, so it is not `List.TProd`; `IPF`/`IW` differ from `MvPFunctor`; Mathlib's `Finset` sums would slow down kernel evaluation.

**Skipped tests**
- I timed each skipped command separately. Anything at or above about 0.5 s moved to `Tests/Main.lean`; everything else is restored in place.
- Moved:
  - `WhileTest`: five `kernel_rfl` runs, including `bits 1000` at about 18 s;
  - `QuotientTest`: one;
  - `RoseVariantsTest`: four;
  - `TcoTest`: all 11 value checks.
- Each old location has a comment pointing to `Tests/Main.lean`.
- `Tests/Main.lean` uses `Spec`. It checks each translation, compiled, against the expected value and against the compiled Lean function. Each check takes a few milliseconds.
- Restoring fixed `BlocksTest`, which had failed because commenting out an `example` left its `#guard_msgs` applying to the wrong command. To make its definitions importable, `TcoTest` is now a public section and `ackInner` is no longer private.

**Why `hyperTCOT_run` needed 4,000,000 heartbeats**
- It was not the kernel. `refine key _ ?_ n b` made the elaborator find the helper's function by higher-order unification through `Term.eval`, which took about 30 s.
- The new proof first has the kernel evaluate the term's shape with `kernel_rfl`, with the arguments left as variables. That shape is two nested `natIter`s over `hyperBaseT.run`. The rest is an induction on the Lean side only.
- It now takes about 0.3 s with default heartbeats, and the whole file dropped from 60 s to about 9 s.
- The value checks are slow in the kernel because it unfolds `Term.eval` through the recursors of the term families, and every `natIter` step. The evaluator itself was not changed; compiled, the same runs take microseconds.

**Optimizer** (`LeanScript/Term/Optimize.lean`)
- `Term.optimize` walks a term the way `Term.eval` does and applies three rewrites, then dead-code elimination (`Term.dce`):
  - copy propagation: `let x := share y` where `y` is an unknown of the same level;
  - `let x := share n; ret x` becomes `ret n` (the same for `jump`);
  - a `record_casesOn` whose fields are never read is dropped.
- A rewrite is skipped whenever it would change the term's level index.
- **Proved:** `Term.optimize_eval` (same value in every environment), `Term.optimize_run` (same program result), and the same for `Term.optimizeN` (run `k` times).
- `TermTests/OptimizeTest.lean` checks that each rewrite fires on a small term (by `rfl`), and that a term with none of the patterns is unchanged. `Tests/Main.lean` also checks the optimized translations on values.
- The optimizer is modest: no common-subexpression elimination and no inlining (see `NOT_IMPLEMENTED.md`).

`README.md` and `NOT_IMPLEMENTED.md` are updated.

# Summary of changes for run b4f840b7-c6bc-4f88-aeb9-4304a2d62ece
This was a refactoring task, so "formalizing" here meant doing in Lean the split of `LeanScript/TermElab/ToTerm/Expr.lean` that I had left out last time. There is no new theorem to state or prove. The full `lake build` passes (134 jobs, no errors or warnings), including all the `TermTests` that run `#leanscript_to_term`. A search finds no `sorry` in the new files.

**What changed:** `Expr.lean` (943 lines) was one large block of mutually recursive functions. It could not be split as it was, because everything calls back into the translator `tr`. Now every function except `tr`, `trProj` and `trApp` takes `tr` as an ordinary argument, so it can live in its own file. The new files in `LeanScript/TermElab/ToTerm/Expr/` are:
- `Loops.lean` (100 lines): `for`/`while` loops and applications (`trStepLoop`, `appArgs`, `trRangeFor`, `trWhile`).
- `Calls.lean` (243 lines): `trHelperCall`, `defaultTerm`, `trFinFoldl`, `trQuotApp`, `wrapperField?`, `externCall`, `trExtern`, `trDecide`.
- `Ctor.lean` (118 lines): `trOptField`, `trCtor`.
- `Cases.lean` (312 lines): `tyOf?`, `nestView?`, `trFoldl`, `trNestFoldl`, `trRecCall`, `peelCases`, `recBranch`, `trCases`.

`Expr.lean` (280 lines) keeps only the three core functions, which pass themselves to the helpers (for example `trCases tr L c args e`). `wrapperField?` and `peelCases` don't use `tr`, so they don't take it. Other than adding the `tr` argument, I only moved code. I checked this with a diff that ignores the added argument: it shows no other change to code or error messages. Functions outside these files still call only `tr`, so their imports are unchanged.

**Earlier in this session, for reference:**
- `TermElab/Anf.lean` is split into `Anf/{Src,Sem,Render,Emit}.lean`.
- `Term/ExternEval/FixedWidth.lean` is replaced by `UInt.lean` and `SInt.lean`.
- `GenElab/Read.lean` is split into `Read/{Base,Nest}.lean`.

`README.md` and `NOT_IMPLEMENTED.md` point to the new file locations. No Lean file in the build is now longer than 540 lines. All work is committed.

# Summary of changes for run 9c4cc405-0bc5-40f6-af3c-f338a43170b8
The old `Term` is gone. The normal-form grammar (previously `NTerm`) is now `LeanScript.Term`, in `LeanScript/Term/*.lean`. As you asked, I did not write a verified normaliser: the elaborators build the new terms through the existing unverified normaliser in `Anf`. The full `lake build` passes (123 jobs), and a search finds no `sorry`, `axiom` or `implemented_by`.

**What is in place:**
- **Two usage types:** `Usage1ω` for definition binders (`letV`, `letE`, join points) and `Usage01ω` for pattern binders (case fields and closure, loop and join-point parameters). Both are enforced in the constructor types. Nothing checks an annotation against how the variable is actually used; per your note, that is left to a later optimiser.
- **Counts across arms:** `ite`/`case` arms take the maximum, not the sum, so a variable used once in each arm counts as 1 (`LeanScript/Term/Occ.lean`).
- **Exact open flag:** each body carries an exact open level `o : Lvl`, and every elimination needs an open operand.
- **Two theorems, proved:** `LeanScript.Term.closed_isValue` (a closed statement is a value, so no closed redex can be written) and `LeanScript.Term.dce_eval` (dead-code elimination preserves evaluation).

**Fixes this session:**
- `ExternElab/TermShorthands.lean`: the auto-parameter tactic now has a public name, which fixes the "Unknown constant `_private…_auto`" error.
- `GenElab/GetCtor.lean`: `Branch.enumList` is now referenced by its full name, which fixes the "imported privately" error.
- I removed one unused simp argument in `RenameEval`.

**Test changes you should know about:** I rewrote the broken tests for the new `Term`. Some checks were dropped or weakened:
- **Printing checks removed:** the `#print`/printing checks in `TermNotationTest` are gone, because there is no pretty printer for the new terms.
- **Substitution tests removed:** the substitution section of `NoIotaTest` is gone, and `TermSubstTest` was renamed to `TermTests/RenameTest.lean`.
- **`ClosedEvalTest`** now checks that closed terms are values.
- **`TcoTest`:** `hyperTCOT_run` needs a higher `maxHeartbeats` (4000000), and several `rfl` proofs became `kernel_rfl`.
- **`Quotient`/`Nest`/`IndexedFamily`/`RoseVariants` proofs** were updated to the new shape of the fold's branch argument.

I also updated `README.md`, `NOT_IMPLEMENTED.md` (normaliser unverified, usage annotations not checked against actual use, no pretty printer) and the table in `TermElab/ToTerm.lean`. All changes are committed.

# Summary of changes for run 9665b58e-c651-4e7e-b8e2-b5d2eb8d85e3
I wrote `proposals/NTermDesign.md`, a detailed explanation of proposal B (two contexts: known and unknown) as it is now built in `LeanScript/NTerm/`, with an assessment and answers to your four questions. The modules and `TermTests/NTermTest.lean` build cleanly with no `sorry`. The normaliser that turns the current `Term` into `NTerm` is not written yet.

**What the note covers**
- **The rule and how the types enforce it.** Every elimination needs an operand that mentions an unknown. So when every variable is known, no computation can be written at all. This is proved in Lean: `Term.closed_isValue` and `Term.run_isValue` say such a term is always a chain of `letV`s ending in `ret v`.
- **Sharing when a redex is stuck.** Closures, delays and data literals are bound once and passed by name. A forced open delay stays a `letE` and its body is not copied in at the force, which is the correction you asked for. `share` only accepts a stuck expression.
- A table matching each constructor of the current `Term` to its `NTerm` counterpart.
- The results already proved: evaluation, renaming preserves meaning, occurrence counting, and dead-code elimination preserves meaning (`Term.dce_eval`).

**Your four questions**
1. **Usage 0|1|ω.** Pattern binders (case fields, closure, loop and join-point parameters) really do need `0`. Definition binders (`letV`, `letE`, join points) should be `1 | ω` after optimisation. But just changing their type to `1 | ω` would not stop dead variables, because nothing checks the annotation against how the variable is actually used. Two real fixes:
   - Track usage counts in the type itself. This is heavy and I don't recommend it now.
   - Add a checked predicate `Term.WellCounted`, plus a proof that dead-code elimination produces terms satisfying it. This is what I recommend.
   A wrong `1` is the dangerous case, because it allows inlining that duplicates work. Two smaller fixes: counts across `ite`/`case` arms should take the maximum instead of adding (used once in each arm is `1`, not `ω`).
2. **The open flag.** Something is open when it mentions an unknown, directly or through an open known value. The constructors compute the flag, so it can't be wrong. Known means known shape, not known value: in `fun n => ⟨n, 3⟩` the record is known but open. Without the flag you could call a closed known closure on a literal, which is a closed redex. Two imprecisions:
   - An "open" body only requires some unknown to be in scope, not that the body uses one. So a closed loop can be kept instead of run. This errs towards keeping too much, never towards a wrong answer.
   - Closed bodies hide open entries by setting their usage to 0, which looks the same as "dead".
3. **Join points for loops.** The only loops are the folds; `for` and structural `while` become a `nat_rec` over `ForInStep` (see `LeanScript/Term/BoundedLoop.lean`). Loop bodies can't jump outward, and early exit is already the `.done` state. So bounded loops need no join points. Self-jumping join points (`joinrec`) only make sense once well-founded recursion is added.
4. **Strict A-normal form.** Yes, and stricter than `Term`:
   - closures and delays are values named by `letV`;
   - known values are never taken apart, called or forced;
   - `share` only takes stuck expressions;
   - a join point immediately followed by a jump to it can't be written.
   The pure conditional `cond` and pure extern calls inside expressions stay, as in `Term`.

**Caveat:** because every closed redex must be evaluated, closed loops are run at compile time, even a closed `nat_rec` over a huge bound.

**Remaining work, in the order the note recommends:**
1. The normaliser (`Term` → `NTerm`) with a proof that it preserves meaning.
2. `WellCounted` and its proof for dead-code elimination.
3. Maximum instead of sum for branch counts.
4. An exact open flag for bodies.
5. Pretty printer and code generation.
6. `joinrec`, only together with well-founded recursion.

I added three entries to the Properties table: the `NTerm.Term` definition, and `Term.closed_isValue` and `Term.dce_eval`, both marked proved.

# Summary of changes for run 469c4cfc-8e0a-477e-9f8d-247c0f44350f
I expanded the Proposal B section of `proposals/NormalFormProposals.md` (§B.1–§B.7) and added two companion files. Neither file is part of the Lake build: `lake env lean` checks each one with no errors and no `sorry`. The Lake-built sources are unchanged.

**What the section now covers**
- **Grammar before (§B.1) and after (§B.2):** today's one-context grammar next to B's two contexts, known (`Φ`) and unknown (`Γ`).
  - B adds `kvar`, a new `Val` family and `letV`. `Val` holds closures, delays and data literals.
  - `Neu.var` only takes unknowns, so a known value can be passed on but never called, forced or taken apart.
  - Both are written in BNF and as Lean signatures.
- **Closed-term theorems (§B.3):** a closed statement is a chain of `val`s ending in `ret v`.
  - If `Φ` holds only closures and delays, `v` is the quotation of the value.
  - If `Φ` also holds data literals, that only holds after inlining `Φ`.
  - Unused `val`s are allowed by the types, so the normaliser must never produce one.
- **Examples (§B.5):** 8 examples: lets used 0/1/2 times (extern calls and function calls), closed values, Ackermann, a loop that rebuilds a record every step (`fibLoop`/`fib`), a record used twice with a condition known at compile time, a closure called twice vs passed on twice, and a `Thunk` forced twice.
  - Each has the Lean input, today's output, the same with named variables, and B's output.
  - Today's outputs are copied from what the project prints for `proposals/NormalFormBExamples.lean`.
  - **B's outputs are worked out by hand, since B is not implemented.**
- **Elaborator changes (§B.6) and costs (§B.7).**

**Your three questions (§B.4)**

*Today* (read from the source and confirmed by the printed outputs), the normaliser never counts uses; what happens depends only on what the `let` binds:
- **0 uses:** not eliminated. `let _ := share (n * 7)` and `let _ := f n` stay. The exception is a trivial atom: a variable, a literal, or a closed Lean term of a leaf type such as `10 * 10`.
- **1 use:** not inlined. A closure called once is still bound and then called. Trivial atoms are the exception again.
- **2+ uses:** shared, except trivial atoms, which are copied (`lit ‹2 + 3›` appears twice).
- A related waste: every projection `s.f` takes the whole record apart again. In `fibLoop` that is 4 destructurings per step, with 12 binders of which 4 are used.

*Under B*, some of this is forced by the types and the rest is a counting pass after normalisation:
- **0 uses:** eliminated, for every kind of let. This is safe because the language is pure and total.
- **1 use:** inlined when the bound thing is pure (a `share` of a neutral expression, a data literal, or the body of a closure or delay at its only call or force). There are two exceptions:
  - Nothing is inlined into a closure, loop or delay body, because that body runs repeatedly.
  - A computation (a call of an unknown function, a fold) cannot be inlined, because operands must be pure.
- **2+ uses:** shared, with two exceptions:
  - Every call of a known closure is inlined (the types require it), which copies the closure's body.
  - A `Thunk` forced twice has its body computed once, which keeps the memoisation.

**Two things I noticed**
- The translator already turns a closed leaf-typed Lean term into a literal holding the Lean expression: `seven` becomes `lit ‹3 + 4›` and `ack 2 3` becomes `lit ‹ack 2 3›`. The value isn't computed at that point, though, and an extern call on two such literals is still produced.
- A test file without `@[expose] public section` fails on record constructors with "invalid scope". Separately, calling a record-building helper inside a structural loop (`loopP n (stepP s)`) gives type-mismatch errors. I didn't investigate either; the examples use forms that work.

**Files**
- `proposals/NormalFormBToy.lean`: B on the same small language as the earlier toy, with closures as the only known values. It proves that nothing neutral is closed whatever is known, that a closed statement is a `val` chain ending in `ret`, the quotation result at first-order types, and that calling a known closure is ill-typed. Its theorems use only `propext` and `Quot.sound`.
- `proposals/NormalFormBExamples.lean`: the examples, translated by today's `#leanscript_to_term` and printed.

# Summary of changes for run 8212a7ba-0314-4faa-ad3a-ec656f9cf030
Yes, this works. `.leanName` is no longer a constructor of `LeanPrimTy`. `Ty.leanName` is now an abbreviation built the same way as `Ty.ordering`. The full project builds (`LeanScript`, `NonEmpty`, `TyTests`, `TermTests`) with no `sorry`, and the change is committed.

**Why it works despite the recursion:** you're right that a closed `Ty` can't write recursion itself; only a declared datatype (`Ty.data`) can. But `Lean.Name` (`anonymous | str p s | num p n`) is the same as a list of components, and `Ty.list` already provides the recursion. So, in `LeanScript/Ty/Ty.lean`:
```lean
abbrev nameComponent {ks : List Nat} : Ty ks :=
  .union (.two (.fields (.one .string)) (.fields (.one .nat)))
abbrev leanName {ks : List Nat} : Ty ks := .list nameComponent
```
It follows the `ordering` pattern closely. `Ordering`'s values are `Fin 3`, converted by `orderingToFin`. Likewise, `Ty.leanName`'s values are `List (String ⊕ Nat)`, root first (`` `a.b.3 `` becomes `[a, b, 3]`), no longer `Lean.Name` itself.

**Conversions** (in `LeanScript/Term/Extern.lean`, next to `orderingToFin`): `nameToComponents` and `nameOfComponents`. Two proved `@[simp]` theorems show they are inverse in both directions.

**Other changes:**
- `LeanPrimTy.leanName` is commented out with a note explaining why, and its cases are removed from `pretty`, `denote`, `Two.lean` and `Three.lean`. I also removed the `-- TODO: name should be constructed as recTaggedUnion` comment.
- **Catalogue:** it now takes a parameter `(leanName : MyTy)`, just as it takes `ordering`. `PreludeExtern` uses it for `lean_name_eq`, and `Extern` passes `Ty.leanName`. The `lean_name_eq` evaluator converts both arguments with `nameOfComponents` and then calls `Lean.Name.beq`.
- **Notation:** `[Ty| Lean.Name]` elaborates to `Ty.leanName` and prints back the same way. Inside a delay, it expands to `.list Ty.nameComponent`.
- **Reading Lean types** (`#leanscript_get_ty` / `#leanscript_to_term`): `Lean.Name` is read as `Ty.leanName`. A dedicated case in the reader emits it.

**What behaves differently now:**
- Values of type `Ty.leanName` are component lists. For example, the translated `nameEq` now runs as `nameEqT'.run (nameToComponents `a.b) (nameToComponents `a.b)`.
- `PExpr.lit` can no longer hold a name. In `TermTests/ListNameExternTest.lean` I build a name literal as `lean_array_to_list` over an array of `union_mk` components (`nameLit`) and test it with `#guard`s.
- In a program being translated, a name literal or a constructor application of `Lean.Name` now gives an explicit error instead of translating.

`TermTests/ListNameExternTest.lean` is updated for all of this: the new denotation, the unfolding of `Ty.leanName` by `rfl`, the round trip, `lean_name_eq` on name literals, and the translated `nameEq` and its printed type.

# Summary of changes for run 81050d2d-ee85-4a33-aa30-cafabf161749
I wrote `proposals/NormalFormProposals.md`. It gives several ways to change the grammar so that a closed `Term` is its own value, with the normalisation done when Lean is elaborated to `Term`. They are ordered as you asked: structural first, then `Prop`-based (I read "Prob" as `Prop`), then `Bool`-based.

I checked the main idea of the recommended proposal on a small separate language in `proposals/NormalFormToy.lean`. It is outside the Lake build; `lake env lean proposals/NormalFormToy.lean` gives no errors, warnings or `sorry`, and its theorems use only `propext` and `Quot.sound`. Everything the document says about the real `LeanScript.Term` comes from reading the sources and has not been built.

**What "true" means.** `Term.eval` returns a Lean value, not a term, so the claim has to go through a read-back function `quote`. It comes at two levels:
- **All types:** every closed statement is `ret v`, with `v` built only from literals, constructors and closures.
- **First-order types:** `t = ret (quote t.run)`, so closed terms correspond exactly to values. This can't hold at function types: `fun x => x + 0` and `fun x => x` are different terms with the same value.

**What breaks it today.** The document lists 9 ways a closed, well-typed term can still compute. The root cause is that "neutral" means "not a constructor" rather than "stuck on a variable", so `lean_nat_add 3 4` counts as neutral. The others are: a `let` that hides a value, calling a `let`-bound closure, folds over literals, delays, join points used only once, zero-argument externs, and `list` having no constructor form.

**Groundwork every proposal needs:** a `list_mk` constructor, `Ty.FO` (first-order types) with `PExpr.quote`, running extern calls whose arguments are all values during elaboration and turning the result back into a term, and a smart constructor `mkExtern`. With this alone, `[Term| 3 + 4]` would elaborate to `ret 7`.

**The proposals:**
- **A (structural, recommended):** "neutral" means stuck on a variable.
  - An extern call needs at least one neutral argument.
  - `app`, `share`, the folds and the forces take neutral arguments.
  - `lam`, `thunk_mk` and `lazy_mk` move into `PExpr`, so every variable in scope stands for an unknown.
  - `join` is only allowed together with the branch that needs it.

  With these changes both levels follow by short inductions. The toy proves:
  - no closed neutral term or computation exists (`Neu.not_closed`, `Comp.not_closed`);
  - a closed statement is `ret v` (`Term.closed_ret`);
  - at first-order types it equals `ret (quote t.run)` (`Term.closed_eq_quote`), so `run` is injective (`Term.closed_run_injective`);
  - `ret (3 + 4)` is rejected (`addT_rejected`).

  The costs: every call of a known closure is inlined, loops over literals are computed or unrolled up to a limit, `PExpr` becomes mutual with `Term`, and substitution has to reduce as it goes.
- **B (structural, keeps sharing):** a second context of `let`-bound known values, which can be passed around but never taken apart or called.
- **A′ (structural, another encoding):** a single family indexed by its shape.
- **C1 / C2 (`Prop`):** keep today's grammar and attach a proof of normality, either bundled or as `:= by term_nf` arguments in the style of `TyWf`. C1 states A's full normal form. C2 only requires that every closed subterm is a value: that is enough for both levels, keeps sharing, and avoids unrolling loops.
- **D (`Bool`):** an `isNF` checker proved by `decide`. It is the weakest option and still needs C's predicate to prove anything.

The document ends with a comparison table and the recommendation: do the groundwork first, then A; switch to B or C2 if inlining or unrolling turns out too costly; keep D only as a debugging check. I made no changes to the Lake-built sources.
