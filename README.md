This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# LeanScript

A typed object language embedded in Lean, with one grammar of types and one grammar of
terms:

* **types** (`Ty ks`): closed types whose recursive datatypes are *declared once*, in a
  datatype signature (`DSig ks`), and named (`Ty.data r`).  Every type has at least two
  values (`Ty.den_exists_ne`); a type of no or one value (`Unit`, `Empty`, …) cannot be
  written, and a type of two values is always `Ty.bool` (a union needs a constructor with
  fields, `BitVec 1` is refused, …): every type other than `Ty.bool` has three different
  values (`Ty.den_exists_three`, `Ty.eq_bool_of_two_points`);
* **terms** (`Term Δ Γ τ`): a direct-style grammar that terminates by construction (every
  loop is a fold: `nat_rec`, `array_foldl`, `data_rec`, `data_brec`), with a total,
  structural evaluator `Term.eval` into Lean values;
* **generators**: `leanscript_signature` declares the datatypes of a program,
  `#leanscript_get_ty` / `#leanscript_get_ctor` / `#leanscript_get_cases` give the type,
  the constructors and the case analysis of a Lean type, and `#leanscript_to_term`
  translates a Lean definition into a `Term`.

Build everything, tests included, with `lake build`; run the compiled tests (the checks that
are too slow for the kernel) with `lake test`.  The project depends on Mathlib (`v4.34.0`,
with Batteries and Aesop); `LeanScript/Term/Syntax/UsageAlgebra.lean` takes the algebra of usages
(commutative monoid, linear order) from it.

## From Lean to JavaScript: `leanscript`

```
lake build leanscript
.lake/build/bin/leanscript Tests/SnapshotsMy/TcoAck.lean     # or a module name: SnapshotsMy.TcoAck
.lake/build/bin/leanscript --check FILE.lean                 # also differential checks
scripts/leanscript-snapshots.sh               # Tests/SnapshotsMy + Tests/SnapshotsPBOPure (files with a public non-recursive or structurally recursive function), checks run with node
```

For each public definition of the file that `LeanScript.Term` supports — non-recursive or
structurally recursive (well-founded and `mutual` definitions are refused for now, with the
reason) — `leanscript` reads its `Expr` (not LCNF or IR, which have lost the types),
translates it to a `Term` (`#leanscript_to_term`), optimises it (`Term.optimizeN`, which
preserves `Term.eval`: `Term.optimizeN_eval`), converts it to the untyped JavaScript grammar
`JsTerm` twice, once per preset (`MoreJs.termToJs`: `pbo` uses `number` for the integer
types, `faithful` uses `BigInt`), and prints it with `LanguageJavascriptMini`.  Next to
`FILE.lean` it writes `FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`,
`FILE-JsTerm-pbo.txt`, `FILE-JsTerm-faithful.txt`, `FILE-pbo.js` and `FILE-faithful.js` (the
runtime helpers the module needs, then one `export const f = (x, y) => …` per function: a
chain of lambdas becomes one arrow with several parameters); with `--check` also
`FILE-pbo.check.mjs` and `FILE-faithful.check.mjs`, which call every exported function on
sample arguments and compare the answers with the ones Lean computes.  Every output lists
the definitions that were not translated, with the reason; the JavaScript outputs also start
with their configuration.  Join points are de Bruijn indexed in `JsTerm` (`JsStmt.join`,
`JsStmt.jump`) and printed as labelled blocks (`j$1: { …; break j$1; }`).  In the `Term`
files a lazy value `Unit → τ` is printed `(Lazy τ)`.

The optimiser (`LeanScript/Term/Optimize/Basic.lean`, `Cse.lean`, `Atom.lean`) does constant
folding, copy propagation, dead-code elimination, common subexpression elimination of pure
computations (`let x := f a; … let y := f a; …` computes `f a` once), an `if` whose branches
are the same atom, and inlining of a join point whose body is trivial (`ret a`, an atom);
`Term.optimize_eval` proves it does not change `Term.eval`, and `Term.numCalls_optimize` that it never increases the number of calls.  `leanscript --help` lists the
options.

| path | what it holds |
| :-- | :-- |
| `JsTerm/Config.lean` | `MoreJs.JsConfig`: how each leaf type is represented (a `number` or a `BigInt`; typed or generic arrays), presets `faithful` (default) and `pbo`, command-line knobs |
| `JsTerm/Ty.lean` | the layouts `JsTerm` (`uint53`: a `number` standing for a `Nat`, checked on overflow; `nat`: a `BigInt`; typed arrays; tagged arrays; …) and `lowerScalarPrim`/`lowerArrayPrim`/`lowerTy` |
| `JsTerm/Syntax.lean` | the JavaScript grammar: `JsExpr`, `JsStmt`, `JsFun`, `JsHelper`, `JsModule`, and the `-JsTerm.txt` dump |
| `JsTerm/Extern.lean` | each extern of the catalogue as inline JavaScript or a runtime helper, per layout (overflow checks for `uint53`, Lean's `x / 0 = 0`, …) |
| `JsTerm/FromTerm.lean` | `MoreJs.termToJs`: a closed `Term` to a `JsFun` (loops for `nat_rec`/`array_foldl`, `if`/`switch` for branches, closures for lambdas) |
| `JsTerm/PrintMini.lean` | `JsModule.toJs`: through the `LanguageJavascriptMini` AST to source text |
| `LeanScriptCli/` | the executable: `Frontend.lean` (elaborating the file, choosing the definitions, translating, open definitions of recursive functions), `RecCalls.lean` (binding the recursive functions of an open definition in its JavaScript, direct calls), `Check.lean` (`--check`), `Main.lean` |

## Layout

| path | what it holds |
| :-- | :-- |
| `LeanScript/Ty/Syntax/LeanPrimTy.lean`, `LeanScript/Ty/Syntax/LeanPrimTyCovariant.lean`, `LeanScript/Ty/Syntax/EnumSchema.lean` | the leaf types, the covariant leaf type formers (arrays, thunks, lazy values; used by the extern catalogue) and the payload of an enum |
| `LeanScript/Ty/Syntax/Ty.lean` | `Ref`, `BRef`, the mutual `Ty`/`Fields`/`Ctor`/`Ctors`, `UnionShape`, with `DecidableEq`, `BEq`, `LawfulBEq`, `Repr`; renaming `Ty.map` and its laws `Ty.map_id`, `Ty.map_map` |
| `LeanScript/Ty/Syntax/Decl.lean` | declarations of blocks of datatypes (`Fld`, `Decl`, `Mems`, `DSig`) and `unfold` |
| `LeanScript/Ty/Den/Container.lean`, `LeanScript/Ty/Den/Basic.lean` | what a type denotes: indexed W-types for the declared blocks, `Ty.den`, `Ty.Den`, `DSig.dataIn`/`dataOut`/`dataRec` |
| `LeanScript/Ty/Den/Facts.lean`, `LeanScript/Ty/Den/Brec.lean` | `dataIn`/`dataOut` are inverse; course-of-values recursion `DSig.dataBrec` and its computation rule |
| `LeanScript/Ty/Den/Two.lean` | every type has two values that a Boolean test tells apart |
| `LeanScript/Ty/Den/Three.lean` | every type other than `bool` has three values that a test tells apart: two points are only ever `bool` |
| `LeanScript/Term/Syntax/Ctx.lean`, `LeanScript/Term/Syntax/Usage.lean`, `LeanScript/Term/Syntax/Term.lean`, `LeanScript/Term/Semantics/Eval.lean` | the grammar of normal-form terms: two contexts (known values `Φ`, unknowns `Γ`), levels (`Lvl`) that make the open/closed flag of every expression and body exact, usages `Usage1ω` on definition binders (`letV`, `letE`, join points) and `Usage01ω` on pattern binders (a binder annotated `0` cannot be referenced); every elimination needs an open operand, so no redex that could be computed can be written (`TermTests/Syntax/NoIotaTest.lean`, `TermTests/Syntax/NormalFormTest.lean`); and its evaluator |
| `LeanScript/Term/Semantics/Closed.lean` | a term with no unknown and no open known value is a value (`Term.closed_isValue`, `Term.run_isValue`) |
| `LeanScript/Term/Semantics/NormalValue.lean` | `Term.eval` of a statement in which every variable is known (no unknown, no open known value, no join point, completely normalised known values) is the reading of a completely normalised value `NVal`: constructors all the way down, delays forced, functions as closures of closed bodies over completely normalised values (`Term.eval_normal`, `Term.run_normal`) |
| `LeanScript/Term/Rename/Basic.lean`, `LeanScript/Term/Rename/Eval.lean`, `LeanScript/Term/Rename/Weaken.lean` | renaming (partial: it fails on a dropped variable that is used) and weakening, and the fact that renaming commutes with evaluation (`Term.rename_eval`, `TermTests/Semantics/RenameTest.lean`) |
| `LeanScript/Term/Optimize/Occ.lean`, `LeanScript/Term/Optimize/Dce.lean` | occurrence counts (added along straight-line code, the maximum across the arms of a branch, `ω` inside a body that may run many times) and dead-code elimination with exact usages, which preserves the meaning (`Term.dce_eval`) |
| `LeanScript/Term/Optimize/Basic.lean` | the optimiser `Term.optimize`: copy propagation (`let x := share y`), a shared answer returned directly (`let x := share n; ret x` is `ret n`), dead `record_casesOn` dropped, then dead-code elimination; it preserves the value (`Term.optimize_eval`, `Term.optimize_run`, `TermTests/Optimize/OptimizeTest.lean`) |
| `LeanScript/Term/Optimize/Count.lean`, `CountRename.lean`, `CountDce.lean`, `CountOptimize.lean`, `Tests/TermTests/Optimize/CseTest.lean` | `Term.numCalls`, the number of calls (`f a`, `t.get`, `t ()`) written in a statement; renaming preserves it (`Term.numCalls_rename`), and every pass of the optimiser never increases it (`Term.numCalls_simp`, `Term.numCalls_cseWalk`, `Term.numCalls_dce`, so `Term.numCalls_optimize`, `Term.numCalls_optimizeN`); on `EsPrecedence01.test1` the translation has 5 calls and the optimised statement 1, with the same value |
| `LeanScript/Term/Rewrite/Step.lean`, `LeanScript/Term/Rename/Comp.lean`, `LeanScript/Term/Rewrite/StepRename.lean`, `LeanScript/Term/Rewrite/StepInv.lean`, `LeanScript/Term/Rewrite/Abstract.lean`, `LeanScript/Term/Rewrite/ChurchRosser.lean`, `LeanScript/Term/Rewrite/SimpStep.lean` | Church–Rosser for rewriting under `Term.eval`: the one-step relation `Term.Step` (drop a dead `val`/`let`/`record_casesOn`/`join`, copy propagation, a shared answer returned or jumped directly, anywhere in a term), which preserves the value (`Term.Step.eval`); it is strongly confluent, hence confluent and Church–Rosser (`Term.Step.confluent`, `Term.Step.churchRosser`, `Term.eval_churchRosser`, `Term.run_churchRosser`), normal forms are unique (`Term.Step.normal_unique`), and the optimiser's rewriting pass is a sequence of such steps (`Term.simp_star`, `Term.simp_joinable`; `TermTests/Optimize/ChurchRosserTest.lean`) |
| `LeanScript/Term/Optimize/OpenRec.lean`, `Tests/TermTests/Optimize/OpenRecTest.lean` | why `leanscript`'s open definitions are faithful: a functional whose recursive calls go down a well-founded relation has exactly one fixed point (`OpenRec.fix_unique`, `OpenRec.fix_isFix`, `OpenRec.eq_fix_of_isFix`); the optimiser keeps the fixed points of a translated open definition (`Term.optimizeN_isFix_iff`, `Term.optimizeN_fix_eq`); a `nat_rec` whose step ignores the accumulator is the `if` the JavaScript prints (`natIter_of_ignoresAcc'`); for `mc91Loop` and `ack` (open definitions written as the tool builds them), every solution of the unfolding equation is the function, and every fixed point of the `#leanscript_to_term` translation of `mc91Loop`'s open definition, optimised any number of times, is `mc91Loop` (`mc91LoopOpenT_optimizeN_fix`) |
| `LeanScript/WFTerm/Syntax.lean`, `LeanScript/WFTerm/Eval.lean`, `LeanScript/WFTerm/Optimize.lean` | `WFTerm`: well-founded recursion around `Term` (whose normal-form terms are the call-free atoms): global functions with pre/postconditions and a well-founded relation, recursive calls (`WFComp.self`) carrying their decrease proof under the path condition, calls of earlier global functions, shared values, `map`/`foldl` whose body knows `x ∈ l`, join points and recursive join points (`joinrec`, loops whose back edges carry their decrease proof); the evaluator `WFTerm.eval`/`WFProgram.run` is total and structural, runs recursion by `WellFounded.fix` (proofs only: no fuel, no measure, no default value) and returns the answer with its postcondition; the optimiser `WFTerm.optimize` (atoms by `Term.optimize`, constant tests, a join point entered at once inlined, folds of `[]`) preserves the value (`WFTerm.optimize_eval`, `WFProgram.optimize_run`; `TermTests/Optimize/WFTermTest.lean`, run in `Tests/Main.lean`) |
| `LeanScript/Term/Build.lean` | abbreviations the elaborators write (`PExpr.externLit`, `Branch.enumList`, `Comp.dataRecS`, …) |
| `LeanScript/Term/Syntax/Tuple.lean` | `Tuple F [a, b] = F a × F b`: right-nested products with no trailing `PUnit`, for environments, extern arguments and join-point closures |
| `LeanScript/Term/Semantics/BoundedLoop.lean` | a loop of a fixed number of steps whose iterations shrink a measure has stopped after `μ init + 1` steps, and more steps change nothing (`boundedLoop_done`, `boundedLoop_stable`): why a translated `while` loop needs no fuel |
| `LeanScript/GenElab/` (`Signature.lean`, `GetCtor.lean`, `Read.lean`, `Read/`, `Translate.lean`, `Print.lean`, `Cache.lean`) | `leanscript_signature`, `#leanscript_get_ty`/`_ctor`/`_cases`, and the generator they share (reading Lean types, erasing fields that depend on earlier fields — `Fin n → Nat` is `Nat → Nat`, `TermTests/ToTerm/DependentFieldTest.lean`; on a recursive cycle `Fin m → X` is `Nat → Option X`, so the rose tree `node : (m : Nat) → (Fin m → Rose) → Rose` is a record of a `nat` and a function to `Option Rose`, different from the `List` and `Array` rose trees, `TermTests/Datatypes/RoseVariantsTest.lean` — and the indices of inductive families — `Vec α n` is the linked list `Vec α`, `TermTests/Datatypes/IndexedFamilyTest.lean`; a type index recursed at other indices goes through a generated element type — `Nest α` is a list of `Nest.Elem α` trees, `TermTests/Datatypes/NestTest.lean` —; a quotient is read as its carrier and a proof field is dropped — `Quot (· % 2 = · % 2)` is `Nat`, `Pos` is `Nat`, `TermTests/Datatypes/QuotientTest.lean` —, SCCs and grounding order, printing, cache) |
| `LeanScript/TyElab/Notation.lean` | the `[Ty| …]` notation |
| `LeanScript/TermElab/Anf.lean`, `LeanScript/TermElab/Anf/` (`Src`, `Sem`, `Render`, `Emit`), `LeanScript/TermElab/Notation.lean` | the normaliser (by evaluation, at elaboration time) of direct-style source trees into normal-form terms, and the `[Term| …]` notation built on it |
| `LeanScript/TermElab/ToTerm.lean`, `LeanScript/TermElab/ToTerm/` | `#leanscript_to_term` (`ToTerm/Basic.lean`: translation state and helpers; `ToTerm/Expr.lean`: the expression translator `tr`, with its cases in `ToTerm/Expr/` (`Loops`, `Calls`, `Ctor`, `Cases`) taking `tr` as an argument, with calls of library functions as calls of catalogue externs (`Neu.extern`, table `ToTerm/ExternTable.lean`), pure `if`s as `Neu.cond` and externs that take a proof, `TermTests/Extern/CondExternTest.lean`; `ToTerm/While.lean`: which `while` loops are structurally terminating, `TermTests/ToTerm/WhileTest.lean`; `ToTerm.lean`: the definition translator and the syntax), including `mutual` groups of recursive functions and members of a block held inside an `Array` or a function (`TermTests/ToTerm/MutualToTermTest.lean`) |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/`, `LeanScript/LeanInitPureExterns/Shorthands.lean`, `LeanScript/ExternElab/CatalogueShorthands.lean` | the catalogue of the pure externs of `Init`, indexed by signature (`LeanInitPureExtern σs τ`): the language's only kind of extern |
| `LeanScript/Term/Extern/Catalogue.lean`, `LeanScript/Term/Extern/Eval.lean`, `LeanScript/Term/Extern/Eval/`, `LeanScript/Term/Extern/Shorthands.lean`, `LeanScript/ExternElab/TermShorthands.lean` | the catalogue instantiated at the types of the language (`Extern ks σs τ`), the meaning of every entry (`Extern.eval`), and one term former per entry (`PExpr.lean_string_any s f`, `Neu.lean_nat_add a b`) |
| `LeanScript/TacticElab/KernelRfl.lean` | `kernel_rfl`, an equation checked by the kernel only |
| `HashableFloat/` | `HashableFloat`/`HashableFloat32`: floats with lawful `BEq`, `Hashable` and a linear `Ord` (away from `NaN`), the leaf types of the floats |
| `NonEmpty/` | correct-by-construction non-empty lists, arrays and strings (their literal notations and `ToExpr` instances are in `NonEmpty/*Elab/`) |
| `TyTests/`, `TermTests/` | the tests, checked by `lake build` (`#guard_msgs` snapshots, `rfl` runs) |
| `Tests/Main.lean`, `Spec/` | `lake test`: the checks on values that are too slow for the kernel (`kernel_rfl` runs of `Term.eval` taking from half a second to many seconds), run compiled with the `Spec` test library, and the optimiser on the same programs |
| `proposals/` | proposals, reviews and stand-alone sketches; nothing here is part of the build (`NominalTyProposal.md` is the design that is implemented) |
| `scripts/` | benchmarking scripts |

Elaborators, notations, tactics and the meta-level code they use live in `XxxElab/`
directories (`TyElab/`, `TermElab/`, `GenElab/`, `ExternElab/`, `TacticElab/`), next to the
modules they elaborate into.

There is no module that gathers the others: a file imports the modules it uses, one by
one.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
