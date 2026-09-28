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
with Batteries and Aesop); `LeanScript/Term/UsageAlgebra.lean` takes the algebra of usages
(commutative monoid, linear order) from it.

## From Lean to JavaScript: `leanscript`

```
scripts/install-leanscript.sh                 # builds it, links ./.lake/bin/leanscript
./.lake/bin/leanscript Tests/SnapshotsMy/TcoAck.lean     # or a module name: SnapshotsMy.TcoAck
./.lake/bin/leanscript --preset=pbo --check FILE.lean    # numbers instead of BigInt; differential checks
scripts/leanscript-snapshots.sh               # Tests/SnapshotsMy + Tests/SnapshotsPBOPure (files with a public structurally total function), checks run with node
```

For each public, structurally total function of the file, `leanscript` reads its `Expr`
(not LCNF or IR, which have lost the types), translates it to a `Term`
(`#leanscript_to_term`), optimises it (`Term.optimizeN`, which preserves `Term.eval`:
`Term.optimizeN_eval`), converts it to the JavaScript grammar `MoreJsTy` at the chosen
configuration (`MoreJs.termToJs`) and prints it with `LanguageJavascriptMini`.  Next to
`FILE.lean` it writes `FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`,
`FILE-MoreJsTy.txt` and `FILE.js` (the runtime helpers the module needs, then one
`export function` per function); with `--check` also `FILE.check.mjs`, which calls every
exported function on sample arguments and compares the answers with the ones Lean computes.
Every output starts with the configuration and lists the functions that were not translated,
with the reason.  `leanscript --help` lists the configuration options (`--nat=num|bigint`,
`--int=…`, `--array-bool=uint8|generic`, …; `MoreJsTy/Config.lean`).

| path | what it holds |
| :-- | :-- |
| `MoreJsTy/Config.lean` | `MoreJs.JsConfig`: how each leaf type is represented (a `number` or a `BigInt`; typed or generic arrays), presets `faithful` (default) and `pbo`, command-line knobs |
| `MoreJsTy/Ty.lean` | the layouts `MoreJsTy` (`uint53`: a `number` standing for a `Nat`, checked on overflow; `nat`: a `BigInt`; typed arrays; tagged arrays; …) and `lowerScalarPrim`/`lowerArrayPrim`/`lowerTy` |
| `MoreJsTy/Syntax.lean` | the JavaScript grammar: `JsExpr`, `JsStmt`, `JsFun`, `JsHelper`, `JsModule`, and the `-MoreJsTy.txt` dump |
| `MoreJsTy/Extern.lean` | each extern of the catalogue as inline JavaScript or a runtime helper, per layout (overflow checks for `uint53`, Lean's `x / 0 = 0`, …) |
| `MoreJsTy/FromTerm.lean` | `MoreJs.termToJs`: a closed `Term` to a `JsFun` (loops for `nat_rec`/`array_foldl`, `if`/`switch` for branches, closures for lambdas) |
| `MoreJsTy/PrintMini.lean` | `JsModule.toJs`: through the `LanguageJavascriptMini` AST to source text |
| `LeanScriptCli/` | the executable: `Frontend.lean` (elaborating the file, choosing the definitions, translating), `Check.lean` (`--check`), `Main.lean` |

## Layout

| path | what it holds |
| :-- | :-- |
| `LeanScript/Ty/LeanPrimTy.lean`, `LeanScript/Ty/LeanPrimTyCovariant.lean`, `LeanScript/Ty/EnumSchema.lean` | the leaf types, the covariant leaf type formers (arrays, thunks, lazy values; used by the extern catalogue) and the payload of an enum |
| `LeanScript/Ty/Ty.lean` | `Ref`, `BRef`, the mutual `Ty`/`Fields`/`Ctor`/`Ctors`, `UnionShape`, with `DecidableEq`, `BEq`, `LawfulBEq`, `Repr`; renaming `Ty.map` and its laws `Ty.map_id`, `Ty.map_map` |
| `LeanScript/Ty/Decl.lean` | declarations of blocks of datatypes (`Fld`, `Decl`, `Mems`, `DSig`) and `unfold` |
| `LeanScript/Ty/Container.lean`, `LeanScript/Ty/Den.lean` | what a type denotes: indexed W-types for the declared blocks, `Ty.den`, `Ty.Den`, `DSig.dataIn`/`dataOut`/`dataRec` |
| `LeanScript/Ty/DenFacts.lean`, `LeanScript/Ty/DenBrec.lean` | `dataIn`/`dataOut` are inverse; course-of-values recursion `DSig.dataBrec` and its computation rule |
| `LeanScript/Ty/Two.lean` | every type has two values that a Boolean test tells apart |
| `LeanScript/Ty/Three.lean` | every type other than `bool` has three values that a test tells apart: two points are only ever `bool` |
| `LeanScript/Term/Ctx.lean`, `LeanScript/Term/Usage.lean`, `LeanScript/Term/Term.lean`, `LeanScript/Term/Eval.lean` | the grammar of normal-form terms: two contexts (known values `Φ`, unknowns `Γ`), levels (`Lvl`) that make the open/closed flag of every expression and body exact, usages `Usage1ω` on definition binders (`letV`, `letE`, join points) and `Usage01ω` on pattern binders (a binder annotated `0` cannot be referenced); every elimination needs an open operand, so no redex that could be computed can be written (`TermTests/NoIotaTest.lean`, `TermTests/NormalFormTest.lean`); and its evaluator |
| `LeanScript/Term/Closed.lean` | a term with no unknown and no open known value is a value (`Term.closed_isValue`, `Term.run_isValue`) |
| `LeanScript/Term/NormalValue.lean` | `Term.eval` of a statement in which every variable is known (no unknown, no open known value, no join point, completely normalised known values) is the reading of a completely normalised value `NVal`: constructors all the way down, delays forced, functions as closures of closed bodies over completely normalised values (`Term.eval_normal`, `Term.run_normal`) |
| `LeanScript/Term/Rename.lean`, `LeanScript/Term/RenameEval.lean`, `LeanScript/Term/Weaken.lean` | renaming (partial: it fails on a dropped variable that is used) and weakening, and the fact that renaming commutes with evaluation (`Term.rename_eval`, `TermTests/RenameTest.lean`) |
| `LeanScript/Term/Occ.lean`, `LeanScript/Term/Dce.lean` | occurrence counts (added along straight-line code, the maximum across the arms of a branch, `ω` inside a body that may run many times) and dead-code elimination with exact usages, which preserves the meaning (`Term.dce_eval`) |
| `LeanScript/Term/Optimize.lean` | the optimiser `Term.optimize`: copy propagation (`let x := share y`), a shared answer returned directly (`let x := share n; ret x` is `ret n`), dead `record_casesOn` dropped, then dead-code elimination; it preserves the value (`Term.optimize_eval`, `Term.optimize_run`, `TermTests/OptimizeTest.lean`) |
| `LeanScript/Term/Step.lean`, `LeanScript/Term/RenameComp.lean`, `LeanScript/Term/StepRename.lean`, `LeanScript/Term/StepInv.lean`, `LeanScript/Term/Rewriting.lean`, `LeanScript/Term/ChurchRosser.lean`, `LeanScript/Term/SimpStep.lean` | Church–Rosser for rewriting under `Term.eval`: the one-step relation `Term.Step` (drop a dead `val`/`let`/`record_casesOn`/`join`, copy propagation, a shared answer returned or jumped directly, anywhere in a term), which preserves the value (`Term.Step.eval`); it is strongly confluent, hence confluent and Church–Rosser (`Term.Step.confluent`, `Term.Step.churchRosser`, `Term.eval_churchRosser`, `Term.run_churchRosser`), normal forms are unique (`Term.Step.normal_unique`), and the optimiser's rewriting pass is a sequence of such steps (`Term.simp_star`, `Term.simp_joinable`; `TermTests/ChurchRosserTest.lean`) |
| `LeanScript/WFTerm/Syntax.lean`, `LeanScript/WFTerm/Eval.lean`, `LeanScript/WFTerm/Optimize.lean` | `WFTerm`: well-founded recursion around `Term` (whose normal-form terms are the call-free atoms): global functions with pre/postconditions and a well-founded relation, recursive calls (`WFComp.self`) carrying their decrease proof under the path condition, calls of earlier global functions, shared values, `map`/`foldl` whose body knows `x ∈ l`, join points and recursive join points (`joinrec`, loops whose back edges carry their decrease proof); the evaluator `WFTerm.eval`/`WFProgram.run` is total and structural, runs recursion by `WellFounded.fix` (proofs only: no fuel, no measure, no default value) and returns the answer with its postcondition; the optimiser `WFTerm.optimize` (atoms by `Term.optimize`, constant tests, a join point entered at once inlined, folds of `[]`) preserves the value (`WFTerm.optimize_eval`, `WFProgram.optimize_run`; `TermTests/WFTermTest.lean`, run in `Tests/Main.lean`) |
| `LeanScript/Term/Build.lean` | abbreviations the elaborators write (`PExpr.externLit`, `Branch.enumList`, `Comp.dataRecS`, …) |
| `LeanScript/Term/Tuple.lean` | `Tuple F [a, b] = F a × F b`: right-nested products with no trailing `PUnit`, for environments, extern arguments and join-point closures |
| `LeanScript/Term/BoundedLoop.lean` | a loop of a fixed number of steps whose iterations shrink a measure has stopped after `μ init + 1` steps, and more steps change nothing (`boundedLoop_done`, `boundedLoop_stable`): why a translated `while` loop needs no fuel |
| `LeanScript/GenElab/` (`Signature.lean`, `GetCtor.lean`, `Read.lean`, `Read/`, `Translate.lean`, `Print.lean`, `Cache.lean`) | `leanscript_signature`, `#leanscript_get_ty`/`_ctor`/`_cases`, and the generator they share (reading Lean types, erasing fields that depend on earlier fields — `Fin n → Nat` is `Nat → Nat`, `TermTests/DependentFieldTest.lean`; on a recursive cycle `Fin m → X` is `Nat → Option X`, so the rose tree `node : (m : Nat) → (Fin m → Rose) → Rose` is a record of a `nat` and a function to `Option Rose`, different from the `List` and `Array` rose trees, `TermTests/RoseVariantsTest.lean` — and the indices of inductive families — `Vec α n` is the linked list `Vec α`, `TermTests/IndexedFamilyTest.lean`; a type index recursed at other indices goes through a generated element type — `Nest α` is a list of `Nest.Elem α` trees, `TermTests/NestTest.lean` —; a quotient is read as its carrier and a proof field is dropped — `Quot (· % 2 = · % 2)` is `Nat`, `Pos` is `Nat`, `TermTests/QuotientTest.lean` —, SCCs and grounding order, printing, cache) |
| `LeanScript/TyElab/Notation.lean` | the `[Ty| …]` notation |
| `LeanScript/TermElab/Anf.lean`, `LeanScript/TermElab/Anf/` (`Src`, `Sem`, `Render`, `Emit`), `LeanScript/TermElab/Notation.lean` | the normaliser (by evaluation, at elaboration time) of direct-style source trees into normal-form terms, and the `[Term| …]` notation built on it |
| `LeanScript/TermElab/ToTerm.lean`, `LeanScript/TermElab/ToTerm/` | `#leanscript_to_term` (`ToTerm/Basic.lean`: translation state and helpers; `ToTerm/Expr.lean`: the expression translator `tr`, with its cases in `ToTerm/Expr/` (`Loops`, `Calls`, `Ctor`, `Cases`) taking `tr` as an argument, with calls of library functions as calls of catalogue externs (`Neu.extern`, table `ToTerm/ExternTable.lean`), pure `if`s as `Neu.cond` and externs that take a proof, `TermTests/CondExternTest.lean`; `ToTerm/While.lean`: which `while` loops are structurally terminating, `TermTests/WhileTest.lean`; `ToTerm.lean`: the definition translator and the syntax), including `mutual` groups of recursive functions and members of a block held inside an `Array` or a function (`TermTests/MutualToTermTest.lean`) |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/`, `LeanScript/LeanInitPureExternShorthands.lean`, `LeanScript/ExternElab/CatalogueShorthands.lean` | the catalogue of the pure externs of `Init`, indexed by signature (`LeanInitPureExtern σs τ`): the language's only kind of extern |
| `LeanScript/Term/Extern.lean`, `LeanScript/Term/ExternEval.lean`, `LeanScript/Term/ExternEval/`, `LeanScript/Term/ExternShorthands.lean`, `LeanScript/ExternElab/TermShorthands.lean` | the catalogue instantiated at the types of the language (`Extern ks σs τ`), the meaning of every entry (`Extern.eval`), and one term former per entry (`PExpr.lean_string_any s f`, `Neu.lean_nat_add a b`) |
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
