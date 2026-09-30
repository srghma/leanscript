# `LeanScript/Term`: layout

Normal-form terms, grouped by what the modules are used for. Each directory only imports
directories listed above it (and `LeanScript/Ty`).

| Directory | Contents |
|---|---|
| `Syntax/` | the language: de Bruijn variables (`DeBruijn`), tuples (`Tuple`), usages (`Usage`, `UsageAlgebra`), contexts (`Common`, `Ctx`), the grammar itself (`Term`), and a closed program packed with its signature (`Packed`) |
| `Extern/` | the catalogue of externs over the types of the language (`Catalogue`), their names (`Name`, `NameElab`), one term former per entry (`Shorthands`), and their meaning (`Eval`, split by theme under `Eval/`) |
| `Semantics/` | the evaluator (`Den`, `Eval`) and its metatheory: closed statements are values (`Closed`), they evaluate to completely normalised values (`NormalValue`), and bounded loops need no fuel (`BoundedLoop`) |
| `Rename/` | partial renamings (`Basic`), renaming preserves the value (`Eval`), composing renamings (`Comp`), total weakening along thinnings (`Weaken`), renaming that changes levels and depth (`Relevel`, `RelevelEval`) |
| `Optimize/` | occurrence counts (`Occ`), dead-code elimination (`Dce`), inlining of known closures computing an expression (`Inline`, `InlineEval`, `CountInline`), inlining in tail position and of single-use closures (`InlineRet`, `InlineRetEval`, `CountInlineRet`, `InlineBlock`, `InlineBlockEval`, `CountRelevel`), substitution of pure expressions for unknowns (`Subst`, `SubstEval`, `CountSubst`), binding an inlined answer and applying a closure to any argument (`InlineSubst`, `InlineSubstEval`, `CountInlineSubst`), inlining at a unique call (`InlineOnce`, `InlineOnceEval`, `CountInlineOnce`), boolean conditions (`Cond`), append chains of arrays and lists (`Append`) and of strings (`StringAppend`, from the left) regrouped and their literals merged, chains of integer `+` and `*` normalised (`ArithBasic`, `ArithPow`: powers in products, `Arith`), unit operands of float operations dropped, exactly (`FloatUnit`: `x * 1.0`, `1.0 * x`, `x / 1.0`, `x - 0.0`; the IEEE identities are proved in `HashableFloat/Identities.lean`), the opt-in, **not** value-preserving re-association of float chains (`FloatReassoc`, `leanscript --float-reassoc`), the optimiser `Term.optimize` (`Basic`), and fixed points of optimised open definitions (`OpenRec`) |
| `Rewrite/` | abstract rewriting (`Abstract`), the one-step relation `Term.Step` (`Step`, `StepRename`, `StepInv`), Church–Rosser (`ChurchRosser`), and the optimiser as a rewrite sequence (`SimpStep`) |
| `Build.lean` | entry point for the elaborators and tests: the abbreviations they write, plus the evaluator and the externs |
| `Pretty.lean` | entry point for the command-line tool: the pretty printer |

The tests follow the same grouping in `Tests/TermTests/` (`Syntax/`, `Semantics/`, `Extern/`,
`Optimize/`, and `ToTerm/` and `Datatypes/` for the `#leanscript_to_term` translation).
