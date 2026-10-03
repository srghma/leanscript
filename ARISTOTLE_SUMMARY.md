# Summary of changes for run 83129ed6-47c2-4da8-9ec4-361123676817
Our JavaScript for `Tests/SnapshotsPBOPure/InlineReferenceOpIsTag.lean` already matched or beat the legacy output on every definition, so the generated JavaScript is unchanged. What was missing was testing: the file had **0 differential checks against Lean**, because the check tool skipped results of recursive datatypes like `MyList Int`. I fixed that, and the file now has 13 checks per preset, all passing.

**Comparison with the legacy output** (the full write-up is in `Tests/SnapshotsPBOPure/InlineReferenceOpIsTag.md`):
- **`test1`–`test3`:** the same as legacy. Each is `(fn) => ({ tag: 0, _1: 0, _2: { tag: 0, _1: 1, _2: fn() } })`. The `match` on the known constructor is already decided when Lean is turned into `Term`. `Term.optimize` then drops the unused `fn ()` call in `test3`.
- **`extern1`–`extern3`:** better. They are computed at compile time, where legacy calls `fn$p({})` when the module loads. Because one-field records are unboxed, `extern2 = extern1` instead of a nested record.
- **`test4`:** the same as legacy (`{ tag: 0, _1: 0, _2: extern1 }`).
- **`test5`, `test6`:** better. They are just `test4`, where legacy builds a new object in an immediately-called function for each.
- **Phases:** every decision happens in `Term -[optimize]-> Term`. The sharing of `extern1`/`test4` happens in `Term -[convert]-> JsTerm`, because `Term` has no global names. The file has no loops or recursion, so labeled blocks and loops don't come into it.

**Change to the check tool (`LeanScriptCli/Check.lean`):**
- **Recursive datatypes are now compared.** On the Lean side, the printer is a chain of `let`-bound functions that each read the previous one. This stays linear in size and can be compiled for evaluation. On the JavaScript side, a new `showTree` function in every check module prints the same format. Both cut values at depth 32 the same way, so deeper values are still compared on their first 32 levels.
- **Lazy parameters returning such a type** (`Unit → MyList Int`) now get samples, written `() => ({ … })`.
- **A one-field structure holding a union** (`RecA`) is now handled, matching how the translation unboxes it.
- **Sanity check:** deliberately breaking `test4` by hand makes `test4`, `test5` and `test6` fail, as they should.

**Testing:**
- **New snapshot `Tests/SnapshotsMy/RecursiveUnionChecks.lean`:** list append, a 40-element list (deeper than the depth-32 cut), a tree mirror and insert, wrapped and paired structures, and a lazy list parameter. It has 242 checks per preset, all passing under node.
- **New `inlineReferenceOpIsTagSpec` in `Tests/Main.lean`:** checks the expected and absent lines on both presets, the number of checks, and runs the checks under node.
- **All snapshots regenerated:**
  - No generated JavaScript changed.
  - The check modules only gained lines: the new printer in each, and new checks in `RecData` and `InlineReferenceOpIsTag`. Every check passes under node.
  - The snapshot script still exits non-zero, as before: three `*Configurable.lean` files report "UInt64 literal too big" at preset `pbo`. Their outputs are unchanged, and the error comes from translation, not from the checks.
- `lake build leanscript tests` succeeds, and `lake exe tests` passes 130/130.

No theorems were involved, so nothing was added to the Properties table. Everything is committed.

## Suggested follow-up

Two things I noticed but didn't change:
1. `fn_prime` (type `Unit → MyList Int`) is exported as a plain value, but a parameter of the same type is treated as a function to call. So `test1(fn_prime)` would fail in JavaScript. This is the project's general convention for `Unit → τ` definitions. I can export them as `() => value` instead if you'd like.
2. While writing the new test file I saw that structural recursion on your own datatypes (e.g. `MyList.app`) translates to a helper that builds a table of results and returns closures, rather than a loop or labeled block. It is correct (all checks pass) but slow and not stack-safe. I can work on translating it as a loop.

# Summary of changes for run 0d1082e6-1724-4bd0-a6fa-54d40319d898
Our JavaScript for `Tests/SnapshotsPBOPure/InlineReferenceOpArrayLength.lean` now matches the legacy output's shape on every definition, and is better on `test2` and `extern1`/`extern2`. While regenerating the snapshots I also found and fixed an optimiser slowdown that blew up exponentially. All checks and tests pass.

**Output compared with the legacy backend** (preset `pbo`):
```js
export const test1 = (fn) => [1, 2, fn()];
export const test2 = (fn) => { const x$1 = fn(); return [[1, 2, x$1], [3, 4], [x$1]]; };
export const fn_x27 = 0;
export const extern1 = [1, 2, 0];
export const extern2 = [extern1, [3], [0]];
export const test3 = extern1;
export const test4 = extern2;
```
- **Size tests:** these were already decided in the `Term -[optimize]-> Term` phase by `Term.knownSizes`.
- **`test2`:** calls `fn` once, where the legacy output calls it twice.
- **`extern1`/`extern2`:** computed to `0` at translation time, where the legacy output calls `fn$p(undefined)` when the module loads.
- **What was missing:** `extern2`, `test3` and `test4` used to repeat the earlier constants' values (`test3 = [1, 2, 0]`, …).

**Change 1: constants refer to earlier constants (`JsTerm/Lower/ShareConsts.lean`, `shareConstValues`).**
- **What it does:** inside a constant's value, any non-empty array, list, record or constructor that is written exactly like an earlier constant's whole value is replaced by that constant's name.
- **Phase:** `Term -[convert]-> JsTerm`, run next to `aliasFuns`. `Term` has no global names, so the `Term` phase can't express this.
- **What it doesn't touch:** function bodies keep their own literals (callers may update a returned array in place). Empty arrays are never shared.
- **Side effect elsewhere:** equal constants from unrelated definitions are also shared, e.g. `TestUInt16$test3 = TestUInt8$test3`. This is correct, because constants are never updated in place, but the legacy backend doesn't do it.

**Change 2: checks for nested arrays (`LeanScriptCli/Check.lean`).** `Array (Array …)` can now be checked against Lean, so `test2`, `extern2` and `test4` are compared too: 9 checks per preset instead of 5.

**Change 3: optimiser speed fix.** `BranchSpecialization01.lean` (nested case analyses on a four-constructor enum) didn't finish in 10 minutes; it now takes about 2 s.
- **Cause:** `Fin.optAll`, used by the renaming and substitution functions that every pass relies on, computed each branch several times, once per level of nesting.
- **Fix:** `Fin.optAllMemo` computes each branch once into an array (`LeanScript/Term/FinMemo.lean`). A `@[csimp]` theorem proves it equal to `Fin.optAll`, so only the compiled code changes and no existing proof is affected.
- **Side effect:** three `t.optimize = t'` examples in `Tests/TermTests/Optimize/OptimizeTest.lean` hit the heartbeat limit. This started when `Term.knownSizes` was added in an earlier run, not with this fix. They now use `kernel_rfl`, as an earlier example already did.

**Testing**
- **New snapshot:** `Tests/SnapshotsMy/ShareConstValues.lean` covers the edge cases (records, `Option`, empty arrays, `Array UInt8` on both presets, functions). It has 17 checks per preset.
- **New specs in `Tests/Main.lean`:** `inlineReferenceOpArrayLengthSpec`, and `nestedEnumCasesSpec`, which fails if `BranchSpecialization01` takes more than 60 s.
- **All snapshots regenerated:** every check passes under node. Some outputs changed that came from earlier optimiser work and had never been regenerated; for example `KnownConstructors` `test2`–`test5` are now translated.
- **Builds:** `lake build leanscript tests TyTests TermTests JsTerm` succeeds, and `lake exe tests` passes 129/129.
- **Known build failure:** building the whole `LeanScript` library still fails on `UsageAlgebra.lean`, which imports Mathlib; I didn't touch that file.

The file has no loops or recursion, so labeled blocks and loops didn't come into it. The full comparison is in `Tests/SnapshotsPBOPure/InlineReferenceOpArrayLength.md`. No theorems were requested, so nothing was added to the Properties table. Everything is committed.

## Suggested follow-up

Possible inconsistency I noticed but did not change: a top-level definition of type `Unit → Int` (like `fn'`) is exported as a plain value (`export const fn_x27 = 0;`). A parameter of the same type is taken as a JavaScript thunk (`test1 = (fn) => [1, 2, fn()]`). So `test1(fn_x27)` would fail in JavaScript. If you want these to work together, I can make such top-level definitions export as `() => value`, or document it as intended.

# Summary of changes for run c70a79e2-172d-4c6b-a9c0-e32d4d7e85a3


## Suggested follow-up

I reached this run’s time limit. Send “continue” to pick up where I left off.

# Summary of changes for run bfdae323-332d-4050-94b4-977c33721f58
The analysis of `InlineReferenceIfThenElse` is now formalized in Lean, in `Tests/TermTests/Optimize/KnownTestTest.lean`. Every theorem in it builds with no `sorry`.

That file sits on top of the formal work from the previous turn: the new optimizer rewrite `Term.knownTests` (`LeanScript/Term/Optimize/KnownTest.lean`), which drops a repeated test on the same condition. Its proofs are `Term.knownTests_eval` (the result of `eval` doesn't change) and `Term.numCalls_knownTests` (no calls are added). I also added `Term.knownTests_run`, the same result stated for a whole program.

The new file copies the snapshot's definitions (`RecA`/`RecB`/`RecC`, `fn`, `test1`, `extern1`, `test2`) and the variants `test7`–`test10` from `Tests/SnapshotsMy/IfThenElseKnownField.lean`, and translates them to `Term` inside Lean. It proves:
- **The snapshot itself:** the translations of `test1` and `test2` are already `ret 42`, they compute `test1`/`test2`, and their optimized versions compute `42`. This matches `const test1 = 42; const test2 = 42;` in the legacy output.
- **The optimizer computes the Lean functions:** for every input, the translations and the optimized versions of `test7` … `test10` compute `test7` … `test10` (`…_translation_run`, `…_optimized_run`). The same holds for `test7` after `Term.knownTests` alone (`test7_knownTests_run`).
- **The repeated tests are actually removed:**
  - The translation of `test7` tests `c` three times.
  - After `Term.knownTests` alone, one `if` is left: `if x2 then ret x4 else ret lean_int_add(x4, 2)`.
  - After the whole optimizer, it is one conditional, `cond(x2, x4, lean_int_add(x4, 2))`, which becomes `c ? x : x + 2` in JavaScript.
  - The final optimized forms of `test8`–`test10` are stated the same way.

The `…_run` theorems are checked by the kernel and use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The theorems that compare printed statements use `native_decide`, like the project's other snapshot tests, so they also rely on that tactic's compiler axiom.

`lake build leanscript tests TyTests TermTests JsTerm LeanScript.Term.Optimize.CountOptimize` succeeds. The new theorems are described in `Tests/SnapshotsPBOPure/InlineReferenceIfThenElse.md` and recorded as proved in the Properties table. Everything is committed.

# Summary of changes for run 7e41ece6-9e22-40ff-9720-4a9018452f9d
Our JavaScript for `Tests/SnapshotsPBOPure/InlineNever.lean` was already better than `InlineNever.js`, so its output hasn't changed. I added support for Lean's `@[noinline]` attribute, which is the Lean version of the `inline never` directive behind the reference output, plus a regression test. All tests pass.

**This file compared with the reference.**
- Ours: `export const foo = "foo"; export const test = "foo";`
- Reference: `const foo = "foo"; const test = foo; export { foo, test };`

The two are the same size, and ours doesn't make `test` read another binding. The reference keeps `test = foo` only because its PureScript source marks `foo` as `inline never`. The Lean file has no such marking, so writing the literal is the better output.

Nothing needed changing in any of the three phases:
- Turning Lean into `Term` already gives `ret "foo"` for `test` (see `InlineNever-Term-unoptimized.txt`).
- The convert step deliberately keeps a constant whose value is a literal as that literal (`aliasFuns` in `JsTerm/Lower/Module.lean`).

The file has no loops or recursion, so labeled blocks and loops didn't come into it.

**What I added: `@[noinline]`.**
- **New behaviour:** if a definition is just another name for one marked `@[noinline]`, the JavaScript now refers to that definition, even when its value is a literal (`export const test = foo;`). This matches what the reference does for `inline never`.
- **How:** `aliasFuns` in `JsTerm/Lower/Module.lean` takes a new optional list of `@[noinline]` names. `LeanScriptCli/Main.lean` collects those names from the Lean environment and passes them in. Both are part of the `Term -[convert]-> JsTerm` phase.
- **Why not the `Term` optimizer:** `Term` has no global names, so it has no way to refer to `foo`.
- **Limitation:** inside a larger expression the marked definition is still inlined and computed. For example, `foo ++ "!"` becomes `"foo!"`. Keeping a reference there would need global names in `Term`.

**Testing.**
- New snapshot `Tests/SnapshotsMy/NoInlineAlias.lean`, with its generated outputs. It covers:
  - a marked string, which becomes `test = foo`
  - an unmarked one, which stays `test2 = "bar"`
  - a marked array, which becomes `test3 = big`
  - a marked definition used inside an expression, which becomes `test4 = "foo!"`

  Its checks pass under node on both presets (7 each).
- I regenerated the other 9 snapshots that use `@[noinline]`. None of their outputs changed.
- New `inlineNeverSpec` in `Tests/Main.lean`, run on both presets. It checks the expected lines for both files and runs their checks under node.
- `lake build leanscript tests` succeeds and `lake exe tests` passes 126/126.

The full comparison is in `Tests/SnapshotsPBOPure/InlineNever.md`. No theorems were involved, so nothing was added to the Properties table. Everything is committed.

# Summary of changes for run 1fa0c318-29e2-42cc-af8c-1999b48ec9bd
The JavaScript we generate for `Tests/SnapshotsPBOPure/InlineCase01.lean` was already better than `legacy-backend/InlineCase01.js`, so I didn't change the compiler's output. What was missing was testing: `test2`, `test4` and `test5` had never been compared with Lean. That gap is now closed, and all checks and tests pass.

**Our output compared with the legacy backend.** The `Term -[optimize]-> Term` phase already inlines `maybe`, `maybe'` and `Option.elim`. It also moves the call to the lazy default `f ()` into the `none` branch. The convert phase then makes each `testN` a single function of all its parameters, and turns `g 1` applied to the field into one call:
```js
export const test2 = (f, g, o) => {
  if (o.tag === 0) {
    return f();
  }
  return g(1, o._1);
};
```
Where the legacy output differs:
- **Closures:** it is curried and allocates closures (`v2 => …`, and `$0 = g(1)`). Ours allocates none.
- **Eager call:** it calls `f()` up front, even when the option is `some`. Ours calls it only in the `none` branch.
- **Dead code:** it ends with an unreachable `throw new Error("UNREACHABLE")`. Ours has one tag test and no `throw`.
- **Integer addition:** its `1 + v2._val | 0` wraps around at 32 bits, which is wrong for Lean's `Int`. Ours gives the exact result: on the `pbo` preset it throws once the result no longer fits in 53 bits, and on `faithful` it uses `bigint`.

The file has no loops or recursion, so labeled blocks and loops didn't come into it.

Two small differences remain, both cosmetic:
- **Parameter names:** the option parameter is called `a` (`a1` in `test5`), the name Lean gives an unnamed parameter.
- **JSDoc:** the type parameters `α`/`β` are documented as `uint53(number)`, because they are read as `Nat`. The code itself works on values of any type.

**What I changed: check generation (`LeanScriptCli/Check.lean`).** The check generator could not produce sample arguments for a parameter that is a function of two arguments, such as `g : Int → α → β`. So `test2`, `test4` and `test5` got no checks. I added samples for such functions when both arguments and the result are `Nat` or `Int`. Each is passed as two fixed functions, written in Lean and as a JavaScript `(x, y) => …`, which is how the generated code calls them. Each preset now has 78 checks instead of 12, and all pass under node.

**Testing.**
- I regenerated every snapshot. Apart from this file, two others gained checks, all passing: 17 per preset in `SnapshotsMy/AppArity` and 4 per preset in `PrimOpInt02Configurable`. No `.js` file changed. The script still exits non-zero for the same reasons as before: the "literal too big" refusals on the `pbo` preset, and Lean panic messages printed while computing expected values.
- I added `inlineCase01Spec` to `Tests/Main.lean`. On both presets it checks the exact shape of each `testN`, checks there's no `maybe`, `elim` or returned closure, expects the 78 checks, and runs them under node.
- `lake build leanscript tests TyTests TermTests JsTerm` succeeds, and `lake exe tests` passes 125/125.

The full comparison is in `Tests/SnapshotsPBOPure/InlineCase01.md`. No theorems were involved, so nothing was added to the Properties table. Everything is committed.

# Summary of changes for run 41d95556-3d46-40de-ab73-cb1cd682ce85
The JavaScript we generate for `Tests/SnapshotsPBOPure/InlineArrayIndex.lean` was already as good as `InlineArrayIndex.js`, so its output hasn't changed. Each `test` is a constant: `{ tag: 1, _1: 1 }` … `{ tag: 0 }` for `test4`. The differences from the legacy output:
- **Encoding:** numeric tags and `_1` fields instead of `"some"`/`_val`. This is the encoding used for every union in the project.
- **`array` is exported:** it is a public Lean definition. `@[inline]` makes it inlined where it's used, but doesn't remove it from the module.

**Answer to the "need to inline?" comment:** no. I checked: without `@[inline]` the output is the same. Calls whose arguments are all known are computed while Lean is turned into `Term`, so the unoptimised `Term` is already `ctor#1(1)`. None of the three phases had work left for this file.

**What was missing, and what I fixed:**
1. **The output had never been compared with Lean.** The check generator only checked `array`, because it never compared results of union types like `Option Int`. Now non-recursive union results are printed as `i(fields…)` on both sides (`LeanScriptCli/Check.lean`). This file now has 5 checks per preset, and all pass under node. Regenerating every snapshot added 274 checks to other files (e.g. `OptionUnbox`, `Variant01`). They all pass, and no generated `.js` file changed.
2. **The bounds were checked twice when the index is a parameter.** This is the variant `array[i]?` with `i` a parameter, which is not in the file itself. It used to compile to `i < 3 ? { tag: 1, _1: uint53__lean_array_get(0, [1, 2, 3], i) } : { tag: 0 }`. It now compiles to `i < 3 ? { tag: 1, _1: [1, 2, 3][i] } : { tag: 0 }`.
   - **How:** the convert step's bounds tracking (`JsTerm/Lower/Bounds.lean`) now also learns from tests of the index against a literal (`i < k`, `i ≤ k`, `i == k`, `k ≤ i`, `k < i`). An index known to be below `k` gets the plain `a[i]`, both on an array literal of at least `k` elements and on an array variable known to hold at least `k`.
   - **Why not the `Term` phase:** `Term` has no unchecked array access, because the proof that the index is in bounds is erased.
   - **Snapshot:** the new `Tests/SnapshotsMy/ArrayIndexBounds.lean` covers these cases. It also has two where the test doesn't prove the bounds (`i < 4` on 3 elements), and those correctly keep the checked call. Its checks pass: 106 per preset.

The file has no loops or recursion, so labeled blocks and loops didn't come into it.

**Testing:** a new `inlineArrayIndexSpec` in `Tests/Main.lean` runs on both presets. It checks that `test1` … `test4` are those constants, that there are 5 checks, and that only the two unproved accesses in `ArrayIndexBounds` keep the checked call. It also runs all the check modules under node. `lake build leanscript tests TyTests TermTests JsTerm` succeeds, and `lake exe tests` passes 124/124. No theorems were involved, so nothing was added to the Properties table.

The full comparison is in `Tests/SnapshotsPBOPure/InlineArrayIndex.md`. Everything is committed.

# Summary of changes for run dfaddf62-079a-4fe4-949a-709d317bbd04
`test` in `Tests/SnapshotsPBOPure/Html.lean` now translates to JavaScript that matches `legacy-backend/Html.js` and is slightly smaller. Before this change nothing in the file was translated. All tests pass and the work is committed.

**What the output files showed.** `Html-pbo.js`, `Html-faithful.js` and both `-Term-*.txt` files were empty apart from the "not translated" notes. `test` was refused with "the recursive type Html is not declared in any signature". The reason is that `Html` is recursive through `List` (`children : List Html`). The tool normally reads `List α` as a plain JavaScript array, and a datatype can't have a recursive field inside one. So the tool's automatic declaration of the file's recursive types rejected `Html`.

**The fix.** It is in `LeanScript/GenElab/Read.lean` (`listNestedInElem`, used by `classify`). This is the step that turns Lean into `Term`, before the three phases you listed. When a list type is a constructor field of a type that recurses through it (`List Html`, `List (RoseTree Nat)`, `List (String × Obj)`), that list is now read as a cons-cell datatype in the same group as the type. All other lists (`List String`, …) stay arrays. The choice depends only on the type, so a given list type is read the same way everywhere in a program. The `Term` optimiser, the conversion and the `JsTerm` optimiser needed no changes: the optimised `Term` of `test` is already a single constructor tree.

**Result (both presets, identical apart from the header):**
```js
export const test = (user) => ({
  tag: 0, _1: "section",
  _2: { tag: 1, _1: { tag: 0, _1: "h1", _2: { tag: 1, _1: { tag: 1, _1: "Posts for " + user }, _2: { tag: 0 } } }, _2: … },
});
```
Like the legacy output, this is one object literal with children as cons cells. The differences:
- **Tags and fields:** numeric tags and `_1`/`_2` fields (the convention used throughout this project) instead of `"elem"`, `_tag`, `_children`.
- **No `render`:** the legacy file emits `render` without exporting it, so it is unused code there. Ours leaves it out because it is `private`.

`test` has no loops or recursion, so labeled blocks and loops didn't come into it.

**Testing.**
- A new `htmlSpec` in `Tests/Main.lean` runs on both presets. It checks that `test` is a single object literal with no statements or calls. It then runs it under node for three users (one containing quotes), renders the result in JavaScript the same way the file's `render` does, and compares that with Lean's `render (test user)` on a copy of the definitions.
- `leanscript --check` still writes 0 checks for this file, because the check generator can't yet print a value of a recursive datatype. The node test above is what exercises the output.
- I regenerated every snapshot: only the `Html` outputs changed and every node check passed. The log also contains Lean "index out of bounds" backtraces. Since no other output changed, they don't come from this change, but I didn't trace where they come from.
- I also tried a scratch file: `List (String × Obj)` and `Rose α` with `List (Rose α)` now translate and their checks pass. `List.length` on such a datatype list is still refused.
- `lake build leanscript tests TyTests TermTests JsTerm` succeeds and `lake exe tests` passes 123/123.

No theorems were involved, so nothing was added to the Properties table. The full comparison is in `Tests/SnapshotsPBOPure/Html.md`.

**Not done:**
- If `render` were made public it would still be refused, because it is defined by well-founded recursion (through `List.map`).
- The parts of the tree that don't depend on `user` could be built once as module-level constants instead of on every call. The legacy backend doesn't do this either.

# Summary of changes for run 6defa27c-394c-4442-9081-1bc91e21c7c1
The JavaScript we generate for `Tests/SnapshotsPBOPure/Heterogeneous01.lean` was already on par with `legacy-backend/Heterogeneous01.js`, so I didn't change the compiler's output. What was missing was testing: the file's check modules contained no checks, so the output had never been compared against Lean. I fixed that and added a regression test; all checks and tests pass.

**Output compared with the legacy backend.** Both translate `test1` to a constant record and `test2` to one record literal. Neither keeps the `Fns` record of closures, a `zipRecord` call or an intermediate `Args`. The `Term -[optimize]-> Term` phase already does all of this. The optimised `Term` for `test2` is one function: it destructures `args` once, does the add and the `!`, and builds one constructor. The later phases only print it, so there was nothing to add to the convert phase or the `JsTerm` optimiser. The file has no control flow, so labeled blocks and loops don't come into it. Three differences remain, all deliberate:
- **Integer addition:** the legacy `(1 + r1.a) | 0` wraps around at 32 bits, which is wrong for Lean's unbounded `Int`. Ours gives the exact result: on the `pbo` preset it throws once the result no longer fits in 53 bits, and on `faithful` it uses `bigint`.
- **Field names:** ours are `_1`, `_2`, … instead of `a`, `fst`, …, which is the naming used for every generated record in this project.
- **Parameter name:** ours keeps the Lean name `args` instead of `r1`.

**The fix: check generation (`LeanScriptCli/Check.lean`).** Checks weren't generated because the generator refused records containing a `Float`, and both `R1` (through `String × Float`) and `Args` have one. The reason for the refusal: Lean prints a float as `42.000000` while JavaScript prints `42`. Floats are now allowed as record fields, including in nested records. When a result holds a float inside a record, the check prints it by its bits, as Lean's side already did. Each preset now has 4 checks (`test1` and three calls of `test2`), and all pass under node.

**Testing.**
- I regenerated all snapshots with `scripts/leanscript-snapshots.sh`. Only the two `Heterogeneous01-*.check.mjs` files changed, and no node check failed. The script still exits non-zero for the same reasons as before: the "literal too big" refusals on the `pbo` preset, and Lean panic messages printed while computing expected values.
- I added `heterogeneous01Spec` to `Tests/Main.lean`. On both presets it pins the shape of `test1` and `test2`, checks there's no closure record or `zipRecord`, expects exactly 4 checks, and runs them under node. `lake build leanscript tests` succeeds and `lake exe tests` passes 122/122.

The full comparison is in `Tests/SnapshotsPBOPure/Heterogeneous01.md`. No theorems were involved, so nothing was added to the Properties table. Everything is committed.

# Summary of changes for run b13fba58-0869-4f88-9a27-d06188bdcb25
`test` in `Tests/SnapshotsPBOPure/Fusion02.lean` now compiles to one plain `for … of` loop that pushes onto the result array. Before this change it wasn't translated at all, and the output is now ahead of `legacy-backend/Fusion02.js`. The new code is in `Term -[convert]-> JsTerm` (`LeanScript/TermElab/ToTerm/StreamFusion.lean`). Node checks pass 8/8 on both presets, `lake exe tests` passes 121/121, and all work is committed. The rewrite is not proved correct; only the node checks and tests back it.

**Starting point.** Only `dropPrefix1` was translated. After inlining, `test`'s body was `toArrayLoop U U.seed #[]`, which couldn't be translated for two reasons:
- `toArrayLoop` (and `filterMapStep`) use well-founded recursion, and the `Term` language has only bounded loops.
- `U` is an `Unfold`, a structure with a field that is a type.

**The legacy backend's output** translates everything, since JavaScript is untyped, but at runtime it still has the whole structure:
- a chain of stream records whose `step` closures call each other;
- a `while (true)` inside `filterMapStep`, called through those closures;
- an outer `while (true)` in `toArrayLoop`;
- an `Option`/`Prod` record allocated per element at each stage;
- a copy of the array on every push (`[...v5, x]`), so building the result takes quadratic time.

**Output now (`Fusion02-pbo.js`):**
```js
export const test = (arr) => {
  let acc$1 = [];
  for (const e$2 of arr) {
    const x$3 = String(int53__lean_int_add(e$2, 1));
    if (string__lean_string_isprefixof("1", x$3)) {
      const x$4 = "2" + uint53__lean_string_drop(x$3, 1);
      if (x$4 !== "wat") { acc$1 = array__lean_array_push_mutable(acc$1, x$4 + "1"); }
    }
  }
  return acc$1;
};
```
There are no stream records, closures, `Option`/`Prod` values or recursion, so the stack can't overflow, and the push is in place. It's the same code as `Fusion01`'s `test`.

**How it works.** All the new code is in that one phase (the `Term` optimiser and the JavaScript phases are unchanged). It turns the whole pipeline into one `Array.foldl`, which the existing pieces then simplify and print as the loop. It matches the shape of each definition's body (read from its unfolding equation), not its name:
- **The loop that drains the stream** (here `toArrayLoop`): when the stream is empty it returns the accumulator; otherwise it calls itself with the next state and an updated accumulator.
- **Transformers** (here `mapU`, and `filterMapU`/`filterU` going through `filterMapStep`): each step either emits a value or skips to the next state, chosen by `if`/`match`.
- **The source** (here `fromArray`): `if h : s < arr.size then some (s+1, arr[s]) else none`.

The per-element work is composed from the draining loop down to the source and becomes the body of a fold over `arr`. If any part doesn't match these shapes, the rewrite does nothing and translation goes on as before. It's hooked into `trApp` in `Expr.lean`.

**Limitation:** the other `Unfold` definitions (`fromArray`, `toArray`, `mapU`, `filterMapU`, `filterU`, `overArray`, `toArrayLoop`, `filterMapStep`) are still listed as not translated, because the typed `Term` language can't represent a structure with a type-valued field. This is the same situation as the `Fold` helpers in Fusion01. Inside a first-order definition like `test` they are inlined and fused away.

**Testing.**
- I regenerated every snapshot. Only the `Fusion02` outputs changed, and every node check passed. The snapshot script still exits non-zero for the same reasons as before: the "literal too big" refusals on the `pbo` preset, and Lean panics printed while computing expected values (for example `get!` on `none`).
- A new `fusion02Spec` in `Tests/Main.lean` checks, on both presets, that `test` is translated as a single `for … of` loop with no `while`, no `toArrayLoop(` or `filterMapStep(` calls and an in-place push, and that the generated checks pass under node.
- `lake build leanscript tests TermTests TyTests JsTerm JsSpec LanguageJavascriptMini` succeeds, with no `sorry` in the new code.
- On a first run, 7 node-based tests hit their 30-second timeout because the snapshot script was running at the same time; run on its own, all 121 passed.

There were no new theorems this run, so I didn't add anything to the Properties table. The analysis and a phase-by-phase table are in `Tests/SnapshotsPBOPure/Fusion02.md`.

# Summary of changes for run d6a455d5-a356-4e1c-add6-c40a83ec91dd
For `test` in `Tests/SnapshotsPBOPure/Fusion01.lean`, the JavaScript output is now better than the purescript-backend-optimizer output in `legacy-backend/Fusion01.js`. The six `Fold`-typed helpers still aren't translated, while the legacy backend does emit them. All builds and tests pass.

**Output for `test`.** The legacy backend builds a cons list in a specialised `foldrMUnsafe` loop and converts it with `$lean_array_mk`. It also re-creates the step closure on every iteration, expands `startsWith`/`drop` into `memcmp` and `String.Slice` records, and goes through `Nat_reprFast`. Ours (`Fusion01-pbo.js`, 8/8 node checks pass on both presets) is one `for … of` loop that pushes straight onto the result array. It has no intermediate list, no closures and no recursion:
```js
let acc$1 = [];
for (const e$2 of arr) {
  const x$3 = String(int53__lean_int_add(e$2, 1));
  if (string__lean_string_isprefixof("1", x$3)) {
    const x$4 = "2" + uint53__lean_string_drop(x$3, 1);
    if (x$4 !== "wat") { acc$1 = array__lean_array_push_mutable(acc$1, x$4 + "1"); }
  }
}
return acc$1;
```
`dropPrefix1`, which didn't translate at all before, is now a single conditional expression.

**Changes, by phase (preferring the earliest phase that worked):**
- **Elaboration to Term** (`LeanScript/TermElab/ToTerm/Fusion.lean`):
  - inlines the non-recursive helpers, `flip`/`∘`/`id`, and projections of `Fold.run` out of structure literals;
  - rewrites `List.toArray (Array.foldr f [] xs)`, when the step only conses, into an `Array.foldl` that pushes;
  - rewrites the string slice operations to the `String.Internal` primitives.
  - Also fixed an existing bug: a `match` on an `if` failed to elaborate.
- **Term optimiser** (every pass proved to preserve the value):
  - New rewrite: a `case` on an `if` whose arms are constructors becomes an `if`, plus sharing into the case. `Term.caseCondTop_eval` and related lemmas are proved, along with "never adds calls" lemmas.
  - Calls with literal arguments can now be hoisted.
  - Dead bindings are now dropped *before* common-subexpression elimination and hoisting. Without this, a dead computation in `RecordUpdate` made `val + 1` run on every path. `Term.optimize_eval` and `Term.numCalls_optimize` were updated and rebuilt with only the standard axioms.
- **Term → JsTerm conversion** (`JsTerm/Lower/LoopAcc.lean`, `Tail.lean`, `Basic.lean`): a loop body now reads the accumulator variable directly instead of copying it into `const a = acc`. An iteration that leaves the accumulator unchanged emits nothing. The copy is kept when a closure in the body reads it. Loops stay plain `for` loops, so there's no stack growth.

**Snapshots.** I regenerated all of them. Many loop snapshots got simpler: `LoopState`, `CaseGuardedSweep`, `TcoHyper`, `LoopClosure`, `ArrayInPlace` and others no longer have the `const a$ = acc$; … acc$ = a$;` pattern. `KnownConstructors03/04` and `OptionUnbox` now translate more. All node checks pass. The only failures in the run are the existing "literal too big" errors in the `*Configurable` files on the pbo preset. The `PANIC` lines printed for `KnownConstructors04` come from Lean evaluating `get!` on `none` while generating expected values, not from the translator.

**Tests.** `lake build leanscript tests TermTests TyTests`, `JsTerm`, `JsSpec`, `LanguageJavascriptMini`, `LeanScript.WFTerm.Optimize` and `LeanScript.Term.Optimize.CountOptimize` all build, with no `sorry`. `lake exe tests` passes 120/120. One test example in `Tests/TermTests/Optimize/OptimizeTest.lean` (`copy.optimize = copyOpt`) now uses `kernel_rfl` because elaborator `rfl` timed out after the extra pass. As before, a plain `lake build` fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib; I didn't touch that file.

**Not translated.** `mapF`, `filterMapF`, `filterF`, `fromArray`, `toArray` and `overArray` take or return a `Fold`, a structure in `Type 1` with a field polymorphic over types. The Term language has no polymorphism over types, so these are still reported as "not translated". Inside a first-order definition like `test` they are inlined and fused away.

The analysis and a phase-by-phase table are in `Tests/SnapshotsPBOPure/Fusion01.md`. I removed the temporary debug hook, and everything is committed.

# Summary of changes for run f2675ed5-5421-4ee7-b66e-3b998422fefe
The JavaScript for `Tests/SnapshotsPBOPure/FunctionCompose03.lean` now matches `legacy-backend/FunctionCompose03.js` and is a bit shorter: `test1` is a single expression, and `test2` keeps one constant instead of two. All of this is committed.

**What the output files showed.** Before this change:
- `-Term-unoptimized.txt` forces the thunks again at every use. `test4` forces `x4 ()`/`x2 ()` five times.
- `-Term-optimized.txt`: the `Term` optimiser's common-subexpression elimination already shared these, so each thunk was forced once per call. That is the behaviour the comment in the file asks for.
- So the JavaScript was already correct. The only gap was cosmetic: the printer wouldn't put a constant used once in the function position of a call. For example, it printed `const x$1 = f(); const x$2 = g(); return x$1(x$2(a));`.

**The fix.** This step is about writing a value directly where it is used inside an expression. The `Term` is in A-normal form, where every intermediate result gets its own named binding, so the `Term` phase can't do it. The existing mechanism for it is in the JavaScript printer, so I extended that rather than adding a new pass. The changes are in `JsTerm/Syntax/Vars/Occs.lean`:
- **Function position:** a constant used once can now be written as the function being called. JavaScript evaluates the function before its arguments, so `f()(g()(a))` still calls `f`, then `g`, in the original order.
- **Chains of such constants:** the order check now accepts a chain where each constant is written inside the next. Previously it refused to inline `x$1` in `test1`.

Result (same on both presets, apart from number types):
```js
export const test1 = (f, g, a) => f()(g()(a));
export const test2 = (f, g, a) => { const x$1 = g(); return x$1(f()(x$1(a))); };
// test3/test4: two shared constants, as legacy
```
Legacy returns a closure from `(f, g)`; ours takes all three arguments at once, so a full call creates no closure. The trade-off: if Lean code partially applies `testN f g` and reuses the result, our version forces the thunks on every call, while legacy forces them once. There are no loops or recursion in this file, so labeled blocks and loops didn't come into it.

**Other snapshots.** I regenerated all 182 snapshot files. Only three others changed, all in the same harmless way:
- `LoopState` now prints `k$10()(x$7)`.
- `TcoHyper` now prints `return acc$2(a2)`.
- `UnpackArray01` now writes `uint53__lean_array_get(…)` directly as an argument of `fn1`.

Every node differential check passed. The script still exits non-zero, but only because of the same "literal too big" refusals on the `pbo` preset for the `PrimOpInt*Configurable` files as before; those outputs didn't change.

**Proofs** (new file `Tests/TermTests/Optimize/FunctionCompose03Test.lean`, stated on copies of the snapshot's definitions, no `sorry`):
- `test1_optimized_run` … `test4_optimized_run`: the optimised translation computes the Lean function for every `f`, `g`, `x`. These use only the standard axioms.
- Call counts before optimisation (4, 6, 8, 10) are checked by the kernel with `rfl`.
- Call counts after optimisation (4, 5, 6, 7) use `native_decide`, as the existing snapshot tests do. They show each thunk is forced once.

**Tests.** A new `functionCompose03Spec` in `Tests/Main.lean` does two things:
- It checks the compiled translations against Lean.
- On both presets it checks the exact `export const …` text, then runs the JavaScript under node with thunks that count how often they are forced. It checks both the values and that each thunk is forced exactly once per call.

`lake build leanscript tests TermTests` succeeds, and `lake exe tests` passes 120/120. Both proofs are in the Properties table, marked proved.

# Summary of changes for run 762ace71-d69b-4930-afd2-2bd5a4bda392
The JavaScript for `Tests/SnapshotsPBOPure/FunctionCompose02.lean` already matches purescript-backend-optimizer's `legacy-backend/FunctionCompose02.js`, and is slightly better. An earlier run on this project reached the same conclusion. I checked it again against a fresh build and didn't change the compiler or any files, so there was nothing new to commit.

**What the output files show.** I rebuilt `leanscript` and ran it on the file. All six outputs came out byte-identical to the committed ones.
- `-Term-unoptimized.txt` / `-Term-optimized.txt`: each `testN` is three nested closures (`f`, `g`, `x`). The body is a straight chain of calls, e.g. `test4` is `x4 x6; x2 x7; x4 x8; x2 x9; x4 x10`. The `∘` compositions are already gone at the `Term` level, and no closure is created for them. The only change optimisation makes is to the usage counts (`[ω]` becomes `[1]`). `f` and `g` are parameters, so their calls can't be inlined and there is nothing more for the `Term` optimiser to remove.
- JavaScript, on both the `pbo` and `faithful` presets:
```js
export const test4 = (f, g, a) => g(f(g(f(g(a)))));   // ours
const test4 = (f) => (g) => (x) => g(f(g(f(g(x)))));  // legacy
```
The body is the same call chain. Ours is uncurried, so a call builds no intermediate closures. The only other difference is the name of the last parameter (`a` instead of `x`), which is cosmetic.

So there is nothing left to optimise in any of the three phases (`Term` optimise, convert, `JsTerm` optimise). The file has no loops or recursion, so labeled blocks and loops don't come into it.

**Checks for this run.**
- `lake build leanscript tests TermTests` succeeds.
- `lake exe tests` passes 118/118. This includes `functionCompose02Spec`, which checks the exact `export const …` lines on both presets and runs the generated JavaScript under node against Lean's values.
- `Tests/TermTests/Optimize/FunctionCompose02Test.lean` has no `sorry`. It proves that the optimised translation computes each `testN` for every `f`, `g`, `x`, and that `test1`–`test4` make 2, 3, 4 and 5 calls after optimisation. The proofs of the printed text and of the call counts after optimisation use `native_decide`, like the existing snapshot tests.
- The Properties table entries for these results are already marked proved.

**One gap:** `leanscript --check` still writes 0 checks for this file, because it can't make sample inputs for parameters that are functions. The JavaScript is exercised only by the node script in `functionCompose02Spec`.

# Summary of changes for run ef3caf4c-0cce-4577-b803-5f23b0c558d0
The JavaScript for `Tests/SnapshotsPBOPure/FunctionCompose02.lean` was already as good as purescript-backend-optimizer's `legacy-backend/FunctionCompose02.js`, and slightly better, so I didn't change the compiler. I added proofs and a test so it stays that way.

**What the output files show.** I rebuilt `leanscript` and ran it on the file. All six outputs came out byte-identical to the committed ones.
- `-Term-unoptimized.txt`: each `testN` is three nested closures (`f`, then `g`, then `x`) whose body is a chain of calls, e.g. `test4` is `x4 x6; x2 x7; x4 x8; x2 x9; x4 x10`. Even before optimisation, the compositions `∘` don't create closures of their own.
- `-Term-optimized.txt`: the same code. The only change is that usage counts go from `[ω]` to `[1]`. `f` and `g` are parameters, so their calls can't be inlined, and there was nothing else for the `Term` optimiser to remove.
- JavaScript (`pbo` and `faithful` presets):
```js
export const test4 = (f, g, a) => g(f(g(f(g(a)))));   // ours
const test4 = (f) => (g) => (x) => g(f(g(f(g(x)))));  // legacy
```
The body is the same call chain. Ours is uncurried, so calling it builds no intermediate closures. The only other difference is the parameter name (`a` instead of `x`).

There are no loops or recursion in this file, so labeled blocks and loops didn't come into it.

**A gap I filled.** The generated `.check.mjs` files contain 0 checks. `leanscript --check` can't make sample inputs for functions whose parameters are functions, so nothing was actually running this JavaScript.

**Proofs.** These are in the new `Tests/TermTests/Optimize/FunctionCompose02Test.lean`, stated on copies of the snapshot's definitions, with no `sorry`:
- `test1_optimized_run` … `test4_optimized_run`: for every `f`, `g` and `x`, the optimised translation computes the Lean function. These use only `propext`, `Classical.choice` and `Quot.sound`.
- `test1_numCalls` … `test4_numCalls`: the translations make 2, 3, 4 and 5 calls. These are checked by the kernel with `rfl`.
- `…_optimized_numCalls`: optimisation keeps that same count.
- `…_optimized_pretty`: the printed optimised statements match `-Term-optimized.txt`.
- The last two groups use `native_decide`, as the existing snapshot tests do.

**Tests.** A new `functionCompose02Spec` in `Tests/Main.lean` does two things:
- It checks the printed statements and call counts, and compares the compiled optimised translations with the Lean functions on sample `f`, `g` and `x`, also with `f` and `g` swapped.
- On both presets it runs `leanscript` and checks the four exact `export const …` lines and that there's no runtime import. It then writes a small node script that calls each `testN` with concrete `f` and `g` (as `number` or `BigInt`, depending on the preset) and compares every result with Lean's value.

`lake build tests` succeeds, and the test executable passes 118/118. I added both proofs to the Properties table, and everything is committed.

# Summary of changes for run 75db1f90-3818-41ae-9be8-acabdcdbe08b
The JavaScript for `Tests/SnapshotsPBOPure/FunctionCompose01.lean` was already as good as the legacy `legacy-backend/FunctionCompose01.js`, so I didn't change the compiler. I added proofs and a regression test so it stays that way.

**What the output files show.** I rebuilt `leanscript` and ran it on the file. All six outputs are byte-identical to the committed ones, and node's checks pass 31/31 on both presets.
- `-Term-unoptimized.txt`: `test4` declares five closures and calls them in a chain. `test1`–`test3` do the same with 2, 3 and 4.
- `-Term-optimized.txt`: every `testN` is a closure that returns its literal (`ret "a"` or `ret "b"`). The `Term` optimiser has already inlined the calls and removed the closures.
- The JavaScript therefore matches legacy line for line:
```js
export const test1 = (a) => "a";   // legacy: const test1 = (_ignored) => "a";
export const test4 = (a) => "b";   // legacy: const test4 = (_ignored) => "b";
```
All the simplification already happens in the `Term -[optimize]-> Term` phase, so nothing was left for the later phases. There are no loops or recursion in this file, so labeled blocks and loops didn't come into it.

**Proofs.** These are in the new `Tests/TermTests/Optimize/FunctionComposeTest.lean`, stated on copies of the snapshot's definitions, with no `sorry`:
- `test1_optimized_run` … `test4_optimized_run`: the optimised translation computes the Lean function on every input. These use only `propext`, `Classical.choice` and `Quot.sound`.
- `test1_numCalls` … `test4_numCalls`: the translations make 2, 3, 4 and 5 calls. These are checked by the kernel with `rfl`.
- `…_optimized_numCalls`: no calls are left after optimisation.
- `…_optimized_pretty`: the printed optimised statements match `-Term-optimized.txt`.
- The last two groups use `native_decide`, as the existing snapshot tests do, because a kernel `rfl` ran out of heartbeats.

**Tests.** A new `functionCompose01Spec` in `Tests/Main.lean` does two things:
- It runs the compiled optimised translations and compares them with Lean.
- On both presets it runs `leanscript --check` and node, and checks the six exact `export const …` lines, that there's no runtime import, and that 31/31 checks pass.

`lake build tests` succeeds, and the test executable passes 116/116. The two new results are in the Properties table, and everything is committed.

# Summary of changes for run 794bc8c7-faff-473e-9934-026dcfbec113
The `Term`-level changes for `FloatLetRegression01` are now formalised in Lean, with no `sorry`. The JavaScript step, and the claim that the JavaScript matches the legacy output, are still only checked by tests, because the JavaScript conversion and printer are `partial def`s and Lean can't prove anything about those.

**Proved in the previous turn, still building**
- `Term.sinkWalk_eval` (`LeanScript/Term/Optimize/SinkLet.lean`): the new pass doesn't change `Term.eval`.
- `Term.numCalls_sinkWalk`: it doesn't change the number of calls.
- `Term.optimize_eval`, `optimizeN_eval` and `numCalls_optimize` include the new pass.
- `SinkLetTest.test_optimized_run`: the optimised translation of `test` computes `test` for every `f : Int → Int`. `litShare_optimized_run` does the same for a second example with repeated `String` and `Nat` literal arguments.

**Added in this turn**
- **What one step of the moving pass does** (`SinkLet.lean`):
  - `Term.sinkLet_letE`: in front of a `let` that isn't used once and doesn't read the moved computation, the computation moves past it and keeps going.
  - `Term.sinkLet_letE_one`: it stops in front of a `let` that is used once, so those keep their order.
- **When a call on a literal can be shared** (`Atom.lean`):
  - `SimpleComp.ofComp?_app_int`, `_nat` and `_str`: a call on an `Int`, `Nat` or `String` literal that doesn't return a function counts as one computation, which common-subexpression elimination can share.
  - `ofComp?_app_lit_fn`: a partial application on a literal never does.
- **Call counts for `FloatLetRegression01`** (`Tests/TermTests/Optimize/SinkLetTest.lean`):
  - `test_numCalls`: the translation makes 3 calls, checked by the kernel.
  - `test_optimized_numCalls`: the optimised translation makes 2, so `f 2` is computed once.
  - `litShare_numCalls` and `litShare_optimized_numCalls`: 4 calls, then 2.
  - The two counts after optimisation use `native_decide`, as the existing printed-`Term` theorems do, because evaluating three optimiser rounds in the kernel ran out of time.

The proofs not using `native_decide` rely only on `propext`, `Classical.choice` and `Quot.sound`.

**Not formally proved**
- The lowering change in `JsTerm/Lower/FromTerm.lean` (reusing an existing variable instead of declaring `const x$1 = a;`).
- The exact JavaScript text (`const x$1 = f(2); return { _1: f(1), _2: x$1, _3: x$1 };`).

Both are covered only by `floatLetRegressionSpec` in `Tests/Main.lean`, which runs `leanscript --check` and node on both presets.

**Checks:** `TermTests`, `TyTests`, `JsTerm`, `JsSpec`, `LanguageJavascriptMini`, `LeanScriptCli`, `HashableFloat`, `NonEmpty`, `leanscript` and `tests` all build, and `lake exe tests` passes 114/114. The new results are in the Properties table, and everything is committed.

# Summary of changes for run 0c9fd108-6c5c-4895-b250-8f546071d590
The JavaScript for `Tests/SnapshotsPBOPure/EtaReduceRegression01.lean` now matches the legacy output (`legacy-backend/EtaReduceRegression01.js`), and is better on two of the three functions. Before this change only `test` was translated. `identity` and `fold` were refused as "universe polymorphic", and `fold` would also have been refused for its instance parameters and its `f : Type → Type` parameter.

Both presets now print:
```js
export const identity = (x) => x;                       // legacy: same
export const fold = (dictFoldable, dictMonoid, a) =>    // legacy: curried, returns a closure
  dictFoldable(dictMonoid, identity, a);
export const test = (a) => (a.tag === 0 ? "" : a._1);   // legacy: if-chain + throw "UNREACHABLE"
```

**What changed, by pipeline phase.** None of the changes is in the `Term -[optimize]-> Term` phase.

1. **Lean → Term.** Nothing was missing from the optimiser; the definitions were refused by the translator itself (`ToTerm.lean`, `GenElab/Read.lean`, `Expr/Loops.lean`).
   - **Universes:** a definition polymorphic in universes is translated at one choice of universes (`α : Sort u` becomes `Type`, any other universe becomes `0`).
   - **Type constructors:** a parameter like `f : Type → Type` is replaced by the stand-in `fun _ => Nat`, just as type parameters are replaced by `Nat`.
   - **Instance parameters:** these are now ordinary parameters holding the dictionary. That is a record of the class's fields, or the field itself for a class with one field.
   - **Polymorphic class fields:** a field like `foldMap : {α m} → [Monoid m] → …` is read at the stand-ins. Using it at any other type is refused with an error.
   - **Point-free definitions:** a non-recursive definition that returns a function is read with that function's arguments added (eta-long form). Lean treats the two forms as equal by definition.
   - **Why eta is done here and not in the Term optimiser:** in the optimiser it would mean moving statements inside a lambda and re-proving the pass correct. Here it needs no new proof obligation. Without it, `fold` built a closure only to call it straight away.
2. **Term → JsTerm.** No change needed.
3. **JsTerm → JsTerm** (`JsTerm/Lower/Globals.lean`). A closure that reads only its own parameters, and whose code is exactly the code of a non-recursive function of the same module, is replaced by that function's name. So `(x) => x` becomes `identity`. This can't be done earlier because `Term` has no global definitions.

Parameter names in the output now skip type-constructor parameters but include instance parameters (`LeanScriptCli/Frontend.lean`). This file has no recursion, so labeled blocks and loops didn't come into it.

**Proofs** (in `Tests/TermTests/ToTerm/PolymorphismTest.lean`, on copies of the definitions; no `sorry`; only `propext`, `Classical.choice` and `Quot.sound`):
- `identityT_run`: the translation of `identity` computes `identity` on every argument.
- `foldT_run`: the translation of `fold` computes `fold` for every `Foldable` dictionary, every `Monoid` dictionary and every argument.

**Tests.**
- A new `etaReduceRegressionSpec` in `Tests/Main.lean` does three things:
  - It compares the compiled translations with Lean.
  - On both presets it checks that nothing is left untranslated, that the three exact lines above appear, and that node's 3/3 checks pass.
  - It calls `fold` from node with the `Foldable Option` and `Monoid String` dictionaries and gets the answers Lean gives.
- `lake exe tests`: 112/112 pass.
- `TermTests`, `TyTests`, `JsTerm`, `JsSpec`, `LanguageJavascriptMini`, `LeanScriptCli`, `leanscript` and `tests` build.
- The README and the module docs are updated.

**Effects on other snapshots.** I regenerated them; every node check that ran passes.
- `CaseGuardedSweep` and `RecData` now call the module's own function (`test4(…)`, `RecData$roseKids(…)`) instead of redefining it as a local closure.
- These are now translated: `InlineReferenceIfThenElse.fn`, `PrimOpArray01` `test2`/`test4`, and the generic `test*` helpers in `PrimOpNumber02` and `PrimOpIntDivConfigurable`. The last three take their instances as dictionary parameters.
- Some refusal messages changed wording (`Fusion01`, `InlineReferenceOpIsTag`).

**Known issues, all present before this change:**
- `KnownConstructors`, `KnownConstructors05` and `KnownConstructors06` hit the snapshot script's 600-second timeout, so their committed outputs were not regenerated. A build of the original commit run side by side was just as slow (`test6` alone takes over 100 seconds either way).
- `PrimOp*Configurable` still fail with "literal too big" under `pbo`.
- The `LeanScript` library as a whole still doesn't build, because `UsageAlgebra.lean` imports Mathlib; I built the targets above individually.

Everything is committed.

# Summary of changes for run f51e836d-36aa-4e87-921d-62a6e2ca14ca
The JavaScript for `Tests/SnapshotsPBOPure/EsSharedElse.lean` was already on par with the legacy output, and slightly shorter. The one gap was where the work happened: the merge was done by the JavaScript-side pass, not the `Term` optimiser. I moved it into the `Term -[optimize]-> Term` phase and proved it doesn't change `Term.eval`. The JS for this file is unchanged:

```js
export const test1 = (a, b, c) => {          // legacy:  if (a && b) { return 1; }
  if (a && b) { return 1; }                  //          if (c) { return 2; }
  return c ? 2 : 3;                          //          return 3;
};
```

**What the outputs showed.**
- `-Term-unoptimized.txt` has the nested `if`s, with the `else` (`c ? 2 : 3`) written twice.
- `-Term-optimized.txt` still had both copies (`if x2 then (if x4 then ret 1 else E) else E`).
- The `&&` came only from `JsBlock.mergeIte` in `JsTerm/Lower/MergeIte.lean`, which works on JavaScript blocks and has no proof.

**The new pass, `Term.mergeTestWalk`** (`LeanScript/Term/Optimize/MergeTest.lean`) runs inside `Term.optimize`, after `condWalk`. When two tests end in the same answer or jump, it merges them into one condition:
- `if p then (if q then X else E) else E` becomes `if (p && q) then X else E`.
- `if p then E else (if q then E else X)` becomes `if (p || q) then E else X`.
- When `E` is the other arm of the inner test, it uses `!q` instead.
- The inner test may also be a conditional answer `ret (q ? a : b)`.
- Chains are grouped to the left (`a && b && c`).

`EsSharedElse-Term-optimized.txt` is now `if cond(x2, x4, false) then ret 1 else ret cond(x6, 2, 3)`. The JavaScript-side pass is kept as a fallback for shared arms bigger than an answer or a jump.

**Proofs** (no `sorry`; only `propext`, `Classical.choice`, `Quot.sound`):
- `Term.mergeTestWalk_eval`: the pass doesn't change evaluation.
- `Term.numCalls_mergeTestWalk`: it never adds a call.
- `Term.optimize_eval`, `optimizeN_eval` and `numCalls_optimize` were updated and still build.

**Other snapshots.** I regenerated all of them. Three files changed in JS, all shorter:
- `CaseProduct` now ends `return f$1 === 4 && f$2 === 5 && f$3 === 6 ? "3" : "catch";` (it was an `if` plus a `return`).
- `CaseRecord` and `CaseHeuristics` change the same way.
- Every node check passes. The only failures are the existing "literal too big" errors in `PrimOp*Configurable` under `pbo`.
- On extra examples I tried, the output is now `a || b ? 1 : 2`, `a && b && c ? 1 : 3` and `a || !b ? 1 : 2`; before, the `||` cases weren't merged at all.

**Tests.**
- New `Tests/TermTests/Optimize/MergeTestTest.lean` checks evaluation is preserved for `test1` and two of the extra examples, and checks the printed optimised `Term` for all five functions.
- `Tests/TermTests/Optimize/CaseProductTest.lean` was updated to the merged form.
- New `esSharedElseSpec` in `Tests/Main.lean` compares all five functions with Lean on every input. It also runs `leanscript --check` and node on both presets (8/8 checks each).
- `lake exe tests` passes 110/110.

`EsSharedElse` has no recursion and no shared statement tails beyond this one, so labeled blocks and loops didn't come into it. I updated `README.md` and the module docs, and everything is committed. As in earlier runs, the `LeanScript` library as a whole doesn't build because `UsageAlgebra.lean` imports Mathlib, so I built the modules I needed individually.

# Summary of changes for run 527b5d4f-7879-418b-8147-0ed74feaaeba
The JavaScript for `Tests/SnapshotsPBOPure/EsPrecedence03.lean` now matches the legacy purescript-backend-optimizer output in shape, and it uses the right operator for Lean's types. Both presets print:

```js
export const test1 = (a, b) => (a >>> b) >>> b;   // legacy: (a >> b) >> b
export const test2 = (a, b) => a >>> (b >>> b);   // legacy: a >> (b >> b)
```

**What was wrong:** the optimised `Term` was already minimal (just the two shift calls), so nothing was left for the Term optimiser to do. The only gap was that `UInt32.shiftRight` became a call to `runtime.js` (`uint32__lean_uint32_shift_right(...)`, which is `a >>> (b % 32)`), plus an import.

**Why the fix is in the `Term -[convert]-> JsTerm` step:** `Term` has no notion of JavaScript operators, so this couldn't go in the `Term -[optimize]-> Term` phase. In the conversion step, the choice of operator for each extern comes from `scripts/js_ops_inline.json`. I added three entries there and regenerated `JsTerm/Ops/*` with `scripts/gen_js_ops.py`:
- `UInt32.shiftRight` → `a >>> b`
- `Int32.shiftRight` → `a >> b`
- `Int32.shiftLeft` → `a << b`

JavaScript already takes the shift count as `b & 31`, so the `% 32` in the runtime function is redundant. The `>>>` is deliberate: legacy's `>>` is signed, which works for PureScript's `Int` but would make a `UInt32` of `2^31` or more negative. The 8- and 16-bit shifts keep their runtime functions, because their count is taken modulo 8 or 16. The printer still parenthesises nested shifts (`(a >>> b) >>> b`), as Prettier does and as legacy's output has it. There is no recursion in this file, so labeled blocks and loops weren't involved.

**Proofs** (new `RuntimeSpec/InlineShift.lean`, no `sorry`, standard axioms only). These use the existing model of JavaScript's 32-bit operators in `RuntimeSpec/Model.lean`:
- `uint32_shift_right_inline`: JavaScript's `>>>` on two `UInt32`s is Lean's `>>>`, for every input.
- `int32_shift_right_inline` and `int32_shift_left_inline`: the same for `>>` and `<<` on `Int32`.

**Tests:**
- New `esPrecedence03Spec` in `Tests/Main.lean`:
  - It checks the model against Lean's shifts on sample values, including negative shift counts and counts of 32 or more.
  - It runs `leanscript --check` and node on `EsPrecedence03`: no runtime import, the expected lines, and 36/36 checks passing per preset.
  - It does the same for a temporary file of `Int32` shifts (34/34 per preset), since no snapshot covers those.
- `lake exe tests` passes 108/108.
- I regenerated all snapshots. Only one other file changed: `PrimOpIntBit01NonConfigurable` now has inline `a >>> b`, `a << b` and `a >> b`, and its 564 checks per preset still pass. The only failures are the existing "literal too big" errors in `PrimOp*Configurable` under `pbo`.

I also updated the `RuntimeSpec` row in `README.md`, and everything is committed. As before, the `LeanScript` library as a whole doesn't build because `UsageAlgebra.lean` imports Mathlib, which the project doesn't depend on. I built the targets I needed individually.

# Summary of changes for run 18d59ff4-b25d-46ca-b72b-b946e933d0d0
The JavaScript for `Tests/SnapshotsPBOPure/EsPrecedence02.lean` now matches the legacy purescript-backend-optimizer output on 4 of the 5 functions and is shorter on `test3`. Results are unchanged, and that is proved in Lean. Both presets print:

```js
export const test1 = (a) => a + a + a + a;   // legacy: same
export const test2 = (a) => a + a + a + a;   // legacy: same
export const test3 = (a) => a - a + a + a;   // legacy: a + a + (a - a)
export const test4 = (a) => a - a + a + a;   // legacy: same
export const test5 = (a) => a - a + a + a;   // legacy: same
```

**What was wrong.** The old output was already correct; it only had extra parentheses (`a + (a + (a + a))`, `a + (a + (a - a))`, `a - a + (a + a)`). Legacy drops them by regrouping, but IEEE addition is not associative, so that is not safe in general. Legacy only gets the right answer here because every operand is the same `a`.

**The fix is in the `Term -[optimize]-> Term` phase.** It is a new step in `Term.arithWalk`, in `LeanScript/Term/Optimize/FloatComm.lean`, and uses only exact float identities:
- **Swapping operands:** the two sides of a float `+` or `*` are swapped when that needs fewer parentheses. So `a + (a + a)` becomes `(a + a) + a`, and `x * (y / z)` becomes `y / z * x`.
- **One regrouping:** `(b - b) + (y + z)` (or the mirror image) becomes `((b - b) + y) + z`, when both `b` are written the same way. This is what fixes `test5`.

**Proofs** (no `sorry`, standard axioms only):
- `Neu.floatComm_eval`: the new step does not change evaluation, so `Term.optimize_eval` still builds.
- `Float.add_comm` and `Float.mul_comm` (with Float32 versions), in `HashableFloat/Commute.lean`: these hold bit for bit for every float, `NaN`, infinities and `-0` included, in Lean's float model.
- `Float.sub_self_add_add`, in `HashableFloat/SubSelf.lean`: `(b - b) + (y + z) = ((b - b) + y) + z` bit for bit for every float. On the way it proves that `b - b` is `+0` or `NaN`, and that a sum is `-0` only when both operands are `-0`. So the generated JavaScript stays exact even on inputs Lean's `HashableFloat` excludes.

**Side effects:**
- `AssocNumberOps` output changed. For example, `1 + (2 + x + x + x + x + 3) + 4` is now `2 + x + x + x + x + 3 + 1 + 4`. Its node checks still pass; no other snapshot changed.
- `--float-reassoc` now regroups both before and after optimising, so it still reproduces the legacy `AssocNumberOps` output exactly.

**Tests:**
- New file `Tests/TermTests/Optimize/FloatCommTest.lean`. It checks evaluation is preserved for `test1`, `test3` and `test5`, and checks the printed optimised `Term` for all five functions plus three extra cases. One of those confirms `a - (a + 2)` is left alone.
- `Tests/TermTests/Optimize/AssocNumberOpsTest.lean` was updated to the new printed forms.
- `esPrecedence02Spec` in `Tests/Main.lean` compares values with the Lean functions bit for bit on sample floats, and runs `leanscript --check` plus node on both presets (40/40 checks each).
- `lake exe tests` passes 106/106.
- I regenerated all snapshots. The only failures are the existing "literal too big" ones in `PrimOp*Configurable` under `pbo`.

This file has no recursion, so labeled blocks and loops didn't come into it. The READMEs and module docs are updated, and everything is committed.

One thing in the existing project: the `LeanScript` library target as a whole doesn't build, because `LeanScript/Term/Syntax/UsageAlgebra.lean` imports Mathlib, which the project doesn't depend on. I built the needed modules individually instead.

# Summary of changes for run eb49fd69-3145-4583-8065-cbbc647ed39a
`EsPrecedence01.test1` now compiles to `export const test1 = (f) => f;` under both presets (`pbo`, `faithful`). That beats the legacy purescript-backend-optimizer output, which still calls `f` up to three times plus `f(b)` and builds nested closures. The change is a new pass in the `Term -[optimize]-> Term` phase, and it is proved not to change `Term.eval`.

**What was there before**
- `-Term-unoptimized.txt`: `f` is called 5 times. `a`, `b` and `()` all have type `Unit`, so `f a`, `f b` and `f ()` are the same call.
- `-Term-optimized.txt`: the existing passes had already shared these into one call, leaving `val k3 := lazy (let x4 := x2 (); ret x4); ret k3`. The JS was `(f) => () => f()`, a new delay that only calls `f`.
- That one call is the whole answer, because `test1 f a b = f ()` (if `f ()` is false, `y` is true and the result is `f ()`; if true, everything is `f ()`).
- `.check.mjs` had 0 checks, because parameters of type `Unit → Bool` and trailing `Unit` parameters had no samples.

**The new pass, `Term.delayEta`** (`LeanScript/Term/Optimize/DelayEta.lean`)
- A known delay whose body only forces another delay `e` and returns its value is `e` itself. This covers `lazy (let x := e (); ret x)` (that is, `() => e()`) and the same with `thunk`/`force`.
- Every mention of such a delay is replaced by `e`, and the existing dead-code pass then removes the delay. Replacements are made only when the levels match, so the pass changes only the pure expressions in a statement, never its shape.
- It runs inside `Term.optimize`, after `openCall` and before `inlineRet`.

**Proofs** (`LeanScript/Term/Optimize/DelayEtaEval.lean`, no `sorry`, only the standard axioms)
- `Term.delayEta_eval`: the pass does not change the result of evaluation.
- `Term.numCalls_delayEta`: it keeps the number of calls the same.
- The overall theorems that the optimizer preserves evaluation (`optimize_eval`, `optimizeN_eval`) and never adds calls (`numCalls_optimize`) were updated and still build.

**Checks for lazy parameters** (`LeanScriptCli/Check.lean`)
- A parameter of type `Unit → Bool/Nat/Int/String` now gets two sample delays, e.g. `() => true`.
- A run of trailing `Unit` parameters becomes one `()` call, e.g. `test1(() => true)()`.
- A function whose parameters are all `Unit` is exported as a constant, so it is read rather than called.
- `EsPrecedence01` now has 2 checks per preset, and both pass.
- `InlineCase01`, `InlineReferenceOpArrayLength` and `InlineReferenceRecordUpdate` also gained checks; all pass.

**Tests**
- `Tests/TermTests/Optimize/CseTest.lean`: the call count after optimization is now 0 (it was 1). I added two small examples, `eta` and `etaArg`; with `etaArg`, a delay passed as an argument to another function is also replaced by the delay it forces.
- `Tests/Main.lean` has a new `esPrecedence01Spec`. It checks the call counts, the printed optimized `Term`, the values, the pass on its own, and runs `leanscript --check` with node on both presets. `lake exe tests` passes 104/104.
- I regenerated all snapshots. No other JS output changed. The only failures are the existing "literal too big" errors in the `PrimOp*Configurable` files under `pbo`.

This file has no recursion, so labeled blocks and loops don't come into it. I also updated the READMEs and the module docs. Everything is committed.

One gap I left: Lean's `Thunk.mk (fun _ => t.get)` translates to a lazy wrapped around a thunk force, and the new pass does not simplify it. The two delay kinds differ, so it needs a separate rewrite, and this file doesn't use it.

# Summary of changes for run 766b0177-2811-4150-9fbd-4e092f1dba76
The output for `Tests/SnapshotsPBOPure/EscapeIdentifiers.lean` now uses the same escape style as purescript-backend-optimizer, and it improves on it: no two different Lean names can get the same JavaScript name, and I proved this in Lean.

**What was wrong**
- The two output files differed only in the exported name. The Term files are just `ret 42`, so there was nothing to optimize.
- Our old name was `a_b_________`, because every character that isn't allowed in an identifier became `_`. That loses information: `a.b`, `a'b` and `a_b` all came out as `a_b`.
- PBO writes `a_u2eb_u20_u3f…_u2192`. Its escapes have no fixed length, so `_u2eb` could be read either as `.` then `b`, or as the single character U+02EB.

**What it produces now**
```js
export const a_x2eb_x20_x3f_x24_x24_x20_x5c_x22_x20_u2192 = 42;
```
- Each escape is as short as PBO's, but always has the same number of digits: `_xHH` for codes below 0x100, `_uHHHH` below 0x10000, and `_UHHHHHH` above that.
- The Lean name really does contain a backslash (`«…\" →»`), which shows up as `_x5c`. The PureScript name has no backslash.
- The other rules:
  - Letters and digits stay as they are.
  - Non-ASCII letters that JavaScript allows in identifiers (`α`) stay as they are.
  - `_` stays, unless the next character is `x`, `u` or `U`, so it can't be mistaken for the start of an escape.
  - A digit at the start is escaped.
  - Reserved words and globals the generated code relies on (`class`, `Math`) get `_x` added at the end.
  - Name parts are joined with `$`.

**Where the change lives.** This is about naming, not optimization, so neither the Term nor the JsTerm optimizer could handle it. It sits in the Term → JsTerm conversion step, in a new file, `JsTerm/Lower/Ident.lean`. `LeanScriptCli/Main.lean` now uses it for exported names. Parameter names keep their short form (`x'` → `x_`), because they are local and duplicates are already renamed. The labeled blocks/loops preference doesn't come into play: this file has no recursion.

**Proof.** `MoreJs.Ident.name_injective` says two non-empty Lean names with the same JavaScript name are equal. It is proved by decoding: `decodeName_name` recovers the original name from the JavaScript one. The file has no `sorry`, and the proof uses only the standard axioms.

**Tests**
- I added `escapeIdentifiersSpec` to `Tests/Main.lean`. It checks sample escapes and that names decode back, then runs `leanscript --check` on this file and confirms both presets' node checks pass.
- `lake exe tests` passes 100/100.
- I regenerated all snapshots. The only failures are the existing `PrimOp*Configurable` "literal too big" ones under the pbo preset.
- Other exported names that changed, with their node checks still passing:

| Before | Now |
|---|---|
| `instInhabitedColour$default_` | `instInhabitedColour$default` (reserved words are now checked against the whole name, not each part) |
| `swapSum_` | `swapSum_x27` (from `swapSum'`) |
| `fn_` | `fn_x27` (from `fn'`) |
| `eval_` | `eval_x` |

Everything is committed.

# Summary of changes for run 7b417144-dae3-4fc6-89da-213e81ee6e7b
The generated JavaScript for `DefaultRulesSemigroup02` now matches the legacy purescript-backend-optimizer output, and is ahead of it in a few places. Both presets (`pbo`, `faithful`) pass all 244 generated runtime checks.

**What was wrong at the start**
- `test4` was not translated at all. Adding two constant arrays failed with a type mismatch, because a constant array result could not be turned into a literal.
- `test3` called the runtime array-append function on `["hello"]`, which pulled in an import.
- `test1` and `test2` were full copies of `appendR` instead of other names for it.

**Changes, by pipeline phase**
1. **Term → Term optimizer.** I added a new pass, `Term.knownLits`, in `LeanScript/Term/Optimize/KnownLit.lean`. Inside array and list append chains, it writes known constant array/list literals in place. It runs as part of `Term.optimize`, after `condWalk` and before `appendWalk`. It is proved not to change evaluation (`Term.knownLits_eval`), and the overall theorem that the optimizer preserves evaluation (`optimize_eval`) and the call-count proofs still hold. Both theorems use only the standard axioms, and the files contain no `sorry`.
   - In the Term step that turns an append of fixed results into a literal (`LeanScript/TermElab/Anf/Render.lean`), array/list appends and pushes of literals now become a literal. This is what fixes `test4`.
2. **Term → JsTerm conversion and the CLI.** A definition that only renames an earlier one is now printed as `export const test1 = Inline$appendR;`, with no import collected for it. Constants whose value is a literal are left as literals, so InlineNever still prints `test = "foo"`.
3. **Printing.** A spread of an array literal is spliced into the surrounding array, so `[...[x, ...a], y]` prints as `[x, ...a, y]`.

**Result compared with legacy**, in all four namespaces:
- `appendR` is a single function taking both arguments, `(a, b) => ({_1: a._1 + b._1, _2: [...a._2, ...b._2]})`. Legacy curries it into two nested functions.
- `test1` and `test2` are other names for `appendR`, as in legacy.
- `test3` is `(b) => ({_1: "hello" + b._1, _2: ["hello", ...b._2]})` everywhere. Legacy gets this form only in AlwaysInline and leaves a partial call elsewhere.
- `test4` is the constant `{_1: "hello, World!", _2: ["hello", "World!"]}` everywhere. In Noinline, legacy still makes the calls.
- There are no runtime imports.
- Two differences remain:
  - Field names are `_1`/`_2` rather than `foo`/`bar`. That is the project-wide naming convention, which I did not change.
  - Legacy splits record parameters into separate fields (`a_bar, a_foo`); I did not do this.
- The labeled blocks/loops preference did not come up, because this file has no recursion.

**Other effects and fixes**
- `STArray02` used to fail to translate with the same mismatch as `test4`. It now translates and passes its 16 checks.
- `TopLevelHygiene02` now prints `test2 = test1`.
- Generating checks for `SnapshotsMy/Html` hit a stack overflow, recursing from `Array Html` back to `Html`. That is fixed in `LeanScriptCli/Check.lean`.

**Tests**
- I added `knownLitSpec` and `defaultRulesSemigroup02Spec` to `Tests/Main.lean`; `lake exe tests` passes 97/97.
- I regenerated all snapshots. The only failures are ones that were already there: the `PrimOp*Configurable` files whose integer literals are too big for a JavaScript number under the `num` preset.

Everything is committed.

# Summary of changes for run c94407ab-d1ec-4176-bed3-7a8ba4063fb7
I removed the special-casing you pointed out and replaced it with one rule in one place. The generated JavaScript is the same as before.

**What was wrong.** The printer named a constant like this:
- It first printed the bound value to JavaScript.
- Then, only if the binder's hint happened to be the string `"x"`, it pattern-matched the printed `f(x)` and checked the set of counter-free names to see whether `f` and `x` were parameters.
- So the hint string was quietly overridden from the outside, and the rule worked on printer output instead of on the program being printed.

**What it is now** (`JsTerm/Print/Mini/Block.lean`, `JsTerm/Print/Mini/Basic.lean`):
- `constName sc hint e` decides the name of every printed `const`:
  ```lean
  match ← e.valueName? sc with
  | some n => niceName n      -- named after its value, no counter if free
  | none => freshName hint    -- named after its binder, `hint$k`
  ```
- `JsExpr.valueName?` matches on the program itself (`.app (.cvar f) (.cons (.cvar a) .nil)`), not on the printed text. It answers `fx` when both variables are local names without a counter.
- A small helper, `plainLocal?`, answers "is this a local name without a counter?". It replaces the old `callHint?` (removed) and the inline lookup in `blockToMini`.
- The `hint == "x"` test is gone, so the rule no longer depends on which hint string the lowering happened to pass.
- The `.const` case in `blockToMini` is now three lines. It prints the value first, as before, so the numbering of names created inside the value doesn't change.
- I updated the module documentation in `JsTerm/Print/Mini.lean` to match.

**Checks**
- `JsTerm`, `leanscript` and `tests` build.
- `lake exe tests` passes 95/95, including the naming tests for `DefaultRulesSemigroup01` (`const fx = f(x);`, the `fx$1` fallback when `fx` is taken, and so on).
- I regenerated every snapshot with `scripts/leanscript-snapshots.sh`. No output file changed, and every node check reports 0 failed, so the generated code is the same as before.

This change only touches how code is written; there are no new theorems. The work is committed.

# Summary of changes for run d6b412ee-0fd1-4457-aafb-517a80513eca
The generated JavaScript for `Tests/SnapshotsPBOPure/DefaultRulesSemigroup01.lean` already matched purescript-backend-optimizer's `legacy-backend/DefaultRulesSemigroup01.js`. I regenerated it with the current code and nothing changed. Ours is slightly better because it takes all parameters at once instead of curried, so it builds no intermediate closures:

```js
export const test1 = (f, g, x) => f(x) + g(x);
export const test2 = (f, g, x) => {
  const fx = f(x);
  const gx = g(x);
  return fx + gx + fx + gx;
};
```

The duplicate `f x` and `g x` calls in the unoptimised Term are already merged by the existing `Term -[optimize]-> Term` phase. This file has no recursion, so labeled blocks and loops don't apply here.

**Analysis of the output files**
- **`-Term-unoptimized.txt`:** `test2` calls `x2 x6` and `x4 x6` twice each.
- **`-Term-optimized.txt`:** each call is bound once (`x7`, `x8`).
- **`-pbo.js` / `-faithful.js`:** the same code as above under both presets; only the doc comments (JSDoc) differ.
- **`.check.mjs`:** before this run they had no checks, because the check generator could not make arguments of function type.

**Changes**
1. **Shared calls now come out in source order** (`LeanScript/TermElab/ToTerm/Expr/Calls.lean`). For a variant like `f i ++ f n ++ f i ++ f n`, the output used to compute `f(n)` before `f(i)`.
   - **Cause:** the Lean-to-`Term` step bound a repeated argument of a built-in call before the argument that contained it.
   - **Fix:** that step now leaves calls of local functions alone, and the `Term` optimiser's existing duplicate-call merging shares them in first-use order. The output is now `const fi = f(i); const fn = f(n);`.
   - No JavaScript snapshot changed from this, so no existing output depended on the old order.
2. **Automatic checks for function parameters** (`LeanScriptCli/Check.lean`).
   - Parameters of type `Nat/Int/String → String`, `Nat → Nat` or `Int → Int` (also behind an `abbrev` like `F`) now get two fixed sample functions, written in both Lean and JavaScript, e.g. `fun x => "[" ++ Int.repr x ++ "]"` and `(x) => "[" + String(x) + "]"`.
   - `DefaultRulesSemigroup01-*.check.mjs` now runs 28 checks per preset against Lean's answers, and all pass.
   - Eight other snapshots also gained passing checks: `TcoHyper`, `TcoMc91`, `KnownConstructor07`, `RecordUpdate`, `FloatLetRegression01`, `TopLevelHygiene01/02`, and `DefaultRulesSemigroup01` itself.
   - I also replaced a deprecated `levelOne` with `Level.one`.

**Tests** (`Tests/Main.lean`)
- One new assertion checks that the four-call variant keeps its calls in source order.
- One new IO test runs `leanscript --check` on this file and checks that node reports `28 passed, 0 failed` under both presets.

**Checks run**
- `lake exe tests` passes 95/95.
- `leanscript`, `tests`, `TermTests`, `TyTests`, `JsTerm` and `LeanScriptCli` build.
- I regenerated all snapshots with `scripts/leanscript-snapshots.sh`. Only `.check.mjs` files changed, and every node check passes. The script still exits with status 1, but only because of the "literal too big" errors that were already there in the `PrimOp*Configurable` files under `pbo`.

This was a code-generation task, so there are no new Lean theorems. Everything is committed.

# Summary of changes for run 7a8ddc39-7385-488d-923d-58150ef23663
`DefaultRulesSemigroup01` now produces the same JavaScript as purescript-backend-optimizer's `legacy-backend/DefaultRulesSemigroup01.js`, except that it takes all parameters at once instead of curried. That part is better: no intermediate closures are built.

**What I found.** Before this run, the generated code was already as good as the legacy file. Only the names differed:
- `test1` printed `(f, g, a) => f(a) + g(a)`. Legacy uses `x` for the last parameter.
- `test2` named its two shared calls `x$1` and `x$2`. Legacy uses `fx` and `gx`.

The work on the code itself was already done in `Term -[optimize]-> Term`. The unoptimised Term (`-Term-unoptimized.txt`) calls `f x` and `g x` twice each, and the existing `Term` optimiser merges them into one call each. So no new optimisation was needed in any of your three preferred phases. This file has no recursion, so labeled blocks and loops don't come into it.

**Changes.** Both are about naming, so they live in the front end and the printer rather than in the optimisation phases:
1. **Parameter names** (`LeanScriptCli/Frontend.lean`, `paramNames`): when a definition's body is itself a function once instances are unfolded, its parameter names are taken from that function. Here, `f ++ g` unfolds to the instance's `fun x => f x ++ g x`, so the parameter is now `x`. This step only runs when the body has a function type.
2. **Names for call results** (`JsTerm/Print/Mini/Basic.lean`, `Block.lean`, `Mini.lean`): when a parameter is called on a parameter, the result is named after both, with no counter (`const fx = f(x);`). The name is only used if it is free. Otherwise it keeps a counter (`fx$1`). A name counts as free if it is not:
   - a parameter or another name chosen this way;
   - a name defined in the module (its functions, imported runtime functions, its own helpers);
   - a JavaScript reserved word or a global the generated code may read (`BigInt`, `Math`, `undefined`, …).

**Result** (both presets):
```js
export const test1 = (f, g, x) => f(x) + g(x);
export const test2 = (f, g, x) => {
  const fx = f(x);
  const gx = g(x);
  return fx + gx + fx + gx;
};
```

**Tests and checks**
- New IO test `defaultRulesSemigroupSpec` in `Tests/Main.lean`:
  - It checks the exact output under both presets. It also runs both functions in node with call-counting `f` and `g`: the answers are `[5](5)` and `[5](5)[5](5)`, with 4 calls in total, so each call is made only once.
  - A second case checks the naming fallback: in modules with functions called `fx` and `ab`, the results stay `fx$1` and `ab$1`, while free names `fi` and `fn` are used as is.
- `lake exe tests` passes 94/94. `leanscript`, `tests`, `JsTerm`, `JsSpec`, `TermTests`, `TyTests`, `LeanScriptCli` and `LanguageJavascriptMini` build.
- I regenerated all snapshots with `scripts/leanscript-snapshots.sh`. Only `DefaultRulesSemigroup01-*.js` and `RecordUpdate-*.js` changed (`x$1 = f(y)` became `fy = f(y)`). All node checks pass. The script still exits with status 1, but only because of the "literal too big" errors that were already there in the `PrimOp*Configurable` files under `pbo`.

**Remaining gaps**
- `DefaultRulesSemigroup01-*.check.mjs` contains no automatic checks, because the check generator can't make sample function arguments. The new IO test covers this file by hand.
- In a variant I tried, `f i ++ f n ++ f i ++ f n`, the shared calls come out in reverse order (`f(n)` before `f(i)`). The order is already reversed in the unoptimised Term output. That is harmless because the code is pure, and I didn't change it.

This was a code-generation task, so there are no new Lean theorems. Everything is committed.

# Summary of changes for run 58b66ce9-33df-41e1-bb9a-57ab8d9deb43
I wrote `proposals/ExactUsageProposals.md` with four proposals for making `Term` usages exact by construction. Each one has a toy `Term` in `proposals/ExactUsageToy.lean`. Nothing under `LeanScript/` was changed. The toy file compiles with `lake env lean proposals/ExactUsageToy.lean` with no errors, warnings or `sorry`, and its main theorems use only Lean's standard axioms. It isn't part of the Lake build, so there are no build targets to report.

**What causes the wrong usages**
- The Lean-to-`Term` step never counts. `TermElab/Anf.lean` and `Anf/Emit.lean` write `.many` on every binder on purpose: `letE`, `letV`, `join`, `Val.lam`, the fold parameters, and case fields (passed as `[]`, which becomes `many`). They leave exact counts to `Term.dce`.
- The current types only rule out referencing a binder marked `zero`. Nothing links `one` or `many` to the body, so even marking a variable `one` when it is used twice would type-check.
- In the snapshot, `k1 [ω]` is the wrong one (it is used once). `x2 [ω]` (4 uses) is correct under today's three-value `0 | 1 | ω`; it only becomes wrong once counts are exact (`x2 [4]`).
- **Step 0**, needed whichever proposal you pick: the elaborator already computes each piece's level bottom-up (`Out.lv`). It can compute a `uses` field the same way and read each binder's count from it instead of writing `.many`.

**Usage types.** All proposals use `UsageN` (0, 1, 2, …, ω) and `UsageNPos` (1, …, ω), with `+` along a path, `max` across branch arms, and ω inside closure or loop bodies. With `UsageNPos` on definition binders, dead code no longer type-checks. That clashes with `Term.dce` deliberately keeping some dead bindings to preserve levels; the document gives two ways around it.

**The four proposals.** Each toy keeps the three contexts (known values, unknowns, join points) and has an erasure to a shared untyped syntax, a reference count, an evaluator, and the `AssocArrayAppend` example. For each, I proved that the usages it carries equal the recount of its erasure:
1. **QTT contexts:** each context entry carries its exact count, and terms split contexts with `Add`/`Max`/`Scale` witnesses. Proved: `P1.Term.exact`, `binder_exact`, `unique`. Downside: the split is an input, so the elaborator has to compute it, and evaluation splits environments.
2. **Hodas–Miller `{Γ} t : τ {Δ}`:** input and output counters are threaded through; a binder enters at 0 and its annotation is the count it leaves with. Lean computes the outputs itself (`body4.1 = ⟨[], [4], []⟩` by `rfl`), and the snapshot's annotations are rejected. Proved: `P2.Term.exact`, `exact_closed`.
3. **Usage vector as an index, like `Lvl` today** (your proposal 1 taken literally): binders store nothing, and the annotation is read from the head of the scope's vector. Proved: `P3.Term.exact`, `letV_use_exact`. With input counters at 0, this is the same information as proposal 2.
4. **Checked cache:** the term type is unchanged, and smart constructors build a subtype that only holds exact annotations. Proved: `P4.ETerm.unique`, and the snapshot's annotation is refuted by `decide`.

**Recommendation.** Do step 0, then proposal 3, which is the smallest change because passes already return levels the same way. Choose proposal 2 if you want the counter to belong to the context. The document also covers migration cost file by file, and two pitfalls found while building the toys:
- output indices must be built from separate variables, not from projections of one variable;
- counter functions must use structural recursion, or Lean can't compute them while type-checking.

# Summary of changes for run a7239854-c4a8-45d9-8654-2214fbdfe359
I added Lean proofs to `Tests/TyTests/OnePointFieldTest.lean` showing that dropping a one-value field like `Fin m → Unit` loses no information. They also show that the two types still refused really have only one value, and that translated functions on `UF` give the same results as the Lean definitions. The `TyTests` target builds, there is no `sorry`, and the proofs use only Lean's standard axioms (`propext`, `Quot.sound`, `Classical.choice`).

One part can't be proved directly: the check that decides which fields count as one-value (`isOnePointType`) runs while Lean elaborates and isn't stated as a Lean function. So what's proved is that each kind of type it accepts has one value, plus the specific examples below.

**Why erasing the field is safe**
- `pi_subsingleton`: if every result type of a function has at most one value, so does the function type, dependent or not. `finUnit_eq` and `unitFinUnit_eq` apply this to show `Fin m → Unit` and `Unit → Fin m → Unit` each have exactly one value.
- `prod_subsingleton`: a pair of one-value types has one value. `uf4Field_eq` combines both results to show `(n : Nat) → Fin n → Unit × PUnit` has exactly one value.

**`UF` is just a `Nat`**
- `UF.ofNat_m` and `UF.m_ofNat`: going from `UF` to `Nat` and back gives the original value, in both directions.
- `Ty.Den Ok₁.Δ Ok₁.t = Nat` holds by `rfl`, so the declared layout of `UF` stands for exactly `Nat`.
- The same holds for `UF₄`, which is read as `Nat × Bool` (`UF₄.ofPair_toPair` and `UF₄.toPair_ofPair`).

**The two types still refused have one value**
- `UF₂.eq` and `UF₃.eq` prove that any two values of each type are equal.
- I used `Fin 3` where you wrote `Fin m`, because Lean rejects `Fin m` when `m : Unit`.

**Translated functions match the Lean definitions**
- `ufMT_run`: the translation of `UF.m` returns `u.m` for every `u : UF`.
- `ufUseT_run`: the translation of `UF.use`, which reads the erased field through `match f ⟨0, h⟩ with | () => …`, equals `UF.use u` for every `u`.
- `ufvT_run`: the translation of the sample value `ufv` is its `Nat`, 3.

The three main results are in the Properties table, marked proved. Everything is committed.

# Summary of changes for run 81f40312-c000-44b6-95d1-4ed24f2803ea
Functions whose result has only one value, like `test1 (f g : F) (a : Unit) : Unit`, can no longer be translated, and the `leanscript` tool now skips them silently. The test functions now use `Nat` instead. All the targets I touched build without `sorry`, and `lake exe tests` passes 92/92.

**What changed**
- **One-value test** (`LeanScript/TermElab/ToTerm.lean`): a new check, `Gen.resultIsOnePoint`, looks at a definition's result type after all its parameters. It counts as one value if it is `Unit` or `PUnit`, or a non-recursive structure built only from such fields and proofs (for example `Unit × PUnit`). It covers `F → F → Unit → Unit` as well.
- **`#leanscript_to_term` refuses these definitions** with the error "the result of `f` has one value: in a pure language the function always answers it and does nothing else, so it has no translation".
- **Removed the `Unit`-generalisation path:** `unitGeneralize?` and the `f._leanscript_unit_gen` declarations are gone. That path existed only to make such functions translatable.
- **The `leanscript` tool skips them** (`LeanScriptCli/Frontend.lean`, `classify`). They are handled like definitions of types or propositions: not exported and not listed under "not translated", even when total and terminating. `paramNames` no longer looks for the removed generalisation.
- The README and module docs are updated to match.

**Tests**
- **Changed to `Nat`:** `test1`, `test2` (`(a : Nat) : Nat`) and `test3` (`Nat → Nat`) in `Tests/SnapshotsPBOPure/DefaultRulesFunction01.lean` and in the copy in `Tests/TermTests/ToTerm/PolymorphismTest.lean`.
- **Proofs:** `test1T_run`, `test2T_run` and `test3T_run` now prove, by `rfl`, that each translation computes the Lean definition itself on every argument. Before, they were stated against the removed generalisation, and `test1_eq_gen` is deleted.
- **New refusal checks:** two `#guard_msgs` tests, `unitResult` (the old `Unit` version of `test1`) and `unitPairResult` (result `Unit × PUnit`), check that the translator refuses them.
- **New IO test** in `Tests/Main.lean`, `oneValueResultSpec`. It runs the binary on a file containing `unitFn`, `unitThunk`, `unitPair` and `natFn`. Under both presets it checks that only `natFn` is emitted (`export const natFn = (f, g, a) => f(1, g("foo", a));`) and that the other three names do not appear anywhere in the output. The `DefaultRulesFunction01` IO test still passes unchanged.

**Snapshots**
- I regenerated all snapshots. Only the two `DefaultRulesFunction01-Term-*.txt` files changed: their headers now read `F → F → Nat → Nat`. The generated JavaScript is byte-identical, so no other snapshot had relied on the removed path.
- All node checks passed. The snapshot script still exits with code 1, but nothing in its log points to a failing check; I did not track down why.

All work is committed.

# Summary of changes for run f8dff525-64d2-4a0c-8bb6-3e032a2f9bad
I removed `LeanPrimTy.tyParam` and the `LeanScript.TyParam` structure. Type parameters are now handled entirely with types the language already has: each one is read at the stand-in `Nat`, i.e. `Ty.nat`.

**How it works now**
- In `LeanScript/TermElab/ToTerm.lean` (`## Polymorphism`), `tyParamExpr i` is replaced by `tyParamStandIn := Nat`. It is used in all three places that bind a type:
  - a parameter like `{α : Type}`;
  - a leading `∀` of the result's type;
  - an unused rank-2 parameter, read at fresh stand-ins.
- The recursive-call check (a type parameter must be passed through unchanged) is the same as before.
- This works for the same reason as the old approach: the body has no instance to look inside a value of type `α` with, so translating one instance translates every instance once types are erased.
- `Nat` is a safe stand-in because its representation never picks a specialised container (an `Array Nat` is a plain array, not a typed array). The differential checks also already ran type parameters at `Nat`.

**Removed along with the leaf**
- The `tyParam` cases in `LeanPrimTy` (`pretty`, `isObjectKey`, `denote`), `GenElab/Read.lean`, `Ty/Den/Two.lean`, `Ty/Den/Three.lean` and `Term/Pretty.lean`.
- On the JavaScript side: `JsTerminalTy.tyParam`, `tyParamName`, its cases in `Ty/Lower.lean`, `Ty/Config.lean` and `Lower/Basic.lean`, and the `@template` code in `JsTerm/Print/Mini.lean`. Once the Term type carries no type-parameter marker, there is nothing for these to work from.

**One visible trade-off:** JSDoc no longer prints `@template A, B, …`. It now shows the stand-in type instead, e.g. `@param {(uint53(number), uint53(number)) => uint53(number)} f` under `pbo`, or `nat(bigint)` under `faithful`.

**Tests**
- In `Tests/TermTests/ToTerm/PolymorphismTest.lean`, `P0`/`P1`/`P2` are replaced by `Nat`. All the `rfl` theorems (`test1T_run` … `swapT_run`) still prove that each translation computes the Lean definition.
- The example in `ToTermTest.lean` is now `run (5 : Nat) = (5 : Nat)`.
- In `Tests/Main.lean`, the `@template` assertion now checks the `test4` doc line at the stand-in type.
- Comments in `ToTerm/Basic.lean` and `LeanScriptCli/Check.lean`, and the README section on polymorphic definitions, are updated.

**Checks run**
- `JsTerm`, `TermTests`, `TyTests`, `LeanScriptCli`, `leanscript`, `tests`, `JsSpec` and `LanguageJavascriptMini` build. There is no `sorry` in the edited test files.
- `lake exe tests` passes 91/91.
- I re-ran `scripts/leanscript-snapshots.sh` and committed the regenerated snapshots (60 files). All node checks pass. The script still exits 1 only because of the existing "literal too big" errors in the `PrimOp*Configurable` files under `pbo`.
- Almost all snapshot changes are doc comments and printed types. The one change to code: in `RecursionSchemes01`, `mapExprF` now returns its argument `a` in the literal case instead of rebuilding `{ tag: 0, _1: a._1 }`. Its parameter and result types are now the same, and the reuse is still correct once types are erased.
- As before, a full default `lake build` fails in `LeanScript.Term.Syntax.UsageAlgebra`, which imports Mathlib, a library this project doesn't depend on.

All work is committed.

# Summary of changes for run 3e6471fe-0c3e-46b9-b579-b9931da47bf9
Both functions in `Tests/SnapshotsPBOPure/DefaultRulesMonoid01.lean` are now translated under both presets. Before this change neither was. The output is on par with purescript-backend-optimizer's `legacy-backend/DefaultRulesMonoid01.js`, and better on `test2`.

**What was wrong:** both failures were bugs in the step that turns Lean code into `Term`, not missing optimizations.
- **`test1`** stopped with an internal type mismatch. `∅ : Array Int` unfolds to `Array.emptyWithCapacity 0`, a call of a built-in function where every argument is a constant. The translator wrote any such call as a constant of a basic type (number, boolean and so on), which an array is not.
- **`test2`** was refused with "dependent function type". When a parameter has a polymorphic type (`f : F`, `F := ∀ {α}, α → α`), the body is translated with `f` at the one type it is used at (`Array Int → Array Int`). But the declared type of the result still had the polymorphic `F`. This only worked before when the definition also went through the existing "replace `Unit` by a type parameter" path, as all the `DefaultRulesFunction01` examples did.

**Fixes:**
1. `LeanScript/TermElab/ToTerm.lean`: if a polymorphic parameter is fixed at one type, the type of the result is now built from that fixed type.
2. `LeanScript/TermElab/Anf/Render.lean`: an empty array with a constant capacity (`∅`, `Array.empty`, `Array.emptyWithCapacity n`) becomes the array literal `#[]`.

**Output now (pbo preset):**
```js
export const test1 = (a) => (a ? [1, 2, 3] : []);
export const test2 = (f, a) => {
  if (a) {
    return f([1, 2, 3]);
  }
  return [];
};
```
- **`test1`** is the same single test as theirs.
- **`test2`**: theirs calls `f` first and returns a closure. Ours takes both arguments at once, builds no closure, and calls `f` only when `a` is true.
- The `faithful` preset gives the same shape with bigint literals.

None of your three optimization phases needed changing for this file. It has no loops and no shared tails, so labeled blocks and loops did not come up.

**Tests:**
- **Proofs:** I added `monoidTest1T_run`, `monoidTest2T_run` and `emptyCapT_run` to `Tests/TermTests/ToTerm/PolymorphismTest.lean`. They use copies of the two functions (renamed `monoidTest1`/`monoidTest2`), since the snapshot file cannot be imported. Each proves the translation computes the same result as the Lean definition for every input.
- **IO test:** I added `defaultRulesMonoidSpec` to `Tests/Main.lean`. Under node it checks:
  - the exact shape of both functions;
  - their answers;
  - that `f` is called exactly once over the calls `test2(f, true)` and `test2(f, false)`.
- **Results:** `lake exe tests` passes 91/91. `TyTests`, `TermTests`, `JsTerm`, `JsSpec`, `LanguageJavascriptMini`, `LeanScriptCli`, `tests` and `leanscript` build, and there is no `sorry` in the edited test file.
- **Snapshots:** `scripts/leanscript-snapshots.sh` was re-run. Only the `DefaultRulesMonoid01` outputs changed and all node checks pass. The script still exits 1 because of the "literal too big" errors in the `PrimOp*Configurable` files under the pbo preset; those were there before.
- **Known build failure:** a full default `lake build` still fails in `LeanScript.Term.Syntax.UsageAlgebra`, because that file imports Mathlib and the project has no Mathlib dependency. This was also there before.

The README has a short note on both fixes. The two `DefaultRulesMonoid01` translation theorems are recorded as proved in the Properties table, and everything is committed.

# Summary of changes for run 8cf09b29-942b-4548-a354-226a0add82e5
The JavaScript for `Tests/SnapshotsPBOPure/DefaultRulesFunctor01.lean` is now on par with purescript-backend-optimizer's `legacy-backend/DefaultRulesFunctor01.js`, and better on `test2` and `test5`. All five functions are translated under both presets.

**What was wrong at the start:**
- `test2` was not translated, because `Option Unit` was refused.
- The four notation declarations (`<#>`, `<$`, `$>`, `<@>`) were listed as "not translated".
- `test5` built a closure for `const`, called it, and allocated a new option.

**What the output is now, compared with purescript-backend-optimizer:**
- `test1`, `test3`, `test4`: the same single tag test and a fresh `some`/`none`, as theirs.
- `test2` is `(mb) => mb.tag !== 0`. `Option Unit` is now read as a boolean, where theirs builds `$Option$some(undefined)`.
- `test5` is `if (mb.tag === 0) return { tag: 0 }; return mb;`. It returns its argument as-is, where theirs rebuilds `$Option$some(mb._val)`.

**Changes, placed in the phases you preferred:**
1. **Term → Term optimizer, two new passes, both proved to preserve the result of eval:**
   - `Term.joinCtor` (`LeanScript/Term/Optimize/JoinCtor.lean`, proof `Term.joinCtor_eval`): when a join point takes apart a constructor that its jumps build, the matching branch is written at each jump, so the value is never built and then taken apart.
   - `Term.openCall` (`OpenCall.lean`, proof `Term.openCall_eval`): a call of a known closure that only returns a pure expression of its argument (such as `Function.const`) is replaced by that expression.
   - Neither pass adds calls (`Term.numCalls_joinCtor`, `Term.numCalls_openCall`). Both are wired into `Term.optimize`, and `Term.optimize_eval` and `Term.numCalls_optimize` still hold. `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`.
2. **Lean → Term:** a `Unit` field of a constructor is now dropped, since it carries no information. So `Option Unit` becomes a boolean and `Nat × Unit` becomes `Nat`, and matching on the `()` read from such a field just takes its one branch. `Unit` on its own is still refused.
3. **CLI:** declarations generated by `infixl`/`infixr` notation are no longer reported as untranslated.

None of this needed new loops or labeled blocks: every function in this file is now a single test with direct returns.

**Side effects on existing tests and snapshots:**
- Four tests expected `Option Unit` / `Nest Unit` / `RoseTreeL Unit` / `RoseTreeA Unit` to be refused; these types are now accepted.
  - In `NestTest.lean` and `SignatureTest.lean` they now check that the declaration is accepted.
  - In `RoseVariantsTest.lean` the two now-accepted declarations were removed and replaced by a comment. Declaring them would have made them the signature the later proof file reads.
- In `PolymorphismTest.lean`, the theorem `isSomeUT_run` was restated: `Option Unit` is now a `Bool`, so the theorem relates the translation applied to `o.isSome` to `isSomeU o`.
- The regenerated snapshots improved in `InlineClosures`, `LoopClosure`, `OwnershipAliasing` and `OptionUnbox`, where a closure called once is now inlined.
- `Html.lean` is still not translated, but the reason changed. It used to be refused for `Unit`; it now gets further and fails with an internal elaboration error in the normaliser. I did not fix that.

**Verification:**
- `TermTests`, `TyTests`, `JsTerm`, the Spec libraries, `tests` and `leanscript` build.
- I added a new IO test, `defaultRulesFunctorSpec` in `Tests/Main.lean`. It checks that every function is translated with no closure, the exact shape of `test2` and `test5`, and the answers of all five functions under node. `lake exe tests`: 90/90 pass.
- `scripts/leanscript-snapshots.sh` was re-run. All node checks pass. It still exits 1 only because of the "literal too big" errors in the `PrimOp*Configurable` files under the `pbo` preset, which were already there.
- The README describes the new passes and the `Unit`-field rule.
- `Term.joinCtor_eval` and `Term.openCall_eval` are recorded as proved in the Properties table.
- Everything is committed.

# Summary of changes for run c55b7d53-48fd-4cb9-9afa-906b52afcb16
`Tests/SnapshotsPBOPure/DefaultRulesFunction01.lean` now translates fully. The JS output matches the legacy purescript-backend-optimizer output, and in a few places it is better. Before this change all six functions were rejected:
- `test1`–`test4` failed on the rank-2 type `F := ∀ {α β γ}, α → β → γ`.
- `test5`–`test6` failed with "parameter α is a type".

**New output (pbo preset):**
```js
export const test1 = (f, g, a) => f(1, g("foo", a));
export const test2 = (f, g, a) => f(1, g("foo", a));
export const test3 = (f, g, a) => f(g(1, 2), 3);
export const test4 = (f, b, a) => f(b, a);
export const test5 = (a, a1) => a;
export const test6 = (a) => a;
```

**Compared with the legacy backend:**
- **Same shape:** each function is a single expression, with no intermediate `const`s.
- **Calls:** we use multi-argument calls instead of curried ones.
- **Types:** JSDoc now includes `@template A, B, …`.
- **`test1`/`test2`:** the Unit argument is passed through as `a` instead of being replaced by `()`.
- **`test4`:** legacy prints `f(a)(b)` only because it names the parameters differently. Ours is `fun b a => flip f a b = f b a`.

**What I changed, by pipeline phase:**
1. **Translation (Lean → Term):**
   - Type parameters become a new leaf type `LeanScript.TyParam i`.
   - A rank-2 parameter like `F` is read at the one type it is actually used at. Two different uses are refused.
   - If a definition only fails because of `Unit`, it is retried with `Unit` replaced by a type parameter, declared as `f._leanscript_unit_gen`.
   - Main code is in `LeanScript/TermElab/ToTerm.lean` (section "Polymorphism"), with recursive-call checks in `Expr/Cases.lean`.
2. **Types (Term → JsTerm):** I added `JsTerminalTy.tyParam` and updated the lowering and type files to handle it.
3. **Printer:** a constant argument such as a literal sitting between uses no longer forces a temporary. `f(g(1), 3)` is now written inline (`JsTerm/Syntax/Vars/Occs.lean`). JSDoc `@template` is printed in `JsTerm/Print/Mini.lean`.
4. **CLI:** parameter names come from the user's own lambda binders, and the differential checks run type parameters at `Nat`.

No change to the Term optimizer was needed for this file. Labelled blocks and loops never came up, because the file has no recursion and no shared tail.

**Verification:**
- The targets `TermTests.ToTerm.PolymorphismTest`, `TermTests.ToTerm.ToTermTest`, `LeanScriptCli` and `tests` build with no `sorry`.
- The new test file has `rfl` theorems checking that the translated Terms evaluate the same as the Lean originals, plus tests that a rank-2 use at two different types is refused.
- I also added a `defaultRulesFunctionSpec` to `Tests/Main.lean`.
- `lake exe tests` reports 89/89 passed. The node checks for this file pass: 18 per preset.
- There is a new README section, "Polymorphic definitions".

**Other effects and known issues:**
- **Other snapshots changed.** I regenerated them; about 116 files changed. Some now translate more functions (e.g. `DefaultRulesFunctor01` `test3`–`test5`), and some have different parameter names (e.g. `AppArity`).
- **Remaining gap:** `DefaultRulesFunctor01` `test5` still leaves a closure call `k$3(12)` that is not inlined.
- **Failures that existed before this work:**
  - The snapshot script still exits with code 1 because of "literal too big" errors in the `PrimOp*Configurable` files.
  - `LeanScript.Term.Syntax.UsageAlgebra` still fails in the full build because the project has no Mathlib dependency.

All work is committed.

# Summary of changes for run e3409c00-d31f-4f1f-b262-a7a0a1fd216b
`CaseSum` already compiled to JavaScript that matches or beats `legacy-backend/CaseSum.js`, so I left all three compilation phases unchanged. What I changed is the testing: the generated check files never called `test1` with `.L 2`, so the `"2"` arm had never been run. Now it is, and a new test compares our output with PBO's.

**Current output** (`CaseSum-pbo.js`; `-faithful.js` is the same with `1n`, `2n`):
```js
export const test1 = (v) => {
  if (v.tag === 0) {
    const { _1: f$1 } = v;
    if (f$1 === 1) { return "1"; }
    return f$1 === 2 ? "2" : "3";
  }
  return "4";
};
```
- **Same order of tests as PBO:** one tag test, then `=== 1`, then `=== 2`.
- **Better than PBO in two places:**
  - On `R`, PBO tests the tag a second time (`v.tag === "R"`) and ends with `throw new Error("UNREACHABLE")`. We skip both, because `R` is the only constructor left.
  - PBO reads `v._n` for each test. We read the field once, into `f$1`.
- **Measured on 12 inputs** (`L`/`R` with 0, 1, 2, 3, 13, 1000), both presets:
  - every answer is Lean's, and PBO's answers are too;
  - `R n` takes 1 comparison and 1 read of the value, where PBO takes 2 and 2;
  - `L 0`, `L 2`, `L 3` take 2 reads, where PBO takes 3;
  - comparisons on `L` are equal to PBO's.
- **Why no labelled blocks or loops:** there is no recursion and no shared tail here, so they would add nothing. No change in any phase would reduce the tests further.
- **Only difference in style:** the last test is written as a conditional expression (`?:`) instead of PBO's `if` and `return`. It makes the same comparisons, and the other snapshots already print this pattern that way.

**Changes**
- **Check inputs (`LeanScriptCli/Check.lean`):** a `Nat` field of an inductive-type parameter is now also tried with the number literals in the function and its helpers such as `test1.match_1` (new `natLitsOf`, at most 4 values). Before, only the first two samples (0 and 1) were used. The checks in `CaseSum-*.check.mjs` went from 4 to 6 and now include `test1({ tag: 0, _1: 2 })` giving `"2"`.
- **New script `scripts/sum-compare.mjs`:** runs our `test1` and PBO's on the same values and counts comparisons with a literal and reads of the value.
- **New test in `Tests/Main.lean` (`caseSumSpec`):** for both presets it checks that:
  - the check file passes and covers the `.L 2` arm;
  - the JS has no runtime import, no `throw`, one tag test, and one test each of `1` and `2`;
  - on every input the answer is Lean's (PBO's too), with no more comparisons or reads than PBO, and exactly one comparison on `R`.
- **`README.md`** describes the new check inputs.

**Checks run**
- `lake build leanscript tests` succeeds, and `lake exe tests` passes 88/88, including the new test.
- I regenerated all snapshots. No `.js` output changed. Only 4 check files gained cases: `CaseSum-*.check.mjs` and `Tests/SnapshotsMy/TagChain-*.check.mjs`, which now also tries the literal `4`. Every node check passes.
- The snapshot script still exits 1, as before, because of the "literal too big" errors in `PrimOpInt02Configurable` and `PrimOpInt03Configurable`.

No Lean theorems changed, so the Properties table is unchanged. Everything is committed.

# Summary of changes for run 28f7b2e0-617b-44e2-a21f-96f3ee85f3ea
`CaseString` was already on par with `legacy-backend/CaseString.js` before this session, so I changed none of the three compilation phases. What I did change is the testing: the generated check files never tried the inputs `"foo"` or `"bar"`, so two of the four arms had never been tested. Now they are.

**Analysis.** The unoptimised `Term` is PBO's chain of tests: `"foo"`, then `"bar"`, then `""`, then `"catch"`. The `Term → Term` optimizer turns only the last `if` into `cond(lean_string_dec_eq(x, ""), "3", "catch")`. Both presets then print this:
```js
export const test1 = (x) => {
  if (x === "foo") { return "1"; }
  if (x === "bar") { return "2"; }
  return x === "" ? "3" : "catch";
};
```
- **Same tests as PBO.** The three tests are the same as PBO's and come in the same order, and each literal is compared once. On every input we tried, both versions make exactly the same number of comparisons: 1 for `"foo"`, 2 for `"bar"`, 3 for anything else.
- **Only difference.** Where PBO writes `if (v === "") return "3"; return "catch";`, we write the same thing as a conditional expression. It is shorter and makes the same comparisons, and it is how the other snapshots already print this pattern.
- **Nothing to gain from more work.** The code has no recursion and no shared tail, so there was no reason for labelled blocks or loops. I found no change in any phase that would reduce the number of comparisons, so I left the JavaScript as it is.

**Changes**
- **Check inputs (`LeanScriptCli/Check.lean`).** With `--check`, a function with a `String` parameter is now also called on the string literals in its own definition and in its helper definitions such as `test1.match_1`, up to 8 of them. So the checks now cover every arm of a `match` on strings. `CaseString-*.check.mjs` went from 5 to 11 checks, including `test1("foo")` giving `"1"` and `test1("bar")` giving `"2"`.
- **Comparison counting (`scripts/count-comparisons.mjs`).** The script now also counts `===` against a string literal, and accepts strings as arguments.
- **New test in `Tests/Main.lean` (`caseStringSpec`).** For both presets it runs `test1` on 10 inputs (the three pattern literals and seven others). It checks that:
  - our answer and PBO's are both Lean's;
  - we never make more comparisons than PBO;
  - each literal is tested exactly once;
  - there is no runtime import;
  - the check file covers the `"foo"` and `"bar"` arms.
- **`README.md`** now describes the new check inputs.

**Checks run**
- `lake build leanscript tests` succeeds, and `lake exe tests` passes 87/87, including the new test.
- I regenerated all snapshots. No `.js` output changed. Only `.check.mjs` files changed: those of the eight snapshots with a `String` parameter (16 files). In functions with several parameters, the new inputs shift which argument combinations are sampled, but the number of checks there stays the same. Every node check passes.
- The snapshot script still exits 1, as it did before, because of the "literal too big" errors in the `PrimOp*Configurable` files.
- No Lean theorems changed, so the Properties table is unchanged. Everything is committed.

**Side observation, not implemented.** In a variant with `| "foo" => x ++ "!"`, the output is `x + "!"` inside `if (x === "foo")`. Replacing `x` with the known literal would give the constant `"foo!"`. That is outside `CaseString` and would need a new rewrite in the `Term` phase.

# Summary of changes for run 11b85fc3-0084-4634-a5d4-9aec69a10bbc
`CaseRedBlackTree` now compiles to JavaScript with the same decision tree as `legacy-backend/CaseRedBlackTree.js`. A new test runs it on all 723 trees of depth 3 or less: it gives Lean's answer on every tree and never reads more tags or colours than PBO. The file dropped from about 440 lines to 80. The changes are in the `Term → JsTerm` step and the printer, not in the `Term → Term` optimizer, for the reason given further down.

**What was wrong.** For patterns 1 and 2, Lean's match compiler copies the tests on the right subtree (patterns 3 and 4) into every branch where they fail. The existing tail-sharing pass (`JsBlock.shareTails`) should have written those copies once, but they were not the same statements, for two reasons:
1. **Rebuilt left subtree.** Lean rebuilds the left subtree from its fields, as `in#0(ctor#1(false, f24, f25, f26))`, using the literal `Red` (`false`) because it has already tested the colour. The step that writes the original variable in place of a rebuilt constructor only matched variables, so each copy rebuilt the subtree differently.
2. **Default answer.** Inside `Leaf` arms, `Leaf` in the default answer was replaced by whichever variable was known to be `Leaf` (`_2: f$3`, `_2: f$9`, …). So each copy of the default answer read a different variable.

**Changes**
- **`Term → JsTerm` (`JsTerm/Lower/Basic.lean`, `FromTerm.lean`):**
  - An `if` on a boolean held in a constant now records that constant's value in each branch (`Names.bools`). A rebuilt constructor whose field is that boolean literal is then recognised as the value already taken apart (`ArgKey`, `knownCtorLvl?`).
  - A constructor without fields, written on its own, is no longer replaced by a variable. Inside a constructor that is replaced it still is, which keeps `CaseJacobs` as it was.
- **Printer (`JsTerm/Print/Mini`, `sinkPattern`):** `const { … } = s; if (c) { … }` with nothing after the `if` becomes `if (c) { const { … } = s; … }`. This only happens when `c` has no effect and reads none of the fields. The `if` then merges with the arm's test, giving `if (t.tag === 1 && t._1)`, which is PBO's `v.tag === "Node" && v._color === "Black"`.

**New output** (`CaseRedBlackTree-pbo.js`; `-faithful.js` is the same with `1n`, …):
```js
export const test1 = (t) => {
  if (t.tag === 1 && t._1) {
    const { _2: f$1, _3: f$2, _4: f$3 } = t;
    if (f$1.tag === 1 && !f$1._1) {
      const { _2: f$4, _3: f$5, _4: f$6 } = f$1;
      if (f$4.tag === 1 && !f$4._1) { return { _1: 1, … }; }
      if (f$6.tag === 1 && !f$6._1) { return { _1: 2, … }; }
    }
    if (f$3.tag === 1 && !f$3._1) {
      const { _2: f$7, _3: f$8, _4: f$9 } = f$3;
      if (f$7.tag === 1 && !f$7._1) { return { _1: 3, … }; }
      if (f$9.tag === 1 && !f$9._1) { return { _1: 4, … }; }
    }
  }
  return { _1: 0, _2: { tag: 0 }, … };
};
```
There is no recursion here, and the shared tail is a plain fall-through, so no labelled block or loop was needed.

**Remaining differences from PBO**
- **Unmatched trees return `default`; PBO throws.** A `panic!` with a constant message is compiled to its `default` value, which is what Lean returns. Making it throw would need `Term` to allow an extern call with only constant arguments, which is a grammar change across all the proofs.
- **Field names.** The result record uses `_1…_8` rather than field names, as all generated records do.

**Why not the `Term → Term` phase.** The rewrite needs to know which boolean an enclosing `if` tested, and it changes a literal into a variable. In the intrinsically typed `Term`, that changes the level index. The conversion already had this "rebuilt constructor = scrutinee" mechanism, so I extended it there.

**Tests and checks**
- **New test in `Tests/Main.lean` (`caseRedBlackTreeSpec`):** it compares our JS, in both presets, with a Lean copy of `test1` on all 723 trees, using the new `scripts/rbt-compare.mjs`. It checks:
  - every answer matches Lean's, and PBO's matches too, or PBO throws where Lean returns `default`;
  - on every tree we read no more tags and colours than PBO;
  - the default answer and each pattern are written exactly once.
- `lake exe tests` passes 86/86.
- `lake build leanscript JsTerm tests OpsSpec` succeeds.
- I regenerated all snapshots and all 342 node check files pass. Only the `CaseRedBlackTree` outputs changed. The script still exits 1, only because of the existing "literal too big" errors in the `PrimOp*Configurable` files.
- `README.md` describes the two changes.
- No Lean theorems changed, so the Properties table is unchanged.

Everything is committed.

# Summary of changes for run 3f0fc641-6a56-498a-8978-c658361af94f
`CaseRecord` now compiles to JavaScript on par with `legacy-backend/CaseRecord.js`. All six functions give Lean's answers and never make more comparisons than PBO. `Test2.test2` was the one function whose shape differed; it now matches PBO's. The fix is a new pass in the `Term → Term` phase, proved to preserve `eval`. The other phases needed no changes.

**What was wrong.** `test1` and `test3`–`test6` already matched PBO. In `Test2.test2`, once `a.c == 2`, we tested `a.b == 1` first. Both of its arms then took `d` apart and tested `d.e == 1 && d.f == 2`, so that test appeared twice. PBO tests `d` once and tests `a.b` inside each result.

**New output** (`CaseRecord-pbo.js`; `-faithful.js` is the same with `1n`, …):
```js
export const Test2$test2 = (x) => {
  const { _1: f$1 } = x._1;
  if (x._1._2 === 2) {
    if (x._2._1 === 1 && x._2._2 === 2) {
      return f$1 === 1 ? 1 : 2;
    }
    return f$1 === 1 ? 3 : 4;
  }
  return 4;
};
```
This has PBO's structure. On all 256 inputs with each field from 0 to 3, it makes the same number of comparisons as PBO on every input (400 in total for both).

**The pass** (`Term.zipTestWalk`, in the new `LeanScript/Term/Optimize/ZipTest.lean`; it runs right after `shareTestWalk` in `Term.optimize`):
- It applies at an `if p` when both arms make the same tests (the same conditions and the same record destructurings, in the same order) and differ only in their answers.
- It then moves `p` into the answers: `if p then (if q then a else b) else (if q then c else d)` becomes `if q then (p ? a : c) else (p ? b : d)`, or just `a` where both answers are the same.
- No input is tested more often than before, and the shared tests are written once.
- It is skipped when both arms are plain answers, or when the result would change the statement's level index.

**Proofs** (standard axioms only, no `sorry`):
- `Term.zipTestWalk_eval`: the pass doesn't change `eval`, so `Term.optimize_eval` still holds. This is added to the Properties table as proved.
- `Term.numCalls_zipTestWalk`: the pass adds no calls, so `Term.numCalls_optimize` still holds.
- In `LeanScript/WFTerm/Optimize.lean`, one existing proof (the `jump` case of `optimizeUnder_eval`) hit the heartbeat limit after the change. I rewrote it without `congr`.

**Tests and tooling**
- `scripts/count-comparisons.mjs` now handles nested records (flattened into separate arguments for PBO). It also counts comparisons such as `0 < f$1` and `v_a > 0`.
- New test in `Tests/Main.lean`, run for both presets on a grid of inputs: all six `CaseRecord` functions give Lean's answers (checked against PBO's too) and never make more comparisons than PBO. It also checks that `Test2.test2` writes the test of `d` once.
- The `README.md` now describes the pass.

**Remaining differences from PBO**
- PBO takes the fields as separate arguments; we pass the record and read its fields. This is how every structure is passed, so I left the interface unchanged.
- Where PBO writes `if (c) return a; return b;` we write `return c ? a : b;`. The comparisons are the same.
- There is no recursion or shared tail in this file, so no labelled block or loop was needed.

**Checks run**
- `lake build leanscript tests TermTests JsSpec JsTerm LeanScript.WFTerm.Optimize LeanScript.Term.Optimize.CountOptimize` succeeds.
- `lake exe tests` passes 85/85, including the new test.
- I regenerated every snapshot. Only the `CaseRecord` outputs changed, and every node check passes. The snapshot script still exits 1, but only because of the existing "literal too big" errors in the `PrimOp*Configurable` files.
- Building the whole `LeanScript` library fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib when the project doesn't depend on it. I didn't change that file.

Everything is committed.

# Summary of changes for run 87bd1df3-dd62-43c2-8b0d-1d7b6ab52db1
I didn't change any code this time. `CaseProduct` already compiles to JavaScript that matches `legacy-backend/CaseProduct.js`, and is slightly better on comparison count. The previous session did the work, and I rebuilt from the current sources to confirm it still holds.

**Reproduced from source:** I built `leanscript` fresh and regenerated `CaseProduct` (`--check`). The output is identical to the committed files: `-Term-unoptimized.txt`, `-Term-optimized.txt`, `-pbo.js` and `-faithful.js`. Output (`CaseProduct-pbo.js`; `-faithful.js` is the same with `1n`, …):
```js
export const test1 = (a) => {
  const { _1: f$1, _2: f$2, _3: f$3 } = a;
  if (f$1 === 1) {
    if (f$2 === 2) { return f$3 === 3 ? "1" : "catch"; }
    return f$2 === 4 ? "2" : "catch";
  }
  if (f$2 === 4) { return "2"; }
  if (f$1 === 4 && f$2 === 5 && f$3 === 6) { return "3"; }
  return "catch";
};
```

**Where the optimization lives:** it happens in the `Term → Term` phase, as you preferred. The pass is `Term.shareTestWalk` in `LeanScript/Term/Optimize/ShareTest.lean`. Where both arms of an `if` start with the same test leading to the same answer, it moves that test first. That makes `b == 4` run before `a == 4` once `a ≠ 1`, as PBO does. The `Term → JsTerm` and `JsTerm → JsTerm` phases needed no changes. There is no recursion or shared tail here, so no labelled block or loop was needed.

**Comparison with PBO:** I ran `scripts/count-comparisons.mjs` on all 343 inputs with each field from 0 to 6.
- Every answer matches PBO's.
- We never make more comparisons than PBO, and make fewer on 6 inputs (1036 in total against 1042). The saving is in the `a == 1` branch: when `b ≠ 2` we don't test `c`, while PBO tests `c === 3` first.

**Remaining differences from PBO:**
- PBO takes the three fields as separate arguments, `(v_a, v_b, v_c)`. We take the structure and destructure it once. This is how every structure is passed, so changing it would change the interface of all generated functions; I left it alone.
- The generated `CaseProduct-*.check.mjs` files only try 3 inputs, all of which answer `"catch"`, because they use the generic sample values. The test in `Tests/Main.lean` covers every branch instead, on all 343 inputs.

**Checks run this session:**
- `lake build leanscript tests TermTests.Optimize.CaseProductTest` succeeds, and there is no `sorry` in the pass or the `CaseProduct` proof file.
- `lake exe tests` passes 84/84. This includes the test that checks `CaseProduct` and `CaseRecord` against Lean's answers and PBO's comparison counts on all 343 inputs, for both presets.
- Both `CaseProduct` check files pass in node.
- Two properties in the table stay proved:
  - `Term.shareTestWalk_eval`: the pass doesn't change `eval`.
  - `CaseProductTest.test1_optimized_run`: the optimised `Term` computes Lean's `test1` for every input.

The step from `Term` to JavaScript is covered by the tests, not by a proof.

# Summary of changes for run 2cec354c-8ba1-4f61-9f9f-172a408550a8
`CaseProduct` now compiles to the same tests as `legacy-backend/CaseProduct.js`. Across a 7×7×7 grid of inputs it never makes more comparisons than PBO and makes fewer on 6 of them. The change is a new `Term → Term` optimizer pass, proved to preserve `eval`. No change to the `JsTerm` phases was needed.

**Analysis.** The previous output answered correctly, but it tested `a == 4` before `b == 4` when `a ≠ 1`, because Lean's match compiler splits on the first field first. PBO tests `b == 4` first for the `⟨_, 4, _⟩` row. Counting comparisons on inputs 0–6 for each field, our old code made more comparisons than PBO on 42 of 343 inputs.

**New output** (`CaseProduct-pbo.js`; `-faithful.js` is the same with `1n`, …):
```js
export const test1 = (a) => {
  const { _1: f$1, _2: f$2, _3: f$3 } = a;
  if (f$1 === 1) {
    if (f$2 === 2) { return f$3 === 3 ? "1" : "catch"; }
    return f$2 === 4 ? "2" : "catch";
  }
  if (f$2 === 4) { return "2"; }
  if (f$1 === 4 && f$2 === 5 && f$3 === 6) { return "3"; }
  return "catch";
};
```
- **Comparisons:** on all 343 inputs every answer matches Lean and PBO, and we never make more comparisons than PBO. On 6 inputs we make fewer, because in the `a == 1` branch we test `b` before `c`.
- **Remaining difference from PBO:** PBO takes the three fields as separate arguments; we take the structure and destructure it once.
- **Labelled blocks:** there is no recursion or shared tail here, so no labelled block or loop is needed.

**The pass** (`Term.shareTestWalk`, in the new `LeanScript/Term/Optimize/ShareTest.lean`, run right after `reuseFields` in `Term.optimize`):
- `if p then (if q then X else Y) else (if q then X else Z)` becomes `if q then X else if p then Y else Z`, and the same when the shared part is the `else` branch.
- A branch written as `ret (q ? a : b)` is treated as an `if` too.
- No input is tested more often than before; when `q` holds it saves one test, and `X` is written once.
- Conditions only count as the same when written identically: same variables, literals and externs. I extended extern comparison to the entries of `PreludeExtern` without type arguments, such as `lean_nat_dec_eq`, because the existing comparison didn't cover that family.

**Proofs** (standard axioms only, no `sorry`; both added to the Properties table as proved):
- `Term.shareTestWalk_eval`: the pass doesn't change the value of a statement, so `Term.optimize_eval` still holds.
- `Term.numCalls_shareTestWalk`: the pass adds no calls, so `Term.numCalls_optimize` still holds.
- `CaseProductTest.test1_optimized_run` (new file `Tests/TermTests/Optimize/CaseProductTest.lean`): for every `a b c`, the optimised `Term` computes Lean's `test1 ⟨a, b, c⟩`. The same file has a `native_decide` check of the optimised text.

**Other effects**
- **`CaseRecord` also improved:** its `test1` is now PBO's chain of tests. On a small grid, `test1` and `test2` now make exactly as many comparisons as PBO; before, they made more on many inputs.
- **Snapshots:** I regenerated all of them. Only the `CaseProduct` and `CaseRecord` outputs changed, and every node check passes. The script still exits 1, only because of the existing "literal too big" errors.
- **`LeanScript/WFTerm/Optimize.lean`:** adding the pass made three one-line proofs time out, so I rewrote them to unfold explicitly.
- **`scripts/count-comparisons.mjs`:** it can now pass a record or separate arguments, and counts comparisons on names containing `$` and on field reads.
- **New test in `Tests/Main.lean`:** for both presets, on all 343 inputs, it checks that `CaseProduct` and `CaseRecord` give Lean's answers and never make more comparisons than PBO. It also checks that `CaseProduct` makes fewer in total.
- **Weak check file:** `CaseProduct-*.check.mjs` still only tries 3 inputs, all of which answer `"catch"`. The new test above covers every branch instead.

**Verification**
- `lake build tests TermTests TyTests JsSpec OpsSpec RuntimeSpec JsTerm leanscript LeanScript.WFTerm.Optimize` succeeds.
- `lake exe tests` passes 84/84. The first run had two 30-second timeouts under parallel load. Both pass on their own, the rerun passed everything, and timing `leanscript` before and after the change showed no slowdown.
- I also updated `README.md` to describe the pass. Everything is committed.

# Summary of changes for run 554e1c5f-dd9a-434c-bcb4-42434e20e727
`CasePartial` now compiles to JavaScript with the same shape as `legacy-backend/CasePartial.js`, and the panic arm now throws, which resolves your `TODO: make sure throws`.

**Before:** `panic!` was unfolded to its logical value, the default `0`. The generated JS ended in `return a === 3 ? 3 : 0;`, the message was lost, and nothing was thrown.

**Now** (`CasePartial-pbo.js`; `-faithful.js` is the same with BigInt literals):
```js
export const test1 = (a) => {
  if (a === 1) { return 1; }
  if (a === 2) { return 2; }
  if (a === 3) { return 3; }
  throw new Error("PANIC at test1 CasePartial:5:9: mypanic " + a);
};
```
- **Comparisons:** I ran `scripts/count-comparisons.mjs` on eight inputs from −7 to 12. We make the same number of comparisons as PBO on each (1, 2 or 3).
- **Message:** it is the exact text Lean prints on a panic, built with one `+`. PBO writes `"panic! mypanic " + v.toString()`.
- **Runtime:** the module imports nothing from `runtime.js`. The throw is a plain statement, with no helper call and no extra stack frame.
- **No labelled block needed:** there is no shared tail or recursion here.

**Changes, by phase**
1. **Lean → `Term`, and the `Term` optimizer**
   - `panicCore` is now a catalogue extern, `lean_panic_fn`, taking the `Inhabited` default and the message. Its evaluator returns the default, which is what `panicCore` means in Lean's logic, so the existing proof that the optimizer preserves `eval` still covers it.
   - A panic whose message is a constant is still just its default value, because `Term` can't represent an extern call with only constant arguments.
   - The string-append merging in the optimizer (`StringAppend.lean`) now also handles `String.Internal.append`, which Lean uses to build the panic message. This is how the message ends up as one literal plus `a`.
   - One assumption to be aware of: `String.Internal.append` is `opaque`, so its evaluator is now defined as `String.append`. Both run the same runtime function, but Lean can't prove the two are equal.
   - The tool now names the module after the input file (`CasePartial`) instead of `LeanScriptInput`. That name appears in the message.
2. **`Term` → `JsTerm`:** there is a new `JsBlock.raise msg` statement. When the value being returned or passed to a join point is a panic, including one arm of a `c ? a : b`, the conversion writes `throw new Error(msg)` instead (`JsBlock.retOrRaise`). The existing `JsTerm` passes all handle the new statement.
3. **Runtime and operation tables:** I added `string__lean_panic_fn` to `runtime.js` for panics that aren't the returned value, and regenerated the tables with the scripts. The operation lookup for this kind of polymorphic extern was wrong, so I fixed it in `gen_js_ops.py`. That also affects `dbgTraceIfShared`.

**Differential checks:** Lean prints a panic message straight to stderr and carries on with the default, so the tool can't see it happen. When a file uses `lean_panic_fn`, `leanscript --check` now runs itself a second time as a child process to record which sample calls panic, and with what message. Those calls are then expected to throw exactly that message. As a side effect, the check run no longer prints PANIC output.

**Verification**
- **Formal checks** (`Tests/TermTests/Optimize/CasePartialTest.lean`, standard axioms plus `native_decide` for the printer check; added to the Properties table):
  - `test1_optimized_run`: for every `n`, the optimised `Term` computes Lean's `test1 n`.
  - `eval_lean_panic_fn`: the extern means `panicCore`.
  - These cover the `Term` phase only. The step to a JavaScript throw is covered by tests, not a proof.
- **New test in `Tests/Main.lean`:** checks the throw statement and message, that the module has no runtime import, that each answer or thrown message matches Lean, and that we make no more comparisons than PBO. `lake exe tests` passes 83/83.
- **All snapshots regenerated:** 14,844 node checks pass, 0 fail.
  - Besides `CasePartial`, only `InlineReferenceOpIsTag` changed: the module name inside an error comment.
  - The script still exits 1, only because of the existing "literal too big" errors.
- **Builds:** `lake build tests TermTests TyTests JsSpec OpsSpec RuntimeSpec JsTerm leanscript` succeeds. As before, building the whole `LeanScript` library fails on `UsageAlgebra.lean`, which imports Mathlib; I didn't touch it.

Everything is committed.

# Summary of changes for run edc709df-3eca-43aa-b8ca-03ba15ad57d8
I didn't change any code: `CaseNumber` already compiles to JavaScript that matches `legacy-backend/CaseNumber.js`. The previous session did that work and committed it. In this session I rebuilt from the current sources, regenerated the files and re-ran the tests to confirm it still holds.

**Current output** (`CaseNumber-pbo.js`; `CaseNumber-faithful.js` is the same):
```js
export const test1 = (f) => {
  if (f === 1) { return "1"; }
  if (f === 2) { return "2"; }
  return f === 3 ? "3" : "catch";
};
export const test2 = (a) => { /* same body */ };
```
- **Same code for both functions:** the `if f == 1.0 …` chain (`test1`) and the `| 1.0 => …` literal match (`test2`) produce the same decision tree as PBO's `test1`.
- **Only difference from PBO:** the last `if … return; return …` is written as a `?:`, which is the same logic in less code.
- **Labelled blocks:** there's no recursion or shared tail here, so no labelled block or loop is needed.
- **Where it happens:** the match translation is fixed in the Lean → `Term` step. The `Term` optimizer turns the last `if` into a `cond`, which becomes the `?:`. No `JsTerm`-level pass is involved.

**Checks from this session**
- I rebuilt `leanscript` and regenerated `CaseNumber`. All six output files came out byte-for-byte the same as the committed ones.
- The generated check modules pass: 16 of 16 for each preset.
- I ran `scripts/count-comparisons.mjs` on inputs 0, 1, 2, 3, 4, 1.5, -1 and -0. Our `test1` and `test2` give the same answers as PBO's `test1`, with exactly the same number of comparisons on each input: 1, 2 or 3.
- `lake build tests` succeeds and `lake exe tests` passes 82/82, including the `CaseNumber` test in `Tests/Main.lean`.
- The two float-equality lemmas behind the `| 1.0 =>` translation (in `LeanScript/TermElab/ToTerm/FloatEq.lean`) build as part of `leanscript`, and are already listed as proved in the Properties table.

**Limitation (unchanged from before):** under the `pbo` preset, a match arm on `0.0` or NaN falls back to comparing raw bit patterns. That fallback overflows JavaScript numbers and throws at run time; under `faithful` it gives the right answer. `CaseNumber` has no such arms, so it isn't affected.

There was nothing new to commit.

# Summary of changes for run f1904c96-30cb-4b3f-b1d9-fa31e1792cef
`test1` in `CaseNumber` already compiled to the same JavaScript as `legacy-backend/CaseNumber.js`. The one real gap was your commented-out `test2` (`| 1.0 => …`): it works on this Lean version, but the translator couldn't handle it. It now compiles, and both functions produce the same code as PBO's `test1`.

**Output now** (`CaseNumber-pbo.js`; `-faithful.js` is the same):
```js
export const test1 = (f) => {
  if (f === 1) { return "1"; }
  if (f === 2) { return "2"; }
  return f === 3 ? "3" : "catch";
};
export const test2 = (a) => { /* same body */ };
```
The only difference from PBO is that the last `if` is written as `?:`. There's no recursion or shared tail here, so no labelled block or loop is needed.

**Why `test2` failed.** A match on float literals checks exact equality `x = 1.0`, not `==`. The translator had no way to handle that equality for `Float`, so it rejected the function.

**The fix** is in the Lean → `Term` translation (`trDecide` in `LeanScript/TermElab/ToTerm/Expr/Calls.lean`). The later phases couldn't do it, because the function never got that far.
- If one side of `x = c` is a finite, non-zero float literal, the translator writes `x == c` (`===` in JavaScript). It checks this condition on the literal while translating.
- Any other float equality (a `0.0` or NaN arm, or no literal) becomes a comparison of the raw bits, which is always correct.

**Proofs** (in the new `LeanScript/TermElab/ToTerm/FloatEq.lean`, no `sorry`, standard axioms only; both added to the Properties table as proved):
- `decide_float_eq_beq_of_finite`: for a finite non-zero `c`, `decide (x = c) = (x == c)`. This works because a finite number has only one bit pattern.
- `decide_float_eq_toBits`: `decide (x = y) = decide (x.toBits = y.toBits)`.

**One limitation of the fallback:** with the `pbo` preset, 64-bit patterns don't fit in a JavaScript number. So a function with a `0.0` or NaN literal arm throws an overflow error at run time under `pbo` instead of answering. Under `faithful` it gives the right answer. I saw this with a scratch example; nothing in the committed snapshots uses it.

**Other changes**
- `CaseNumber.lean`: I uncommented `test2` and removed its TODO.
- `LeanScriptCli/Check.lean`: before, the generated checks for `CaseNumber` only tried inputs that return `"catch"`. I added `1`, `2`, `3` to the `Float` sample values, so they now reach every arm.
- `scripts/count-comparisons.mjs` now also recognises decimal literals like `1.0`, which PBO's output uses.
- A new test in `Tests/Main.lean`, run for both presets, checks that:
  - the generated checks run and none fail;
  - both functions give Lean's answers on 9 inputs;
  - both make no more comparisons than PBO's `test1`;
  - no bit comparison is left in the output.

**Results**
- I regenerated all snapshots. Besides `CaseNumber`, only `*.check.mjs` files changed (they have more float cases now); no other generated JavaScript changed, and every node check passes. The snapshot script still exits 1, only because of the known "literal too big" errors in the `PrimOpInt*Configurable` files.
- `lake build leanscript tests TyTests TermTests JsTerm JsSpec` succeeds, and `lake exe tests` passes 82/82.
- A plain `lake build` fails, but not because of this change: `LeanScript/Term/Syntax/UsageAlgebra.lean` imports Mathlib, which this project doesn't depend on, and I didn't touch that file.

Everything is committed.

# Summary of changes for run af8e26f8-0a6b-4eee-b8c8-01b5e407c30b
`CaseNewtype` already compiles to JavaScript that matches `legacy-backend/CaseNewtype.js`, and is slightly shorter, so I made no compiler changes. I rebuilt `leanscript` from the current sources and regenerated the file; the JS and `Term` outputs came out byte-for-byte the same as the committed snapshots.

**What the output looks like** (`CaseNewtype-pbo.js`; `-faithful.js` is the same with `1n`, `2n`, …):
```js
export const test1 = (v) => {
  if (v === 1) { return "1"; }
  if (v === 2) { return "2"; }
  return v === 3 ? "3" : "catch";
};
```
`test2` is the same, with the parameter named `a`, because the Lean pattern-matching definition has no user-given name for it.
- The one-field structure `NewTypeInt` is stored as its `Int`, with no record and no `._1`, just like PureScript's newtype.
- `match v.val` and `match v with ⟨1⟩` produce the same code.
- The optimized `Term` (`CaseNewtype-Term-optimized.txt`) is already a single test per arm, the same decision tree as PBO's. The only change from PBO is that the last `if` becomes a `?:`.
- There is no recursion or shared tail, so no labelled block or loop is needed.

**Comparison with PBO.** For inputs -1, 0, 1, 2, 3, 4 and 12, on both functions and both presets, our answers equal Lean's. We make exactly as many comparisons as PBO on every input: 1, 2 or 3.

**A problem I found and fixed.** The generated `CaseNewtype-*.check.mjs` files contained no checks at all ("0 passed, 0 failed"). I fixed this in `LeanScriptCli/Check.lean`:
- A structure with one field is now accepted as a check argument or result, using its field's sample values, since that is how it is stored in JS. The exception is a field that is itself a tagged union, which still has no Lean `ToString` to compare against.
- `1` and `2` are now among the `Int` samples, so the checks reach the `| 1` and `| 2` arms here and in other snapshots.
- `CaseNewtype` now runs 14 checks per preset, all passing.

**Effect on other snapshots.** I regenerated all of them. Only `*.check.mjs` files changed (52 of them, now with more cases); no generated JS changed, and every node check passes. The snapshot script still exits 1, only because of the known "literal too big" errors in the `PrimOpInt*Configurable` files.

**New test.** I added a test in `Tests/Main.lean`, and `scripts/count-comparisons.mjs` now also accepts one-argument functions. For both presets the test checks that:
- the generated checks actually run and none fail;
- every answer equals the Lean `match`;
- we never make more comparisons than PBO;
- no field is ever read.

`lake build tests leanscript` succeeds and `lake exe tests` passes 81/81. Nothing new was formally proved, so I added no rows to the Properties table. All work is committed.

# Summary of changes for run 014398fd-e9fe-4b8e-9aa6-575964a558cb
`CaseNamed` now compiles to JavaScript that is as good as `legacy-backend/CaseNamed.js` or better. `test1` has the same shape as purescript-backend-optimizer's (PBO) version, and `test2` makes fewer string conversions on three of its four paths and the same number on the last. The fix is a new pass in the `Term → Term` optimizer, the phase you preferred, with proofs.

**What was wrong**
- `test1`: every arm computed `String(x)` separately.
- `test2`: the last arm converted `a` twice (`String(f$1) + f$1`), so that path made 4 conversions where PBO makes 3.

**Output now** (`CaseNamed-pbo.js`; `-faithful.js` is the same with `1n`):
```js
export const test1 = (x) => {
  const x$1 = String(x);
  if (x === 1) { return x$1 + x$1 + x$1; }
  return x === 2 ? x$1 : "any: " + x$1 + x$1 + x$1;
};
export const test2 = (x) => {
  const { _1: f$1, _2: f$2, _3: f$3 } = x;
  if (f$1 === 1) { return String(f$2) + f$3 + "1"; }
  const x$4 = String(f$1);
  if (f$2 === 1) { return x$4 + f$3 + "1"; }
  const x$5 = String(f$2);
  if (f$3 === 1) { return x$4 + x$5 + "1"; }
  const x$6 = String(f$3);
  return x$4 + x$4 + x$5 + x$5 + x$6 + x$6;
};
```
Counting by hand from this output (not measured by a tool), `test2` makes 2, 2, 2 and 3 conversions on its four paths. PBO computes all three `toString`s up front, so it makes 3 on every path. There's no recursion or shared tail here, so no labelled blocks or loops are needed.

**The new pass** (`LeanScript/Term/Optimize/Hoist.lean`, `HoistExpr.lean`, `ExternEq.lean`)
- It looks for a call of an extern whose arguments are all variables, such as `toString x`.
- If every path of a statement already makes that call, and it appears at least twice, the call is made once in front of the statement and every occurrence is replaced by the new name. No path does more work than before.
- It runs inside `Term.optimize`, right after the existing common-subexpression pass.
- Two calls count as the same when their externs are equal by `Extern.beq`, which is proved correct (`Extern.eq_of_beq`). It only recognises the extern families where Lean could derive equality automatically: arithmetic, bitwise, conversion and string externs. Calls from the other families are never shared, which is safe but misses some cases.

**Proofs** (no `sorry`, standard axioms only), both added to the Properties table as proved:
- `Term.hoistWalk_eval`: the pass doesn't change `eval`. `Term.optimize_eval` still holds with the pass included.
- `Term.numCalls_hoistWalk`: the pass adds no calls, so `Term.numCalls_optimize` still holds.
- One limit: "no path makes more extern calls than before" comes from how the pass chooses what to hoist, and is not proved.

**Effect on other snapshots.** I regenerated all of them with `scripts/leanscript-snapshots.sh` and every node check passes. The script still exits 1, only because of the known "literal too big" errors in the `PrimOpInt*Configurable` files. Two other snapshots changed:
- `IntPow.powSum`: `x^3 + x^3` became `x*x*x*2`.
- `ProfunctorLenses01`: `String(x)`, which appeared in both arms of `x < 0 ? {…String(x)} : {…String(x)}`, is now computed once. The speed is the same, but the function is now a block instead of a single expression, so it's a few lines longer.

**New test.** The generated `CaseNamed-*.check.mjs` only try inputs that reach the last arm, so I added a test to `Tests/Main.lean`. For both presets it:
- runs every arm and compares each answer with the Lean `match`;
- checks that `test1` converts `x` exactly once, before the tests;
- checks that `test2`'s last `return` makes no conversion of its own.

`lake build tests TermTests TyTests JsSpec JsTerm leanscript` succeeds and `lake exe tests` passes 80/80. Everything is committed.

# Summary of changes for run 5f82cc03-3403-467f-a252-e83b868e2365
I checked `CaseMulti` again. The code as it stands already produces JS that is as good as `legacy-backend/CaseMulti.js` or better, so I made no changes this session.

**What I ran**
- I rebuilt `leanscript` from the current sources and regenerated `CaseMulti` with `--check`.
- All six output files (`CaseMulti-Term-unoptimized.txt`, `CaseMulti-Term-optimized.txt`, `CaseMulti-pbo.js`, `CaseMulti-faithful.js` and both `.check.mjs` files) came out byte-for-byte the same as the committed snapshots.
- The generated node checks pass: 13/13 for the `pbo` preset and 13/13 for `faithful`.
- I did not re-run the full `lake exe tests` suite.

**Output now (`CaseMulti-pbo.js`)**
```js
export const test1 = (x, y) => {
  if (x === 1) {
    if (y === 1) { return "1.1"; }
    if (y === 2) { return "1.2"; }
    if (y === 3) { return "1.3"; }
    if (y !== 4) { return y === 5 ? "1.5" : "_._"; }
  } else if (y !== 4) {
    return y === 2 ? "_.2" : "_._";
  }
  return "_.4";
};
```
`CaseMulti-faithful.js` is the same with BigInt literals (`1n`, `2n`, …).

**Comparison with purescript-backend-optimizer**
- **Results:** I ran our output and theirs through `scripts/count-comparisons.mjs` for every `x` in {0,1,2} and `y` in {0,…,6}. Both give the same result for every pair.
- **Comparisons:** the number of comparisons is also identical on every pair. For example, 5 for `(1,4)`, 2 for `(0,4)`, and 6 for `(1,0)`.
- **Size:** ours is smaller. `"_.4"` is written once instead of twice, there are two fewer `if` statements, and the function takes both arguments at once instead of being curried.
- **Labelled blocks:** nothing here needs a labelled block or loop. It is plain nested `if`s and returns, so there is no recursion or stack-depth risk.

**Where each part happens in your pipeline**
- **Term → Term optimizer:** its output (`CaseMulti-Term-optimized.txt`) is already the same decision tree as the purescript-backend-optimizer's, one test per `if`.
- **JsTerm → JsTerm:** the only step that improves on it is the tail-sharing pass (`JsTerm/Lower/ShareTail.lean`), done in an earlier session. It writes `return "_.4"` once and has each branch fall through to it. It shares a tail only when that doesn't make any input do more comparisons.
- Neither Term optimization was possible here, because the saving comes from merging identical JS tails, which only exist after conversion.
- The existing `CaseMulti` test in `Tests/Main.lean` checks both properties: answers equal the Lean `match`, and our comparison count is never above theirs.

No properties were added, since no new formal result was proved.

# Summary of changes for run f1979b50-1050-4919-9c64-d218ea6cf35c
`CaseMulti` now makes no more comparisons than `legacy-backend/CaseMulti.js` on any input, and its code is shorter. The fix is in the JsTerm → JsTerm pass that shares common tails. It is checked by tests and snapshots, not by a proof.

**What was wrong.** The `Term` after optimisation was already the same decision tree as PBO's. The problem came later, in the pass that writes a repeated fall-through only once (`JsTerm/Lower/ShareTail.lean`). That pass shared `if (y === 4) return "_.4"; return y === 5 ? …` with the leaf `return "_.4"` in the `x ≠ 1` branch, which is already inside a `y === 4` test. The jump from that leaf then tested `y === 4` a second time. So for `x ≠ 1, y = 4` the old output made 3 comparisons where PBO makes 2.

**Output now** (`CaseMulti-pbo.js`; `-faithful.js` is the same but uses `1n`, `2n`, …):
```js
export const test1 = (x, y) => {
  if (x === 1) {
    if (y === 1) { return "1.1"; }
    if (y === 2) { return "1.2"; }
    if (y === 3) { return "1.3"; }
    if (y !== 4) { return y === 5 ? "1.5" : "_._"; }
  } else if (y !== 4) {
    return y === 2 ? "_.2" : "_._";
  }
  return "_.4";
};
```
- **Speed:** on every pair in {0,1,2} × {0..6}, the number of comparisons is exactly PBO's.
- **Size:** `"_.4"` is written once, and there are two fewer `if` statements than in PBO's version.
- **Labelled blocks:** nothing here needs one. Where a shared tail does need one, the pass still writes a labelled block with `break`.

**The change.** Sharing a tail used to be chosen only by code size. Now, whenever a jump comes from a copy of the tail that the surrounding tests have already narrowed down, each test the tail will run again adds a penalty (`retestCost` = 20 characters, about the size of one `if`). That makes this kind of sharing happen only when it saves more code than repeating the tests would cost.

**Why not in the earlier phases:** there was nothing to fix there. The optimised `Term` already matches PBO's tree, and the extra test was introduced only by this JsTerm pass.

**Effect on other snapshots.** I regenerated all of them with `scripts/leanscript-snapshots.sh`, and every node check passes. Only two other files changed:
- `CaseJacobs.test1` no longer tests `f$4.tag === 3` twice, and now has the same structure as PBO's.
- `CaseRecord.Test2$test2` no longer tests `b === 1` twice, and is shorter.

I tried larger penalties too, but they made `CaseRecord.test1` and `CaseRedBlackTree` noticeably longer, so I kept 20.

**New test.** The generated `CaseMulti-*.check.mjs` files only try inputs that return `"_._"`, so I added a test in `Tests/Main.lean` using a new helper, `scripts/count-comparisons.mjs`. It runs both presets and PBO's JS on the whole grid above and counts every comparison with a literal. It checks that:
- each answer equals the Lean `match`;
- our comparison count is never above PBO's on any input.

The old output fails this test at (0, 4) and (2, 4).

**Checks:**
- `lake build JsTerm JsSpec tests leanscript` succeeds.
- `lake exe tests` passes 79/79.

Nothing new was formally proved, so I added no rows to the Properties table. All work is committed.

# Summary of changes for run bbd12bbe-c1a3-401b-8046-7accbe90b348
The JS for `CaseLeafTco` now has the same shape as `legacy-backend/CaseLeafTco.js`, and is a bit better in places. It took two changes: one in the `Term → JsTerm` conversion and one in the JsTerm pass that shares code between the functions of a module. Neither change is formally proved. They are checked by the node tests, the snapshots and a new test.

**Problems in the old output**
1. Each loop iteration built an option and then took it apart right away:
   ```js
   let x$3;
   if (0 < p$1.length) { x$3 = { tag: 1, _1: p$1[0] }; } else { x$3 = { tag: 0 }; }
   if (x$3.tag === 0) { … }
   ```
   In the optimized `Term` this is a join point whose body does `case` on its parameter, reached by two jumps: one passes `ctor#1(…)`, the other `ctor#0()`.
2. `test1FuelCalled` contained a second full copy of `test1Fuel`'s loop, with `1000000` in place of the first parameter. `Term` has no global definitions, so the call gets inlined. PBO writes it as a plain call.

**Output now** (`CaseLeafTco-pbo.js`; `-faithful.js` is the same but uses `1000000n`):
```js
if (0 < p$1.length) {
  const x$3 = p$1[0];
  if (x$3 === 1) { … } else { … }
} else { … }
…
export const test1FuelCalled = (b, arr) => test1Fuel(1000000, b, arr);
export const test1FuelCalled$$mut_1 = (b, arr) => test1Fuel$$mut_2(1000000, b, arr);
```
It matches PBO's control flow. It is better in three ways: tests are `x === 1` rather than `Int_instDecidableEq(v7, 1)`, the array is one flat literal rather than 17 nested spreads with `Array_append`, and the version that owns its array updates it in place. The loop is still a `while (true)` loop, so recursion depth isn't an issue.

**Change 1: `Term → JsTerm` conversion** (`JsTerm/Lower/FromTerm.lean`, `JsTerm/Lower/Basic.lean`)
- This applies to a join point whose body starts with a case analysis of its parameter and reads it nowhere else.
- At a jump that passes a constructor literal, the arm for that constructor is converted right there, using the literal's fields. This only happens for constructors that no other jump passes, so no code is duplicated.
- If every jump is handled this way, the join point disappears. Otherwise it stays for the remaining jumps.
- A new mapping in `Names` from `Term` join-point indices to `JsTerm` ones (`jmap`, `inl`) keeps the jumps inside the moved arm pointing at the right join points. The arm also gets the bounds and constructor facts known at the jump, which is why `p$1[0]` is written without a bounds check.

**Change 2: sharing code between functions** (`JsTerm/Print/Share.lean`, `literalCalls`)
- A function `g` becomes a call `f(lit, params…)` of an earlier function `f` only when two things hold:
  - `g`'s code dump is exactly `f`'s dump with its first parameter replaced by the literal;
  - the call is shorter than the code. Without this rule, `test9 = (a) => !a` in `PrimOpBoolean01` turned into `test6(true, a)`, so I added the length check.

**Why not the `Term` optimizer (your first choice):** every rewrite there has to come with a proof that `eval` is unchanged. This one needs substitution, weakening from the join point's context to the jump's context, and reindexing of the join-point context, all proved correct against the evaluator's join-point semantics in the intrinsically typed `Term`. That is a large piece of new proof work, so I did the rewrite in the next phase you preferred instead.

**Checks**
- All snapshots were regenerated with `scripts/leanscript-snapshots.sh`, and all 342 node check runs pass.
  - The script still exits 1, only because of the known "literal too big" errors in the `PrimOpInt*Configurable` files.
  - Apart from `CaseLeafTco`, one snapshot changed: `OptionUnbox` `test6` builds no option any more and is shorter.
- `lake build JsTerm JsSpec tests leanscript` succeeds.
- `lake exe tests` passes 78/78. That includes a new test in `Tests/Main.lean`: it runs the `CaseLeafTco` checks in both presets, checks that no option or join variable is built, and checks that `test1FuelCalled` calls `test1Fuel`.

I added no rows to the Properties table, because none of this is a formally proved result. Everything is committed.

# Summary of changes for run 1bede2c0-a286-42bf-b63d-f580e62309be
`Tests/SnapshotsPBOPure/CaseJacobs.lean` now translates, and the generated JS is equal to or better than `legacy-backend/CaseJacobs.js`. This work is all in the conversion, JS-optimisation and printing phases, and none of it is proved; the Term optimizer is untouched.

**What was wrong.** The committed CaseJacobs outputs were empty. The CLI never declared signatures, so it rejected both functions with "the recursive type Expr is not declared in any signature".

**What the output looks like now.** `Tests/SnapshotsPBOPure/CaseJacobs-pbo.js`:
- `renderExpr` is plain direct recursion: an `if` chain on `a.tag` that recurses on the fields. It matches PBO without the nested `else`.
- `test1` is one decision tree. Each shared fall-through (`e7`, `e4`) is written once and reached by falling out of the `if`s, where PBO repeats `return "e7: " + renderExpr(v0)` four times. A constructor rebuilt from the fields being matched (`x@(.add a b)`) is written as the original value `a`, as PBO does, with no alias constant. Calls sit inline in the string concatenations.
- Both preset outputs pass 148 checks each, run with node on samples of the recursive type.
- PBO also exports `instToStringExpr_toString = renderExpr`; we don't export the instance.
- One small leftover: `const { _1: f$5, _2: f$6 } = f$3;` is not yet moved into the one branch that uses it.

**Changes, by phase:**
- **CLI** (`LeanScriptCli/Frontend.lean`, `Main.lean`, `LeanScript/GenElab/Signature.lean`): the recursive types a file uses are now declared automatically. `LeanScriptCli/Check.lean` now also builds sample values of recursive union types for the checks.
- **Term → JsTerm** (`JsTerm/Lower/FromTerm.lean`, `Basic.lean`, `DataRec.lean`):
  - When a fold's case analysis is on the parameter it recurses on, the analysis is merged into the branch, so no pairs are built.
  - Facts recorded from case analyses let a rebuilt constructor reuse the matched value. This session I made such a rebuilt value just a new name for the original instead of a `const k = a` alias; that alias was what stopped the last duplicated `e7` arm from being shared.
- **JsTerm → JsTerm:** a new `JsTerm/Lower/Globals.lean` makes a module's recursive functions call each other directly by name. `JsTerm/Syntax/Vars/Occs.lean` moves calls into concatenations when the evaluation order stays the same.
- **Printing** (`JsTerm/Print/Mini/Block.lean`): a pattern field the block never reads is no longer bound. This removes dead `const { _1: f } = a;` lines in `ScalarRepl`, `LoopState` and similar files.

**Why not in the Term optimizer:** reusing a matched value is only valid under facts from the enclosing case analyses, and the Term optimizer requires a proof that the result is unchanged. That proof would need a large new body of lemmas, so the rewrite went into conversion.

**Labelled blocks and loops:** shared tails become labelled blocks with `break`, and folds keep compiling to loops. `renderExpr` stays ordinary recursion, as in PBO, because it is not tail-recursive.

**Checks:**
- All snapshots were regenerated with `scripts/leanscript-snapshots.sh`, and every node check passes. The script still exits 1, only because of the known "literal too big" errors in the three `PrimOpInt*Configurable` files.
- Other snapshots got shorter (for example `RecData`, `OwnershipAliasing`, `CaseGuardedSweep`). Newly translated files (for example `CaseGuarded`, `ProfunctorLenses01`, `KnownConstructor07`) now have output where they had none.
- `lake build JsTerm JsSpec tests leanscript` succeeds, and `lake exe tests` passes 77/77.
- Everything is committed.

# Summary of changes for run e0e7c6c6-0da2-4e01-8d12-7c42e4b25e01
I made no code changes this session. The JavaScript for `CaseInt` already matches purescript-backend-optimizer's legacy output and is slightly shorter, so there was nothing left to optimise.

**Checks**
- I rebuilt `leanscript` from the current source and regenerated all six `Tests/SnapshotsPBOPure/CaseInt-*` files. They came out byte-for-byte identical to the committed ones, and `git status` is clean.
- The generated checks `CaseInt-pbo.check.mjs` and `CaseInt-faithful.check.mjs` pass 5/5 each.
- Those checks only try the inputs −7, −1, 0, 3 and 12, so the `1` and `2` arms are never tested. I ran the functions by hand on 0–4 in both presets and got `catch, 1, 2, 3, catch`, which is correct. That hand check isn't saved anywhere in the project.

**Current output** (`CaseInt-pbo.js`; `-faithful.js` is the same except it uses BigInt literals `1n`, `2n`, `3n`):
```js
export const test1 = (a) => {
  if (a === 1) { return "1"; }
  if (a === 2) { return "2"; }
  return a === 3 ? "3" : "catch";
};
```

**Compared with `legacy-backend/CaseInt.js`:**
- **Same tests:** both run the same three comparisons in the same order, so no input costs more tests than in PBO's version.
- **Shorter:** ours has one fewer `if` statement, because the last test and the fall-through `"catch"` become one ternary.

**Which phase does the work** — your preferred phase, `Term → Term`:
- The step from Lean to `Term` already turns the `Int` match into a chain of `lean_int_dec_eq` tests with one final `"catch"`. Lean's decision tree creates no repeated fall-through here, so there's nothing to share.
- The `Term` optimizer then turns the last `if` into `cond(lean_int_dec_eq(x2, 3), "3", "catch")`, which prints as the ternary. You can see this by comparing `CaseInt-Term-unoptimized.txt` with `CaseInt-Term-optimized.txt`.
- The later phases (`Term → JsTerm`, the `JsTerm` optimizer) only print this out; nothing needs deduplicating.
- No labelled blocks or loops are needed: the function has no shared tail and no recursion, so nothing risks a stack overflow.

The only Lean I built was the `leanscript` executable, to regenerate the snapshots; I'm claiming no new Lean results.

# Summary of changes for run 1fbff342-249f-48d7-8a5c-ac17ace2328d
The JavaScript for `CaseHeuristics` is now better than purescript-backend-optimizer's legacy output for all four functions. All 21 generated checks pass in both presets.

**What was wrong with the old output.** Lean compiles each `match` into a decision tree and copies the last pattern (`_, _ => …`) into every branch where an earlier test fails. As a result:
- `testPB` repeated its fall-through five times.
- `testPBA` and `testPBAN` repeated `return 4` many times.
- There were tests with identical outcomes, like `a1.tag === 1 ? 4 : 4`.

**Result (`pbo`; `faithful` is the same with BigInt literals):**
```js
export const testPB = (a, a1) => {
  if (a.tag === 1) {
    if (a._1 === 1 && a1.tag === 1 && a1._1 === 1) { return 1; }
  } else if (a.tag === 2 && a._1 === 2 && a._2 === 3 && a1.tag === 2 && a1._1 === 2 && a1._2 === 3) {
    return 2;
  }
  return a1.tag === 0 ? 3 : 4;
};
```
- `testPBA` and `testPBAN` also end in a single `return 4;`, with no repeated tag test.
- `testP` keeps its shape but drops the repeated `a2 === 4 ? 4 : 5`.
- Line counts: `testPB` 16 vs PBO's 23, `testPBA`/`testPBAN` 14 vs 20, `testP` 18 vs 22.

**Where the changes are.** None are in the `Term` optimizer. Its rewrites all carry proofs that `eval` is unchanged, and this one would need two things `Term` lacks: a default case arm, and a join point that passes no value (every type has at least two values). Proving that comparison and specialisation preserve `eval` in the intrinsically typed `Term` was more than I could finish here. The conversion step (`Term → JsTerm`) wasn't a good fit either, because the rewrite needs whole blocks to compare.
- **`JsTerm` optimizer, new pass `JsTerm/Lower/ShareTail.lean` (`JsBlock.shareTails`):** at each test, it finds a block that ends two or more branches and writes it once after a labelled block `L: { … }`. Each copy becomes `break L;`, or nothing when it falls through.
  - Tests already decided above a copy are taken into account: inside `a1.tag === 0`, `return 3` counts as a copy. This only uses tests on constants, whose values can't change.
  - `return c ? a : b` becomes `if (c) return a;` plus a jump when `return b` is a copy.
  - Among candidates it keeps the one whose printed JavaScript is shortest, and only if that is shorter than the original (`blockCost` in `JsTerm/Print/Share.lean`).
  - The pass runs between two runs of the existing `mergeIte`.
- **Printer (`JsTerm/Print/Mini/`):**
  - Identical case arms are written once under `t₀ || t₁`, and the most common arm comes last with no test (`groupedChain`).
  - `if (c) { if (b) S }` becomes `if (c && b) S`.
  - A jump that carries no value writes no assignment and needs no `let x;`.

**Checks.**
- I regenerated all snapshots: every generated check passes, and 16 other snapshot files changed, all shorter or dead code removed (e.g. `a.tag === 1 ? a : a` becomes `a`).
- The script still exits with status 1, but only because of the same "literal too big" errors (the `PrimOpInt*Configurable` files) it reported before these changes.
- `lake exe tests` passes, including a new test in `Tests/Main.lean` that checks `CaseHeuristics`.
- A full `lake build` fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib, and Mathlib isn't available here. I didn't touch that file. `lake build JsTerm JsSpec tests leanscript` succeeds.

**Proofs.** In the model of JavaScript with state and exceptions from `JsSpec/MergeIte.lean`, `JsSpec/ShareTail.lean` proves, with no `sorry` and only standard axioms:
- `TStmt.labelled_share_den`: sharing a tail behind a labelled block keeps the meaning, including copies narrowed by earlier tests and the `? :` form.
- `chain_eq_arm`: the grouped chain of arms computes the arm for the actual tag.
- `jsAnd_not_eq_eq`: `!(x === l₁) && x === l₂` equals `x === l₂` when `l₁ ≠ l₂`.

These are proofs about a model of the algorithms, not the `JsTerm` code itself, and the code's "same dump" check is modelled as syntactic equality. They are registered as proved in the Properties table.

# Summary of changes for run fb688dc2-829b-4305-81b2-e73561aa086f
I proved the CaseGuarded changes in Lean. Both files build with no `sorry` and use only the standard axioms. One limit: the proofs about the JavaScript-side rewrites are about a model of the algorithm, not the `JsTerm` code itself, because `JsTerm` has no formal semantics.

**1. `test1` through the `Term` optimizer** (`Tests/TermTests/Optimize/CaseGuardedTest.lean`)
- `test1_optimized_run`: for every `n : Int`, the translated and optimised `Term` (`Term.optimizeN 3`) computes the Lean `test1 n`, including `toString n`, which is now the new extern `lean_int_repr`.
- It rests on `test1T_run`, checked by the kernel with `kernel_rfl`: the translated statement's three tests, with its strings built by `Int.repr`.
- `test1_optimized_pretty`: the optimised term is exactly the one in `CaseGuarded-Term-optimized.txt`. This is checked with `native_decide`, since the printer is compiled code.
- `eval_lean_int_repr` and `eval_lean_nat_repr`: the two new externs mean Lean's `toString`, so the existing proof that the optimizer doesn't change `eval` covers them.

**2. The JavaScript-side rewrites** (new library `JsSpec`, file `JsSpec/MergeIte.lean`)
These three rewrites can't be expressed in `Term`, so they're proved in a small model of JavaScript where every expression or statement reads and writes a state and may throw. Evaluation order, side effects and exceptions all count.
- **Merged tests** (`Stmt.mergeIte_den`):
  - The model repeats the algorithm of `JsTerm/Lower/MergeIte.lean`, including left-grouping of `&&`/`||` chains.
  - Rewriting `if (a) { if (b) T; E } E` to `if (a && b) T; E`, and the `||` form, bottom-up, leaves every statement's meaning unchanged, whatever the tests and other statements do.
  - The implementation decides that two statements are the same by comparing their dumps; the model treats that as syntactic equality, which is not itself proved.
- **`&&` and `||`**:
  - `cond_false_eq_and` / `cond_true_eq_or`: `c ? a : false` equals `c && a`, and `c ? true : b` equals `c || b`.
  - `jsAnd_assoc` / `jsOr_assoc`: a chain can be regrouped to the left.
- **Numbers in a concatenation**:
  - `plus_str_digits` / `plus_digits_str`: in a model of JavaScript `+` on numbers, BigInts and strings, `s + String(x)` equals `s + x`, and `String(x) + s` equals `x + s`.
  - `plus_str_num`: `"n: " + n` equals Lean's `"n: " ++ toString n`.
  - This rests on one modelling assumption: JavaScript's conversion of a safe integer or BigInt to a string gives the same decimal digits as Lean's `toString`.

**Build:** `lake build JsSpec TermTests` succeeds, and I added `JsSpec` to `lakefile.toml` and its default targets. `rg` finds no `sorry` or `admit`. `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`, plus the axiom `native_decide` generates for the printer check. The four main results are marked proved in the Properties table, and all work is committed.

# Summary of changes for run a78d54e4-d55b-499f-ac6f-a121c67c56f7
I made no code changes this session. The JavaScript output for `CaseGrafting` is already better than purescript-backend-optimizer's legacy output, so there was nothing left to optimize.

**Checks:**
- I rebuilt `leanscript` from the current source and regenerated the `Tests/SnapshotsPBOPure/CaseGrafting-*` files. They came out byte-for-byte identical to the committed ones, and `git status` is clean.
- The generated checks `CaseGrafting-pbo.check.mjs` and `CaseGrafting-faithful.check.mjs` pass 8/8 each, which covers every combination of the three `Bool` arguments.

**Current output** (`CaseGrafting-pbo.js`; `-faithful.js` is the same except it uses BigInt literals `1n`…`4n`):
```js
export const test1 = (a, a1, a2) => {
  if (a1) {
    if (a) {
      return a2 ? 4 : 3;
    }
    return 2;
  }
  return a2 ? 1 : 3;
};
```

**Compared with `legacy-backend/CaseGrafting.js`:**
- **Fewer tests:** ours checks each argument at most once, so a call makes at most 3 tests. PBO's checks `v1` and `v2` more than once, making up to 5 tests on some inputs.
- **No dead code:** ours has no unreachable `if (v2)` and no `throw new Error("UNREACHABLE")`.
- **One function:** ours is a single function taking all three arguments, where PBO's is three nested closures.

**Which phase does the work:**
- **Before the `Term` optimizer:** the step from Lean to `Term` turns Lean's sparse case analysis (`_sparseCasesOn`) into a full case split. This comes from `sparseAsCasesOn?` in `LeanScript/TermElab/ToTerm/Expr/Cases.lean`, which is called from `LeanScript/TermElab/ToTerm/Expr.lean`.
- **`Term` optimizer (your preferred phase):** it turns the innermost `if`s into `cond(x6, 4, 3)` and `cond(x6, 1, 3)`, which print as the ternaries. You can see this by comparing `CaseGrafting-Term-unoptimized.txt` with `CaseGrafting-Term-optimized.txt`.
- **`Term → JsTerm` conversion and the `JsTerm` optimizer:** they add nothing for this file.

This function has no recursion or loops, so labelled blocks and loops don't come into play here. No Lean theorems were involved, so the Properties table is unchanged.

# Summary of changes for run 47d9506c-cc16-4c16-bcc9-b60d06e01ed0
I made no changes this session. `CaseGrafting`'s JavaScript output is already better than purescript-backend-optimizer's legacy output, so there was nothing left to optimize.

**Checks:** I rebuilt `leanscript` from the current source and regenerated the `Tests/SnapshotsPBOPure/CaseGrafting-*` files. They came out byte-for-byte identical to the committed ones (`git status` is clean). The generated checks `CaseGrafting-pbo.check.mjs` and `CaseGrafting-faithful.check.mjs` pass 8/8 each, covering every combination of the three `Bool` arguments.

**Current output** (`CaseGrafting-pbo.js`; `-faithful.js` is the same except it uses BigInt literals `1n`…`4n`):
```js
export const test1 = (a, a1, a2) => {
  if (a1) {
    if (a) {
      return a2 ? 4 : 3;
    }
    return 2;
  }
  return a2 ? 1 : 3;
};
```

**Compared with `legacy-backend/CaseGrafting.js`:**
- **Fewer tests:** ours checks each argument at most once, so a call makes at most 3 tests. PBO's checks `v1` and `v2` more than once, making up to 5 tests on some inputs.
- **No dead code:** ours has no unreachable `if (v2)` and no `throw new Error("UNREACHABLE")`.
- **One function:** ours is a single function taking all three arguments, where PBO's is three nested closures.

**Which phase does the work:**
- **Before the `Term` optimizer:** the step from Lean to `Term` turns Lean's sparse case analysis (`_sparseCasesOn`) into a full case split. This was added in an earlier session in `LeanScript/TermElab/ToTerm/Expr/Cases.lean` (`sparseAsCasesOn?`).
- **`Term` optimizer (your preferred phase):** it turns the innermost `if`s into `cond(x6, 4, 3)` and `cond(x6, 1, 3)`, which print as the ternaries. You can see this by comparing `CaseGrafting-Term-unoptimized.txt` with `CaseGrafting-Term-optimized.txt`.
- **`Term → JsTerm` conversion and the `JsTerm` optimizer:** they add nothing for this file.

This function has no recursion or loops, so labelled blocks and loops don't come into play here. No Lean theorems were involved, so the Properties table is unchanged.

# Summary of changes for run 27a66449-9222-4829-9974-31c76bbf45de
I made no changes. `CaseGrafting`'s JavaScript output already beats purescript-backend-optimizer's legacy output, because of the fix from the previous session. That fix is in the source (`sparseAsCasesOn?` in `LeanScript/TermElab/ToTerm/Expr/Cases.lean`, called from `LeanScript/TermElab/ToTerm/Expr.lean`).

**Checks:**
- I rebuilt `leanscript` from the current source and regenerated all six `Tests/SnapshotsPBOPure/CaseGrafting-*` files. They came out byte-for-byte identical to the committed ones.
- The generated checks `CaseGrafting-pbo.check.mjs` and `CaseGrafting-faithful.check.mjs` pass 8/8 each, covering all eight Boolean argument combinations.

**Current output** (`CaseGrafting-pbo.js`; `-faithful.js` is the same with `1n`…`4n`):
```js
export const test1 = (a, a1, a2) => {
  if (a1) {
    if (a) {
      return a2 ? 4 : 3;
    }
    return 2;
  }
  return a2 ? 1 : 3;
};
```

**Compared with PBO's version** (`legacy-backend/CaseGrafting.js`):
- Ours tests each argument at most once, so any call does at most 3 tests. PBO's re-tests `v1` and `v2`, and one path does 5.
- Ours has no dead `if (v2)` and no `throw new Error("UNREACHABLE")`.
- Ours is a single uncurried function rather than three nested closures.

**Where the work happens:**
- **Elaboration** turns Lean's sparse case analysis (`_sparseCasesOn`) into an ordinary full case split. This is what lets `test1` translate at all.
- **`Term` optimizer** (your preferred phase) turns the innermost `if`s into `cond(x6, 4, 3)` and `cond(x6, 1, 3)`, which print as the ternaries. You can see this by comparing `CaseGrafting-Term-unoptimized.txt` with `CaseGrafting-Term-optimized.txt`.
- **`Term → JsTerm` conversion and `JsTerm → JsTerm` optimizer** add nothing for this file.

There is no recursion or loop in this file, so labelled blocks and loops don't apply and there is no stack-overflow risk.

No Lean theorems were involved, so the Properties table is unchanged.

# Summary of changes for run c30895da-dd6f-4dbf-b87d-a23c0d14faa4
`CaseGrafting` now translates, and its JS is better than purescript-backend-optimizer's legacy output. Before this change `test1` wasn't translated at all: every output file only said "the helper `test1._sparseCasesOn_1` is universe polymorphic".

**Why it failed.** For overlapping patterns like these, Lean's `match` compiler emits a sparse case analysis, `T._sparseCasesOn_k`. It has arms for only some constructors plus a catch-all `else`. The translator didn't recognise it, fell back to treating it as an ordinary helper function, and rejected it for being universe polymorphic.

**The fix is in elaboration (Lean → `Term`), the step before the `Term` optimizer.** Nothing needed to change in `Term → Term`, `Term → JsTerm` or `JsTerm → JsTerm`:
- A new `sparseAsCasesOn?` in `LeanScript/TermElab/ToTerm/Expr/Cases.lean` rewrites a sparse case analysis into the full `T.casesOn` it stands for, built the same way Lean's own `mkSparseCasesOn` builds it.
  - Each constructor that has an arm gets that arm.
  - Every other constructor gets the `else` branch, applied to a proof that the translation erases.
  - The catch-all is passed as an extra argument, which the existing `casesOn` translation already pushes into the branches.
- `LeanScript/TermElab/ToTerm/Expr.lean` calls it wherever `_sparseCasesOn` appears.

**Output now** (`CaseGrafting-pbo.js`; `-faithful.js` is the same with `1n`…`4n`):
```js
export const test1 = (a, a1, a2) => {
  if (a1) {
    if (a) { return a2 ? 4 : 3; }
    return 2;
  }
  return a2 ? 1 : 3;
};
```
The optimised `Term` is the same decision tree, with the inner branches already turned into `cond` by the `Term` optimizer.

**Compared with PBO's version:**
- Ours tests each argument at most once, so any call does at most 3 tests. PBO's re-tests `v1` and `v2` and can do up to 5.
- There is no dead `if (v2)` and no `throw new Error("UNREACHABLE")`.
- It is a single uncurried function.
- There is no recursion or loop, so labelled blocks and loops don't come into it for this file.

**Checks:**
- The generated differential checks cover all 8 argument combinations and pass 8/8 in both presets.
- I regenerated every snapshot with `scripts/leanscript-snapshots.sh`, and all node checks pass.
- `lake build` builds every default target except `LeanScript.Term.Syntax.UsageAlgebra`. That module imports Mathlib, which this project doesn't depend on, so the failure is unrelated to this change.
- `lake exe tests` passes 76/76.

**Side effects in other snapshots.** The same fix lets more definitions translate:
- `test2`/`test3` in `TagChain`
- `test5` in `CaseGuarded`
- `testPB`, `testPBA`, `testPBAN` in `CaseHeuristics`
- parts of `ProfunctorLenses02` and `RecursionSchemes01`

Their output is correct but not yet tight:
- **Repeated tests:** an inner `match` on the same value re-tests a constructor the outer one has already decided (e.g. `s.tag === 0` inside the `s.tag === 1` branch).
- **Pointless ternaries:** some have identical branches, like `x ? 4 : 4`.

Removing those would take a new "known constructor" pass in the `Term` optimizer, with its proof that `eval` is unchanged; I haven't done that. `TagChain`'s `test1` now fails with a different message, an `omega` error, which I haven't investigated.

No Lean theorems were added or changed, so nothing was added to the Properties table. The work is committed.

# Summary of changes for run 60fdd191-962d-472c-997e-10af6daab90a
I made no changes. `CaseChar`'s JS output already matches purescript-backend-optimizer's legacy output, and is slightly shorter.

**Current output** (`Tests/SnapshotsPBOPure/CaseChar-pbo.js`; `CaseChar-faithful.js` is identical):
```js
export const test1 = (a) => {
  if (a === "a") { return "1"; }
  if (a === "b") { return "2"; }
  return a === "c" ? "3" : "catch";
};
```
**PBO's output** (`legacy-backend/CaseChar.js`): the same chain of `if (v === "a") return "1"; …`, but with a fourth `if`/`return` where ours has a ternary.

**How they compare:** both are the same chain of early returns. Each branch does one `===` on the character, which in both backends is a one-character JS string. Neither needs runtime helpers or imports. There is no recursion or loop, so labelled blocks and loops don't come into it, and nothing here can overflow the stack.

**Which phase does the work:**
- **Elaboration:** Lean's `Char` match becomes `lean_string_dec_eq(lean_string_push("", x2), "a")`, one per literal (`CaseChar-Term-unoptimized.txt`). The translator compares characters this way because it can't look inside a `Char` value.
- **`Term` optimizer:** it turns the last `if` into `cond(…, "3", "catch")`, which becomes the final ternary (`CaseChar-Term-optimized.txt`).
- **`Term → JsTerm` conversion** (`lowerExtern` in `JsTerm/Lower/Extern.lean`): it prints `"".push c` as just `c`, and string equality as `===`. This gives `a === "a"`.

That last rewrite can't move into the `Term` phase, your preferred one. In `Term`, a `Char` is not a `String`, so `"".push c` has no simpler form there; the two only coincide after conversion to JS. So the conversion step is the next-best place for it, and no `JsTerm → JsTerm` pass is needed.

**How I checked it:**
- I rebuilt `leanscript` from the current source and regenerated the six `CaseChar` output files. They were byte-for-byte identical to the committed ones.
- The generated checks `CaseChar-pbo.check.mjs` and `CaseChar-faithful.check.mjs` pass 4/4 each. They cover `"a"`, `"z"`, `" "` and `"é"`.
- Those checks never test `'b'` or `'c'`, so I also ran both presets by hand on `a, b, c, d, "ab", 😀`. Both gave `1, 2, 3, catch, catch, catch`, which is what the Lean definition says. This hand check isn't saved in the project.

No Lean theorems were involved, so nothing was added to the Properties table, and there was nothing to commit.

# Summary of changes for run 270dba99-9b5a-499a-8d7d-c84afc62fb48
I made no changes. `CaseBoolean`'s JS output already matches purescript-backend-optimizer's legacy output, and is shorter.

**Current output** (`Tests/SnapshotsPBOPure/CaseBoolean-pbo.js`; `CaseBoolean-faithful.js` is identical):
```js
export const test1 = (a) => (a ? "1" : "2");
```

**PBO's output** (`legacy-backend/CaseBoolean.js`):
```js
const test1 = (v) => {
  if (v) {
    return "1";
  }
  return "2";
};
```

**How they compare:** both test the boolean once, with no runtime helpers and no imports. Ours is a single-expression arrow function, while PBO's needs a block with `if`/`return`. Both presets produce the same code, since a `Bool` is a plain JS boolean in each.

**Which phase does the work:** the `Term` optimizer, which is the phase you prefer. `CaseBoolean-Term-unoptimized.txt` has `if x2 then ret "1" else ret "2"`. `CaseBoolean-Term-optimized.txt` rewrites that to `ret cond(x2, "1", "2")`. The conversion then prints it directly as a ternary. The conversion step and the `JsTerm → JsTerm` step add nothing for this file. Because there is no loop or recursion, there was nothing that needed labelled blocks or loops, and no stack-overflow risk.

**How I checked it:**
- I rebuilt `leanscript` from the current source and regenerated the `CaseBoolean` outputs. The regenerated files matched the committed ones exactly (the working tree stayed clean).
- The generated differential checks passed: `CaseBoolean-pbo.check.mjs` and `CaseBoolean-faithful.check.mjs` each ran 2/2, covering `test1(true)` → `"1"` and `test1(false)` → `"2"`.

No Lean theorems were involved, so nothing was added to the Properties table, and there was nothing to commit.

# Summary of changes for run eab80d7a-b3b3-43d4-99d4-226372c2de6d
I made no changes: `CaseArray`'s JS output was already on par with purescript-backend-optimizer's legacy output, and in one respect better.

**Current output** (`Tests/SnapshotsPBOPure/CaseArray-pbo.js`; the `faithful` preset is the same with `0n`/`1n`/`2n`):
```js
export const test1 = (a) => {
  if (a.length === 0) { return "0"; }
  if (a.length === 1) { return a[0] === 1 ? "1" : "any1"; }
  if (a.length === 2) { return a[1] === 2 ? "2" : "catch"; }
  return a.length === 3 ? "3" : "catch";
};
```

**Compared with `legacy-backend/CaseArray.js`:**
- **Same structure:** a chain of early `return`s on `a.length`, one element read per branch, plain `a[i]` reads with no bounds-checked runtime helper, and no runtime imports.
- **Better on correctness:** PBO's output returns `"1"` for every one-element array, so it loses the difference between `#[1]` and `#[_]`. Ours keeps it with `a[0] === 1 ? "1" : "any1"`.
- **Shorter:** the final `if`/`return` pairs are written as ternaries.

**Where the earlier work went:** the previous session made these improvements, as recorded in `ARISTOTLE_SUMMARY.md`. They sit in the `Term → JsTerm` conversion (`JsTerm/Lower/Bounds.lean`, called from `JsTerm/Lower/FromTerm.lean`) rather than the `Term` optimizer you'd prefer. That's because `Term` can't express either change:
- It has no array read without a default value: the in-bounds proof is erased, so every read becomes `get!`.
- It has no choice between `BigInt` and `number`, which only exists after conversion.

No `JsTerm → JsTerm` pass was needed. There is no recursion and no deep nesting, so nothing here could overflow the stack.

**How I checked it:**
- I rebuilt `leanscript` from the current source and regenerated all six `CaseArray` output files. The result was identical to the committed files.
- The generated differential checks (`CaseArray-pbo.check.mjs` and `CaseArray-faithful.check.mjs`) pass 8/8 each.
- Those checks never reach the `#[1]`, `#[_, 2]` or `#[_, y≠2]` branches. So I ran both JS presets by hand on `#[1]`, `#[7]`, `#[5,2]`, `#[5,3]`, `#[1,2,3]` and `#[]`. Both gave the same answers as Lean's own evaluation of `test1`: `"1"`, `"any1"`, `"2"`, `"catch"`, `"3"`, `"0"`. This hand check isn't saved in the project.

No Lean theorems were involved, so nothing was added to the Properties table, and there was nothing to commit.

# Summary of changes for run 13b05612-04c5-4646-8db7-a3cfc44aa239
`CaseArray` now generates the same JS as purescript-backend-optimizer in both presets, and it keeps the `#[1]`/`#[_]` distinction that PBO's legacy output drops. All differential checks pass.

**What was different.** The branch structure already matched PBO. Two things were left:
1. Each element read under a size test went through the runtime's bounds-checked getter, e.g. `uint53__lean_array_get(0, a, 1)`.
2. The `faithful` preset converted the length before comparing it: `BigInt(a.length) === 2n`.

**Output now (`faithful`; `pbo` is the same with `1`/`2` for `1n`/`2n`):**
```js
export const test1 = (a) => {
  if (a.length === 0) { return "0"; }
  if (a.length === 1) { return a[0] === 1n ? "1" : "any1"; }
  if (a.length === 2) { return a[1] === 2n ? "2" : "catch"; }
  return a.length === 3 ? "3" : "catch";
};
```
The pbo file no longer imports anything from the runtime.

**Why these went in the `Term → JsTerm` conversion, not the `Term` optimizer.** The `Term` language can't express either change:
- It has no array read without a default: the proof that the index is in bounds is erased, so `a[i]` becomes `get!`.
- It has no choice of number representation: `BigInt` vs `number` only exists after conversion.

The `Term` optimizer and its proofs are unchanged. No `JsTerm → JsTerm` pass was needed either.

**Changes** (new file `JsTerm/Lower/Bounds.lean`, called from `JsTerm/Lower/FromTerm.lean`):
- **Tracking sizes:** while converting `if`/`?:`, the conversion records what each test says about array sizes:
  - `a.size = k`, `k < a.size`, `k ≤ a.size` (literal `k`), or `i < a.size` in the `then` branch;
  - the negated forms in the `else` branch, e.g. `a.size ≥ 1` after `a.size = 0`, and `i < a.size` after `a.size ≤ i`.
  - Facts are recorded for constants and for a loop's mutable variables. A loop only reassigns those at the end of an iteration, from values computed before any assignment.
- **Plain reads:** under such a fact, `a[i]!` is written as a new `JsExpr.index`: `a[i]`, or `a[Number(i)]` for a `BigInt` index that isn't a literal. This only happens when the dropped default value involves no operation. All passes and the printer handle the new constructor.
- **Comparing lengths as numbers:** at the `BigInt` preset, `===`, `<` and `<=` between an array length and another length or a small literal now compare plain numbers.

**Rendering:** no recursion was added. Loops stay `while (true)` with `return`, so the stack doesn't grow; the existing labelled blocks are unchanged.

**Tests**
- New snapshot `Tests/SnapshotsMy/ArrayBounds.lean` covers:
  - array-literal patterns;
  - `if h : i < a.size`, `getD`, and the `else` of `a.size ≤ i` and of `a.size = 0`;
  - literal indices under `2 < a.size`;
  - size comparisons;
  - two loops where the index, or the array and the index, are loop variables;
  - an access that isn't known to be in bounds, which keeps its own test.
- **Bug caught and fixed:** my first printer version wrote `Number(i)` without the `a[...]` around it at the `faithful` preset. The differential checks caught it.
- **Other snapshots that improved:**
  - `CaseLeafTco` (both presets) now reads `p$1[0]` under `0 < p$1.length`.
  - `ArrayFSet`, `OwnershipAliasing` and `InlineReferenceOpArrayLength` (faithful) lose their `BigInt(...length)` wrappers.
- **Results:**
  - `scripts/leanscript-snapshots.sh`: all 340 node check outputs report 0 failures. It still exits non-zero for the same reasons as before: the "literal too big" cases and the deliberate `mypanic` test.
  - `lake exe tests`: 76/76 passed.
  - `lake build tests JsTerm leanscript LanguageJavascriptMini` succeeds.
  - Plain `lake build` fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib; that file was already like this in the project and is not imported by anything else.

No Lean theorems were added. These are code-generation changes checked by the differential tests, so nothing was added to the Properties table. All work is committed.

# Summary of changes for run ac02405e-93ac-4066-ad7b-44ceeba7cc30
`CaptureDerefRegression01` was already close to the purescript-backend-optimizer output from earlier sessions: same loop shape, `testOdd` as a short wrapper around `testEven`, and no recursion. The one place it was still no better than PBO was the unrolled loop in `testEven`. It now beats PBO there in both presets, and all differential checks pass.

**What was left.** In the loop that runs two steps per iteration, the second step was built on temporaries from the first: `x5 = p1 + 2; …; p1 = x5 + 3`. PBO produces the same chain.

**Change 1: additions of literals folded through constants** (new file `JsTerm/Lower/AddChain.lean`, in the `JsTerm → JsTerm` phase)
- `x + c2`, where `x` is a constant holding `a + c1`, becomes `a + (c1 + c2)`. On integers, subtracting a literal counts as adding its negative, so `(p - 7) + 3` becomes `p - 4`.
- **Why not earlier phases:** the `Term` optimizer already folds `1 + x + x + 3` to `x * 2 + 4` (see the `AssocIntOps` snapshots). This chain only appears after the loop is unrolled at the JS level, so the `Term` phase never sees it.
- **Safety with mutable variables:** if `a` is a mutable variable, the fold is only done while `a` is certainly unchanged. What is known about it is forgotten after:
  - an assignment to it, or a counter decrement,
  - any function call,
  - entering a closure or a loop, or leaving a loop or a labelled block.
- **Safety with overflow checks:** on the overflow-checked safe-integer operations used by the `pbo` preset, literals are only combined when they have the same sign. That way the new code throws whenever the old one did. BigInt addition is exact, so the `faithful` preset has no such limit.

**Change 2: pure constants moved into the only branch that reads them** (new file `JsTerm/Lower/Sink.lean`)
- If `const x = e` is followed by `if (j === 0) {…} j--;` or an `if/else`, and only one of the two paths reads `x`, the constant moves into that path.
- This is only done when `e` cannot throw, has no effect, and works only on numbers, booleans or strings, so it applies to the `faithful` preset but not to `pbo`'s checked arithmetic.
- The printer then writes the constant directly where it is used.

**Result for `testEven`**
- `faithful`: `if (j$3 === 0n) { return { _1: p$2 + 1n, _2: p$1 + 2n }; } j$3--; p$1 = p$1 + 5n; p$2 = p$2 + 5n;` Each variable now depends only on itself, and the loop does two additions per iteration instead of four.
- `pbo`: `p$1 = int53__lean_int_add(p$1, 5); p$2 = int53__lean_int_add(p$2, 5);` PBO writes `v3 = v7 + 3; v4 = v6 + 4`.

Both passes run on every function in `JsTerm/Print/Share.lean`, after the loop unrolling. The loops stay `while (true)` loops using `return` and labels, with no recursion, so the stack doesn't grow.

**New snapshot** `Tests/SnapshotsMy/AddChainMutual.lean` covers three mutual pairs:
- fields swapped each step, which folds to `p = p + 5`;
- fields not swapped, where each new value depends on the other variable. This one checks that the second assignment doesn't read a variable the first has just changed; it is still folded correctly to `p$2 + 4n` / `p$1 + 6n`.
- literals of mixed sign, which `faithful` combines (`p$1 - 4n`) and `pbo` deliberately leaves alone.

**Checks**
- `scripts/leanscript-snapshots.sh`: all 338 node check outputs report 0 failures (336 existing plus the 2 new ones). The script still exits non-zero for the same reasons as before: the known "literal too big" cases and the intentional `mypanic` test.
- No other existing snapshot changed.
- `lake build JsTerm tests leanscript` succeeds, and `lake exe tests` passes 76/76.
- The `Term` optimizer and its proofs are unchanged.
- No `sorry` was added. These are code-generation passes checked by the differential tests, not Lean theorems, so I added nothing to the Properties table.

All work is committed.

# Summary of changes for run 38c147f6-2a99-423b-8dc8-3be65e844e1a
The JS for `Tests/SnapshotsPBOPure/CaptureDerefRegression01.lean` now has the same structure as the purescript-backend-optimizer output in `legacy-backend/CaptureDerefRegression01.js`, and is a little shorter.

**`testEven` / `testOdd` now (pbo preset):**
```js
export const testEven = (n, b) => {
  let p$1 = b._1; let p$2 = b._2; let j$3 = n;
  while (true) {
    if (j$3 === 0) { return { _1: p$1, _2: p$2 }; }
    j$3--;
    const x$4 = int53__lean_int_add(p$2, 1);
    const x$5 = int53__lean_int_add(p$1, 2);
    if (j$3 === 0) { return { _1: x$4, _2: x$5 }; }
    j$3--;
    p$1 = int53__lean_int_add(x$5, 3);
    p$2 = int53__lean_int_add(x$4, 4);
  }
};
export const testOdd = (n, b) => {
  if (n === 0) { return b; }
  return testEven(n - 1, { _1: int53__lean_int_add(b._2, 3), _2: int53__lean_int_add(b._1, 4) });
};
```
- **Before:** one shared loop tested and set a `Bool` tag on every step.
- **Now:** PBO's shape — the loop runs two steps per iteration with no tag, and `testOdd` does one step and then calls `testEven`.
- **Compared with PBO:** there is no `tag: 0` field, and `testOdd` returns `b` itself when `n` is 0.
- The loop uses constant stack space.
- `int53__lean_int_add` is still there because of how the pbo preset handles `Int`; the faithful preset writes `+`.

**Where the changes went.** None of this could go in the `Term → Term` optimizer. The tag, the loop counter and the loop variables are JavaScript-level mutable variables, which `Term` doesn't have. And a `Term` can't refer to another top-level function, which the new `testOdd` does. So everything is in `JsTerm → JsTerm`, and the optimizer and its proofs are unchanged. There are also no new Lean theorems. These are code-generation changes, checked by the differential tests below.

1. **Unrolling** (new file `JsTerm/Lower/Unroll.lean`): a loop over a `Bool` tag runs two iterations per step, with a test of the counter in the middle, and the tag is dropped. The last assignments of the first half are postponed, so the second half reads the new values directly. A base case that reads the tag gets the value the tag would have at that point.
2. **Peeling:** the other function of the pair runs one iteration without any mutable variables, then calls the first function. Its arguments are rebuilt from how the first function initialises its loop. A record literal built from all the fields of a destructured record of plain values is replaced by that record (hence `return b;`).
3. **Where they run:** both happen in `pairTagLoops` (`JsTerm/Print/Share.lean`), before the existing shared-worker pass. They are all-or-nothing: on any shape they don't recognise, the old output is kept.
4. **Grammar:** three new constructors — `JsBlock.tick` (a mid-step `if (j === 0) {…} j--;`), `JsBlock.natCase` (`if (n === 0) {…}`, then `n - 1`) and `JsExpr.global` (a call to another function in the module). All traversals and the printer handle them.
5. **Printer** (`JsTerm/Syntax/Vars/Occs.lean`): a constant can now be written at its use even when another constant that is also inlined sits in between, as long as evaluation order is kept. My first version of this reordered an array read past an in-place update, and `ReadBeforeWrite` test5 caught it; I fixed that before regenerating.

**Rendering:** loops are `while (true)` with `return` and no recursion, so there is no stack growth. No labelled blocks were needed for these functions; the existing `countdown`/join rendering still uses labels where needed.

**Checks**
- All snapshots regenerated with `scripts/leanscript-snapshots.sh`: all 336 node check outputs report 0 failures. The script's non-zero exit is the same as before: the known "literal too big" cases and the intentional `mypanic` test.
- Other snapshots that changed:
  - `Tests/SnapshotsMy/MutualTail`: `test1` is now a tag-free loop, and `test2` is `if (a === 0) return false; return test1(a - 1);`.
  - About 16 snapshot files in `SnapshotsMy`/`SnapshotsPBOPure` just lose a temporary `const`.
- `lake build JsTerm tests leanscript` succeeds with no warnings, and `lake exe tests` passes 76/76.
- No `sorry` was added, and nothing was added to the Properties table because there are no new theorems.
- All work is committed.

# Summary of changes for run 5d9def2c-bb05-47dc-9575-1705020fb0d4
The JS generated for `Tests/SnapshotsPBOPure/CaptureDerefRegression01.lean` is now as good as the purescript-backend-optimizer output in `legacy-backend/CaptureDerefRegression01.js`, and a little better in places. The two changes are below. Neither one could go in the `Term → Term` optimizer, so its proofs are unchanged.

**What was still worse than PBO at the start**
- `testEven` and `testOdd` each carried their pair argument as a record in one loop variable. Every iteration built a new `{_1, _2}` and took it apart again, so it allocated once per step. PBO keeps the two fields in separate variables.
- `testOdd` repeated the whole loop. PBO writes it as a short wrapper around the other function.

**1. Loop variables that hold a record are split into one variable per field (`Term → JsTerm`, `JsTerm/Lower/FromTerm.lean`, `Basic.lean`, `Tail.lean`)**
- This applies when the record's fields are all plain values (numbers, booleans, strings, enums) and the loop body only takes the record apart. The body passes the next record as a literal, and those fields are assigned straight to the variables.
- The whole record is rebuilt only where the loop returns it.
- If the body uses the record whole anywhere, this is not done: that would build a record on every step, so the loop is converted exactly as before.
- It can't go in the Term optimizer because it is about mutable JS loop variables, which Term doesn't have.

**2. Functions that differ only in their first starting value share one private worker (`JsTerm → JsTerm`, new `JsTerm/Print/Share.lean`)**
- `testEven` and `testOdd` compile to the same loop apart from the starting `Bool` tag.
- The tool now writes the loop once, as `const testEven$shared = (tag, n, b) => …`, then `export const testEven = (n, b) => testEven$shared(true, n, b);` and the same for `testOdd` with `false`.
- Two functions share a worker only when the printed JS of their workers is exactly the same text, so each still runs its own code.
- It can't go in the Term phase or the conversion because a Term can't refer to another top-level definition, and each function is converted on its own.
- To support this, `JsFun` has two new fields, `exported` and `delegate?`, and the printer handles both.

**How the output now compares with PBO**
- `test1`, `test2`: identical.
- `test3`: both arguments taken at once instead of curried.
- `test4`, `test5`: no `tag: 0` field.
- `testEven`, `testOdd`: one loop with no allocation per step and constant stack use, plus two one-line wrappers. PBO has one loop and one wrapper. The loop starts with `let p$2 = b._1; let p$3 = b._2;` and its steps only assign numbers.
- Remaining differences:
  - PBO handles two steps per iteration and so needs no tag; we still test and set a `Bool` tag each step.
  - The `pbo` preset calls `int53__lean_int_add` where PBO writes `+`. That is the preset's overflow-checked `Int`, not something I changed; the `faithful` preset writes `+` on BigInts.

**Checks**
- All snapshots were regenerated with `scripts/leanscript-snapshots.sh`, and all 336 node checks pass with 0 failures.
- Only two snapshots changed: this one and `Tests/SnapshotsMy/MutualTail`, where `test1` and `test2` now share a worker in the same way.
- `lake build JsTerm tests` succeeds and `lake exe tests` passes 76/76.
- No `sorry` was added. These are code-generation changes checked by the differential tests, with no new Lean theorems, so I added no entries to the Properties table.
- All work is committed.

# Summary of changes for run 3c48ab1a-45eb-45f5-aa51-e42c6592d447
I rewrote how `Tests/SnapshotsPBOPure/CaptureDerefRegression01.lean` is compiled. For every test except `testOdd`, the JavaScript is now as short as the purescript-backend-optimizer output in `legacy-backend/CaptureDerefRegression01.js`, or shorter. `testOdd` is still a full loop, while the legacy backend gives it a 5-line wrapper. Both presets pass all 60 differential checks against Lean.

**What was wrong at the start**
- `test4` and `test5` were not translated at all, because private types gave an "invalid scope" error.
- `testEven` and `testOdd`, which call each other, were refused. Once the refusal was removed, a hidden miscompile showed up: the call to the other function was treated as a call to itself.
- The output kept temporary constants that are read only once, such as `const k$2 = …; return {_1: k$2, …}` and `const x$6 = false; p$1 = x$6;`.

**Changes, in pipeline order**
1. **Lean → Term:** private declaration names are cleaned up, which fixes the scope error. Mutual recursion on a `Nat` (like `testEven`/`testOdd`) becomes one `nat_rec` whose answer takes a tag saying which function is running (a `Bool` for two functions). This also fixes the miscompile.
2. **Term → JsTerm:** when a `nat_rec` answers a function that is applied at once and only calls itself in tail position, it becomes a countdown loop, `let p = …; let j = n; while (true) { if (j === 0) … j--; … }`. So these functions no longer need stack space for each step. Loop variables that hold arrays can now be updated in place: the initial value is copied only if something else still uses it. Without this, `LocalFnInPlace` `test5`/`test6` copied the array on every step, and the `lake exe tests` check "test5 updates in place" failed. They now use `push_mutable` in the loop.
3. **Printing:** a constant read exactly once is written at its use, but only when that cannot change behaviour: not inside a loop or a closure, and not moved past any side effect. While doing this I found and fixed a bug where an array read was moved past an in-place update of the same array (it broke `Tests/SnapshotsMy/ReadBeforeWrite`). Now only constants, literals, closures and fresh records or arrays can be moved past other code.

I did not put the loop and ownership work in the Term optimizer as you preferred, because it depends on JavaScript-level facts (loops, mutable variables, in-place updates). The Term optimizer and its proofs are unchanged.

**Result compared with the legacy backend**
- `test1`, `test2`: identical.
- `test3`: we produce `(v, p1) => …` with both arguments at once; the legacy backend produces the curried `(v0) => (v1) => …`.
- `test4`, `test5`: `(v) => ({ _1: (x) => …, _2: (x) => … })`, the same as the legacy backend but without the `tag: 0` field.
- `testEven`, `testOdd`: each is a while loop with a `Bool` tag, which is linear time and uses constant stack. The legacy backend instead specialises two steps per iteration and keeps the fields in separate variables. We still destructure the record in each branch, so this part is close to the legacy output but not identical.
- The `pbo` preset calls `int53__lean_int_add` where the legacy backend writes `+`, because of how that preset handles `Int`; the `faithful` preset writes `f + 1n`.

**Verification**
- All snapshots were regenerated with `scripts/leanscript-snapshots.sh`. All 336 node check outputs report 0 failures. The script still exits non-zero, as before, because of the known "literal too big" cases and the intended `mypanic` test.
- `lake build leanscript` succeeds, and `lake exe tests` passes 76/76.
- A plain `lake build` of the default targets fails in `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That file is unchanged since the initial commit, so this failure was already there before this session.

All work is committed. The main files changed are `LeanScript/GenElab/Cache.lean`, `LeanScript/TermElab/ToTerm/Expr/Cases.lean`, `LeanScriptCli/Main.lean`, `LeanScriptCli/Check.lean`, `JsTerm/Lower/FromTerm.lean`, `JsTerm/Syntax/Vars/Occs.lean`, `JsTerm/Print/Mini/Block.lean` and the JsTerm loop support files.

# Summary of changes for run 842d423c-714b-4752-b48b-f54cc64bb8dc
The JS for `BranchSpecialization01` is now shorter than the purescript-backend-optimizer output. PBO's `instBEqTestEnum$beq` is a four-branch `if` chain; ours is a single comparison:
```js
export const instBEqTestEnum$beq = (x, y) => x === y;
export const test1 = (a) => a === 2;
export const test2 = (a) => a === 2;
```
The pbo and faithful presets now give the same output, and neither uses `BigInt`.

**Why the old output was big.** Lean compiles `BEq` on an enum as `Nat.decEq (toCtorIdx x) (toCtorIdx y)`. `toCtorIdx` became a join point fed by a case analysis over every constructor (`case e of cᵢ => jump j i`). On top of that, closure wrappers (`const k = x => …; const y = k(a); return y`) were left around the tail calls.

**What changed at each stage:**

1. **`Term → Term` optimizer (proved).**
   - `Term.subst` now reduces a case analysis on an enum literal.
   - It also collapses a join point once its main part becomes a jump; this only happens when the argument is cheap or used at most once.
   - New rewrite `Term.openTailCall?`: `val k := fun x => body; let y := k a; ret y` becomes `body[x:=a]`. It runs inside `Term.retLetV`.
   - Proved that these rewrites never change the result of eval: `Term.subst_eval` (re-proved for the extended substitution) and `Term.openTailCall?_eval`. The matching call-count lemmas are proved too; the `numCalls_subst` lemmas now state `≤` instead of `=`, because these rewrites can remove calls.
   - So `Term.optimize_eval` still holds. Both eval theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

2. **`Term → JsTerm` conversion (not proved; the JS side has no formal semantics in this project).**
   - Recognizing `toCtorIdx` couldn't be done in the Term phase: the Term grammar has no enum-to-Nat primitive, and adding one would touch the whole proved codebase. So it lives in the conversion.
   - `cBranch` recognizes the pattern `join j (x:Nat) := body; case e of cᵢ => jump j i` and binds `x` as a view of the enum's index, with no join. There are two new `JsExpr` constructors: `enumIndex` (printed as `e`, `e±k` or `BigInt(…)`) and `enumEq` (printed as `a === b`).
   - In `cNeu`, `Nat.decEq`/`Nat.beq` on two such indices becomes `enumEq`. Against an out-of-range literal it becomes `false`.

3. **`JsTerm` optimizer:** unchanged.

**Verification:**
- The listed targets build, and `lake exe tests` passes 76/76.
- No `sorry` was added.
- All 179 snapshots were regenerated and every node check passed. `leanscript` exited non-zero on three `PrimOp*Configurable` files, but those errors are expected: they are "literal too big" refusals for the pbo preset.
- Other snapshots changed only for the better: the `k$…` wrapper closures are gone from `DefaultRulesSemigroup02`, `CaseLeafTco`, `RecData`, `LocalFnInPlace`, `ArrayInPlace` and `InlineClosures`. In total that is 861 lines added and 985 removed.
- Regenerated snapshots are committed.

**Remaining differences from PBO:** only style. We emit one `export const` per definition plus JSDoc comments, where PBO uses a different export layout.

# Summary of changes for run 49637ffa-a26f-4355-9e3a-c74256372169
I made no code changes. The JavaScript generated for `Tests/SnapshotsPBOPure/BackendSemantics02.lean` already matches purescript-backend-optimizer's `BackendSemantics02.js`: both come down to a single constant, 97. So none of the three pipeline stages you listed needed a new optimisation.

**The input:** `def test1 : Nat := 'a'.toNat`

**PBO's output:**
```js
const test1 = 97;
export { test1 };
```

**What each stage does:**
- **Lean code → `Term`:** elaboration already reduces `'a'.toNat` to the literal `ret 97` (see `BackendSemantics02-Term-unoptimized.txt`).
- **`Term` → optimised `Term`:** there is nothing left to simplify, so `BackendSemantics02-Term-optimized.txt` is the same as the unoptimised file.
- **Converting to `JsTerm`, optimising and printing:** the literal comes out as a plain constant, not a zero-argument function.
  - With the `pbo` preset, `Nat` is a JS number: `export const test1 = 97;` (`BackendSemantics02-pbo.js`).
  - With the `faithful` preset, `Nat` is a BigInt: `export const test1 = 97n;` (`BackendSemantics02-faithful.js`). That `n` is a deliberate choice of how numbers are represented, not a missed optimisation.

**Remaining differences from PBO, all style only:**
- The constant is exported where it is defined (`export const`), instead of in a closing `export { test1 }`.
- There is a JSDoc comment giving the type, which PBO's output doesn't have.

**Checks I ran:**
- I rebuilt the `leanscript` tool (`lake build leanscript` succeeded).
- I regenerated this file's outputs with `leanscript --quiet --skip-empty --check`. The new files are identical to the committed ones (`git status` shows no changes).
- The node checks pass 1 of 1 for both presets.

There was nothing to commit, and no Properties-table entries changed. I listed no build targets because I edited no Lean files; the only build was the `leanscript` rebuild above.

# Summary of changes for run 466f136c-66dc-441d-b487-7868036304be
The JavaScript for `Tests/SnapshotsPBOPure/BackendSemantics01.lean` already gave the same four values as purescript-backend-optimizer's `BackendSemantics01.js`. I made one printing change that makes one line more readable than PBO's.

**What each stage does with this file**
- **Lean code → `Term`:** elaboration already turns each definition into a literal: `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'`.
- **`Term` → optimised `Term`:** there is nothing left to simplify, so `BackendSemantics01-Term-optimized.txt` is the same as the unoptimised file. This is why none of your three preferred stages needed a new optimisation for this file.
- **Converting to `JsTerm`, optimising and printing:** each literal becomes a plain constant.

**The change**
- **Before:** `test3` was written as the raw character U+FFFF between quotes. That character is invisible in editors and diffs, and it is a Unicode "noncharacter". PBO's file has the same raw character.
- **After:** it is written as `"\uFFFF"`.
- **Where:** the string-literal printer, `LanguageJavascriptCommon/StringLit.lean`, in the last step that turns the syntax tree into text. It can't go in an earlier stage, because it only changes how a string is spelled, not its value.
- **Which characters are now escaped:**
  - C1 control characters (U+0080–U+009F);
  - U+2028 and U+2029, which weren't allowed in string literals before ES2019;
  - zero-width and bidirectional formatting characters (U+200B–200F, U+202A–202E, U+2066–2069);
  - the byte-order mark U+FEFF;
  - noncharacters: U+FDD0–FDEF and the last two code points of every plane, e.g. U+FFFF.
- **Format:** characters up to U+FFFF are written as `\uXXXX`; those above it as `\u{…}`.
- **Tests:** I added `#guard` checks that pin these spellings and confirm the escaped text decodes back to the original string.

**Output now (both presets, doc comments left out):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "\uFFFF";
export const test4 = "\x00";
```
**Remaining differences from PBO, all style only:**
- Each constant is exported where it is defined, instead of in one closing `export { … }` list.
- `"\x00"` is a shorter spelling of PBO's `"\u0000"`; both give the same string.
- Each constant has a JSDoc `@type` comment, which PBO's output doesn't have.

**Checks**
- **Builds:** `lake build leanscript LanguageJavascriptMini JsTerm TermTests TyTests tests` succeeds, and `lake exe tests` passes 76/76.
- **Snapshots:** I regenerated every snapshot with `scripts/leanscript-snapshots.sh`. Only the two `BackendSemantics01-{pbo,faithful}.js` files changed. No node check failed; `BackendSemantics01` passes 4/4 at both presets.
  - The script still exits with status 1 because of the known `mypanic` panics in the test inputs.
- **Existing problem, not changed:** a plain `lake build` of the default targets fails because `LeanScript/Term/Syntax/UsageAlgebra.lean` imports Mathlib, which this project doesn't depend on. This was already the case before my change. Nothing else imports that file, so none of the targets above are affected.

The change is committed. No Properties-table entries were affected.

# Summary of changes for run e9ca2fb9-6607-4693-b486-d52307a3f196
I made no code changes. The JavaScript generated for `Tests/SnapshotsPBOPure/BackendSemantics01.lean` already matches purescript-backend-optimizer's `BackendSemantics01.js` in values and structure, so no stage of the pipeline needed a new optimisation.

**Checks I ran:** I rebuilt the `leanscript` tool (it built without errors) and regenerated this file's outputs with `leanscript --quiet --skip-empty --check`. The regenerated files are identical to the committed ones (`git status` shows no changes). The node checks pass 4 of 4 for both the `pbo` and `faithful` presets.

**What each stage does:**
- **Lean code → `Term`:** elaboration already turns all four definitions into literals: `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'` (see `BackendSemantics01-Term-unoptimized.txt`).
- **`Term` → optimised `Term`:** there is nothing left to simplify, so `BackendSemantics01-Term-optimized.txt` is the same as the unoptimised file.
- **Convert to `JsTerm`, optimise and print:** each literal comes out as a plain constant, not a zero-argument function.

**Current output, the same for both presets (doc comments left out):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "￿";
export const test4 = "\x00";
```

**How this differs from PBO's output, all in style only:**
- **Exports:** each constant is exported where it is defined (`export const`), instead of in one `export { test1, test2, test3, test4 }` at the end. The same names are exported.
- **Escape spelling:** `"\x00"` is a shorter way to write PBO's `"\u0000"`; both give the same string.
- **Comments:** each constant has a JSDoc comment with its `@type`, which PBO's output doesn't have.

There was nothing to commit, and no proofs or Properties-table entries changed. I listed no Lean targets below because no Lean files were edited; the only build was the `leanscript` rebuild described above.

# Summary of changes for run f5971781-903e-4130-95b6-03ec20ca0974
I made no code changes: the JavaScript this project generates for `Tests/SnapshotsPBOPure/BackendSemantics01.lean` already has the same values and structure as purescript-backend-optimizer's `BackendSemantics01.js`. The only differences are in style.

**Checks I ran:** I rebuilt the `leanscript` tool (it built without errors) and regenerated this file's outputs with `leanscript --quiet --skip-empty --check`. The regenerated files are identical to the committed ones (`git status` shows no changes). The node checks pass 4 of 4 for both the `pbo` and `faithful` presets.

**What each stage does:**
- **Lean code → `Term`:** elaboration already turns every definition into a literal. `Int32.maxValue - 1`, `Int32.minValue + 1`, the hand-built 0xFFFF `Char` and `Char.ofNat 0` become `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'` (see `BackendSemantics01-Term-unoptimized.txt`).
- **`Term` → optimised `Term`:** there is nothing left to optimise, so `BackendSemantics01-Term-optimized.txt` is the same as the unoptimised file.
- **Convert to `JsTerm`, optimise and print:** a definition with no parameters used to come out as a zero-argument function (`() => 2147483646`). An earlier session fixed this in the printing step (`JsTerm/Syntax/Basic.lean`, `JsTerm/Print/Mini.lean`). It couldn't go in one of the earlier stages you preferred, because neither `Term`, the conversion step nor `JsTerm` can tell a constant from a zero-argument function.

**Current output, the same for both presets (doc comments left out):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "￿";
export const test4 = "\x00";
```

**How this differs from PBO's output:**
- **Exports:** each constant is exported where it is defined (`export const`), instead of in one `export { test1, test2, test3, test4 }` at the end. The same names are exported.
- **Escape spelling:** `"\x00"` is a shorter way to write PBO's `"\u0000"`; both give the same string.
- **Comments:** each constant has a JSDoc comment giving its `@type`, which PBO's output doesn't have.

There was nothing to commit, and no proofs or Properties-table entries changed. I listed no Lean targets below because no Lean files were edited; the only build was the `leanscript` rebuild described above.

# Summary of changes for run 446048a4-c2d8-4c3a-96af-ad58638b3578
I made no code changes: the JavaScript output for `Tests/SnapshotsPBOPure/BackendSemantics01.lean` already matches purescript-backend-optimizer's `BackendSemantics01.js`, apart from style. An earlier run made the fix, and the current code still reproduces it.

**Checks I ran:** I rebuilt the tool (`lake build leanscript` succeeded) and regenerated this file's outputs with `leanscript --skip-empty --check`. The regenerated files are byte-identical to the committed ones (`git status` is clean), and the node checks pass 4/4 at both the `pbo` and `faithful` presets.

**What each stage does:**
- **Lean → `Term`:** elaboration already reduces every definition to a literal. `BackendSemantics01-Term-unoptimized.txt` is just `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'`.
- **`Term` → optimised `Term`:** there is nothing left to optimise; `BackendSemantics01-Term-optimized.txt` is the same as the unoptimised version.
- **Conversion, `JsTerm` optimisation and printing:** the one real gap was here, and it is already fixed. A definition with no parameters used to come out as a zero-argument function (`() => 2147483646`); it is now printed as a plain constant. That fix is in the final print step (`JsTerm/Syntax/Basic.lean`, `JsTerm/Print/Mini.lean`). It couldn't go in one of the earlier stages you preferred, because neither `Term`, the conversion step nor the `JsTerm` grammar can tell a constant apart from a zero-argument function.

**Current output, the same at both presets (doc comments omitted):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "￿";
export const test4 = "\x00";
```
This has the same four values as PBO's output. The differences are cosmetic:
- **Exports:** they are written inline instead of in a closing `export { … }` list.
- **Escape spelling:** `"\x00"` is a shorter way to write PBO's `"\u0000"`; both are the same string.
- **Doc comments:** each constant has an `@type` comment, which PBO's output doesn't have.

Since nothing changed, there was nothing to commit, and no proofs or Properties-table entries were affected.

# Summary of changes for run 367a5680-d978-4bd7-964a-413b4ea61f13
I didn't need to change anything. `BackendSemantics01` already compiles to the same JavaScript as purescript-backend-optimizer, apart from how exports are written. The fix was made in the previous run, and the current code reproduces it exactly.

**Checks I ran this session:** I rebuilt the `leanscript` tool (`lake build leanscript` succeeded) and regenerated this file's outputs with `leanscript --skip-empty --check`. The regenerated files are byte-identical to the committed ones (`git status` stays clean). The node checks pass 4/4 at both the `pbo` and `faithful` presets.

**Your pipeline, stage by stage:**
- **Lean code → `Term`:** elaboration already folds everything to constants. `BackendSemantics01-Term-unoptimized.txt` is just `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'`. `Int32.maxValue - 1`, `Int32.minValue + 1`, the hand-built `Char` for 0xFFFF and `Char.ofNat 0` all reduce to literals.
- **`Term` → optimised `Term`:** nothing is left to do here. `BackendSemantics01-Term-optimized.txt` is identical to the unoptimised version.
- **Conversion, `JsTerm` optimisation and printing:** the only gap was here. A definition with no parameters used to come out as a zero-argument function, e.g. `export const test1 = () => 2147483646;`. The previous run changed the top-level print step (`JsTerm/Syntax/Basic.lean`, `JsTerm/Print/Mini.lean`) so that a definition whose type isn't a function is written as a plain constant. It had to go there because neither `Term`, the conversion nor the `JsTerm` grammar can tell a constant apart from a zero-argument function.

**Output now, the same at both presets (doc comments omitted):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "￿";
export const test4 = "\x00";
```
PBO's `BackendSemantics01.js` has the same four values. The only differences are cosmetic:
- **Export style:** exports are written inline (`export const`) instead of in a closing `export { test1, test2, test3, test4 }` list. Both export the same names.
- **Escape spelling:** `"\x00"` is a shorter way to write PBO's `"\u0000"`. Both give the same string.
- **Doc comments:** each constant has a comment giving its `@type`, which PBO's output doesn't have.

Since there was no code change, there was nothing to commit, and no proofs or Properties-table entries were affected.

# Summary of changes for run 60036a24-2ad5-4987-a0a3-13e7bef71b58
`BackendSemantics01` now compiles to the same JavaScript as purescript-backend-optimizer, apart from export style.

**What was wrong.** The `Term` side was already fine: the unoptimised and optimised terms are both just `ret 2147483646`, `ret -2147483647`, `ret '\uFFFF'` and `ret '\x00'`. There were two real gaps and one tooling problem:
1. **Definitions without parameters became zero-argument functions**, e.g. `export const test1 = () => 2147483646;`. PBO writes `const test1 = 2147483646;`.
2. **`test1` and `test2` (`Int32`) got no node checks**, because the check generator didn't accept fixed-width integer types.
3. **The snapshot script deleted this file's outputs**, because `--functions-only` skips files that contain only constants.

**Output now (both presets):**
```js
export const test1 = 2147483646;
export const test2 = -2147483647;
export const test3 = "￿";
export const test4 = "\x00";
```
The remaining differences are style only. The exports are written inline instead of in a closing `export { … }` list. `"\x00"` is a shorter spelling of PBO's `"\u0000"`; both give the same string.

**Changes**
- **Constants** (`JsTerm/Syntax/Basic.lean`, `JsTerm/Print/Mini.lean`): a definition whose type isn't a function is now printed as `export const x = value;`, with `@type` in its doc comment. If the body is more than a single `return e`, it is wrapped in an arrow that is called immediately, `export const x = (() => { … })();`.
  - This lives in the print step, because none of `Term`, the conversion or the `JsTerm` grammar can express "constant vs zero-argument function"; only the top-level declaration form changes.
  - The value is now computed once, when the module loads, which is how Lean initialises closed constants. Since the translated programs are pure and total, the value doesn't change.
  - Caveat: the constant is shared, so it must not be passed to a version of a function that owns its parameter and may update it in place (the `$$mut` versions). The doc comment says this.
- **Checks** (`LeanScriptCli/Check.lean`):
  - Constants are read (`M.test1`) rather than called.
  - `UInt8`–`UInt64` and `Int8`–`Int64` are now sample types. Below 64 bits the samples include the range edges, to exercise wrapping.
  - At the `pbo` preset, where 64-bit integers are plain numbers, a 64-bit expected answer beyond ±(2^53−1) is skipped. The runtime deliberately throws there ("use the bigint representation"), so there is nothing to compare.
- **Snapshot script:** a new `leanscript --skip-empty` option skips a file only if it has no translatable definition at all. `scripts/leanscript-snapshots.sh` now uses it, so files with only constants (`BackendSemantics01`/`02`, the `PrimOp…` files and others) now get outputs and checks.
- **New snapshot** `Tests/SnapshotsMy/TopConstants.lean` covers `Int32`/`UInt8` constants (including a wrapped one), a pair, an array, a list, and functions over every fixed-width type.

**Checks run**
- Rebuilt `leanscript` and regenerated all snapshots. All node checks pass, and the `pbo` checks went from 3297 to 5549. `BackendSemantics01` passes 4/4 at both presets; `TopConstants` passes 76/76.
- `lake build JsTerm tests` succeeds, and `lake exe tests` passes 76/76. No proofs or theorems changed, so I added nothing to the Properties table.
- The snapshot script still exits non-zero because of the "literal too big" errors at the `pbo` preset. These already existed for `PrimOpInt02Configurable` and `PrimOpInt03Configurable`. `PrimOpIntBit02Configurable` now shows the same error too, because it is translated for the first time.

**Separate issues I noticed and didn't fix:**
- `InlineReferenceRecordUpdate.fn_prime` now comes out as an immediately-called arrow. That exposes a missed `Term` inlining: a local zero-argument closure that is only copied and then called is not inlined.
- A constant built from a `for` loop over `push` (e.g. `squares`) fails to translate with a type mismatch.
- `Int32` addition calls a runtime function rather than being written inline.

# Summary of changes for run c4dce21e-c8f8-45f3-bbd6-16acd18393db
I didn't need to change anything. `AssocStringAppend` already compiles to JavaScript that matches the legacy backend at both presets, because the fix was made in the previous run.

**Output now, the same at both presets:**
```
export const test1 = (x) => "ab" + x + x + x + x + "cd";
export const test2 = (x) => "ab" + x + x + x + x + "cd";
export const test3 = (x) => "ab" + x + x + x + x + "cde" + x + x + x + x + "fg";
```
These function bodies are character-for-character the same as `legacy-backend/AssocStringAppend.js`. The only difference is style: the exports are written inline (`export const`) rather than in a closing `export { … }` list, which does the same thing.

**Why the output matches.** Lean turns each `testN` into nested `String.append` calls; `AssocStringAppend-Term-unoptimized.txt` shows `"a"`, `"b"`, `"c"` and `"d"` still separate. The fix is entirely in the `Term → Term` phase, which is the phase you prefer. The `StrApp.normNeu` step in `LeanScript/Term/Optimize/StringAppend.lean` runs as part of `Term.optimize` and does three things:
- drops empty `""` literals;
- merges neighbouring literals, so `"a" ++ "b"` becomes `"ab"`;
- regroups the whole chain from the left, `((x₁ ++ x₂) ++ …) ++ xₙ`.

JavaScript's `+` also groups from the left, so the printer needs no parentheses and none of the later phases had to change. `AssocStringAppend-Term-optimized.txt` shows the regrouped chain.

**Checks I ran this session:**
- **Snapshot:** I rebuilt the `leanscript` tool and regenerated the snapshot from the current code. The new files are byte-identical to the committed ones.
- **JavaScript tests:** the node checks pass, 15/15 for each preset.
- **Proofs:** `LeanScript.Term.Optimize.StringAppend` and `TermTests.Optimize.AssocStringAppendTest` build, with no `sorry`.
  - `StrApp.normNeu_eval` proves the step never changes a value, so the theorem that the whole optimiser preserves results (`Term.optimize_eval`) still holds. It uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
  - `testN_optimized_run` proves that for every `x`, each optimised `testN` computes the legacy body. For `test3` that is `"ab" ++ x ++ x ++ x ++ x ++ "cde" ++ x ++ x ++ x ++ x ++ "fg"`.
  - `testN_optimized_pretty` checks that the optimised term has exactly this form. These use `native_decide`, so they also depend on Lean's compiler.

Both results were already marked proved in the Properties table, and I left the table as it was. There were no changes to commit.

# Summary of changes for run 2a0f49c6-8076-414f-9c35-d5cfc587645e
The JavaScript for `AssocStringAppend` now matches the legacy backend exactly, at both presets. The fix is entirely in the `Term → Term` optimiser; the later phases didn't need changes.

**What was wrong.** Lean elaborates each `testN` into nested `String.append` calls (see `AssocStringAppend-Term-unoptimized.txt`), and the optimiser left them as they were. JavaScript's `+` groups from the left, so every append nested on the right got its own parentheses, and literals like `"a" ++ "b"` stayed separate:
`"a" + ("b" + (x + (x + (x + (x + "c"))))) + "d"`.

**What I changed**
- **New optimiser step** (`LeanScript/Term/Optimize/StringAppend.lean`). It takes a chain of `String.append`s and:
  - drops empty `""` literals;
  - merges neighbouring literals into one;
  - regroups the chain from the left, `((x₁ ++ x₂) ++ …) ++ xₙ`. This is also the grouping Lean's `String.append` works best with, since it appends in place onto its left operand.
  - `String.push s 'c'` with a literal character counts as `s ++ "c"`, so it joins the chain.
- **Hooked in** through `Neu.normAppend` in `Append.lean`, so it runs inside the existing `Term.appendWalk`.
- **Proved:** the step never changes a value (`StrApp.normNeu_eval`), so the theorem that the whole optimiser preserves results (`Term.optimize_eval`) still holds. Both use only the standard axioms. The theorem that the optimiser adds no calls is unaffected.
- `String.Internal.append` is left alone, because Lean treats it as opaque and nothing can be proved about it.

**Result**
```
export const test1 = (x) => "ab" + x + x + x + x + "cd";
export const test2 = (x) => "ab" + x + x + x + x + "cd";
export const test3 = (x) => "ab" + x + x + x + x + "cde" + x + x + x + x + "fg";
```
- **`PrimOpString03`** also changed. Its three tests all became `"ab" + a + "cd"`, which is exactly its legacy output.
- **`StringWalk`:** only the optimised `Term` changed (`push` became an append); its JavaScript is the same.

**Tests added**
- `Tests/TermTests/Optimize/AssocStringAppendTest.lean`:
  - For every `x`, each optimised `testN` computes the legacy body, e.g. `"ab" ++ x ++ x ++ x ++ x ++ "cde" ++ x ++ x ++ x ++ x ++ "fg"`. These proofs use only the standard axioms.
  - The optimised term is exactly the left-grouped chain with merged literals. This is checked with `native_decide`, because the printer is compiled code, so it also depends on Lean's compiler.
- `Tests/SnapshotsMy/StringAppend.lean` covers edge cases: `"" ++ x`, `x ++ ""`, a closed part, two variables, a chain inside a call, `push`, and Unicode. Its node checks pass (77 per preset).

**Checks**
- The listed targets build with no `sorry`.
- `lake exe tests` passes 76/76.
- I regenerated all snapshots, and every node check passes. The snapshot script still exits non-zero because of the existing "literal too big" errors at the pbo preset.
- The docs in `Term/Optimize/Basic.lean` and `LeanScript/Term/README.md` are updated, and both results are in the Properties table as proved.

A plain `lake build` of the default targets fails at `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That file isn't imported by the rest of the project, and I didn't touch it.

# Summary of changes for run 5955a48e-7894-4519-b892-47ec6545df8d
**What I found.** `AssocNumberOps` wasn't being translated at all: all six functions failed, and the committed `.js` files contained only "not translated" errors. The cause was float literals such as `1.0`:
- The language's float type is `HashableFloat`, not `Float`, so the literal didn't type-check.
- The command-line tool then tried to reduce the float symbolically at compile time, which is far too slow.

The same bug also affected `CaseNumber`, `InlineReferencePrimOpNumber` and `PrimOpNumber02`.

**What I changed**
1. **Float literals now translate** (`TermElab/ToTerm/Expr.lean`, `LeanScriptCli/Frontend.lean`).
   - A closed `Float`/`Float32` value becomes a literal and is computed natively.
   - `NaN` and `-0.0` are refused with a clear error. The language's floats can't represent them, and silently turning them into `0.0` would change the program.
2. **New proved step in the `Term → Term` optimiser** (`Term/Optimize/FloatUnit.lean`, run inside `Term.arithWalk`).
   - `x * 1.0`, `1.0 * x`, `x / 1.0` and `x - 0.0` become `x`.
   - The facts behind it are proved from Lean's float model in the new file `HashableFloat/Identities.lean`. They hold bit for bit for every float, `NaN` and `-0.0` included.
   - `Term.optimize_eval` still holds, using only the standard axioms.
   - `x + 0.0` is not rewritten, because it gives `+0.0` when `x` is `-0.0`.
3. **Optional `--float-reassoc` flag** (`Term/Optimize/FloatReassoc.lean`). It regroups float chains from the left and folds neighbouring literals, as the legacy backend does. It is off by default, and the JavaScript header says when it was used.

**Output compared with the legacy backend**

| | default (same results as Lean) | `--float-reassoc` | legacy |
|---|---|---|---|
| test1 | `1 + (2 + x + x + x + x + 3) + 4` | `3 + x + x + x + x + 7` | same as `--float-reassoc` |
| test4 | `2 * x * x * x * x * 3 * 4` | `2 * x * x * x * x * 12` | same as `--float-reassoc` |
| test6 | `2 * (x * (x * (x * (x * 3)))) * 4 * (5 * x * x * x * x * 6) * 7` | `2 * x * x * x * x * 60 * x * x * x * x * 42` | same as `--float-reassoc` |

With `--float-reassoc` the output is exactly the legacy output. The default mode is not on par for sums: float addition isn't associative, so the legacy form computes something different from Lean. `Tests/TermTests/Optimize/AssocNumberOpsTest.lean` shows this:
- `test1` and the legacy body differ at `x = 3/7`.
- `--float-reassoc` changes the translated `test1`'s result at that input.

That is why regrouping isn't part of the proved optimiser. These checks, and the ones showing the exact optimised output, use `native_decide`, so they depend on Lean's compiler.

**Checks**
- The listed build targets build, with no `sorry`.
- `lake exe tests` passes 76/76.
- I regenerated all snapshots and every node check passes, including the new `Tests/SnapshotsMy/FloatUnit.lean` (55 checks per preset).
- The snapshot script still exits non-zero, because of the existing "literal too big" errors at the pbo preset.
- The Properties table and the READMEs are updated.

**Still open**
- In `PrimOpNumber02`, the closed comparisons such as `1.5 == 1.0` still can't be computed at compile time.
- Passing two files to one `leanscript --functions-only` call deleted the second file's outputs. The snapshot script runs one file at a time, so it isn't affected. I didn't investigate this.

# Summary of changes for run fdf39749-5b78-4d25-983f-6bcd472e7ec5
I added a new Lean file, `Tests/TermTests/Optimize/AssocIntOpsTest.lean`, that proves the `AssocIntOps` results for all six functions. It builds with no `sorry`, and it is committed.

**What is proved, for each `testN`** (the functions are copied from `Tests/SnapshotsPBOPure/AssocIntOps.lean`, translated to `Term` and optimised with `optimizeN 3`):
- **The optimised term computes the closed form for every `x`** (`testN_optimized_run`):
  - test1 and test2: `x * 4 + 10`
  - test3: `x * 8 + 28`
  - test4 and test5: `x ^ 4 * 24`
  - test6: `x ^ 8 * 5040`
  
  The proofs combine the existing theorem that the optimiser never changes a result (`Term.optimizeN_run`) with a proof about the Lean function itself (`testN_eq`). They use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **The optimised term is exactly the two-operation term** (`testN_optimized_pretty`). For example, test6 becomes `ret lean_int_mul(lean_int_pow(x2, 8), 5040)`, which matches `AssocIntOps-Term-optimized.txt`.
- **Operation counts** (`numIntOps_optimized`, `numIntOps_unoptimized`): every optimised term has 2 `lean_int_…` operations. The unoptimised terms have 7 (test1, test2, test4, test5) or 14 (test3, test6).

**Caveats:**
- **Two statements depend on Lean's compiler.** The printed form and the operation counts are checked with `native_decide`, because the printer is compiled code that Lean's proof checker cannot run. So those theorems are trusted only as far as the compiler is. The closed-form theorems don't have this dependency.
- **Operation count is at the `Term` level.** It counts operations in the printed `Term`, not in the final JavaScript.
- **Legacy numbers are my own count.** In `legacy-backend/AssocIntOps.js`, the legacy backend writes 5 or 10 `+`/`*` operations, each followed by `| 0`. That count is from reading the file, not proved in Lean.

**Correction:** my previous reply said the legacy output had "9 ops" and "19 ops". The correct counts are 5 and 10 arithmetic operations, each with its own `| 0`.

**Checks:** `lake build TermTests.Optimize.AssocIntOpsTest` succeeds. I checked the axioms with `#print axioms` on one theorem of each kind (a closed form, a printed form and the operation counts). Both results are in the Properties table as proved.

# Summary of changes for run 6e55788b-8aed-4d9a-b403-2ad68c80aef4
I made no changes in this session. The work you asked for was already done in the previous run, and I checked that it still builds and passes.

**What the analysis shows.** Lean elaborates each `test` in `AssocIntOps.lean` into a nested chain of `lean_int_add`/`lean_int_mul` calls (see `AssocIntOps-Term-unoptimized.txt`). The `Term → Term` optimiser pass `Term.arithWalk` normalises these chains, so no change was needed in the later phases (`Term → JsTerm`, `JsTerm → JsTerm`):
- it folds all the literals into one;
- in a sum, it counts the copies of `x` (`x + … + x` becomes `x * k`);
- in a product of `Int`/`Nat`, three or more copies of `x` become one power (`x ^ k`).

This is in `LeanScript/Term/Optimize/Arith.lean`, `ArithBasic.lean` and `ArithPow.lean`.

**Current output compared with the legacy backend:**
| | faithful (`BigInt`) | pbo (`number`) | legacy |
|---|---|---|---|
| test1/test2 | `x * 4n + 10n` | `int53__lean_int_add(int53__lean_int_mul(x, 4), 10)` | 9 ops, each with `\|0` |
| test3 | `x * 8n + 28n` | same shape (8, 28) | 19 ops |
| test4/test5 | `x ** 4n * 24n` | `int53__lean_int_mul(int53__uint53__lean_int_pow(x, 4), 24)` | 9 ops |
| test6 | `x ** 8n * 5040n` | same shape (8, 5040) | 19 ops |

The faithful output is shorter than the legacy one in all six tests. The pbo output uses 2 operations instead of 9–19. It calls functions in `runtime.js` instead of writing `\|0` inline, on purpose: `\|0` wraps to 32 bits, which would give wrong results for Lean's `Int`, while the runtime functions check for overflow.

**Checks I ran:**
- `lake build leanscript tests` succeeds.
- Regenerating the `AssocIntOps` snapshots with `leanscript --functions-only --check` gives files identical to the committed ones (`git status` is clean).
- The node checks pass: 30/30 at the pbo preset and 30/30 at faithful.
- `lake exe tests` passes 76/76.
- `Term.arithWalk_eval` (the pass never changes a term's value) and `Term.optimize_eval` build without `sorry`. They use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The Properties table is up to date.

**Limitations (not needed for `AssocIntOps`):**
- In a sum, only repeated variables are counted: `x ** 3n + x ** 3n` is not combined into `x ** 3n * 2n`.
- `(x ^ 2) ^ 3` is not folded into `x ^ 6`.
- Subtraction is not part of the chains.

# Summary of changes for run d9b4267f-a48b-4ca3-a609-3f306145da48
The JavaScript for `AssocIntOps.lean` is now shorter than the legacy-backend output in all six tests, at both presets.

**What I found.** An earlier run had already added `Term.arithWalk`, which folds the literals and counts copies of `x` in sums. That gave `test1`–`test3` = `x * 4n + 10n` / `x * 8n + 28n`, against 9–19 chained operations in the legacy output. The products were still one multiplication per factor: `test6` was `x * x * x * x * x * x * x * x * 5040n`.

**What I changed.** The main change is in the `Term → Term` phase.
- **Optimiser (`Term.arithWalk`).** In a product of `Int`s or `Nat`s, three or more copies of an unknown now become one power: `x`, `x ^ k₁`, … turn into `x ^ (1 + k₁ + …)`. An `x ^ k` already there counts as `k` copies, so nested chains combine correctly. `x * x` is left alone, and fixed-width types are unchanged because they have no power operation.
  - The new code is in `LeanScript/Term/Optimize/ArithPow.lean` (`ArithOp.groupPow`).
  - `Arith.lean` was split, with its first half moved to `ArithBasic.lean`.
  - **Proved:** `Term.arithWalk_eval` (value unchanged in every environment) still holds, and so do `Term.optimize_eval` and `Term.numCalls_optimize`. No `sorry`; only the standard axioms.
- **New operation `lean_int_pow`** for `Int.pow`, which isn't `@[extern]` in Lean. It is added to the catalogue with an evaluator, so user code `x ^ n` on `Int` now uses it too. I regenerated `ExternTable.lean` and the `JsTerm/Ops` tables with the existing scripts.
  - With `BigInt` integers it is written as `a ** b`. I also changed `Nat.pow` on `BigInt`s to `a ** b`; it previously called `$bigPow`.
  - With `number` integers it calls new functions in `runtime.js`. They compute the power exactly by repeated squaring and throw on overflow, like `int53__lean_int_mul`. `uint53__lean_nat_pow` now uses the same method instead of `Math.pow`, which isn't guaranteed to be exact.
- **Printer.** The JavaScript syntax tree had no `**`, so I added it. Nested `**` always keeps its parentheses, and so does a unary operand on its left: `(-x) ** 3n`, `-(x ** 3n)`, `(x ** 2n) ** 3n`.

**Result on `AssocIntOps`**
| | faithful (`BigInt`) | pbo (`number`) | legacy |
|---|---|---|---|
| test1/2 | `x * 4n + 10n` | 2 calls | 9 ops |
| test3 | `x * 8n + 28n` | 2 calls | 19 ops |
| test4/5 | `x ** 4n * 24n` | `int53__lean_int_mul(int53__uint53__lean_int_pow(x, 4), 24)` | 9 ops |
| test6 | `x ** 8n * 5040n` | the same shape with 8 and 5040 | 19 ops |

At the pbo preset these stay runtime calls rather than inline `|0`. `|0` wraps at 32 bits, which would give wrong answers for Lean's `Int`; the calls check for overflow instead.

**Tests**
- New snapshot `Tests/SnapshotsMy/IntPow.lean` covers `x ^ n`, the parenthesisation cases above, and `Nat` products. Its node checks pass at both presets (84 cases each).
- I regenerated all snapshots. Only the `AssocIntOps` outputs changed, and every node check passes.
- The snapshot script still exits non-zero. The cause is the "literal too big" errors at the pbo preset in `PrimOpInt02Configurable`/`PrimOpInt03Configurable`, which were there before this change.
- `lake exe tests` passes 76/76. The `test5` expectation is updated and there is a new `Nat` case; `ArithTest.lean` proves for all inputs that the optimised term computes the original function.
- The full build still fails only on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib; that file is unchanged.
- The READMEs and the Properties table are updated.

**Limitations**
- In a sum, only unknowns are counted. `x ** 3n + x ** 3n` is not turned into `x ** 3n * 2n`.
- `(x ^ 2) ^ 3` is not folded into `x ^ 6`.
- A repeated factor that CSE has already bound to a variable (`const x3 = x * x`) is not seen through.

# Summary of changes for run 3a0b9416-3542-4366-9f58-f7075301ffe5
The faithful (BigInt) JavaScript for `AssocIntOps.lean` is now shorter than the legacy-backend output. For example, `test1` compiles to `(x) => x * 4n + 10n`, where the legacy backend wrote nine chained `+`/`|0` steps. All of the change is in the `Term → Term` phase, with a proof that it doesn't change the result.

**What the analysis showed.** Before this change, `Term.optimize` left the chains exactly as elaborated, e.g. `lean_int_add(lean_int_add(1, …lean_int_add(2, x2)…), 4)`. The JavaScript converter then printed them one operation at a time. The legacy backend at least folded the literals at the ends of each chain (`3 + x … + 7`).

**New pass: `Term.arithWalk`** (`LeanScript/Term/Optimize/Arith.lean`, run inside `Term.optimize` after `inlineRet`). It works on chains of `+` and `*` over `Int`, `Nat`, `UInt8`–`UInt64` and `Int8`–`Int64`:
- All literals in a chain are folded into one, which goes last and is dropped if it is `0` (sums) or `1` (products). Fixed-width types wrap around, e.g. `200 + x + 200 : UInt8` becomes `x + 144`.
- In a sum, repeated copies of the same variable are counted: `x + … + x` becomes `x * k`. A term already written as `x * c` counts as `c` copies, so inner chains that were already rewritten still combine correctly with the chain around them.
- The operands are then combined from the left.
- **Proved:** `Term.arithWalk_eval` (the value is unchanged in every environment) and `Term.numCalls_arithWalk` (no calls are added). `Term.optimize_eval` and `Term.numCalls_optimize` were updated and still hold. The proofs use only the standard axioms and contain no `sorry`.

**Result on `AssocIntOps`, faithful preset:**
| | new output | legacy backend |
|---|---|---|
| `test1`, `test2` | `x * 4n + 10n` | 9 operations |
| `test3` | `x * 8n + 28n` | 19 operations |
| `test4`, `test5` | `x * x * x * x * 24n` | 9 operations |
| `test6` | `x * x * x * x * x * x * x * x * 5040n` | 19 operations |

At the `pbo` preset, `test1` is `int53__lean_int_add(int53__lean_int_mul(x, 4), 10)`: two operations instead of nine. They stay calls into `runtime.js` rather than inline `|0`, because `|0` wraps to 32 bits and would give wrong answers for Lean's `Int`; these calls check for overflow instead. Since the pass reorders operations, at this preset it can change which intermediate result overflows, though never the value when nothing overflows.

**Tests and snapshots**
- New `Tests/TermTests/Optimize/ArithTest.lean` proves, for all inputs, that the optimised terms compute the original functions (`AssocIntOps` tests 1, 3 and 5, a `UInt8` example and a two-variable `Nat` example).
- New `arithSpec` in `Tests/Main.lean` checks the printed optimised terms and their values. `lake exe tests` passes 75/75.
- One existing expectation in `OptimizeTest.lean` changed: `n + n` now optimises to `n * 2`.
- I regenerated all snapshots and every node check passes. Only files with integer chains changed, all in the same direction (e.g. `11n + f$2 + 10n` became `f$2 + 21n`, and `x + 0n` became `x`).
- The snapshot script still exits non-zero because of the "literal too big" errors at the `pbo` preset in `PrimOpInt02Configurable`/`PrimOpInt03Configurable`, which were there before this change. In `PrimOpInt03Configurable`, the failing `test4` functions now report the folded literal (for example `1553255926290448384`) instead of the original one.
- `README.md` and `LeanScript/Term/README.md` are updated, and both theorems are in the Properties table as proved.

**Limitations**
- Only unknowns (not other repeated expressions) are counted in sums.
- There is no power operation for `Int`, so `x * x * x * x` is not shortened further.
- `x * 0` is not simplified to `0`.
- Subtraction is not part of the chains.

# Summary of changes for run ee049884-65ac-4c81-91b0-bdb941450640
I added `hashMap` and `hashSet` to `LeanPrimTyCovariant` and catalogued the `Std.HashMap` and `Std.HashSet` functions in two new files under `LeanScript/LeanInitPureExterns/`. They are **not connected to the compiler yet**: `Ty` has no hash-map or hash-set type, so these calls are not translated, evaluated or compiled to JS. The default build succeeds except for `LeanScript/Term/Syntax/UsageAlgebra.lean`, which fails because the project has no Mathlib dependency. That file was already there and nothing imports it. `lake exe tests` passes.

**What changed**
- **`LeanScript/Ty/Syntax/LeanPrimTyCovariant.lean`:** the two new formers are `hashMap : α → α → LeanPrimTyCovariant α` (keys, then values) and `hashSet : α → LeanPrimTyCovariant α`. `map` and `format` handle them. I replaced `val` with `children : … → List α`, because a hash map has two children; nothing in the project used `val`.
- **`LeanPrimTy.isObjectKey`** (in `LeanPrimTy.lean`): decides when a key can become a JS `Object` property via `String(key)`. It is true for every leaf type except `substringRaw`, `stringSlice`, `floatModel` and `float32Model`, since equal slices can come from different strings and the float models are structures. Enums also qualify; the docs say so, since enums are not leaf types. For other keys, the documented plan is a JS `Map` from hash to bucket, using the program's own `BEq` and `Hashable`.

**What the analysis found**
- No function of `Std.HashMap` or `Std.HashSet` is `@[extern]`: each is Lean code over an array of buckets. Unfolding them loses the fact that the value is a hash map, so every function gets an entry.
- `LeanInitPureExterns/HashMap.lean` defines `HashMapExtern` with 41 entries, including `Array.groupByKey` and `List.groupByKey`. `LeanInitPureExterns/HashSet.lean` defines `HashSetExtern` with 25 entries. Each file's header has a table mapping every function to its JS form (e.g. `{...m, [k]: v}`, `k in m`, `Object.entries`, `Object.groupBy`, `Set.union`).
- **Hash and equality functions:** following the `Array.contains` pattern, entries that hash or compare keys take the key's `BEq.beq` and `Hashable.hash` as their first two arguments. Entries that only walk the buckets (`size`, `toList`, `fold`, `filter`, `map`, `all`, …) don't take them. The backend drops the two arguments for object keys.
- **Iteration order differs:** `toList`, `toArray`, `keys`, `values` and `fold` follow Lean's bucket order. That depends on the hashes and on the map's history. A JS `Object` lists integer-like keys first and a `Map` uses insertion order. These entries are marked `(order)`: JS containers are only safe for them when the result doesn't depend on order; otherwise the runtime must reproduce Lean's buckets.
- **Left out on purpose, with reasons in comments:** `get`/`getKey` (they take a proof), the monadic `foldM`/`forM`/`forIn`, and `unitOfList`/`unitOfArray`/`insertManyIfNewUnit` (they return `HashMap κ Unit`, which is really a hash set). `Repr` and `numBuckets` are also omitted.

**Why it isn't connected yet**
- A `Std.HashMap κ ν` type takes the key's `BEq`/`Hashable` instances as parameters. Most key types in the language have no such instances (functions have no `BEq`), so a new `Ty` constructor needs a design decision first. One option is to allow only object keys; another is to store the instances as functions. This is written up in `NOT_IMPLEMENTED.md`.
- Until then, the two families are not part of `LeanInitPureExtern`. `Ty.ofCovariant` sends the new formers to the type of their `toArray`, only so the function covers every case; nothing uses that result.
- The extern-table and JS-ops generator scripts read an explicit list of catalogue files, so the new files don't affect generated code.

**Test:** `Tests/TermTests/Extern/HashExternCatalogueTest.lean` checks that every entry's argument order matches the real Lean function (with `String` keys and `Nat` values). It also builds entries of both families over the language's own types, and checks `isObjectKey`, `map` and `children` on a few examples.

# Summary of changes for run 45b9c980-61ca-4514-a782-9d4c2396d7b3
When this session started, the generated JavaScript for `AssocArrayAppend.lean` already matched `legacy-backend/AssocArrayAppend.js`. Every array test compiled to one literal like `(arr) => ["a", "b", ...arr, ...arr, ...arr, ...arr, "c", "d"]`, and so did the list tests at the `pbo` preset. What I changed is where the regrouping happens: you said you prefer optimisations in the `Term → Term` phase, so I moved it there, with a proof that it doesn't change the result. The generated JavaScript is the same as before.

**New optimiser pass (`LeanScript/Term/Optimize/Append.lean`, `Term.appendWalk`)**
- It runs inside `Term.optimize` and handles chains of `Array.append` and `List.append`.
- **Merging:** empty literal operands are dropped, and literals next to each other become one.
- **Arrays are grouped to the left**, `((x₁ ++ x₂) ++ …) ++ xₙ`. `Array.append` pushes onto its first operand (in place when nothing else refers to it), so each later operand is copied once.
- **Lists are grouped to the right**, `x₁ ++ (x₂ ++ …)`. `List.append` copies its first operand, so each operand except the last is copied once.
- **Why arrays go left:** I first grouped arrays to the right too. That made the output worse in `LocalFnInPlace` and `OwnershipAliasing`, where an owned first array is appended to in place; one case even allocated an extra `[...x, ...a]`. Grouping arrays to the left removed those regressions.
- **Proved:** `Term.appendWalk_eval` (the value is unchanged in every environment) and `Term.numCalls_appendWalk` (the number of calls is unchanged). `Term.optimize_eval` and `Term.numCalls_optimize` were updated and still hold. They use only the standard axioms, and there is no `sorry`.

**Result on `AssocArrayAppend`**
- In `AssocArrayAppend-Term-optimized.txt`, `ArrayTest.test1` is now `lean_array_append(lean_array_append(lean_array_append(lean_array_append(lean_array_append(#["a","b"], x2), x2), x2), x2), #["c","d"])`.
- `ListTest.test1` is now `lean_list_append(["a","b"], lean_list_append(x2, … lean_list_append(x2, ["c","d"])))`.
- The `.js` outputs are byte-identical to before, at both presets.

**Tests**
- New `Tests/TermTests/Optimize/AppendTest.lean` proves, for all inputs, that the optimised array tests compute the original functions.
- `Tests/Main.lean` has a new `appendSpec` that checks the printed optimised terms and runs their values. `lake exe tests` passes 70/70.
- I regenerated every snapshot. All node checks pass. Only two `-Term-optimized.txt` files changed (`AssocArrayAppend` and `ListRepr`); no `.js` file changed.
- `README.md` and `LeanScript/Term/README.md` are updated, and the two theorems are in the Properties table as proved. I couldn't view the whole table, so I didn't check older rows that may quote the previous `Term.optimize` pipeline.

**Limitations**
- A literal that the translator binds by name and reuses (for example an `#[]` used several times) isn't recognised as a literal, so it isn't merged or dropped.
- There is still no version of `List.append` that modifies the list in place, because the ownership analysis only tracks arrays. In every current snapshot the non-literal left operand is a function parameter, so it couldn't be used there anyway.
- The full `lake build` still fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That file is unchanged since the initial commit.
- The snapshot script still reports "literal too big" at the `pbo` preset for some large 64-bit literals, as before.

# Summary of changes for run 0c5446ca-5acd-4474-a6e6-0cb2e1c64833
Most of this task was already done in the previous run. The generated JavaScript for `AssocArrayAppend.lean` already matches `legacy-backend/AssocArrayAppend.js`: every array test, and the list tests at the `pbo` preset, compile to one literal such as `(arr) => ["a", "b", ...arr, ...arr, ...arr, ...arr, "c", "d"]`. The std array functions from your table were already catalogue entries, so they are no longer unfolded into `array_foldl`/`lean_array_push`. This session closed one remaining gap between the output and your `ListTest.test1` sketch.

**What changed: `List.append` on cons cells is now written into the generated module, not imported.** As you pointed out, the code generator chooses how `List` is laid out (`{ tag, _1, _2 }` cells), so the append helper shouldn't live in `runtime.js`.
- New file `JsTerm/Lower/LocalHelpers.lean` holds the table of such helpers (`localHelper?`). For now the only entry is `consList__lean_list_append`, written as a loop so a long list can't overflow the stack.
- `JsModule` has a new `locals` field. `mkModule` moves these helpers out of the import list, and the printer writes their definitions (not exported) at the top of any module that calls them.
- `ListTest.test1` at the `faithful` preset now has no import at all. It is the local helper followed by `{ tag: 1, _1: "a", _2: { tag: 1, _1: "b", _2: consList__lean_list_append(arr, … consList__lean_list_append(arr, { tag: 1, _1: "c", _2: { tag: 1, _1: "d", _2: { tag: 0 } } })…) } }`.
- The literal operands become cells directly, so nothing gets copied or mutated. That's why the `__owned_at_1` call from your sketch isn't needed.
- `runtime.js` keeps a function of the same name, because the operation tables are generated from it.

**Checks**
- `lake build JsTerm leanscript tests` succeeds.
- `lake exe tests` passes 67/67. The new test runs both copies in node and checks that they give the same results, share the right operand, and handle a 200,000-cell list.
- I regenerated the three snapshots that use the helper (`AssocArrayAppend`, `ListRepr`, `InlineClosures`). All their node checks pass at both presets (36, 58 and 40 cases).
- `README.md` and `NOT_IMPLEMENTED.md` are updated, and the helper table is registered in the Properties table.

**Not done**
- **In-place (`__mut0`) version:** there is no version that mutates the last cell of the left list. The ownership analysis only tracks arrays, not list spines, so it can't tell when the left list is safe to mutate. In every current snapshot the non-literal left operand is a function parameter, which the caller may still hold, so this version could not be used there anyway.
- **Other cons-list helpers:** the other cons-list functions in `runtime.js` (`consList__of_array`, `consList__to_array`, `consList__append`, …) are still imported. They convert lists between the array and cons-cell layouts.
- **`lake build` failure:** the full `lake build` still fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That file hasn't changed since the initial commit, and the project doesn't depend on Mathlib.

# Summary of changes for run 93fd0d49-ba7c-43f4-9cbd-4556a621e7ac
The JavaScript for `AssocArrayAppend.lean` now matches the purescript-backend-optimizer output: every array test, and the list tests at the `pbo` preset, compile to one array literal. For example, `ArrayTest.test1` and `test2` both become `(arr) => ["a", "b", ...arr, ...arr, ...arr, ...arr, "c", "d"]`, the same as `legacy-backend/AssocArrayAppend.js`. At the `faithful` preset, `ListTest.test1` is close to your sketch:
```
{ tag: 1, _1: "a", _2: { tag: 1, _1: "b", _2:
  consList__lean_list_append(arr, consList__lean_list_append(arr, … consList__lean_list_append(arr,
    { tag: 1, _1: "c", _2: { tag: 1, _1: "d", _2: { tag: 0 } } })…)) } }
```
The append chain is regrouped to the right, and literal operands become cells directly, so there is nothing to copy or mutate. The copying helper comes from `runtime.js` rather than being generated per module. The in-place variant (`__owned_at_1`) wasn't needed. All 36 generated checks pass in node for both presets.

**Why new externs rather than recovering the pattern.** Once `Array.append` is unfolded into `array_foldl … lean_array_push`, the loop could be the unfolding of `append`, of `map`, or of any hand-written fold. Recognising it again would be fragile, and a Term→Term pass can't express the result anyway, because `Term` has no array literal with spreads. So I took the middle-ground option you suggested: std functions written in Lean become catalogue entries whose meaning is the Lean function itself. The existing eval proofs therefore still apply, and an entry can't change what a program computes. The literal splicing is done in the Term→JsTerm conversion.

**From your table** (catalogue in `LeanScript/LeanInitPureExterns/ArrayStdFunctionsNonExternButBigEnoughToLoseInformation.lean`):
- **Added:** `append`, `map`, `filter`, `flatMap`, `flatten`, `reverse`, `extract`, `any`, `all`, `contains`, `find?`, `findIdx?`, `idxOf?`, `eraseIdx!`, `insertIdx!`, `qsort` (an exact port of Lean's quicksort, so the order matches), plus `eraseIdxIfInBounds`, `insertIdxIfInBounds`, `foldr`, `zipWith`, `zip`, `back?`, `countP` and `List.append`.
- **Not needed:** `Array.replicate` is already the C extern `lean_mk_array`. `take` and `drop` unfold to `extract`. `back!` and `xs[i]?` unfold to a bounds check and a read.

**Other changes:**
- **Conversion to JavaScript** (`JsTerm/Lower`): chains of appends become one literal, merging any literal operands. Cons-cell list appends are built from the end as described above. An append onto an array nothing else refers to is still done in place.
- **Elaborator:** an array literal bound by `let` and used once (not inside a `fun`) is substituted so it can be spliced. An argument that another argument also computes is now bound once; before, `(a.map f).filter p` computed `a.map f` twice because of the default bound `.size`.
- **JavaScript operations and `runtime.js`:** new functions for all entries, with generic and typed-array versions and both number and BigInt indices. I fixed a wrong result type for `zip`.
- **Proof:** `OpsSpec.cands_sig_nodup` now also covers the new entries (no extern has two candidates at one signature). `lake build OpsSpec RuntimeSpec RefactorSpec` passes with no `sorry`.
- **Tests:**
  - `lake exe tests` passes 66/66; I updated the list of array updates to include append.
  - New snapshot `Tests/SnapshotsMy/ArrayStdFunctions.lean` translates all 22 functions, and its 304 checks pass in node for both presets.
  - After regenerating all snapshots, every node check passes and no file translates fewer functions. `MapFilter`, `CaseLeafTco` and `OwnershipAliasing` now translate more.
  - README and `NOT_IMPLEMENTED.md` are updated.

**Still failing or not supported:**
- `lake build` fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib; that file is unchanged since the initial commit and the project doesn't depend on Mathlib. Everything else in the default build compiles.
- The snapshot script still reports "literal too big" for `PrimOpInt02Configurable`/`PrimOpInt03Configurable`, as it did before.
- `Array.map` and similar over arrays whose elements are functions still can't be translated, as before. Such calls now fall back to unfolding, which fails for `Array.map`.
- `ArrayAppend` tests `test1` and `test3` were already untranslated before these changes and still are.
- I did not add a proved Term→Term append pass; I kept the optimisation in the conversion for the reason above.

# Summary of changes for run 124c4104-9e6e-43a8-bd95-e720134d20cc
I extended the proven `Term.optimize` inliner and brought the documentation up to date. Everything builds with no `sorry`. The new theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and `lake exe tests` passes 66/66.

**New optimisations, each proved to leave `Term.eval` unchanged and never add calls:**
- **Substitution (`Term.subst`, `LeanScript/Term/Optimize/Subst.lean`):** replaces variables with pure expressions. It also simplifies a record pattern-match applied directly to a record literal. It only copies cheap expressions (variables, constants, literals) into places where they could run more than once, so no computation is repeated. Proved: `Term.subst_eval` (value unchanged) and `Term.numCalls_subst` (number of calls exactly the same).
- **Inlining on any argument (`InlineSubst.lean`):** a closure used once can now be inlined at a call whose argument is any pure expression, including a record literal. Record fields that compute something are first given names with `let`, so they aren't evaluated twice. The inlined body's result can be any expression.
- **Inlining at the only call (`Term.inlineAt`, `InlineOnce.lean`):** a closure used once whose body itself makes calls is inlined at its single call. This works when that call is reached through `let`s, record pattern-matches, `if` branches and join points. Proved: `Term.inlineAt_eval` and `Term.numCalls_inlineAt`.
- These are wired into `Term.inlineRet`, so `Term.optimize_eval` and `Term.numCalls_optimize` still hold.

**Effect on the output:** I regenerated the snapshots. `ScalarRepl.test3` no longer builds a record, and more helper closures are inlined in `AppArity`, `RecData`, `OptionUnbox`, `LoopClosure`, `LocalFnInPlace`, `OwnershipAliasing`, `ArrayInPlace` and `InlineClosures`. The node checks report no failures. The snapshot script still exits with an error, but only because of a "literal too big" problem in `PrimOpInt02`/`PrimOpInt03Configurable` that was there before this work.

**Documentation:** updated the `Term.optimize` docstring in `Optimize/Basic.lean`, the `InlineBlock.lean` header, `README.md`, `LeanScript/Term/README.md`, `NOT_IMPLEMENTED.md` and `proposals/NoJsTermOptimizations.md`. The four new theorems are in the Properties table as proved, and the `Term.inlineRet_eval` entry now describes the pass as it is. I haven't re-checked the rest of the table in this session.

**Still not done:**
- **Closures that capture outer variables** are not inlined, for example `k$2` in `InlineClosures.sumShifted`. This is the main remaining piece of the old `inlineConsts`.
- Closures used several times whose body is more than a single `ret e` are not inlined.
- A closure whose only call sits under a match on an enum or union is not inlined.
- Fusion, constructor specialisation, unboxing parameters, recovering `Q`'s type parameters, and the other data representations are not implemented.

# Summary of changes for run eabcd799-d14b-4458-a4a4-d464fa3c2891
This session adds a proven Term-level inliner, `Term.inlineRet`, which takes over part of what the old module-level `inlineConsts` did. It does not replace `inlineConsts` completely; the cases it still misses are listed at the end. It runs inside `Term.optimize`, after `condWalk` and before `dce`, and `Term.optimize_eval` still holds. `Term.optimize_eval`, `Term.inlineRet_eval`, `Term.relvl_eval` and `Term.numCalls_inlineRet` have no `sorry` and depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

**What the inliner does** (`LeanScript/Term/Optimize/InlineRet.lean`, `InlineBlock.lean`)
- **Tail calls:** when a call to a known closure `fun x => ret e` is returned directly (`let y := k a; ret y`), it becomes `ret e[a]`. This works whatever the result is, including literals, constants and data literals.
- **Dead bindings:** they are dropped even when that changes the level, for example inside closed bodies.
- **Closures used once:** a known closure used once, whose closed body makes no calls, is inlined where it is called on a simple variable or expression argument. Its body is moved to the call site with a new renaming that can change levels (`Term.relvl`, in `LeanScript/Term/Rename/Relevel.lean`). The body's result is then bound to the call's result.
- **Bodies ending in a branch (new this session):** the rest of the calling code becomes a join point, and every arm of the branch jumps to it. This adds `Term.retToJump` / `Branch.retToJump` / `Branches.retToJump`, with proofs that they keep the value and add no calls.

**Proved results**
- `Term.inlineRet_eval`: the pass does not change `Term.eval`.
- `Term.numCalls_inlineRet`: the pass never adds calls; `Term.numCalls_optimize` was extended to cover it.
- `Term.relvl_eval`: the level-changing renaming does not change `Term.eval`.

**Effect on the generated JavaScript** (all snapshots regenerated)
- `FunctionCompose01` shrinks to `(a) => "a"`.
- The helper closures of `RecData` (`sumArray`, `reverse`, `sort`) and `OwnershipAliasing` are now inlined.
- `KnownConstructors`, `KnownConstructors05` and `BranchSpecialization01` no longer build a local closure and call it; for example, `test6` now assigns the result directly in an if/else chain.

**Checks**
- `lake build leanscript tests TermTests TyTests JsTerm` and `LeanScript.Term.Optimize.CountOptimize` both succeed.
- `lake exe tests` passes 66/66.
- There is no `sorry` in `LeanScript/Term/Optimize` or `LeanScript/Term/Rename`.
- All node snapshot checks passed. The snapshot script still exits with status 1, only because of the same "literal too big" errors as before in `PrimOpInt02Configurable` and `PrimOpInt03Configurable`.

**Documentation:** updated `README.md`, `LeanScript/Term/README.md`, `NOT_IMPLEMENTED.md`, `proposals/NoJsTermOptimizations.md` and the `Term.optimize` docstring. Three proved entries were added to the Properties table.

**Still not done**
- These cases are not inlined yet:
  - calls whose argument is not a simple variable or expression, such as a record literal `k ⟨x, y⟩`;
  - closure bodies that make calls;
  - closures used several times whose body is more than a single `ret e`;
  - closures that return closures (`AppArity`);
  - closures passed to other closures (`InlineClosures.sumShifted`).
- Fusion, constructor specialisation, unboxing of parameters, the nullable and struct-of-arrays representations, and recovering `Q`'s type parameters are also not implemented.

# Summary of changes for run d1f4c2f2-996f-4294-afb8-ba499ba78b49
The first part of your request was already in place from earlier runs: several versions of each non-inlined function, each allowed to update different array parameters in place. For the "finish" part, I added the first step of the Term-level inliner, which the proposal named as the main remaining work. It is proved correct. Everything else on that list is still not done.

**What was added: `Term.inlineKnown`**
- New files: `LeanScript/Term/Optimize/Inline.lean`, `InlineEval.lean`, `CountInline.lean`. It is now the first pass of `Term.optimize`.
- It handles a local closure whose body mentions nothing from outside and is just `ret e[x]`, i.e. it only computes one expression of its parameter.
- At a call `let y := k a`, the call becomes `let y := share e[a]`. This only happens when `e[a]` is an expression that can be named by `let`. Dead-code elimination then removes `k`.
- The walk keeps track of what it knows about each closure in scope. It carries that information into the body of each `val` and into closed bodies.

**Proved (no `sorry`; only the axioms `propext`, `Classical.choice`, `Quot.sound`)**
- `Term.inlineKnown_eval`: the pass does not change `Term.eval`, in any environment. So `Term.optimize_eval` and `Term.optimizeN_eval` still hold for the extended optimiser.
- `Term.numCalls_inlineKnown`: the pass never adds calls. `Term.numCalls_optimize` now covers it.

**Effect on the generated code**
- The snapshots were regenerated. Only `InlineDemo` and `LocalFnInPlace` changed, with 6 calls inlined in total.
- For example, `useScale` now emits `const x$1 = uint53__lean_nat_mul(n, 2); …` with no helper closure.
- All node checks pass. The script still exits with an error because of the existing "literal too big" refusals in `PrimOpInt02Configurable` and `PrimOpInt03Configurable` under the pbo preset.
- `lake build leanscript tests JsTerm TermTests TyTests` succeeds and `lake exe tests` passes 66/66.

**Not inlined yet** (listed in `NOT_IMPLEMENTED.md` and `proposals/NoJsTermOptimizations.md`)
- Calls whose result is a literal or data literal, such as `fun _ => "a"` in `FunctionCompose01`, `OptionUnbox` and `RecData`. The result cannot simply be named by `let`; handling these means re-normalising the rest of the function.
- Closures whose body is more than one expression.
- Closures passed to other closures, such as `InlineClosures.sumShifted`.

The remaining cases would all need a general inliner. It would have to substitute known values, normalise the result again, and shift the depth of the inlined body.

**Also still open from your list:**
- Fusion, constructor specialisation and unboxing parameters.
- The nullable and struct-of-arrays representations.
- Recovering Q's type parameters.

**Also note:** `LeanScript/Term/Syntax/UsageAlgebra.lean` imports Mathlib, which this project does not depend on, so building the whole `LeanScript` library fails on that one file. This was already the case before this work. The targets above do not depend on it.

README, `LeanScript/Term/README.md`, `NOT_IMPLEMENTED.md` and the proposal document are updated. Both theorems are in the Properties table as proved, and all work is committed.

# Summary of changes for run 4e42c39e-2e2f-4623-aa50-762420654cfa
I extended the static in-place analysis (no runtime reference counts) from top-level exports to local functions, closures and folds over datatypes. None of this analysis is proved: it only decides which array updates the generated JavaScript does in place, and it is checked by tests. `Term.eval`, the optimiser and its existing correctness proofs are unchanged. The Term-level inliner that would replace `inlineConsts` is still not done.

**What changed**
- **Usage counters** (`LeanScript/Term/Ownership/Basic.lean`, `Walk.lean`):
  - The two arms of a conditional now count as exclusive, so a value used once in each arm counts as used once.
  - The environment now tracks, for each local function, which versions of it exist and which of its parameters it may update in place.
- **Versions of local functions:** a function that is not inlined can get up to 3 extra versions, each updating a different set of array parameters in place. For example, one version can update its 1st argument in place and leave the 2nd and 3rd alone. When the conversion to JsTerm (`JsTerm/Lower/FromTerm.lean`) emits the function, it writes one constant per version (`k`, `k_mut`, …), and each call site picks the version that fits what that site owns. Partially applied functions that are used more than once keep this information, but pass no ownership.
- **Owning closures:** a closure can own an array it captures. The array is updated in place inside the closure, and is copied once when the closure is called if the caller does not own it.
- **Other cases now updated in place:**
  - array literals;
  - the result of a conditional, when both arms give an owned array;
  - owned results of calls;
  - fields of records;
  - in folds over declared datatypes, the answers coming back from the recursive positions.
- **Data structure:** `Translated.optimized` holds an `OwnedTerm`: the optimised term plus the list of versions to generate. The first version borrows every parameter, and each extra export is emitted as `f$$mut_i_j`.

**Checks**
- Two new snapshot files, `Tests/SnapshotsMy/LocalFnInPlace.lean` and `Tests/SnapshotsMy/OwnershipAliasing.lean`, cover this. The second includes a `Bag` datatype to test aliasing.
- The JavaScript now updates in place in several existing snapshots: `ArrayInPlace.test6`, `InlineClosures.downFrom`, `RecData` (`toArray`, `inorder`, `reverse`, `sort`), `MapFilter.test5` and `ArrayFSet`.
- The full snapshot run found no failing node check. It still exits with an error, because the UInt64 and Nat literals in `PrimOpInt02Configurable` and `PrimOpInt03Configurable` don't fit in a JavaScript number under the pbo preset; that error was already there before this work.
- The node checks run every version and check they give the same answer. They also call each plain export twice on the same array, to confirm it does not change its argument.
- `lake build tests TermTests TyTests JsTerm leanscript` succeeds. `lake exe tests` passes 66/66, including a new test for local-function versions and owning closures.
- There is no `sorry` in the ownership code.

**Still not done** (recorded in `README.md`, `NOT_IMPLEMENTED.md` and `proposals/NoJsTermOptimizations.md`, all updated)
- `inPlace` still runs on the finished JsTerm.
- `hoistConsts` and `shareFuns` still build the module.
- `inlineConsts` needs a proven Term-level inliner before it can move.
- Fusion, constructor specialisation and unboxing parameters have not been written.

The `OwnedTerm` entry in the Properties table is updated and stays in progress, since the analysis has no proof. All work is committed.

# Summary of changes for run 65988e37-4427-41dc-9c90-c5f78cb3c033
The compiler now updates arrays in place based on a static "functional but in place" analysis, with no reference counts at run time. It generates several versions of each exported function, which differ in which array parameters they are allowed to mutate. The analysis itself is not proved correct; it is checked by tests.

**Ownership analysis on `Term`** (`LeanScript/Term/Ownership/Basic.lean`, `Walk.lean`)
- It runs on the optimised `Term`, before conversion to JavaScript.
- For each variable it counts uses, and separately the uses that escape, the uses inside a loop body, and the uses inside a closure or delay.
- It then walks each function in execution order and tracks which arrays are *owned*: built by the function itself, or a parameter the caller gave up. An owned array that nothing uses afterwards is updated in place (`push`, `pop`, `set`, `swap`, `fset`, `fswap`).
- A `set!`/`swapIfInBounds` on an array that is still used afterwards copies it first, then updates the copy.
- The accumulator of a loop (`nat_rec`, `foldl`) is borrowed, owned, or copied once before the loop when that saves a copy on every iteration.
- As you suggested, only types that contain arrays take part; numbers, records of numbers and lists do not.

**Function versions**
- `Translated.optimized` in `LeanScriptCli/Main.lean` is now an `OwnedTerm`: the optimised term plus a non-empty list of versions. Each version records which parameters it owns and its static cost (updates in place, array copies).
- The first version borrows every parameter; it is the plain export and is safe for any caller.
- If owning some array parameters saves copies, there is one extra version owning all of them. When two or three parameters qualify, there is also one version owning each of them alone.
- `termToJs … owned` builds each version from the same `Term`. Extra versions are exported as `f$$mut_i_j` (owning parameters i and j), and each one's doc comment says what it owns and what it costs. `FILE-Term-optimized.txt` lists them as `-- version …` lines.
- Example from the `ArrayInPlace` snapshot: `test1` and `test5` update in place; `test3` copies its parameter once before the loop (`[...a0]`) and then mutates the copy; `test3$$mut_0` never copies.

**Limits**
- Translated functions never call each other, so the `$$mut` versions are only for JavaScript callers. A caller must not use an array after passing it to a parameter that version owns.
- Local closures get no versions; they always borrow their parameters.

**The second item ("finish" the remaining JsTerm-stage work)**
- The in-place rewrite that used to run on finished JsTerm is now decided on `Term`, and the conversion emits the in-place (`…_mutable`) array updates directly.
- The module-level inlining of known closures (`inlineConsts`) is still not done. It needs a proven inliner at the `Term` level, and it remains open, as noted in `proposals/NoJsTermOptimizations.md`.

**Checks**
- The node snapshot checks now run every version of each function. For functions with array parameters, they also call the plain export twice on the same array to confirm it does not mutate its argument.
- All snapshots in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` were regenerated and all node checks passed. The run's non-zero exit is the existing "literal too big" refusal in `PrimOpInt02`/`PrimOpInt03Configurable`, which is expected.
- `lake build JsTerm leanscript tests TermTests TyTests` succeeds and `lake exe tests` passes 65/65.
- No `sorry` in the new code, and `Term.eval` and the proofs about `Term.optimize` are unchanged.

**Docs**
- `README.md`, `NOT_IMPLEMENTED.md` and the status note in `proposals/NoJsTermOptimizations.md` describe the analysis and its limits.
- `OwnedTerm` is in the Properties table as an unproved definition.

All work is committed.

# Summary of changes for run fdf29682-b553-456d-978f-6030204fda0d
Proposals P, R and S from `proposals/TypedDataProposals3.md` are now in place, along with Q's prelude. Q's other part, recovering type parameters, is not done. As you asked, nothing optimises JsTerm into JsTerm. The new typing and representations are chosen when `Term` is converted to JsTerm, and the printer only reads them. All optimisations are still on `Term`.

**What I found.** P (nominal `JsTy.obj id args` with the signature `JsSig`) and Q's prelude (`consList`, plus `Option`/`Prod` as anonymous `union`/`record` declarations) were already implemented. R had unchecked, untested code, and the docs said it was missing. S had not been started.

**R: one id for datatypes with the same layout** (new file `JsTerm/Ty/Canon.lean`)
- `refineClasses` merges datatypes whose layouts are equal as infinite trees. `isBisim` checks the result, and `canonDecls` falls back to "every datatype keeps its own id" if the check fails. `termToJs` names each datatype by its canonical id.
- **Proved:** `canonDecls_sound` says a datatype and its canonical datatype unfold to the same layout at every depth. It follows from `isBisim_sound` and uses only the `propext` and `Quot.sound` axioms, with no `sorry`.

**S: the representation is part of the type**
- A union's id now carries its representation, `JsObjId.union arities repr`, with `JsRepr` either `cells` or `smallIntNullary`. So the two representations are different types, and switching between them needs an explicit conversion.
- Under `smallIntNullary`, a constructor without fields is printed as the number of its position (`0` instead of `{ tag: 0 }`) and tested with `s === 0`. Constructors with fields are unchanged.
- It is off by default. Turn it on with `leanscript --nullary=int` (`JsConfig.nullaryRepr`). It then applies only to unions that have constructors both with and without fields. The standard library's cons cells stay as they are, because `runtime.js` reads them.
- Catalogue externs still take and return the object form. Around them the conversion is explicit (`JsListOp.nullaryToInt` / `nullaryToCells`, backed by two new `runtime.js` functions).

**Tooling**
- `scripts/gen_js_ops.py` emits the new union form, and rerunning it reproduces `JsTerm/Ops/Imported.lean` exactly.
- `scripts/annotate_runtime.py` could not parse `.obj` types before this change. It can now, and it keeps hand-written tags. `--check` passes.

**Checks**
- `lake build JsTerm TermTests TyTests tests leanscript OpsSpec RefactorSpec` succeeds.
- `lake exe tests` passes 65/65. Four tests are new:
  - canonical ids;
  - representation typing and the converted extern;
  - the `runtime.js` conversions under node;
  - an end-to-end run of `leanscript --nullary=int --check` on `RecData` and `ListRepr`, with the generated checks run under node.
- `scripts/leanscript-snapshots.sh` regenerates every snapshot byte-for-byte with the default settings. The script still exits non-zero, as it did before my changes, because of the existing "literal too big" refusals in `PrimOpInt02Configurable` and `PrimOpInt03Configurable`.
- I also ran the whole snapshot corpus with `--nullary=int`: all 282 check files passed (4206 checks). That was a one-off run and is not part of `lake test`.

**Not done** (recorded in `NOT_IMPLEMENTED.md` and in a status note at the top of the proposal):
- Q's type parameters are not recovered by anti-unification. Datatypes stay `obj (decl i) []`, and the JavaScript would be identical either way.
- The other representations (`nullable`, struct-of-arrays) are not implemented, and the representation is chosen per module, not per use.
- The gains that are really optimisations are not done: fusion, constructor specialisation and unboxing parameters. They would have to be written on `Term`, with `Term.eval` proofs.

I updated `README.md` and the Properties table: I added `canonDecls_sound` (proved), `canonDecls` and `JsRepr`, and removed an entry for the deleted `JsBlock.emit`. All work is committed.

# Summary of changes for run 548bb7bc-3053-4d68-81fe-5b4762d7f12c
**Is it possible?** Mostly, yes. The function-level part is now done. The function-level JsTerm optimisations no longer run as a separate JsTerm→JsTerm stage: they now happen while `termToJs` builds the JsTerm. Two things still run on finished JsTerm: `inPlace` and the module assembly in `mkModule`. Removing either today would lose optimisations, so I kept them. I checked that nothing was lost by regenerating the snapshots and running the tests; this is not a formal proof that the output is unchanged.

**What changed**
- **New file `JsTerm/Lower/Emit.lean`:** it adds `JsBlock.emit`, which every block goes through as `JsTerm/Lower/FromTerm.lean` builds it. The children of a block are already simplified, so it only applies the rules at the new block. These are the same rules the old passes used: `cleanup` (copy propagation, constants used once, …), `peephole`, the array-literal rules, and `tidyStep` (unboxing, scalar replacement, contification, join-point flattening, closure-chain tail calls, target-specific narrowing and arithmetic).
  - When a rule rewrites a block, that block is simplified again until nothing changes. I tried one pass without this: 21 snapshot files came out worse, so the repeat is needed to miss nothing.
  - Some rules are only valid when no closure reads a mutable variable, which depends on the whole function. So `termToJs` first does a quick conversion with no rules to decide that, then the real one.
- **`termToJs`** no longer calls `cleanup`, `peephole`, `inlineArrays` or `tidy`. I deleted the unused whole-function drivers `tidy` and `inlineArrays`.
- **New Term-level pass `LeanScript/Term/Optimize/Cond.lean`:** `Term.condWalk` is now part of `Term.optimize`. It rewrites `c ? true : false` to `c`, and a test of `c ? false : true` swaps the two arms. I proved it keeps the value (`Term.condWalk_eval` and related lemmas), so `Term.optimize_eval` and `Term.optimizeN_eval` still hold. Their only axioms are `propext`, `Classical.choice` and `Quot.sound`. I also proved it never adds calls (`numCalls_condWalk`).
  - It shortens three `Term-optimized.txt` snapshots, e.g. in `PrimOpBoolean01` a four-deep nested `cond(...)` becomes `cond(x2,false,x4)`.
  - The JavaScript for those is unchanged, because the JsTerm rules already simplified it.

**Checks**
- `lake build leanscript tests JsTerm TermTests TyTests` succeeds, with no `sorry` in the new code.
- Every JavaScript snapshot in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` regenerates byte-for-byte the same as before; only the three Term snapshots above changed.
- The test runner passes 61/61.
- As before, the `LeanScript` library as a whole still doesn't build, because `LeanScript/Term/Syntax/UsageAlgebra.lean` imports Mathlib, which this project doesn't have. That's why I built the specific targets above.

**What still runs on finished JsTerm, and why** (details in `proposals/NoJsTermOptimizations.md`)
- **`inPlace`** updates arrays in place when nothing else refers to them. It needs to see every later read of the array in the whole function, so it can't be done block by block. Moving it earlier would need a uniqueness analysis at the Term level.
- **`mkModule`:**
  - `hoistConsts` and `shareFuns` work across all the functions of one `.js` file; they are what builds the module.
  - `inlineConsts` inlines known closures from the module into their call sites. That is a functional optimisation that belongs in `Term.optimize`, but it needs a proven Term-level inliner first. That is the main remaining piece of work.
- The proposal document also has a table of how often each rule fired across the snapshots (from an instrumented run, not a formal check), and whether each could move to Term.

I also updated the `README.md` and the docstrings that described the old pipeline, and added the new pass and `JsBlock.emit` to the Properties table. `ARISTOTLE_SUMMARY.md` is unchanged. All work is committed.

# Summary of changes for run bfd42c21-9291-4ab3-a611-9ceae53b2e42
I wrote the proposals in `proposals/TypedDataProposals3.md`. The project already had two notes on this question (`proposals/TypedDataProposals.md` and `TypedDataProposals2.md`), so this one only covers designs they don't. Nothing in `JsTerm` was changed.

**Why optimisations get lost.** The passes find their work by matching four forms: `union_mk`, `unionCases`, `record_mk` and `destructure`. Checking the code, I found that the passes never *create* an object type; they only match on one. Object types are created only during lowering and in five signatures of the extern catalogue: `Option String` and four pairs. So the object types can be redesigned without rewriting the passes themselves; only the type indices in their patterns change.

**The proposals:**
- **P (recommended): every tagged-object type becomes a name.** `JsTy` gets one form, `obj (n : Nat) (args : List JsTy)`, which replaces `record`, `union`, `data` and `consList`. It points into a table of declarations; a structural union becomes an anonymous declaration. The constructor form and the case analysis use the same index, so rewrites like case-of-a-known-constructor need no cast nodes, proof fields or type coercions. Each value also has exactly one type, unlike the earlier "head form" design, where a value has one type at a binder and another inside fields. Type equality becomes a comparison of a number and a list of arguments.
- **Q: datatypes with type parameters.** JavaScript erases types, so one declaration of `List α` can serve every element type. The built-in `List` and a user's `MyList α` would share one code path, which removes `consList` and the roughly 40 list-specific matches in the passes. The extern catalogue gets a small prelude (`Option`, `Prod`, `List`), and helpers are emitted once per datatype rather than once per element type.
- **R: one id per layout.** Before building the typed code, datatypes with identical layouts (compared as possibly infinite trees) are merged into one id, using a standard automaton-minimisation algorithm. This gives the meaning of a recursive-type binder, but equality is decided once, up front, so inside the typed code it stays a plain comparison. Datatypes with the same layout then produce identical JavaScript.
- **S: the representation stored with each declaration.** The layout choice (cells, array, nullable, and so on) becomes part of a declaration's table entry instead of the global `listRepr` setting. Two representations of the same constructors are different types, so Lean's type checker rejects mixing them, and every change of representation is an explicit conversion. The global setting stays as the default.

**How typing can improve the optimisations (beyond the earlier notes):**
- identical code, constants and object shapes for identical layouts;
- constructors without fields printed as small integers instead of `{ tag: 0 }` objects;
- tag tests by pointer comparison (`x === $tag0`);
- one typed array per field for arrays of all-number records;
- loop fusion and constructor specialisation written once for all datatypes;
- unboxing record parameters of functions, as `Unbox` already does for local variables;
- faster type comparison in the compiler, and an `a === b ||` shortcut in generated equality helpers.

The note ends with a comparison table against the earlier recommendations and a suggested order: stable ids, then pass counters, then P (tried first on `Unbox`), then Q, R and S.

**Toy model.** `proposals/TypedDataNodeToy.lean` is a small standalone model of P and Q together, outside the Lake build. It compiles with `lake env lean proposals/TypedDataNodeToy.lean` with no errors, warnings or `sorry`. It proves that the case-of-a-known-constructor rewrite preserves evaluation (`Expr.knownCtor_eval`, which uses only the `propext` axiom). Its examples use one declaration of `List α` at both `List Nat` and `List (List Nat)`, plus an anonymous union, checked by `rfl`. It doesn't model the real passes, the lowering, R's merging or S's representations.

Everything is committed.

# Summary of changes for run 5a7cf501-d194-4980-9eea-1de898c78986
I wrote the proposals in `proposals/TypedDataProposals2.md`. The project already had `proposals/TypedDataProposals.md` on the same question, so this note covers designs that one doesn't. Nothing in `JsTerm` was changed.

**The risk.** The optimisation passes find their work by matching the syntax of four forms: `union_mk`, `unionCases`, `record_mk` and `destructure`. There are 114 such matches in `JsTerm/Passes` and `JsTerm/Print`. The usual typed design adds "cast" nodes around datatype values. The passes would no longer recognise those values, and an optimisation that stops firing fails silently: the snapshots still compute the right answers.

**The proposals:**
- **A. A stable number per datatype.** `data (id : Nat)` with a table in the module. The current `D<depth>_<j>` names come from a relative depth, so they change between scopes and can clash. This step fixes that, and the other proposals build on it.
- **B. No expression has a datatype type (recommended).** Wherever a value is bound (a match arm, a constructor argument, a function parameter), its type is the datatype unfolded one level. A `List Nat` value then has an ordinary union type. It is built by the existing `union_mk` and matched by the existing `unionCases`, so all 114 patterns keep their shape, with no cast nodes and no proof fields. Only the indices of binders change (`heads Σ fs`).
- **C. The datatype's declaration stored inside the type.** Recursive positions become slots, so the passes need no extra signature parameter. Combined with B, the passes keep their current parameters; the cost is a larger hand-written equality on types.
- **D. The layout proof found automatically.** A lighter version of part 1's recommendation, where instance search supplies the proof that a type unfolds to given constructors.
- **E. Rejected:** indexing expressions by runtime shape loses the field types.

**Catching a lost optimisation.**
- Each pass would report counters (known-constructor rewrites, shared `$tag0` constants, `Unbox` removals, in-place updates), and a test in `Tests/Main.lean` fails if a count drops.
- A second test compiles the same program with `List` and with an equivalent user type `MyList` and requires identical JavaScript. It can only run once recursive user types are accepted.

**Optimisations typing adds:**
- Built-in lists and user datatypes share one code path, replacing about 40 list-specific lines in the passes.
- In-place array updates next to lists and other array-free datatypes. Today the check (`shareFree`) rejects any value containing a list.
- Overwriting a matched cell in place when it is uniquely owned (the reset/reuse technique Lean's own compiler uses).
- One object layout per datatype, so JavaScript engines see a single object shape.
- `null` for the empty case of option-like types.
- Loops chosen from the type, direct field reads, and per-datatype equality and hashing helpers.

The note ends with a comparison table and a suggested order: A, then the counters, then B, then the gains.

**Toy model.** `proposals/TypedDataHeadToy.lean` is a small standalone model of Proposal B, outside the Lake build; check it with `lake env lean proposals/TypedDataHeadToy.lean`. It compiles with no errors, warnings or `sorry`. It proves that the case-of-known-constructor rewrite preserves evaluation (`Expr.knownCtor_eval`, which uses only the `propext` axiom), and that rewrite needs no casts. The model also has a fuel-free evaluator and `List Nat` examples checked by `rfl`. What it doesn't show is that the real passes, `Unbox` in particular, adapt as easily; the note says to try `Unbox` first. Everything is committed.

# Summary of changes for run bf163571-921e-461c-8c7a-e52fbcdd477d
I wrote the proposals in `proposals/TypedDataProposals.md`. It builds on §3 of `JsTermReviewPlan.md` and on `RecursiveDatatypesProposal.md`. Nothing in the main code base was changed.

**The problem.** The passes in `JsTerm/Passes` find their work by matching on `union_mk`, `unionCases`, `record_mk` and `destructure`, about 40 places in all. The usual way to type `data` adds two "cast" nodes (`data_in` / `data_out`) that do nothing at run time. Those nodes would hide the patterns from the passes, so optimisations like `$tag0` sharing, `Unbox`, and case of a known constructor would silently stop firing. The snapshots would still pass; only the output would get slower. Separately, the current `D<depth>_<j>` name is computed from a relative depth, so the same datatype can get different names in different scopes.

**The five proposals:**
1. **Store an index plus a checker.** `data (id : Nat)`, with a table of layouts in `JsModule` and a separate well-formedness check. No pass changes and nothing is lost, but the typing is only checked, not guaranteed by Lean's types.
2. **Keep the cast nodes, but add helpers.** Constructors that cancel a cast followed by its inverse, plus "views" that let each pass look through casts. It works, but every pass has to be ported.
3. **Recommended: prove the layout instead of casting.** `union_mk`, `unionCases`, `record_mk` and `destructure` each take a proof that their type unfolds to the given constructors (`τ.ctors? Σ = some cs`). A structural union and a declared datatype then use the same syntax. Porting a pass means adding one proof field to its patterns, and one rewrite covers both kinds of type.
4. **Make the signature a parameter.** Passing the signature as a parameter of `JsExpr` / `JsBlock`, instead of indexing every type by it, keeps the changes small. `JsTy`'s decidable equality stays as it is, and names become stable across scopes.
5. **A recursive-type binder (`μ`) in `JsTy`.** Assessed and not recommended: type equality stops being syntactic and the cast problem comes back.

**How typing can improve the optimisations:**
- `consList` becomes the built-in `List` datatype, so lists and user datatypes share one set of passes (including tail sharing).
- Whether a traversal can be compiled to a loop (lists and other linear types) becomes a property of the signature that can be decided, instead of a guess from the code's shape.
- A "known constructor" type would allow reading fields directly (`cur._1`) with no tag test, typed loops over a cursor, and a type-directed `Unbox`.
- Layout choices per datatype (`null` for the empty case, `Nat`-like types as numbers, and so on) would be enforced by the types.
- The generator could emit equality, hashing and array conversion once per datatype.
- `JsTerm` would get a semantics that passes can be proved against.

The document ends with a comparison table and a suggested order: Proposal 1 first to unblock the `FromTerm` translation, then 3 + 4, then the improvements.

**Toy model.** `proposals/TypedDataToy.lean` is a small standalone Lean model of Proposal 3. It is not part of the Lake build; check it with `lake env lean proposals/TypedDataToy.lean`. It compiles with no errors and no `sorry`. It has one constructor former and one case analysis serving both structural unions and a recursive declared datatype, an evaluator that needs no fuel, and a proof that the case-of-known-constructor rewrite preserves evaluation (`Expr.knownCtor_eval`, which depends only on `propext`). It also includes a small `List Nat` example checked by `rfl`.

# Summary of changes for run 8008d3bc-0d2e-457a-a2c8-fa56fdc6ffad
I added the `ListRepr` setting to the JavaScript backend, exactly as you wrote it, and implemented both layouts. `JsConfig.listRepr` defaults to `.taggedUnion`, and `JsConfig.presetPBO` sets `.stdListToJsArray`. The setting is also available as the knob `list=tagged|array`, and every generated file's configuration line now shows `list=…`. The snapshot checks show the generated code gives the same answers as Lean under both presets.

**How it works**
- **The tagged layout (default, `faithful` preset).** A list is cons cells: `[]` is `{ tag: 0 }` and `x :: xs` is `{ tag: 1, _1: x, _2: xs }`. I added a new JS type, `JsTy.consList`, and a small set of list operations (`JsListOp`: the two constructors plus conversions to and from arrays). All the JS passes, the printers and the `lowerTy` conversion handle them.
- **Constant lists** become one shared constant, and the empty list reuses the existing `$tag0`. The one difference from your example is naming: the constant is `$k2` and the exported definition is `() => $k2`, not `k0` and a plain constant:
  ```js
  const $tag0 = { tag: 0 };
  const $k2 = { tag: 1, _1: 1n, _2: { tag: 1, _1: 2n, _2: { tag: 1, _1: 3n, _2: $tag0 } } };
  export const ListRepr$x = () => $k2;
  ```
- **Tail sharing.** A list that ends an expression is shared, not copied. For example, `[a, "b"] ++ xs` becomes `{ tag: 1, _1: a, _2: { tag: 1, _1: "b", _2: xs } }`. A list that comes before other elements has to be copied, via `consList__append(xs, ys)` or `consList__of_array_onto(arr, tail)`.
- **Built-in list operations** such as `Array.toList` and `List.toArray` are still written for arrays. Under the tagged layout, their list arguments and results are converted at the call. A round trip is removed, so `xs.toArray.toList` compiles to just `xs`.
- **`runtime.js`** has four new functions: `consList__of_array`, `consList__of_array_onto`, `consList__append` and `consList__to_array`.
- **The array layout (`pbo` preset)** is unchanged; its outputs differ only in the configuration line.
- **User-defined list-like types** (your `MyList`) are declared datatypes, not the standard `List`, so they stay tagged unions whatever `listRepr` says. Recursive user datatypes are still refused by the JavaScript conversion, as they were before this change.

**Proofs** (in `JsTerm/Ty/Lower.lean`, no `sorry`, standard axioms only):
- `lowerTy_list_of_taggedUnion` and `lowerTy_list_of_stdListToJsArray`: which JS type `List t` gets under each setting.
- `lowerTy_data_listRepr`: a declared datatype's layout doesn't depend on `listRepr`.

**Tests**
- There's a new snapshot, `Tests/SnapshotsMy/ListRepr.lean`, showing both layouts. All snapshot outputs were regenerated: 4150 checks run under node pass and none fail. The script still exits with an error, as before this change, because some `pbo` tests use literals too big for a JavaScript number.
- `Tests/Main.lean` has 4 new Spec tests: types and knobs, literals and sharing, conversions around the list operations, and the new runtime functions under node. `lake exe tests` passes 61/61.
- `lake build` succeeds except for `LeanScript/Term/Syntax/UsageAlgebra.lean`, which fails because it imports Mathlib and the project doesn't depend on it. That was already the case and I didn't touch it. `OpsSpec`, `RefactorSpec` and `RuntimeSpec` build.

The README and the `leanscript --help` text describe the new setting. Everything is committed.

# Summary of changes for run 34eda188-bea5-45e0-bcb9-4cbe3537257f
**Why `Cand` exists:** each extern has one operation for every way its configurable Lean types (`Nat`, `Int`, `UInt64`, `Int64`, wide `BitVec`) can be represented in JavaScript, as a `BigInt` or as a `number`. For example, `lean_nat_div` has `bigint_nat__lean_nat_div : [bigint_nat, bigint_nat] → bigint_nat` and `uint53__lean_nat_div : [uint53, uint53] → uint53`. Array externs also have a generic and a typed-array version. `JsOp e t σs τ` is indexed by its signature, so these operations all have different types. The only way to put them in one list is to pack each with its signature, which is what `Cand` does. `firstOf` then compares signatures to pick the one the call needs.

**Were there duplicates?** No. I checked all 457 externs: 301 have one candidate, 127 have two and 11 have four (the other 18 are the array/thunk externs, whose candidates depend on the call's types). Within each extern the candidates' signatures are all different, and I proved this in Lean for every extern. So a call, whose types are fixed by the configuration, never has more than one candidate. The lookup already returned exactly one; the other list entries are the versions for other representations.

**What I changed:**
- **Proof that there is only one candidate.** New library `OpsSpec` (added to `lakefile.toml`, not a default target), file `OpsSpec/LookupUnique.lean`:
  - `cands_sig_nodup`: for every extern name and types, the candidates have pairwise distinct signatures.
  - `cands_unique`: two candidates of one extern with the same signature are the same candidate.
  - `lookup_unique`: when `JsOp.lookup name σs τ` finds an operation, every candidate at `σs → τ` is that operation.
  - These build with no `sorry` and use only the standard axioms `propext` and `Quot.sound`. The file takes about 2.5 minutes to build, which is why it isn't a default target.
- **Generator (`scripts/gen_js_ops.py`):**
  - It now stops with an error if an extern ever gets two operations at the same signature, and an alias pointing at an operation already listed is added only once. This way a real duplicate can't appear without notice.
  - Polymorphic array candidates used to recompute `layoutOf? (σs ++ [τ])` once per candidate and join several one-element lists. They now compute it once, with a single match (`JsTerm/Ops/Cands/Misc.lean` regenerated).
  - `JsTerm/Ops/Lookup.lean` now has a named `JsOp.cands name σs τ`, and `lookup` is `firstOf σs τ (cands name σs τ)`.
  - Running the generator again changes nothing.
- **`JsTerm/Ops/Op.lean`:** `Cand` now has a doc comment explaining the above, and there is a new `Cand.sig`, the signature of a candidate.

**Checks:** `lake build JsTerm tests OpsSpec` succeeds, and `lake exe tests` passes 57/57. The lookup's behaviour is unchanged: since signatures are unique, the reordering of the array candidates can't change which one is picked. Everything is committed.

# Summary of changes for run b0e523ce-d852-4b35-9565-27a3bace3fbd
`leanscript` no longer writes `FILE-JsTerm-pbo.txt` or `FILE-JsTerm-faithful.txt`, and I deleted the 280 existing copies from `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure`. There are none left in the project.

**What changed:**
- **`LeanScriptCli/Main.lean`:** the line that wrote the grammar dump for each preset is gone. If an old `FILE-JsTerm-{pbo,faithful}.txt` is next to the output, the tool now deletes it, so running it again on an older tree cleans up after itself. They are also still on the `--functions-only` cleanup list. I took them out of the module doc and the `--help` text. The help lines for `FILE-pbo.js` and `FILE-faithful.js` now say what each preset means: numbers instead of BigInt for `pbo`, BigInt everywhere for `faithful`.
- **`scripts/leanscript-snapshots.sh` and `README.md`:** these no longer list the removed files.
- **Kept:** the code that prints the grammar, in `JsTerm/Syntax/Pretty.lean` and the type renderings, because `Tests/Main.lean` uses it. It just isn't written to a file any more.

**Checks:**
- `lake build leanscript` succeeds.
- I ran the tool on `Tests/SnapshotsMy/AppArity.lean` with a stale `AppArity-JsTerm-pbo.txt` next to it. It deleted that file and wrote no dump. Its other outputs differed only in the file path in the header line, because I ran it from a different directory. I restored those files, so no other snapshot changed.
- `lake exe tests` passes 57/57.

Everything is committed.

# Summary of changes for run eb85d3b2-900e-4286-bea3-cb753ade3aeb
You're right that `Number(x)` on an `int53` does nothing: it's the identity. But the identity is also wrong here, so this was a bug, not just a wasted call. A `float32` value is supposed to be a number already rounded to single precision by `Math.fround`, and `Int64.toFloat32` rounds. For example, `(16777217 : Int64).toFloat32` is `16777216` in Lean, but the generated JavaScript returned `16777217`, which isn't a single-precision value at all. The template should have been `Math.fround(x)`. The cause is `conv_value` in `scripts/gen_js_ops.py`, which handled `float` and `float32` targets the same way.

**Other inlined operations.** I checked every template in `JsTerm/Ops/Template.lean` that is the identity or calls `Number`, `BigInt` or `Math.fround`. Six were wrong:
- `int53__lean_int64_to_float32` and `uint53__lean_uint64_to_float32` (both did nothing with `Number(x)`) and `int32__lean_int32_to_float32` and `uint32__lean_uint32_to_float32` (both the identity). These are now `Math.fround(x)`.
- `bigint_int__lean_int64_to_float32` and `bigint_nat__lean_uint64_to_float32` used `Number(x)`, which gives a double, not a single. `Math.fround(Number(x))` wouldn't fix it, because it rounds twice: `2^63 + 2^39 + 1` would come out as `2^63` instead of `2^63 + 2^40`. They are now `runtime.js` functions using a new helper, `$bigToF32`, which rounds once.

All the other templates are correct, and none does nothing:
- 8- and 16-bit integers → float32 are exact, so the identity is right.
- Integer `number` → `Float` is exact.
- `Number(bigint)` → `Float` rounds correctly.
- Every other `Number` or `BigInt` call changes the JavaScript type.

**`runtime.js`.** No function converts a value to the type it already has, and every function returning a `float32` rounds its result. Some `uint53`/`int53` functions go through `BigInt` (multiply, shift left, bitwise and/or/xor, the hash mix). That's needed for 64-bit wrap-around and for bit operations above 32 bits. Two functions do unneeded work, and I left them unchanged because `RuntimeSpec` models and proves them as written:
- `uint53__lean_uint64_neg` always throws for any argument other than 0.
- `uint53__lean_uint64_complement` always throws.

**Changes:**
- `scripts/gen_js_ops.py` and `scripts/js_ops_inline.json` now produce the corrected templates.
- `runtime.js` has `$bigToF32` and the two new exported functions.
- The generated files `Template`, `Inlinable`, `Imported` and `Cands/{SInt,UInt}` are regenerated; running the generator again changes nothing.

**Checks:**
- In a one-off script (not part of the test suite), I compared about 19,800 values, including values at and next to every rounding midpoint, against Lean's `UInt64.toFloat32` and `Int64.toFloat32`. The new code had 0 mismatches. The old code had 18,670, and `Math.fround(Number(x))` had 1,201.
- New regression tests:
  - seven cases in `Tests/Main.lean` ("runtime.js computes what Lean computes");
  - a new snapshot test, `Tests/SnapshotsMy/IntToFloat32.lean`, with 20 checks per preset. With the old templates, 8 of the 20 `pbo` checks fail.
- `lake exe tests` passes 57/57.
- The snapshot suite passes 4042 checks with 0 failures, and no existing snapshot changed. The snapshot script still exits with an error, but only because some existing `pbo` tests use literals too large for a JavaScript number; that is unrelated to this change.
- `lake build` fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib, a library the project doesn't depend on. I didn't touch that file.

The full write-up is in `proposals/IntToFloat32Conversions.md`. Everything is committed.

# Summary of changes for run 8ddc87fc-4a97-4d7a-b7cb-d49aca150751
**Short answer: no, `JsOpImported` (398 constructors) and `JsOpInlinable` (219) don't need to be split at their current size.** I measured this with the Lean profiler. The full write-up is in `proposals/JsOpSizeAssessment.md`.

**Why splitting isn't needed:**

1. **The "tag too big" limit isn't reached.** Compiled code can't build a constructor whose index is above 243 if it has fields. I re-checked this on the current toolchain: `.c243 1` compiles, `.c244 1` fails, and a constructor with no fields at index 249 is fine. `scripts/gen_js_ops.py` already puts the constructors with fields first, so only indices 0–32 (`JsOpImported`) and 0–12 (`JsOpInlinable`) have fields.

2. **No `rfl`/`decide` proof reduces `JsOp` values.** This is why `LeanInitPureExtern` did have to be split: kernel reduction of a match costs time in proportion to the number of constructors. The JsTerm pipeline only runs as compiled code, where a `match` is a jump on the tag and `name` is an array lookup. So the number of constructors doesn't slow down running code.

3. **Compile time is moderate.** Building `Imported.lean` takes about 17 s and `Inlinable.lean` about 10 s; roughly 3–3.5 s of each is loading imports. Declaring the first 100, 200 and 398 constructors of `JsOpImported` took about 1.2 s, 3.0 s and 8.5 s, so the cost grows a bit faster than linearly.
   - Splitting it into about 4 groups would save roughly 3–4 s of CPU, and only when the generator is re-run.
   - None of the files that use these types (`Template`, `Op`, `Cands/*`, `Lookup`, the in-place passes, `Hoist`, `Print/Mini`, `Syntax/Basic`) has a declaration above 0.3 s, except `template` at about 1.5 s. Their time goes mostly into loading imports, which a split wouldn't change.

**When to split:**
- more than 244 constructors with fields;
- proofs that evaluate `JsOp` values by `rfl` or `decide`;
- `JsOpImported` growing to around 800 or more constructors.

If that happens, the note describes a split following the existing `LeanInitPureExtern` pattern: one group per lookup group, a wrapper type, and shorthand definitions so existing patterns keep working.

**One code change:** `scripts/gen_js_ops.py` now stops with an error if either type ever has more than 244 constructors with fields, so the tag limit can't be exceeded without notice. Re-running the generator produces identical Lean files.

No Lean code changed, so there was nothing new to build. The note and the generator change are committed.

# Summary of changes for run 69593980-3404-45a2-931b-86343b876529
I proved in Lean that removing the duplicated `number` literal code changed neither the JavaScript tree nor the source text it produces, for every `Float` and every `Float32`. I also turned the other duplications I named last time into theorems. Everything builds with no `sorry`. The main theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

The proofs are in a new library, `RefactorSpec` (added to `lakefile.toml`). It contains a copy of the removed code, under `MoreJs.Legacy`, so old and new can be compared.

**Results:**
- **Printed JavaScript is unchanged** (`RefactorSpec/NumberPrint.lean`):
  - `numberExpr_ofFloat_eq_legacy` and `numberExpr_ofFloat32_eq_legacy`: for every `Float` or `Float32`, the new printer builds exactly the same JavaScript syntax tree as the removed one.
  - The general form, `numberExpr_eq_legacy`, covers every unpacked float whose mantissa is below 2^53. That limit is needed: the removed code only stripped up to 400 trailing zeros, so for huge mantissas the two versions really do differ.
- **Supporting facts** (`RefactorSpec/NumberStrip.lean`):
  - The old zero-stripping equals `JSNumber.stripZeros` on any positive number with fewer than 400 trailing zeros.
  - `shortestDecimal` only ever produces such numbers when the mantissa is below 2^53.
  - Every unpacked `Float` or `Float32` has a mantissa below 2^53.
- **Source text is unchanged** (`RefactorSpec/NumberSource.lean`):
  - `numberSource_eq_legacy` and `float32Source_eq_legacy`: the new spelling equals the old one, including `1e+21`, `-0`, `NaN` and `-Infinity`.
  - The core step, `withExponentSign_renderDecimal`: the decimal writer of the JavaScript trees, `JSNumber.renderDecimal`, plus the `+` added to a positive exponent, is exactly the removed `decimalString` for every positive mantissa.
- **The other duplications** (`RefactorSpec/Duplicates.lean`):
  - `neList_equiv_nonEmptyList`: the removed `NEList` and your `NonEmptyList` convert into each other and back without change, keeping the same elements.
  - `WFFnVar` and `JsMem` convert into each other and back without change, via `wfFnVarToJsMem` and `jsMemToWFFnVar`.
  - `lookup_eq_find?_map`: the hand-written lookup `(l.find? (·.1 == n)).map (·.2)` is `List.lookup n l`.
  - `JSNumber.repeatChar` is `String.pushn`, and `JSNumber.powNat` is `^`.
  - That `JSNumber.digitChar` equals `Nat.digitChar` below 16 was already proved in your project (`LiteralPrintSpec.JSNumber.digitChar_eq`), so I didn't repeat it.

**Code changes needed for the proofs:**
- `withExponentSign` in `JsTerm/Syntax/NumberLit.lean` now works on the character list instead of using `splitOn`, which made it provable. Its output is the same; the full build, `lake exe tests` (57/57) and the snapshot checks (4002 passed, 0 failed, no snapshot file changed) all still pass.
- `smallNat?_pos` moved from `NumberPrint.lean` to `NumberStrip.lean` so both proof files can use it.
- `NumberPrint.lean` and `NumberSource.lean` are not module files, because the files they import (the printer and `LiteralPrintSpec`) are not modules. `NumberStrip.lean` and `Duplicates.lean` are.

The Properties table has four new entries: the `NumberForm` definition, and the three results above, marked proved. Everything is committed.

# Summary of changes for run 6152da32-29f0-462a-8dd7-2f58d6ef43b2
I made the generated JavaScript smaller by improving the Term → JsTerm conversion passes. I did not change `Term.optimize`: the extra rewrites I considered there, such as inlining beta-redexes, would have meant a lot of new proof work on top of `Term.optimize_eval`. So that optimiser and its proofs are exactly as before, and all the new work is in the JsTerm passes. Those passes are checked by the snapshot tests, not proved.

What changed:
- **`JsTerm/Passes/Simplify.lean`:** array spreads are now flattened through list↔array conversions. A list built from literals and an array becomes a single literal, e.g. `["a", ...arr, "b"]`.
- **`JsTerm/Passes/Cleanup.lean`:**
  - When it inlines a constant that is used once, it now respects the evaluation order of inlined operators: operands of `a && b` or `c ? a : b` may not be evaluated. It also lets that inlining pass over pure operations that cannot throw.
  - When the value of a record or union is known, it picks the field or union arm directly.
  - It simplifies conditionals: `(c ? false : true) ? a : b` becomes `c ? b : a`, `c ? a : a` becomes `a`, and `x === y ? y : x` becomes `x` on non-float types.
  - It drops `+0`, `*1` and `-0` on the integer representations.
- **New `JsTerm/Passes/InlineConsts.lean`** (run from `mkModule` after hoisting) inlines module constants whose values are known:
  - a closure that is passed as an argument or called is written out where it is used (up to 4 uses), then beta-reduced;
  - a record or union of constants is read directly where it is used;
  - a block closure called once in tail position is inlined there.
  Functions this changes go through in-place array updates and the clean-ups again. A closure equal to an exported function still just refers to that function. For example, `test5` in `Tests/SnapshotsMy/ScalarRepl.lean` is now `export const test5 = uint53__lean_nat_add;`.
- **New snapshot test:** `Tests/SnapshotsMy/InlineClosures.lean` (40 checks).

**Results:** I compared the `-pbo.js` and `-faithful.js` snapshots that existed at the start of this round, ignoring comments, imports and blank lines:

| | before | after |
| :-- | --: | --: |
| lines | 3437 | 3387 |
| bytes | 108840 | 106540 |
| `const`s | 1568 | 1511 |
| module constants (`$k`) | 58 | 39 |
| arrows | 947 | 922 |

16 test programs' output changed.

**Checks run:**
- Regenerating all snapshots passes 4002 node checks with 0 failures. The script still exits with status 1, as before, because of the tests that deliberately panic.
- `lake build JsTerm leanscript tests LeanScriptCli TermTests TyTests RuntimeSpec` succeeds.
- `lake exe tests` reports 57/57 passed.
- No `sorry` in the pass files.

The README now describes the new passes and gives these numbers. I also corrected the comment in `Tests/SnapshotsMy/ShareFuns.lean`, and the Properties table has an updated row for the clean-up passes and a new row for the constant inlining, both marked as test-checked rather than proved. Everything is committed.

# Summary of changes for run 98d27366-ec64-4629-a737-71f7610e83dd
I made `Term.optimize` and the Term → JsTerm → JavaScript conversion produce smaller JavaScript. The optimizer change is proved correct in Lean. The JavaScript changes are checked only by the snapshot tests, because `JsTerm` has no formal semantics to prove them against.

**`Term.optimize` (proved).** `if c then ret a else ret b` now becomes `ret (c ? a : b)`, using the existing pure conditional (`Term.condRet` in `LeanScript/Term/Optimize/Cse.lean`). This is skipped when `a` or `b` is already a conditional, so long chains of `?:` are not built. The new lemma `Term.condRet_eval` proves this step leaves `Term.eval` unchanged, and I updated the proofs of `Term.optimize_eval` and `Term.numCalls_optimize` to use it. There is no `sorry`, and `#print axioms` for these theorems shows only `propext`, `Classical.choice` and `Quot.sound`.

**JavaScript output (tested, not proved).**
- **Fields read in place:** a field that is read once, outside loops and closures, is now read as `p._1` instead of being unpacked into a `const` first. This only happens when the record is a constant, or a mutable variable that is not reassigned afterwards. Example: `(a, b) => ({ _1: a._1 + b._1, … })`.
- **One-sided updates:** `x = c ? a : x;` is now written `if (c) { x = a; }`.
- **Rebuilt values:** the existing check for a union arm that rebuilds the value it just unpacked now also works inside a `?:` expression (`Cleanup.lean`).
- **Sharing functions** (new `JsModule.shareFuns` in `Hoist.lean`, run when the module is assembled):
  - a module-level closure that equals an exported function is dropped, and the function is used instead. This is skipped if another constant reads it while the module loads, so nothing is read before it is defined.
  - an exported function equal to an earlier one is written `export const g = f;`.
  - an exported function that only passes its parameters, in order, to a runtime function is written as that function, e.g. `export const add = uint8__lean_uint8_add;`.

**Results** on the `-pbo.js`/`-faithful.js` snapshots, not counting comments, blank lines or the new test file:

| | before | after |
| :-- | --: | --: |
| lines | 4192 | 3738 |
| bytes | 133990 | 120319 |
| record destructurings | 140 | 30 |
| `$k` module constants | 74 | 56 |
| `if`s | 240 | 196 |

**Checks.** I regenerated all snapshots, and all 3922 checks pass: the previous 3860, plus 62 from a new file, `Tests/SnapshotsMy/ShareFuns.lean`, which exercises the in-place field reads, the `?:` returns, the one-sided update and both kinds of aliases. The snapshot script still exits with status 1 because of the panics that were already expected ("literal too big", `mypanic`). `lake build JsTerm leanscript tests LeanScriptCli TermTests TyTests RuntimeSpec` succeeds with no warnings, and `lake exe tests` passes 57/57.

**Existing build failure.** Building the whole `LeanScript` library, which is one of the default targets, fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`: it imports Mathlib, which this project does not depend on. That file is unchanged since the initial commit, and I did not touch it.

I added a paragraph on these changes to `README.md` and updated the Properties table: the optimizer row stays proved, and there is a new tested-only row for `JsModule.shareFuns`. All work is committed.

# Summary of changes for run 9fac2b3b-5bb8-4b18-9826-4c32388c445a
I improved `Term.optimize` and the Term → JsTerm conversion so the generated JavaScript is smaller and the loops are simpler. The optimizer change is proved correct. The JavaScript changes are only checked by tests: `JsTerm` has no formal semantics, so there is nothing to prove them against.

**Term optimizer (proved).** `Term.reuseRecord` in `LeanScript/Term/Optimize/FieldsWalk.lean` used to drop a repeated record case analysis only when that left the level of its body unchanged. When dropping it would change the level, it now keeps the case analysis but renames its fields to the ones already known. The helpers for this, `FieldVars.toRenKeep` and `FieldVars.Holds.agreeKeep`, are in `Fields.lean`. This stops a record from being taken apart twice under different names. I updated the proofs that the optimizer leaves `Term.eval` unchanged and never adds calls. They build without `sorry`, and `#print axioms LeanScript.Term.optimize_eval` shows only `propext`, `Classical.choice` and `Quot.sound`.

**New JsTerm passes (tested, not proved).** There are three new files, `JsTerm/Passes/Unbox.lean`, `Contify.lean` and `Tco.lean`. A driver, `tidy`, repeats them until the output stops changing (at most 6 rounds); `termToJs` calls it before `inPlace`. They:
- keep accumulators of a one-constructor union unboxed;
- replace a record accumulator with one mutable variable per field;
- merge a join point that is jumped to only once into its caller;
- turn a local closure that is only called in tail position into a join point;
- move assignments up and inline literals;
- beta-reduce a returned closure that is applied straight away;
- merge mutable variables that only copy each other, and drop constants nothing uses;
- turn the closure chains a tail-recursive function builds as a loop accumulator (`acc = (x) => a(f(x))`) into a loop over its parameters (`x = f(x)`), including a version with early return.

**Smaller changes.** The printer now leaves out the loop counter in a last iteration that doesn't use it. `Cleanup.lean` now spots a rebuilt union even when it is nested inside other statements. There is a new snapshot, `Tests/SnapshotsMy/LoopState.lean`, with small loop examples.

**Results.** On the `-pbo.js`/`-faithful.js` snapshots, not counting comments, blank lines or the new snapshot:

| | before | after |
| :-- | --: | --: |
| lines | 4229 | 4073 |
| bytes | 135942 | 130955 |
| record destructurings | 200 | 138 |
| `.tag` reads | 50 | 26 |
| `const`s | 1791 | 1667 |

All snapshots were regenerated and all 3860 snapshot checks pass. The snapshot script still exits with status 1, because of panics that were already expected: "literal too big" in the `PrimOpInt0*Configurable` tests and `mypanic` in `CasePartial`. `lake build JsTerm leanscript tests LeanScriptCli TermTests TyTests RuntimeSpec` succeeds, and `lake exe tests` passes 57/57.

I added a section on the new passes to `README.md` and updated the Properties table. All work is committed.

# Summary of changes for run c23dc253-fc6e-49fb-952d-599dcf6008dd
I improved both `Term.optimize` and the Term → JsTerm → JavaScript conversion. The generated JavaScript is now shorter, and all 3824 snapshot checks still pass.

**What changed in the output.** Across all snapshots (`Tests/SnapshotsMy`, `Tests/SnapshotsPBOPure`, both presets, all regenerated and committed):
- lines: 6949 → 5477
- bytes: 163888 → 137190
- statements: 3468 → 2513
- record/union destructurings: 310 → 200
- copies like `const y = x;`: 222 → 38 (the ones left are needed, e.g. values captured by closures inside loops)
- self-assignments `x = x;`: 4 → 0

**`Term.optimize` (proved).** It is now `(t.simp.widenFields.reuseFields []).cseWalk.dce`:
- **Field reuse:** a record that has already been taken apart, or was rebuilt from known fields, reuses the fields bound the first time instead of taking the record apart again (`Fields.lean`, `FieldsWalk.lean`).
- **Unused fields:** dead-code elimination now re-annotates the fields of each case analysis with how often they are used, so a field nobody reads is not taken apart (`Reannot.lean`, `Term.reannotFields`).

`Term.optimize_eval`, `Term.optimizeN_eval`, `Term.numCalls_optimize`, `Term.reuseFields_eval` and `Term.reannotFields_eval` are proved without `sorry`, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**JsTerm clean-ups (tested, not proved).** These passes are in the new file `JsTerm/Passes/Cleanup.lean`. They run after the conversion (`termToJs`) and again after constants are moved to the top of the module (`mkModule`). There is no formal proof for them because JsTerm has no formal semantics.
- **Copy propagation:** removes copies such as `const k$1 = $k1;` and `const y = x;`. A copy of a mutable variable is removed only when that variable is never reassigned afterwards and the copy is not captured by a closure.
- **Self-assignments:** `x = x;` is dropped.
- **Rebuilt unions:** in a case analysis on a variable, an arm that rebuilds the value it just took apart (`acc = { tag: 0, _1: f }` in the tag-0 arm) uses the variable instead.
- **Unused pattern fields:** fields that are bound but never read are left out of the pattern.
- **One-use constants (last pass):** a constant read once, by the next statement, is inlined there (`const x = f(y); return g(x);` → `return g(f(y));`). This only happens if nothing that could have an effect or throw is evaluated before the read, so evaluation order is unchanged. The pass does nothing if any closure assigns a captured mutable variable; the backend never produces such a closure.

**Printer changes.**
- **`if` statements:** no empty `else`; an empty `then` becomes a negated test (`x.tag !== 0`); no `else` after a `return`/`throw`/`break`/`continue`.
- **Returns and conditions:** `if (c) return true; else return false;` → `return c;`, and branches returning names or literals become `return c ? a : b;`. `c ? true : false` → `c`, and `c ? false : true` → the negated test.
- **Identical union arms** are written once, with no test. The arms are compared as generated statements.
- **Join points:** one that is assigned once becomes a `const`.
- **Arrows:** a body that prints as a single `return` becomes `(x) => e`.

**Checks run.** `lake build JsTerm leanscript tests LeanScriptCli TermTests TyTests RuntimeSpec` succeeds, and `lake exe tests` passes 57/57. There is no `sorry` in the optimizer or JsTerm files.

`README.md` now describes the new optimizer steps, the clean-ups, the printer changes and these numbers. I added two rows to the Properties table: the clean-up passes (tested, not proved) and the extended optimizer theorem (proved).

# Summary of changes for run b930ce8d-207d-4a52-bb68-04dd7543f37d
This request was already done in the previous run, whose changes are in the project. I rechecked that it still holds, and the only thing I changed this session was an out-of-date planning doc.

**What `runtime.js` has, matching `JsTerm/Ops`**
- Every array update comes as a pair: `…_immutable`, which returns an updated copy and leaves the argument unchanged, and `…_mutable`, which updates the array in place and returns it.
- The updates are `push`, `pop`, `set`, `swap`, `fset` and `fswap`. `set` and `swap` exist for both index types, `bigint_nat__…` and `uint53__…`, and so do `fset` and `fswap`.
- Both functions in a pair have the same signature, and their names match the `JsOpImported` constructors in `JsTerm/Ops/Imported.lean`. The generated `JsOpImported.toMutable?` pairs them: 10 updates have both versions.
- In `JsTerm/Ops`, the `_mutable` operations are the only ones marked `effectful`; everything else is `pure`.
- **One exception:** `push` and `pop` on a typed array (`typedArray__lean_array_push_immutable`, `typedArray__lean_array_pop_immutable`) only have the immutable version, because a typed array can't grow or shrink.
- String operations have no mutable version, because JavaScript strings are immutable.
- Inside the runtime's own functions, `let` is used only for variables that are reassigned; everything else is `const`.

**Checks run this session**
- The build of `JsTerm`, `leanscript`, `tests`, `LeanScriptCli` and `RuntimeSpec` succeeds with no warnings.
- `lake exe tests` passes 57/57. This includes:
  - a check that every `_mutable` function has an `_immutable` partner;
  - a check of `toMutable?` and of which operations are marked effectful;
  - a `node` run showing that each immutable function leaves its argument unchanged, each mutable one returns its argument, and both give the same array.
- Running `scripts/gen_js_ops.py` again changes nothing, and `scripts/annotate_runtime.py --check` reports that the `runtime.js` comments are up to date.
- This is checked by tests, not by a Lean proof. The Properties table row stays in progress, with the new checks noted in its comments.

**Change this session:** in `proposals/JsTermReviewPlan.md`, the status table still said `lean_array_fset` was just an alias of `set`, and gave the old count of 388 operations. I updated it to describe the current pairing and the 398 operations. This is committed.

If you meant something else by "mutable and immutable variables", such as mutable and immutable variables in the generated JavaScript, tell me and I'll work on that instead.

# Summary of changes for run 247c4764-15d3-4d16-abe4-9e7ca3367cae
I read your request as asking for mutable and immutable *variants* (not variables): every array update in `runtime.js` should now come as an `…_immutable` / `…_mutable` pair whose names and signatures match the operations in `JsTerm/Ops`, paired by `JsOpImported.toMutable?`. That was the unfinished part of §7.2 of `proposals/JsTermReviewPlan.md`. This is checked by tests, not by a proof.

**What changed in `runtime.js`**
- **`fset` / `fswap` (`Array.set` / `Array.swap`, whose bounds are proved):** these were only copying aliases of `set_immutable` / `swap_immutable`. They are now real functions, `bigint_nat__…` and `uint53__lean_array_fset_immutable` / `_mutable` and `lean_array_fswap_immutable` / `_mutable`. They don't check bounds, because Lean has already proved `i < a.size`.
- **`push` / `pop` split by layout:**
  - On generic arrays: `array__lean_array_push_immutable` / `_mutable` and `array__lean_array_pop_immutable` / `_mutable`, each pair with the same signature.
  - On typed arrays: new `typedArray__lean_array_push_immutable` and `typedArray__lean_array_pop_immutable`, with no mutable version, since a typed array can't grow or shrink.
  - This removes the last `Array.isArray` run-time test from the runtime.
- **Header:** there is now a table listing every pair. I also moved three stray doc comments back onto the functions they describe.

**Generated and Lean code**
- `scripts/gen_js_ops.py` now treats `fset` / `fswap` as updates and splits `push` / `pop`. The script now fails if an update's `_mutable` function is missing from the runtime.
- The regenerated `JsTerm/Ops/Imported.lean` has 398 imported operations, up from 388. `toMutable?` now pairs all 10 updates that have a mutable version.
- In `JsTerm/Ops/Cands/Misc.lean`, `lean_array_fset` / `lean_array_fswap` now go to their own operations.
- The in-place pass (`JsTerm/Passes/InPlace/Linear.lean`) now counts `fset` / `fswap` as updates, so they are done in place when the array is owned. The docs are updated in `JsTerm/Ops/Basic.lean`, `JsTerm/Passes/InPlace.lean` and `README.md`.
- `scripts/annotate_runtime.py` has been rerun, and `--check` reports the `runtime.js` comments are up to date.

**Checks**
- **Build:** `lake build JsTerm leanscript tests LeanScriptCli RuntimeSpec` succeeds with no errors or warnings.
- **`lake exe tests`:** 57/57 pass. The new tests are:
  - Every `_mutable` operation has its `_immutable` one. Every `_immutable` one has a `_mutable` one, except typed `push` / `pop`.
  - `toMutable?` pairs the right operations, and only the mutable ones are effectful.
  - A node run over 11 cases shows that each immutable function leaves its argument unchanged, each mutable one returns its argument, and both give the same array (including typed arrays and out-of-bounds indices). This test passes silently if `node` is not installed.
  - An owned array gets `uint53__lean_array_fset_mutable`.
- **`scripts/leanscript-snapshots.sh`:** 3806 passed, 0 failed, and no existing snapshot changed. It still exits 1, as before, because of the deliberate panic and literal-too-big inputs.
- **New snapshot `Tests/SnapshotsMy/ArrayFSet.lean`:** all 18 checks pass. The generated code shows `fset_mutable` / `fswap_mutable` on an owned array, the immutable versions on a shared array or a parameter, and typed `push` / `pop`.

The result is in the Properties table as a tested property (in progress, not proved). All work is committed.

# Summary of changes for run 696172ff-3b3e-4f05-a9f9-e308b76e4c21
`JsTerm/` had already been split into groups (`Ty/`, `Ops/`, `Syntax/`, `Passes/`, `Lower/`, `Print/`) before this session. I split the remaining large hand-written files further and grouped the new pieces into subdirectories. The sets of definitions, theorems and instances before and after are identical (I diffed them), so no definition changed; they only moved.

**Checks, all passing**
- `JsTerm`, `leanscript`, `tests` and `LeanScriptCli` build with no warnings.
- `lake exe tests` passes 55/55.
- `scripts/leanscript-snapshots.sh` reports 3806 passed and 0 failed, and no snapshot file changed.
- Running `scripts/gen_js_ops.py` a second time changes nothing.
- `scripts/annotate_runtime.py --check` reports the `runtime.js` comments are still up to date.

**What was split**
- **`Ty/Basic.lean`** (447 lines) became three files:
  - `Ty/Defs.lean`: `JsTerminalTy`, `JsTy` and the typed arrays.
  - `Ty/DecEq.lean`: the hand-written decidable equality.
  - `Ty/Basic.lean`: names, renderings, `JsNatTy` and `JsArrayLayout`. It imports the other two, so files that import it still work.
- **`Syntax/Vars.lean`** (392 lines) is now a short summary module importing `Syntax/Vars/Rename.lean`, `Subst.lean` and `Occs.lean`.
- **`Passes/InPlace.lean`** (494 lines) was split as follows:
  - `Passes/InPlace/Linear.lean`: the array operations and linear variables.
  - `Passes/InPlace/Collect.lean`: the definitions of the variables and the rebuilt body.
  - `Passes/InPlace.lean`: keeps the explanation of the pass plus `greatestFix` and `inPlace`.
- **`Print/Mini.lean`** (473 lines) was split as follows:
  - `Print/Mini/Basic.lean`: helpers, the printer's state and where an iteration ends early.
  - `Print/Mini/Block.lean`: expressions and blocks.
  - `Print/Mini.lean`: functions and modules.
  - A new `JsTerm/Print.lean` summary module imports the group, like the other groups have.
- **`Ops/Inlinable.lean`** (702 lines, generated): `scripts/gen_js_ops.py` now writes `JsOpInlinable.template` to a separate generated file, `Ops/Template.lean`, leaving `Ops/Inlinable.lean` at 480 lines. All other generated files are unchanged. `Syntax/Basic.lean` and `Ops.lean` import the new module.

**Docs:** I updated the `README.md` layout table and the module table in `Ops/Basic.lean`. One path reference in `scripts/annotate_runtime.py` now points to `Ty/Defs.lean`.

**Still large:** the only hand-written file over 420 lines is `Syntax/Basic.lean` at 419. The largest file is still the generated `Ops/Imported.lean` at 844 lines, almost all of it the single `JsOpImported` inductive, which can't be split across files. The generated `Ops/Cands/*` files are at most 571 lines.

All work is committed.

# Summary of changes for run 4f9140d4-5dc9-4bc9-8472-0c0cbc1c3532
I reorganized `JsTerm/` into subdirectories by group and split its large files. The refactor changes no definitions: the same declarations are just in new places. Builds pass for `JsTerm`, `leanscript`, `tests`, `TyTests`, `TermTests` and `LeanScriptCli` with no warnings. `lake exe tests` passes 55/55. `scripts/leanscript-snapshots.sh` reports 3806 passed and 0 failed, and no snapshot file changed.

The script itself still exits with status 1. That comes from inputs it is meant to reject: the literal-too-big errors in `PrimOpInt0{2,3}Configurable` and the deliberate `mypanic` panics. A plain `lake build` of all default targets still fails on `LeanScript/Term/Syntax/UsageAlgebra.lean` ("unknown module prefix 'Mathlib'"). I did not touch that file.

**New layout**
- `Ty/`
  - `Config.lean`
  - `Basic.lean`: `JsTerminalTy`, `JsTy`, layouts. It no longer depends on the configuration.
  - `Lower.lean`: `lowerScalarPrim`, `lowerArrayPrim`, `lowerTy`, split out of the old `Ty.lean`.
- `Ops/` (replaces the 1593-line `Ops.lean` and the 2356-line `OpsLookup.lean`)
  - `Basic.lean`, hand-written: `Effectfulness`, `MayThrow`, `JsInline`, `jsSafeName`.
  - Generated: `Imported.lean` (`JsOpImported`, `extraArgs`, `toMutable?`) and `Inlinable.lean` (`JsOpInlinable`, `template`).
  - `Op.lean`, hand-written: `JsOp`, `Cand`, `firstOf`, …
  - Generated `Cands/{Nat,UInt,SInt,Float,String,Misc}.lean`: each group's per-extern candidate lists plus its own dispatch function.
  - Generated `Lookup.lean`: a short `JsOp.lookup` that tries the groups in turn. The groups don't overlap, so its results are unchanged.
- `Syntax/`
  - `NumberLit.lean`
  - `Basic.lean`: the grammar. It now imports only the operation types, not the whole lookup.
  - `Vars.lean`
  - `Pretty.lean`: the `-JsTerm-*.txt` dump, split out of the old `Syntax.lean`.
- `Passes/`: `Simplify.lean`, `InPlace.lean`, `Hoist.lean`.
- `Lower/`
  - `Extern.lean`
  - `Basic.lean`: literals, `ConvM`, `Ref`/`Names`, casts and builders.
  - `FromTerm.lean`: the conversion itself and `termToJs`, split out of the old `FromTerm.lean`.
- `Print/Mini.lean`: the old `PrintMini.lean`.
- Summary modules `JsTerm/{Ty,Ops,Syntax,Passes,Lower}.lean` each import their whole group.

The largest file is now `Ops/Imported.lean` at 844 lines, most of it the single `JsOpImported` inductive, which can't be split further. Every other file is under 710 lines.

**Generator**
- `scripts/gen_js_ops.py` now writes the generated `Ops/` modules above.
- The constructors and candidate lists it produces are the same as before; I compared them line by line.
- Running it again changes nothing.
- `scripts/annotate_runtime.py --check` still reports the `runtime.js` comments as up to date.

**Other updates**
- Imports in `LeanScriptCli/Main.lean`, `LeanScriptCli/Check.lean`, `Tests/Main.lean` and the disabled `LeanScriptCli/RecCalls.lean_`.
- Path references in `README.md` (the layout table now describes the new directories), `NOT_IMPLEMENTED.md`, `runtime.js`, `scripts/annotate_runtime.py` and doc comments.
- I left the older design notes in `proposals/` as they were, so they still use the old paths.

Everything is committed.

# Summary of changes for run d3b7d4c7-a546-4b4a-b067-c43210f6b01a
I added `scripts/annotate_runtime.py` and ran it: each of the 422 exported functions in `runtime.js` now has a comment on top giving the types of its arguments and its result.

**Where the types come from.** The script imports `scripts/gen_js_ops.py` and uses the same signatures that go into `JsTerm/Ops.lean`. So the types are the ones the backend actually calls each function at. It adds JSDoc tags to the end of each function's existing description, for example:

```
/** `Array.get!Internal`: `a[i]`, or the default `d` out of bounds.
 *  @template A, E the array layout `l : JsArrayLayout A E`: `A` is `array E`, or `typedArray t` with `E` = `terminal t.leaf`
 *  @param {E} d `E`
 *  @param {Array<E>|TypedArray} a `A`
 *  @param {bigint} i `bigint_nat`
 *  @returns {E} `E` */
```

Each tag gives the JavaScript type in braces, followed by the `JsTy` representation, which says more (a `uint53` and an `int16` are both `number`s). Other types are written like this:
- records as `{_1: …, _2: …}` and unions as `({tag: 0}|{tag: 1, _1: string})`;
- substrings and string slices as `[string, number, number]`;
- functions as `function(string): boolean`;
- thunks as `Thunk<α>`.

Polymorphic operations also get a `@template` line. For the typed-array `mk_array` functions, the extra first parameter `C` (the typed-array constructor) is documented too. An alias (`export const a = b;`) gets the types of its own signature, using `b`'s parameter names.

**Running it:**
- `python3 scripts/annotate_runtime.py` rewrites `runtime.js`. You can run it again after changing a signature: it first removes the tags it wrote before, so nothing is duplicated.
- `python3 scripts/annotate_runtime.py --check` changes nothing and exits 1 if the comments are out of date.
- The script stops with an error if a function's parameter count in `runtime.js` doesn't match its signature. There were no mismatches and no exported function without a signature.
- The private `$…` helpers have no signature in `JsTerm/Ops.lean`, so they are left as they were.

**Checks:**
- With comments removed, the code in `runtime.js` is the same as before (only blank lines differ).
- `node --check runtime.js` passes, and node can import the module and call its functions.
- Running `gen_js_ops.py` again leaves `JsTerm/Ops.lean` and `JsTerm/OpsLookup.lean` unchanged, so the detection of which operations may throw is unaffected.
- Running the script a second time gives the same file.
- I did not rebuild or run the Lean test suite. No Lean file changed, and the tests only look for the `export const …` lines, which are unchanged.

I also added a short note to the header of `runtime.js` pointing to the script, and updated the `runtime.js` and `scripts/` rows of the `README.md` layout table. Everything is committed.

# Summary of changes for run 062e2ff6-504b-4c8d-b37c-06125785d425
I refactored `runtime.js` and formalized the refactor in Lean. Everything builds with no `sorry`.

**Runtime refactor.** Each function in `runtime.js` now handles one representation and has no `typeof` tests or `BigInt()` coercions. For example, `bigint_nat__lean_array_set` now works on the `BigInt` index directly. I removed the helpers `$idx`, `$count`, `$capNat` and `low53` and added a few small private ones for 53-bit bitwise operations, `log2` and overflow. 22 operations can no longer throw, so I regenerated `JsTerm/Ops.lean`; the set of operations is otherwise unchanged.

Checks that passed:
- `lake build JsTerm leanscript tests`
- `lake exe tests`: 55/55
- `scripts/leanscript-snapshots.sh`: 3806 passed, 0 failed, snapshot files unchanged
- a one-off node script comparing old and new on all 388 operations; that script is not in the repo.

**Formalization.** This is a new library, `RuntimeSpec` (`lake build RuntimeSpec`), with three files:
- `RuntimeSpec/Model.lean`: a Lean model of the JavaScript semantics the runtime relies on (`BigInt`, safe-integer numbers, 32-bit operators).
- `RuntimeSpec/Runtime.lean`: the new functions written out in Lean, plus the old versions of those whose shape changed.
- `RuntimeSpec/Correct.lean`: 42 theorems, all proved. They show:
  - the new functions compute the matching Lean operations: `UInt64` and `Int64` arithmetic, bitwise operations, shifts and `log2` on safe integers; `UInt8/16/32` and `Int8/16/32` conversions; `natAbs` and `negSucc`; and array access (`List.getD`);
  - the old versions give the same results as the new ones;
  - the throws I removed could never have fired.

`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound`. The `README.md` layout table has a new row for `RuntimeSpec/`, and the result is in the Properties table.

**Assumptions and limits.** The theorems depend on the model, not on the real JavaScript engine:
- Arithmetic on safe-integer numbers is assumed exact, and floor/trunc division is assumed to give the exact quotient.
- 32-bit operators are modeled with `BitVec 32`.
- For the array theorem, `Number()` of a `BigInt` is assumed monotone and exact on safe integers; these are explicit hypotheses of that theorem.
- String and floating-point functions, and the throws on failed memory allocation, are not formalized.

# Summary of changes for run 383399f1-023c-4a93-a519-3a78e7f3d9e1
I implemented `proposals/JsTermReviewPlan.md` with your decisions and wrote the new proposal for recursive datatypes.

**What changed, by plan section**
- **§1, typed arrays:** the type is now `JsTy.typedArray (elem : JsTypedElem)`. The typed-array kind is computed from the element (`t.kind`, `t.leaf`), so a pair like "`Uint8Array` of strings" can no longer be written. The polymorphic operations quantify over one `t`.
- **§2, records and unions:** I used the fully structural version, `record (f₁ f₂ : JsTy) (fs : List JsTy)` and `union (c₀ c₁ : List JsTy) (cs : List (List JsTy))`. `record_mk`, `union_mk`, `destructure` and `unionCases` follow it, and the `{}` case is gone.
- **§3, `data`:** set aside as agreed. The new proposal is `proposals/RecursiveDatatypesProposal.md`. It covers:
  - the constructor-object layout, with `List` as a linked list `{tag:0}` / `{tag:1,_1,_2}`;
  - loops instead of recursion for linear types (left folds as a `while` loop with a cursor, like your `ofList`; right folds with a stack on the heap; `map`-like rebuilding that fills in fresh cells);
  - local recursive functions for trees, and what `Term` and `JsTerm` would need;
  - a phased plan and open questions. To follow your "all optimizations in `Term.optimize`" rule, the loop shapes are proposed as new `Term` constructs introduced by proved rewrites.
- **§4, uncurried functions:**
  - `JsTy.fn (doms : List JsTy) cod`, with n-ary `lam` and `app`. `lazy t` is `fn [] t`, and `lazy_mk`/`lazy_force` are removed.
  - `A → B → C` becomes a two-parameter function everywhere. A lambda takes every parameter of its type; if its body isn't the next lambda, it computes the function and then calls it on the remaining parameters.
  - A call is emitted only once all arguments are known. A partial application becomes a closure only when it is used as a value.
  - Exported functions take every parameter of their type, so `ack2` now takes `m, n`. The snapshots show code like `f(x, y)` where it used to be `f(x)(y)`.
- **§5, number literals:** `JsTerm/NumberLit.lean`, built on `UnpackedFloat` (committed earlier in this task).
- **§6, all externs implemented:** every extern now has an implementation in `runtime.js` at every representation, and `lean_extern_unimplemented` is deleted. A missing operation is now a conversion error, and `scripts/gen_js_ops.py` refuses to generate if one is missing (`--report` lists none).
  - Operations on a `String.Pos s` take `s` as a first argument, which the converter passes as a literal.
  - Runtime names escape `?`, `!` and `'` as `$3F`, `$21` and `$27`.
- **§7, one operations file:** `JsTerm/Ops.lean` contains `JsOpImported` (388 operations) and `JsOpInlinable` (219), indexed as `Effectfulness → MayThrow → List JsTy → JsTy`.
  - `runtimeName` comes from the constructor names via the existing `ctor_names%`; the name-deriving elaborator I had started was deleted.
  - `uint53` operations that throw past `2^53` are marked `mayThrow` and do throw.
  - Array updates are renamed `_immutable`/`_mutable`. 34 aliases with the same signature are merged, so `fset` is `set_immutable` and `fswap` is `swap_immutable`.
  - `JsTerm/Ops.lean` builds in about 12 s, so I didn't split it into groups.
  - **§7.3 (optimizations in `JsExpr`) was deliberately not done**, since you want all optimizations in `Term.optimize`.

**Checks**
- The project builds with `lake build JsTerm leanscript tests TyTests TermTests`.
- `lake exe tests`: 55/55 pass. New tests cover:
  - the effects of operations, and the merged aliases;
  - an unknown extern being a conversion error;
  - every imported operation being exported by `runtime.js`;
  - the version, githash and target constants in `runtime.js` matching this Lean;
  - a node-vs-Lean comparison of new runtime functions: string hash, `mixHash`, `Float.toString`, `frExp`, `scaleB`, `toUInt8`, `toBits`, `String.Pos.Raw.prev`/`get?`, and the `uint53` `RangeError`. This test passes silently if `node` is not installed.
- `bash scripts/leanscript-snapshots.sh`: 3806 checks passed, 0 failed, the same as before. The snapshots were regenerated. The script still exits 1, but only because of the intentional "literal too big" inputs, as before.
- A plain `lake build` of the default targets still fails, in `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That file hasn't changed since the initial commit.

`README.md`, `NOT_IMPLEMENTED.md` and a status table at the top of `proposals/JsTermReviewPlan.md` are updated. Everything is committed.

# Summary of changes for run 18d7c91e-0eaf-4d42-8118-3eae1c32fdf1
I wrote the plan and assessment to `proposals/JsTermReviewPlan.md`. No code has changed yet, and nothing was built or tested. It goes through your seven points one by one: whether each concern holds, a Lean sketch of the fix, and which files it affects. It ends with a phased plan and four questions for you.

1. **`typedArray kind elem`:** you're right. Today `typedArray .uint8Array .string` is a valid type. In every pair the code actually produces, the array kind follows from the element, so I propose one `JsTypedElem` type listing only the valid elements, with the kind computed from it.
2. **Empty records and unions:** you're right, and the real limits are stricter. The source types already guarantee a record has at least 2 fields and a union has at least 2 constructors, one of them with fields. I propose keeping the lists but adding these rules as proof fields that fill themselves in with `by decide`, so existing code and tests still read the same.
3. **`data`:** this names a user-declared recursive datatype, as the string `D<block>_<member>`. The string carries no layout, so the backend can't build, match or take apart such values. As a result, every program that uses a recursive datatype currently fails to convert. I propose indexing `JsTy` by the datatype declarations and reusing the source's `Ref`, with the module carrying each datatype's layout. This is the largest change in the plan.
4. **Uncurried functions:** I propose `fn (doms : List JsTy) cod` with multi-argument `lam`/`app`, and `lazy t` becomes `fn [] t`. Each function type is fully uncurried, and partial applications are wrapped in a closure. One trade-off: work between two curried arguments is redone on every call instead of shared.
5. **`FloatParts`:** it should move into a new `JsTerm/NumberLit.lean`. Lean's core library already has a replacement, `Float.Model.UnpackedFloat`, reached via `f.toModel.unpack`. It is stricter than `FloatParts` (zero has its own case, and a finite value's mantissa is provably positive). I checked with a quick `#eval` that it runs, but not with a test. Batteries' `Float.toRatParts` loses the sign of zero and can't tell NaN from infinity, and the project doesn't depend on Batteries, so it isn't a better fit.
6. **Missing operations:** 149 operations still throw at run time:
   - 50 float math functions (`sin`, `pow`, …);
   - 36 float conversions;
   - 48 string/substring operations;
   - 12 version/platform constants;
   - 3 hashes.
   Two need care: JavaScript's `Math.round` rounds `-2.5` to `-2` where Lean gives `-3`, and float-to-integer casts must saturate as Lean's do. Once all are done, a missing operation would become a conversion error instead of a throw.
7. **One `Ops.lean`:** a few corrections to the sketch:
   - `import` is a reserved word in Lean, so the constructors should be `imported`/`inlined`.
   - The type name should be spelled `Inlinability`.
   - Constructors are written without the leading dot.
   - The existing `JsOp` in `OpsLookup.lean` gets replaced.
   On mutable variants: push, pop, set and swap already have in-place versions, which would be renamed `_immutable`/`_mutable`. `fset` and `fswap` gain new `_mutable` variants. String operations can't have one, because JavaScript strings are immutable. For purity in `JsTerm`, I propose tagging each expression with the most effect it may have, and requiring shared top-level constants to be pure. The plan lists what this enables: dead-code removal, common-subexpression sharing, moving code out of loops, and a checked basis for the in-place updates.
   There is a risk: one inductive of about 500 operations may be slow to compile. The plan describes a fallback that keeps a single type.

The phases, in order: float printing → type fixes → merged ops with purity → purity in expressions → uncurried functions → datatypes. The missing operations can be done alongside.

Questions for you (also listed at the end of the file):
- Two purity levels as you sketched, or three (`pure | throws | mutates`)? With two, all overflow-checked `uint53` arithmetic counts as impure.
- Is the lost sharing from uncurrying acceptable?
- Should the version/platform constants report the Lean toolchain that ran `leanscript`?
- May float math differ from Lean's results in the last bit, or must it match exactly?

# Summary of changes for run d620c7e3-de18-4f5d-b280-8d306c175814
`JsTerm` is now a simply typed language with de Bruijn indices, and constants, mutable variables and join points live in separate contexts. The `JsNum…/JsBigInt…/JsBool…/JsStr…/JsBinOp/Js*UnOp` operators are gone. Every extern is now one operation per representation of its types, named `type__externname`. `lake build JsTerm leanscript tests` succeeds with no warnings and no `sorry`, and all 51 tests in `lake test` pass. I regenerated the snapshots: node ran 3806 checks and all passed. `scripts/leanscript-snapshots.sh` still exits with 1, but only because of the intended literal-too-big errors in two files (see below).

**Types (`JsTerm/Ty.lean`)**
- `JsTerminalTy` holds the leaf types from your sketch. How a Lean type maps onto it depends on the configuration: `Nat` becomes `bigint_nat` or `uint53`, and `UInt64`/`Int64` go the same way.
- `JsTy` wraps a leaf and adds generic arrays, typed arrays (`typedArray kind elem`), lists, functions, records, unions, enums, `data`, thunks and lazy values.
- Two changes from your sketch:
  - `bitvec_small` requires `2 ≤ n`, not `2 < n`, because Lean's `BitVec` type here allows width 2.
  - Arrays and lists are in `JsTy`, not in the leaf type.

**Grammar (`JsTerm/Syntax.lean`, `JsTerm/Vars.lean`)**
- Expressions have type `JsExpr C M τ` and blocks have type `JsBlock C M J k`. `C` holds the constants, `M` the mutable variables (`let`, reassigned by `assign`) and `J` the join points (`join`/`jump`).
- `JsTerm/Vars.lean` has renaming, weakening, substitution and occurrence tracking.
- Every pass keeps terms well-typed, so the printer never sees an ill-typed term and picks the variable names itself.

**Operations**
- `scripts/gen_js_ops.py` reads the extern catalogue and generates three files:
  - `JsTerm/OpsImported.lean`: 320 operations, each a function of the same name in `runtime.js`.
  - `JsTerm/OpsInlined.lean`: 171 operations printed as a single operator or conversion.
  - `JsTerm/OpsLookup.lean`: finds the operation for an extern at given types.
- Your examples work as described:
  - `bigint_nat__lean_nat_div` and `uint53__lean_nat_div` are imported.
  - `bigint_nat__lean_nat_land` is inlined as `a & b`.
  - `uint53__lean_nat_land` is imported and uses your fast implementation.
- `lean_array_get_size` is inlined as `a.length`, or `BigInt(a.length)` for `bigint_nat`.
- Because conversions follow from the types, no unneeded `Number(i)`/`BigInt(i)` is written.
- 149 operations still have no implementation and throw via `lean_extern_unimplemented`; `python3 scripts/gen_js_ops.py --report` lists them. None of them was implemented before either.

**Passes rewritten for the typed version**
- Conversion from `Term` (`JsTerm/FromTerm.lean`).
- Clean-ups (`JsTerm/Simplify.lean`).
- In-place array updates (`JsTerm/InPlace.lean`).
- Hoisting constants and collecting imports (`JsTerm/Hoist.lean`).
- Printing (`JsTerm/PrintMini.lean`): a join point only gets a labelled block when a jump leaves it early.

**`leanscript`**
- Generated modules now import from a single `runtime.js` (option `--runtime=FILE`).
- It exits with a failure if the runtime does not export a function a module imports.
- As you asked, a literal too big for its representation (a `Nat` above `2^53 - 1` where `Nat` is `uint53`) is a conversion error and `leanscript` exits with a failure. At the `pbo` preset this now happens for `PrimOpInt02Configurable` and `PrimOpInt03Configurable`.

**Tests and docs**
- `Tests/Main.lean` has new tests for the types, the operation naming, the in-place updates, the hoisting, the literal-too-big error, and a check that `runtime.js` exports every imported operation.
- I deleted `Tests/ExternCatalogue.lean` and its entry in `lakefile.toml`.
- `README.md` and `NOT_IMPLEMENTED.md` are updated.

Plain `lake build` still fails on an existing Mathlib import in `UsageAlgebra.lean`, which is not part of this change.

# Summary of changes for run 2bf2eaaf-a730-4ca2-94bf-7bbb38e11512
I merged the runtime files into one `runtime.js` with a Python script and deleted the originals. Nothing else in the project was changed, and nothing was built or tested.

- **Files merged:** `runtime/` had no `*.js` files, only 15 `*.mjs` files, so I merged those. They are `lean_runtime_{bitvec,int64,int,isize,nat,uint64,usize}_{bigint,num}.mjs` plus `lean_runtime_non_configurable.mjs`.
- **Format:** the files are joined in alphabetical order. Each one starts with a `==== FILE: runtime/<name> ====` header line, the same format the old `runtime.js` used. The new file is 2169 lines.
- **Old `runtime.js` replaced:** there was already a `runtime.js` from an earlier merge, and it has been overwritten. It contained a `runtime/lean_values.mjs` section. That file was no longer in `runtime/`, so its contents are not in the new `runtime.js`. The earlier version is still in git history if you need it.
- **Cleanup:** the 15 `.mjs` files were removed, and so was the empty `runtime/` directory.
- **Not updated:** Lean sources and docs that refer to paths under `runtime/` were left as they are, as you asked.

The change is committed.

# Summary of changes for run afce7a8a-c865-4879-b362-458391a89761
All three changes are in, and every regenerated snapshot passes: 3806 checks against Lean with 0 failures, and all generated `.js` files pass `node --check`. The unit tests pass too (`lake exe tests`: 52/52). These are tests only; none of the three changes is formally proved.

**1. Runtime imports instead of injected helpers**
- Generated modules no longer define runtime functions. Each one starts with `import { … } from "<relative path>/runtime/lean_runtime_….mjs"`, then the shared constants, then `export const f = …`.
- An extern becomes an operator, a short expression, or a call of `$` + its C symbol (e.g. `$lean_nat_sub`).
- That function is imported from the module for the knob of its result type. For `nat`, `int`, `uint64`, `int64` and `bitvec` this is `lean_runtime_<knob>_bigint.mjs` or `lean_runtime_<knob>_num.mjs`, depending on the configuration. Everything else comes from `lean_runtime_non_configurable.mjs`.
- Import paths are relative to each output file. `--runtime-dir` changes the directory; the default is `runtime/`.
- The `runtime/*.mjs` files were rewritten so each `_bigint`/`_num` pair exports the same names. They include in-place array functions and `$lean_extern_unimplemented`.
- `runtime/lean_values.mjs` is deleted. Its list/array helpers are now `$lean_array_to_list` / `$lean_array_mk` in the non-configurable module, and the Option constructors are gone.
- The file headers of the `uint64`, `int64` and `bitvec` `_num` modules now say what the functions actually do: a result that doesn't fit in a safe integer throws a `RangeError` instead of being rounded.
- An extern with no runtime function becomes a call that throws when evaluated.
- The code is in `JsTerm/Extern.lean`, `JsTerm/Syntax.lean`, `JsTerm/PrintMini.lean` and `LeanScriptCli/Main.lean`.

**2. Arrays are mutated when safe** (`JsTerm/InPlace.lean`)
- If a local variable is the only owner of its array, `$lean_array_push/set/swap/pop` on it become the mutating `_inplace` versions. Owning means the function built the array, reads it at most once per path, never reads it inside a closure, and nothing else refers to it.
- Parameters and shared arrays are still copied.
- **Limitation:** an array that starts as a parameter is copied by its first update, and a loop pushing onto a parameter copies on every iteration. This is listed in `NOT_IMPLEMENTED.md`.

**3. Constants are computed once, at the top of the file** (`JsTerm/Hoist.lean`)
- Expressions that depend on no variable are moved to the top of the module and shared by every function. This covers constructors without fields, records/unions built from constants, closures that capture nothing, and literal arithmetic that can't throw.
- Arrays and runtime calls are never moved.
- **Naming differs from your example:** constants are named by shape (`const $tag0 = { tag: 0 };`, then `$k1`, `$k2`, …), not `Option$none`. The intermediate typed terms don't carry Lean constructor names, so the Lean name isn't available.

**Tests**
- `Tests/Main.lean` is updated to the new API, with new tests for runtime imports, in-place updates (owned, parameter, shared and closure cases) and constant hoisting.
- A new test reads the real `runtime/` files. It checks that each `_bigint`/`_num` pair exports the same names, and that every extern marked implemented in the new `Tests/ExternCatalogue.lean` resolves to a function the runtime exports. That catalogue is 646 of 894 rows over both presets and is built as the `ExternCatalogue` library in `lakefile.toml`.
- `README.md` and `NOT_IMPLEMENTED.md` are updated.

**Build:** `JsTerm`, `TermTests`, `TyTests`, `ExternCatalogue`, `tests` and `leanscript` all build. A plain `lake build` still fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`: it imports Mathlib, which this project doesn't depend on. I haven't changed that file.

All work is committed.

# Summary of changes for run 77a31dac-95e7-48b1-8dbc-f0387399589c
Both changes are done. `JsTerm` no longer has an `opaque` type, and all six functions in `Tests/SnapshotsPBOPure/AssocArrayAppend.lean` now compile to single spread array literals. This is covered by tests, not formally proved.

**1. No `opaque` in `JsTerm`**
- **What was opaque:** `JsTerm.opaque` was used in exactly two places:
  - for `Float.Model` and `Float32.Model`;
  - as the default result type of an exported function, `JsFun.ret := .opaque "?"`.
- **The change:** I removed the constructor. A `Float.Model` is now `float` and a `Float32.Model` is `float32`, i.e. a plain JavaScript number.
  - A model literal is emitted as the number `Float.ofModel m` (previously it was refused).
  - `Float.toModel`/`ofModel` and the `Float32` versions compile to the identity.
  - `JsFun.ret` now has to be given explicitly (the translator always sets it).
- Nothing else in the type grammar is opaque.

**2. `AssocArrayAppend`**
The `.lean` file now contains exactly the code you gave. The generated JavaScript (both presets) is:
```js
export const ArrayTest$test1 = (arr) => ["a", "b", ...arr, ...arr, ...arr, ...arr, "c", "d"];
```
`ArrayTest$test2` gives the same array. `ArrayTest$test3` is `["a","b",...arr ×4,"c","d","e",...arr ×4,"f","g"]`. The three `ListTest` functions give the same outputs.

Two differences from your example:
- The printer breaks the literal across lines.
- The parameter keeps its Lean name, `arr`, rather than `x`.

What changed to get there:
- **Exported names:** namespaces are now joined with `$` instead of `_`, so `ArrayTest.test1` becomes `ArrayTest$test1` (`LeanScriptCli/Main.lean`).
- **Array literals:** `#[…]` of simple values such as strings used to be refused. They are now translated as array literals.
- **Appends to spreads:** `a ++ b` on arrays was a loop pushing each element. On generic arrays it is now written `[...a, ...b]`. A follow-up pass in `JsTerm/FromTerm.lean` (`inlineArrays`) then:
  - inlines an array literal that is used exactly once and not inside a loop or closure;
  - flattens a spread of a literal into its elements.
- **Lists:** in the `leanscript` tool, `List α` is now read as the built-in list type, which is a JavaScript array. Before, every `List` was refused.
  - Supported: list literals, and `xs ++ ys`, which is translated as `(xs.toArray ++ ys.toArray).toList` and so produces the same spreads.
  - Not supported yet: `x :: xs` on a non-literal list, `match` on a list, and other `List` functions.
  - Inside Lean, `#leanscript_to_term` still treats `List` as a datatype that a signature declares, so the existing tests are unaffected.
- **Checks:** `--check` now also generates list arguments and results. `AssocArrayAppend` passes 24/24 checks against Lean for each preset.

**Testing**
- `JsTerm`, `TyTests`, `TermTests`, `tests` and `leanscript` build.
- `lake exe tests` passes 49/49, including new unit tests for the `Float.Model` layout and the array flattening.
- I regenerated all snapshots with `scripts/leanscript-snapshots.sh`: 3806 checks against Lean, 0 failures, up from 3478 because more functions are now translated. Every `.js` passes `node --check`.
- A plain `lake build` still fails on `LeanScript/Term/Syntax/UsageAlgebra.lean`, which imports Mathlib. That failure predates this change and I didn't touch the file.

`README.md` and `NOT_IMPLEMENTED.md` describe the new behaviour.

# Summary of changes for run b3ce68ff-dda5-440d-ad8d-3d2c330f83d8
Both changes are done. The runtime helpers in `JsTerm/Extern.lean` are now written in the JsTerm grammar instead of as JavaScript text, and records and unions come out as the objects you asked for. The project builds, `lake exe tests` passes 47/47, and I regenerated all the snapshots: 3478 checks against Lean, 0 failures. None of this is formally proved; it is covered by tests only.

**1. Extern helpers written in JsTerm**
- **Helper type:** `JsHelper` (`JsTerm/Syntax.lean`) no longer holds a string of JavaScript. It holds a name, parameters and a body of JsTerm statements, which the existing printer turns into `function name(a, b) { … }`.
- **New syntax:** writing the helpers needed a few new pieces of syntax:
  - expressions: object literals `{ k: e }`, indexing by an expression `e[i]`, `new C(args)` and spread `...e`;
  - statements: object destructuring `const { k: x } = e`, `o.k = e`, `o[i] = e`, expression statements, `while` loops, and `throw new C(msg)` for any error class (so `RangeError` works).
- **`Extern.lean`:** every extern implementation is now built as a JsTerm term, and no JavaScript text is left in the file. A handful of short builders at the top (`Js.v`, `Js.op`, `Js.meth`, …) keep the code readable.
- **Differences in the output:**
  - `Nat` to the power of `Nat` on `BigInt`s now uses a new helper, `$bigPow`, which squares repeatedly. The printer has no `**` operator, so the old text could not be expressed as a term.
  - `$utf8` now creates a new `TextEncoder` each time it is called, instead of sharing one.
  - The 64-bit-as-`number` helpers convert their parameters with `a = BigInt(a)` instead of wrapping the body in a function that is called immediately.
- **Dump files:** `-JsTerm-*.txt` now shows the full helper functions, not just their names.

**2. Records and unions as objects**
- A record is `{ _1: …, _2: … }`.
- A union constructor is `{ tag: i, _1: …, … }`, where `i` is the constructor's position counting from 0. A constructor with no fields is `{ tag: 0 }`.
- Taking a record or constructor apart is `const { _1: f$8 } = x;`, and a case analysis tests `x.tag === 0`.
- In `JsTerm/Ty.lean` the layout constructors `tuple`/`tagged` are renamed to `record`/`union`, and the layout text and doc table use the new shapes.
- The `Substring`/`String.Slice` values (`[str, start, stop]`) are still arrays. They aren't records, so I left them alone.

**Testing**
- All 211 generated snapshot files under `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` were regenerated with `scripts/leanscript-snapshots.sh`. Every `.js` file passes `node --check`.
- `Tests/Main.lean` has two new unit tests: one for the record and union shapes, and one showing that a helper is built as a JsTerm term.
- Helpers the snapshots never call (for example `$force`, `$bigPow`, `$utf8Set`/`$utf8Extract`, `Int` division that rounds down, `Int8` division, 64-bit values stored as `number`s) I checked in a one-off Node script against hand-worked expected values. Those 27 checks all passed, but the script is not part of the project.

`README.md` and `NOT_IMPLEMENTED.md` now describe the new layouts, and everything is committed.

# Summary of changes for run bdbea385-e2ff-4c39-bf36-b4e37ca3d699
I've proved in Lean the two claims that weren't formal yet: that the optimizer never adds calls, and that it reduces `EsPrecedence01.test1` from five calls to one. The files below build with no `sorry`, `#print axioms` shows only the standard axioms, and `lake exe tests` still passes 45/45. The existing proof that the optimizer doesn't change `Term.eval` (`Term.optimize_eval`, `Term.optimizeN_eval`) is unchanged.

**How calls are counted:** `Term.numCalls` (`LeanScript/Term/Optimize/Count.lean`) counts every `f a`, `t.get` and `t ()` written in a statement, including inside closures, loop bodies, branches and join points.

**The optimizer never adds calls:** `Term.numCalls_optimize` states `t.optimize.numCalls ≤ t.numCalls` for every statement, and `Term.numCalls_optimizeN` states the same for any number of rounds. It is proved one piece at a time:
- `Term.numCalls_rename` (`CountRename.lean`): renaming variables doesn't change the count.
- `Term.numCalls_dce` (`CountDce.lean`): dead-code elimination only removes calls.
- `Term.numCalls_simp` (`CountOptimize.lean`): the first pass (copy propagation, shared answers, dropping unused record matches) never adds calls.
- `Term.numCalls_cseWalk` (`CountOptimize.lean`): the second pass (sharing repeated calls, collapsing identical branches, inlining trivial join points) never adds calls.

**`EsPrecedence01.test1`** (`Tests/TermTests/Optimize/CseTest.lean`, checked when the file builds):
- The unoptimized Term has 5 calls of `f`. That is 5, not 3: the translation also emits a call for `f b` and `f ()`, which are the same call because `a b : Unit`.
- After `optimizeN 3` there is exactly 1 call.
- For every `b`, the optimized Term computes `test1 (fun _ => b) () ()`.

The new files are all in the `LeanScript` library, and `README.md` has a row for them. The Properties table lists `Term.numCalls`, `Term.numCalls_optimize` (proved) and the `EsPrecedence01` result (proved).

# Summary of changes for run 71e123da-7a39-4478-ba2e-5e1a63f2f9d4
`MoreJsTy` is now `JsTerm` everywhere in the project except `ARISTOTLE_SUMMARY.md`, which you asked me not to edit. The code builds and all 45 tests pass, but only with a temporary lakefile change (see below), so I'm not listing any build targets.

**How:** one Python script walked every file tracked by git and replaced the exact string `MoreJsTy` with `JsTerm`. It then used `git mv` to rename every path containing that string. I ran it from outside the project, so the old name doesn't survive in the script itself.
- **Contents:** 18 files changed, including:
  - the Lean sources: module names, imports, namespaces and identifiers
  - the `lean_lib` entry in `lakefile.toml`, now `name = "JsTerm"`, `globs = ["JsTerm.+"]`
  - the `-JsTerm.txt` output suffix used by the `leanscript` tool in `LeanScriptCli/Main.lean` and in `scripts/leanscript-snapshots.sh`
  - `README.md`, `NOT_IMPLEMENTED.md`, `Tests/Main.lean` and `.lean-spec-timings-and-last-failures`.
- **Paths:** 150 renamed. The `MoreJsTy/` directory is now `JsTerm/`, and every `*-MoreJsTy.txt` snapshot under `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` is now `*-JsTerm.txt`.
- **Name clash:** `JsTerm` didn't appear anywhere in the project before, so nothing collides.
- **Search:** afterwards, a search for `MoreJsTy` in file contents and names (outside the build cache) found it only in `ARISTOTLE_SUMMARY.md`.

**Build:** as in earlier runs, `lakefile.toml` requires `mathlib` but `lake-manifest.json` has no entry for it, so `lake` stops straight away. To check the rename I removed that requirement locally and put it back before committing, so the only lakefile change in the commit is the library rename. With it removed:
- `lake build JsTerm leanscript LeanScriptCli tests TyTests TermTests` succeeded (353 jobs).
- `lake exe tests` passed 45/45.

To build it yourself, either delete the unused `mathlib` requirement or run `lake update`.

Everything is in one commit.

# Summary of changes for run 9211ea27-8f57-4883-a285-96d0c333b2d1
I created the `runtime/` directory by splitting the bundled `runtime.js` at its `==== FILE: runtime/… ====` markers. Each section's contents were copied exactly as they were, with only trailing blank lines trimmed to a single newline. That gives 16 files:

- `lean_values.mjs`
- `lean_runtime_non_configurable.mjs`
- `lean_runtime_{int,nat,isize,usize,int64,uint64,bitvec}_{num,bigint}.mjs`

All 16 files pass `node --check`, which only checks syntax. I didn't run any of the JavaScript tests that import from `runtime/`. Nothing else was changed: `runtime.js` is still there, and no Lean, test or docs files were touched. The new directory is committed. No Lean build was involved, so no build targets are listed.

# Summary of changes for run 67f85bf7-a16b-4270-b0b9-0b56d38d291b
I reorganised `LeanScript/Term` into subdirectories grouped by what each module is for, and did the same for `LeanScript/Ty` and `Tests/TermTests`. No declarations, namespaces or proofs changed. Only file locations, module names in `import` lines, and references to modules and paths in docs and comments changed. Everything is committed.

**Why `build_targets` is empty:** `lake build` can't run in this checkout. The lakefile requires `mathlib`, but `lake-manifest.json` has no entry for it. So I checked everything in a copy of the tree with the Mathlib requirement removed. That also meant leaving out `LeanScript/Term/Syntax/UsageAlgebra.lean`, the only file that imports Mathlib. Its only change is its import line, but it has not been compiled.

**New layout of `LeanScript/Term`** (also described in the new `LeanScript/Term/README.md`)
- `Syntax/`: `DeBruijn`, `Tuple`, `Usage`, `UsageAlgebra`, `Common`, `Ctx`, `Term`, `Packed`
- `Extern/`:
  - `Catalogue` (was `Extern`), `Name`, `NameElab`, `Shorthands`
  - `Eval` (was `ExternEval`), with `Eval/{Core,UInt,SInt,String,Float}`
- `Semantics/`: `Den`, `Eval`, `Closed`, `NormalValue`, `BoundedLoop`
- `Rename/`: `Basic` (was `Rename`), `Eval`, `Comp`, `Weaken`
- `Optimize/`: `Occ`, `Dce`, `Basic` (was `Optimize`), `OpenRec`
- `Rewrite/`: `Abstract` (was `Rewriting`), `Step`, `StepRename`, `StepInv`, `ChurchRosser`, `SimpStep`
- These stay at the top level as entry points: `Build.lean` (used by the elaborators and tests) and `Pretty.lean` (used by the command-line tool).

**Other moves**
- `LeanScript/Ty/`:
  - `Syntax/` holds `LeanPrimTy`, `LeanPrimTyCovariant`, `EnumSchema`, `Ty`, `Decl`.
  - `Den/` holds `Container`, `Basic` (was `Den`), `Facts`, `Brec`, `Two`, `Three`.
- `LeanScript/LeanInitPureExternShorthands.lean` is now `LeanScript/LeanInitPureExterns/Shorthands.lean`.
- `Tests/TermTests/` now follows the source layout: `Syntax/`, `Semantics/`, `Extern/`, `Optimize/`, `ToTerm/`, and `Datatypes/` for the indexed-family, nested, quotient and rose-tree tests together with their proof files.
- `Tests/TyTests` is unchanged. Its expected outputs contain names built from the module name (for example `TyTests.GetCtorTest.…`), so moving it would change those outputs.

**References updated to match**
- All importers (`GenElab`, `TermElab`, `WFTerm`, `MoreJsTy`, `LeanScriptCli`, `Tests/Main.lean`, the tests, `proposals/*.lean`).
- The module name that the command-line tool imports at run time (`LeanScriptCli/Frontend.lean`).
- Module and path references in `README.md`, `NOT_IMPLEMENTED.md`, `proposals/*.md` and doc comments. `ARISTOTLE_SUMMARY.md` and the snapshot outputs were not touched.

**Checks run in that copy**
- `lake build` of the default targets passed, both after the `LeanScript` move and after the `TermTests` move.
- `MoreJsTy`, `LeanScriptCli`, the `leanscript` executable, `Spec` and the `LanguageJavascript*` libraries also built.
- `lake exe tests` passed 45 of 45.
- I built the original commit the same way and ran `leanscript --check` on six snapshot files in both trees, one file per run: `TcoAck`, `StringWalk`, `AppArity` and three from `Tests/SnapshotsPBOPure`. The outputs were byte-for-byte identical.
- No `sorry` was found in `LeanScript/Term`.

**One oddity you may hit:** when `StringWalk.lean` and `AppArity.lean` were passed to a single `leanscript` call, the second file's functions were reported as `noncomputable`. Run on its own, `AppArity.lean` gives the committed output. I only saw this on the reorganised tree and did not test the original tree in that mode, so I can't say whether it predates this change. The snapshot script runs one file per call and is not affected.

The Properties table now points each result at its new file; their statuses are unchanged.

# Summary of changes for run b17cc614-820d-4167-a580-8242bc29d1e6
The four outputs (`FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`, `FILE-MoreJsTy.txt`, `FILE.js`, plus `FILE.check.mjs`) now also cover well-founded functions in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure`. The tool already handled most of this before this session. I rebuilt it and reran it on every file, and it reproduced the committed outputs exactly. That rerun showed which well-founded functions were still refused, and I fixed the one blocker that could be fixed without a larger redesign.

**Changes**
- **`==` on `Char`** (`LeanScript/TermElab/ToTerm/Expr/Calls.lean`). This was what kept the well-founded loops `StringWalk.test1.go` and `test2.go` out. Lean compares characters by looking inside the `Char` value, which the translator can't do. It now translates `a == b` as a comparison of the two one-character strings `"".push a` and `"".push b`, using the existing string operations.
- **JavaScript for that comparison** (`MoreJsTy/Extern.lean`). A character is already a one-character string in the JavaScript output, so `"".push c` is printed as just `c`. The comparison comes out as `get(s, p) === c`.
- **Proof that the rewrite is correct** (`LeanScript/TermElab/ToTerm/CharEq.lean`). `decide_char_eq_push` shows that deciding `a = b` and deciding `"".push a = "".push b` always give the same answer; `char_beq_eq_push` does the same for `==`. There is no `sorry`, and the proof uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **Progress output** (`LeanScriptCli/Main.lean`). When run without `--quiet`, the tool now prints a line for each refused well-founded or `mutual` function, with the reason.

**Results**
- `StringWalk`'s `test1`, `test1.go`, `test2` and `test2.go` are now translated; `StringWalk` has 7 functions exported and none refused, with 59 checks.
- As a side effect, `CaseChar.test1` and `PrimOpChar01`'s `test1` and `test2` are now translated too.
- On a full rerun over both directories, all 2064 checks passed and none failed. `lake exe tests` passed 45 of 45.

**Still refused**
- These well-founded functions are polymorphic or monadic, which the translator doesn't support in general: `Fusion02`'s `toArrayLoop` and `filterMapStep`, `RecursionSchemes01`'s `cata` and `cataMap`, and `VanLaarhovenTraversals01`'s `rewriteBottomUpM`.
- `CaptureDerefRegression01`'s `testEven` and `testOdd` also fail, with a type-mismatch error. They are a `mutual` pair recursing on a subvalue, not well-founded functions, so they are outside this request. `NOT_IMPLEMENTED.md` lists the polymorphic/monadic ones.

**Not verified:** the translator code that performs the `Char` rewrite is only tested by the generated checks, not proved.

**Build setup:** as in earlier runs, `lakefile.toml` requires Mathlib but `lake-manifest.json` has no entry for it, so `lake` stops immediately. I removed that requirement locally to build, then restored it, so your lakefile is unchanged. For that reason I'm not listing any build targets. The only module that failed was `LeanScript/Term/UsageAlgebra.lean`, which imports Mathlib; it failed before this change too.

`README.md` and `NOT_IMPLEMENTED.md` are updated, the regenerated outputs are included, and everything is committed.

# Summary of changes for run f15c3bd1-7932-4195-9d74-37f950b4def1
The four output files (`FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`, `FILE-MoreJsTy.txt`, `FILE.js`) now cover well-founded functions in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure`, not only structurally recursive ones. Each file still also gets its `FILE.check.mjs`.

**What was already there.** The tool could already translate well-founded functions. It writes each one as its "open definition", with recursive calls turned into a parameter, and the function is the fixed point of that. `--functions-only` already counts well-founded functions, so files like `TcoBoom`, `Tco07` and `Tco08` already had outputs. I rebuilt the tool and reran `scripts/leanscript-snapshots.sh`, and it reproduced the committed files exactly. That meant the remaining work was the well-founded functions that were still refused.

**Changes**
- **Proof helpers Lean splits out** (`LeanScriptCli/Frontend.lean`). Lean moves some proofs inside a definition into separate helpers, and their statements still mention the function. Once the recursive calls were replaced, those proofs no longer type-checked, so `Tco09`'s `Mc91.M` failed with a kernel error. The open definition now copies those proofs inline.
- **Constants that call well-founded functions** (`LeanScriptCli/Main.lean`). A definition like `def ack999 := ack 999 1` used to be refused. It is now exported as `export function ack999() { return ack(999n, 1n); }`.
- **Types that depend only on a proof** (`LeanScript/GenElab/Read.lean`). A function type like `(n : Nat) → {m // m ≥ n - 10}` used to be refused as dependent. The dependency is only in the part that gets erased, so it is now read as `Nat → Nat`.
- **Local proofs** (`LeanScript/TermElab/ToTerm/Expr.lean`). A local proof such as `have h : p := …` has no runtime value, so it is now substituted into the body instead of being translated.

**Results**
- `Mc91` and `Mc91.M` in `Tco09` and `ack999` in `Tco08`/`TcoAck` are now translated. `Mc91.M` comes out as the expected nested recursion `Mc91_M(Mc91_M(n + 11n))`.
- As a side effect, `CaseArray.test1` in `SnapshotsPBOPure` is now translated too.
- Functions now going through the open-definition path include `boom`, `ack`, `diagonal`, `diagonal_tr`, `hyper`, `ackRev`, `mc91Loop`, `mc91TR`, `Mc91`, `Mc91.M`, `gcdT`, `stepsDown`, `StringWalk.test4`/`test4.go`, `Tco05.span`, and the `mutual` examples.
- In a full rerun of the script, every check passed: 2008 passed, 0 failed.

**Still not translated**
- `StringWalk`'s `test1.go`/`test2.go` compare `Char`s with `==`, and the translator has no support for `Char` equality yet. This is a general gap, now noted in `NOT_IMPLEMENTED.md`.
- Some well-founded functions in `Fusion02` and `VanLaarhovenTraversals01` are refused because they are polymorphic or monadic, which the translator doesn't handle in general.

Because the translator core changed, I rebuilt the `LeanScript`, `TyTests` and `TermTests` libraries and the `tests` executable, and ran `tests`; it passed. The only module that failed to build was `LeanScript/Term/UsageAlgebra.lean`, which imports Mathlib; that was already the case before this change.

**Build setup:** as in earlier runs, `lakefile.toml` requires Mathlib but `lake-manifest.json` has no entry for it, so `lake` stops immediately. I removed that requirement locally to build, then restored it, so your lakefile is unchanged. For that reason I'm not claiming any build targets. None of this is new proof work.

`README.md` and `NOT_IMPLEMENTED.md` are updated, and everything is committed.

# Summary of changes for run df763831-9200-4bda-bc91-868d7bc2aed2
I formalized in Lean why translating a well-founded function through its "open definition" gives the right function. The proofs contain no `sorry` and use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`). Everything is committed.

What is still unverified: the tool code that builds the open definition from a Lean function, and the JavaScript printing of recursive calls. For `mc91Loop` and `ack` I wrote the open definition by hand in the shape the tool builds.

**General theorems (`LeanScript/Term/OpenRec.lean`)**

Setup: an open definition is a functional `F : (α → β) → α → β`, and the original function `f` is its fixed point, `f = F f`. `OpenRec.Respects r F` means `F` only calls its recursive parameter on arguments smaller for `r`, which is what Lean's termination proof establishes.

- **At most one fixed point (`OpenRec.fix_unique`).** If `r` is well-founded and `F` respects it, two fixed points of `F` are equal. So any function that satisfies the unfolding equation is the original function, and the translation cannot compute a different one.
- **A fixed point exists (`OpenRec.fix_isFix`, `OpenRec.fix_exists`, `OpenRec.eq_fix_of_isFix`).** It is built with `WellFounded.fix`, and every fixed point equals it.
- **The optimiser keeps the fixed points (`Term.optimizeN_isFix_iff`, `Term.optimizeN_fix_eq`).** These follow from the existing `Term.optimizeN_run`. The translated open term, optimised any number of times, has the same fixed points as before, and so still denotes the original function.
- **Loop-to-`if` rewrite (`natIter_of_ignoresAcc'`).** A `nat_rec` whose step ignores the accumulator equals `if 0 < n then s (n-1) z else z`. This is the `if` the JavaScript printer now emits instead of a loop, which is the change that stopped the exponential blow-up in `mc91Loop`.

**Examples from the snapshots (`Tests/TermTests/OpenRecTest.lean`)**

- **`mc91Loop`:** it satisfies its open definition's equation, the recursive calls decrease the termination measure `2*(111-n)+21*c`, and every solution of the equation is `mc91Loop` (`mc91Loop_unique`).
- **`ack`:** the same, under the lexicographic order (`ack_unique`).
- **End to end (`mc91LoopOpenT_optimizeN_fix`):** I translated `mc91Loop`'s open definition with `#leanscript_to_term`, as the tool does. The resulting `Term` computes the open definition; this step uses the existing `kernel_rfl` tactic, so the kernel checks it. Every fixed point of that translated term, optimised any number of times, is `mc91Loop`.

`README.md` has a new row for these two files, and the Properties table lists the five main results as proved.

**Build:** as in earlier runs, `lakefile.toml` requires Mathlib but `lake-manifest.json` has no entry for it, so `lake` stops immediately. I removed that requirement locally to build `LeanScript.Term.OpenRec` and `TermTests.OpenRecTest` (both built successfully) and restored it before committing, so your lakefile is unchanged. For that reason no build targets are claimed.

# Summary of changes for run 347f97b8-4503-4de7-9a88-e37029d3fafe
I implemented `WFTerm`, a layer wrapped around `Term` that adds well-founded recursion, along with its evaluator and an optimiser. The optimiser is proved not to change results. The proofs contain no `sorry` and use only the axioms `propext`, `Classical.choice` and `Quot.sound`. All 45 tests pass, including 7 new ones for `WFTerm`. Everything is committed.

**The grammar** (`LeanScript/WFTerm/Syntax.lean`) follows your PCL design:
- **Call-free layer:** this is `Term` itself. An atom (`WFAtom`) is a normal-form `Term` whose unknowns are the `WFTerm` variables, and it is evaluated by `Term.eval`. Path conditions and decrease proofs can mention it without induction–recursion.
- **Computations** (`WFComp`):
  - `self`: a recursive call carrying its decrease proof under the path condition.
  - `call`: a call of an earlier global function, with its precondition.
  - `share`.
  - `map` and `foldl`, whose body knows `x ∈ l`.
- **Statements** (`WFTerm`): `ret`, `ite`, `letE` (the only binder), `join`, `joinrec` and `jump`. In `joinrec`, back edges must prove `P e v ∧ R e v x`.
- **Supporting pieces:** global functions with pre/postconditions and a well-founded relation (`WFFn`, `WFGlobals`), `WFProgram`, and shorthand forms (`fixSelfCall`, `gCall`, `plet`).
- **One design change from PCL:** each computation declares only the new fact it establishes, and the continuation runs under `G ∧ fact`. This is what lets the optimiser strengthen path conditions.
- **Omitted:** `mu_rec`/`mu_brec` are not separate computations, because `Term`'s `data_rec`/`data_brec` are already available inside atoms. I also left out the `isNF` proofs, since `Term` is already a normal-form grammar.

**The evaluator** (`LeanScript/WFTerm/Eval.lean`): `WFTerm.eval` is structural on the syntax and returns the answer together with a proof of its postcondition. Global functions (`WFFn.fix`) and `joinrec` loops run through `WellFounded.fix`, which compiles to ordinary code. There is no fuel, measure, default value or `Acc` data; only proofs are involved. `WFFn.fix_eq` (the unfolding equation of a global function) is proved.

**The optimiser** (`LeanScript/WFTerm/Optimize.lean`) keeps each statement's type, so every decrease proof carries over. It:
- optimises each atom with `Term.optimize`;
- resolves an `if` whose test is the literal `true`/`false`;
- turns `join j v := body in jump j a` into `let v := a in body`;
- replaces `map f []` with `[]` and `foldl f init []` with `init`.

Two theorems state that the result is unchanged:
- `WFTerm.optimize_eval`: in every environment.
- `WFProgram.optimize_run`: for whole programs.

**Tests**
- **`Tests/TermTests/WFTermTest.lean`:** example programs with their decrease proofs:
  - `gcd`;
  - Ackermann with a lexicographic order;
  - a `joinrec` loop whose postcondition "the answer is 7" is carried to the result (`countdown_run`);
  - a `map` whose body calls `gcd`.

  It also checks two optimiser rewrites with `rfl`.
- **`Tests/Main.lean`:** a new `WFTerm` spec runs these programs compiled, before and after optimisation: `gcd` on large numbers, `ack 3 3`, a 100,000-step loop, and the `map`. Each takes a few milliseconds.

`README.md` has a new row for these files.

**Build issue (unchanged from earlier runs):** `lakefile.toml` requires Mathlib, but `lake-manifest.json` has no entry for it, so `lake` stops at once. To build and test I removed that requirement locally and restored it before committing, so your lakefile is unchanged. For that reason I'm not listing any build targets as checked here. The modules `LeanScript.WFTerm.Syntax`, `.Eval` and `.Optimize`, `TermTests.WFTermTest` and the `tests` executable all built successfully with the requirement removed. To build it yourself, either delete that requirement or run `lake update`.

# Summary of changes for run e419aa3b-6302-46e1-978c-79ad2a564399
I generated `FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`, `FILE-MoreJsTy.txt` and `FILE.js` next to every `.lean` file in `Tests/SnapshotsMy` and `Tests/SnapshotsPBOPure` that has at least one public, structurally total function. Each of those files also got a `FILE.check.mjs`, which runs the exported functions on sample inputs and compares the results with Lean's answers. Every generated `.js` passes `node --check`, and every check passes: 694 in `SnapshotsMy` and 1006 in `SnapshotsPBOPure`, with 0 failures. Everything is committed.

**Which files got outputs**
- **`SnapshotsMy`:** 35 of the 46 files. 24 of them export at least one function, 72 functions in total.
- **`SnapshotsPBOPure`:** 106 of the 119 files. 59 of them export at least one function, 430 functions in total.
- In the other files, a file with outputs lists each function it didn't translate, with the reason (e.g. user-defined datatypes aren't converted to JavaScript yet).
- **Files with no outputs** (they contain only constants, types, `IO`/`ST` code, or functions using well-founded recursion):
  - `SnapshotsMy`: `ArgsArrayEntry`, `CompiledTerms`, `ComputedFields`, `InductiveTypesTest`, `IoEntry`, `StdinEntry`, `Tco07`, `Tco08`, `TcoBoom`, `ThrowEntry`, `WriteEntry`. **Their old generated outputs have been deleted.**
  - `SnapshotsPBOPure`: `BackendSemantics01`, `BackendSemantics02`, `EscapeIdentifiers`, `InlineArrayIndex`, `InlineNever`, `KnownConstructors01`, `PrimOpIntBit02Configurable`, `PrimOpIntBit02NonConfigurable`, `STArray01`, `STObject01`, `STRun01`, `Show`, `StringLiteral01`.

**Changes to the `leanscript` tool (`LeanScriptCli/`)**
- **New `--functions-only` option.** It writes nothing for a file with no public, structurally total function, meaning a definition with at least one value parameter. It also deletes outputs from an earlier run for that file, but only files the tool itself wrote. `scripts/leanscript-snapshots.sh` now uses this option and covers both folders; `README.md` is updated to match.
- **Bug fixed: mutual recursion was compiled wrongly.** Members of a `mutual` block (e.g. `test1`/`test2` in `MutualTail`) came out wrong: a call to the other member was treated as a call to the function itself, and 14 checks failed. These members are now refused with the reason "part of a `mutual` block … mutual recursion is not translated yet". Their files still get outputs (`MutualSlots`, `MutualTail`, `MutualUnreachMarker`, `Tco03`, `Tco04`, `Tco06`, …). Actually translating mutual recursion is still to do.

**Old JavaScript in `SnapshotsPBOPure`**
- Each file that got a new `FILE.js` already had a `FILE.js` from the earlier backend. Those old `FILE.js` files, with their `FILE.test.js` and `FILE.expected.js`, were moved unchanged to `Tests/SnapshotsPBOPure/legacy-backend/`, which has a README. This is the same arrangement already used in `SnapshotsMy`.
- Old files belonging to snapshots without outputs were left where they were.

**Build problem (as in earlier runs):** `lakefile.toml` requires Mathlib, but `lake-manifest.json` has no entry for it, so `lake` stops immediately. To build the tool I removed that requirement locally and put it back before committing, so your lakefile is unchanged. None of this work is formally proved, so no Lean build targets are claimed.

# Summary of changes for run 6a7fd921-c33c-4de8-9586-13adfdf09762
The four output files (`-Term-unoptimized.txt`, `-Term-optimized.txt`, `-MoreJsTy.txt`, `.js`) and a `.check.mjs` now exist for `TcoBoom`, `TcoDiagonal`, `TcoHyper` and `TcoMc91`, next to each `.lean` file in `Tests/SnapshotsMy/`. I regenerated `TcoAck` too. Every generated `.js` file passes `node --check`, and every `.check.mjs` reports 0 failures.

**The old files already existed.** The previous run had generated files for every `Tests/SnapshotsMy/*.lean`, and re-running the tool reproduced them unchanged. But they were wrong in one way: every recursive function was refused as "a `partial` definition", including structurally recursive ones like `ack2`, `hyperLoop`, `hyperTCO`, `hyperWhile` and `iter`. The tool assumed that a function with an `_unsafe_rec` helper is `partial`, but Lean 4.34 creates that helper for every recursive definition.

**Changes to the tool (`LeanScriptCli/`)**
- `Frontend.lean`: only a real `partial def` is refused as partial. Functions that use well-founded recursion are now refused as "defined by well-founded recursion, not structurally". Structurally recursive functions are now translated.
- `Check.lean`: each Lean answer used by the checks now has a 2-second limit, and small sample inputs are tried first. Without this, computing `ack2 13 13` or `hyperTCO 13 13 13` in Lean ran forever. When a function is exported curried (e.g. `ack2(m)(n)`), the check now calls it that way.
- `Main.lean`: passes the number of parameters to the checks, and exits explicitly so that computations that ran out of time are stopped.

**Results per file**

| File | Translated | Not translated (reason) | Checks |
|---|---|---|---|
| `TcoBoom` | nothing | `boom` (well-founded) | none |
| `TcoDiagonal` | nothing | `diagonal`, `diagonal_tr` (well-founded); `diagonalWhile` (the translator can't tell that its `while` loop terminates) | none |
| `TcoHyper` | `hyperBase`, `hyperLoop`, `hyperTCO`, `hyperWhile` | `hyper` (well-founded) | 53 passed |
| `TcoMc91` | `mc91`, `iter` | `mc91Loop` (well-founded); `mc91TR` (calls `mc91Loop`); `mc91While` (same `while` limitation) | 5 passed |
| `TcoAck` | `pair`, and now `ack2` | `ack` (well-founded); the others as before | 20 passed |

`hyperLoop` and `iter` take a function as an argument, so the tool writes no automatic checks for them. I tested them by hand in node (`hyperLoop(x=>2x, 5, 3) = 96`, `iter(x=>x+3, 4, 1) = 13`, `hyperTCO(3,2,4) = 16`), but that test is not saved in the project.

**Things to be aware of**
- The other `Tests/SnapshotsMy` outputs were not regenerated, so any structurally recursive functions in them are still wrongly shown as refused. To refresh them, run `scripts/leanscript-snapshots.sh`.
- The build problem from earlier runs is still there: `lakefile.toml` requires Mathlib, but `lake-manifest.json` has no entry for it, so `lake` stops immediately. To build the tool I removed that requirement locally and put it back before committing, so your lakefile is unchanged.
- Nothing here involves Lean proofs, so no build targets are claimed. All changes are committed.

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
