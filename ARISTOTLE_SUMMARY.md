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
