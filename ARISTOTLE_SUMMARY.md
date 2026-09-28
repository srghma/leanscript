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
