# Are `JsOpImported` / `JsOpInlinable` too big?

Short answer: **no, they don't need to be split at their current size.**

| inductive | constructors | with fields (index) | file build |
| :-- | --: | --: | --: |
| `JsOpImported` (`JsTerm/Ops/Imported.lean`) | 398 | 33 (0–32) | ≈ 17 s (≈ 3.5 s of it imports) |
| `JsOpInlinable` (`JsTerm/Ops/Inlinable.lean`) | 219 | 13 (0–12) | ≈ 10 s (≈ 3 s of it imports) |

## 1. The "tag too big" limit is not hit

Compiled code can't build a constructor of index > 243 **if it has fields**
(checked again on this toolchain: `.c243 1` compiles, `.c244 1` fails with "tag for constructor
… is too big"; a constructor with no fields of index 249 is fine). `scripts/gen_js_ops.py`
already puts the constructors with fields first, so only indices 0–32 and 0–12 have fields.
The generator now **fails** if either inductive ever has more than 244 constructors with fields,
so this can't break silently.

## 2. No kernel / `rfl` reduction goes through them

The 460-constructor `LeanInitPureExtern` had to be split (`ExternCatalogueSpeed.md`) because
`rfl` / `decide` checks evaluate `Extern.eval`, and each reduction step instantiates every
alternative of the `casesOn`. Nothing proves or `decide`s anything about `JsOp` values: the
JsTerm pipeline is only run as compiled code (snapshot tests, `lake exe tests`). In compiled
code a `match` is a jump on the tag and `name` is `names[op.ctorIdx]!`, so the number of
constructors has no effect on speed when the code runs.

## 3. Compile-time cost (measured, `-Dtrace.profiler=true`)

Declaring the first *n* constructors of `JsOpImported` (inductive + `sizeOf` + `ctorElim`
compilation + `noConfusion`):

| n | total |
| --: | --: |
| 100 | ≈ 1.2 s |
| 200 | ≈ 3.0 s |
| 398 | ≈ 8.5 s |

This grows a bit faster than linearly (about n^1.4). Splitting `JsOpImported` into 4 families of
about 100 constructors would save about 3–4 s of CPU (more wall-clock time on a parallel build),
and only when the generator is re-run, since nothing else changes these files. Every module
that uses them (`Template`, `Op`, `Cands/*`, `Lookup`, `Passes/InPlace*`, `Hoist`,
`Print/Mini`, `Syntax/Basic`) has no declaration above 0.3 s apart from `template` (≈ 1.5 s for
a 219-way match). What costs time there is loading the imports (≈ 3 s per file), which a split
wouldn't change.

## When to split

- more than about 244 constructors with fields (the generator now stops with an error);
- `rfl`/`decide` proofs that reduce `JsOp` values (for example a formal semantics of JsTerm
  checked by evaluation), where the per-step cost is proportional to the constructor count;
- `JsOpImported` growing to about 800 or more constructors, where the file alone would take
  about 25 s or more.

If one of these happens, use the same two levels as `LeanInitPureExtern`: one family per
group already used by the lookup (`Cands/Nat`, `UInt`, `SInt`, `Float`, `String`, `Misc`), a
wrapper inductive, and `@[match_pattern, reducible]` shorthands so the existing patterns
(`.array__lean_array_push_immutable α`, …) keep working.
