# Why externs made the checks slower, and the "tag too big" error

Both problems come from the same thing: `LeanScript.LeanInitPureExtern` is **one inductive
with 460 constructors**, and `Extern.eval` is **one 460-way `match`** on it.

## 1. "tag too big" in compiled definitions

The compiled runtime keeps a constructor's index in the 8-bit tag of the object header.
Only tags `0 … 243` are for ordinary constructors. Tags `244 … 255` are reserved for the
runtime's own objects (`include/lean/lean.h`: `LeanMaxCtorTag 243`, then `LeanPromise`,
`LeanClosure`, `LeanArray`, …, `LeanString`, `LeanMPZ`, `LeanThunk`, …). The IR checker
(`Lean/Compiler/IR/Checker.lean`) therefore refuses any compiled code that *builds* a
constructor with index `> 243` if that constructor has fields. A constructor with no fields
is stored as a boxed number, so it is not affected.

Every catalogue entry has fields, so entries `244 … 459` (216 of them) can't be built by
compiled code. For example, `lean_int32_dec_le` (index 243) compiles, while
`lean_int32_of_nat` (index 244) and `lean_string_compare` (index 459, the last entry) do
not. I checked the index-243 and index-459 cases directly. The kernel and `rfl` proofs
never go through the compiler, which is why proofs work and only `def`s fail.

**Fix:** have no inductive with more than 244 constructors, as described in section 3.

## 2. Why the checks got slower

### 2a. Each extern call costs time proportional to the size of the catalogue

To reduce `Extern.eval (.lean_nat_add a b)`, the kernel unfolds `Extern.eval` to its
matcher, then `casesOn`, then `LeanInitPureExtern.rec`. That application has
**460 minor premises** (one per alternative) plus the 11 parameters of the catalogue, and
reducing it instantiates all of them, even though only one alternative is used. So each
extern call costs time proportional to the catalogue size, not to the entry's own work.

Measured in the project (kernel only, `decide +kernel`, 2000 calls of `Nat.add`):

| loop body                                          | kernel time |
| :------------------------------------------------- | ----------: |
| `Extern.eval (.lean_nat_add acc 1)`                 | ≈ 4.4 s     |
| `Nat.add acc 1`                                     | negligible  |

That is about 2 ms per extern call. The same effect appears in isolation
(`scripts/bench_extern_dispatch.py`, 3000 calls, no project imports):

| shape                                                 | kernel time |
| :---------------------------------------------------- | ----------: |
| one inductive, 460 constructors, one 460-way `match`   | 10–11 s     |
| one inductive, 8 constructors                          | ≈ 0.2 s     |
| 20 inductives × 23 constructors + a 20-way wrapper     | ≈ 0.4 s     |

The two-level shape is about **25× faster** per call.

### 2b. Most of the time was the elaborator, not the kernel

`example : … := rfl` is checked twice. First the elaborator's `isDefEq` decides whether
the two sides agree. Then the kernel re-checks the finished proof. **Only the first check
counts heartbeats**, and for this evaluator it is much slower than the kernel. Its
reduction of the 460-way matcher is more expensive than the kernel's, and on symbolic
goals it unfolds `Extern.eval` repeatedly. Profiles:

| check                                                        | elaborator | kernel  |
| :----------------------------------------------------------- | ---------: | ------: |
| `hstep` in `window_eval` (`TermTests/FibWindowTest.lean`)      | 15.6 s     | 0.3 s   |
| typical value check in `TermTests/ArrayRecToTermTest.lean`     | 4–7 s      | ≈ 1 s   |

The raised `maxHeartbeats` were covering the elaborator's work, not the kernel's.

## 3. What to do

### Done now: `kernel_rfl` (`LeanScript/KernelRfl.lean`)

`kernel_rfl` closes `a = b` with `Eq.refl a` and skips the elaborator's check. The kernel
still type-checks the whole declaration, so a wrong equation is still rejected (as a
kernel error at the declaration; I tested this). It also works on symbolic goals, which
`decide +kernel` can't handle.

I used it at every spot that had a raised heartbeat limit, and **all the `maxHeartbeats`
overrides are gone**:

| file                                   | spot(s)                                   | build time  |
| :------------------------------------- | :---------------------------------------- | ----------: |
| `TermTests/FibWindowTest.lean`         | `hstep` inside `window_eval` (was 400000) | 38 s → 16 s |
| `TermTests/ArrayRecToTermTest.lean`    | the three `tribArr`/`tetraArr` checks (were 800000) | 109 s → 90 s |
| `TermTests/NatRecDepthTest.lean`       | `hexanacci 8` (was 1000000)                | 61 s → 50 s |

Using `kernel_rfl` (or `decide +kernel`) for *all* value checks in
`ArrayRecToTermTest.lean` brought that file from ≈ 105 s to ≈ 49 s in a trial run. That
change is not applied, because it would rewrite every check in the file. The downside of
`kernel_rfl` is its error message: a failure is reported as a kernel type mismatch instead
of `rfl`'s "not definitionally equal" message.

### Structural fix (done, see section 4): a two-level catalogue

This fixes both problems at once:

```lean
inductive NatExtern     : MyTy → Type | lean_nat_add : Nat → Nat → NatExtern nat | …
inductive StringExtern  : MyTy → Type | lean_string_compare : … | …
inductive Float32Extern : MyTy → Type | …
-- one per family, e.g. following the `-- Init/…` section headers already in the file
inductive LeanInitPureExtern : MyTy → Type
  | nat     {τ} : NatExtern … τ     → LeanInitPureExtern τ
  | string  {τ} : StringExtern … τ  → LeanInitPureExtern τ
  | float32 {τ} : Float32Extern … τ → LeanInitPureExtern τ
  | …
```

`Extern.eval` then becomes a short outer `match`, calling one small `eval` per family.
Every inductive stays far below 244 constructors, so compiled `def`s work for every entry.
Per call, the kernel instantiates about 20 + 40 alternatives instead of 460.

To keep existing code (`.lean_nat_add a b`, `Extern.lean_array_fget …`) unchanged, the
generator can also emit, for every entry,

```lean
@[match_pattern, reducible] def LeanInitPureExtern.lean_nat_add … := .nat (.lean_nat_add …)
```

What would change:
- the catalogue file, split into families;
- `Eval/Extern.lean`, as one `eval` per family plus the dispatcher;
- `scripts/gen_externs.py`, so that `ExternTable.lean` records the family as well as the
  constructor;
- `ToTerm/Extern.lean` line 221, which builds the constructor by name and would wrap it in
  the family constructor.

The tests that use the dot names keep working if the `match_pattern` abbreviations are
generated.

## 4. Implemented: the two-level catalogue

**Layout.**
- `LeanScript/LeanInitPureExterns.lean`: each `-- Init/…` section is now an inductive of its
  own, a *family* (`PreludeExtern`, `StringBasicExtern`, `FloatExtern`, …). The two long
  sections `Init/Data/UInt/Basic.lean` (54 entries) and `Init/Data/SInt/Basic.lean` (92) are
  split by width (`UInt8BasicExtern` … `Int64BasicExtern`). Sections whose entries are all
  commented out (`Init/Data/Repr.lean`, `Init/Data/Nat/Gcd.lean`, the byte/float arrays,
  `IO`, `Promise`, `ShareCommon`) keep their commented entries but get no family.
  `LeanInitPureExtern` has one constructor per family (`preludeExtern`, `stringBasicExtern`,
  …). That gives 35 families, the largest with 55 entries (`Float32Extern`), and 460
  entries in all, as before.
- A family only has the parameters its entries use (that is how inductives in a
  `variable` context work), so each constructor of `LeanInitPureExtern` applies its family
  to those parameters. If an entry using another parameter (for example `option`) is added to a
  family, that constructor must be updated too. Lean reports it if you forget.
- `LeanScript/LeanInitPureExternShorthands.lean` (generated): for every entry, a
  `@[match_pattern, reducible] def LeanInitPureExtern.<entry>`, e.g.
  `LeanInitPureExtern.lean_nat_add a b = .preludeExtern (.lean_nat_add a b)`. Every shorthand
  takes all parameters of `LeanInitPureExtern`, in its order. So `.lean_nat_add a b` still
  works wherever an `Extern τ` is expected, both as a term and as a pattern. No test had to
  change.
- `LeanScript/Eval/Extern.lean`: one `eval` per family (`PreludeExtern.eval`, …) with the
  alternatives of the old `match`, unchanged, and `Extern.eval` as a 35-way dispatch.
- `scripts/gen_externs.py` reads the families and the constructor of each, and writes both
  `LeanScript/LeanInitPureExternShorthands.lean` and `LeanScript/ToTerm/ExternTable.lean`.
  The table still names the entry. That name is both the shorthand in
  `LeanInitPureExtern` and the constructor in its family.
- `LeanScript/ToTerm/Extern.lean` builds an entry by applying its shorthand to the
  catalogue's parameters, as it did with the constructor before. It then unfolds the
  shorthand, so translated terms contain the two constructors
  (`LeanInitPureExtern.preludeExtern (PreludeExtern.lean_array_fget …)`).

**Results** (same machine, old tree vs new tree):

| check | before | after |
| :---- | -----: | ----: |
| `decide +kernel`, 2000 calls of `Extern.eval (.lean_nat_add acc 1)` (kernel) | 4.5 s | 0.83 s |
| `decide`, 150 such calls (elaborator) | 0.70 s | 0.36 s |
| `def externCompare := .extern (.lean_string_compare "a" "b")` | "tag too big" | compiles and runs |
| build of `LeanScript.LeanInitPureExterns` | 33 s | 6 s (+ 4 s for the shorthands) |
| build of `LeanScript.Eval.Extern` | 24 s | 6 s |
| `rfl` for `hstep` in `TermTests/FibWindowTest.lean` (elaborator) | 15.6 s, needed 400000 heartbeats | 8.8 s, within the default budget |

The large test files (`ArrayRecToTermTest`, `NatRecDepthTest`) take about as long as before.
Their time goes into elaborating the translations and the value checks, not into extern
dispatch. The `kernel_rfl` uses stay, because they are still faster than `rfl`.

`TermTests/ExternTest.lean` now has a compiled definition that builds `lean_string_compare`
(the last entry, number 459 before). It also checks that the shorthand unfolds to the two
constructors and that the shorthands work as patterns.
