# `InlineArrayIndex.lean`: our output vs `InlineArrayIndex.js` (purescript-backend-optimizer)

```lean
@[inline] def array : Array Int := #[1, 2, 3] -- need to inline?
def test1 : Option Int := array[0]?
...
def test4 : Option Int := array[3]?
```

## Output

| | legacy (`InlineArrayIndex.js`) | ours (`InlineArrayIndex-pbo.js`; `-faithful.js` has `1n` …) |
| --- | --- | --- |
| `test1` | `{ tag: "some", _val: 1 }` | `{ tag: 1, _1: 1 }` |
| `test2` | `{ tag: "some", _val: 2 }` | `{ tag: 1, _1: 2 }` |
| `test3` | `{ tag: "some", _val: 3 }` | `{ tag: 1, _1: 3 }` |
| `test4` | `{ tag: "none" }` | `{ tag: 0 }` |
| `array` | not emitted | `export const array = [1, 2, 3];` |

Every `test` is already folded to a constant, the same as in the legacy output. The differences:

* **Tags and fields**: numeric tags and `_1` fields, the encoding used for every union in this
  project.
* **`array` is exported**. It is a public Lean definition, so it is part of the module's API.
  `@[inline]` asks for it to be inlined at its uses, and it is: no `test` refers to it. It
  does not ask for the definition to be dropped.

**`@[inline]` is not needed.** Without it the output is the same. While a definition is
translated to `Term`, the definitions it calls are unfolded. A call of an extern whose arguments
are all closed has no `Term` form (`Neu.extern` needs an open argument), so it is computed
at that point. `#[1, 2, 3][0]?` therefore becomes `ctor#1(1)` even before the `Term` optimiser
runs (see `InlineArrayIndex-Term-unoptimized.txt`). None of the three phases had anything left
to do for this file.

## What changed this run

1. **Checks of union results** (`LeanScriptCli/Check.lean`). Before, `--check` only checked
   `array`, because a result of a union type (`Option Int`) was never compared. A non-recursive
   union result (each field a `Nat`, `Int`, `Bool`, `String` or `Char`) is now printed as
   `i(f₁, …)`, the constructor index followed by the fields. In Lean this is done with
   `casesOn`, and in JavaScript with `showUnion` in the check prelude. Each preset now has 5
   checks (`array`, `test1` … `test4`), and all pass under node. Regenerating every snapshot
   added 274 checks to other files' check modules (for example `OptionUnbox` and `Variant01`).
   All of them pass, and no generated `.js` file changed.
2. **Accesses bounded by a test against a literal** (`Term -[convert]-> JsTerm`,
   `JsTerm/Lower/Bounds.lean`). This came up in the non-constant variant of this file,
   `array[i]?` with `i` a parameter. After inlining that is
   `i < 3 ? { tag: 1, _1: uint53__lean_array_get(0, [1, 2, 3], i) } : { tag: 0 }`, which checks
   the bounds twice. The facts gathered from enclosing tests now also include `i < k`, `i ≤ k`,
   `i == k`, `k ≤ i` and `k < i` against a literal `k`. An index known to be below `k` is in
   bounds:
   * for an array literal of at least `k` elements, and
   * for an array variable known to hold at least `k` elements.

   In those cases the access is the plain `a[i]`:
   ```js
   export const getOpt = (i) => (i < 3 ? { tag: 1, _1: [1, 2, 3][i] } : { tag: 0 });
   export const getSized = (a, i) => { if (a.length === 5) { return i < 5 ? a[i] : 1; } return 2; };
   ```
   This cannot be done in the `Term` phase: `Term` has no unchecked access, because the proof of
   bounds is erased. The new snapshot `Tests/SnapshotsMy/ArrayIndexBounds.lean` covers these
   cases, plus two where the test does not prove the bounds (`i < 4` on 3 elements), which keep
   the checked call. Its checks pass: 106 per preset.

## Tests

`inlineArrayIndexSpec` in `Tests/Main.lean` runs on both presets. It checks that `test1` …
`test4` are the constants above and that each preset has 5 checks. In `ArrayIndexBounds` it
checks that exactly the two unproved accesses keep `__lean_array_get(`. It runs every check
module under node.
