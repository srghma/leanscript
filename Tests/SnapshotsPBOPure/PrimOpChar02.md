# `PrimOpChar02`: the comparisons of `Char`, folded

```lean
@[inline] def charValues (op : Char → Char → Bool) : Array Bool :=
  #[op 'a' 'a', op 'a' 'b', op 'b' 'a']

def test1 := charValues (fun a b => a == b)
def test2 := charValues (fun a b => a != b)
def test3 := charValues (fun a b => decide (a < b))
def test4 := charValues (fun a b => a > b)
def test5 := charValues (fun a b => decide (a <= b))
def test6 := charValues (fun a b => decide (a >= b))
```

## Result

The output was already as good as the legacy output, or better, when this analysis began. Both
presets (`PrimOpChar02-pbo.js`, `PrimOpChar02-faithful.js`) print the same thing:

| fn | legacy (`legacy-backend/PrimOpChar02.js`) | ours |
|---|---|---|
| `charValues` | `(op) => [op("a")("a"), op("a")("b"), op("b")("a")]` | `(op) => [op("a", "a"), op("a", "b"), op("b", "a")]` |
| `test1` … `test6` | `[true, false, false]`, … | the same lines, with `export` in front |

* `test1` … `test6` match legacy line for line. The `Term` optimiser inlines `charValues` and
  the comparison, then folds each comparison of two literals: `PrimOpChar02-Term-optimized.txt`
  has only `ret #[true, false, false]`, ….
* `charValues` is one call with two arguments per element, where legacy makes two curried calls.
  Each call is written where it is used, in the program's order (no `const x$1 = …`).
* There are no loops or recursion here, so labelled blocks and loops don't come into it.
* Every check passes: 6/6 at each preset. `charValues` takes a function, so it has no checks.

## Variations

`PrimOpChar02` folds to literals, so it says little about how comparisons of characters are
written. I tried variations in `Tests/SnapshotsMy/CharCmpSelf.lean`. The main one is
`charValues` applied to an unknown character `c`:

```lean
@[inline] def charValuesAt (op : Char → Char → Bool) (c : Char) : Array Bool :=
  #[op c 'a', op 'a' c, op c c]
def v1 (c : Char) := charValuesAt (fun a b => a == b) c   -- … v6 as test1 … test6
```

| fn | before | now |
|---|---|---|
| `v1` (`==`) | `[c === "a", "a" === c, c === c]` | `[c === "a", c === "a", true]` |
| `v2` (`!=`) | `[c !== "a", "a" !== c, c !== c]` | `[c !== "a", c !== "a", false]` |
| `v3` (`<`) | `[c < "a", c > "a", c < c]` | `[c < "a", c > "a", false]` |
| `v4` (`>`) | `[c > "a", c < "a", c < c]` | `[c > "a", c < "a", false]` |
| `v5` (`<=`) | `[c <= "a", c >= "a", c >= c]` | `[c <= "a", c >= "a", true]` |
| `v6` (`>=`) | `[c >= "a", c <= "a", c >= c]` | `[c >= "a", c <= "a", true]` |
| `selfNat`, `selfInt`, `selfUInt8`, … | `[n === n, n < n, …]` | `[true, false, …]` |
| `selfFloat` | `[x === x, x < x, x <= x]` | unchanged: `x === x` is `false` for `NaN` |

Two problems showed up:

1. **A comparison of an operand with itself** (`op c c`) was computed at run time.
2. **A literal on the left of `===`**: `"a" === c`. The order comparisons (`<`, …) were already
   written with the literal on the right (`"a" < c` is `c > "a"`), but equality wasn't.

## What changed, phase by phase

**`Term → Term`** (`LeanScript/Term/Optimize/KnownCond.lean`, `KnownTest.lean`). This handles
problem 1, and is proved to keep `Term.eval`.

* `Neu.ordView?` recognises a call of `<` or `≤` on `Nat`, `Int`, `String` (and so `Char`, whose
  comparisons are those of one-character strings), and the fixed-width integers. `Neu.reflView?`
  adds the equality calls that `Neu.eqView?` already recognised. Each comes with the value the
  call has when its two operands are equal: `true` for `==` and `≤`, `false` for `<`.
* `Neu.reflLit?` gives that value when the two operands are written the same way (`PExpr.same`).
  `Neu.reflFold` turns such a call into its literal. `Neu.reflFold_eval` proves the value is
  unchanged.
* It is applied:
  * in `Neu.condSimp`, to every extern call it rebuilds (in answers, conditions, jumps);
  * in `Term.letEOrSubst`, to `let x := share n`: such a binding is replaced by its literal
    however often `x` is used. `Term.letEOrSubst_eval` and `Term.numCalls_letEOrSubst` still
    hold.
* `Float` is never folded: `x == x` is `false` for `NaN` in Lean and in JavaScript.

`Term.optimizeN_eval` and `Term.numCalls_optimizeN` still build, with no `sorry`.

**`Term → JsTerm`** (`JsTerm/Lower/FromTerm.lean`, `JsTerm/Lower/OrdCmp.lean`).

* **Fallback for problem 1.** In a function of several parameters the `Term` optimiser can't
  fold `s == s`. Folding would leave a parameter unused, which changes the level of an open body,
  and `Body.knownTestWalk` keeps that level. The conversion applies `Neu.reflFold` to every extern
  call too, so `selfMixed (s n i x)` is `[true, false, …]`. The `Term` output keeps the calls
  there (see `Tests/TermTests/Optimize/ReflCmpTest.lean`).
* **Problem 2.** `JsExpr.eqFlip?` writes `k === x` as `x === k`, and likewise for `!==`, when `k`
  is a literal and `x` isn't, or when both are parameters and the left one is bound later. It
  uses the same rule as the order comparisons (`JsExpr.swapOperands`). `===` is symmetric for
  every pair of values, including `NaN`. Reading a literal or a constant has no effect, so the
  order the operands are computed in doesn't matter. The operation stays the same inlined
  operation, so later rewrites still recognise it.
  * This could be done on `Term` too, by swapping the arguments of `lean_string_dec_eq`. But the
    level of a call is computed from its arguments in order, so each equality extern would need
    its own proof that the level is unchanged. It is a question of how the output reads, not of
    what gets computed, so it is done where the comparison is written.

**`JsTerm → JsTerm`:** nothing needed.

## Tests

* `Tests/SnapshotsMy/CharCmpSelf.lean`: 125/125 checks at each preset.
* `Tests/TermTests/Optimize/ReflCmpTest.lean`: the optimised `Term`s (`native_decide` on the
  printed statements), and the value of `selfMixed` (`Term.optimizeN_run`).
* `primOpChar02Spec` in `Tests/Main.lean` checks:
  * every legacy `const testN` line and our `charValues` line;
  * the `CharCmpSelf` lines;
  * that no `"a" === c`, `c === c` or `c < c` is left;
  * the node checks.
* I regenerated every snapshot. No other output changed, and every check passes.

## Not done

* `Char.toNat`, `Char.isDigit`, `Char.isAlpha`, `Char.toUpper`, `Char.isUpper` and
  `Char.isAlphanum` are still not translated ("`Char` is a leaf of the language"). They read the
  code point (`Char.val`), and no extern of the language gives it. Translating them needs a new
  extern, for example `Char → UInt32` written `c.codePointAt(0)`.
* Ordering of characters still compares UTF-16 code units, as legacy does. See
  `PrimOpChar01.md`. The constants in `astral` are folded by Lean, so they are right.
