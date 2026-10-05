# `PrimOpChar01`: comparisons of `Char`

```lean
def test1 (a b : Char) : Bool := a == b
def test2 (a b : Char) : Bool := a != b
def test3 (a b : Char) : Bool := a < b
def test4 (a b : Char) : Bool := decide (a > b)
def test5 (a b : Char) : Bool := a <= b
def test6 (a b : Char) : Bool := decide (a >= b)
```

## Result

Both presets (`PrimOpChar01-pbo.js`, `PrimOpChar01-faithful.js`) now print exactly the lines of
`legacy-backend/PrimOpChar01.js`, with `export` in front:

| fn | legacy | before | now |
|---|---|---|---|
| `test1` | `a === b` | `a === b` | `a === b` |
| `test2` | `a !== b` | `a !== b` | `a !== b` |
| `test3` | `a < b` | not translated | `a < b` |
| `test4` | `a > b` | not translated | `a > b` |
| `test5` | `a <= b` | not translated | `a <= b` |
| `test6` | `a >= b` | not translated | `a >= b` |

Before, `test3` … `test6` failed with "`Char` is a leaf of the language: its values are
literals, not constructor applications". All 96 checks against Lean pass at each preset.

## Why they were refused

Lean decides `a < b` on `Char` with `Char.instDecidableLt a b := a.val.decLt b.val`, and `a ≤ b`
with `Char.instDecidableLe`. Both look inside the character (`Char.val`, a `UInt32`). In the
language a `Char` is a leaf: its values are literals and nothing can look inside them. There is
no extern on characters to compare with. `==` had already been handled by comparing the
one-character strings `"".push a` and `"".push b`.

## What changed, phase by phase

**Lean → `Term`** (`LeanScript/TermElab/ToTerm/Expr/Calls.lean`, `trDecide`). This is where the
instance is read. The same trick as for `==` works here:

* `decide (a < b)` becomes `decide ("".push a < "".push b)`, which is the extern `String.decidableLT`
  (`lean_string_dec_lt`);
* `decide (a ≤ b)` becomes `!decide ("".push b < "".push a)`, which is how `String.decLE` decides
  `≤` on strings.

Both are proved in `LeanScript/TermElab/ToTerm/CharEq.lean`, with no `sorry` and only the
standard axioms: `char_push_lt_iff`, `char_le_iff_not_lt`, `decide_char_lt_push`,
`decide_char_le_push`. In JavaScript `"".push c` is just `c` (a `Char` is a one-character string),
so the optimised `Term` already has the shape of the legacy output:

```
test3: ret lean_string_dec_lt(lean_string_push("", x2), lean_string_push("", x4))
test4: ret lean_string_dec_lt(lean_string_push("", x4), lean_string_push("", x2))
test5: ret cond(lean_string_dec_lt(lean_string_push("", x4), lean_string_push("", x2)), false, true)
test6: ret cond(lean_string_dec_lt(lean_string_push("", x2), lean_string_push("", x4)), false, true)
```

**`Term → Term`.** Nothing to do: the optimised `Term` is minimal. `Term`'s externs are Lean's,
which only compare with `<` (and, for numbers, `≤`). So `Term` cannot say `a > b` or `a >= b`.

**`Term → JsTerm`** (new `JsTerm/Lower/OrdCmp.lean`, called from `JsTerm/Lower/FromTerm.lean`).
With only the change above, the output was the same as `PrimOpString01`'s: `b < a`, `!(b < a)`,
`!(a < b)`. The conversion now writes a comparison with the operator that reads best:

* `!(x < y)` becomes `x >= y` and `!(x <= y)` becomes `x > y`. The operands stay in the same
  order. This is done only on types that JavaScript orders totally: booleans, integers as
  `number` or `BigInt`, and strings. It is never done on floats, where `!(a < b)` is not
  `a >= b` because of `NaN`.
* `c ? false : y` becomes `c' && y`, and `c ? y : true` becomes `c' || y`, where `c'` is the
  opposite comparison.
* The operands are swapped (`b < a` becomes `a > b`) only when this cannot change what is
  computed:
  * two parameters of the same function, with the parameter to the left written on the left.
    It does not apply to any two constants: `i < n` with a loop counter `i` stays as it is.
    The conversion now records the parameters of the innermost enclosing function
    (`Names.params`);
  * a literal on the left with something else on the right (`"z" >= c` becomes `c <= "z"`).

  Any other comparison (`i < a.length`, `y < 64`, `b + 1 < a`) is left as it is. This keeps the
  shapes that later rewrites look for.

The comparison node `JsExpr.boolCmp` (added for booleans by `PrimOpBoolean01`) now takes operands
of any terminal type. The identities are proved in a small model of the ECMAScript relational
operators (`JsOrd`), which defines `>`, `<=` and `>=` from *IsLessThan*, with `undefined` for
`NaN`:

* `JsOrd.eval_flip`: `y > x` is `x < y`, and so on, for any *IsLessThan*;
* `JsOrd.eval_neg`: `!(x op y)` is `x op' y` when *IsLessThan* is never `undefined`;
* `JsOrd.eval_neg_needs_total`: without that condition the negation fails, which is why floats are
  excluded.

The conversion code itself is not formally verified; the generated checks back it up.

**`JsTerm → JsTerm`.** Not needed.

This file has no loops or recursion, so labelled blocks and loops don't come into it.

## Other outputs that changed

The same rewrites apply wherever Lean writes `>` or `≥`. For example, `PrimOpString01`'s
`test4`…`test6` were `b < a`, `!(b < a)`, `!(a < b)` and are now `a > b`, `a <= b`, `a >= b`, as
in legacy. `TestNat$gt`/`$ge` in `PrimOpNumber01` are now `a > b`/`a >= b` instead of `b < a`/
`b <= a`. The new snapshot `Tests/SnapshotsMy/OrdCmp.lean` covers `Nat`, `Int`, `UInt8`, `UInt32`,
`String`, `Char` (with literals: `c >= "a" && c <= "z"`), computed operands and floats. It passes
291/291 checks at each preset.

## Caveat (unchanged)

Ordering of characters inherits the limit of `String` ordering listed in `NOT_IMPLEMENTED.md`.
JavaScript's `<` compares UTF-16 code units and Lean compares code points, so the two disagree when
one character is above `U+FFFF` and the other is in `U+E000`–`U+FFFF`. The legacy output has the
same behaviour, because a PureScript `Char` is a UTF-16 code unit.
