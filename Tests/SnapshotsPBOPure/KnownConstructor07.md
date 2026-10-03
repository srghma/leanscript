# `KnownConstructor07`: our output compared with purescript-backend-optimizer

Files: `KnownConstructor07.lean` (the Lean port), `KnownConstructor07.purs` (the original),
`legacy-backend/KnownConstructor07.js` (purescript-backend-optimizer), and our outputs
`KnownConstructor07-pbo.js` / `KnownConstructor07-faithful.js` (and `-Term-optimized.txt`).

## `test`

Legacy:

```js
const test = (f, y) => {
  const z = f(y);
  return { bar: (z - 2) | 0, foo: (z + 1) | 0 };
};
```

Ours (preset `pbo`; the `faithful` preset writes `fy + 1n` / `fy - 2n` on `bigint`):

```js
export const test = (f, y) => {
  const fy = f(y);
  return { _1: int53__lean_int_add(fy, 1), _2: int53__lean_int_sub(fy, 2) };
};
```

This was already on par before this change: one call of `f`, kept in a constant, and the record
built directly. Neither intermediate record (`a`, `b`) is built, which is what the regression test
is about. Two differences remain, and neither can be removed:

* **`(z + 1) | 0` against `int53__lean_int_add(fy, 1)`.** PureScript's `Int` is 32 bits and wraps
  around. Lean's `Int` has no bound. Under `int=num`, a result that does not fit in 53 bits has to
  be reported, which is what the runtime's checked addition does. `| 0` would give a wrong
  answer instead.
* **The name `fy` instead of `z`.** The `Term` language does not keep source names. The printer
  names a constant holding `f(y)` the way purescript-backend-optimizer does when it has no name.

## `instReprPairBox.repr` (the `deriving Repr`; the PureScript file has no counterpart)

Before:

```js
export const instReprPairBox$repr = (x, prec) => {
  const x$1 = { tag: 3, _1: String(x._1) };
  const x$2 = { tag: 3, _1: String(x._2) };
  return { tag: 6, _1: { … x$1 … x$2 … }, _2: false };
};
```

Now it is a single expression, with each field's text written where it is used:

```js
export const instReprPairBox$repr = (x, prec) => ({
  tag: 6,
  _1: { … _2: { tag: 3, _1: String(x._1) } … _2: { tag: 3, _1: String(x._2) } … },
  _2: false,
});
```

**Why the constants were there.** `Repr Int` is `if i < 0 then Repr.addAppParen (toString i) prec
else toString i`. At precedence `0` both arms give the same text. In each arm Lean reads the field
again (`x.foo`), so the `Term` had, for each field,

```
join j (x8 : Format) := …
if lean_int_dec_lt(f5, 0) then
  let ⟨_ [0], _ [0]⟩ := x2      -- taken apart again, fields unused
  jump j ctor#3(lean_int_repr(f5))
else
  let ⟨_ [0], _ [0]⟩ := x2
  jump j ctor#3(lean_int_repr(f5))
```

Before this change the two arms were only merged after the `Term` phase, in `JsTerm`
(`MergeIte`), which left the join point's parameter as a constant. The unused case analyses could
not be dropped in `Term`, because doing so changes the level index of the arm.

**The change: `Term → Term` optimiser** (`LeanScript/Term/Optimize/SameJump.lean`, and
`Term.joinSame` in `LeanScript/Term/Optimize/KnownTest.lean`):

1. `Term.deadJumpHead?` reads the argument of a jump to the innermost join point through record case
   analyses whose fields the argument does not use. The argument is moved out of the fields by the
   strengthening renaming `URen.strN`.
2. `Branch.sameJumpArg?` recognises `if c then (…; jump j a) else (…; jump j a)` with the same `a`
   (`PExpr.same`).
3. `Term.joinSame`: such a join point is replaced by its body with `a` for its parameter
   (`Term.subst`), provided the parameter is used at most once (counted with `Term.countU`), so that
   `a` is never copied. The test and the case analyses are not needed because the language is pure
   and total.
4. When the two arms are the *same* statement but read the record's fields themselves, as in
   `if c then t.a + t.b else t.a + t.b`, `Term.zipTest` merges them into one statement. That
   statement ends in the jump, and the join point's body is written at that jump, under the case
   analyses (`Term.inlineTailJump`, `Term.joinViaZip`). `Term.zipTest` now also merges two jumps
   to the same join point with the same argument.

All of this is proved: the value does not change (`Term.joinSame_eval`, built from
`Term.deadJumpHead?_eval`, `Branch.sameJumpArg?_eval`, `Term.inlineTailJump_eval` and
`Term.joinViaZip_eval`, and the extended `Term.zipTest_eval`), and no call is added
(`Term.numCalls_joinSame`). `Term.optimize_eval` still depends only on `propext`,
`Classical.choice` and `Quot.sound`.

No change was needed in `Term → JsTerm` or in `JsTerm → JsTerm`. The file has no loop or recursion,
so labeled blocks and loops are not involved.

## Variants: `Tests/SnapshotsMy/ReprSameJump.lean`

* `fmtInt (x : Int) := repr x` is `(x) => ({ tag: 3, _1: String(x) })`.
* `showTriple`, `showNested` and `showMixed` (derived instances: three `Int`s, nested, and
  `Nat`/`Int`/`String`) have no sign tests left.
* `sameArg` (`if c then t.a + t.b else t.a + t.b`, then `g v`) is
  `(g, t, c) => g(int53__lean_int_add(t._1, t._2))`. Before, it was a constant and a `return`.
* `otherArg` (different arms) keeps its `if`.

Node checks: 14 per preset for `KnownConstructor07`, 24 per preset for `ReprSameJump`, all
passing.

## Other snapshots that changed

`CaseGuarded`, `RecordUpdate` and `ProfunctorLenses01` all have derived `Repr` instances with
`Int` fields. Each one lost its `const x$k = { tag: 3, _1: String(x._k) }` constants in the same
way, and every node check still passes.
