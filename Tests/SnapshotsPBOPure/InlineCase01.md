# `InlineCase01.lean` compared with `legacy-backend/InlineCase01.js`

## The output (`InlineCase01-pbo.js`; `-faithful.js` has `1n` and `a + 1n` instead)

```js
export const test1 = (f, o) => {
  if (o.tag === 0) {
    return f();
  }
  return int53__lean_int_add(o._1, 1);
};
export const test2 = (f, g, o) => {
  if (o.tag === 0) {
    return f();
  }
  return g(1, o._1);
};
// test3 is test1 and test4 is test2 (parameter `a` instead of `o`)
export const test5 = (a, g, a1) => {
  if (a1.tag === 0) {
    return int53__lean_int_add(a, 1);
  }
  return g(1, a1._1);
};
```

This was already the output before this run: the `Term -[optimize]-> Term` phase inlines
`maybe`/`maybe'` (`@[inline]`) and `Option.elim`, applies the inlined lambda to the field, and
puts the forcing of the lazy default `f ()` into the `none` branch
(`InlineCase01-Term-optimized.txt`). The convert phase then makes each `testN` one function of
all its parameters and makes `g 1` applied to the field a single call `g(1, o._1)`.

## Compared with the legacy backend

| | legacy (`purescript-backend-optimizer`) | ours |
| :-- | :-- | :-- |
| shape | curried: `f => { const $0 = f(); return v2 => { … } }` | one function of all parameters, `(f, o) => { … }` |
| closures allocated per call | one (`v2 => …`), plus `$1 = g(1)` in `test2`/`test4`/`test5` | none |
| lazy default `f()` | called **eagerly**, once per partial application, even when the option is `some` | called only in the `none` branch |
| `g 1` | `$0 = g(1)` (a closure), then `$0(v2._val)` | `g(1, o._1)`: one direct call, no intermediate closure |
| tag test | `if none … if some … throw new Error("UNREACHABLE")` | one test `o.tag === 0`, no unreachable `throw` |
| `x + 1` on `Int` | `1 + v2._val \| 0`: wraps at 32 bits, which is wrong for Lean's `Int` | exact: `int53__lean_int_add` (throws past 53 bits) on `pbo`, `bigint` on `faithful` |
| `maybe`/`maybe'` | not emitted (inlined) | not emitted (private and inlined) |

So the output is ahead of the legacy one: shorter, no closure, no eager call, no dead `throw`.
There are no loops or recursion in this file, so labeled blocks and loops do not come into it.

Remaining (cosmetic) differences:

* **Parameter names**: `test3`/`test4`/`test5` take the option as `a` (`a1` in `test5`,
  where `a` is taken): the name Lean gives the unnamed parameter of `Option α → β`.
* **Type parameters in the JSDoc**: `α`/`β` are read at `Nat`, so the JSDoc says
  `uint53(number)` (`nat(bigint)` on `faithful`) for them. The code itself never looks at
  such a value, so the functions work on values of any type.

## What changed in this run: the checks

Before, the check modules had 12 checks per preset (`test1` and `test3`). `test2`, `test4`
and `test5` had none, because the check generator (`LeanScriptCli/Check.lean`) had no sample
for a parameter `g : Int → α → β` (a function of **two** arguments). There is now a sample type
`SType.fn2` for functions of two `Nat`/`Int` arguments with a `Nat`/`Int` result. It is passed
as two fixed functions, `x * 10 + y` and `y * 3 - x` (cut at 0 for a `Nat` result), written in
Lean and as a JavaScript `(x, y) => …`. That is how the generated code calls such a function
(`g(1, o._1)`), with a `BigInt`/`Number` conversion when the representations of the arguments
and the result differ. Each preset now has 78 checks (6 for each of `test1` and `test3`, 12 for
each of `test2` and `test4`, 42 for `test5`), and all of them pass under node.
Regenerating every snapshot also added checks to two other files: 17 per preset to
`Tests/SnapshotsMy/AppArity` (`test4`, whose `f : Nat → Nat → Nat` is now sampled) and 4 per
preset to `PrimOpInt02Configurable` (`TestNat.intValues`, `TestInt.intValues`). They all pass,
and no `.js` output changed.

## Tests

`inlineCase01Spec` in `Tests/Main.lean` translates the file on both presets. For each `testN`
it checks that the function is exactly one tag test with the two `return`s above, that there is
no `maybe`, no `elim` and no returned closure, and that there are 78 checks, including checks of
`test2`/`test4`/`test5` with functions of two arguments. It then runs the checks under node.
