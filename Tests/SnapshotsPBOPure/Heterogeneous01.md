# Heterogeneous01: LeanScript output compared with purescript-backend-optimizer

`Heterogeneous01.lean` defines three structures (`R1`, `Fns`, `Args`) and an `@[inline]`
`zipRecord` that applies each field of a `Fns` (a record of closures) to the matching field
of an `Args`. Two definitions use it:

* `test1`: `zipRecord` applied to a literal `Fns` and a literal `Args`, so the whole thing is a
  constant;
* `test2 (args : Args)`: `zipRecord` applied to a literal `Fns` and the parameter.

## The legacy backend (`legacy-backend/Heterogeneous01.js`)

```js
const test1 = { a: 13, b: { fst: "bar", snd: 42.0 }, c: false };
const test2 = (r1) => ({ a: (1 + r1.a) | 0, b: { fst: "bar", snd: r1.b }, c: !r1.c });
```

## LeanScript's output (`Heterogeneous01-pbo.js`, `Heterogeneous01-faithful.js`)

```js
// pbo
export const test1 = { _1: 13, _2: { _1: "bar", _2: 42 }, _3: false };
export const test2 = (args) => ({
  _1: int53__lean_int_add(args._1, 1),
  _2: { _1: "bar", _2: args._2 },
  _3: !args._3,
});
// faithful
export const test1 = { _1: 13n, _2: { _1: "bar", _2: 42 }, _3: false };
export const test2 = (args) => ({ _1: args._1 + 1n, _2: { _1: "bar", _2: args._2 }, _3: !args._3 });
```

The code has the same shape as the legacy output. `test1` is folded to a constant, and `test2`
builds one record literal. Neither keeps a closure record, a `zipRecord` call or an
intermediate `Args`/`Fns` value. The `Term` optimiser already does all of it. The
`Term-optimized.txt` for `test2` is a single function that destructures `args` once, then
does `lean_int_add`, a `cond` (printed as `!`), and one constructor. The later phases only
print it, so there was nothing to add to `Term -[convert]-> JsTerm` or
`JsTerm -[optimize]-> JsTerm`. There is no control flow in this file, so labeled blocks and
loops don't come into it.

The remaining differences are deliberate:

| | legacy | LeanScript |
|---|---|---|
| `Int` addition | `(1 + r1.a) \| 0`: wraps around at 32 bits, which is wrong for Lean's unbounded `Int` (`2147483647 + 1` gives `-2147483648`) | `pbo`: `int53__lean_int_add` gives the exact result, or throws once the result no longer fits in 53 bits; `faithful`: `bigint`, always exact |
| field names | `a`, `b`, `c`, `fst`, `snd` | `_1`, `_2`, … (the convention for every generated record in this project) |
| parameter name | `r1` | `args`, the Lean name |

## Differential checks (changed in this run)

Before this run, `Heterogeneous01-*.check.mjs` contained **no checks**. The check generator
(`LeanScriptCli/Check.lean`) refused records with a `Float` field. A `Float` is compared by
its bits, but the generic `show` of the check module prints a number found inside a record the
way JavaScript does (`42`), while Lean's `toString` gives `42.000000`. `R1` contains
`String × Float`, and `Args` contains a `Float`.

Now a record field can be a `Float`, including in nested records. When a result holds a `Float`
inside a record, the check prints the JavaScript value with a printer chosen by the type
(`jsShowOf`): `floatBits` for a `Float` field, field by field for a record. This matches what
`showExpr` prints on the Lean side. Each preset now has 4 checks (`test1` and three calls of
`test2`), and all of them pass under node. When I regenerated every snapshot, only the
`Heterogeneous01` check modules changed, and no check failed.

`heterogeneous01Spec` in `Tests/Main.lean` checks both presets: it pins the shape of `test1`
and `test2` and runs the checks under node.
