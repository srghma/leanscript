# `PrimOpArray01`: ours against `legacy-backend/PrimOpArray01.js`

| fn | `pbo` | `faithful` | legacy |
|---|---|---|---|
| `test1` | `(a) => a.length` | `(a) => BigInt(a.length)` | `(a) => a.length` |
| `test2` | `(inst, a) => a[2] ?? inst` | `(inst, a) => a[2] ?? inst` | `(a) => a[2]` |
| `test3` | `(a) => a.length` | `(a) => BigInt(a.length)` | `(a) => a.length` |
| `test4` | `(inst, a) => a[2] ?? inst` | `(inst, a) => a[2] ?? inst` | `(a) => a[2]` |

Before this change `test2`/`test4` were `(inst, a) => uint53__lean_array_get(inst, a, 2)` (a call
of `runtime.js`, imported).

* `test1`, `test3`: identical (`faithful` represents `Int` as `BigInt`, hence the conversion).
* `test2`, `test4`: the same access as legacy, plus `?? inst`.  Lean's `a[2]!` answers the
  `Inhabited` default when the array has fewer than three elements; legacy's `a[2]` answers
  `undefined` there.  `inst` is the `Inhabited α` instance, which is the default value itself.
  The `{ a // a.size > 0 }` of `test3`/`test4` is erased (a subtype is its value), and size `> 0`
  does not prove index `2` in bounds, so `test4` keeps the default.

`a[i] ?? d` is exact: no value of the language is `undefined` or `null`, and reading an array (or
a typed array) past its end gives `undefined`, so `??` takes the default exactly when `i` is out
of bounds.  JavaScript computes `a`, `i`, then (only out of bounds) `d`, so this form is only built
when the default is computed by no operation (a variable, a literal, a constructor of those).

Where it is done: the `Term` language has no access without a default (the proof of bounds is
erased, every `a[i]` is `Array.get!Internal`), so this cannot be a `Term → Term` rewrite.  It is
done in the conversion `Term → JsTerm` (`JsTerm/Lower/Bounds.lean`: `JsExpr.defaultGet?`, and
`JsExpr.condGet?` for `i < a.length ? a[i] : d`, the shape of `a.getD i d` and of
`if h : i < a.size then a[i] else d`), into the new `JsTerm` node `JsExpr.indexOr`, printed
`a[i] ?? d`.

There are no loops or recursion in this file, so labelled blocks and loops do not come into it.

Variants (`Tests/SnapshotsMy/ArrayGetDefault.lean`, 176 checks against Lean per preset):
`Bool`, `Option`, `String`, `Float`, `Int`, pairs, `ByteArray`, `UInt8` elements, two accesses
in one expression, `getD` with a literal and a constructor default, and `if h : i < a.size`.
