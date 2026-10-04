# `KnownConstructors.lean` compared with purescript-backend-optimizer (legacy)

There is no `legacy-backend/KnownConstructors.js`; this file gathers the cases of
`KnownConstructors02`–`06`, whose legacy outputs are in `legacy-backend/KnownConstructors0*.js`.
The comparison below is per function (`pbo` preset; `faithful` is the same with `BigInt`
literals such as `42n`).

| function | legacy | ours | verdict |
| --- | --- | --- | --- |
| `known1` | (no counterpart) | `export const known1 = "b";` | constant folded |
| `test1` (`02`) | two tag tests, `return a._1` in each, `throw "UNREACHABLE"` | `(a) => a._1` | better |
| `test2` (`03`) | `if (x > 42) return "Hello, World!"; return "";` | `(x) => (42 < x ? "Hello, World!" : "")` | same |
| `test3` | (`04` has `none` in the else arm) | `42 < x ? ["Hello, World", "Hello, Universe"] : ["Default, World", "Default, Universe"]` | on par: no record, one test, all strings folded |
| `test4` | `f("Hello, World")("Hello, Universe")` (on the `none` variant of `04`) | see below | **improved in this change** |
| `test5` | `if (x > 42) return false; throw …` | `(x) => false` | better |
| `fromString` | chain of `if`s returning `$Option$some(Foo)` … `$Option$none` | same chain, last case `s === "qux" ? {tag:1,_1:3} : {tag:0}` | same |
| `test6` (`05`) | chain of `if (a === "foo") return 1; …; return 0;` | same chain, last case `a === "qux" ? 4 : 0` | same |

## `test4`

```lean
def test4 (f : String → String → String) (x : Int) : String :=
  let a := if x > 42 then some "Hello" else some "Default"
  match a with
  | some s => f (s ++ ", World") (s ++ ", Universe")
  | none => ""
```

Before (strings concatenated at run time):

```js
export const test4 = (f, x) => {
  const x$1 = 42 < x ? "Hello" : "Default";
  return f(x$1 + ", World", x$1 + ", Universe");
};
```

After (all strings are literals, one comparison, no record, one call of `f`):

```js
export const test4 = (f, x) => {
  const x$1 = 42 < x;
  return f(
    x$1 ? "Hello, World" : "Default, World",
    x$1 ? "Hello, Universe" : "Default, Universe",
  );
};
```

Writing `42 < x ? f("Hello, World", "Hello, Universe") : f("Default, World", "Default, Universe")`
would copy the call of `f`; the `Term` optimiser is proved never to add calls
(`Term.numCalls_optimize`), so the choice stays inside the arguments, as for `test2` of
`KnownConstructors04`.

### The change (`Term → Term`)

`Term.shareSubst` (`LeanScript/Term/Optimize/CondJump.lean`) writes a shared conditional
`let x := share (c ? a : b)` where it is used.  It did so when `x` was used once or only as the
operand of case analyses.  It now also does so when `a` and `b` are constants and every use of `x`
is an argument of an extern call whose other arguments are constants (`Term.onlyFoldUse`).
After that, `Neu.condFold` (`Term.arithWalk`) folds each call into a conditional of two literals,
and hoisting shares the repeated test `42 < x` again.  The condition is gathered in
`Term.shareSubstOk`; the proofs `Term.shareSubst_eval` and `Term.numCalls_shareSubst` are
unchanged apart from naming it, and `Term.optimize_eval` / `Term.numCalls_optimize` still hold
(axioms: `propext`, `Classical.choice`, `Quot.sound`).

No loops or recursion occur in this file, so labelled blocks and loops are not involved.

## Variants: `Tests/SnapshotsMy/KnownCtorCondConst.lean`

| function | output (`pbo`) |
| --- | --- |
| `twoAppends` | as `test4` above |
| `intOps` | `const x$1 = 42 < x; return f(x$1 ? 11 : 21, x$1 ? 30 : 60);` |
| `threeUses` | `0 < x ? ["pos!", "<pos", "yes"] : ["neg!", "<neg", "no"]` |
| `usesInArms` | `const x$1 = 0 < x; if (0 < y) return f(x$1 ? "a1" : "b1"); return f(x$1 ? "a2" : "b2");` |
| `alsoDirect` | unchanged on purpose (`x` also passed as is): `const x$1 = 0 < x ? "a" : "b"; return f(x$1, x$1 + "!");` |
| `natOps` | `const x$1 = 5 < x; return f(x$1 ? 9 : 11, x$1 ? 6 : 8);` |

Node checks against Lean: 31 per preset for `KnownConstructors`, 51 per preset for the variants,
all passing.  No other snapshot output changed.
