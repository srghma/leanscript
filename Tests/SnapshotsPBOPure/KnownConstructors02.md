# `KnownConstructors02`: our output compared with purescript-backend-optimizer

Files: `KnownConstructors02.lean` (the Lean port), `KnownConstructors02.purs` (the original),
`legacy-backend/KnownConstructors02.js` (purescript-backend-optimizer), and our outputs
`KnownConstructors02-pbo.js` / `KnownConstructors02-faithful.js` (and `-Term-*.txt`).
The variants are in `Tests/SnapshotsMy/KnownCtorExcept.lean`.

## `test`

```lean
def test (a : Except Int Int) : Int :=
  match some a with
  | some (Except.error b) => b
  | some (Except.ok c) => c
  | none => 42
```

purescript-backend-optimizer:

```js
const test = (a) => {
  if (a.tag === "error") { return a._1; }
  if (a.tag === "ok") { return a._1; }
  throw new Error("UNREACHABLE");
};
```

Ours, at both presets (unchanged by this work; it was already better):

```js
export const test = (a) => a._1;
```

* The known `some` is gone before our pipeline sees the code: even the unoptimised `Term` is a
  case analysis of `a` only (the `none => 42` arm is dead and dropped).
* Both arms answer the field at the same position, so the printer writes the arms once
  (`sameUnionArms`, `JsTerm/Print/Mini/Block.lean`): no tag test and no `UNREACHABLE` throw.
  Neither `Term` nor `JsTerm` has an expression "field `i` of a union, whatever its
  constructor", so this merge can only be seen once both arms are printed.

## Variants (`Tests/SnapshotsMy/KnownCtorExcept.lean`)

Already ideal before this work (both presets):

| Lean | JavaScript (`pbo`) |
|------|--------------------|
| the original | `(a) => a._1` |
| `Sum String String` | `(a) => a._1` |
| three constructors, first field each | `(t) => t._1` |
| through an inlined helper, or `some (some a)` | `(a) => a._1` |
| the same `* 2` in each arm | `(a) => int53__lean_int_mul(a._1, 2)` |
| different fields (`threeMixed`) | `(t) => (t.tag === 2 ? t._2 : t._1)` |
| `Except.ok x` known | `(x) => int53__lean_int_add(x, 1)` |
| two scrutinees (`knownPair`) | one test, on `b` only |

### What changed

**1. The same field, then more code** (`knownThenAdd`, `callAfter`):

```lean
def callAfter (f : Int → Int) (a : Except Int Int) : Int :=
  let v := match a with | .error b => b | .ok c => c
  f v + 1
```

Before:

```js
export const callAfter = (f, a) => {
  const x$1 = a._1;
  return int53__lean_int_add(f(x$1), 1);
};
```

Now:

```js
export const callAfter = (f, a) => int53__lean_int_add(f(a._1), 1);
```

(`knownThenAdd` is now `(a, k) => int53__lean_int_add(a._1, k)`; `faithful`: `a._1 + k`.)

**2. A loop whose state is rebuilt by a `match` on itself** (`countDown`). Before, every
iteration built the new state in a temporary and then copied it:

```js
    let x$3;
    if (p$1.tag === 0) {
      x$3 = { tag: 1, _1: int53__lean_int_add(p$1._1, 1) };
    } else {
      x$3 = { tag: 0, _1: int53__lean_int_sub(p$1._1, 1) };
    }
    p$1 = x$3;
```

Now each arm assigns the loop variable itself:

```js
    if (p$1.tag === 0) {
      p$1 = { tag: 1, _1: int53__lean_int_add(p$1._1, 1) };
    } else {
      p$1 = { tag: 0, _1: int53__lean_int_sub(p$1._1, 1) };
    }
```

The loop is still the `while (true)` loop with the counter (no recursion, so no stack growth).

### Where it is done, and why there

You asked for the `Term → Term` phase first. Neither rewrite can be done there:

* **1.** In `Term` the code is `join j (x) := f x + 1; case a of ctor#0(f) => jump j f | ctor#1(g) => jump j g`.
  `Term` cannot say "field 1 of `a`, whatever its constructor", so the only way to get rid of the
  join point is to write its body into both arms and rely on them being printed the same. That
  copies every call in the body into each arm. The `Term` optimiser is proved never to add calls
  (`Term.numCalls_optimize`), so the rewrite would break that theorem whenever the body makes a
  call, as `callAfter` does. `JsTerm` has no field projection for unions either, and it has no
  such count.
* **2.** The temporary `x$3` and the loop variable `p$1` only exist after conversion: in `Term`
  the loop is a recursion with an argument, and there are no mutable variables.
* The conversion `Term → JsTerm` builds join points one statement at a time and does not know
  what follows them, so it is not the right place either.

So both rewrites are one new `JsTerm → JsTerm` pass, `JsBlock.joinArms`
(`JsTerm/Lower/JoinArms.lean`), run first in the `JsTerm` optimiser (`shareWorkers`,
`JsTerm/Print/Share.lean`):

* **`JsBlock.joinIntoArms?`**: `join x { case s of … each arm: jump x (its one field) } rest`,
  where every arm takes apart the field at the same position, becomes `case s of … each arm: rest`.
  The arms are then the same statements, so the printer writes them once without a test, and the
  field is read where it is used (`a._1`). The guard (the same field position in every arm, and
  the same `rest`) is exactly what makes the printer's merge apply, so nothing is duplicated in
  the output.
* **`JsBlock.joinIntoAssign?`**: `join x { block } m = x; rest`, with `rest` not reading `x`:
  every jump `x = e; break` of `block` becomes `m = e; break`. A jump ends the block, so the
  assignment happens at the same point as before as far as anything reading `m` can tell, and
  `e` is still computed before `m` changes. Jumps out of loop bodies and closures go to their own
  join points, never to this one, so no assignment is moved into a loop.

One small printer change goes with 2 (`readInPlace`, `JsTerm/Print/Mini/Block.lean`): a field
of a mutable variable may be read in place (`p$1._1`) when the block's first statement assigns
that variable and the field is read only in the assigned expression, which runs before the
assignment. Without it, each arm above would start with `const { _1: f$3 } = p$1;`.

### Effect on the other snapshots

I regenerated all of them: every `--check` passes. The script still exits 1 because of
`KnownConstructors04`'s known `get!` panics. The only other output that changed is
`LoopState.minMaxSum` (both presets). Its last two lines

```js
  const x$12 = acc$1._1;
  return { _1: x$12._1, _2: { _1: x$12._2._1, _2: x$12._2._2 } };
```

are now one line, `return { _1: acc$1._1._1, _2: { _1: acc$1._1._2._1, _2: acc$1._1._2._2 } };`,
which has no temporary but reads `acc$1._1` three times. (Ideally this would be `return acc$1._1;`.
That needs the nested record eta, which `Term.recordEta` does not do yet.)

### Not translated (unchanged)

`for a in xs` over a `List`/`Array` of `Except` (`List.forIn'.loop` / `Array.forIn'.loop` cannot
be unfolded), and structural recursion over `List (Except Int Int)` (the built-in `List` has no
constructors of its own for `Term`), are rejected. This has nothing to do with known
constructors, so these functions are not in the variants file.

## Test

`knownConstructors02Spec` in `Tests/Main.lean` runs leanscript on both files and checks, at both
presets:

* `test` is `(a) => a._1` with no tag test and no throw;
* the variants' fragments are present, and `const x$`, `let x$` and `const { _1: f$` are absent;
* the generated `node` checks pass (4 for `KnownConstructors02`, 119 for `KnownCtorExcept`).
