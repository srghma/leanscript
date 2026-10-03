# `InlineNever.lean` compared with `InlineNever.js` (purescript-backend-optimizer)

## The output (`InlineNever-pbo.js`; `-faithful.js` is the same apart from the header)

```js
export const foo = "foo";
export const test = "foo";
```

purescript-backend-optimizer writes:

```js
const foo = "foo";
const test = foo;
export { foo, test };
```

## Comparison

| | purescript-backend-optimizer | ours |
| :-- | :-- | :-- |
| `foo` | `"foo"` | `"foo"` |
| `test` | `foo` (a read of another binding) | `"foo"` (the literal) |
| size | same | same |

Ours is the same size and reads no other binding. The PureScript test marks `foo` as
`inline never`, which is why its output keeps `test = foo`. The Lean file has no such
attribute, so the literal is the better output. This was already our output: the step that
turns Lean into `Term` already gives `ret "foo"` for `test` (`InlineNever-Term-unoptimized.txt`),
and the convert step deliberately keeps a constant whose value is a literal as that literal
instead of writing it as another name (`aliasFuns`, `JsTerm/Lower/Module.lean`). None of the
three phases has work left for this file. It has no loops or recursion, so labeled blocks and
loops don't come into it.

## Added in this run: `@[noinline]`, the Lean counterpart of `inline never`

A definition that only renames an earlier one that is marked `@[noinline]` now refers to it, even
when the value is a literal (`aliasFuns` takes the names of the translated `@[noinline]`
definitions, collected in `LeanScriptCli/Main.lean`). `Tests/SnapshotsMy/NoInlineAlias.lean`:

```lean
@[noinline] def foo : String := "foo"
def test : String := foo          -- export const test = foo;      (as purescript-backend-optimizer)
def bar : String := "bar"
def test2 : String := bar         -- export const test2 = "bar";   (no attribute: the literal)
@[noinline] def big : Array Nat := #[1, 2, 3]
def test3 : Array Nat := big      -- export const test3 = big;
def test4 : String := foo ++ "!"  -- export const test4 = "foo!";
```

Limitation: `@[noinline]` is honoured only for a definition that is exactly another name for it.
Inside a larger expression (`test4`) the definition is still unfolded and folded, because
`Term` has no global names. A reference to `foo` from within an expression would need those.

## Testing

* `inlineNeverSpec` in `Tests/Main.lean` (both presets) checks the lines above for both files
  and runs their checks under node (2 for `InlineNever`, 7 for `NoInlineAlias`, per preset).
* Regenerating the other snapshots that use `@[noinline]` left their outputs unchanged.
