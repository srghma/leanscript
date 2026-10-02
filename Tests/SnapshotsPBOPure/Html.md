# `Html.lean` compared with `legacy-backend/Html.js`

## Before

Nothing was translated:

```
// not translated:
//   instReprHtml.repr: a `partial` definition
//   test: LeanScript: the recursive type Html is not declared in any signature; declare it with `leanscript_signature`
```

`Html` is a *nested* inductive type: it recurses through `List` (`elem (tag : String) (children : List Html)`).
The `leanscript` tool reads `List α` as the built-in list (`Ty.list`, a JavaScript array on the
`pbo` preset), and a recursive occurrence inside the built-in list cannot be declared in the
signature (`Fld` has no list), so the automatic signature (`autoSignature`) refused `Html`, and
`test` could not be translated.

## The fix (Lean → `Term`, the elaboration, before all three phases)

`LeanScript/GenElab/Read.lean` (`listNestedInElem`, used by `classify`): a list type
`List T` that is a field type of a constructor of a nested inductive type `T` mentions
(`List Html` in `Html.elem`) is part of that type's recursion, so it is read as a datatype
(`nil | cons Html (List Html)`, a member of the block of `Html`) even when lists are otherwise
built-in. The decision depends only on the type, so `List Html` reads the same everywhere in a
program; other lists (`List String`, `List Nat`, …) are still built-in arrays.

No change to the `Term` optimiser, the conversion or the `JsTerm` optimiser was needed: the
`Term` of `test` already is one constructor tree (`Html-Term-optimized.txt`), and it prints as
one object literal.

## After (`Html-pbo.js`; `Html-faithful.js` is identical apart from the header)

```js
export const test = (user) => ({
  tag: 0,
  _1: "section",
  _2: {
    tag: 1,
    _1: { tag: 0, _1: "h1", _2: { tag: 1, _1: { tag: 1, _1: "Posts for " + user }, _2: { tag: 0 } } },
    _2: { tag: 1, _1: { tag: 0, _1: "article", _2: … }, _2: { tag: 0 } },
  },
});
```

| | legacy (`purescript-backend-optimizer`) | ours |
| :-- | :-- | :-- |
| `test` | one object literal, `List Html` as cons cells | the same: one object literal, cons cells, no statement, no call |
| tags / fields | `tag: "elem"`, `_tag`, `_children`, `_head`, `_tail` | `tag: 0`/`1`, `_1`, `_2` (the naming of every datatype in this project; shorter, numeric comparisons) |
| `render` | emitted, but not exported (dead code), via `$List$map`/`$String$intercalate` | not emitted: it is `private` (not part of the module's interface) |

So the output of `test` is on par with the legacy backend, and the module is smaller (no dead
`render`). There are no loops or recursion in `test`, so labeled blocks and loops do not come
into it.

## Tests

`htmlSpec` in `Tests/Main.lean` translates the file on both presets, checks that `test` is one
object literal with no statement and no call, and runs it under node on three users (one with
quotes), rendering the result in JavaScript with the same function as the file's `render`, and
compares with Lean's `render (test user)` on a copy of the definitions.
`leanscript --check` writes no check for `test`, because the check generator cannot yet show a
value of a recursive datatype.

## Not done

* A public `render` would still not be translated: it is defined by well-founded recursion
  (through `List.map`), which the tool refuses.
* The parts of the tree that do not depend on `user` (the whole `article` subtree) could be
  built once, as constants of the module, instead of on every call; the legacy backend does not
  do this either.
