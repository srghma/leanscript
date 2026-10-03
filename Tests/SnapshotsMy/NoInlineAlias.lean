-- A definition marked `@[noinline]` that another one only renames: the JavaScript refers to it
-- (`export const test = foo;`), as purescript-backend-optimizer does for `inline never`
-- (`Tests/SnapshotsPBOPure/InlineNever.js`).  Without the attribute a literal constant stays
-- the literal (`test2`, as in `Tests/SnapshotsPBOPure/InlineNever.lean`).
@[noinline] def foo : String := "foo"
def test : String := foo
def bar : String := "bar"
def test2 : String := bar
@[noinline] def big : Array Nat := #[1, 2, 3]
def test3 : Array Nat := big
-- inside a larger expression the definition is still unfolded (`Term` has no global names)
def test4 : String := foo ++ "!"
