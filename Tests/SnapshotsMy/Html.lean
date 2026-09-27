private inductive Html where
  | elem (tag : String) (children : Array Html)
  | text (content : String)
deriving Repr

-- 1. A builder monad that accumulates child nodes into an array
abbrev HtmlM := StateM (Array Html) Unit

-- 2. Automatically lift any `Html` node into the builder monad
private instance : Coe Html HtmlM where
  coe h := modify (·.push h)

-- 3. Base constructors
private def text (content : String) : Html :=
  Html.text content

private def mkElem (tag : String) (children : HtmlM) : Html :=
  let (_, nodes) := children.run #[]
  Html.elem tag nodes

-- 4. HTML tag functions (take a `do` block, return `Html`)
private def section_ (c : HtmlM) : Html := mkElem "section" c
private def article (c : HtmlM) : Html := mkElem "article" c
private def h1 (c : HtmlM)      : Html := mkElem "h1" c
private def h2 (c : HtmlM)      : Html := mkElem "h2" c
private def p (c : HtmlM)       : Html := mkElem "p" c

-- 5. The test function using pure `do` blocks
def test (user : String) : Html := section_ do
  h1 do
    text s!"Posts for {user}"
  article do
    h2 do
      text "The first post"
    p do
      text "This is the first post."
      text "Not much else to say."

-- 6. The whole program `test` is, as the backend models it: `HtmlM` and the
-- `recTaggedUnion` of `Html`, then the declarations `test` calls — callees first — and
-- `test` itself.  The *module* cannot be compiled: `deriving Repr` writes a
-- `partial def` beside the type, which the backend refuses.  The program of a
-- declaration that never calls it can, which is what this command compiles.
-- Refused since the type language dropped its unit type: `HtmlM` is
-- `StateM (Array Html) Unit`, and `Unit` has a single value carrying nothing at run
-- time, so there is no type to model it with.  A builder monad that returns something
-- observable — or one written in continuation-passing style — is compiled as before.
-- #lean_to_lean_term test

-- The `Coe` instance is not among them: LCNF had already copied its one field into the
-- `do` blocks that use it.  Pointed at on its own it *is* a program, and it is the
-- unboxed field — `instCoeHtmlHtmlM_coe` — rather than a record, which is how the
-- backend compiles every instance.
-- #lean_to_lean_term instCoeHtmlHtmlM

-- The JavaScript the same closure is emitted as sits in `Html-test.js`, written by
-- `lean-to-js-backend --decl=test SnapshotsMy/Html.lean`, with the rendering above in
-- `Html-test-Program.txt`.
-- #lean_to_lean_js test
