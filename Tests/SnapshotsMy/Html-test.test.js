// Tests of `Html-test.js`: the program of the single declaration `test` of
// `SnapshotsMy/Html.lean`, which `#lean_to_lean_term test` prints and
// `lean-to-js-backend --decl=test` writes.  The *module* cannot be compiled — the
// `deriving Repr` beside the type is a `partial def` — so this is the case the
// declaration-rooted compiler is for: only what `test` calls is translated.
//
// `Html` is a recursive `inductive`, so a value of it is `{ tag, _1, _2 }`: tag 0 is
// `elem (tag : String) (children : Array Html)` and tag 1 is `text (content : String)`.
import assert from "node:assert/strict";
import test_ from "node:test";

import { test } from "./Html-test.js";

const elem = (tag, children) => ({ tag: 0, _1: tag, _2: children });
const text = (content) => ({ tag: 1, _1: content });

test_("the builder monad accumulates the children of every element", () => {
  assert.deepEqual(
    test("bob"),
    elem("section", [
      elem("h1", [text("Posts for bob")]),
      elem("article", [
        elem("h2", [text("The first post")]),
        elem("p", [
          text("This is the first post."),
          text("Not much else to say."),
        ]),
      ]),
    ]),
  );
});

test_("the interpolated argument is the only thing that changes", () => {
  const a = test("alice");
  const b = test("bob");
  assert.equal(a._2[0]._2[0]._1, "Posts for alice");
  assert.equal(b._2[0]._2[0]._1, "Posts for bob");
  assert.deepEqual(a._2[1], b._2[1]);
});

test_("the whole tree is built, not shared with its builder", () => {
  const a = test("alice");
  a._2.pop();
  assert.equal(test("alice")._2.length, 2);
});
