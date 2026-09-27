// Tests of `StringWalk.js`.  A Lean string position is a *byte* offset into the UTF-8
// encoding of the string, so the answers below count bytes and not characters: in
// "héllo" the 'l' starts at byte 3, because 'é' takes two bytes.
import assert from "node:assert/strict";
import test from "node:test";

import { test1, test1_go, test2, test3, test4, test4_go } from "./StringWalk.js";

test("test1 counts the occurrences of a character", () => {
  assert.equal(test1("banana", "a"), 3);
  assert.equal(test1("", "a"), 0);
  assert.equal(test1("héllo", "l"), 2);
});

test("test2 answers with the byte position of the first occurrence", () => {
  assert.equal(test2("banana", "n"), 2);
  assert.equal(test2("héllo", "l"), 3);
  // no occurrence: the walk ends at the end of the string, which is its byte size
  assert.equal(test2("abc", "z"), 3);
});

test("test4 sums the indices below the character length of the string", () => {
  assert.equal(test4(""), 0);
  assert.equal(test4("abcd"), 6);
  assert.equal(test4("héllo"), 10);
});

test("test3 adds the byte size of a string that grows by one character a step", () => {
  assert.equal(test3("ab", 0), 0);
  assert.equal(test3("ab", 3), 9);
  assert.equal(test3("é", 2), 5);
});

test("the loops of the local `go` functions are entered directly too", () => {
  assert.equal(test1_go("banana", "a", 0, 0), 3);
  assert.equal(test1_go("banana", "a", 2, 10), 12);
  assert.equal(test4_go("abcd", 0, 0), 6);
  assert.equal(test4_go("abcd", 2, 0), 5);
});
