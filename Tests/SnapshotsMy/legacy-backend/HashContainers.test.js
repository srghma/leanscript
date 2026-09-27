// Tests of `HashContainers.js`: Lean's own hash-container implementation, compiled.
// The functions take a Lean `List` of strings (or of numbers) and answer with a number,
// an `Option` or a `List`.
import assert from "node:assert/strict";
import test from "node:test";

import { test1, test2, test3, test4, test5, test6, test7 } from "./HashContainers.js";
import { list, none, ofList, some } from "../runtime/lean_values.mjs";

test("test1 counts the distinct keys of a string-keyed map", () => {
  assert.equal(test1(list([])), 0);
  assert.equal(test1(list(["a"])), 1);
  assert.equal(test1(list(["a", "b", "a"])), 2);
});

test("test2 looks 3 up in a number-keyed map", () => {
  assert.deepEqual(test2(list([])), none);
  assert.deepEqual(test2(list([3])), some(9));
  assert.deepEqual(test2(list([1, 2, 3, 4])), some(9));
  assert.deepEqual(test2(list([1, 2, 4])), none);
});

test("test3 is the size of a set, plus one when it holds \"a\"", () => {
  assert.equal(test3(list([])), 0);
  assert.equal(test3(list(["a"])), 2);
  assert.equal(test3(list(["b", "c"])), 2);
  assert.equal(test3(list(["a", "a", "b"])), 3);
});

test("test4 adds the sizes of a map and a set built from the same list", () => {
  assert.equal(test4(list([])), 0);
  assert.equal(test4(list(["a"])), 2);
  assert.equal(test4(list(["a", "b", "a"])), 4);
});

test("test5 erases two keys, each out of its own copy of the map", () => {
  assert.equal(test5(list([])), 0);
  assert.equal(test5(list(["a"])), 1);
  assert.equal(test5(list(["a", "b"])), 101);
  assert.equal(test5(list(["a", "b", "c"])), 202);
});

test("test7 reads a key out of a map of string lengths", () => {
  assert.equal(test7(list([]), "a"), 0);
  assert.equal(test7(list(["ab", "c"]), "ab"), 2);
  assert.equal(test7(list(["ab", "c"]), "zz"), 0);
});

test("test6 answers with the keys of the map", () => {
  // Which order the entries come out in is decided by the hash of the keys, and the
  // hash a JavaScript runtime gives a string is not the one Lean's runtime gives it,
  // so only the *set* of keys is a property of the compiled program.
  assert.deepEqual(ofList(test6(list([]))), []);
  assert.deepEqual(ofList(test6(list(["a"]))), ["a"]);
  assert.deepEqual(ofList(test6(list(["a", "b", "a"]))).sort(), ["a", "b"]);
  assert.deepEqual(ofList(test6(list(["b", "a"]))).sort(), ["a", "b"]);
});
