// Building and reading the values a compiled module takes and answers with.
//
// The backend represents a value of a Lean inductive type as `{ tag, _1, _2, … }`: the
// number of the constructor, in declaration order, and its fields, numbered from one.
// So `List` is `{ tag: 0 }` / `{ tag: 1, _1: head, _2: tail }` and `Option` is
// `{ tag: 0 }` / `{ tag: 1, _1: value }`.  A `Nat`, an `Int` and a `String.Pos.Raw` are
// JavaScript numbers, a `String` is a JavaScript string and an `Array` is a JavaScript
// array.  These helpers are for the tests only; nothing the backend emits needs them.

/** The Lean `List` of the elements of a JavaScript array. */
export const list = (xs) => {
  let out = { tag: 0 };
  for (let i = xs.length - 1; i >= 0; i--) out = { tag: 1, _1: xs[i], _2: out };
  return out;
};

/** The elements of a Lean `List`, as a JavaScript array. */
export const ofList = (xs) => {
  const out = [];
  let cur = xs;
  while (cur.tag === 1) {
    out.push(cur._1);
    cur = cur._2;
  }
  return out;
};

/** `Option.none`. */
export const none = { tag: 0 };

/** `Option.some x`. */
export const some = (x) => ({ tag: 1, _1: x });
