module

@[expose] public section

set_option autoImplicit false

/-!
# Operations the generated module defines itself

Most operations of `JsTerm` are functions of `runtime.js`, which the generated module imports.
An operation over a datatype whose JavaScript representation the code generator chooses
itself (the cons cells of `List`, `ListRepr.taggedUnion`: `{ tag: 1, _1: head, _2: tail }` and
`{ tag: 0 }`) is instead **generated with the module**: its definition is written into the
module, next to the functions that use it, and it is not imported.  Only the operations a
module calls are written.

`localHelper? name` is the JavaScript definition (a `const`, not exported) of the operation
`name` when the module defines it itself.  The same operation is also a function of
`runtime.js` of the same name (so that the operation tables, generated from `runtime.js`, and
the tests of `runtime.js` against Lean still cover it); `lake exe tests` checks that the two
answer the same.
-/

namespace MoreJs

/-- `List.append` (`xs ++ ys`) on cons cells, written with the module: copies of the cells of
    `xs` in front of the cells of `ys`, which are shared, not copied (`xs` itself when `ys` is
    empty, `ys` itself when `xs` is).  A loop, so that a long `xs` does not overflow the stack;
    `O(|xs|)` cells. -/
def consListAppendJs : String :=
  "/** `List.append` (`xs ++ ys`) on the cons cells of this module (generated with the module,
 *  not imported): copies of the cells of `xs` in front of the cells of `ys`, which are shared.
 *  @template α
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} xs
 *  @param {({tag: 0}|{tag: 1, _1: α, _2: *})} ys
 *  @returns {({tag: 0}|{tag: 1, _1: α, _2: *})} */
const consList__lean_list_append = (xs, ys) => {
  if (xs.tag === 0) return ys;
  if (ys.tag === 0) return xs;
  const head = { tag: 1, _1: xs._1, _2: ys };
  let cur = head;
  for (let it = xs._2; it.tag === 1; it = it._2) {
    const c = { tag: 1, _1: it._1, _2: ys };
    cur._2 = c;
    cur = c;
  }
  return head;
};
"

/-- The JavaScript definition of the operation `name` when the generated module defines it
    itself instead of importing it from `runtime.js` (`none` for an imported operation). -/
def localHelper? (name : String) : Option String :=
  if name == "consList__lean_list_append" then some consListAppendJs else none

/-- Is the operation `name` defined by the generated module itself? -/
def isLocalHelper (name : String) : Bool := (localHelper? name).isSome

end MoreJs

end
