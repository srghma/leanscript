# Recursive datatypes in JavaScript: a proposal for fast code

This file replaces §3 (`data (name : String)`) of `JsTermReviewPlan.md`. It is a design, not
an implementation: nothing below exists in the code yet. It answers one question: how should
`JsTerm` represent and traverse recursive datatypes (`List`, user inductives, mutual blocks) so
that the generated code is as fast as code written by hand, like this:

```js
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
```

The two properties that make this code fast are the targets of the whole design:

1. **The layout is the plain constructor layout.** A `List` is a linked list of small objects of
   one fixed shape (`{ tag, _1, _2 }`), not an array and not a class instance. V8 gives every
   cell the same hidden class, and `cur.tag === 1`, `cur._1` and `cur._2` are monomorphic loads.
2. **A traversal is a loop, not a recursion.** `ofList` walks the list with a `while` loop and
   a mutable cursor. It uses no stack, so it works on a list of ten million elements, where a
   recursive function would overflow V8's stack after about ten thousand frames.

The rest of the file says how to get both from `Term` automatically.

---

## 1. Where we are

- `JsTy.data (name : String)` is a bare name. The backend knows nothing about its layout, and
  every construct that touches a declared datatype (`data_in`, `data_out`, `data_rec`,
  `data_brec`) is refused by `FromTerm` (`notYet`).
- `List` is **not** a datatype in `Term`: `Ty.list` is a primitive former, with literals
  (`list_mk`) and a few externs (`Array.toList`, `Array.mk`, `String.toList`, `String.mk`,
  `String.intercalate`). In JavaScript it is a JavaScript **array** (`JsTy.list`). A Lean
  program cannot match on a list today.
- Records and unions are already objects: `{ _1, _2 }` and `{ tag, _1, … }`. Nullary
  constructors are shared constants (`const $tag0 = { tag: 0 };`, `JsTerm/Hoist.lean`).

## 2. The layout of a datatype

**Proposal: a member of a block of datatypes is laid out as the union (or record, or enum) of
its constructors, exactly as a non-recursive type with the same constructors would be.**

| Lean | JavaScript |
| --- | --- |
| `List.nil` | `$nil`, the shared constant `{ tag: 0 }` |
| `List.cons x xs` | `{ tag: 1, _1: x, _2: xs }` |
| `Tree.leaf` | `{ tag: 0 }` (shared) |
| `Tree.node l v r` | `{ tag: 1, _1: l, _2: v, _3: r }` |
| a datatype of one constructor (`structure`-like, `Rose.node a cs`) | `{ _1: a, _2: cs }` (no tag) |
| a datatype of nullary constructors only | an enum (a number) |

Every object of one constructor is created by the same object literal, with its properties in
the same order, so all of them share one hidden class. Nothing is ever deleted from them.

**Why not `null` for `nil`?** `null` saves one allocation per list (none, in fact: `$nil` is
shared) and one load per step (`cur !== null` instead of `cur.tag === 1`). But it makes the
tag test a special case for the "one nullary and one recursive constructor" types only, and
`cur` becomes polymorphic (object or `null`), which V8 handles well but not better. The
uniform `{ tag: 0 }` keeps one rule for every union, and it is what the example above uses. A
configuration knob (`JsConfig.nullaryAsNull`) can be added later if a benchmark shows a gain.

### 2.1 In `JsTy`

`data` must carry what it unfolds to. The type-safe version (plan §3) indexes `JsTy` by the
block sizes:

```lean
inductive JsTy : List Nat → Type where
  …
  | data {ks : List Nat} (r : Ref ks) : JsTy ks           -- a member of a block
```

and the module carries the unfoldings:

```lean
/-- The layout of every member of every block: the union of its constructors, where a
    recursive field is `data r'` again. -/
structure JsSig (ks : List Nat) where
  unfold : Ref ks → JsTy ks                                -- a `union`, `record` or `enum`
```

A value of type `data r` **is** a value of type `sig.unfold r`: `data_in` and `data_out` are the
identity in JavaScript, so they need no expression former of their own. `FromTerm` casts
through them:

```lean
| fold   {r : Ref ks} (e : JsExpr C M (Σ.unfold r)) : JsExpr C M (.data r)   -- prints `e`
| unfold {r : Ref ks} (e : JsExpr C M (.data r))    : JsExpr C M (Σ.unfold r) -- prints `e`
```

The cheaper intermediate step (plan §3), `data (block member : Nat)` with an untyped table in
the module, is enough to start with; the index `ks` can come after.

### 2.2 `List` becomes a datatype

`List α` becomes the builtin block `List α ≅ nil | cons α (List α)`, handled like a declared
one, so that matching on a list and recursion over it use the same machinery as user
datatypes. `JsTy.list α` stays as a name for it (it is a parameterised member, the element type
being an argument), and its layout is the linked list of §2. This changes:

- `list_mk [a, b, c]`: for a short literal, nested objects
  (`{ tag: 1, _1: a, _2: { tag: 1, _1: b, _2: … $nil } }`); for a long one, the runtime's
  `list([a, b, c, …])`, the builder of the example (one loop, from the end).
- The externs over lists (`Array.toList`, `Array.mk`, `String.toList`/`String.data`,
  `String.mk`/`String.ofList`, `String.intercalate`): their functions in `runtime.js` convert
  with `list` and `ofList` of the example (`array__lean_array_to_list` is `list`,
  `array__lean_array_mk` is `ofList`). The generator needs no change: only the functions of the
  runtime do. `Array.toList` and `Array.mk` stop being the identity (they were, since a list was
  an array).
- The exported functions: a parameter or result of type `List α` is a linked list. The
  JavaScript caller builds one with `list` (exported by `runtime.js`) and reads one with
  `ofList`; the check files of `leanscript --check` do the same.

## 3. Traversals as loops

`Term` expresses recursion over a datatype with `data_rec` (structural recursion: one branch
per member of the block, each receiving the constructor's fields with every recursive field
replaced by the result of the recursive call) and `data_brec` (course-of-values). The naive
translation is a recursive local function:

```js
const go = (xs) => xs.tag === 0 ? z : f(xs._1, go(xs._2));
```

This is always correct, and it is the right translation for **trees**, whose depth is their
height. For **linear** datatypes — a member with exactly one recursive field in each
constructor, such as `List`, `Nat`-like unary types, "snoc lists", streams, the spine of an
expression chain — the depth is the length, and the recursion overflows on long values. These
are the ones to turn into loops. There are three shapes, and all three can be recognised in
`Term` from the way the branch uses the recursive result.

### 3.1 Left folds: the recursive result is the answer (tail recursion)

Lean code written with an accumulator:

```lean
def sumAux : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => sumAux xs (acc + x)
```

`Term` sees a `data_rec` whose motive is a function `Nat → Nat` (the accumulator) and whose
cons branch returns the recursive result applied to a new accumulator: a tail call. It becomes
a `while` loop with the list and the accumulator as mutable variables:

```js
export const sum = (xs) => {
  let acc = 0n;
  let cur = xs;
  while (cur.tag === 1) {
    acc = acc + cur._1;
    cur = cur._2;
  }
  return acc;
};
```

This is `ofList`'s loop. It is the same loop `array_foldl` already produces for arrays, with a
cursor instead of an index.

### 3.2 Right folds: the recursive result is used after (general structural recursion)

```lean
def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
```

The step needs `sum xs` before it can finish, so the elements are combined from the end. The
loop version walks the list once, pushing each cell onto an explicit stack (a JavaScript
array), then folds the stack from its end:

```js
export const sum = (xs) => {
  const stack = [];
  let cur = xs;
  while (cur.tag === 1) {
    stack.push(cur._1);
    cur = cur._2;
  }
  let acc = 0n;                                   // the nil branch
  for (let i = stack.length - 1; i >= 0; i--) acc = stack[i] + acc;
  return acc;
};
```

The stack lives on the heap, so the depth is unbounded; it costs one array push per element,
far cheaper than a call frame. When a branch uses only some fields (here `x`), only those are
pushed. When the combination is associative and has a unit (`+`, `*`, `&&`, `++`),
`Term.optimize` can turn the right fold into a left fold (3.1) instead and skip the stack; that
is a `Term` rewrite, proved correct like the other rewrites of `Term.optimize`, not a JavaScript
one.

### 3.3 Rebuilding a list: tail recursion modulo cons

`map`, `filter`, `append`, `zip`, `take`, `insert` build a new list in the order of the old one:

```lean
def map (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

The recursive result goes straight into the tail field of a new cell. The fast translation
builds the cells front to back, each cell created with a placeholder tail that the next step
fills in — "destination-passing style":

```js
export const map = (f, xs) => {
  const head = { tag: 1, _1: undefined, _2: $nil };   // a dummy cell before the result
  let last = head;
  let cur = xs;
  while (cur.tag === 1) {
    const cell = { tag: 1, _1: f(cur._1), _2: $nil };
    last._2 = cell;
    last = cell;
    cur = cur._2;
  }
  return head._2;
};
```

This is the one place where the generated code writes to an object after creating it. It is
safe because the cell is **fresh**: nothing else can see it until the loop ends, which is the
same ownership argument as the in-place array updates (`JsTerm/InPlace.lean`), only simpler
(the cell is created by the loop itself). Every cell still has its final shape from the start
(`_2` holds `$nil` before it holds the real tail), so the hidden class never changes.

A branch that sometimes does not produce a cell (`filter`) just skips the `last._2 = cell`
step; a branch that ends the list early (`take`) sets `last._2` to its result and breaks out of
the loop.

### 3.4 Everything else

- **Trees and other non-linear types**: a recursive local function, which needs a new block
  former (§4). Its depth is the height of the tree. An explicit-stack version, like 3.2, is
  possible but slower on balanced trees; it can be a configuration knob for degenerate trees.
- **Mutual blocks** (`Even`/`Odd`, an expression type and a statement type): one recursive
  local function per member, defined together.
- **`data_brec`** (course-of-values): the loops above apply when only the immediate recursive
  result is used; otherwise it falls back to recursive functions that return the pair of the
  result and the "below" table, as the Lean compiler does.

### 3.5 Who decides the shape

The user asked that every optimisation be a rewrite of `Term` (`Term.optimize`, proved to
preserve `Term.eval`). The loop shapes fit that rule if `Term` gets them as constructs of its
own, the way `array_foldl` already is a construct of `Term` and not a pattern the JavaScript
backend guesses:

```lean
-- new computations of `Term`, on a linear member of a block
| data_foldl  … : PExpr (data r) → PExpr ρ → Body [ρ, fields…] ρ → Comp ρ          -- 3.1
| data_foldr  … : PExpr (data r) → Body [fields…] ρ → Body [ρ, fields…] ρ → Comp ρ -- 3.2
| data_mapAcc … : … → Comp (data r')                                              -- 3.3
```

- `Term.eval` gives them their meaning (by recursion, as for `data_rec`), and `Term.optimize`
  rewrites a `data_rec` into one of them when the branch has the shape, with a proof that the
  rewrite preserves `eval`, like the existing rewrites.
- `FromTerm` then has one JavaScript shape per construct, with no analysis of its own: it stays
  a syntax-directed translation.
- A `data_rec` that has none of these shapes stays a `data_rec`, and becomes a recursive local
  function.

## 4. What `JsTerm` needs

| Construct | JavaScript | For |
| --- | --- | --- |
| `JsTy.data r`, the module's `JsSig` | — | §2.1 |
| `JsBlock.whileTag` (a loop over a cursor while `cur.tag === k`) | `while (cur.tag === 1) { … }` | 3.1, 3.2, 3.3 |
| `JsExpr.field e i` (read field `i` of a constructor whose tag is known) | `cur._1` | loops, instead of destructuring each step |
| `JsBlock.setTail` (write the tail field of a fresh cell) | `last._2 = cell;` | 3.3 only, on a cell created by the loop |
| `JsBlock.letRec` (local recursive functions, mutually recursive) | `const go = (x) => …;` | 3.4 |
| `JsBlock.forDown` over an array (the explicit stack) | `for (let i = n - 1; i >= 0; i--)` | 3.2 |

`setTail` is the only effectful construct. Its typing restricts it to a cell bound by the
same loop body (a constant of the body created by a constructor literal), so no pass has to
reason about aliasing; it is marked `effectful` like the `_mutable` array operations.

`whileTag` is typed like the other loops: the body reads the cursor as its innermost constant
and ends by assigning the next cursor and the accumulators. The existing machinery (mutable
variables, `retToNext`, the in-place pass) applies unchanged.

## 5. Plan

1. **Layout and matching, no recursion.** `JsTy.data (block member : Nat)` plus a table of
   unfoldings in `JsModule`; `data_in` / `data_out` as casts; matching on a datatype value
   (`data_out` then `union_casesOn`) works. Programs that construct and match values without
   recursing convert.
2. **Recursion as local functions.** `JsBlock.letRec`; `data_rec` / `data_brec` become
   recursive local functions. Every program over datatypes converts (with the stack limit on
   long linear values).
3. **`List` as a datatype.** The builtin block, the linked-list layout, `list` / `ofList` in
   `runtime.js`, the list externs rewritten, the check files updated.
4. **Loops.** `data_foldl`, `data_foldr`, `data_mapAcc` in `Term`, their `eval`, the rewrites
   in `Term.optimize` with their proofs, and their JavaScript shapes (`whileTag`, `setTail`,
   `forDown`).
5. **Type-safe `data`.** Index `JsTy` by `ks` (plan §3).

Each step comes with snapshot programs run against Lean by `scripts/leanscript-snapshots.sh`,
including, from step 4, lists of a million elements (a stack overflow shows up as a failure).

## 6. Open questions

- Should `Nat`-like unary datatypes and `List Unit` be represented as numbers? (A faithful
  layout is the linked list; a number is much faster but changes the layout.)
- Should the explicit stack of 3.2 be reused across calls (a module-level array), or allocated
  per call? Per call is simpler and safe with re-entrancy; reuse saves an allocation.
- Should exported functions accept JavaScript arrays for `List` parameters and convert at the
  boundary (`list(xs)` in a wrapper), to keep the JavaScript API natural? That costs a copy per
  call; the linked list is what the Lean semantics require inside.
