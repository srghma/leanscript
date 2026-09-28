module

@[expose] public section

set_option autoImplicit false

/-!
# The operations of `JsTerm`: their indices

The operations are **generated** by `scripts/gen_js_ops.py` from the catalogue of externs
(`LeanScript/LeanInitPureExterns/*.lean`) and `runtime.js`, in the other modules of
`JsTerm/Ops/`; this module has the (hand-written) indices and templates they use:

| module | contents |
| --- | --- |
| `JsTerm.Ops.Basic` | `Effectfulness`, `MayThrow`, `JsInline`, `jsSafeName` |
| `JsTerm.Ops.Imported` | *generated*: `JsOpImported`, `extraArgs`, `toMutable?` |
| `JsTerm.Ops.Inlinable` | *generated*: `JsOpInlinable`, `template` |
| `JsTerm.Ops.Op` | `JsOp` (either of them) and the helpers of the lookup |
| `JsTerm.Ops.Cands.*` | *generated*: the operations of each extern, by group of externs |
| `JsTerm.Ops.Lookup` | *generated*: `JsOp.lookup`, the operation of an extern at given types |

Every extern of the catalogue is split by the JavaScript representation of its arguments and
its result (`lean_nat_div : [nat, nat] → nat` is `bigint_nat__lean_nat_div : [bigint_nat,
bigint_nat] → bigint_nat` and `uint53__lean_nat_div : [uint53, uint53] → uint53`).  An
operation is either

* **imported** (`JsOpImported`): a call of the function of `runtime.js` named as its
  constructor (`JsOpImported.runtimeName`, read off the constructors by `ctor_names%`), which
  the generated module imports; or
* **inlined** (`JsOpInlinable`): written in place of its call as a JavaScript operator,
  conversion or literal over its arguments (`JsOpInlinable.template`).

The name of an operation is its *type prefix* and the name of the extern, joined by `__`: the
representations of the configurable Lean types of the signature (`Nat`, `Int`, `UInt64`,
`Int64`, `BitVec n` for `n > 53`) in order of first appearance and without repetitions, or,
when there is none, the first leaf of the signature (`uint32__lean_uint32_add`), or the family
of a polymorphic operation (`array__lean_array_push_immutable`, `thunk__lean_mk_thunk`).  A
polymorphic array operation works on every layout of an array (`JsArrayLayout`: a generic
array or a typed array).

Both families are indexed by what an operation may do besides answering (`Effectfulness`,
`MayThrow`), by the types of its arguments and by the type of its result:

* an operation is **effectful** when it changes something outside of it: the `_mutable` array
  updates, which update their array argument in place (the backend calls them only on an array
  nothing else refers to), are the only ones; every other operation is **pure**;
* an operation **may throw** when its function in `runtime.js` may (a `throw`, directly or in a
  function it calls): the operations on a `number` representation of an unbounded type, which
  throw a `RangeError` when the result does not fit in a safe integer (so that no result is
  ever silently wrong).  The inlined operations never throw.

The array updates come in two versions: `…_immutable` (the extern: a copy of the array) and
`…_mutable` (the same update in place); `JsOpImported.toMutable?` pairs them.  An extern whose
function in `runtime.js` is an alias of another at the same signature (`lean_array_fset` of
`lean_array_set`) has that operation.
-/

namespace MoreJs

/-- Whether an operation changes something outside of it. -/
inductive Effectfulness where
  /-- It only computes its result. -/
  | pure
  /-- It changes something outside of it (it updates an argument in place). -/
  | effectful
  deriving DecidableEq, Repr, Inhabited

/-- Whether an operation may throw. -/
inductive MayThrow where
  /-- It never throws. -/
  | doesntThrow
  /-- It may throw (a `RangeError` when a result does not fit in its representation). -/
  | mayThrow
  deriving DecidableEq, Repr, Inhabited

/-- How an inlined operation is written in JavaScript, over its arguments. -/
inductive JsInline where
  /-- The argument of position `i` (from `0`). -/
  | arg (i : Nat)
  /-- `a op b`, for the JavaScript binary operator `op` (`+`, `&`, `===`, …). -/
  | bin (op : String) (a b : JsInline)
  /-- `op a`, for the JavaScript prefix operator `op` (`-`, `~`, `!`). -/
  | un (op : String) (a : JsInline)
  /-- `f(args)`, `f` a global function (`BigInt`, `Number`, `Math.sin`, `Uint8Array.from`). -/
  | call (f : String) (args : List JsInline)
  /-- `new C(args)`. -/
  | new (ctor : String) (args : List JsInline)
  /-- An integer `number` literal. -/
  | num (n : Int)
  /-- A `BigInt` literal. -/
  | big (n : Int)
  /-- `[]`. -/
  | emptyArray
  /-- `a.field` (`a.length`). -/
  | member (a : JsInline) (field : String)
  deriving Inhabited, Repr

/-- The name of a function of `runtime.js` for the name of an operation: the characters a
    JavaScript identifier cannot have are written `$` and their code in hexadecimal (`get?` is
    `get$3F`, `get!` is `get$21`, `next'` is `next$27`). -/
def jsSafeName (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '?' => acc ++ "$3F"
    | '!' => acc ++ "$21"
    | '\'' => acc ++ "$27"
    | c => acc.push c) ""

end MoreJs

end
