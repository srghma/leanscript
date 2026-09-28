module

public import JsTerm.Passes.InPlace.Collect

@[expose] public section

set_option autoImplicit false

/-!
# Updating arrays in place

The runtime functions of the array externs (`array__lean_array_push_immutable`,
`uint53__lean_array_set_immutable`, `bigint_nat__lean_array_swap_immutable`,
`array__lean_array_pop_immutable`, …) never mutate their argument: they answer with a copy,
since the argument may be referred to elsewhere.  When nothing else refers to it, and nothing
reads it afterwards, the copy is wasted work (a loop pushing `n` elements copies `O(n²)` of
them), and the backend calls the mutable operation instead (`array__lean_array_push_mutable`,
`uint53__lean_array_set_mutable`, …: an `effectful` constructor of the same signature,
`JsOpImported.toMutable?`), which mutates the array and answers with it.  (`push` and `pop`
have a mutable version on generic arrays only: a typed array cannot grow or shrink.)

The pass (`inPlace`) works on the body of one function.  It tells the variables apart by
numbering their binders in the order it meets them, and computes the variables that **own**
their value:

* a variable is **linear** (`linearFrom`) when, on every path from its definition (or from
  any assignment to it), it is read at most once before it is assigned again, never in a
  closure, and never in a loop that does not assign it first;
* a variable **owns** its value when it is linear and every value it is given is *fresh*
  (`freshValue`): a value of a type without arrays (`JsTy.shareFree`: numbers, strings,
  booleans, enums, and records and unions of those), an array just built (a literal, an
  operation answering with a new array: `…__lean_array_push`, `…__lean_mk_array`, `[]`,
  `Uint8Array.from(a)`, …), an owned variable (read for the last time), an update
  (`…__lean_array_set`, `…__lean_array_swap`) of an owned variable, an inlined operation
  answering with its argument (`Array.mk` on generic arrays) of a fresh value, a field of a
  record or union that an owned variable holds, or a record or union all of whose fields are
  fresh.  Nothing else refers to an array an owning variable holds (directly, or through the
  fields of the records and unions it holds).

The variables are the constants (`const`, the fields of a pattern, the value of a join point,
defined by every jump to it) and the mutable variables (`let`, and every assignment); the
parameters of the function, of its closures and the elements of the loops are never owned.
The owners are the greatest set closed under these rules (a variable is dropped until nothing
changes).  Then every copying update on an owning variable `v` becomes the in-place update:
the call is the last read of `v`, and nothing else refers to the array.

Records and unions are never mutated.  The pass runs before the constants of the module are
shared (`MoreJs.hoistConsts`), which never shares an array.

The analysis is in `JsTerm/Passes/InPlace/`: `Linear.lean` (the array operations, and linear
variables) and `Collect.lean` (the definitions of the variables, and the rebuilt body).
-/

namespace MoreJs

/-! ## The owners, and the rewrite -/

/-- The greatest set of variables all of whose definitions satisfy their predicate (given the
    set). -/
partial def greatestFix (defs : Array (Nat × DefOf)) (start : List Nat) : List Nat :=
  let next := start.filter fun x => defs.all fun (y, d) => y != x || d start
  if next.length == start.length then start else greatestFix defs next

/-- Update in place the arrays nothing else refers to, in the body of a function. -/
def inPlace {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  let (build, st) := (collectB {} b).run {}
  let cands := st.linear.toList.eraseDups.filter fun x => st.defs.any (·.1 == x)
  let own := greatestFix st.defs cands
  if own.isEmpty then b else build own

end MoreJs

end
