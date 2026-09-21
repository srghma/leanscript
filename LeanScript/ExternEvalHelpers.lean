module

public import Init
public import LeanScript.LeanPrimTy

@[expose] public section

set_option autoImplicit false

/-!
# Running the functions the runtime implements

The evaluator of `LeanScript.Eval` must be able to *run* `lean_nat_add 1 2`, not merely to
stop in front of it, so the meaning of the catalogue of `LeanScript.Externs` is given here:
a Lean function for each entry, on the Lean values the literals of `LeanScript.LeanPrimTyLit`
hold.

Three pieces:

* `LeanPrimTy.denote` — the Lean type a terminal type describes (`.nat` is `Nat`,
  `.float` is `Float`); every terminal type denotes a type with literals, since the
  three run-time *handles* that had none are commented out of `LeanPrimTy`;
* `LeanPrimLit.val` and `LeanPrimLit.ofVal` — the two directions between a literal and
  the value it holds, with `val_ofVal` and `ofVal_val` saying they are inverse;
* `eval`, one per family of the catalogue — the **total** Lean function the entry
  denotes, on the values of its arguments.

## Why `eval` is total, and what that cost

An evaluator that answers `none` is an evaluator that gets stuck, so the four terminal
families are now required to denote a function of their arguments' values, and `eval`
answers with `b.denote` rather than `Option b.denote`.  Three kinds of entry could not
meet that requirement, and all three are commented out of
`LeanScript.LeanInitPureExterns` — not deleted — with the reason attached to each line:

1. **An entry whose type in the catalogue was not the type its name says.**  `byteArray`,
   `floatArray`, `ordering` and `name` are not constructors of `LeanPrimTy`, so
   `autoImplicit` read them as type variables and e.g. `lean_byte_array_size` was "the
   size of a value of *any* terminal type".  Such an entry denotes no function of its
   argument's value.  Marked `(†)`; `set_option autoImplicit false` now keeps them out.
2. **A constant of the host.**  `lean_version_get_major`, `lean_system_platform_windows`,
   `lean_internal_get_hardware_concurrency`, … answer a fact about the machine the
   *compiled program* runs on, and reading it off the machine that runs the *compiler*
   would bake the wrong answer into the semantics.  Marked `(‡)`; the whole
   `LeanInitPureExternLazy` family is empty until the backend has a target description,
   and `LeanInitPureExternLazy.eval` is total for that vacuous reason.
3. **A second name for an entry already in the catalogue.**  `lean_float_to_model` and
   its three companions are the *same* C function as `lean_float_to_bits` and friends,
   and what they answer with is `Float.Model`, not a terminal type.  Marked `(§)`; use
   the `_bits` entries, which do run.

An entry whose meaning is about the *representation* rather than the value
(`lean_ptr_addr`, `lean_is_exclusive_obj`, `lean_dbg_*`) was already outside the terminal
families, in the polymorphic ones, which have no `eval` at all: there is no value form in
`Term` for an array, a list, a task or a thunk, so an entry that answers with one has
nothing to answer *with*.  Giving them a meaning is a change to `Term`, not to these
tables.  (`lean_sharecommon_quick` is the exception that proves the rule: hash-consing is
the identity on values, so `Expr.Step.quick` runs it at every type.)

Everything else — the whole of arithmetic on `Nat`, `Int`, the fixed-width integers and
the floats, the conversions between them, the bit operations, the comparisons, and the
functions on `String`, `Char` and `Substring` — is given its Lean meaning, so a closed
term built out of those externs runs to a literal.
-/

namespace LeanScript

/-! ## Small helpers the tables use -/

/-- The byte position of the first occurrence of a character in a string, and the byte
    size of the string when it does not occur: what `lean_string_posof` answers. -/
def strPosOf (s : String) (c : Char) : Nat :=
  go s.toList 0
where
  /-- Walk the characters, adding up the bytes each of them takes. -/
  go : List Char → Nat → Nat
    | [], acc => acc
    | ch :: rest, acc => if ch == c then acc else go rest (acc + ch.utf8Size)

/-- The bytes of a string from one byte position up to another. -/
def strBytes (s : String) (start stop : Nat) : List UInt8 :=
  ((String.toUTF8 s).extract start stop).toList

end LeanScript
