module

public import JsTerm.Syntax.Vars
public import JsTerm.Ops.Lookup
public import LeanScript.Term.Extern.Name

@[expose] public section

set_option autoImplicit false

/-!
# Externs in JavaScript

A call of an extern of the catalogue (`LeanScript.Neu.extern`) becomes, in `JsTerm`, a call
of the **operation** of that extern at the JavaScript types of its arguments and result
(`JsOp.lookup`, `JsTerm.Ops.Lookup`): `Nat.div` on `BigInt`s is `bigint_nat__lean_nat_div`, a
function of `runtime.js`; `Nat.land` on `BigInt`s is `bigint_nat__lean_nat_land`, written
inline as `a & b`.  The operations are typed, so a representation is never converted where it
does not need to be (an index held as a `uint53` is passed as it is; one held as a
`bigint_nat` is converted by the operation that takes it).

Every extern of the catalogue has an operation at every representation (`scripts/gen_js_ops.py`
refuses to generate the operations otherwise), so an extern with no operation at the types of a
call is an error of the conversion (a type the catalogue does not foresee), never a call that
fails when it runs.

A `String.Pos s` is a byte offset into the string `s`, a parameter of the extern known when the
program is converted: the operations of the externs on such positions take `s` as their first
argument (`FromTerm` passes it, as a literal).
-/

namespace MoreJs

open LeanScript

/-- The call of the extern `name` on the arguments `args`, answering a value of type `τ`; an
    error if the extern has no operation at these types. -/
def lowerExtern {C M σs : List JsTy} {τ : JsTy} (name : String) (args : JsArgs C M σs) :
    Except String (JsExpr C M τ) :=
  -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one code
  -- point), how `a = b` on `Char` is translated
  let pushEmpty? : Option (JsExpr C M τ) :=
    if name != "lean_string_push" then none else
    match args with
    | .cons (.lit (.string s)) (.cons (σ := σ) c .nil) =>
      if s.isEmpty then (if h : σ = τ then some (h ▸ c) else none) else none
    | _ => none
  match pushEmpty? with
  | some e => pure e
  | none =>
    match JsOp.lookup name σs τ with
    | some ⟨_, _, .imported op⟩ => pure (.imported op args)
    | some ⟨_, _, .inlined op⟩ => pure (.inlined op args)
    | none => throw s!"the extern {name} has no operation at the types {σs} → {τ}"

end MoreJs

end
