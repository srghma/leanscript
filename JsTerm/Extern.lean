module

public import JsTerm.Vars
public import LeanScript.Term.Extern.Name

@[expose] public section

set_option autoImplicit false

/-!
# Externs in JavaScript

A call of an extern of the catalogue (`LeanScript.Neu.extern`) becomes, in `JsTerm`, a call
of the **operation** of that extern at the JavaScript types of its arguments and result
(`JsOp.lookup`, `JsTerm.OpsLookup`): `Nat.div` on `BigInt`s is `bigint_nat__lean_nat_div`, a
function of `runtime.js`; `Nat.land` on `BigInt`s is `bigint_nat__lean_nat_land`, written
inline as `a & b`.  The operations are typed, so a representation is never converted where it
does not need to be (an index held as a `uint53` is passed as it is; one held as a
`bigint_nat` is converted by the operation that takes it).

An extern that has no operation at these types is `JsExpr.unimplemented`: a call of
`lean_extern_unimplemented` that throws when it is evaluated, so the rest of the module still
loads and runs.
-/

namespace MoreJs

open LeanScript

/-- The call of the extern `name` on the arguments `args`, answering a value of type `τ`. -/
def lowerExtern {C M σs : List JsTy} {τ : JsTy} (name : String) (args : JsArgs C M σs) :
    JsExpr C M τ :=
  -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one code
  -- point), how `a = b` on `Char` is translated
  let pushEmpty? : Option (JsExpr C M τ) :=
    if name != "lean_string_push" then none else
    match args with
    | .cons (.lit (.string s)) (.cons (σ := σ) c .nil) =>
      if s.isEmpty then (if h : σ = τ then some (h ▸ c) else none) else none
    | _ => none
  match pushEmpty? with
  | some e => e
  | none =>
    match JsOp.lookup name σs τ with
    | some (.imported op) => .imported op args
    | some (.inlined op) => .inlined op args
    | none => .unimplemented name τ

end MoreJs

end
