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

The operations of the catalogue that take or answer a `List` are written for the array layout
of lists (`JsTy.list`).  Under `ListRepr.taggedUnion` a list is cons cells (`JsTy.consList`):
such a call converts its list arguments to arrays (`consList__to_array`) and its list result
back to cons cells (`consList__of_array`) around the operation at the array layout — only the
outermost list of each argument and of the result, which is all the operations see
(`String.intercalate` on `List String`, `Array.mk`, `Array.toList`, …; the elements of a
polymorphic one are passed through as they are).
-/

namespace MoreJs

open LeanScript

/-- The array layout of a type of cons cells (`consList α` is `list α`); any other type
    itself. -/
def JsTy.arrayList : JsTy → JsTy
  | .consList α => .list α
  | t => t

/-- Is the type a list of cons cells? -/
def JsTy.isConsList : JsTy → Bool
  | .consList _ => true
  | _ => false

/-- A value at the array layout of its type (`JsTy.arrayList`): cons cells converted to an
    array, any other value itself. -/
def JsExpr.asArrayList {C M : List JsTy} : {σ : JsTy} → JsExpr C M σ → JsExpr C M σ.arrayList
  | .consList _, e => e.toArrayList
  | .terminal _, e | .array _, e | .typedArray _, e | .list _, e | .fn _ _, e
  | .record _ _ _, e | .union _ _ _, e | .enum _ _, e | .data _, e | .thunk _, e => e

/-- A value given at the array layout of its type (`JsTy.arrayList`), at its type: an array
    converted to cons cells, any other value itself. -/
def JsExpr.ofArrayListAt {C M : List JsTy} : (σ : JsTy) → JsExpr C M σ.arrayList → JsExpr C M σ
  | .consList _, e => e.ofArrayList
  | .terminal _, e | .array _, e | .typedArray _, e | .list _, e | .fn _ _, e
  | .record _ _ _, e | .union _ _ _, e | .enum _ _, e | .data _, e | .thunk _, e => e

/-- Arguments at the array layouts of their types. -/
def JsArgs.asArrayLists {C M : List JsTy} : {σs : List JsTy} → JsArgs C M σs →
    JsArgs C M (σs.map JsTy.arrayList)
  | [], .nil => .nil
  | _ :: _, .cons a as => .cons a.asArrayList as.asArrayLists

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
    | none =>
      let err := s!"the extern {name} has no operation at the types {σs} → {τ}"
      if !(σs.any JsTy.isConsList || τ.isConsList) then throw err else
      -- lists of cons cells: the operation at the array layout, with conversions around it
      let as := args.asArrayLists
      match JsOp.lookup name (σs.map JsTy.arrayList) τ.arrayList with
      | some ⟨_, _, .imported op⟩ => pure (JsExpr.ofArrayListAt τ (.imported op as))
      | some ⟨_, _, .inlined op⟩ => pure (JsExpr.ofArrayListAt τ (.inlined op as))
      | none => throw err

end MoreJs

end
