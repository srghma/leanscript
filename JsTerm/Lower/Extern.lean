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

variable {S : JsSig}

open LeanScript

/-- The layout the operations of the catalogue use for a type (`runtime.js` is written for
    it): cons cells at the array layout (`consList α` is `list α`), a union whose constructors
    without fields are numbers with every constructor an object (`JsRepr.cells`); any other
    type itself.  Only the outermost type changes, which is all the operations see. -/
def JsTy.arrayList : JsTy → JsTy
  | .obj .consList [α] => .list α
  | .obj (.union ar .smallIntNullary) args => .obj (.union ar .cells) args
  | t => t

/-- Is the type one whose layout the operations do not use (`JsTy.arrayList` changes it)? -/
def JsTy.isConsList : JsTy → Bool
  | .obj .consList [_] => true
  | .obj (.union _ .smallIntNullary) _ => true
  | _ => false

/-- A value at the layout of the operations (`JsTy.arrayList`): cons cells converted to an
    array, the constructors without fields of a union to objects, any other value itself. -/
def JsExpr.asArrayList {C M : List JsTy} : {σ : JsTy} → JsExpr S C M σ → JsExpr S C M σ.arrayList
  | .obj .consList [_], e => e.toArrayList
  | .obj (.union ar .smallIntNullary) args, e => .listOp (.nullaryToCells ar args) (.cons e .nil)
  | .obj .consList [], e | .obj .consList (_ :: _ :: _), e | .obj (.record _) _, e
  | .obj (.union _ .cells) _, e | .obj (.decl _) _, e => e
  | .terminal _, e | .array _, e | .typedArray _, e | .list _, e | .strMap _, e | .fn _ _, e
  | .enum _ _, e | .thunk _, e => e

/-- A value given at the layout of the operations (`JsTy.arrayList`), at its type: an array
    converted to cons cells, the constructors without fields of a union to numbers, any other
    value itself. -/
def JsExpr.ofArrayListAt {C M : List JsTy} : (σ : JsTy) → JsExpr S C M σ.arrayList → JsExpr S C M σ
  | .obj .consList [_], e => e.ofArrayList
  | .obj (.union ar .smallIntNullary) args, e => .listOp (.nullaryToInt ar args) (.cons e .nil)
  | .obj .consList [], e | .obj .consList (_ :: _ :: _), e | .obj (.record _) _, e
  | .obj (.union _ .cells) _, e | .obj (.decl _) _, e => e
  | .terminal _, e | .array _, e | .typedArray _, e | .list _, e | .strMap _, e | .fn _ _, e
  | .enum _ _, e | .thunk _, e => e

/-- Arguments at the layouts of the operations. -/
def JsArgs.asArrayLists {C M : List JsTy} : {σs : List JsTy} → JsArgs S C M σs →
    JsArgs S C M (σs.map JsTy.arrayList)
  | [], .nil => .nil
  | _ :: _, .cons a as => .cons a.asArrayList as.asArrayLists

/-- The type of the values of the first hash map with string keys among the types. -/
def strMapValue? : List JsTy → Option JsTy
  | [] => none
  | .strMap v :: _ => some v
  | _ :: ts => strMapValue? ts

/-- The operation `op` on a hash map with string keys (`JsStrMapOp`) at the arguments `args`,
    answering a value of type `τ`, when the types are its signature (`JsStrMapOp.sig`). -/
def strMapCall? {C M σs : List JsTy} {τ : JsTy} (op : JsStrMapOp) (args : JsArgs S C M σs) :
    Option (JsExpr S C M τ) :=
  match strMapValue? (σs ++ [τ]) with
  | none => none
  | some v =>
    -- the representation of a natural number: the answer of `size`, the capacity of
    -- `emptyWithCapacity`
    let N : JsTy := match op with
      | .size => τ
      | .emptyWithCapacity => σs.headD (.terminal .uint53)
      | _ => .terminal .uint53
    if h₁ : σs = (op.sig v N).1 then
      if h₂ : (op.sig v N).2 = τ then
        some (h₂ ▸ JsExpr.listOp (S := S) (C := C) (M := M) (.strMap op v N) (h₁ ▸ args))
      else none
    else none

/-- The call of the extern `name` of `StrMapExtern` (`LeanScript.LeanInitPureExterns.StrMap`) on
    the arguments `args`: its operation (`JsStrMapOp`), with the conversions of a list of cons
    cells or of a union whose constructors without fields are numbers around it, as for the
    operations of the other externs. -/
def lowerStrMap {C M σs : List JsTy} {τ : JsTy} (op : JsStrMapOp) (name : String)
    (args : JsArgs S C M σs) : Except String (JsExpr S C M τ) :=
  match strMapCall? op args with
  | some e => pure e
  | none =>
    let err := s!"the extern {name} has no operation at the types {σs} → {τ}"
    if !(σs.any JsTy.isConsList || τ.isConsList) then throw err else
    match strMapCall? (τ := τ.arrayList) op args.asArrayLists with
    | some e => pure (JsExpr.ofArrayListAt τ e)
    | none => throw err

/-- The call of the extern `name` on the arguments `args`, answering a value of type `τ`; an
    error if the extern has no operation at these types. -/
def lowerExtern {C M σs : List JsTy} {τ : JsTy} (name : String) (args : JsArgs S C M σs) :
    Except String (JsExpr S C M τ) :=
  -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one code
  -- point), how `a = b` on `Char` is translated
  let pushEmpty? : Option (JsExpr S C M τ) :=
    if name != "lean_string_push" then none else
    match args with
    | .cons (.lit (.string s)) (.cons (σ := σ) c .nil) =>
      if s.isEmpty then (if h : σ = τ then some (h ▸ c) else none) else none
    | _ => none
  match pushEmpty? with
  | some e => pure e
  | none =>
    if let some op := JsStrMapOp.ofExtern? name then lowerStrMap op name args else
    match JsOp.lookup name σs τ with
    | some ⟨_, _, .imported op⟩ => pure (.imported op args)
    | some ⟨_, _, .inlined op⟩ => pure (.inlined op args)
    | none =>
      let err := s!"the extern {name} has no operation at the types {σs} → {τ}"
      if !(σs.any JsTy.isConsList || τ.isConsList) then throw err else
      -- lists of cons cells, unions with numbers: the operation at the layout of the
      -- catalogue, with conversions around it
      let as := args.asArrayLists
      match JsOp.lookup name (σs.map JsTy.arrayList) τ.arrayList with
      | some ⟨_, _, .imported op⟩ => pure (JsExpr.ofArrayListAt τ (.imported op as))
      | some ⟨_, _, .inlined op⟩ => pure (JsExpr.ofArrayListAt τ (.inlined op as))
      | none => throw err

end MoreJs

end
