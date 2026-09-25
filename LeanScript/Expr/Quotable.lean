module
public import LeanScript.Ty.TyWf

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-!
# The types whose values can be written back as a term

An extern called on values has a value that is known where the term is written.  Whether
the call can be **replaced** by that value depends on the result type: the value must be
writable as a term again.  That is `TyWf.quotable`, and it holds for every type that has
**no function inside it**:

* a primitive type, whose value is a literal (`Term.nat_mk`, `Term.string_mk`, …).  The
  literals of `stringPos s`, `stringSlice`, `floatModel` and `float32Model` hold a proof
  about the value (that a position is valid, that a slice's start is before its end, that
  the bits of a float are canonical); those propositions are decidable, so the literal is
  rebuilt with a proof by `decide`;
* an enum, whose value is a constructor number (`Term.enum_mk`);
* an array, a thunk or a lazy value of a quotable type (`Term.array_mk`, `Term.thunk_mk`,
  `Term.lazy_mk` of the values they hold);
* a record, a tagged union (an `Option`, say) or a recursive tagged union (a `List`) whose
  fields are quotable (`Term.record_mk`, `Term.taggedUnion_mk`, `Term.recTaggedUnion_mk`,
  constructor by constructor);
* a recursive record, newtype or mutual family: this model gives them no value at all
  (`LeanScript.Ty.Den`), so there is nothing to write and they count as quotable,
  vacuously.

A **function** is the one thing that is not quotable: its value is a Lean function, and
there is no way to read a term back from one.  So an extern that answers with a function,
or with a value that holds one (an array of functions, a pair whose component is a
function), stays an extern (`Term.extern`) even on values.

`Ty.quotableIn sf` is the same test on a tree written inside a recursive binder, where
`Ty.self` is an occurrence of the binder: it is quotable when the binder is (`sf`).  A
closed type is tested with `sf = false`.

`LeanScript.Term` asks, in `Term.extern`, that the result type is **not** quotable: an
extern on values whose result is quotable is a redex, and the grammar rejects it.  The
translation (`#leanscript_to_term`) computes the value and writes it
(`LeanScript.Quoted`, `LeanScript.Ty.quote`).
-/

namespace LeanScript

mutual

/-- Can every value of this tree be written back as a term?  An occurrence `Ty.self` of
    the binder the tree is written under counts as `sf`.  See the module header. -/
def Ty.quotableIn (sf : Bool) : Ty → Bool
  | .self => sf
  | .familyMember _ => true
  | .shape s => Ty.quotableShape sf s
  | .recTaggedUnion l => Ty.quotableTU true l
  | .recObject _ => true
  | .recAlias _ => true
  | .mutualRecursiveFamily _ => true

/-- `Ty.quotableIn`, on a node: everything but a function. -/
def Ty.quotableShape (sf : Bool) : TyShape Ty → Bool
  | .prim _ => true
  | .fn _ _ => false
  | .primCovariant c => Ty.quotableCov sf c
  | .enum _ => true
  | .record fs => Ty.quotableRecord sf fs
  | .taggedUnion l => Ty.quotableTU sf l

/-- `Ty.quotableIn`, on an array, a thunk or a lazy value. -/
def Ty.quotableCov (sf : Bool) : LeanPrimTyCovariant Ty → Bool
  | .array a => Ty.quotableIn sf a
  | .thunk a => Ty.quotableIn sf a
  | .lazy a => Ty.quotableIn sf a

/-- `Ty.quotableIn`, on every type of a list. -/
def Ty.quotableList (sf : Bool) : List Ty → Bool
  | [] => true
  | t :: ts => Ty.quotableIn sf t && Ty.quotableList sf ts

/-- `Ty.quotableIn`, on a non-empty list of fields. -/
def Ty.quotableNE (sf : Bool) : NonEmptyList Ty → Bool
  | ⟨a, as⟩ => Ty.quotableIn sf a && Ty.quotableList sf as

/-- `Ty.quotableIn`, on the fields of a record. -/
def Ty.quotableRecord (sf : Bool) : LeanRecordSchema Ty → Bool
  | ⟨a, b, rest⟩ => Ty.quotableIn sf a && Ty.quotableIn sf b && Ty.quotableList sf rest

/-- `Ty.quotableIn`, on the fields of every constructor of a list. -/
def Ty.quotableCtors (sf : Bool) : List (List Ty) → Bool
  | [] => true
  | fs :: rest => Ty.quotableList sf fs && Ty.quotableCtors sf rest

/-- `Ty.quotableIn`, on the constructors that follow a field-less one. -/
def Ty.quotableCP (sf : Bool) : CtorsWithPayload Ty → Bool
  | .here fields rest => Ty.quotableNE sf fields && Ty.quotableCtors sf rest
  | .skip rest => Ty.quotableCP sf rest

/-- `Ty.quotableIn`, on the constructors of a tagged union. -/
def Ty.quotableTU (sf : Bool) : LeanTaggedUnionSchema Ty → Bool
  | .payloadFirst fields next rest =>
      Ty.quotableNE sf fields && Ty.quotableList sf next && Ty.quotableCtors sf rest
  | .skip rest => Ty.quotableCP sf rest

end

/-- Can every value of this (closed) tree be written back as a term?  See the module
    header. -/
def Ty.quotable (t : Ty) : Bool := Ty.quotableIn false t

/-- Can every value of this type be written back as a term?  See the module header. -/
def TyWf.quotable (τ : TyWf) : Bool := τ.toTy.quotable

end LeanScript

end
