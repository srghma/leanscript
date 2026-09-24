module
public import LeanScript.Ty.TyWf

@[expose] public section

set_option autoImplicit false

/-!
# The types whose values can be written back as a term

An extern called on values has a value that is known where the term is written.  Whether
the call can be **replaced** by that value depends on the result type: the value must be
writable as a term again.  That is `TyWf.quotable`:

* a primitive type, whose value is a literal (`Term.nat_mk`, `Term.string_mk`, …) — but
  not `stringPos s`, `stringSlice`, `floatModel` and `float32Model`, whose literals hold a
  proof about the value that cannot be rebuilt from a computed value;
* an enum, whose value is a constructor number (`Term.enum_mk`);
* an array of a quotable type (`Term.array_mk` of the elements);
* a thunk or a lazy value of a quotable type (`Term.thunk_mk`, `Term.lazy_mk` of the
  value it stands for).

A function, a record, a tagged union and the recursive shapes are not quotable, so an
extern that answers with one stays an extern (`Term.extern`) even on values.

`LeanScript.Term` asks, in `Term.extern`, that the result type is **not** quotable: an
extern on values whose result is quotable is a redex, and the grammar rejects it.  The
translation (`#leanscript_to_term`) computes the value and writes it
(`LeanScript.Quoted`, `LeanScript.Ty.quote`).
-/

namespace LeanScript

/-- Does every value of this primitive type have a literal that can be written from the
    value alone? -/
def LeanPrimTy.quotable : LeanPrimTy → Bool
  | .stringPos _ | .stringSlice | .floatModel | .float32Model => false
  | _ => true

mutual

/-- Can every value of this type be written back as a term?  See the module header. -/
def Ty.quotable : Ty → Bool
  | .shape s => Ty.quotableShape s
  | _ => false

/-- `Ty.quotable`, on a node. -/
def Ty.quotableShape : TyShape Ty → Bool
  | .prim p => p.quotable
  | .enum _ => true
  | .primCovariant c => Ty.quotableCov c
  | _ => false

/-- `Ty.quotable`, on an array, a thunk or a lazy value. -/
def Ty.quotableCov : LeanPrimTyCovariant Ty → Bool
  | .array a => Ty.quotable a
  | .thunk a => Ty.quotable a
  | .lazy a => Ty.quotable a

end

/-- Can every value of this type be written back as a term?  See the module header. -/
def TyWf.quotable (τ : TyWf) : Bool := τ.toTy.quotable

end LeanScript

end
