module

public import LeanScript.Ty.Class

@[expose] public section

/-!
# The type-level helpers of `#leanscript_ctor`

`TyWf.AsType`, a Lean type standing for a bundled tree, and `TyWf.oneOf`, the tagged union
`#leanscript_to_term` builds where values of different types meet.
-/

namespace LeanScript

/-- A Lean type that stands for the bundle `t`: its values are irrelevant (it is `PUnit`), and
    its `LeanScriptTyWf` instance is `t`.  So `tyWfOf (F t.AsType)` is the tree `F`'s own
    instance gives `F α` when `α` is modelled by `t`.  This is how `#leanscript_ctor` writes
    the tree of a field of type `F S`, for a type argument `S`, when the tree of `F`'s instance
    is one the bundled smart constructors cannot rebuild — a recursive one, such as
    `List S`'s: it is `tyWfOf (List S.AsType)`. -/
def TyWf.AsType.{u} (_t : TyWf) : Type u := PUnit

instance TyWf.instLeanScriptTyWfAsType.{u} (t : TyWf) : LeanScriptTyWf (TyWf.AsType.{u} t) := ⟨t⟩

/-- **One of** the types `a`, `b`, `cs…`: the tagged union with one constructor per type,
    whose one field is a value of that type.

    `#leanscript_to_term` builds it where values of *different* types meet — the branches of
    an `if` that build a datatype with existentials with different choices of the hidden
    types — and injects each value with the constructor of its own type. -/
@[reducible] def TyWf.oneOf (a b : TyWf) (cs : List TyWf) : TyWf :=
  TyWf.taggedUnion (.payloadFirst ⟨a, []⟩ [b] (cs.map fun c => [c]))

end LeanScript

end
