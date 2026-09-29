module

public import JsTerm.Ops.Cands.Nat
public import JsTerm.Ops.Cands.UInt
public import JsTerm.Ops.Cands.SInt
public import JsTerm.Ops.Cands.Float
public import JsTerm.Ops.Cands.String
public import JsTerm.Ops.Cands.Misc
public import JsTerm.Ops.Cands.ArrayStd

@[expose] public section

set_option autoImplicit false

/-!
# Finding the operation of an extern call

**Generated** by `scripts/gen_js_ops.py`; do not edit.

`JsOp.lookup name σs τ` is the operation of the extern `name` (as the catalogue spells it,
`lean_nat_div`) at the argument types `σs` and the result type `τ`, if there is one: the
constructor of `JsOpImported` or `JsOpInlinable` whose signature is exactly `σs → τ` (a
polymorphic one instantiated from the types), with its effects.  The candidates of the externs
are in `JsTerm/Ops/Cands/`, by group of externs.
-/

namespace MoreJs

namespace JsOp

/-- The candidates of the extern `name` (none if it is not an extern of the catalogue): its
    operations, one per representation of its configurable types, at most one of them at
    any signature (`OpsSpec.LookupUnique`). -/
def cands (name : String) (σs : List JsTy) (τ : JsTy) : List Cand :=
  (candsNat? name <|>
    candsUInt? name <|>
    candsSInt? name <|>
    candsFloat? name <|>
    candsString? name <|>
    candsMisc? name σs τ <|>
    candsArrayStd? name σs τ).getD []

/-- The operation of the extern `name` at the signature `σs → τ`, if there is one: the
    candidate at this signature (there is at most one, `OpsSpec.LookupUnique`). -/
def lookup (name : String) (σs : List JsTy) (τ : JsTy) : Option (JsSomeOp σs τ) :=
  firstOf σs τ (cands name σs τ)

end JsOp

end MoreJs

end
