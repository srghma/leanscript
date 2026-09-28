module

public import JsTerm.Ops.Imported
public import JsTerm.Ops.Inlinable

@[expose] public section

set_option autoImplicit false

/-!
# The operations, imported or inlined

`JsOp` is an operation of either family (`JsOpImported`, `JsOpInlinable`).  The rest are the
helpers of the (generated) lookup of the operation of an extern (`JsOp.lookup`,
`JsTerm.Ops.Lookup`): a *candidate* is an operation at its signature, and the lookup picks the
first candidate of the extern whose signature is exactly the one asked for (`firstOf`),
instantiating the polymorphic ones from the types (`elemOf?`, `layoutOf?`).
-/

namespace MoreJs

/-- An operation: one that calls the runtime, or one written inline. -/
inductive JsOp : Effectfulness → MayThrow → List JsTy → JsTy → Type where
  | imported {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
      (op : JsOpImported e t σs τ) : JsOp e t σs τ
  | inlined {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
      (op : JsOpInlinable e t σs τ) : JsOp e t σs τ

/-- An operation of some effects. -/
abbrev JsSomeOp (σs : List JsTy) (τ : JsTy) : Type := Σ e t, JsOp e t σs τ

namespace JsOp

/-- The name of the operation. -/
def name {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy} : JsOp e t σs τ → String
  | .imported op => op.name
  | .inlined op => op.name

/-- A candidate: an operation at some signature. -/
abbrev Cand : Type := Σ (σs : List JsTy) (τ : JsTy) (e : Effectfulness) (t : MayThrow), JsOp e t σs τ

/-- The first candidate that has the signature `σs → τ`. -/
def firstOf (σs : List JsTy) (τ : JsTy) : List Cand → Option (JsSomeOp σs τ)
  | [] => none
  | ⟨σs', τ', e, t, op⟩ :: rest =>
    if h : σs' = σs ∧ τ' = τ then some ⟨e, t, h.1 ▸ h.2 ▸ op⟩ else firstOf σs τ rest

/-- The type a thunk operation delays (the first delay among the types). -/
def elemOf? : List JsTy → JsTy
  | [] => .terminal .bool
  | .thunk t :: _ => t
  | .fn [] t :: _ => t
  | _ :: ts => elemOf? ts

/-- The layout of the array among the argument types (the first one that is an array). -/
def layoutOf? : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => layoutOf? ts

end JsOp

end MoreJs

end
