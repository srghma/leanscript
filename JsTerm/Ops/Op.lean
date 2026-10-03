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

/-- A candidate: an operation at some signature.

    The candidates of one extern are its operations for every choice of representation of the
    configurable Lean types of its signature (`Nat`, `Int`, `UInt64`, `Int64`, the wide
    `BitVec`s: a `BigInt` or a `number`): `lean_nat_div` has `bigint_nat__lean_nat_div` at
    `[bigint_nat, bigint_nat] → bigint_nat` and `uint53__lean_nat_div` at
    `[uint53, uint53] → uint53`.  An operation's type `JsOp e t σs τ` is indexed by its
    signature and its effects, so operations of different signatures have different types:
    to keep them in one list, each is packed with its indices (a dependent pair).  They are
    not duplicates: no two candidates of an extern have the same signature
    (`OpsSpec.LookupUnique`), so a call, whose types are fixed by the configuration, has at most
    one candidate, which `firstOf` finds by comparing signatures. -/
abbrev Cand : Type := Σ (σs : List JsTy) (τ : JsTy) (e : Effectfulness) (t : MayThrow), JsOp e t σs τ

/-- The signature of a candidate: its argument types and its result type. -/
def Cand.sig (c : Cand) : List JsTy × JsTy := (c.1, c.2.1)

/-- The candidate that has the signature `σs → τ` (the first one, but there is at most one:
    `OpsSpec.LookupUnique`). -/
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

/-- The first array among the types. -/
def firstLayoutOf? : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => some ⟨t, e, l⟩
    | none => firstLayoutOf? ts

/-- The first array among `ts` whose element type is also among `all`. -/
def elemLayoutOf? (all : List JsTy) : List JsTy → Option (Σ a e, JsArrayLayout a e)
  | [] => none
  | t :: ts => match JsArrayLayout.of? t with
    | some ⟨e, l⟩ => if all.contains e then some ⟨t, e, l⟩ else elemLayoutOf? all ts
    | none => elemLayoutOf? all ts

/-- The layout of the array among the argument types: the first array whose element type is
    also among the types (the array of `lean_array_get : [E, A, Nat] → E` when `E` is itself an
    array type, not the default `E`), else the first array. -/
def layoutOf? (ts : List JsTy) : Option (Σ a e, JsArrayLayout a e) :=
  match elemLayoutOf? ts ts with
  | some r => some r
  | none => firstLayoutOf? ts

end JsOp

end MoreJs

end
