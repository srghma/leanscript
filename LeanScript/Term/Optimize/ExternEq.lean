module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# Recognising two calls of the same extern

`Extern.beq e₁ e₂` decides, for two entries of the catalogue of the same signature, that they
are the same entry (`Extern.eq_of_beq`).  It is *partial*: it answers `true` only for entries
of the families whose equality `deriving DecidableEq` can decide (the families whose entries
take no type argument: the arithmetic, bitwise, conversion and string families), and `false`
otherwise, which only means "not recognised".  The families whose entries take a type argument
(`lean_array_push αt`) compute their indices through the abstract coercions of the catalogue,
which `deriving DecidableEq` cannot unify (see `LeanInitPureExtern`).

This is what lets the optimiser share two calls of the same extern on the same arguments
(`LeanScript.Term.Optimize.Hoist`).
-/

namespace LeanScript

deriving instance DecidableEq for IntBasicExtern
deriving instance DecidableEq for NatDivExtern
deriving instance DecidableEq for NatBitwiseExtern
deriving instance DecidableEq for UtilExtern
deriving instance DecidableEq for NatLog2Extern
deriving instance DecidableEq for IntDivModExtern
deriving instance DecidableEq for UIntBasicAuxExtern
deriving instance DecidableEq for UInt8BasicExtern
deriving instance DecidableEq for UInt16BasicExtern
deriving instance DecidableEq for UInt32BasicExtern
deriving instance DecidableEq for UInt64BasicExtern
deriving instance DecidableEq for Int8BasicExtern
deriving instance DecidableEq for Int16BasicExtern
deriving instance DecidableEq for Int32BasicExtern
deriving instance DecidableEq for Int64BasicExtern
deriving instance DecidableEq for StringDefsExtern
deriving instance DecidableEq for StringPosRawExtern
deriving instance DecidableEq for StringLengthExtern
deriving instance DecidableEq for FloatExtern
deriving instance DecidableEq for StringPatternExtern
deriving instance DecidableEq for StringSliceExtern
deriving instance DecidableEq for OrdStringExtern
deriving instance DecidableEq for Float32Extern
deriving instance DecidableEq for StringBootstrapExtern

variable {ks : List Nat}

/-- Are the two entries (of the same signature) recognised as the same entry?  `false` means
    "different, or not recognised" (`Extern.eq_of_beq`). -/
def Extern.beq {σs : List (Ty ks)} {τ : Ty ks} (e₁ e₂ : Extern ks σs τ) : Bool :=
  match e₁ with
  | .intBasicExtern a => match e₂ with
    | .intBasicExtern b => decide (a = b)
    | _ => false
  | .natDivExtern a => match e₂ with
    | .natDivExtern b => decide (a = b)
    | _ => false
  | .natBitwiseExtern a => match e₂ with
    | .natBitwiseExtern b => decide (a = b)
    | _ => false
  | .utilExtern a => match e₂ with
    | .utilExtern b => decide (a = b)
    | _ => false
  | .natLog2Extern a => match e₂ with
    | .natLog2Extern b => decide (a = b)
    | _ => false
  | .intDivModExtern a => match e₂ with
    | .intDivModExtern b => decide (a = b)
    | _ => false
  | .uintBasicAuxExtern a => match e₂ with
    | .uintBasicAuxExtern b => decide (a = b)
    | _ => false
  | .uint8BasicExtern a => match e₂ with
    | .uint8BasicExtern b => decide (a = b)
    | _ => false
  | .uint16BasicExtern a => match e₂ with
    | .uint16BasicExtern b => decide (a = b)
    | _ => false
  | .uint32BasicExtern a => match e₂ with
    | .uint32BasicExtern b => decide (a = b)
    | _ => false
  | .uint64BasicExtern a => match e₂ with
    | .uint64BasicExtern b => decide (a = b)
    | _ => false
  | .int8BasicExtern a => match e₂ with
    | .int8BasicExtern b => decide (a = b)
    | _ => false
  | .int16BasicExtern a => match e₂ with
    | .int16BasicExtern b => decide (a = b)
    | _ => false
  | .int32BasicExtern a => match e₂ with
    | .int32BasicExtern b => decide (a = b)
    | _ => false
  | .int64BasicExtern a => match e₂ with
    | .int64BasicExtern b => decide (a = b)
    | _ => false
  | .stringDefsExtern a => match e₂ with
    | .stringDefsExtern b => decide (a = b)
    | _ => false
  | .stringPosRawExtern a => match e₂ with
    | .stringPosRawExtern b => decide (a = b)
    | _ => false
  | .stringLengthExtern a => match e₂ with
    | .stringLengthExtern b => decide (a = b)
    | _ => false
  | .floatExtern a => match e₂ with
    | .floatExtern b => decide (a = b)
    | _ => false
  | .stringPatternExtern a => match e₂ with
    | .stringPatternExtern b => decide (a = b)
    | _ => false
  | .stringSliceExtern a => match e₂ with
    | .stringSliceExtern b => decide (a = b)
    | _ => false
  | .ordStringExtern a => match e₂ with
    | .ordStringExtern b => decide (a = b)
    | _ => false
  | .float32Extern a => match e₂ with
    | .float32Extern b => decide (a = b)
    | _ => false
  | .stringBootstrapExtern a => match e₂ with
    | .stringBootstrapExtern b => decide (a = b)
    | _ => false
  | _ => false

/-- An entry recognised as another one is that entry. -/
theorem Extern.eq_of_beq {σs : List (Ty ks)} {τ : Ty ks} {e₁ e₂ : Extern ks σs τ}
    (h : Extern.beq e₁ e₂ = true) : e₁ = e₂ := by
  revert h
  cases e₁ <;> cases e₂ <;> intro h <;>
    first | exact (Bool.false_ne_true h).elim | (have h' := of_decide_eq_true h; subst h'; rfl)

end LeanScript

end
