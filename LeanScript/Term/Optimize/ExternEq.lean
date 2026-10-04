module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# Recognising two calls of the same extern

`Extern.beq e₁ e₂` decides, for two entries of the catalogue of the same signature, that they
are the same entry (`Extern.eq_of_beq`).  It is *partial*: it answers `true` only for entries
of the families whose equality `deriving DecidableEq` can decide (the families whose entries
take no type argument: the arithmetic, bitwise, conversion and string families) and for the
entries of `PreludeExtern` that take no type argument (`lean_nat_add`, `lean_nat_dec_le`, …,
compared by their constructor index, `Extern.preludeOfIdx`), and `false` otherwise, which only
means "not recognised".  The families whose entries take a type argument
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

/-- The entries of `PreludeExtern` that take no type argument, by their constructor index
    (`deriving DecidableEq` cannot compare the entries of this family: some of them take one). -/
def Extern.preludeOfIdx (ks : List Nat) :
    Nat → Option ((σs : List (Ty ks)) × (τ : Ty ks) × Extern ks σs τ)
  | 0 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat_mk⟩
  | 1 => some ⟨_, _, .preludeExtern .lean_uint32_dec_eq⟩
  | 2 => some ⟨_, _, .preludeExtern .lean_uint32_dec_lt⟩
  | 3 => some ⟨_, _, .preludeExtern .lean_nat_div⟩
  | 4 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat__UInt32_ofNatLT⟩
  | 5 => some ⟨_, _, .preludeExtern .lean_uint32_of_nat__Char_ofNatAux⟩
  | 7 => some ⟨_, _, .preludeExtern .lean_uint8_to_nat__UInt8_toBitVec⟩
  | 8 => some ⟨_, _, .preludeExtern .lean_nat_dec_lt⟩
  | 9 => some ⟨_, _, .preludeExtern .lean_nat_mod__Nat_modCore⟩
  | 10 => some ⟨_, _, .preludeExtern .lean_nat_mod__Nat_mod⟩
  | 12 => some ⟨_, _, .preludeExtern .lean_nat_sub⟩
  | 13 => some ⟨_, _, .preludeExtern .lean_uint8_dec_lt⟩
  | 14 => some ⟨_, _, .preludeExtern .lean_uint32_dec_le⟩
  | 17 => some ⟨_, _, .preludeExtern .lean_nat_dec_eq__Nat_decEq⟩
  | 18 => some ⟨_, _, .preludeExtern .lean_nat_dec_eq__Nat_beq⟩
  | 21 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat__UInt8_ofNat⟩
  | 22 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat__UInt8_ofNatLT⟩
  | 23 => some ⟨_, _, .preludeExtern .lean_uint8_dec_le⟩
  | 24 => some ⟨_, _, .preludeExtern .lean_nat_dec_le__Nat_ble⟩
  | 25 => some ⟨_, _, .preludeExtern .lean_nat_dec_le__Nat_decLe⟩
  | 27 => some ⟨_, _, .preludeExtern .lean_nat_add⟩
  | 29 => some ⟨_, _, .preludeExtern .lean_uint16_to_nat__UInt16_toBitVec⟩
  | 30 => some ⟨_, _, .preludeExtern .lean_uint16_of_nat_mk⟩
  | 31 => some ⟨_, _, .preludeExtern .lean_uint16_dec_eq⟩
  | 32 => some ⟨_, _, .preludeExtern .lean_string_dec_eq⟩
  | 33 => some ⟨_, _, .preludeExtern .lean_nat_pred⟩
  | 34 => some ⟨_, _, .preludeExtern .lean_string_mk__String_ofList⟩
  | 35 => some ⟨_, _, .preludeExtern .lean_string_hash⟩
  | 36 => some ⟨_, _, .preludeExtern .lean_uint64_to_nat__UInt64_toBitVec⟩
  | 37 => some ⟨_, _, .preludeExtern .lean_uint64_of_nat_mk⟩
  | 38 => some ⟨_, _, .preludeExtern .lean_uint32_to_nat__UInt32_toNat⟩
  | 39 => some ⟨_, _, .preludeExtern .lean_uint32_to_nat__UInt32_toBitVec⟩
  | 40 => some ⟨_, _, .preludeExtern .lean_uint64_dec_eq⟩
  | 41 => some ⟨_, _, .preludeExtern .lean_uint16_of_nat__UInt16_ofNatLT⟩
  | 42 => some ⟨_, _, .preludeExtern .lean_name_eq⟩
  | 43 => some ⟨_, _, .preludeExtern .lean_uint8_of_nat_mk⟩
  | 44 => some ⟨_, _, .preludeExtern .lean_uint8_dec_eq⟩
  | 45 => some ⟨_, _, .preludeExtern .lean_nat_pow⟩
  | 46 => some ⟨_, _, .preludeExtern .lean_nat_mul⟩
  | 47 => some ⟨_, _, .preludeExtern .lean_string_utf8_byte_size⟩
  | 49 => some ⟨_, _, .preludeExtern .lean_uint64_mix_hash⟩
  | 50 => some ⟨_, _, .preludeExtern .lean_uint64_of_nat__UInt64_ofNatLT⟩
  | _ => none

/-- The constructor index of an entry of `PreludeExtern`. -/
def Extern.preludeIdx? {σs : List (Ty ks)} {τ : Ty ks} : Extern ks σs τ → Option Nat
  | .preludeExtern e => some e.ctorIdx
  | _ => none

theorem Extern.preludeOfIdx_eq {σs : List (Ty ks)} {τ : Ty ks} (e : Extern ks σs τ) (k : Nat)
    (hk : e.preludeIdx? = some k) (x : (σs : List (Ty ks)) × (τ : Ty ks) × Extern ks σs τ)
    (h : Extern.preludeOfIdx ks k = some x) : x = ⟨σs, τ, e⟩ := by
  cases e with
  | preludeExtern e =>
      simp only [Extern.preludeIdx?, Option.some.injEq] at hk
      subst hk
      cases e <;> simp [Extern.preludeOfIdx, PreludeExtern.ctorIdx] at h <;> exact h.symm
  | _ => simp [Extern.preludeIdx?] at hk

/-- `Extern.beq` on the families compared by `deriving DecidableEq`. -/
def Extern.beqCore {σs : List (Ty ks)} {τ : Ty ks} (e₁ e₂ : Extern ks σs τ) : Bool :=
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

/-- `Extern.beq` on the entries of `PreludeExtern` without type argument: the same constructor
    index, one that `Extern.preludeOfIdx` knows. -/
def Extern.preludeBeq {σs : List (Ty ks)} {τ : Ty ks} (e₁ e₂ : Extern ks σs τ) : Bool :=
  match e₁.preludeIdx?, e₂.preludeIdx? with
  | some k, some k' => k == k' && (Extern.preludeOfIdx ks k).isSome
  | _, _ => false

/-- Are the two entries (of the same signature) recognised as the same entry?  `false` means
    "different, or not recognised" (`Extern.eq_of_beq`). -/
def Extern.beq {σs : List (Ty ks)} {τ : Ty ks} (e₁ e₂ : Extern ks σs τ) : Bool :=
  Extern.beqCore e₁ e₂ || Extern.preludeBeq e₁ e₂

theorem Extern.eq_of_beqCore {σs : List (Ty ks)} {τ : Ty ks} {e₁ e₂ : Extern ks σs τ}
    (h : Extern.beqCore e₁ e₂ = true) : e₁ = e₂ := by
  revert h
  cases e₁ <;> cases e₂ <;> intro h <;>
    first | exact (Bool.false_ne_true h).elim | (have h' := of_decide_eq_true h; subst h'; rfl)

theorem Extern.eq_of_preludeBeq {σs : List (Ty ks)} {τ : Ty ks} {e₁ e₂ : Extern ks σs τ}
    (h : Extern.preludeBeq e₁ e₂ = true) : e₁ = e₂ := by
  unfold Extern.preludeBeq at h
  split at h
  · rename_i k k' hk hk'
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    obtain ⟨rfl, x, hx⟩ := h
    have e1 := Extern.preludeOfIdx_eq e₁ k hk x hx
    have e2 := Extern.preludeOfIdx_eq e₂ k hk' x hx
    rw [e1] at e2
    cases e2
    rfl
  · cases h

/-- An entry recognised as another one is that entry. -/
theorem Extern.eq_of_beq {σs : List (Ty ks)} {τ : Ty ks} {e₁ e₂ : Extern ks σs τ}
    (h : Extern.beq e₁ e₂ = true) : e₁ = e₂ := by
  unfold Extern.beq at h
  rw [Bool.or_eq_true] at h
  exact h.elim Extern.eq_of_beqCore Extern.eq_of_preludeBeq

end LeanScript

end
