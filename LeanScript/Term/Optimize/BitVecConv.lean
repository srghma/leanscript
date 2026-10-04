module

public import LeanScript.Term.Optimize.FloatUnit

@[expose] public section

set_option autoImplicit false

/-!
# A fixed-width integer read as its bit vector and back

`UInt32.ofBitVec (UInt32.toBitVec y)` is `y` (a structure is the constructor of its field), for
`UInt8`, `UInt16`, `UInt32` and `UInt64`: the externs `lean_uint32_of_nat_mk` and
`lean_uint32_to_nat__UInt32_toBitVec` cancel out.  The translation of the operations of
`BitVec w` (`LeanScript/TermElab/ToTerm/BitVecOps.lean`) writes each one as the operation of the
fixed-width integer between these conversions (`a * b + c` on `BitVec 32` is
`toBitVec(add(ofBitVec(toBitVec(mul(ofBitVec(a), ofBitVec(b)))), ofBitVec(c)))`), so a chain of
them leaves such a pair between two operations, which this rewrite drops
(`toBitVec(add(mul(ofBitVec(a), ofBitVec(b)), ofBitVec(c)))`).

`Neu.uintRoundTrip` is applied by `Term.arithWalk` at every neutral expression of a leaf type
(`Neu.normArithPrim`), bottom-up.  Proved: the value is unchanged (`Neu.uintRoundTrip_eval`).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

/-- The integer `y` of a bit vector written `UInt8.toBitVec y`. -/
def PExpr.ofToBitVec8? {h : 2 ≤ 8} : {o : Lvl} → (x : PExpr Δ Φ Γ (.prim (.bitvec 8 h)) o) →
    Option ((o' : Lvl) × (y : PExpr Δ Φ Γ (.prim .uint8) o') ×'
      ∀ κ ρ, x.eval κ ρ = UInt8.toBitVec (y.eval κ ρ))
  | _, .neu (.extern (.preludeExtern .lean_uint8_to_nat__UInt8_toBitVec) (.cons y .nil) _) =>
    some ⟨_, y, fun _ _ => rfl⟩
  | _, _ => none

/-- The integer `y` of a bit vector written `UInt16.toBitVec y`. -/
def PExpr.ofToBitVec16? {h : 2 ≤ 16} : {o : Lvl} → (x : PExpr Δ Φ Γ (.prim (.bitvec 16 h)) o) →
    Option ((o' : Lvl) × (y : PExpr Δ Φ Γ (.prim .uint16) o') ×'
      ∀ κ ρ, x.eval κ ρ = UInt16.toBitVec (y.eval κ ρ))
  | _, .neu (.extern (.preludeExtern .lean_uint16_to_nat__UInt16_toBitVec) (.cons y .nil) _) =>
    some ⟨_, y, fun _ _ => rfl⟩
  | _, _ => none

/-- The integer `y` of a bit vector written `UInt32.toBitVec y`. -/
def PExpr.ofToBitVec32? {h : 2 ≤ 32} : {o : Lvl} → (x : PExpr Δ Φ Γ (.prim (.bitvec 32 h)) o) →
    Option ((o' : Lvl) × (y : PExpr Δ Φ Γ (.prim .uint32) o') ×'
      ∀ κ ρ, x.eval κ ρ = UInt32.toBitVec (y.eval κ ρ))
  | _, .neu (.extern (.preludeExtern .lean_uint32_to_nat__UInt32_toBitVec) (.cons y .nil) _) =>
    some ⟨_, y, fun _ _ => rfl⟩
  | _, _ => none

/-- The integer `y` of a bit vector written `UInt64.toBitVec y`. -/
def PExpr.ofToBitVec64? {h : 2 ≤ 64} : {o : Lvl} → (x : PExpr Δ Φ Γ (.prim (.bitvec 64 h)) o) →
    Option ((o' : Lvl) × (y : PExpr Δ Φ Γ (.prim .uint64) o') ×'
      ∀ κ ρ, x.eval κ ρ = UInt64.toBitVec (y.eval κ ρ))
  | _, .neu (.extern (.preludeExtern .lean_uint64_to_nat__UInt64_toBitVec) (.cons y .nil) _) =>
    some ⟨_, y, fun _ _ => rfl⟩
  | _, _ => none

/-- The integer `y`, when the neutral expression is `UIntW.ofBitVec (UIntW.toBitVec y)`. -/
def Neu.uintRoundTrip? {ℓ : Nat} : (p : LeanPrimTy) → (n : Neu Δ Φ Γ (.prim p) ℓ) →
    Option n.SameAs
  | .uint8, .extern (.preludeExtern .lean_uint8_of_nat_mk) (.cons x .nil) _ =>
    match x.ofToBitVec8? with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt8.ofBitVec (x.eval κ ρ); rw [hy]; rfl⟩
    | none => none
  | .uint16, .extern (.preludeExtern .lean_uint16_of_nat_mk) (.cons x .nil) _ =>
    match x.ofToBitVec16? with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt16.ofBitVec (x.eval κ ρ); rw [hy]; rfl⟩
    | none => none
  | .uint32, .extern (.preludeExtern .lean_uint32_of_nat_mk) (.cons x .nil) _ =>
    match x.ofToBitVec32? with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt32.ofBitVec (x.eval κ ρ); rw [hy]; rfl⟩
    | none => none
  | .uint64, .extern (.preludeExtern .lean_uint64_of_nat_mk) (.cons x .nil) _ =>
    match x.ofToBitVec64? with
    | some ⟨_, y, hy⟩ => some ⟨_, y, fun κ ρ => by
        show _ = UInt64.ofBitVec (x.eval κ ρ); rw [hy]; rfl⟩
    | none => none
  | _, _ => none

/-- **A fixed-width integer read as its bit vector and back is itself**
    (`UInt32.ofBitVec (UInt32.toBitVec y)` is `y`), when `y` is a neutral expression of the same
    level (otherwise the expression is kept). -/
def Neu.uintRoundTrip (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ) :
    Neu Δ Φ Γ (.prim p) ℓ :=
  match Neu.uintRoundTrip? p n with
  | some r =>
    if h : r.o = some ℓ then
      match PExpr.asNeu? (h ▸ r.e) with
      | some m => m.1
      | none => n
    else n
  | none => n

theorem Neu.uintRoundTrip_eval (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (Neu.uintRoundTrip p n).eval κ ρ = n.eval κ ρ := by
  unfold Neu.uintRoundTrip
  split
  · rename_i r _
    split
    · rename_i h
      split
      · rename_i m _
        rw [m.2, PExpr.eval_levelCast, r.eval]
      · rfl
    · rfl
  · rfl

end LeanScript

end
