module

public import LeanScript.Term.Optimize.Append
public import HashableFloat.Identities

@[expose] public section

set_option autoImplicit false

/-!
# Units of float operations

A float operation with a unit operand is that operand, **exactly** (bit for bit, in Lean's
logical model of floats, `LeanScript.FloatIdentities`):

| call | becomes |
|---|---|
| `x * 1.0`, `1.0 * x`, `x / 1.0` | `x` |
| `x - 0.0` | `x` |

for `Float` (`lean_float_*`) and `Float32` (`lean_float32_*`).  These hold for **every** float,
`-0.0` and `NaN` included, so the JavaScript stays exact even on inputs the language's floats
(`HashableFloat`) exclude.  `x + 0.0` and `0.0 + x` are deliberately *not* rewritten: they are
`x` only when `x` is not `-0.0` (`-0.0 + 0.0` is `+0.0`), which holds for `HashableFloat` but
not for every JavaScript number a caller may pass.

Nothing else is done to float chains.  In particular they are **not re-associated** (as the
integer chains are by `Term.arithWalk`): `1.0 + (2.0 + x)` is not `3.0 + x` in IEEE arithmetic
(it differs at `x = 3/7`, see `Tests/TermTests/Optimize/AssocNumberOpsTest.lean`).

`Neu.floatUnit` is applied by `Term.arithWalk` at every neutral expression of a leaf type
(`Neu.normArithPrim`), bottom-up.  Proved: the value is unchanged (`Neu.floatUnit_eval`).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

open FloatIdentities

/-! ## Literals by their bits -/

/-- The bits of an operand that is a `Float` literal. -/
def PExpr.floatBits? : {o : Lvl} → PExpr Δ Φ Γ (.prim .float) o → Option UInt64
  | _, .lit _ v => some (HashableFloat.toFloat v).toBits
  | _, _ => none

theorem PExpr.floatBits?_eval {o : Lvl} (e : PExpr Δ Φ Γ (.prim .float) o) (b : UInt64)
    (h : e.floatBits? = some b) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    HashableFloat.toFloat (e.eval κ ρ) = Float.ofBits b := by
  unfold PExpr.floatBits? at h
  split at h
  · cases h; exact (Float.ofBits_toBits _).symm
  · cases h

/-- The bits of an operand that is a `Float32` literal. -/
def PExpr.float32Bits? : {o : Lvl} → PExpr Δ Φ Γ (.prim .float32) o → Option UInt32
  | _, .lit _ v => some (HashableFloat32.toFloat32 v).toBits
  | _, _ => none

theorem PExpr.float32Bits?_eval {o : Lvl} (e : PExpr Δ Φ Γ (.prim .float32) o) (b : UInt32)
    (h : e.float32Bits? = some b) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    HashableFloat32.toFloat32 (e.eval κ ρ) = Float32.ofBits b := by
  unfold PExpr.float32Bits? at h
  split at h
  · cases h; exact (Float32.ofBits_toBits _).symm
  · cases h

/-! ## The identities on the values of the language -/

theorem HashableFloat.normalize_mul_one (a : HashableFloat) :
    HashableFloat.normalize (Float.mul a.toFloat (Float.ofBits Float.oneBits)) = a := by
  rw [Float.mul_one, HashableFloat.normalize_toFloat]

theorem HashableFloat.normalize_one_mul (a : HashableFloat) :
    HashableFloat.normalize (Float.mul (Float.ofBits Float.oneBits) a.toFloat) = a := by
  rw [Float.one_mul, HashableFloat.normalize_toFloat]

theorem HashableFloat.normalize_div_one (a : HashableFloat) :
    HashableFloat.normalize (Float.div a.toFloat (Float.ofBits Float.oneBits)) = a := by
  rw [Float.div_one, HashableFloat.normalize_toFloat]

theorem HashableFloat.normalize_sub_zero (a : HashableFloat) :
    HashableFloat.normalize (Float.sub a.toFloat (Float.ofBits 0)) = a := by
  rw [Float.sub_zero, HashableFloat.normalize_toFloat]

theorem HashableFloat32.normalize_mul_one (a : HashableFloat32) :
    HashableFloat32.normalize (Float32.mul a.toFloat32 (Float32.ofBits Float32.oneBits)) = a := by
  rw [Float32.mul_one, HashableFloat32.normalize_toFloat32]

theorem HashableFloat32.normalize_one_mul (a : HashableFloat32) :
    HashableFloat32.normalize (Float32.mul (Float32.ofBits Float32.oneBits) a.toFloat32) = a := by
  rw [Float32.one_mul, HashableFloat32.normalize_toFloat32]

theorem HashableFloat32.normalize_div_one (a : HashableFloat32) :
    HashableFloat32.normalize (Float32.div a.toFloat32 (Float32.ofBits Float32.oneBits)) = a := by
  rw [Float32.div_one, HashableFloat32.normalize_toFloat32]

theorem HashableFloat32.normalize_sub_zero (a : HashableFloat32) :
    HashableFloat32.normalize (Float32.sub a.toFloat32 (Float32.ofBits 0)) = a := by
  rw [Float32.sub_zero, HashableFloat32.normalize_toFloat32]

/-! ## The rewrite -/

/-- An operand that has the value of a neutral expression. -/
structure Neu.SameAs {p : LeanPrimTy} {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ) where
  o : Lvl
  e : PExpr Δ Φ Γ (.prim p) o
  eval : ∀ κ ρ, e.eval κ ρ = n.eval κ ρ

/-- The other operand, when a binary call has a unit operand (at `Float`). -/
def Neu.floatUnit64? {ℓ : Nat} : (n : Neu Δ Φ Γ (.prim .float) ℓ) → Option n.SameAs
  | .extern (.floatExtern .lean_float_mul) (.cons x (.cons y .nil)) _ =>
    match hy : y.floatBits? with
    | some b =>
      if hb : b = Float.oneBits then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat.normalize (Float.mul _ (HashableFloat.toFloat (y.eval κ ρ)))
          rw [PExpr.floatBits?_eval y b hy, hb]; exact (HashableFloat.normalize_mul_one _).symm⟩
      else none
    | none =>
      match hx : x.floatBits? with
      | some b =>
        if hb : b = Float.oneBits then
          some ⟨_, y, fun κ ρ => by
            show _ = HashableFloat.normalize (Float.mul (HashableFloat.toFloat (x.eval κ ρ)) _)
            rw [PExpr.floatBits?_eval x b hx, hb]; exact (HashableFloat.normalize_one_mul _).symm⟩
        else none
      | none => none
  | .extern (.floatExtern .lean_float_div) (.cons x (.cons y .nil)) _ =>
    match hy : y.floatBits? with
    | some b =>
      if hb : b = Float.oneBits then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat.normalize (Float.div _ (HashableFloat.toFloat (y.eval κ ρ)))
          rw [PExpr.floatBits?_eval y b hy, hb]; exact (HashableFloat.normalize_div_one _).symm⟩
      else none
    | none => none
  | .extern (.floatExtern .lean_float_sub) (.cons x (.cons y .nil)) _ =>
    match hy : y.floatBits? with
    | some b =>
      if hb : b = 0 then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat.normalize (Float.sub _ (HashableFloat.toFloat (y.eval κ ρ)))
          rw [PExpr.floatBits?_eval y b hy, hb]; exact (HashableFloat.normalize_sub_zero _).symm⟩
      else none
    | none => none
  | _ => none

/-- The other operand, when a binary call has a unit operand (at `Float32`). -/
def Neu.floatUnit32? {ℓ : Nat} : (n : Neu Δ Φ Γ (.prim .float32) ℓ) → Option n.SameAs
  | .extern (.float32Extern .lean_float32_mul) (.cons x (.cons y .nil)) _ =>
    match hy : y.float32Bits? with
    | some b =>
      if hb : b = Float32.oneBits then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat32.normalize (Float32.mul _ (HashableFloat32.toFloat32 (y.eval κ ρ)))
          rw [PExpr.float32Bits?_eval y b hy, hb]; exact (HashableFloat32.normalize_mul_one _).symm⟩
      else none
    | none =>
      match hx : x.float32Bits? with
      | some b =>
        if hb : b = Float32.oneBits then
          some ⟨_, y, fun κ ρ => by
            show _ = HashableFloat32.normalize (Float32.mul (HashableFloat32.toFloat32 (x.eval κ ρ)) _)
            rw [PExpr.float32Bits?_eval x b hx, hb]; exact (HashableFloat32.normalize_one_mul _).symm⟩
        else none
      | none => none
  | .extern (.float32Extern .lean_float32_div) (.cons x (.cons y .nil)) _ =>
    match hy : y.float32Bits? with
    | some b =>
      if hb : b = Float32.oneBits then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat32.normalize (Float32.div _ (HashableFloat32.toFloat32 (y.eval κ ρ)))
          rw [PExpr.float32Bits?_eval y b hy, hb]; exact (HashableFloat32.normalize_div_one _).symm⟩
      else none
    | none => none
  | .extern (.float32Extern .lean_float32_sub) (.cons x (.cons y .nil)) _ =>
    match hy : y.float32Bits? with
    | some b =>
      if hb : b = 0 then
        some ⟨_, x, fun κ ρ => by
          show _ = HashableFloat32.normalize (Float32.sub _ (HashableFloat32.toFloat32 (y.eval κ ρ)))
          rw [PExpr.float32Bits?_eval y b hy, hb]; exact (HashableFloat32.normalize_sub_zero _).symm⟩
      else none
    | none => none
  | _ => none

/-- The other operand, when a binary float call has a unit operand. -/
def Neu.floatUnit? {ℓ : Nat} : (p : LeanPrimTy) → (n : Neu Δ Φ Γ (.prim p) ℓ) → Option n.SameAs
  | .float, n => n.floatUnit64?
  | .float32, n => n.floatUnit32?
  | _, _ => none

/-- **A unit operand of a float operation dropped** (`x * 1.0` is `x`, …), when the other
    operand is a neutral expression of the same level (otherwise the expression is kept). -/
def Neu.floatUnit (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ) :
    Neu Δ Φ Γ (.prim p) ℓ :=
  match Neu.floatUnit? p n with
  | some r =>
    if h : r.o = some ℓ then
      match PExpr.asNeu? (h ▸ r.e) with
      | some m => m.1
      | none => n
    else n
  | none => n

theorem PExpr.eval_levelCast {τ : Ty ks} {o o' : Lvl} (h : o = o') (e : PExpr Δ Φ Γ τ o)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (h ▸ e).eval κ ρ = e.eval κ ρ := by
  subst h; rfl

theorem Neu.floatUnit_eval (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (Neu.floatUnit p n).eval κ ρ = n.eval κ ρ := by
  unfold Neu.floatUnit
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
