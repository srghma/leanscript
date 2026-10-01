module

public import LeanScript.Term.Optimize.Append
public import HashableFloat.Commute
public import HashableFloat.SubSelf
public import LeanScript.Term.Optimize.ShareTest

@[expose] public section

set_option autoImplicit false

/-!
# Commuting (and, in one case, regrouping) float operands for fewer parentheses

IEEE addition and multiplication are **commutative**, exactly (bit for bit, `NaN`, infinities
and both zeros included; `LeanScript.FloatIdentities.Float.add_comm`, `Float.mul_comm`), even
though they are not associative.  So the two operands of a `Float` `+` or `*` may be swapped
freely.  `Neu.floatComm` swaps them when that saves parentheses in JavaScript, where `+`, `-`,
`*` and `/` group from the left:

| Lean | before | after |
|---|---|---|
| `a + (a + (a + a))` | `a + (a + (a + a))` | `a + a + a + a` |
| `a + (a + (a - a))` | `a + (a + (a - a))` | `a - a + a + a` |
| `x * (y / z)` | `x * (y / z)` | `y / z * x` |
| `(x + y) * (z * w)` | `(x + y) * (z * w)` | `z * w * (x + y)` |

In general nothing is regrouped: `a + (b + c)` becomes `(b + c) + a` (`b + c + a`), never
`(a + b) + c`, so every result is the same as before, on every float.

An operand of a float operation is *additive* (`+`, `-`), *multiplicative* (`*`, `/`) or
*atomic* (anything else, printed without parentheses in an operand position;
`PExpr.floatPrec`).  An operand of `+` needs parentheses on the right when it is additive (and
never on the left); an operand of `*` needs them on the right when it is additive or
multiplicative, and on the left when it is additive (`floatParens`).  The operands are swapped
exactly when that makes fewer parentheses (`floatSwap`), so the rewrite is idempotent.

The one regrouping is `(b - b) + (y + z)` (or `(y + z) + (b - b)`) into `((b - b) + y) + z`,
when the two `b` are written the same way (`Neu.floatSubSelf?`): `b - b` is `+0` or `NaN`, and
then the two groupings agree on every float, bit for bit
(`LeanScript.FloatIdentities.Float.sub_self_add_add`); in the language's floats `b - b` is
`+0`, which is what the proof of `Neu.floatSubSelf?` uses.  So `(a - a) + (a + a)` is
`a - a + a + a` in JavaScript.

`Neu.floatComm` is applied by `Term.arithWalk` at every neutral expression of a leaf type
(`Neu.normArithPrim`), bottom-up, so in a nested chain the inner operations are rewritten first.
Proved: the value is unchanged (`Neu.floatComm_eval`).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

open FloatIdentities

/-- How tightly an operand of a float operation binds in JavaScript: `2` for an addition or a
    subtraction, `3` for a multiplication or a division, `4` for anything else. -/
def PExpr.floatPrec : {o : Lvl} → PExpr Δ Φ Γ (.prim .float) o → Nat
  | _, .neu (.extern (.floatExtern .lean_float_add) (.cons _ (.cons _ .nil)) _) => 2
  | _, .neu (.extern (.floatExtern .lean_float_sub) (.cons _ (.cons _ .nil)) _) => 2
  | _, .neu (.extern (.floatExtern .lean_float_mul) (.cons _ (.cons _ .nil)) _) => 3
  | _, .neu (.extern (.floatExtern .lean_float_div) (.cons _ (.cons _ .nil)) _) => 3
  | _, _ => 4

/-- The number of parentheses pairs JavaScript needs around the operands `l` and `r` (given by
    their `PExpr.floatPrec`) of a left-associative operator binding with `prec`. -/
def floatParens (prec l r : Nat) : Nat :=
  (if l < prec then 1 else 0) + (if r ≤ prec then 1 else 0)

/-- Whether swapping the operands (of `PExpr.floatPrec` `l` and `r`) of an operator binding with
    `prec` saves parentheses. -/
def floatSwap (prec l r : Nat) : Bool :=
  decide (floatParens prec r l < floatParens prec l r)

/-- The level of two arguments does not depend on their order. -/
theorem Lvl.meet_swap_two {o₁ o₂ : Lvl} {ℓ : Nat}
    (h : Lvl.meet o₁ (Lvl.meet o₂ none) = some ℓ) : Lvl.meet o₂ (Lvl.meet o₁ none) = some ℓ := by
  rw [Lvl.meet_none] at h ⊢
  cases o₁ <;> cases o₂ <;> simp_all [Lvl.meet, Nat.min_comm]

/-- A neutral expression with the value of `n`. -/
structure Neu.EvalEq {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) where
  m : Neu Δ Φ Γ τ ℓ
  eval : ∀ κ ρ, m.eval κ ρ = n.eval κ ρ

/-! ## `(b - b) + (y + z)` regrouped -/

/-- When the operand is `b - b` (the same expression twice, `PExpr.same`): the proof that its
    value is `+0` in the language's floats (`HashableFloat.toFloat_normalize_sub_self`). -/
def PExpr.floatSubSelf? : {o : Lvl} → (x : PExpr Δ Φ Γ (.prim .float) o) →
    Option (PLift (∀ κ ρ, HashableFloat.toFloat (x.eval κ ρ) = Float.ofBits 0))
  | _, .neu (.extern (.floatExtern .lean_float_sub) (.cons b (.cons b' .nil)) _) =>
    if h : b.same b' then
      some ⟨fun κ ρ => by
        obtain ⟨_, hb⟩ := PExpr.same_eval b b' h
        have e : b.eval κ ρ = b'.eval κ ρ := eq_of_heq (hb κ ρ)
        show HashableFloat.toFloat (HashableFloat.normalize
          (Float.sub (HashableFloat.toFloat (b.eval κ ρ)) (HashableFloat.toFloat (b'.eval κ ρ)))) = _
        rw [← e]
        exact HashableFloat.toFloat_normalize_sub_self _⟩
    else none
  | _, _ => none

/-- The two operands of a `Float` addition. -/
structure PExpr.FloatSum {o : Lvl} (y : PExpr Δ Φ Γ (.prim .float) o) where
  o₁ : Lvl
  a : PExpr Δ Φ Γ (.prim .float) o₁
  o₂ : Lvl
  b : PExpr Δ Φ Γ (.prim .float) o₂
  eval : ∀ κ ρ, y.eval κ ρ = HashableFloat.normalize
    (Float.add (HashableFloat.toFloat (a.eval κ ρ)) (HashableFloat.toFloat (b.eval κ ρ)))

/-- The two operands, when the operand is a `Float` addition. -/
def PExpr.floatSum? : {o : Lvl} → (y : PExpr Δ Φ Γ (.prim .float) o) → Option y.FloatSum
  | _, .neu (.extern (.floatExtern .lean_float_add) (.cons a (.cons b .nil)) _) =>
    some ⟨_, a, _, b, fun _ _ => rfl⟩
  | _, _ => none

/-- `(x + a) + b`, when the levels work out (the level of the result is checked). -/
def Neu.floatAddLeft? {ℓ : Nat} {ox o₁ o₂ : Lvl} (x : PExpr Δ Φ Γ (.prim .float) ox)
    (a : PExpr Δ Φ Γ (.prim .float) o₁) (b : PExpr Δ Φ Γ (.prim .float) o₂) :
    Option (Neu Δ Φ Γ (.prim .float) ℓ) :=
  match hm : Lvl.meet ox (Lvl.meet o₁ none) with
  | some ℓ' =>
    if hl : Lvl.meet (some ℓ') (Lvl.meet o₂ none) = some ℓ then
      some (.extern (.floatExtern .lean_float_add)
        (.cons (.neu (.extern (.floatExtern .lean_float_add) (.cons x (.cons a .nil)) hm))
          (.cons b .nil)) hl)
    else none
  | none => none

theorem Neu.floatAddLeft?_eval {ℓ : Nat} {ox o₁ o₂ : Lvl} (x : PExpr Δ Φ Γ (.prim .float) ox)
    (a : PExpr Δ Φ Γ (.prim .float) o₁) (b : PExpr Δ Φ Γ (.prim .float) o₂)
    (m : Neu Δ Φ Γ (.prim .float) ℓ) (h : Neu.floatAddLeft? x a b = some m)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    m.eval κ ρ = HashableFloat.normalize (Float.add (HashableFloat.toFloat
      (HashableFloat.normalize (Float.add (HashableFloat.toFloat (x.eval κ ρ))
        (HashableFloat.toFloat (a.eval κ ρ))))) (HashableFloat.toFloat (b.eval κ ρ))) := by
  unfold Neu.floatAddLeft? at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

/-- `+0 + (y + z)` and `(+0 + y) + z` have the same value in the language's floats. -/
theorem HashableFloat.normalize_zero_add_add (x y z : HashableFloat) (hx : x.toFloat = Float.ofBits 0) :
    HashableFloat.normalize (Float.add x.toFloat
      (HashableFloat.normalize (Float.add y.toFloat z.toFloat)).toFloat) =
    HashableFloat.normalize (Float.add
      (HashableFloat.normalize (Float.add x.toFloat y.toFloat)).toFloat z.toFloat) := by
  rw [hx, Float.zero_add _ (HashableFloat.normalize _).notNegZero, HashableFloat.normalize_toFloat,
    Float.zero_add _ y.notNegZero, HashableFloat.normalize_toFloat]

/-- **`(b - b) + (y + z)` regrouped as `((b - b) + y) + z`**, and `(y + z) + (b - b)` as
    `((b - b) + y) + z` too, with the proof that the value is the same (in the language's
    floats `b - b` is `+0`; on every float the identity holds bit for bit as well,
    `FloatIdentities.Float.sub_self_add_add`). -/
def Neu.floatSubSelf? {ℓ : Nat} : (n : Neu Δ Φ Γ (.prim .float) ℓ) → Option n.EvalEq
  | .extern (.floatExtern .lean_float_add) (.cons x (.cons y .nil)) _ =>
    match x.floatSubSelf? with
    | some hx =>
      match y.floatSum? with
      | some s =>
        match hm : Neu.floatAddLeft? (ℓ := ℓ) x s.a s.b with
        | some m => some ⟨m, fun κ ρ => by
            rw [Neu.floatAddLeft?_eval x s.a s.b m hm]
            show _ = HashableFloat.normalize (Float.add (HashableFloat.toFloat (x.eval κ ρ))
              (HashableFloat.toFloat (y.eval κ ρ)))
            rw [s.eval]
            exact (HashableFloat.normalize_zero_add_add _ _ _ (hx.down κ ρ)).symm⟩
        | none => none
      | none => none
    | none =>
    match y.floatSubSelf? with
    | some hy =>
      match x.floatSum? with
      | some s =>
        match hm : Neu.floatAddLeft? (ℓ := ℓ) y s.a s.b with
        | some m => some ⟨m, fun κ ρ => by
            rw [Neu.floatAddLeft?_eval y s.a s.b m hm]
            show _ = HashableFloat.normalize (Float.add (HashableFloat.toFloat (x.eval κ ρ))
              (HashableFloat.toFloat (y.eval κ ρ)))
            rw [s.eval]
            conv => rhs; rw [Float.add_comm]
            exact (HashableFloat.normalize_zero_add_add _ _ _ (hy.down κ ρ)).symm⟩
        | none => none
      | none => none
    | none => none
  | _ => none

/-! ## Commuting -/

/-- **The operands of a `Float` `+` or `*` swapped** when that saves parentheses in JavaScript
    (`floatSwap`), with the proof that the value is the same; any other expression is kept. -/
def Neu.floatComm64? {ℓ : Nat} : (n : Neu Δ Φ Γ (.prim .float) ℓ) → n.EvalEq
  | .extern (.floatExtern .lean_float_add) (.cons x (.cons y .nil)) h =>
    if floatSwap 2 x.floatPrec y.floatPrec then
      ⟨.extern (.floatExtern .lean_float_add) (.cons y (.cons x .nil)) (Lvl.meet_swap_two h),
        fun κ ρ => by
          show HashableFloat.normalize (Float.add (HashableFloat.toFloat (y.eval κ ρ))
              (HashableFloat.toFloat (x.eval κ ρ))) =
            HashableFloat.normalize (Float.add (HashableFloat.toFloat (x.eval κ ρ))
              (HashableFloat.toFloat (y.eval κ ρ)))
          rw [Float.add_comm]⟩
    else ⟨_, fun _ _ => rfl⟩
  | .extern (.floatExtern .lean_float_mul) (.cons x (.cons y .nil)) h =>
    if floatSwap 3 x.floatPrec y.floatPrec then
      ⟨.extern (.floatExtern .lean_float_mul) (.cons y (.cons x .nil)) (Lvl.meet_swap_two h),
        fun κ ρ => by
          show HashableFloat.normalize (Float.mul (HashableFloat.toFloat (y.eval κ ρ))
              (HashableFloat.toFloat (x.eval κ ρ))) =
            HashableFloat.normalize (Float.mul (HashableFloat.toFloat (x.eval κ ρ))
              (HashableFloat.toFloat (y.eval κ ρ)))
          rw [Float.mul_comm]⟩
    else ⟨_, fun _ _ => rfl⟩
  | n => ⟨n, fun _ _ => rfl⟩

/-- `Neu.floatComm64?`, the expression only. -/
def Neu.floatComm64 {ℓ : Nat} (n : Neu Δ Φ Γ (.prim .float) ℓ) : Neu Δ Φ Γ (.prim .float) ℓ :=
  match n.floatSubSelf? with
  | some r => r.m
  | none => n.floatComm64?.m

/-- `Neu.floatComm64` at a leaf type, when it is `Float`. -/
def Neu.floatComm {ℓ : Nat} : (p : LeanPrimTy) → Neu Δ Φ Γ (.prim p) ℓ → Neu Δ Φ Γ (.prim p) ℓ
  | .float, n => n.floatComm64
  | _, n => n

theorem Neu.floatComm64_eval {ℓ : Nat} (n : Neu Δ Φ Γ (.prim .float) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : n.floatComm64.eval κ ρ = n.eval κ ρ := by
  unfold Neu.floatComm64
  split
  · rename_i r _; exact r.eval κ ρ
  · exact n.floatComm64?.eval κ ρ

theorem Neu.floatComm_eval (p : LeanPrimTy) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim p) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (Neu.floatComm p n).eval κ ρ = n.eval κ ρ := by
  unfold Neu.floatComm
  split
  · exact Neu.floatComm64_eval _ κ ρ
  · rfl

end LeanScript

end
