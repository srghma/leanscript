module

public import LeanScript.Term.Optimize.ArithBasic

@[expose] public section

set_option autoImplicit false

/-!
# Chains of multiplications: powers of an unknown

In a product of `Int`s or of `Nat`s, the operands `x`, `x ^ k₁`, …, `x ^ kₙ` of the same unknown
`x` (a power by a literal, `Int.pow`/`lean_int_pow` or `Nat.pow`/`lean_nat_pow`) are one power
`x ^ (1 + … + kₙ)`: `x * x * x * x * 24` is `x ^ 4 * 24` (`x ** 4n * 24n` in JavaScript).  This
is the multiplicative half of the counting of `LeanScript.Term.Optimize.Arith` (`ArithOp.group`),
which uses `ArithOp.groupPow`; `x ^ k` counts as `k` copies of `x`, so a product normalised
bottom-up is the same as if it had been read at once.

The fixed-width integers have no power extern, so their products are not grouped.
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks}

namespace ArithOp

/-- Whether the operation is a multiplication with a power extern (`Int.pow`, `Nat.pow`). -/
def hasPow : ArithOp → Bool
  | .intMul | .natMul => true
  | _ => false

/-- `x ^ k`, in the type of a multiplication with a power extern (`x` otherwise). -/
def pow : (a : ArithOp) → a.D → Nat → a.D
  | .intMul => fun x k => Int.pow x k
  | .natMul => fun x k => Nat.pow x k
  | _ => fun x _ => x

theorem pow_one : (a : ArithOp) → a.hasPow = true → (x : a.D) → a.pow x 1 = x
  | .intMul, _, x => Int.pow_one x
  | .natMul, _, x => Nat.pow_one x

theorem op_pow_pow : (a : ArithOp) → a.hasPow = true → (x : a.D) → (m n : Nat) →
    a.op (a.pow x m) (a.pow x n) = a.pow x (m + n)
  | .intMul, _, x, m, n => (Int.pow_add x m n).symm
  | .natMul, _, x, m, n => (Nat.pow_add x m n).symm

/-- The power extern of a multiplication. -/
def powExt : (a : ArithOp) → a.hasPow = true →
    Extern ks [.prim a.prim, .prim .nat] (.prim a.prim)
  | .intMul, _ => .intBasicExtern .lean_int_pow
  | .natMul, _ => .preludeExtern .lean_nat_pow

variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- A call of a binary extern on two operands of which one at least is open. -/
def call2 {σ₁ σ₂ τ : Ty ks} {o₁ o₂ : Lvl} {ℓ : Nat} (e : Extern ks [σ₁, σ₂] τ)
    (x : PExpr Δ Φ Γ σ₁ o₁) (y : PExpr Δ Φ Γ σ₂ o₂) (h : Lvl.meet o₁ o₂ = some ℓ) :
    PExpr Δ Φ Γ τ (some ℓ) :=
  .neu (.extern e (.cons x (.cons y .nil)) (by rw [Lvl.meet_none]; exact h))

theorem call2_powExt_eval : (a : ArithOp) → (hp : a.hasPow = true) → {o₁ o₂ : Lvl} → {ℓ : Nat} →
    (x : PExpr Δ Φ Γ (.prim a.prim) o₁) → (y : PExpr Δ Φ Γ (.prim .nat) o₂) →
    (h : Lvl.meet o₁ o₂ = some ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (call2 (a.powExt hp) x y h).eval κ ρ = a.pow (x.eval κ ρ) (y.eval κ ρ)
  | .intMul, _, _, _, _, _, _, _, _, _ => rfl
  | .natMul, _, _, _, _, _, _, _, _, _ => rfl

/-- The value of a `Nat` literal. -/
def natLit? : {o : Lvl} → PExpr Δ Φ Γ (.prim .nat) o → Option Nat
  | _, .lit _ v => some v
  | _, _ => none

theorem natLit?_eval {o : Lvl} (e : PExpr Δ Φ Γ (.prim .nat) o) (k : Nat)
    (h : natLit? e = some k) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : e.eval κ ρ = k := by
  unfold natLit? at h
  split at h
  · cases h; rfl
  · cases h

/-- A power by a literal, `x ^ k`, with the fact that it is one. -/
structure PowLit (a : ArithOp) {o : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o) where
  o' : Lvl
  x : PExpr Δ Φ Γ (.prim a.prim) o'
  k : Nat
  eval : ∀ κ ρ, e.eval κ ρ = a.pow (x.eval κ ρ) k

theorem powLit_eval (a : ArithOp) {o o₁ o₂ : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o)
    (x : PExpr Δ Φ Γ (.prim a.prim) o₁) (y : PExpr Δ Φ Γ (.prim .nat) o₂)
    (hxy : ∀ κ ρ, e.eval κ ρ = a.pow (x.eval κ ρ) (y.eval κ ρ)) (k : Nat)
    (hy : natLit? y = some k) : ∀ κ ρ, e.eval κ ρ = a.pow (x.eval κ ρ) k :=
  fun κ ρ => by rw [hxy, natLit?_eval y k hy]

/-- The operand and the exponent, when a pure expression is a power by a literal (in the type
    of a multiplication with a power extern). -/
def powView : (a : ArithOp) → {o : Lvl} → (e : PExpr Δ Φ Γ (.prim a.prim) o) →
    Option (a.PowLit e)
  | .intMul, _, .neu (.extern (.intBasicExtern .lean_int_pow) (.cons x (.cons y .nil)) _) =>
      match hy : natLit? y with
      | some k => some ⟨_, x, k, powLit_eval .intMul _ x y (fun _ _ => rfl) k hy⟩
      | none => none
  | .natMul, _, .neu (.extern (.preludeExtern .lean_nat_pow) (.cons x (.cons y .nil)) _) =>
      match hy : natLit? y with
      | some k => some ⟨_, x, k, powLit_eval .natMul _ x y (fun _ _ => rfl) k hy⟩
      | none => none
  | _, _, _ => none

/-- An operand of a product that is an unknown `x`, or a power `x ^ k` of an unknown by a
    literal: the position of the unknown, the unknown and the exponent (`1` for `x` alone). -/
structure PowTerm (a : ArithOp) (p : Opnd Δ Φ Γ a) where
  idx : Nat
  base : Opnd Δ Φ Γ a
  exp : Nat
  base_idx : a.varIdx? base = some idx
  eval : ∀ κ ρ, a.val p κ ρ = a.pow (a.val base κ ρ) exp

/-- The unknown and its exponent, when an operand of a product is `x` or `x ^ k`. -/
def powTerm? (a : ArithOp) (h : a.hasPow = true) (p : Opnd Δ Φ Γ a) : Option (a.PowTerm p) :=
  match hv : a.varIdx? p with
  | some i => some ⟨i, p, 1, hv, fun _ _ => (a.pow_one h _).symm⟩
  | none =>
    match a.powView p.2 with
    | some m =>
      match hb : a.varIdx? ⟨_, m.x⟩ with
      | some i => some ⟨i, ⟨_, m.x⟩, m.k, hb, fun κ ρ => m.eval κ ρ⟩
      | none => none
    | none => none

/-- The position of the unknown of an operand of a product that is `x` or `x ^ k`. -/
def powIdxOf? (a : ArithOp) (h : a.hasPow = true) (p : Opnd Δ Φ Γ a) : Option Nat :=
  (a.powTerm? h p).map (·.idx)

/-- The exponent of an operand of a product that is `x ^ k` (`1` for `x`). -/
def expOf (a : ArithOp) (h : a.hasPow = true) (p : Opnd Δ Φ Γ a) : Nat :=
  match a.powTerm? h p with
  | some t => t.exp
  | none => 1

/-- Every operand of the same unknown as a first one is a power of that unknown. -/
theorem val_of_powIdxOf (a : ArithOp) (h : a.hasPow = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (x : Opnd Δ Φ Γ a) (t : a.PowTerm x) (q : Opnd Δ Φ Γ a) (hq : a.powIdxOf? h q = some t.idx) :
    a.val q κ ρ = a.pow (a.val t.base κ ρ) (a.expOf h q) := by
  unfold powIdxOf? at hq
  unfold expOf
  cases hv : a.powTerm? h q with
  | none => rw [hv] at hq; cases hq
  | some tq =>
    rw [hv] at hq
    have hi : tq.idx = t.idx := Option.some.inj hq
    simp only
    rw [tq.eval, varIdx?_eval a κ ρ tq.base t.base t.idx (hi ▸ tq.base_idx) t.base_idx]

/-- `x ^ c * (x ^ k₁ * (… * unit))` is `x ^ (c + k₁ + … + kₙ)`. -/
theorem op_pow_den (a : ArithOp) (h : a.hasPow = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : a.D)
    (f : Opnd Δ Φ Γ a → Nat) : (c : Nat) → (qs : List (Opnd Δ Φ Γ a)) →
    (∀ q ∈ qs, a.val q κ ρ = a.pow v (f q)) →
    a.op (a.pow v c) (a.den qs κ ρ) = a.pow v (c + (qs.map f).sum)
  | c, [], _ => by simp [op_unit]
  | c, q :: qs, hq => by
    rw [den_cons, hq q (List.mem_cons_self), op_pow_den a h κ ρ v f (f q) qs
      (fun q' h' => hq q' (List.mem_cons_of_mem _ h')), op_pow_pow a h, List.map_cons,
      List.sum_cons]

/-- `x ^ k` (`x` when `k` is `1`), where `x` is an unknown. -/
def powBy (a : ArithOp) (h : a.hasPow = true) (x : Opnd Δ Φ Γ a) (k : Nat) :
    Option (Opnd Δ Φ Γ a) :=
  if k = 1 then some x
  else
    match hm : Lvl.meet x.1 none with
    | some ℓ => some ⟨some ℓ, call2 (a.powExt h) x.2 (.lit .nat k) hm⟩
    | none => none

theorem powBy_val (a : ArithOp) (h : a.hasPow = true) (x : Opnd Δ Φ Γ a) (k : Nat)
    (x' : Opnd Δ Φ Γ a) (hx : a.powBy h x k = some x') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    a.val x' κ ρ = a.pow (a.val x κ ρ) k := by
  unfold powBy at hx
  split at hx
  · rename_i hk
    cases hx
    rw [hk, pow_one a h]
  · split at hx
    · cases hx
      simp only [val]
      rw [call2_powExt_eval a h]
      rfl
    · cases hx

/-- The smallest number of copies of an unknown written as a power (`x * x` stays). -/
def powMin : Nat := 3

/-- In a product, the operands `x`, `x ^ k₁`, …, `x ^ kₙ` of the same unknown as the first
    operand `x₀` (one at least) become `x ^ (k₀ + k₁ + … + kₙ)`, when that is at least
    `powMin` copies: the power, and the other operands (`none` when there is nothing to
    group). -/
def groupPow (a : ArithOp) (h : a.hasPow = true) (x : Opnd Δ Φ Γ a) (xs : List (Opnd Δ Φ Γ a)) :
    Option (Opnd Δ Φ Γ a × List (Opnd Δ Φ Γ a)) :=
  match a.powTerm? h x with
  | none => none
  | some t =>
    let same := xs.filter (fun y => a.powIdxOf? h y == some t.idx)
    let k := t.exp + (same.map (a.expOf h)).sum
    if same.isEmpty || k < powMin then none
    else
      match a.powBy h t.base k with
      | some x' => some (x', xs.filter (fun y => !(a.powIdxOf? h y == some t.idx)))
      | none => none

theorem groupPow_den (a : ArithOp) (h : a.hasPow = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (x : Opnd Δ Φ Γ a) (xs : List (Opnd Δ Φ Γ a)) (x' : Opnd Δ Φ Γ a)
    (rest : List (Opnd Δ Φ Γ a)) (hg : a.groupPow h x xs = some (x', rest)) :
    a.op (a.val x' κ ρ) (a.den rest κ ρ) = a.den (x :: xs) κ ρ := by
  unfold groupPow at hg
  split at hg
  · cases hg
  · rename_i t _
    simp only at hg
    split at hg
    · cases hg
    · split at hg
      · rename_i x'' hx''
        simp only [Option.some.injEq, Prod.mk.injEq] at hg
        obtain ⟨rfl, rfl⟩ := hg
        rw [powBy_val a h _ _ _ hx'', den_cons,
          den_filter a κ ρ (fun y => a.powIdxOf? h y == some t.idx) xs, ← op_assoc, t.eval,
          op_pow_den a h κ ρ (a.val t.base κ ρ) (a.expOf h) t.exp
            (xs.filter (fun y => a.powIdxOf? h y == some t.idx))]
        intro q hq
        simp only [List.mem_filter, beq_iff_eq] at hq
        exact val_of_powIdxOf a h κ ρ x t q hq.2
      · cases hg

end ArithOp

end LeanScript

end
