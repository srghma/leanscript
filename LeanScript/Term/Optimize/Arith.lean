module

public import LeanScript.Term.Optimize.ArithPow
public import LeanScript.Term.Optimize.FloatUnit
public import LeanScript.Term.Optimize.FloatComm

@[expose] public section

set_option autoImplicit false

/-!
# Chains of additions and multiplications

`Term.arithWalk` normalises every chain of additions, and every chain of multiplications, of
integers (`Int`, `Nat`, `UInt8`–`UInt64`, `Int8`–`Int64`).  Each of these operations is
associative and commutative with a unit (for the fixed-width types: modulo `2ⁿ`), so the
operands of a chain can be regrouped and reordered freely:

* the **literals are folded** into one, which is dropped when it is the unit (`0` for `+`,
  `1` for `*`);
* in a sum, the **copies of an unknown are counted**: the operands `x` and `x * c` (a product
  by a literal) of the same unknown `x`, wherever they stand in the chain, become one operand
  `x * k` (`k` the sum of their literals, `1` for `x` alone; `x` itself when `k = 1`);
* in a product of `Int`s or of `Nat`s, the **copies of an unknown are counted** as well: the
  operands `x` and `x ^ k` (a power by a literal, `lean_int_pow`/`lean_nat_pow`) of the same
  unknown become one operand `x ^ k`, when that is three copies or more (`x * x` stays;
  `ArithOp.groupPow` in `LeanScript.Term.Optimize.ArithPow`);
* the operands are then **combined from the left**, open operands first and the folded literal
  last: `1 + (((((2 + x) + x) + x) + x) + 3) + 4` is `x * 4 + 10`, and
  `1 * (2 * (x * (x * (x * (x * 3))))) * 4` is `x ^ 4 * 24` (`x ** 4n * 24n` in JavaScript).

The chain is read into its operands (`ArithOp.flat`), put in order (`ArithOp.arrange`: the
literals folded by `ArithOp.lits`, the unknowns counted by `ArithOp.group`) and combined again
(`ArithOp.build`); the result replaces the chain when it is still a neutral expression of the
same level (`ArithOp.normNeu`), decided on the spot.  The walk is bottom-up, so an inner chain
is normalised before the chain around it; counting `x * c` like `c` copies of `x` makes the
result the same as if the whole chain had been read at once (and so does counting `x ^ k` like
`k` copies in a product).

Proved: the value is unchanged (`Term.arithWalk_eval`), and no call is added
(`Term.numCalls_arithWalk`: only pure expressions change).  In JavaScript a `number` model of
`Int`/`Nat` (the `pbo` preset) checks every operation for overflow; regrouping can change which
intermediate result overflows (not the value when none does).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks}

namespace ArithOp

variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- A product by a literal, `x * c`, with the fact that it is one. -/
structure MulLit (a : ArithOp) {o : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o) where
  o' : Lvl
  x : PExpr Δ Φ Γ (.prim a.prim) o'
  c : a.D
  eval : ∀ κ ρ, e.eval κ ρ = a.mul (x.eval κ ρ) c

theorem mulLit_eval (a : ArithOp) {o o₁ o₂ : Lvl} (e : PExpr Δ Φ Γ (.prim a.prim) o)
    (x : PExpr Δ Φ Γ (.prim a.prim) o₁) (y : PExpr Δ Φ Γ (.prim a.prim) o₂)
    (hxy : ∀ κ ρ, e.eval κ ρ = a.mul (x.eval κ ρ) (y.eval κ ρ)) (c : a.D)
    (hy : a.litVal? y = some c) : ∀ κ ρ, e.eval κ ρ = a.mul (x.eval κ ρ) c :=
  fun κ ρ => by rw [hxy, a.litVal?_eval y c hy]

/-- The operand and the literal, when a pure expression is a product by a literal (in the type
    of an addition). -/
def mulView : (a : ArithOp) → {o : Lvl} → (e : PExpr Δ Φ Γ (.prim a.prim) o) →
    Option (a.MulLit e)
  | .intAdd, _, .neu (.extern (.intBasicExtern .lean_int_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .intAdd y with
      | some c => some ⟨_, x, c, mulLit_eval .intAdd _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .natAdd, _, .neu (.extern (.preludeExtern .lean_nat_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .natAdd y with
      | some c => some ⟨_, x, c, mulLit_eval .natAdd _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .uint8Add, _, .neu (.extern (.uint8BasicExtern .lean_uint8_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .uint8Add y with
      | some c => some ⟨_, x, c, mulLit_eval .uint8Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .uint16Add, _, .neu (.extern (.uint16BasicExtern .lean_uint16_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .uint16Add y with
      | some c => some ⟨_, x, c, mulLit_eval .uint16Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .uint32Add, _, .neu (.extern (.uint32BasicExtern .lean_uint32_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .uint32Add y with
      | some c => some ⟨_, x, c, mulLit_eval .uint32Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .uint64Add, _, .neu (.extern (.uint64BasicExtern .lean_uint64_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .uint64Add y with
      | some c => some ⟨_, x, c, mulLit_eval .uint64Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .int8Add, _, .neu (.extern (.int8BasicExtern .lean_int8_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .int8Add y with
      | some c => some ⟨_, x, c, mulLit_eval .int8Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .int16Add, _, .neu (.extern (.int16BasicExtern .lean_int16_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .int16Add y with
      | some c => some ⟨_, x, c, mulLit_eval .int16Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .int32Add, _, .neu (.extern (.int32BasicExtern .lean_int32_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .int32Add y with
      | some c => some ⟨_, x, c, mulLit_eval .int32Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | .int64Add, _, .neu (.extern (.int64BasicExtern .lean_int64_mul) (.cons x (.cons y .nil)) _) =>
      match hy : ArithOp.litVal? .int64Add y with
      | some c => some ⟨_, x, c, mulLit_eval .int64Add _ x y (fun _ _ => rfl) c hy⟩
      | none => none
  | _, _, _ => none

/-- An operand of a sum that is an unknown `x`, or a product `x * c` of an unknown by a literal:
    the position of the unknown, the unknown and the literal (`1` for `x` alone). -/
structure VarTerm (a : ArithOp) (p : Opnd Δ Φ Γ a) where
  idx : Nat
  base : Opnd Δ Φ Γ a
  coef : a.D
  base_idx : a.varIdx? base = some idx
  eval : ∀ κ ρ, a.val p κ ρ = a.mul (a.val base κ ρ) coef

/-- The unknown and its literal, when an operand of a sum is `x` or `x * c`. -/
def varTerm? (a : ArithOp) (h : a.isAdd = true) (p : Opnd Δ Φ Γ a) : Option (a.VarTerm p) :=
  match hv : a.varIdx? p with
  | some i => some ⟨i, p, a.one, hv, fun _ _ => (a.mul_one h _).symm⟩
  | none =>
    match a.mulView p.2 with
    | some m =>
      match hb : a.varIdx? ⟨_, m.x⟩ with
      | some i => some ⟨i, ⟨_, m.x⟩, m.c, hb, fun κ ρ => m.eval κ ρ⟩
      | none => none
    | none => none

/-- The position of the unknown of an operand of a sum that is `x` or `x * c`. -/
def idxOf? (a : ArithOp) (h : a.isAdd = true) (p : Opnd Δ Φ Γ a) : Option Nat :=
  (a.varTerm? h p).map (·.idx)

/-- The literal of an operand of a sum that is `x * c` (`1` for `x`). -/
def coefOf (a : ArithOp) (h : a.isAdd = true) (p : Opnd Δ Φ Γ a) : a.D :=
  match a.varTerm? h p with
  | some t => t.coef
  | none => a.one

/-- Every operand of the same unknown as a first one has the value of that unknown times its
    literal. -/
theorem val_of_idxOf (a : ArithOp) (h : a.isAdd = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (x : Opnd Δ Φ Γ a) (t : a.VarTerm x) (q : Opnd Δ Φ Γ a) (hq : a.idxOf? h q = some t.idx) :
    a.val q κ ρ = a.mul (a.val t.base κ ρ) (a.coefOf h q) := by
  unfold idxOf? at hq
  unfold coefOf
  cases hv : a.varTerm? h q with
  | none => rw [hv] at hq; cases hq
  | some tq =>
    rw [hv] at hq
    have hi : tq.idx = t.idx := Option.some.inj hq
    simp only
    rw [tq.eval, varIdx?_eval a κ ρ tq.base t.base t.idx (hi ▸ tq.base_idx) t.base_idx]

/-- `c + d₁ + … + dₙ`, combined from the right. -/
def csum (a : ArithOp) : a.D → List a.D → a.D
  | c, [] => c
  | c, d :: ds => a.op c (a.csum d ds)

/-- `x * c + (x * d₁ + (… + unit))` is `x * (c + d₁ + … + dₙ)`. -/
theorem op_mul_den (a : ArithOp) (h : a.isAdd = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : a.D)
    (f : Opnd Δ Φ Γ a → a.D) : (c : a.D) → (qs : List (Opnd Δ Φ Γ a)) →
    (∀ q ∈ qs, a.val q κ ρ = a.mul v (f q)) →
    a.op (a.mul v c) (a.den qs κ ρ) = a.mul v (a.csum c (qs.map f))
  | c, [], _ => by simp [op_unit, csum]
  | c, q :: qs, hq => by
    rw [den_cons, hq q (List.mem_cons_self), op_mul_den a h κ ρ v f (f q) qs
      (fun q' h' => hq q' (List.mem_cons_of_mem _ h')), List.map_cons, csum, mul_op a h]

/-- `x * c` (`x` when `c` is `1`), where `x` is an unknown. -/
def scaleBy (a : ArithOp) (x : Opnd Δ Φ Γ a) (c : a.D) : Option (Opnd Δ Φ Γ a) :=
  if @decide (c = a.one) (a.decEq c a.one) then some x
  else
    match h : Lvl.meet x.1 none with
    | some ℓ => some ⟨some ℓ, call a.mulExt x.2 (.lit a.prim c) h⟩
    | none => none

theorem scaleBy_val (a : ArithOp) (hadd : a.isAdd = true) (x : Opnd Δ Φ Γ a) (c : a.D)
    (x' : Opnd Δ Φ Γ a) (h : a.scaleBy x c = some x') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    a.val x' κ ρ = a.mul (a.val x κ ρ) c := by
  unfold scaleBy at h
  split at h
  · rename_i hc
    cases h
    rw [@of_decide_eq_true _ (a.decEq c a.one) hc, mul_one a hadd]
  · split at h
    · cases h
      simp only [val]
      rw [call_mulExt_eval a hadd]
      rfl
    · cases h

/-- In a sum, the operands `x`, `x * c₁`, …, `x * cₙ` of the same unknown `x` (`n ≥ 2`) are
    replaced by `x * (c₁ + … + cₙ)`, at the place of the first; in a product of `Int`s or
    `Nat`s, the operands `x`, `x ^ k₁`, …, `x ^ kₙ` by `x ^ (k₁ + … + kₙ)` (`ArithOp.groupPow`,
    at least `ArithOp.powMin` copies).  At most `n` operands are looked at. -/
def group (a : ArithOp) : Nat → List (Opnd Δ Φ Γ a) → List (Opnd Δ Φ Γ a)
  | 0, xs => xs
  | _ + 1, [] => []
  | n + 1, x :: xs =>
    if h : a.isAdd = true then
      match a.varTerm? h x with
      | none => x :: group a n xs
      | some t =>
        let same := xs.filter (fun y => a.idxOf? h y == some t.idx)
        if same.isEmpty then x :: group a n xs
        else
          match a.scaleBy t.base (a.csum t.coef (same.map (a.coefOf h))) with
          | some x' => x' :: group a n (xs.filter (fun y => !(a.idxOf? h y == some t.idx)))
          | none => x :: group a n xs
    else if hp : a.hasPow = true then
      match a.groupPow hp x xs with
      | some (x', rest) => x' :: group a n rest
      | none => x :: group a n xs
    else x :: xs

theorem group_den (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (n : Nat) → (xs : List (Opnd Δ Φ Γ a)) → a.den (a.group n xs) κ ρ = a.den xs κ ρ
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => by
    unfold group
    split
    · rename_i hadd
      split
      · rw [den_cons, den_cons, group_den a κ ρ n xs]
      · rename_i t _
        simp only
        split
        · rw [den_cons, den_cons, group_den a κ ρ n xs]
        · split
          · rename_i x' hx'
            rw [den_cons, group_den a κ ρ n, scaleBy_val a hadd _ _ x' hx', den_cons,
              den_filter a κ ρ (fun y => a.idxOf? hadd y == some t.idx) xs, ← op_assoc, t.eval,
              op_mul_den a hadd κ ρ (a.val t.base κ ρ) (a.coefOf hadd) t.coef
                (xs.filter (fun y => a.idxOf? hadd y == some t.idx))]
            intro q hq
            simp only [List.mem_filter, beq_iff_eq] at hq
            exact val_of_idxOf a hadd κ ρ x t q hq.2
          · rw [den_cons, den_cons, group_den a κ ρ n xs]
    · split
      · rename_i hp
        split
        · rename_i x' rest hg
          rw [den_cons, group_den a κ ρ n rest, groupPow_den a hp κ ρ x xs x' rest hg]
        · rw [den_cons, den_cons, group_den a κ ρ n xs]
      · rfl

/-! ### Putting the chain together again -/

/-- The operands, literals folded into one (last, dropped when it is the unit), unknowns counted
    in a sum, and open operands first. -/
def arrange (a : ArithOp) (ops : List (Opnd Δ Φ Γ a)) : List (Opnd Δ Φ Γ a) :=
  let rest := a.group ops.length (ops.filter (fun p => !a.isLit p))
  let c := a.lits ops
  rest.filter (fun p => p.1.isSome) ++ rest.filter (fun p => !p.1.isSome) ++
    (if a.isUnit c then [] else [⟨none, .lit a.prim c⟩])

theorem arrange_den (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (ops : List (Opnd Δ Φ Γ a)) :
    a.den (a.arrange ops) κ ρ = a.den ops κ ρ := by
  unfold arrange
  simp only
  rw [den_append, den_append, ← den_filter, group_den,
    den_filter a κ ρ a.isLit ops, den_filter_isLit, op_comm a (a.lits ops)]
  congr 1
  split
  · rename_i h
    rw [den_nil, eq_unit_of_isUnit a _ h]
  · simp only [den_cons, den_nil, val]; exact a.op_unit _

/-- `x ∘ r`, when one at least is open. -/
def mkOp (a : ArithOp) (x r : Opnd Δ Φ Γ a) : Option (Opnd Δ Φ Γ a) :=
  match h : Lvl.meet x.1 r.1 with
  | some ℓ => some ⟨some ℓ, call a.ext x.2 r.2 h⟩
  | none => none

theorem mkOp_val (a : ArithOp) (x r p : Opnd Δ Φ Γ a) (h : a.mkOp x r = some p)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.val p κ ρ = a.op (a.val x κ ρ) (a.val r κ ρ) := by
  unfold mkOp at h
  split at h
  · rename_i ℓ hh
    cases h; exact call_ext_eval a _ _ hh κ ρ
  · cases h

/-- `((acc ∘ c₁) ∘ c₂) ∘ … ∘ cₙ`. -/
def foldOp (a : ArithOp) : Opnd Δ Φ Γ a → List (Opnd Δ Φ Γ a) → Option (Opnd Δ Φ Γ a)
  | acc, [] => some acc
  | acc, c :: cs =>
    match a.mkOp acc c with
    | some acc' => foldOp a acc' cs
    | none => none

theorem foldOp_val (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (acc : Opnd Δ Φ Γ a) → (cs : List (Opnd Δ Φ Γ a)) → (p : Opnd Δ Φ Γ a) →
    a.foldOp acc cs = some p → a.val p κ ρ = a.op (a.val acc κ ρ) (a.den cs κ ρ)
  | acc, [], p, h => by
    simp only [foldOp, Option.some.injEq] at h; subst h; simp [op_unit]
  | acc, c :: cs, p, h => by
    simp only [foldOp] at h
    split at h
    · rename_i acc' hm
      rw [foldOp_val a κ ρ acc' cs p h, mkOp_val a acc c acc' hm, den_cons, op_assoc]
    · cases h

/-- The operands combined from the left. -/
def build (a : ArithOp) : List (Opnd Δ Φ Γ a) → Option (Opnd Δ Φ Γ a)
  | [] => none
  | x :: xs => a.foldOp x xs

theorem build_val (a : ArithOp) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (ops : List (Opnd Δ Φ Γ a))
    (p : Opnd Δ Φ Γ a) (h : a.build ops = some p) : a.val p κ ρ = a.den ops κ ρ := by
  cases ops with
  | nil => cases h
  | cons x xs => exact foldOp_val a κ ρ x xs p h

/-- How deep a chain is taken apart. -/
def flatFuel : Nat := 256

/-- **A chain normalised** (`ArithOp.arrange`, then `ArithOp.build`), when the result is still
    a neutral expression of the same level (otherwise the expression is kept). -/
def normNeu (a : ArithOp) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim a.prim) ℓ) :
    Neu Δ Φ Γ (.prim a.prim) ℓ :=
  match a.build (a.arrange (a.flat flatFuel (.neu n))) with
  | some ⟨o, p⟩ =>
    if h : o = some ℓ then
      match PExpr.asNeu? (h ▸ p) with
      | some m => m.1
      | none => n
    else n
  | none => n

theorem normNeu_eval (a : ArithOp) {ℓ : Nat} (n : Neu Δ Φ Γ (.prim a.prim) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (a.normNeu n).eval κ ρ = n.eval κ ρ := by
  unfold normNeu
  split
  · rename_i o p hb
    split
    · rename_i h
      split
      · rename_i m _
        rw [m.2]
        have e1 := build_val a κ ρ _ _ hb
        rw [arrange_den, flat_den] at e1
        subst h
        exact e1
      · rfl
    · rfl
  · rfl

end ArithOp

namespace ArithOp

/-- Every operation, the addition of each type before its multiplication. -/
def all : List ArithOp :=
  [.intAdd, .intMul, .natAdd, .natMul, .uint8Add, .uint8Mul, .uint16Add, .uint16Mul,
    .uint32Add, .uint32Mul, .uint64Add, .uint64Mul, .int8Add, .int8Mul, .int16Add, .int16Mul,
    .int32Add, .int32Mul, .int64Add, .int64Mul]

/-- `ArithOp.normNeu` on a neutral expression of a leaf type, when it is the type of the
    operation (otherwise the expression is kept). -/
def normAt (a : ArithOp) {Φ : KCtx ks} {Γ : UCtx ks} (p : LeanPrimTy) {ℓ : Nat}
    (n : Neu Δ Φ Γ (.prim p) ℓ) : Neu Δ Φ Γ (.prim p) ℓ :=
  if h : a.prim = p then h ▸ a.normNeu (h ▸ n) else n

theorem normAt_eval (a : ArithOp) {Φ : KCtx ks} {Γ : UCtx ks} (p : LeanPrimTy) {ℓ : Nat}
    (n : Neu Δ Φ Γ (.prim p) ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (a.normAt p n).eval κ ρ = n.eval κ ρ := by
  unfold normAt
  split
  · rename_i h
    subst h
    exact a.normNeu_eval n κ ρ
  · rfl

end ArithOp

/-- `ArithOp.normAt` of every operation, in turn (`ArithOp.all`), on a neutral expression of a
    leaf type: for an integer type, its sums, then its products; then, for a float type, a unit
    operand dropped (`Neu.floatUnit`: `x * 1.0` is `x`, …), and the operands of a `Float` `+`
    or `*` swapped when that saves parentheses in JavaScript (`Neu.floatComm`). -/
def Neu.normArithPrim {Φ : KCtx ks} {Γ : UCtx ks} (p : LeanPrimTy) {ℓ : Nat}
    (n : Neu Δ Φ Γ (.prim p) ℓ) : Neu Δ Φ Γ (.prim p) ℓ :=
  Neu.floatComm p (Neu.floatUnit p (ArithOp.all.foldl (fun n a => a.normAt p n) n))

theorem Neu.normArithPrim_eval {Φ : KCtx ks} {Γ : UCtx ks} (p : LeanPrimTy) {ℓ : Nat}
    (n : Neu Δ Φ Γ (.prim p) ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (Neu.normArithPrim p n).eval κ ρ = n.eval κ ρ := by
  unfold Neu.normArithPrim
  rw [Neu.floatComm_eval, Neu.floatUnit_eval]
  generalize ArithOp.all = as
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, ArithOp.normAt_eval]

/-- `Neu.normArithPrim` on a neutral expression of a leaf type. -/
def Neu.normArith {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | .prim p, _, n => Neu.normArithPrim p n
  | _, _, n => n

theorem Neu.normArith_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    n.normArith.eval κ ρ = n.eval κ ρ := by
  cases τ with
  | prim p => exact Neu.normArithPrim_eval p n κ ρ
  | _ => rfl

/-! ## The walk -/

mutual
/-- `Neu.normArith` at every extern call of a neutral expression, bottom-up. -/
def Neu.arithWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j e => .data_out b j e.arithWalk
  | _, _, .cond c a b => .cond c.arithWalk a.arithWalk b.arithWalk
  | _, _, .extern e args h => Neu.normArith (.extern e args.arithWalk h)
/-- `Neu.arithWalk` in a pure expression. -/
def PExpr.arithWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu n.arithWalk
  | _, _, .kvar k => .kvar k
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk args.arithWalk
  | _, _, .union_mk ix args => .union_mk ix args.arithWalk
  | _, _, .array_mk es => .array_mk es.arithWalk
  | _, _, .list_mk es => .list_mk es.arithWalk
  | _, _, .data_in b j e => .data_in b j e.arithWalk
/-- `Neu.arithWalk` in arguments. -/
def Args.arithWalk {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons a.arithWalk as.arithWalk
/-- `Neu.arithWalk` in the elements of a literal. -/
def Elems.arithWalk {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons e.arithWalk es.arithWalk
end

mutual
theorem Neu.arithWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    (n : Neu Δ Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → n.arithWalk.eval κ ρ = n.eval κ ρ
  | _, _, .var _, _, _ => rfl
  | _, _, .data_out b j e, κ, ρ => by
      simp only [Neu.arithWalk, Neu.eval, Neu.arithWalk_eval e]
  | _, _, .cond c a b, κ, ρ => by
      simp only [Neu.arithWalk, Neu.eval, Neu.arithWalk_eval c, PExpr.arithWalk_eval a,
        PExpr.arithWalk_eval b]
  | _, _, .extern e args _, κ, ρ => by
      simp only [Neu.arithWalk]
      rw [Neu.normArith_eval]
      simp only [Neu.eval, Args.arithWalk_eval args]
theorem PExpr.arithWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    (e : PExpr Δ Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → e.arithWalk.eval κ ρ = e.eval κ ρ
  | _, _, .neu n, κ, ρ => by simp only [PExpr.arithWalk, PExpr.eval, Neu.arithWalk_eval n]
  | _, _, .kvar _, _, _ => rfl
  | _, _, .lit _ _, _, _ => rfl
  | _, _, .enum_mk _ _, _, _ => rfl
  | _, _, .record_mk args, κ, ρ => by
      simp only [PExpr.arithWalk, PExpr.eval, Args.arithWalk_eval args] <;> rfl
  | _, _, .union_mk _ args, κ, ρ => by
      simp only [PExpr.arithWalk, PExpr.eval, Args.arithWalk_eval args] <;> rfl
  | _, _, .array_mk es, κ, ρ => by
      simp only [PExpr.arithWalk, PExpr.eval, Elems.arithWalk_eval es] <;> rfl
  | _, _, .list_mk es, κ, ρ => by
      simp only [PExpr.arithWalk, PExpr.eval, Elems.arithWalk_eval es] <;> rfl
  | _, _, .data_in _ _ e, κ, ρ => by
      simp only [PExpr.arithWalk, PExpr.eval, PExpr.arithWalk_eval e]
theorem Args.arithWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    (as : Args Δ Φ Γ σs o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → as.arithWalk.eval κ ρ = as.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons a as, κ, ρ => by
      simp only [Args.arithWalk, Args.eval, PExpr.arithWalk_eval a, Args.arithWalk_eval as]
theorem Elems.arithWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ Φ Γ t o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → es.arithWalk.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons e es, κ, ρ => by
      simp only [Elems.arithWalk, Elems.eval, PExpr.arithWalk_eval e, Elems.arithWalk_eval es] <;> rfl
end

mutual
/-- `Term.arithWalk` in a value. -/
def Val.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.arithWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.arithWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.arithWalk
  | _, _, _, _, _, .record_mk args => .record_mk args.arithWalk
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args.arithWalk
  | _, _, _, _, _, .array_mk es => .array_mk es.arithWalk
  | _, _, _, _, _, .list_mk es => .list_mk es.arithWalk
  | _, _, _, _, _, .data_in b j e => .data_in b j e.arithWalk
/-- `Term.arithWalk` in a body. -/
def Body.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.arithWalk
  | _, _, _, _, _, _, .opened t h => .opened t.arithWalk h
/-- `Term.arithWalk` in a computation. -/
def Comp.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f.arithWalk a.arithWalk h
  | _, _, _, _, _, .share n => .share n.arithWalk
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n.arithWalk z.arithWalk s.arithWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a.arithWalk z.arithWalk s.arithWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).arithWalk) j e.arithWalk h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).arithWalk) j e.arithWalk h
  | _, _, _, _, _, .thunk_force e => .thunk_force e.arithWalk
  | _, _, _, _, _, .lazy_force e => .lazy_force e.arithWalk
/-- **Chains of additions and multiplications normalised** everywhere in a statement
    (`Neu.normArith`), bottom-up. -/
def Term.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e.arithWalk
  | _, _, _, _, _, _, .letV u v b => .letV u v.arithWalk b.arithWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.arithWalk b.arithWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n.arithWalk b.arithWalk
  | _, _, _, _, _, _, .branch br => .branch br.arithWalk
  | _, _, _, _, _, _, .jump j e => .jump j e.arithWalk
/-- `Term.arithWalk` in a branch. -/
def Branch.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c.arithWalk t.arithWalk e.arithWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e.arithWalk (fun i => (bs i).arithWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e.arithWalk bs.arithWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.arithWalk main.arithWalk
/-- `Term.arithWalk` in the branches of a union's case analysis. -/
def Branches.arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.arithWalk b₂.arithWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.arithWalk bs.arithWalk
end

mutual
theorem Val.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.arithWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.arithWalk, Val.eval]; funext x; rw [Body.arithWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.arithWalk, Val.eval]; rw [Body.arithWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.arithWalk, Val.eval]; rw [Body.arithWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk args, κ, ρ => by
      simp only [Val.arithWalk, Val.eval, Args.arithWalk_eval args] <;> rfl
  | _, _, _, _, _, .union_mk _ args, κ, ρ => by
      simp only [Val.arithWalk, Val.eval, Args.arithWalk_eval args] <;> rfl
  | _, _, _, _, _, .array_mk es, κ, ρ => by
      simp only [Val.arithWalk, Val.eval, Elems.arithWalk_eval es] <;> rfl
  | _, _, _, _, _, .list_mk es, κ, ρ => by
      simp only [Val.arithWalk, Val.eval, Elems.arithWalk_eval es] <;> rfl
  | _, _, _, _, _, .data_in _ _ e, κ, ρ => by
      simp only [Val.arithWalk, Val.eval, PExpr.arithWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.arithWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.arithWalk, Body.eval]; exact Term.arithWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.arithWalk, Body.eval]; exact Term.arithWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.arithWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a _, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval f, PExpr.arithWalk_eval a]
  | _, _, _, _, _, .share n, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, Neu.arithWalk_eval n]
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval n, PExpr.arithWalk_eval z]
      congr 1; funext k acc; exact Body.arithWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval]
      rw [PExpr.arithWalk_eval a κ ρ, PExpr.arithWalk_eval z κ ρ]
      congr 1; funext acc x; exact Body.arithWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval e]
      congr 1; funext i x; exact Body.arithWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval e]
      congr 1; funext i x; exact Body.arithWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force e, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval e]
  | _, _, _, _, _, .lazy_force e, κ, ρ => by
      simp only [Comp.arithWalk, Comp.eval, PExpr.arithWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.arithWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, κ, ρ, _ => by
      simp only [Term.arithWalk, Term.eval, PExpr.arithWalk_eval e]
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.arithWalk, Term.eval, Val.arithWalk_eval v, Term.arithWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.arithWalk, Term.eval, Comp.arithWalk_eval c, Term.arithWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.arithWalk, Term.eval, Neu.arithWalk_eval n, Term.arithWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.arithWalk, Term.eval, Branch.arithWalk_eval br]
  | _, _, _, _, _, _, .jump _ e, κ, ρ, jκ => by
      simp only [Term.arithWalk, Term.eval, PExpr.arithWalk_eval e]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.arithWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.arithWalk, Branch.eval, Neu.arithWalk_eval c, Term.arithWalk_eval t,
        Term.arithWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.arithWalk, Branch.eval]; rw [Neu.arithWalk_eval e]
      exact Term.arithWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.arithWalk, Branch.eval, Neu.arithWalk_eval e]
      exact Branches.arithWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.arithWalk, Branch.eval, Branch.arithWalk_eval main, Term.arithWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.arithWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.arithWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.arithWalk, Branches.eval, Term.arithWalk_eval b₁, Term.arithWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.arithWalk, Branches.eval, Term.arithWalk_eval b,
        Branches.arithWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.arithWalk.numCalls = v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.arithWalk, Val.numCalls, Body.numCalls_arithWalk b]
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.arithWalk, Val.numCalls, Body.numCalls_arithWalk b]
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.arithWalk, Val.numCalls, Body.numCalls_arithWalk b]
  | _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.arithWalk.numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.arithWalk, Body.numCalls, Term.numCalls_arithWalk t]
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.arithWalk, Body.numCalls, Term.numCalls_arithWalk t]
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.arithWalk.numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.arithWalk, Comp.numCalls, Body.numCalls_arithWalk s]
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.arithWalk, Comp.numCalls, Body.numCalls_arithWalk s]
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.arithWalk, Comp.numCalls, Body.numCalls_arithWalk]
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.arithWalk, Comp.numCalls, Body.numCalls_arithWalk]
  | _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.arithWalk.numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, .letV _ v b => by
      simp only [Term.arithWalk, Term.numCalls, Val.numCalls_arithWalk v, Term.numCalls_arithWalk b]
  | _, _, _, _, _, _, .letE _ c b => by
      simp only [Term.arithWalk, Term.numCalls, Comp.numCalls_arithWalk c, Term.numCalls_arithWalk b]
  | _, _, _, _, _, _, .record_casesOn _ _ b => by
      simp only [Term.arithWalk, Term.numCalls, Term.numCalls_arithWalk b]
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.arithWalk, Term.numCalls, Branch.numCalls_arithWalk br]
  | _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → br.arithWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.arithWalk, Branch.numCalls, Term.numCalls_arithWalk t,
        Term.numCalls_arithWalk e]
  | _, _, _, _, _, _, .enum_casesOn _ bs => by
      simp only [Branch.arithWalk, Branch.numCalls, Term.numCalls_arithWalk]
  | _, _, _, _, _, _, .union_casesOn _ bs => by
      simp only [Branch.arithWalk, Branch.numCalls, Branches.numCalls_arithWalk bs]
  | _, _, _, _, _, _, .join _ _ _ body main => by
      simp only [Branch.arithWalk, Branch.numCalls, Term.numCalls_arithWalk body,
        Branch.numCalls_arithWalk main]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_arithWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.arithWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => by
      simp only [Branches.arithWalk, Branches.numCalls, Term.numCalls_arithWalk b₁,
        Term.numCalls_arithWalk b₂]
  | _, _, _, _, _, _, _, _, .cons _ b bs => by
      simp only [Branches.arithWalk, Branches.numCalls, Term.numCalls_arithWalk b,
        Branches.numCalls_arithWalk bs]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
