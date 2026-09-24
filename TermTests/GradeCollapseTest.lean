import LeanScript.Expr.Usage

set_option autoImplicit false

/-!
# Would a three-valued grade `0 | 1 | many` lose anything?

`LeanScript.Usage` counts uses with `Nat`.  The grammar only ever asks two questions
of a count: `Term.letE` asks `2 ≤ n` ("shared"), and `Term.nat_rec`/`Term.array_rec` ask
`0 < n` ("read at all").  The counts are built with `0`, `1`, `+`, `*` (`Usage.smul`,
`Usage.letU`) and `Usage.many = (2 * ·)`.

This file checks that collapsing a count to `0 | 1 | many` (`Grade.collapse n`, i.e.
`min n 2`) commutes with every one of those operations, and that both questions only
depend on the collapsed value.  So replacing `Nat` by the three-valued `Grade` below
accepts and rejects exactly the same terms: the distinction between `2` and `3`, … is
never used.

The file then shows:
* `three_values_needed`: the two questions already separate `0`, `1` and `2`, so no
  coarser grade works;
* `GExpr.indistinguishable`: counts that agree after collapsing give the same answers in
  every grade expression built from the grade operations (so a fourth value `2` would
  never be read);
* `join_vs_add`: adding the grades of branches is where precision is lost, and fixing it
  needs a join operation, not another value;
* the `GUsage` section: the same facts for the real grade vectors `LeanScript.Usage`,
  including `letE_hUsed_iff` and `hRec_iff`, which say that the proof arguments of
  `Term.letE` and `Term.nat_rec`/`Term.array_rec` read only the three-valued grades.
-/

namespace GradeCollapse

/-- A use count up to "many": the usual `0 | 1 | ω` grade. -/
inductive Grade where
  | zero
  | one
  | many
  deriving DecidableEq, Repr

namespace Grade

/-- Addition: the uses of two subterms. -/
def add : Grade → Grade → Grade
  | zero, g | g, zero => g
  | _, _ => many

/-- Multiplication: the uses of a subterm copied `k` times (`Usage.smul`, `Usage.letU`). -/
def mul : Grade → Grade → Grade
  | zero, _ | _, zero => zero
  | one, g | g, one => g
  | _, _ => many

/-- A use under a binder that may run many times (`Usage.many`). -/
def under : Grade → Grade
  | zero => zero
  | _ => many

/-- Collapse a count: `0 ↦ zero`, `1 ↦ one`, `≥ 2 ↦ many`. -/
def collapse (n : Nat) : Grade :=
  if n = 0 then zero else if n = 1 then one else many

/-- The question `Term.letE` asks. -/
def isShared : Grade → Bool
  | many => true
  | _ => false

/-- The question `Term.nat_rec` / `Term.array_rec` ask. -/
def isUsed : Grade → Bool
  | zero => false
  | _ => true

theorem collapse_add (m n : Nat) : collapse (m + n) = add (collapse m) (collapse n) := by
  unfold collapse
  by_cases hm0 : m = 0 <;> by_cases hm1 : m = 1 <;> by_cases hn0 : n = 0 <;>
    by_cases hn1 : n = 1 <;> simp_all [add]
  omega

theorem collapse_mul (m n : Nat) : collapse (m * n) = mul (collapse m) (collapse n) := by
  unfold collapse
  by_cases hm0 : m = 0 <;> by_cases hm1 : m = 1 <;> by_cases hn0 : n = 0 <;>
    by_cases hn1 : n = 1 <;> simp_all [mul]
  have h0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
  have h1 : m * n ≠ 1 := fun h => hm1 (Nat.eq_one_of_mul_eq_one_right h)
  simp [h0, h1]

theorem collapse_many (n : Nat) : collapse (2 * n) = under (collapse n) := by
  unfold collapse
  by_cases hn0 : n = 0
  · simp [hn0, under]
  · have h0 : 2 * n ≠ 0 := by omega
    have h1 : 2 * n ≠ 1 := by omega
    by_cases hn1 : n = 1 <;> simp [under, hn0, hn1, h0, h1]

theorem shared_iff (n : Nat) : 2 ≤ n ↔ isShared (collapse n) = true := by
  unfold collapse
  by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;> simp [isShared, hn0, hn1]
  omega

theorem used_iff (n : Nat) : 0 < n ↔ isUsed (collapse n) = true := by
  unfold collapse
  by_cases hn0 : n = 0 <;> by_cases hn1 : n = 1 <;> simp [isUsed, hn0, hn1]
  omega

/-- The graded `let` rule `smul (head v) u + tail v`, pointwise, commutes with the
    collapse too. -/
theorem collapse_letU (hv u tv : Nat) :
    collapse (hv * u + tv) = add (mul (collapse hv) (collapse u)) (collapse tv) := by
  rw [collapse_add, collapse_mul]


/-! ## Three values are also *needed*

The two questions already separate `0`, `1` and `2`: any abstraction of counts from which
both answers can still be read must keep these three apart.  So `0 | 1 | many` is the
coarsest grade that works — and, by the section above, it is fine enough. -/

theorem three_values_needed {α : Type} (f : Nat → α) (P Q : α → Prop)
    (hP : ∀ n, 2 ≤ n ↔ P (f n)) (hQ : ∀ n, 0 < n ↔ Q (f n)) :
    f 0 ≠ f 1 ∧ f 1 ≠ f 2 ∧ f 0 ≠ f 2 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (hQ 1).mp (by decide); rw [← h] at this; exact absurd ((hQ 0).mpr this) (by decide)
  · have := (hP 2).mp (by decide); rw [← h] at this; exact absurd ((hP 1).mpr this) (by decide)
  · have := (hQ 2).mp (by decide); rw [← h] at this; exact absurd ((hQ 0).mpr this) (by decide)

/-! ## A separate `2` is never observable

A grade expression: what the constructors of `LeanScript.Term` compute a grade with —
variables (grades of subterms), literals (`single`, the grade `k` of `Usage.cons`), `+`,
`*` (`Usage.smul`, `Usage.letU`) and `Usage.many`.  Two assignments of counts to the
variables that agree after collapsing give the same answer to both questions, whatever
the expression.  In particular `2` and `3` (or any two counts `≥ 2`) are interchangeable
everywhere: a four-valued `0 | 1 | 2 | many` would carry information nobody reads. -/

/-- A grade expression over variables `0, 1, …`. -/
inductive GExpr where
  | var (i : Nat)
  | lit (n : Nat)
  | add (a b : GExpr)
  | mul (a b : GExpr)
  | many (a : GExpr)

namespace GExpr

/-- The count an expression computes. -/
def eval (ρ : Nat → Nat) : GExpr → Nat
  | var i => ρ i
  | lit n => n
  | add a b => eval ρ a + eval ρ b
  | mul a b => eval ρ a * eval ρ b
  | many a => 2 * eval ρ a

/-- The three-valued grade the same expression computes. -/
def evalG (ρ : Nat → Grade) : GExpr → Grade
  | var i => ρ i
  | lit n => collapse n
  | add a b => Grade.add (evalG ρ a) (evalG ρ b)
  | mul a b => Grade.mul (evalG ρ a) (evalG ρ b)
  | many a => under (evalG ρ a)

/-- Computing with counts and collapsing agrees with computing with grades. -/
theorem collapse_eval (ρ : Nat → Nat) (e : GExpr) :
    collapse (e.eval ρ) = e.evalG (fun i => collapse (ρ i)) := by
  induction e with
  | var i => rfl
  | lit n => rfl
  | add a b iha ihb => simp only [eval, evalG, collapse_add, iha, ihb]
  | mul a b iha ihb => simp only [eval, evalG, collapse_mul, iha, ihb]
  | many a ih => simp only [eval, evalG, collapse_many, ih]

/-- Counts that agree after collapsing are indistinguishable by both questions, in every
    grade expression. -/
theorem indistinguishable (ρ ρ' : Nat → Nat) (h : ∀ i, collapse (ρ i) = collapse (ρ' i))
    (e : GExpr) :
    (2 ≤ e.eval ρ ↔ 2 ≤ e.eval ρ') ∧ (0 < e.eval ρ ↔ 0 < e.eval ρ') := by
  have he : collapse (e.eval ρ) = collapse (e.eval ρ') := by
    rw [collapse_eval, collapse_eval]; simp only [h]
  rw [shared_iff, shared_iff (e.eval ρ'), used_iff, used_iff (e.eval ρ'), he]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- `2` and `3` are interchangeable in every grade expression. -/
theorem two_three_indistinguishable (e : GExpr) :
    (2 ≤ e.eval (fun _ => 2) ↔ 2 ≤ e.eval (fun _ => 3)) ∧
      (0 < e.eval (fun _ => 2) ↔ 0 < e.eval (fun _ => 3)) :=
  indistinguishable (fun _ => 2) (fun _ => 3) (fun _ => rfl) e

end GExpr

/-! ## Adding branches over-approximates

A dispatch adds the grades of its branches, so `if c then x else x` counts `x` as
`many`, although only one branch runs.  Telling "once in each branch" apart from
"twice" needs a different operation — a join — not a fourth value. -/

/-- The grade of a use in one of two branches exactly one of which runs. -/
def join : Grade → Grade → Grade
  | zero, g => g
  | g, zero => g
  | one, one => one
  | _, _ => many

example : Grade.add one one = many := rfl
example : join one one = one := rfl
/-- A join differs from a sum only by answering `one` where the sum answers `many`. -/
theorem join_vs_add (a b : Grade) : join a b = add a b ∨ (join a b = one ∧ add a b = many) := by
  cases a <;> cases b <;> simp [join, add]

end Grade

/-! ## The same, for the grade vectors of `LeanScript.Usage` -/

open LeanScript

/-- A grade vector of three-valued grades. -/
def GUsage (Γ : Ctx) : Type := (τ : TyWf) → Var Γ τ → Grade

namespace GUsage

open Grade

variable {Γ : Ctx} {σ : TyWf}

/-- Collapse every count of a grade vector. -/
def ofUsage (u : Usage Γ) : GUsage Γ := fun τ x => collapse (u τ x)

/-- The three-valued version of `Usage.sumN`: the grade with which a fold's branch reads
    the `n` answers it is given. -/
def sumN (τ : TyWf) : (n : Nat) → GUsage (natRecCtx τ n Γ) → Grade
  | 0, _ => .zero
  | n + 1, g => Grade.add (g τ Var.head) (sumN τ n (fun τ' x => g τ' x.tail))

theorem ofUsage_zero (τ : TyWf) (x : Var Γ τ) : ofUsage (0 : Usage Γ) τ x = .zero := rfl

theorem ofUsage_add (u v : Usage Γ) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (u + v) τ x = Grade.add (ofUsage u τ x) (ofUsage v τ x) :=
  collapse_add _ _

theorem ofUsage_smul (k : Nat) (u : Usage Γ) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (Usage.smul k u) τ x = Grade.mul (collapse k) (ofUsage u τ x) :=
  collapse_mul _ _

theorem ofUsage_many (u : Usage Γ) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (Usage.many u) τ x = under (ofUsage u τ x) :=
  collapse_many _

theorem ofUsage_cons_head (k : Nat) (u : Usage Γ) :
    ofUsage (Usage.cons (σ := σ) k u) σ Var.head = collapse k := rfl

theorem ofUsage_cons_tail (k : Nat) (u : Usage Γ) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (Usage.cons (σ := σ) k u) τ x.tail = ofUsage u τ x := rfl

theorem ofUsage_tail (u : Usage (σ :: Γ)) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (Usage.tail u) τ x = ofUsage u τ x.tail := rfl

theorem ofUsage_letU (u : Usage Γ) (v : Usage (σ :: Γ)) (τ : TyWf) (x : Var Γ τ) :
    ofUsage (Usage.letU u v) τ x =
      Grade.add (Grade.mul (ofUsage v σ Var.head) (ofUsage u τ x)) (ofUsage v τ x.tail) :=
  collapse_letU _ _ _

/-- A single occurrence is never `many`. -/
theorem single_le_one : {Γ : Ctx} → {τ : TyWf} → (x : Var Γ τ) → (ρ : TyWf) →
    (y : Var Γ ρ) → Usage.single x ρ y ≤ 1
  | _ :: _, _, .head, _, .head => Nat.le_refl _
  | _ :: _, _, .head, _, .tail _ => Nat.zero_le _
  | _ :: _, _, .tail _, _, .head => Nat.zero_le _
  | _ :: _, _, .tail x, _, .tail y => single_le_one x _ y

theorem ofUsage_single_ne_many {τ : TyWf} (x : Var Γ τ) (ρ : TyWf) (y : Var Γ ρ) :
    ofUsage (Usage.single x) ρ y ≠ .many := by
  have := single_le_one x ρ y
  unfold ofUsage collapse
  by_cases h0 : Usage.single x ρ y = 0
  · simp [h0]
  · have h1 : Usage.single x ρ y = 1 := by omega
    simp [h1]

/-- `hUsed` of `Term.letE` reads only the three-valued grade. -/
theorem letE_hUsed_iff (v : Usage (σ :: Γ)) :
    2 ≤ Usage.head v ↔ isShared (ofUsage v σ Var.head) = true :=
  shared_iff _

/-- `Usage.sumN`, collapsed, is the three-valued `sumN` of the collapsed vector. -/
theorem ofUsage_sumN (τ : TyWf) :
    (n : Nat) → (w : Usage (natRecCtx τ n Γ)) → collapse (Usage.sumN τ n w) = sumN τ n (ofUsage w)
  | 0, _ => rfl
  | n + 1, w => by
      show collapse (Usage.head w + Usage.sumN τ n (Usage.tail w)) = _
      rw [collapse_add, ofUsage_sumN τ n (Usage.tail w)]
      rfl

/-- `hRec` of `Term.nat_rec` / `Term.array_rec` reads only the three-valued grades. -/
theorem hRec_iff (τ : TyWf) (n : Nat) (w : Usage (natRecCtx τ n Γ)) :
    0 < Usage.sumN τ n w ↔ isUsed (sumN τ n (ofUsage w)) = true := by
  rw [used_iff, ofUsage_sumN]

end GUsage

end GradeCollapse
