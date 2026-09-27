import IntUInt53.BoundedInt64.Add
import IntUInt53.BoundedInt64.Sub
import IntUInt53.BoundedInt64.Mul
import IntUInt53.BoundedInt64.Div
import IntUInt53.BoundedInt64.Neg

/-!
# A machine-word implementation of the operations on `BoundedInt64`

As for `TopBoundedUInt64`, the operations are *specified* through `toInt`:
they convert to `Int`, compute there — exactly, with no bound — and convert
back.  This module gives each of them an implementation that stays inside
`Int64`, proves it equal to the specification and registers the equation with
`@[csimp]`, so that compiled code does machine arithmetic while the kernel
still sees the original definition.

One side condition appears, tested at run time on the *bounds* only:
`moderate lo hi` says that both bounds are at most `2 ^ 61 - 1` in absolute
value, which leaves enough head room in a 64-bit word for the sum, the
difference and the modular reduction to be computed without wrapping.  It holds
for `Int53`.  When it fails, the fast path falls back to the original `Int`
computation, so the equations below hold for *all* bounds.
-/

set_option autoImplicit false

open BoundedWordAux

namespace BoundedInt64

variable {lo hi : Int64}

/-! ### Machine arithmetic facts -/

/-- The machine sum is exact when it does not leave the 64-bit range. -/
theorem toInt_word_add {x y : Int64} (h₁ : -2 ^ 63 ≤ x.toInt + y.toInt)
    (h₂ : x.toInt + y.toInt < 2 ^ 63) : (x + y).toInt = x.toInt + y.toInt := by
  rw [Int64.toInt_add]; exact Int.bmod_eq_of_le h₁ h₂

/-- The machine difference is exact when it does not leave the 64-bit range. -/
theorem toInt_word_sub {x y : Int64} (h₁ : -2 ^ 63 ≤ x.toInt - y.toInt)
    (h₂ : x.toInt - y.toInt < 2 ^ 63) : (x - y).toInt = x.toInt - y.toInt := by
  rw [Int64.toInt_sub]; exact Int.bmod_eq_of_le h₁ h₂

/-- The machine product is exact when it does not leave the 64-bit range. -/
theorem toInt_word_mul {x y : Int64} (h₁ : -2 ^ 63 ≤ x.toInt * y.toInt)
    (h₂ : x.toInt * y.toInt < 2 ^ 63) : (x * y).toInt = x.toInt * y.toInt := by
  rw [Int64.toInt_mul]; exact Int.bmod_eq_of_le h₁ h₂

/-- The machine negation is exact when it does not leave the 64-bit range. -/
theorem toInt_word_neg {x : Int64} (h₁ : -2 ^ 63 ≤ -x.toInt) (h₂ : -x.toInt < 2 ^ 63) :
    (-x).toInt = -x.toInt := by
  rw [Int64.toInt_neg]; exact Int.bmod_eq_of_le h₁ h₂

/-- The machine quotient is exact when it does not leave the 64-bit range. -/
theorem toInt_word_div {x y : Int64} (h₁ : -2 ^ 63 ≤ x.toInt.tdiv y.toInt)
    (h₂ : x.toInt.tdiv y.toInt < 2 ^ 63) : (x / y).toInt = x.toInt.tdiv y.toInt := by
  rw [Int64.toInt_div]; exact Int.bmod_eq_of_le h₁ h₂

/-- Strict comparison of machine words is the negation of the reverse comparison. -/
theorem int64_lt_iff_not_le {x y : Int64} : x < y ↔ ¬ (y ≤ x) := by
  rw [int64_lt_iff, int64_le_iff]; omega

/-- Turning an overflow predicate into the conjunction of two machine comparisons. -/
theorem flag_eq {P Q₁ Q₂ : Prop} [Decidable P] [Decidable Q₁] [Decidable Q₂]
    (h : P ↔ (Q₁ ∧ Q₂)) : decide (¬ P) = !(decide Q₁ && decide Q₂) := by
  by_cases hq₁ : Q₁
  · by_cases hq₂ : Q₂
    · rw [decide_eq_false (not_not_intro (h.mpr ⟨hq₁, hq₂⟩)), decide_eq_true hq₁,
        decide_eq_true hq₂]
      rfl
    · have hnp : ¬ P := fun hp => hq₂ (h.mp hp).2
      rw [decide_eq_true hnp, decide_eq_false hq₂, decide_eq_true hq₁]
      rfl
  · have hnp : ¬ P := fun hp => hq₁ (h.mp hp).1
    rw [decide_eq_true hnp, decide_eq_false hq₁]
    rfl

/-- The machine remainder is always exact. -/
theorem toInt_word_mod (x y : Int64) : (x % y).toInt = x.toInt.tmod y.toInt :=
  Int64.toInt_mod x y

/-- The Euclidean remainder, expressed through the truncating one: this is what lets a
modular reduction be computed with the machine `%`. -/
theorem emod_of_tmod {d P : Int} (hP : 0 < P) :
    d % P = if d.tmod P < 0 then d.tmod P + P else d.tmod P := by
  have hd : d.tmod P + P * (d.tdiv P) = d := Int.tmod_add_mul_tdiv d P
  have hlt : d.tmod P < P := Int.tmod_lt_of_pos d hP
  have hnat : (d.tmod P).natAbs = d.natAbs % P.natAbs := Int.natAbs_tmod d P
  have hpnat : 0 < P.natAbs := by omega
  have hmod : d.natAbs % P.natAbs < P.natAbs := Nat.mod_lt _ hpnat
  have hgt : -P < d.tmod P := by omega
  have key : d % P = d.tmod P % P := by
    have h1 : d.tmod P % P = (d.tmod P + P * (d.tdiv P)) % P :=
      (Int.add_mul_emod_self_left _ _ _).symm
    rw [h1, hd]
  split
  · next h =>
    have h2 : (d.tmod P + P) % P = d.tmod P % P := by
      have h3 := Int.add_mul_emod_self_left (a := d.tmod P) (b := P) (c := 1)
      rwa [Int.mul_one] at h3
    rw [key, ← h2, Int.emod_eq_of_lt (by omega) (by omega)]
  · next h =>
    rw [key, Int.emod_eq_of_lt (by omega) hlt]

/-! ### The side condition -/

/-- Both bounds are at most `2 ^ 61 - 1` in absolute value. -/
def moderate (lo hi : Int64) : Bool :=
  -2305843009213693951 ≤ lo && hi ≤ 2305843009213693951

theorem moderate_iff {lo hi : Int64} :
    moderate lo hi = true ↔ (-(2 ^ 61 - 1) ≤ lo.toInt ∧ hi.toInt ≤ 2 ^ 61 - 1) := by
  have h₁ : (-2305843009213693951 : Int64).toInt = -(2 ^ 61 - 1) := by decide +kernel
  have h₂ : (2305843009213693951 : Int64).toInt = 2 ^ 61 - 1 := by decide +kernel
  unfold moderate
  simp only [Bool.and_eq_true, decide_eq_true_eq, int64_le_iff, h₁, h₂]

/-- Under the side condition every value of the type is at most `2 ^ 61 - 1` in
absolute value. -/
theorem toInt_bounds (hm : moderate lo hi = true) (a : BoundedInt64 lo hi) :
    -(2 ^ 61 - 1) ≤ a.toInt ∧ a.toInt ≤ 2 ^ 61 - 1 := by
  obtain ⟨h₁, h₂⟩ := moderate_iff.mp hm
  exact ⟨Int.le_trans h₁ (lo_le_toInt a), Int.le_trans (toInt_le_hi a) h₂⟩

/-! ### Building a value from a machine word -/

/-- The checked constructor from a machine word: no `Int` is involved. -/
def ofWord? (lo hi : Int64) (v : Int64) : Option (BoundedInt64 lo hi) :=
  if h₁ : lo ≤ v then (if h₂ : v ≤ hi then some ⟨v, h₁, h₂⟩ else none) else none

theorem ofWord?_eq (v : Int64) : ofWord? lo hi v = ofInt? lo hi v.toInt := by
  unfold ofWord? ofInt?
  by_cases h₁ : lo.toInt ≤ v.toInt
  · by_cases h₂ : v.toInt ≤ hi.toInt
    · rw [dite_eq_left (int64_le_iff.mpr h₁), dite_eq_left (int64_le_iff.mpr h₂), dite_eq_left ⟨h₁, h₂⟩]
      exact congrArg some (ext (by rw [toInt_ofIntMem]; rfl))
    · rw [dite_eq_left (int64_le_iff.mpr h₁), dite_eq_right (fun hc => h₂ (int64_le_iff.mp hc)),
        dite_eq_right (fun hc => h₂ hc.2)]
  · rw [dite_eq_right (fun hc => h₁ (int64_le_iff.mp hc)), dite_eq_right (fun hc => h₁ hc.1)]

/-- The saturating constructor from a machine word. -/
def ofWordSat (h : lo ≤ hi) (v : Int64) : BoundedInt64 lo hi :=
  if h₁ : v ≤ lo then minVal h
  else if h₂ : hi ≤ v then maxVal h
  else ⟨v,
    int64_le_iff.mpr (Int.le_of_lt (Int.not_le.mp fun hc => h₁ (int64_le_iff.mpr hc))),
    int64_le_iff.mpr (Int.le_of_lt (Int.not_le.mp fun hc => h₂ (int64_le_iff.mpr hc)))⟩

theorem toInt_ofWordSat (h : lo ≤ hi) (v : Int64) :
    (ofWordSat h v).toInt = max lo.toInt (min v.toInt hi.toInt) := by
  have hle : lo.toInt ≤ hi.toInt := int64_le_iff.mp h
  unfold ofWordSat
  by_cases h₁ : v.toInt ≤ lo.toInt
  · rw [dite_eq_left (int64_le_iff.mpr h₁), toInt_minVal]
    omega
  · rw [dite_eq_right (fun hc => h₁ (int64_le_iff.mp hc))]
    by_cases h₂ : hi.toInt ≤ v.toInt
    · rw [dite_eq_left (int64_le_iff.mpr h₂), toInt_maxVal]
      omega
    · rw [dite_eq_right (fun hc => h₂ (int64_le_iff.mp hc))]
      show v.toInt = _
      omega

theorem ofWordSat_eq (h : lo ≤ hi) (v : Int64) : ofWordSat h v = ofIntSat h v.toInt :=
  ext (by rw [toInt_ofWordSat, toInt_ofIntSat])

/-! ### The modular reduction, in a machine word -/

/-- Reduce a machine word into `[lo, hi]` modulo the period, using machine arithmetic
only. -/
def wrapWord (lo hi : Int64) (s : Int64) : Int64 :=
  let p := hi - lo + 1
  let t := (s - lo) % p
  lo + (if t < 0 then t + p else t)

theorem toInt_wrapWord (hm : moderate lo hi = true) (hle : lo ≤ hi) {s : Int64}
    (h₁ : -(2 ^ 62) ≤ s.toInt) (h₂ : s.toInt ≤ 2 ^ 62) :
    (wrapWord lo hi s).toInt = lo.toInt + (s.toInt - lo.toInt) % period lo hi := by
  obtain ⟨hlo, hhi⟩ := moderate_iff.mp hm
  have hlohi : lo.toInt ≤ hi.toInt := int64_le_iff.mp hle
  have hone : (1 : Int64).toInt = 1 := by decide +kernel
  have hzero : (0 : Int64).toInt = 0 := by decide +kernel
  have hperdef : period lo hi = hi.toInt - lo.toInt + 1 := rfl
  have hsub : (hi - lo : Int64).toInt = hi.toInt - lo.toInt :=
    toInt_word_sub (by omega) (by omega)
  have hp : (hi - lo + 1 : Int64).toInt = period lo hi := by
    rw [toInt_word_add (by rw [hsub, hone]; omega) (by rw [hsub, hone]; omega), hsub, hone,
      hperdef]
  have hppos : 0 < period lo hi := by omega
  have hpbound : period lo hi ≤ 2 ^ 62 := by omega
  have hd : (s - lo : Int64).toInt = s.toInt - lo.toInt := toInt_word_sub (by omega) (by omega)
  have ht : ((s - lo) % (hi - lo + 1) : Int64).toInt
      = (s.toInt - lo.toInt).tmod (period lo hi) := by
    rw [toInt_word_mod, hd, hp]
  have hqlt : (s.toInt - lo.toInt).tmod (period lo hi) < period lo hi :=
    Int.tmod_lt_of_pos _ hppos
  have hqnat : ((s.toInt - lo.toInt).tmod (period lo hi)).natAbs
      = (s.toInt - lo.toInt).natAbs % (period lo hi).natAbs := Int.natAbs_tmod _ _
  have hpnat : 0 < (period lo hi).natAbs := by omega
  have hqmod : (s.toInt - lo.toInt).natAbs % (period lo hi).natAbs < (period lo hi).natAbs :=
    Nat.mod_lt _ hpnat
  have hqgt : -(period lo hi) < (s.toInt - lo.toInt).tmod (period lo hi) := by omega
  have hadj : (if ((s - lo) % (hi - lo + 1) : Int64) < 0 then
        ((s - lo) % (hi - lo + 1) : Int64) + (hi - lo + 1) else
        ((s - lo) % (hi - lo + 1) : Int64)).toInt
      = (if (s.toInt - lo.toInt).tmod (period lo hi) < 0 then
          (s.toInt - lo.toInt).tmod (period lo hi) + period lo hi
        else (s.toInt - lo.toInt).tmod (period lo hi)) := by
    by_cases hneg : (s.toInt - lo.toInt).tmod (period lo hi) < 0
    · have hlt : ((s - lo) % (hi - lo + 1) : Int64) < 0 :=
        int64_lt_iff.mpr (by rw [ht, hzero]; omega)
      rw [ite_eq_left hlt, ite_eq_left hneg,
        toInt_word_add (by rw [ht, hp]; omega) (by rw [ht, hp]; omega), ht, hp]
    · have hnlt : ¬ ((s - lo) % (hi - lo + 1) : Int64) < 0 := by
        intro hc
        have hcc := int64_lt_iff.mp hc
        rw [ht, hzero] at hcc
        omega
      rw [ite_eq_right hnlt, ite_eq_right hneg, ht]
  show (lo + (if ((s - lo) % (hi - lo + 1) : Int64) < 0 then
      ((s - lo) % (hi - lo + 1) : Int64) + (hi - lo + 1) else
      ((s - lo) % (hi - lo + 1) : Int64))).toInt = _
  rw [toInt_word_add (by rw [hadj]; omega) (by rw [hadj]; omega), hadj,
    emod_of_tmod (d := s.toInt - lo.toInt) hppos]

theorem ofWordSat_wrapWord (hm : moderate lo hi = true) (hle : lo ≤ hi) {s : Int64}
    (h₁ : -(2 ^ 62) ≤ s.toInt) (h₂ : s.toInt ≤ 2 ^ 62) :
    ofWordSat hle (wrapWord lo hi s) = ofIntWrap hle s.toInt := by
  have hlohi : lo.toInt ≤ hi.toInt := int64_le_iff.mp hle
  have hppos : 0 < period lo hi := period_pos hle
  have hw := toInt_wrapWord hm hle h₁ h₂
  have hnn : 0 ≤ (s.toInt - lo.toInt) % period lo hi := Int.emod_nonneg _ (Int.ne_of_gt hppos)
  have hlt : (s.toInt - lo.toInt) % period lo hi < period lo hi := Int.emod_lt_of_pos _ hppos
  have hper : period lo hi = hi.toInt - lo.toInt + 1 := rfl
  apply ext
  rw [toInt_ofWordSat, toInt_ofIntWrap, hw]
  omega

/-! ### Addition -/

/-- Machine-word checked addition. -/
def checked_add_fast (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi then ofWord? lo hi (a.val + b.val) else ofInt? lo hi (exactAdd a b)

/-- The integer denoted by a value is the integer denoted by its underlying word. -/
theorem toInt_val (a : BoundedInt64 lo hi) : a.val.toInt = a.toInt := rfl

theorem toInt_val_add (hm : moderate lo hi = true) (a b : BoundedInt64 lo hi) :
    (a.val + b.val).toInt = a.toInt + b.toInt := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  obtain ⟨hb₁, hb₂⟩ := toInt_bounds hm b
  have hav := toInt_val a
  have hbv := toInt_val b
  exact toInt_word_add (by omega) (by omega)

@[csimp] theorem checked_add_eq_fast : @checked_add = @checked_add_fast := by
  funext lo hi a b
  unfold checked_add_fast
  split
  · next hm => rw [ofWord?_eq, toInt_val_add hm]; rfl
  · rfl

/-- Machine-word wrapping addition. -/
def wrapping_add_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (a.val + b.val))
  else ofIntWrap (lo_le_hi a) (exactAdd a b)

@[csimp] theorem wrapping_add_eq_fast : @wrapping_add = @wrapping_add_fast := by
  funext lo hi a b
  unfold wrapping_add_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    obtain ⟨hb₁, hb₂⟩ := toInt_bounds hm b
    have hs := toInt_val_add hm a b
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hs]; omega) (by rw [hs]; omega), hs]
    rfl
  · rfl

/-- Machine-word saturating addition. -/
def saturating_add_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (a.val + b.val)
  else ofIntSat (lo_le_hi a) (exactAdd a b)

@[csimp] theorem saturating_add_eq_fast : @saturating_add = @saturating_add_fast := by
  funext lo hi a b
  unfold saturating_add_fast
  split
  · next hm => rw [ofWordSat_eq, toInt_val_add hm]; rfl
  · rfl

/-- Machine-word overflowing addition. -/
def overflowing_add_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  if moderate lo hi then
    (wrapping_add_fast a b, !(lo ≤ a.val + b.val && a.val + b.val ≤ hi))
  else (wrapping_add a b, decide (¬ InRange lo hi (exactAdd a b)))

@[csimp] theorem overflowing_add_eq_fast : @overflowing_add = @overflowing_add_fast := by
  funext lo hi a b
  unfold overflowing_add_fast
  split
  · next hm =>
    have hs := toInt_val_add hm a b
    have hflag : decide (¬ InRange lo hi (exactAdd a b))
        = !(decide (lo ≤ a.val + b.val) && decide (a.val + b.val ≤ hi)) := by
      have hiff : InRange lo hi (exactAdd a b) ↔ (lo ≤ a.val + b.val ∧ a.val + b.val ≤ hi) := by
        show (lo.toInt ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ hi.toInt) ↔ _
        rw [int64_le_iff, int64_le_iff, hs]
      exact flag_eq hiff
    show (wrapping_add a b, decide (¬ InRange lo hi (exactAdd a b))) = _
    rw [hflag, congrFun (congrFun (congrFun (congrFun wrapping_add_eq_fast lo) hi) a) b]
  · rfl

/-! ### Subtraction -/

theorem toInt_val_sub (hm : moderate lo hi = true) (a b : BoundedInt64 lo hi) :
    (a.val - b.val).toInt = a.toInt - b.toInt := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  obtain ⟨hb₁, hb₂⟩ := toInt_bounds hm b
  have hav := toInt_val a
  have hbv := toInt_val b
  exact toInt_word_sub (by omega) (by omega)

/-- Machine-word checked subtraction. -/
def checked_sub_fast (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi then ofWord? lo hi (a.val - b.val) else ofInt? lo hi (exactSub a b)

@[csimp] theorem checked_sub_eq_fast : @checked_sub = @checked_sub_fast := by
  funext lo hi a b
  unfold checked_sub_fast
  split
  · next hm => rw [ofWord?_eq, toInt_val_sub hm]; rfl
  · rfl

/-- Machine-word wrapping subtraction. -/
def wrapping_sub_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (a.val - b.val))
  else ofIntWrap (lo_le_hi a) (exactSub a b)

@[csimp] theorem wrapping_sub_eq_fast : @wrapping_sub = @wrapping_sub_fast := by
  funext lo hi a b
  unfold wrapping_sub_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    obtain ⟨hb₁, hb₂⟩ := toInt_bounds hm b
    have hs := toInt_val_sub hm a b
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hs]; omega) (by rw [hs]; omega), hs]
    rfl
  · rfl

/-- Machine-word saturating subtraction. -/
def saturating_sub_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (a.val - b.val)
  else ofIntSat (lo_le_hi a) (exactSub a b)

@[csimp] theorem saturating_sub_eq_fast : @saturating_sub = @saturating_sub_fast := by
  funext lo hi a b
  unfold saturating_sub_fast
  split
  · next hm => rw [ofWordSat_eq, toInt_val_sub hm]; rfl
  · rfl

/-- Machine-word overflowing subtraction. -/
def overflowing_sub_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  if moderate lo hi then
    (wrapping_sub_fast a b, !(lo ≤ a.val - b.val && a.val - b.val ≤ hi))
  else (wrapping_sub a b, decide (¬ InRange lo hi (exactSub a b)))

@[csimp] theorem overflowing_sub_eq_fast : @overflowing_sub = @overflowing_sub_fast := by
  funext lo hi a b
  unfold overflowing_sub_fast
  split
  · next hm =>
    have hs := toInt_val_sub hm a b
    have hflag : decide (¬ InRange lo hi (exactSub a b))
        = !(decide (lo ≤ a.val - b.val) && decide (a.val - b.val ≤ hi)) := by
      have hiff : InRange lo hi (exactSub a b) ↔ (lo ≤ a.val - b.val ∧ a.val - b.val ≤ hi) := by
        show (lo.toInt ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt ≤ hi.toInt) ↔ _
        rw [int64_le_iff, int64_le_iff, hs]
      exact flag_eq hiff
    show (wrapping_sub a b, decide (¬ InRange lo hi (exactSub a b))) = _
    rw [hflag, congrFun (congrFun (congrFun (congrFun wrapping_sub_eq_fast lo) hi) a) b]
  · rfl

/-! ### Multiplication -/

/-- The magnitude of a machine word. -/
def absWord (v : Int64) : Int64 := if v < 0 then -v else v

theorem toInt_absWord {v : Int64} (h₁ : -(2 ^ 62) ≤ v.toInt) (h₂ : v.toInt ≤ 2 ^ 62) :
    (absWord v).toInt = (v.toInt.natAbs : Int) := by
  have hzero : (0 : Int64).toInt = 0 := by decide +kernel
  unfold absWord
  by_cases hneg : v.toInt < 0
  · rw [ite_eq_left (int64_lt_iff.mpr (by rw [hzero]; omega)), toInt_word_neg (by omega) (by omega)]
    omega
  · have hnlt : ¬ v < 0 := by
      intro hc
      have hcc := int64_lt_iff.mp hc
      rw [hzero] at hcc
      omega
    rw [ite_eq_right hnlt]
    omega

theorem val_eq_zero_iff {b : BoundedInt64 lo hi} : b.val = 0 ↔ b.toInt = 0 := by
  have hzero : (0 : Int64).toInt = 0 := by decide +kernel
  constructor
  · intro h; show b.val.toInt = 0; rw [h, hzero]
  · intro h; exact int64_eq_of_toInt_eq (by rw [hzero]; exact h)

/-- The two operands are small enough for their product to be computed in a machine
word: the test is a single machine division. -/
def mulFits (a b : BoundedInt64 lo hi) : Bool :=
  b.val == 0 || absWord a.val ≤ 2305843009213693951 / absWord b.val

/-- When the test succeeds, the machine product is the exact product, and that product is
at most `2 ^ 61 - 1` in absolute value. -/
theorem toInt_val_mul_of_mulFits (hm : moderate lo hi = true) {a b : BoundedInt64 lo hi}
    (hf : mulFits a b = true) :
    (a.val * b.val).toInt = a.toInt * b.toInt ∧
      (a.toInt * b.toInt).natAbs ≤ 2 ^ 61 - 1 := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  obtain ⟨hb₁, hb₂⟩ := toInt_bounds hm b
  have hav := toInt_val a
  have hbv := toInt_val b
  have hna : (a.toInt * b.toInt).natAbs = a.toInt.natAbs * b.toInt.natAbs := Int.natAbs_mul _ _
  have hcast : ((a.toInt.natAbs * b.toInt.natAbs : Nat) : Int)
      = (a.toInt.natAbs : Int) * (b.toInt.natAbs : Int) := Int.natCast_mul _ _
  have hbound : (a.toInt * b.toInt).natAbs ≤ 2 ^ 61 - 1 := by
    by_cases hb : b.val = 0
    · have hz : b.toInt = 0 := val_eq_zero_iff.mp hb
      have hz' : b.toInt.natAbs = 0 := by omega
      rw [hna, hz']
      omega
    · have hdiv : (decide (absWord a.val ≤ 2305843009213693951 / absWord b.val)) = true := by
        rcases Bool.or_eq_true _ _ |>.mp hf with h0 | h1
        · exact absurd (by simpa using h0) hb
        · exact h1
      have hdivP := of_decide_eq_true hdiv
      have hbnz : b.toInt ≠ 0 := fun hc => hb (val_eq_zero_iff.mpr hc)
      have habsa := toInt_absWord (v := a.val) (by omega) (by omega)
      have habsb := toInt_absWord (v := b.val) (by omega) (by omega)
      have hC : (2305843009213693951 : Int64).toInt = 2 ^ 61 - 1 := by decide +kernel
      have habsbpos : 0 < (absWord b.val).toInt := by rw [habsb, hbv]; omega
      have hnn : (0 : Int) ≤ 2 ^ 61 - 1 := by omega
      have hediv_le : (2 ^ 61 - 1 : Int) / (absWord b.val).toInt ≤ 2 ^ 61 - 1 :=
        Int.ediv_le_self _ hnn
      have hediv_nn : 0 ≤ (2 ^ 61 - 1 : Int) / (absWord b.val).toInt :=
        Int.ediv_nonneg hnn (by omega)
      have hq : (2305843009213693951 / absWord b.val : Int64).toInt
          = (2 ^ 61 - 1 : Int) / (absWord b.val).toInt := by
        rw [toInt_word_div (by rw [hC, Int.tdiv_eq_ediv_of_nonneg hnn]; omega)
            (by rw [hC, Int.tdiv_eq_ediv_of_nonneg hnn]; omega), hC,
          Int.tdiv_eq_ediv_of_nonneg hnn]
      have hstep : (absWord a.val).toInt ≤ (2 ^ 61 - 1 : Int) / (absWord b.val).toInt := by
        have hle := int64_le_iff.mp hdivP
        rwa [hq] at hle
      have hmul := (Int.le_ediv_iff_mul_le habsbpos).mp hstep
      rw [habsa, habsb, hav, hbv] at hmul
      omega
  exact ⟨toInt_word_mul (by rw [hav, hbv]; omega) (by rw [hav, hbv]; omega), hbound⟩

/-- Machine-word checked multiplication.  When the product is too large for a machine
word — which can only happen when it is out of range anyway — the exact `Int` product is
used instead. -/
def checked_mul_fast (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi && mulFits a b then ofWord? lo hi (a.val * b.val)
  else ofInt? lo hi (exactMul a b)

@[csimp] theorem checked_mul_eq_fast : @checked_mul = @checked_mul_fast := by
  funext lo hi a b
  unfold checked_mul_fast
  split
  · next hc =>
    obtain ⟨hm, hf⟩ := Bool.and_eq_true _ _ |>.mp hc
    rw [ofWord?_eq, (toInt_val_mul_of_mulFits hm hf).1]
    rfl
  · rfl

/-- Machine-word saturating multiplication. -/
def saturating_mul_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi && mulFits a b then ofWordSat (lo_le_hi a) (a.val * b.val)
  else ofIntSat (lo_le_hi a) (exactMul a b)

@[csimp] theorem saturating_mul_eq_fast : @saturating_mul = @saturating_mul_fast := by
  funext lo hi a b
  unfold saturating_mul_fast
  split
  · next hc =>
    obtain ⟨hm, hf⟩ := Bool.and_eq_true _ _ |>.mp hc
    rw [ofWordSat_eq, (toInt_val_mul_of_mulFits hm hf).1]
    rfl
  · rfl

/-- Machine-word wrapping multiplication.  The modular reduction is done in a machine
word whenever the exact product fits in one. -/
def wrapping_mul_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi && mulFits a b then
    ofWordSat (lo_le_hi a) (wrapWord lo hi (a.val * b.val))
  else ofIntWrap (lo_le_hi a) (exactMul a b)

@[csimp] theorem wrapping_mul_eq_fast : @wrapping_mul = @wrapping_mul_fast := by
  funext lo hi a b
  unfold wrapping_mul_fast
  split
  · next hc =>
    obtain ⟨hm, hf⟩ := Bool.and_eq_true _ _ |>.mp hc
    obtain ⟨hprod, hbound⟩ := toInt_val_mul_of_mulFits hm hf
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hprod]; omega) (by rw [hprod]; omega),
      hprod]
    rfl
  · rfl

/-- Machine-word overflowing multiplication. -/
def overflowing_mul_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  if moderate lo hi && mulFits a b then
    (wrapping_mul_fast a b, !(lo ≤ a.val * b.val && a.val * b.val ≤ hi))
  else (wrapping_mul a b, decide (¬ InRange lo hi (exactMul a b)))

@[csimp] theorem overflowing_mul_eq_fast : @overflowing_mul = @overflowing_mul_fast := by
  funext lo hi a b
  unfold overflowing_mul_fast
  split
  · next hc =>
    obtain ⟨hm, hf⟩ := Bool.and_eq_true _ _ |>.mp hc
    have hprod := (toInt_val_mul_of_mulFits hm hf).1
    have hflag : decide (¬ InRange lo hi (exactMul a b))
        = !(decide (lo ≤ a.val * b.val) && decide (a.val * b.val ≤ hi)) := by
      have hiff : InRange lo hi (exactMul a b) ↔ (lo ≤ a.val * b.val ∧ a.val * b.val ≤ hi) := by
        show (lo.toInt ≤ a.toInt * b.toInt ∧ a.toInt * b.toInt ≤ hi.toInt) ↔ _
        rw [int64_le_iff, int64_le_iff, hprod]
      exact flag_eq hiff
    show (wrapping_mul a b, decide (¬ InRange lo hi (exactMul a b))) = _
    rw [hflag, congrFun (congrFun (congrFun (congrFun wrapping_mul_eq_fast lo) hi) a) b]
  · rfl


/-! ### Division and remainder -/

theorem toInt_val_div (hm : moderate lo hi = true) (a b : BoundedInt64 lo hi) :
    (a.val / b.val).toInt = a.toInt.tdiv b.toInt := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  have hav := toInt_val a
  have hbv := toInt_val b
  have hle : (a.toInt.tdiv b.toInt).natAbs ≤ a.toInt.natAbs := Int.natAbs_tdiv_le_natAbs _ _
  exact toInt_word_div (by rw [hav, hbv]; omega) (by rw [hav, hbv]; omega)

theorem toInt_val_mod (a b : BoundedInt64 lo hi) :
    (a.val % b.val).toInt = a.toInt.tmod b.toInt := toInt_word_mod a.val b.val

theorem natAbs_tmod_le (a b : BoundedInt64 lo hi) :
    (a.toInt.tmod b.toInt).natAbs ≤ a.toInt.natAbs := by
  rw [Int.natAbs_tmod]
  exact Nat.mod_le _ _

/-- Machine-word checked division. -/
def checked_div_fast (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi then
    (if b.val = 0 then none else ofWord? lo hi (a.val / b.val))
  else (if b.toInt = 0 then none else ofInt? lo hi (exactDiv a b))

@[csimp] theorem checked_div_eq_fast : @checked_div = @checked_div_fast := by
  funext lo hi a b
  unfold checked_div_fast checked_div
  by_cases hmod : moderate lo hi = true
  · rw [ite_eq_left hmod]
    by_cases hb : b.val = 0
    · rw [ite_eq_left hb, ite_eq_left (val_eq_zero_iff.mp hb)]
    · rw [ite_eq_right hb, ite_eq_right (fun hcc => hb (val_eq_zero_iff.mpr hcc)), ofWord?_eq,
        toInt_val_div hmod]
      rfl
  · rw [ite_eq_right hmod]

/-- Machine-word checked remainder. -/
def checked_mod_fast (a b : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if b.val = 0 then none else ofWord? lo hi (a.val % b.val)

@[csimp] theorem checked_mod_eq_fast : @checked_mod = @checked_mod_fast := by
  funext lo hi a b
  unfold checked_mod_fast checked_mod
  by_cases hb : b.val = 0
  · rw [ite_eq_left hb, ite_eq_left (val_eq_zero_iff.mp hb)]
  · rw [ite_eq_right hb, ite_eq_right (fun hcc => hb (val_eq_zero_iff.mpr hcc)), ofWord?_eq,
      toInt_val_mod]
    rfl

/-- Machine-word wrapping division. -/
def wrapping_div_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (a.val / b.val))
  else ofIntWrap (lo_le_hi a) (exactDiv a b)

@[csimp] theorem wrapping_div_eq_fast : @wrapping_div = @wrapping_div_fast := by
  funext lo hi a b
  unfold wrapping_div_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    have hq := toInt_val_div hm a b
    have hle : (a.toInt.tdiv b.toInt).natAbs ≤ a.toInt.natAbs := Int.natAbs_tdiv_le_natAbs _ _
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hq]; omega) (by rw [hq]; omega), hq]
    rfl
  · rfl

/-- Machine-word wrapping remainder. -/
def wrapping_mod_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (a.val % b.val))
  else ofIntWrap (lo_le_hi a) (exactMod a b)

@[csimp] theorem wrapping_mod_eq_fast : @wrapping_mod = @wrapping_mod_fast := by
  funext lo hi a b
  unfold wrapping_mod_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    have hr := toInt_val_mod a b
    have hle := natAbs_tmod_le a b
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hr]; omega) (by rw [hr]; omega), hr]
    rfl
  · rfl

/-- Machine-word saturating division. -/
def saturating_div_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (a.val / b.val)
  else ofIntSat (lo_le_hi a) (exactDiv a b)

@[csimp] theorem saturating_div_eq_fast : @saturating_div = @saturating_div_fast := by
  funext lo hi a b
  unfold saturating_div_fast
  split
  · next hm => rw [ofWordSat_eq, toInt_val_div hm]; rfl
  · rfl

/-- Machine-word saturating remainder. -/
def saturating_mod_fast (a b : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  ofWordSat (lo_le_hi a) (a.val % b.val)

@[csimp] theorem saturating_mod_eq_fast : @saturating_mod = @saturating_mod_fast := by
  funext lo hi a b
  unfold saturating_mod_fast
  rw [ofWordSat_eq, toInt_val_mod]
  rfl

/-! ### Negation and absolute value -/

theorem toInt_val_neg (hm : moderate lo hi = true) (a : BoundedInt64 lo hi) :
    (-a.val).toInt = -a.toInt := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  have hav := toInt_val a
  exact toInt_word_neg (by omega) (by omega)

theorem toInt_absWord_val (hm : moderate lo hi = true) (a : BoundedInt64 lo hi) :
    (absWord a.val).toInt = exactAbs a := by
  obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
  have hav := toInt_val a
  have h := toInt_absWord (v := a.val) (by omega) (by omega)
  have hex : exactAbs a = if a.toInt < 0 then -a.toInt else a.toInt := by
    unfold exactAbs
    split <;> omega
  rw [h, hex, hav]
  split <;> omega

/-- Machine-word checked negation. -/
def checked_neg_fast (a : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi then ofWord? lo hi (-a.val) else ofInt? lo hi (exactNeg a)

@[csimp] theorem checked_neg_eq_fast : @checked_neg = @checked_neg_fast := by
  funext lo hi a
  unfold checked_neg_fast
  split
  · next hm => rw [ofWord?_eq, toInt_val_neg hm]; rfl
  · rfl

/-- Machine-word checked absolute value. -/
def checked_abs_fast (a : BoundedInt64 lo hi) : Option (BoundedInt64 lo hi) :=
  if moderate lo hi then ofWord? lo hi (absWord a.val) else ofInt? lo hi (exactAbs a)

@[csimp] theorem checked_abs_eq_fast : @checked_abs = @checked_abs_fast := by
  funext lo hi a
  unfold checked_abs_fast
  split
  · next hm => rw [ofWord?_eq, toInt_absWord_val hm]; rfl
  · rfl

/-- Machine-word saturating negation. -/
def saturating_neg_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (-a.val)
  else ofIntSat (lo_le_hi a) (exactNeg a)

@[csimp] theorem saturating_neg_eq_fast : @saturating_neg = @saturating_neg_fast := by
  funext lo hi a
  unfold saturating_neg_fast
  split
  · next hm => rw [ofWordSat_eq, toInt_val_neg hm]; rfl
  · rfl

/-- Machine-word saturating absolute value. -/
def saturating_abs_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (absWord a.val)
  else ofIntSat (lo_le_hi a) (exactAbs a)

@[csimp] theorem saturating_abs_eq_fast : @saturating_abs = @saturating_abs_fast := by
  funext lo hi a
  unfold saturating_abs_fast
  split
  · next hm => rw [ofWordSat_eq, toInt_absWord_val hm]; rfl
  · rfl

/-- Machine-word wrapping negation. -/
def wrapping_neg_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (-a.val))
  else ofIntWrap (lo_le_hi a) (exactNeg a)

@[csimp] theorem wrapping_neg_eq_fast : @wrapping_neg = @wrapping_neg_fast := by
  funext lo hi a
  unfold wrapping_neg_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    have hn := toInt_val_neg hm a
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hn]; omega) (by rw [hn]; omega), hn]
    rfl
  · rfl

/-- Machine-word wrapping absolute value. -/
def wrapping_abs_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi :=
  if moderate lo hi then ofWordSat (lo_le_hi a) (wrapWord lo hi (absWord a.val))
  else ofIntWrap (lo_le_hi a) (exactAbs a)

@[csimp] theorem wrapping_abs_eq_fast : @wrapping_abs = @wrapping_abs_fast := by
  funext lo hi a
  unfold wrapping_abs_fast
  split
  · next hm =>
    obtain ⟨ha₁, ha₂⟩ := toInt_bounds hm a
    have hn := toInt_absWord_val hm a
    have hex : exactAbs a = (a.toInt.natAbs : Int) := rfl
    rw [ofWordSat_wrapWord hm (lo_le_hi a) (by rw [hn, hex]; omega) (by rw [hn, hex]; omega),
      hn]
    rfl
  · rfl

/-- Machine-word overflowing negation. -/
def overflowing_neg_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  if moderate lo hi then (wrapping_neg_fast a, !(lo ≤ -a.val && -a.val ≤ hi))
  else (wrapping_neg a, decide (¬ InRange lo hi (exactNeg a)))

@[csimp] theorem overflowing_neg_eq_fast : @overflowing_neg = @overflowing_neg_fast := by
  funext lo hi a
  unfold overflowing_neg_fast
  split
  · next hm =>
    have hn := toInt_val_neg hm a
    have hflag : decide (¬ InRange lo hi (exactNeg a))
        = !(decide (lo ≤ -a.val) && decide (-a.val ≤ hi)) := by
      have hiff : InRange lo hi (exactNeg a) ↔ (lo ≤ -a.val ∧ -a.val ≤ hi) := by
        show (lo.toInt ≤ -a.toInt ∧ -a.toInt ≤ hi.toInt) ↔ _
        rw [int64_le_iff, int64_le_iff, hn]
      exact flag_eq hiff
    show (wrapping_neg a, decide (¬ InRange lo hi (exactNeg a))) = _
    rw [hflag, congrFun (congrFun (congrFun wrapping_neg_eq_fast lo) hi) a]
  · rfl

/-- Machine-word overflowing absolute value. -/
def overflowing_abs_fast (a : BoundedInt64 lo hi) : BoundedInt64 lo hi × Bool :=
  if moderate lo hi then
    (wrapping_abs_fast a, !(lo ≤ absWord a.val && absWord a.val ≤ hi))
  else (wrapping_abs a, decide (¬ InRange lo hi (exactAbs a)))

@[csimp] theorem overflowing_abs_eq_fast : @overflowing_abs = @overflowing_abs_fast := by
  funext lo hi a
  unfold overflowing_abs_fast
  split
  · next hm =>
    have hn := toInt_absWord_val hm a
    have hflag : decide (¬ InRange lo hi (exactAbs a))
        = !(decide (lo ≤ absWord a.val) && decide (absWord a.val ≤ hi)) := by
      have hiff : InRange lo hi (exactAbs a) ↔ (lo ≤ absWord a.val ∧ absWord a.val ≤ hi) := by
        show (lo.toInt ≤ exactAbs a ∧ exactAbs a ≤ hi.toInt) ↔ _
        rw [int64_le_iff, int64_le_iff, hn]
      exact flag_eq hiff
    show (wrapping_abs a, decide (¬ InRange lo hi (exactAbs a))) = _
    rw [hflag, congrFun (congrFun (congrFun wrapping_abs_eq_fast lo) hi) a]
  · rfl

end BoundedInt64
