import RefactorSpec.NumberStrip
import LanguageJavascriptCommon.LiteralPrintSpec

/-!
# The JavaScript source text of a `number` literal did not change

`Legacy.decimalString` and `Legacy.source` are the removed spelling of a `number` literal (its
own positional/scientific decimal writer).  The new `NumberForm.source` spells a decimal with
`JSNumber.render` of the JavaScript trees (`renderDecimal`) and adds the `+` of a positive
exponent (`withExponentSign`).  `source_eq_legacy` proves the two give the same string for every
unpacked float whose mantissa is below `2 ^ 53`; `numberSource_eq_legacy` and
`float32Source_eq_legacy` drop the hypothesis for the values of a `Float` or a `Float32`.

The key step is `withExponentSign_renderDecimal`: for a positive mantissa, the writer of the
JavaScript trees plus the exponent sign is exactly the removed writer.

(This file is not a `module`: it uses `LanguageJavascriptCommon.LiteralPrintSpec`, which is not
one.)
-/

namespace MoreJs

open Language.JavaScript (JSNumber)
open Float.Model (UnpackedFloat)

/-- The removed `NumberForm.decimalString`. -/
def Legacy.decimalString (digits : Nat) (exponent : Int) : String :=
  let s := toString digits
  let k : Int := s.length
  let n : Int := exponent + k
  if k ≤ n ∧ n ≤ 21 then s ++ String.ofList (List.replicate (n - k).toNat '0')
  else if 0 < n ∧ n ≤ 21 then
    String.ofList (s.toList.take n.toNat) ++ "." ++ String.ofList (s.toList.drop n.toNat)
  else if -6 < n ∧ n ≤ 0 then "0." ++ String.ofList (List.replicate n.natAbs '0') ++ s
  else
    let mant := match s.toList with
      | [] => s
      | [c] => String.singleton c
      | c :: cs => String.singleton c ++ "." ++ String.ofList cs
    let e := n - 1
    mant ++ "e" ++ (if e ≥ 0 then "+" else "-") ++ toString e.natAbs

/-- The removed `NumberForm.source`. -/
def Legacy.source : Legacy.NumberForm → String
  | .nan => "NaN"
  | .infinity neg => if neg then "-Infinity" else "Infinity"
  | .negZero => "-0"
  | .int n => toString n
  | .decimal neg d ex => (if neg then "-" else "") ++ decimalString d ex

namespace RefactorSpec

/-- Every character of the list is one byte long in UTF-8. -/
def Ascii (l : List Char) : Prop := ∀ c ∈ l, c.utf8Size = 1

theorem toList_pushn (c : Char) : ∀ (n : Nat) (s : String),
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  intro n
  induction n with
  | zero => intro s; simp [String.pushn_eq_repeat_push, Nat.repeat]
  | succ n ih =>
    intro s
    have := ih s
    rw [String.pushn_eq_repeat_push] at this ⊢
    simp only [Nat.repeat, String.toList_push]
    rw [this, List.replicate_succ', List.append_assoc]

theorem ofList_cons (c : Char) (l : List Char) :
    String.ofList (c :: l) = String.singleton c ++ String.ofList l := by
  apply String.toList_inj.mp; simp

theorem utf8ByteSize_ofList_of_ascii : ∀ (l : List Char), Ascii l →
    (String.ofList l).utf8ByteSize = l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons c l ih =>
    intro h
    rw [ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton,
      h c (by simp), ih (fun x hx => h x (by simp [hx]))]
    simp; omega

theorem extract_go₂_ascii : ∀ (l : List Char) (i n : Nat), Ascii l →
    String.Pos.Raw.extract.go₂ l ⟨i⟩ ⟨i + n⟩ = l.take n := by
  intro l
  induction l with
  | nil => intro i n _; simp [String.Pos.Raw.extract.go₂]
  | cons c l ih =>
    intro i n h
    cases n with
    | zero => simp [String.Pos.Raw.extract.go₂]
    | succ n =>
      have hc : c.utf8Size = 1 := h c (by simp)
      simp only [String.Pos.Raw.extract.go₂, String.Pos.Raw.add_char_eq, hc]
      have : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + (n + 1)⟩ := by simp
      simp only [this, ↓reduceIte]
      have := ih (i + 1) n (fun x hx => h x (by simp [hx]))
      rw [show i + (n + 1) = i + 1 + n by omega, this]
      simp

theorem extract_go₁_ascii : ∀ (l : List Char) (i b : Nat) (e : String.Pos.Raw), Ascii l →
    String.Pos.Raw.extract.go₁ l ⟨i⟩ ⟨i + b⟩ e = String.Pos.Raw.extract.go₂ (l.drop b) ⟨i + b⟩ e := by
  intro l
  induction l with
  | nil => intro i b e _; simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
  | cons c l ih =>
    intro i b e h
    cases b with
    | zero => simp [String.Pos.Raw.extract.go₁]
    | succ b =>
      have hc : c.utf8Size = 1 := h c (by simp)
      simp only [String.Pos.Raw.extract.go₁, String.Pos.Raw.add_char_eq, hc]
      have : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + (b + 1)⟩ := by simp
      simp only [this, ↓reduceIte]
      have := ih (i + 1) b e (fun x hx => h x (by simp [hx]))
      rw [show i + (b + 1) = i + 1 + b by omega, this]
      simp

/-- The first `n` characters of an ASCII string. -/
theorem extract_prefix (l : List Char) (hl : Ascii l) (n : Nat) (hn : 0 < n) :
    String.Pos.Raw.extract (String.ofList l) ⟨0⟩ ⟨n⟩ = String.ofList (l.take n) := by
  unfold String.Pos.Raw.extract
  have h0 : ¬ (0 ≥ n) := by omega
  simp only [h0, ↓reduceIte, String.toList_ofList]
  have := extract_go₁_ascii l 0 0 ⟨n⟩ hl
  simp only [Nat.add_zero, List.drop_zero] at this
  rw [show (0 : String.Pos.Raw) = ⟨0⟩ from rfl, this]
  have := extract_go₂_ascii l 0 n hl
  simp only [Nat.zero_add] at this
  rw [this]

/-- An ASCII string from its `n`-th character on. -/
theorem extract_suffix (l : List Char) (hl : Ascii l) (n : Nat) :
    String.Pos.Raw.extract (String.ofList l) ⟨n⟩ ⟨(String.ofList l).utf8ByteSize⟩ =
      String.ofList (l.drop n) := by
  unfold String.Pos.Raw.extract
  rw [utf8ByteSize_ofList_of_ascii l hl]
  by_cases h : n ≥ l.length
  · simp only [h, ↓reduceIte]
    rw [List.drop_eq_nil_of_le h]
  · simp only [h, ↓reduceIte, String.toList_ofList]
    have := extract_go₁_ascii l 0 n ⟨l.length⟩ hl
    simp only [Nat.zero_add] at this
    rw [show (0 : String.Pos.Raw) = ⟨0⟩ from rfl, this]
    have := extract_go₂_ascii (l.drop n) n (l.length - n) (fun x hx => hl x (List.mem_of_mem_drop hx))
    rw [show n + (l.length - n) = l.length by omega] at this
    rw [this, List.take_of_length_le (by simp)]

/-- A decimal digit is one byte long, and it is neither `e` nor `-`. -/
theorem digit_facts {c : Char} (h : c.isDigit = true) :
    c.utf8Size = 1 ∧ c ≠ 'e' ∧ c ≠ '-' := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Char.utf8Size]
    have : c.val ≤ 127 := UInt32.le_trans h2 (by decide)
    simp [this]
  · rintro rfl; exact absurd h2 (by decide)
  · rintro rfl; exact absurd h1 (by decide)

/-- The characters of a decimal numeral are digits. -/
theorem mem_toDigits {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : c.isDigit = true :=
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

theorem go_append_of_not_e : ∀ (l r : List Char), 'e' ∉ l →
    NumberForm.withExponentSign.go (l ++ r) = l ++ NumberForm.withExponentSign.go r := by
  intro l
  induction l with
  | nil => intro r _; rfl
  | cons c l ih =>
    intro r h
    have hc : c ≠ 'e' := fun h' => h (h' ▸ List.mem_cons_self)
    simp only [List.cons_append, NumberForm.withExponentSign.go, hc, ↓reduceIte]
    rw [ih r (fun h' => h (List.mem_cons_of_mem _ h'))]

theorem go_e (r : List Char) :
    NumberForm.withExponentSign.go ('e' :: r) =
      'e' :: (if r.head? = some '-' then r else '+' :: r) := by
  simp only [NumberForm.withExponentSign.go, ↓reduceIte]
  split <;> rfl

/-- `JSNumber.stripZerosAux` removes the trailing zeros, when the fuel covers them. -/
theorem stripZerosAux_spec : ∀ (F d : Nat) (e : Int), 0 < d → ¬ 10 ^ F ∣ d →
    ∃ z : Nat, JSNumber.stripZerosAux F d e = (d / 10 ^ z, e + z) ∧ 10 ^ z ∣ d ∧
      (d / 10 ^ z) % 10 ≠ 0 := by
  intro F
  induction F with
  | zero => intro d e _ h; simp at h
  | succ F ih =>
    intro d e hd hdv
    simp only [JSNumber.stripZerosAux]
    by_cases h : d % 10 = 0
    · have h1 : 0 < d / 10 := by omega
      have h2 : ¬ 10 ^ F ∣ d / 10 := by
        intro ⟨c, hc⟩
        apply hdv
        refine ⟨c, ?_⟩
        have := Nat.div_add_mod d 10
        rw [h, hc, Nat.add_zero] at this
        rw [← this, Nat.pow_succ, Nat.mul_left_comm, Nat.mul_assoc]
      obtain ⟨z, hz, hdz, hmod⟩ := ih (d / 10) (e + 1) h1 h2
      refine ⟨z + 1, ?_, ?_, ?_⟩
      · simp only [h, beq_self_eq_true, ↓reduceIte, hz, Nat.div_div_eq_div_mul, Nat.pow_succ]
        rw [Nat.mul_comm (10 ^ z) 10]
        simp only [Prod.mk.injEq, true_and]; omega
      · rw [Nat.pow_succ, Nat.mul_comm]
        exact Nat.mul_dvd_of_dvd_div (Nat.dvd_of_mod_eq_zero h) hdz
      · rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    · refine ⟨0, ?_, by simp, by simpa using h⟩
      simp [h]

/-- `JSNumber.stripZeros` removes the trailing zeros of a positive mantissa. -/
theorem stripZeros_spec (d : Nat) (e : Int) (hd : 0 < d) :
    ∃ z : Nat, JSNumber.stripZeros d e = (d / 10 ^ z, e + z) ∧ 10 ^ z ∣ d ∧
      (d / 10 ^ z) % 10 ≠ 0 := by
  have hself : ¬ 10 ^ d ∣ d := fun hdv =>
    Nat.lt_irrefl d (Nat.lt_of_lt_of_le (Nat.lt_pow_self (by decide)) (Nat.le_of_dvd hd hdv))
  have : (d == 0) = false := by simp; omega
  simp only [JSNumber.stripZeros, this, Bool.false_eq_true, ↓reduceIte]
  exact stripZerosAux_spec d d e hd hself

/-- Removing the trailing zeros a second time changes nothing. -/
theorem normalize_normalize (d : Nat) (e : Int) :
    (JSNumber.normalize (.decimal d e)).normalize = JSNumber.normalize (.decimal d e) := by
  by_cases hd : d = 0
  · subst hd; rfl
  · obtain ⟨z, hz, hdz, hmod⟩ := stripZeros_spec d e (by omega)
    have hpos : 0 < d / 10 ^ z := Nat.div_pos (Nat.le_of_dvd (by omega) hdz) (Nat.pow_pos (by decide))
    simp only [JSNumber.normalize, hz]
    have : (d / 10 ^ z == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hpos)
    simp only [JSNumber.stripZeros, this, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k, d / 10 ^ z = k + 1 := ⟨d / 10 ^ z - 1, by omega⟩
    rw [hk, JSNumber.stripZerosAux]
    rw [hk] at hmod
    simp [hmod]

/-- `v * 10 ^ z` is written as `v` followed by `z` zeros. -/
theorem toDigits_mul_pow (v : Nat) (hv : 0 < v) : ∀ z : Nat,
    Nat.toDigits 10 (v * 10 ^ z) = Nat.toDigits 10 v ++ List.replicate z '0' := by
  intro z
  induction z with
  | zero => simp
  | succ z ih =>
    have hpos : 0 < v * 10 ^ z := Nat.mul_pos hv (Nat.pow_pos (by decide))
    have := Nat.toDigits_append_toDigits (b := 10) (d := 0) (by decide) hpos (by decide)
    rw [Nat.toDigits_zero, Nat.add_zero, ih] at this
    rw [show v * 10 ^ (z + 1) = 10 * (v * 10 ^ z) by rw [Nat.pow_succ]; ac_rfl, ← this,
      List.replicate_succ', List.append_assoc]

/-- The decimal writer of the JavaScript trees, with the sign of a positive exponent added, is
    the removed decimal writer. -/
theorem withExponentSign_renderDecimal (d : Nat) (ex : Int) (hd : 0 < d) :
    NumberForm.withExponentSign (JSNumber.renderDecimal d ex) = Legacy.decimalString d ex := by
  have hd0 : (d == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hd)
  have hdig : JSNumber.digitsOf 10 d = String.ofList (Nat.toDigits 10 d) := by
    rw [Language.JavaScript.LiteralPrintSpec.JSNumber.digitsOf_eq 10 (by decide) (by decide), hd0]; rfl
  unfold JSNumber.renderDecimal Legacy.decimalString
  simp only [hd0, Bool.false_eq_true, ↓reduceIte, hdig, Nat.toString_eq_ofList_toDigits,
    String.length_ofList, String.toList_ofList]
  have hT : ∀ c ∈ Nat.toDigits 10 d, c.utf8Size = 1 ∧ c ≠ 'e' ∧ c ≠ '-' :=
    fun c hc => digit_facts (mem_toDigits hc)
  have hne : Nat.toDigits 10 d ≠ [] := Nat.toDigits_ne_nil
  generalize Nat.toDigits 10 d = T at hT hne
  have hA : Ascii T := fun c hc => (hT c hc).1
  have hE : 'e' ∉ T := fun h => (hT _ h).2.1 rfl
  simp only [Int.ofNat_eq_natCast]
  rw [show ex + (T.length : Int) = (T.length : Int) + ex from Int.add_comm _ _]
  generalize (T.length : Int) + ex = n
  simp only [extract_suffix T hA, extract_prefix T hA 1 (by decide)]
  have go_id : ∀ l : List Char, 'e' ∉ l → NumberForm.withExponentSign.go l = l := fun l hl => by
    have := go_append_of_not_e l [] hl
    simpa [NumberForm.withExponentSign.go] using this
  unfold NumberForm.withExponentSign
  by_cases h1 : (T.length : Int) ≤ n ∧ n ≤ 21
  · simp only [h1, decide_true, Bool.and_self, ↓reduceIte, and_self]
    apply String.toList_inj.mp
    simp only [String.toList_ofList, String.toList_append, JSNumber.repeatChar, toList_pushn]
    rw [go_id _ (by simp [List.mem_append, List.mem_replicate, hE])]
    simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq, h1, ↓reduceIte]
    by_cases h2 : 0 < n ∧ n ≤ 21
    · simp only [h2, and_self, ↓reduceIte, extract_prefix T hA n.toNat (by omega)]
      apply String.toList_inj.mp
      simp only [String.toList_ofList, String.toList_append]
      rw [go_id _ (by
        simp only [List.mem_append, not_or]
        exact ⟨⟨fun h => hE (List.mem_of_mem_take h), by decide⟩, fun h => hE (List.mem_of_mem_drop h)⟩)]
    · simp only [h2, ↓reduceIte]
      by_cases h3 : -6 < n ∧ n ≤ 0
      · simp only [h3, and_self, ↓reduceIte]
        apply String.toList_inj.mp
        simp only [String.toList_ofList, String.toList_append, JSNumber.repeatChar, toList_pushn]
        rw [go_id _ (by simp [List.mem_append, List.mem_replicate, hE])]
        simp only [String.toList_empty, List.nil_append]
        have : (-n).toNat = n.natAbs := by omega
        rw [this]
      · simp only [h3, ↓reduceIte]
        obtain ⟨c, cs, rfl⟩ : ∃ c cs, T = c :: cs := by
          cases T with
          | nil => exact absurd rfl hne
          | cons c cs => exact ⟨c, cs, rfl⟩
        generalize n - 1 = e
        have hnd : ∀ k : Nat, (Nat.toDigits 10 k).head? ≠ some '-' := fun k h =>
          (digit_facts (mem_toDigits (List.mem_of_mem_head? h))).2.2 rfl
        have key : ∀ M : String, 'e' ∉ M.toList →
            String.ofList (NumberForm.withExponentSign.go
              (M ++ "e" ++ (if e < 0 then "-" ++ toString (-e) else toString e)).toList) =
            M ++ "e" ++ (if e ≥ 0 then "+" else "-") ++ String.ofList (Nat.toDigits 10 e.natAbs) := by
          intro M hM
          apply String.toList_inj.mp
          simp only [String.toList_ofList, String.toList_append, List.append_assoc]
          rw [go_append_of_not_e _ _ hM, show "e".toList = ['e'] from rfl, List.singleton_append,
            go_e]
          by_cases he : e < 0
          · have h' : ¬ e ≥ 0 := by omega
            have h0 : 0 ≤ -e := by omega
            simp only [he, h', h0, ↓reduceIte, String.toList_append, Int.toString_eq_repr,
              Int.repr_eq_ite, Nat.toList_repr, show "-".toList = ['-'] from rfl,
              show (-e).toNat = e.natAbs by omega]
            rfl
          · have h' : e ≥ 0 := by omega
            simp only [he, h', ↓reduceIte, Int.toString_eq_repr, Int.repr_eq_ite, Nat.toList_repr,
              show "+".toList = ['+'] from rfl, show e.toNat = e.natAbs by omega, hnd]
            rfl
        have e1 : ∀ l : List Char, String.ofList (List.take 1 (c :: l)) = String.singleton c := by
          intro l; apply String.toList_inj.mp; simp
        cases cs with
        | nil =>
          have e2 : (String.ofList (List.drop 1 [c])).isEmpty = true := rfl
          simp only [e2, ↓reduceIte, e1]
          exact key _ (by simpa using hE)
        | cons c' cs' =>
          have e2 : (String.ofList (List.drop 1 (c :: c' :: cs'))).isEmpty = false := by
            cases h : (String.ofList (List.drop 1 (c :: c' :: cs'))).isEmpty
            · rfl
            · have := congrArg String.toList (String.isEmpty_iff.mp h); simp at this
          simp only [e2, Bool.false_eq_true, ↓reduceIte, e1]
          refine key _ ?_
          simp only [String.toList_append, String.toList_singleton, String.toList_ofList,
            List.drop_succ_cons, List.drop_zero, List.mem_append, not_or]
          exact ⟨⟨fun h => hE (by simp at h; subst h; exact List.mem_cons_self), by decide⟩,
            fun h => hE (List.mem_cons_of_mem _ h)⟩

/-- A positive integer of at most `2 ^ 53` is spelled as itself. -/
theorem withExponentSign_render_int (v : Nat) (hv : 0 < v) (hv' : v ≤ 2 ^ 53) :
    NumberForm.withExponentSign (JSNumber.decimal v 0).render = toString v := by
  obtain ⟨z, hz, hdz, _⟩ := stripZeros_spec v 0 hv
  have hw : 0 < v / 10 ^ z := Nat.div_pos (Nat.le_of_dvd hv hdz) (Nat.pow_pos (by decide))
  have hvw : v = v / 10 ^ z * 10 ^ z := (Nat.div_mul_cancel hdz).symm
  generalize v / 10 ^ z = w at hw hvw hz
  subst hvw
  have hw0 : (w == 0) = false := beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hw)
  simp only [JSNumber.render, JSNumber.normalize, hz, JSNumber.renderDecimal, hw0,
    Bool.false_eq_true, ↓reduceIte,
    Language.JavaScript.LiteralPrintSpec.JSNumber.digitsOf_eq 10 (by decide) (by decide),
    String.length_ofList, Int.ofNat_eq_natCast, Nat.toString_eq_ofList_toDigits,
    toDigits_mul_pow w hw z]
  have hb := (digits_bounds w hw).1
  rw [Nat.toString_eq_ofList_toDigits, String.length_ofList] at hb
  have hlen : (Nat.toDigits 10 w).length + z ≤ 21 := by
    have h1 : 10 ^ ((Nat.toDigits 10 w).length - 1 + z) ≤ w * 10 ^ z := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_right _ hb
    have h2 : w * 10 ^ z < 10 ^ 16 := Nat.lt_of_le_of_lt hv' (by decide)
    have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp (Nat.lt_of_le_of_lt h1 h2)
    have := @Nat.length_toDigits_pos 10 w
    omega
  have hc : ((Nat.toDigits 10 w).length : Int) ≤ (Nat.toDigits 10 w).length + (0 + (z : Int)) ∧
      ((Nat.toDigits 10 w).length : Int) + (0 + (z : Int)) ≤ 21 := by omega
  simp only [hc, decide_true, Bool.and_self, ↓reduceIte]
  unfold NumberForm.withExponentSign
  apply String.toList_inj.mp
  simp only [String.toList_ofList, String.toList_append, JSNumber.repeatChar, toList_pushn,
    String.toList_empty, List.nil_append]
  have hE : 'e' ∉ Nat.toDigits 10 w := fun h => (digit_facts (mem_toDigits h)).2.1 rfl
  rw [go_append_of_not_e _ _ hE]
  have : NumberForm.withExponentSign.go (List.replicate ((Nat.toDigits 10 w).length + (0 + (z:Int)) - (Nat.toDigits 10 w).length).toNat '0') = List.replicate z '0' := by
    rw [show ((Nat.toDigits 10 w).length + (0 + (z:Int)) - (Nat.toDigits 10 w).length).toNat = z by omega]
    have := go_append_of_not_e (List.replicate z '0') [] (by simp [List.mem_replicate])
    simpa [NumberForm.withExponentSign.go] using this
  rw [this]

/-- The two spellings agree on every unpacked float with a mantissa below `2 ^ 53`. -/
theorem source_eq_legacy (u : UnpackedFloat)
    (hu : ∀ s m e h, u = .finite s m e h → m < 2 ^ 53) :
    NumberForm.source (.float u) = Legacy.source (Legacy.ofUnpacked u) := by
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> decide
  | zero s => cases s <;> decide
  | finite s m e hm =>
    have hlt := hu s m e hm rfl
    simp only [NumberForm.source, Legacy.ofUnpacked, NumberForm.finiteDecimal]
    cases hv : NumberForm.smallNat? m e with
    | some v =>
      have hv0 := smallNat?_pos hm hv
      have hv1 := smallNat?_le hv
      simp only [withExponentSign_render_int v hv0 hv1]
      cases s
      · simp only [Legacy.source, Legacy.signIsNeg, NumberForm.signPrefix, ↓reduceIte,
          Int.toString_eq_repr, Int.repr_eq_ite, show ¬ (0 ≤ -(v : Int)) by omega, Int.neg_neg,
          Int.toNat_natCast, Nat.toString_eq_repr]
      · simp only [Legacy.source, Legacy.signIsNeg, NumberForm.signPrefix, Bool.false_eq_true,
          ↓reduceIte, Int.toString_eq_repr, Int.repr_eq_ite, show (0 ≤ (v : Int)) by omega,
          Int.toNat_natCast, Nat.toString_eq_repr, String.empty_append]
    | none =>
      obtain ⟨h1, h2⟩ := shortestDecimal_digits_ok m e hm hlt
      have hs := Legacy.stripZeros_eq _ (shortestDecimal m e).2 h1 h2
      obtain ⟨z, hz, hdz, _⟩ := stripZeros_spec _ (shortestDecimal m e).2 h1
      have hs' : Legacy.stripZeros (shortestDecimal m e) =
          ((shortestDecimal m e).1 / 10 ^ z, (shortestDecimal m e).2 + z) := by
        rw [← hz, ← hs]
      have hpos : 0 < (shortestDecimal m e).1 / 10 ^ z :=
        Nat.div_pos (Nat.le_of_dvd h1 hdz) (Nat.pow_pos (by decide))
      have hr : (JSNumber.decimal (shortestDecimal m e).fst (shortestDecimal m e).snd).normalize.render =
          JSNumber.renderDecimal ((shortestDecimal m e).1 / 10 ^ z) ((shortestDecimal m e).2 + z) := by
        unfold JSNumber.render
        rw [normalize_normalize]
        simp only [JSNumber.normalize, hz]
      simp only [hr, hs', withExponentSign_renderDecimal _ _ hpos]
      cases s <;> simp [Legacy.source, Legacy.signIsNeg, NumberForm.signPrefix]

/-- The two spellings of a double agree. -/
theorem numberSource_eq_legacy (f : Float) :
    numberSource f = Legacy.source (Legacy.ofFloat f) :=
  source_eq_legacy _ fun _ _ _ _ hu => float_mantissa_lt f hu

/-- The two spellings of a `Float32` agree. -/
theorem float32Source_eq_legacy (f : Float32) :
    float32Source f = Legacy.source (Legacy.ofFloat32 f) :=
  source_eq_legacy _ fun _ _ _ _ hu => float32_mantissa_lt f hu

end RefactorSpec

end MoreJs
