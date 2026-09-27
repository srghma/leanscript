/-
What the canonical printing of a literal guarantees.

A numeric and a regular expression literal are stored as their value and
printed canonically, so the exact source spelling is *not* preserved:
`0X1f` comes back as `0x1f`, `070` as `0o70`, `1.50` as `1.5`.  What is
preserved is the value, and printing is stable — reading back what was
printed gives the same value again, so printing a second time changes
nothing.

The statements below are checked by the kernel (`by decide`, on closed
terms), which the readers and the renderers support because they are
ordinary total definitions.
-/
import LanguageJavascriptCommon.Types

namespace Language.JavaScript.LiteralPrintSpec

/-! ## Reading a spelling back gives the value it denoted -/

/-- Spellings which differ only in layout denote the same value: the tree
cannot tell `0X1f` from `0x1f`, or `1.50` from `1.5`. -/
theorem parse_hex_case_insensitive :
    JSNumber.parse? "0X1f" = JSNumber.parse? "0x1F" := by decide

theorem parse_trailing_zero :
    JSNumber.parse? "1.50" = JSNumber.parse? "1.5" := by decide

theorem parse_exponent :
    JSNumber.parse? "1.0e4" = JSNumber.parse? "10000" := by decide

/-! ## Printing is canonical, and stable

Printing a value and reading the result back gives the value again, so the
second printing is the first one.  The spelling the source used is lost,
which is the point: `070` is printed `0o70`. -/

theorem render_hex : (JSNumber.radix .hexadecimal 31).render = "0x1f" := by decide

theorem render_legacy_octal :
    ((JSNumber.parse? "070").map JSNumber.render) = some "0o70" := by decide

theorem render_trailing_zero :
    ((JSNumber.parse? "1.50").map JSNumber.render) = some "1.5" := by decide

theorem render_big_exponent :
    ((JSNumber.parse? "0.7e-18").map JSNumber.render) = some "7e-19" := by decide

/-- Reading back a printed number gives the number itself, once it is in
canonical form (`normalize`), for each of the shapes a literal has. -/
theorem parse_render_decimal :
    JSNumber.parse? (JSNumber.decimal 15 (-1)).render = some (.decimal 15 (-1)) := by decide

theorem parse_render_radix :
    JSNumber.parse? (JSNumber.radix .hexadecimal 255).render
      = some (.radix .hexadecimal 255) := by decide

theorem parse_render_octal :
    JSNumber.parse? (JSNumber.radix .octal 56).render = some (.radix .octal 56) := by decide

theorem parse_render_binary :
    JSNumber.parse? (JSNumber.radix .binary 5).render = some (.radix .binary 5) := by decide

theorem parse_render_bigint :
    JSNumber.parse? (JSNumber.bigint .decimal 123).render
      = some (.bigint .decimal 123) := by decide

theorem parse_render_exponent :
    JSNumber.parse? (JSNumber.decimal 7 (-19)).render = some (.decimal 7 (-19)) := by decide

/-! ## Regular expression literals

The pattern is stored as it was written — it is the code of the expression,
not a number — but the flags are typed, so they come back in the canonical
order `dgimsuvy`. -/

theorem regex_flags_canonical :
    ((RegExpLit.parse? "/x/ig").map RegExpLit.render) = some "/x/gi" := by decide

theorem regex_parse_render :
    ((RegExpLit.parse? "/a\\/b/gi").map RegExpLit.render) = some "/a\\/b/gi" := by decide

theorem regex_parse_render_parse :
    ((RegExpLit.parse? "/x/ig").map RegExpLit.render).bind RegExpLit.parse?
      = RegExpLit.parse? "/x/ig" := by decide

/-! ## The digits of a number are written without building a list

`JSNumber.digitsAux` pushes the digits of a number straight into the string
being built, where the renderer used to call `Nat.toDigits`, which returns a
`List Char`.  The two agree on every input. -/

namespace JSNumber

open Language.JavaScript

/-- The digit characters are the ones `Nat.digitChar` gives. -/
theorem digitChar_eq : ∀ d < 16, JSNumber.digitChar d = Nat.digitChar d := by decide

/-- `Nat.toDigitsCore` accumulates: what it is given comes out at the end. -/
theorem toDigitsCore_append (base : Nat) :
    ∀ (fuel n : Nat) (ds : List Char),
      Nat.toDigitsCore base fuel n ds = Nat.toDigitsCore base fuel n [] ++ ds := by
  intro fuel
  induction fuel with
  | zero => intro n ds; simp [Nat.toDigitsCore]
  | succ fuel ih =>
    intro n ds
    rw [Nat.toDigitsCore, Nat.toDigitsCore]
    by_cases h : n / base = 0
    · simp [h]
    · simp only [h]
      rw [ih (n / base) (Nat.digitChar (n % base) :: ds),
        ih (n / base) [Nat.digitChar (n % base)]]
      simp

/-- Pushing the digits onto a string appends exactly the characters
`Nat.toDigitsCore` would have listed. -/
theorem digitsAux_toList (base : Nat) (h0 : 0 < base) (h16 : base ≤ 16) :
    ∀ (fuel n : Nat) (acc : String),
      (JSNumber.digitsAux base fuel n acc).toList
        = acc.toList ++ Nat.toDigitsCore base fuel n [] := by
  intro fuel
  induction fuel with
  | zero => intro n acc; simp [JSNumber.digitsAux, Nat.toDigitsCore]
  | succ fuel ih =>
    intro n acc
    have hd : JSNumber.digitChar (n % base) = Nat.digitChar (n % base) :=
      digitChar_eq _ (Nat.lt_of_lt_of_le (Nat.mod_lt _ h0) h16)
    rw [JSNumber.digitsAux, Nat.toDigitsCore]
    by_cases h : n / base = 0
    · simp [h, hd]
    · simp only [h, beq_iff_eq, String.toList_push, hd, ite_false]
      rw [toDigitsCore_append base fuel (n / base) [Nat.digitChar (n % base)], ih]
      simp

/-- The in-place digit writer gives, for every base up to sixteen and every
number, the string the list based one gave. -/
theorem digitsOf_eq (base : Nat) (h0 : 0 < base) (h16 : base ≤ 16) (n : Nat) :
    JSNumber.digitsOf base n
      = if n == 0 then "0" else String.ofList (Nat.toDigits base n) := by
  rw [JSNumber.digitsOf]
  by_cases h : n = 0
  · simp [h]
  · simp only [h, beq_iff_eq, ite_false]
    apply String.toList_inj.mp
    rw [digitsAux_toList base h0 h16]
    simp [Nat.toDigits]

end JSNumber

end Language.JavaScript.LiteralPrintSpec
