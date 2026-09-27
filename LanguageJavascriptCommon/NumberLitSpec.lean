/-
`Language.JavaScript.JSNumber.parse?` reads a numeric literal *in place*: it
scans the spelling by byte index, skipping the numeric separators where they
are written, so that reading a literal allocates nothing.  It used to build
the list of the characters of the spelling, filter the separators out of it,
and walk the result with `List.span`.

This module proves that the two read the same literal:

* `JSNumber.parse?_eq_parseChars?` : `parse? raw = parseChars? raw`.

It is proved in two steps, through `parseList?` — the same one pass reader as
`parse?`, written on a `List Char`:

* `parse?_eq_parseList?`, proved in `LanguageJavascriptCommon.NumberLitScanSpec`,
  says that scanning by byte index is walking the list of characters;
* `parseList?_eq_parseCharsList?`, proved here, says that the one pass reader
  computes what the `filter`/`span` based one computed.
-/
import LanguageJavascriptCommon.NumberLitScanSpec

set_option autoImplicit false

namespace Language.JavaScript

namespace JSNumber

/-! ## The one pass reader computes what the `span` based one computed -/

/-- The characters of `l` which are not numeric separators — what the reader
which was replaced started by building. -/
def filterSep (l : List Char) : List Char := l.filter (fun c => c != '_')

@[simp] theorem filterSep_nil : filterSep [] = [] := rfl

theorem filterSep_cons (c : Char) (cs : List Char) :
    filterSep (c :: cs) = if c == '_' then filterSep cs else c :: filterSep cs := by
  by_cases h : c = '_'
  · subst h; simp [filterSep]
  · simp [filterSep, h]

theorem filterSep_eq_filter (l : List Char) : filterSep l = l.filter (· ≠ '_') := by
  simp only [filterSep]
  congr 1
  funext c
  by_cases h : c = '_' <;> simp [h]

theorem filterSep_append (l m : List Char) :
    filterSep (l ++ m) = filterSep l ++ filterSep m := by
  simp [filterSep, List.filter_append]

theorem filterSep_reverse (l : List Char) : filterSep l.reverse = (filterSep l).reverse := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, filterSep_append, ih, filterSep_cons]
    by_cases h : c = '_'
    · subst h; simp [filterSep]
    · simp [filterSep, h]

/-- Reading digits from left to right, starting from `acc`. -/
def foldStep (radix : Nat) : Option Nat → List Char → Option Nat
  | acc, [] => acc
  | acc, c :: cs =>
      match acc with
      | none => none
      | some a =>
          match digitVal? c with
          | none => none
          | some d => if d < radix then foldStep radix (some (radix * a + d)) cs else none

@[simp] theorem foldStep_none (radix : Nat) (cs : List Char) :
    foldStep radix none cs = none := by
  cases cs <;> rfl

/-- The value of a list of digits is the fold, once there is a digit. -/
theorem digitsVal?_eq_foldStep (radix : Nat) (cs : List Char) :
    digitsVal? radix cs = if cs.isEmpty then none else foldStep radix (some 0) cs := by
  have hfold : ∀ (l : List Char) (a : Option Nat),
      l.foldl (fun acc c => do
        let x ← acc
        let d ← digitVal? c
        if d < radix then some (radix * x + d) else none) a = foldStep radix a l := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons c cs ih =>
      intro a
      cases a with
      | none => simpa using ih none
      | some x =>
        cases hdv : digitVal? c with
        | none => simpa [foldStep, hdv] using ih none
        | some d =>
          by_cases hlt : d < radix
          · simpa [foldStep, hdv, hlt] using ih (some (radix * x + d))
          · simpa [foldStep, hdv, hlt] using ih none
  cases cs with
  | nil => rfl
  | cons c cs => simpa [digitsVal?] using hfold (c :: cs) (some 0)

/-- Reading digits in place skips the separators, which is reading the
digits of the filtered list. -/
theorem digitsList?_some (radix : Nat) : ∀ (l : List Char) (a : Nat),
    digitsList? radix l (some a) = foldStep radix (some a) (filterSep l) := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons c cs ih =>
    intro a
    simp only [digitsList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih a
    · rw [ite_eq_right hu, ite_eq_right hu]
      cases hdv : digitVal? c with
      | none => simp [foldStep, hdv]
      | some d =>
        by_cases hlt : d < radix
        · simp only [ite_eq_left hlt, foldStep, hdv, Option.getD_some]
          exact ih _
        · simp [foldStep, hdv, hlt]

theorem digitsList?_none (radix : Nat) (l : List Char) :
    digitsList? radix l none = digitsVal? radix (filterSep l) := by
  rw [digitsVal?_eq_foldStep]
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [digitsList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih
    · rw [ite_eq_right hu, ite_eq_right hu]
      cases hdv : digitVal? c with
      | none => simp [foldStep, hdv]
      | some d =>
        by_cases hlt : d < radix
        · simp only [ite_eq_left hlt, Option.getD_none, List.isEmpty_cons, Bool.false_eq_true,
            ite_false, foldStep, hdv]
          rw [digitsList?_some]
        · simp [foldStep, hdv, hlt]

/-- The next character which is not a separator is the head of the filtered
list. -/
theorem nextCharList?_filter : ∀ (l : List Char),
    (nextCharList? l).map (fun r => (r.1, filterSep r.2.2))
      = (match filterSep l with
         | [] => none
         | c :: cs => some (c, cs)) := by
  intro l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [nextCharList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]
      rw [← ih]
      cases nextCharList? cs <;> rfl
    · rw [ite_eq_right hu, ite_eq_right hu]
      rfl

/-! ### The reader which was replaced, restructured

The `match`es of `parseCharsList?` are written as functions below, which is
the same computation — `parseCharsList?_eq_alt` — in a shape the proofs can
work with. -/

/-- Split at the first `e`; the `e` itself is dropped. -/
def splitE : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c == 'e' || c == 'E' then ([], cs)
      else (c :: (splitE cs).1, (splitE cs).2)

/-- Split at the first decimal point; the point itself is dropped. -/
def splitDot : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c == '.' then ([], cs)
      else (c :: (splitDot cs).1, (splitDot cs).2)

/-- The `n` suffix of a `BigInt` literal, at the head of the reversed
spelling. -/
def stripBigList (l : List Char) : Option (List Char) :=
  match l with
  | [] => none
  | c :: rs => if c == 'n' then some rs else none

/-- The exponent of a base ten literal, as the reader which was replaced
read it. -/
def oldExp (cs : List Char) : Option Int :=
  match cs with
  | [] => some 0
  | '-' :: ds => (digitsVal? 10 ds).map (fun n => -(Int.ofNat n))
  | '+' :: ds => (digitsVal? 10 ds).map Int.ofNat
  | ds => (digitsVal? 10 ds).map Int.ofNat

/-- A base ten literal, as the reader which was replaced read it: the tail
of `parseCharsList?`, verbatim. -/
def oldDecimal (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let (mantissaChars, expChars) :=
    match cs.span (fun c => c ≠ 'e' && c ≠ 'E') with
    | (m, []) => (m, ([] : List Char))
    | (m, _ :: e) => (m, e)
  let (intChars, fracChars) :=
    match mantissaChars.span (· ≠ '.') with
    | (i, []) => (i, ([] : List Char))
    | (i, _ :: f) => (i, f)
  if intChars.isEmpty && fracChars.isEmpty then none else
  let digits := intChars ++ fracChars
  let mantissa ← if digits.isEmpty then some 0 else digitsVal? 10 digits
  let e ← oldExp expChars
  if isBig then
    if fracChars.isEmpty && e ≥ 0 then
      some (.bigint .decimal (mantissa * powNat 10 e.toNat))
    else none
  else
    some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The same, with the two `span`s written as `splitE` and `splitDot`. -/
def oldDecimalSplit (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let (mantissaChars, expChars) := splitE cs
  let (intChars, fracChars) := splitDot mantissaChars
  if intChars.isEmpty && fracChars.isEmpty then none else
  let digits := intChars ++ fracChars
  let mantissa ← if digits.isEmpty then some 0 else digitsVal? 10 digits
  let e ← oldExp expChars
  if isBig then
    if fracChars.isEmpty && e ≥ 0 then
      some (.bigint .decimal (mantissa * powNat 10 e.toNat))
    else none
  else
    some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The digits of the literal, as the reader which was replaced read
them. -/
def oldCore (cs : List Char) (isBig : Bool) : Option JSNumber :=
  match cs with
  | '0' :: c :: rest =>
      if c == 'x' || c == 'X' then
        (digitsVal? 16 rest).map (ofRadixDigits isBig .hexadecimal)
      else if c == 'o' || c == 'O' then
        (digitsVal? 8 rest).map (ofRadixDigits isBig .octal)
      else if c == 'b' || c == 'B' then
        (digitsVal? 2 rest).map (ofRadixDigits isBig .binary)
      else if '0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7') then
        (digitsVal? 8 (c :: rest)).map (ofRadixDigits isBig .octal)
      else oldDecimalSplit ('0' :: c :: rest) isBig
  | cs => oldDecimalSplit cs isBig

/-- The reader which was replaced, restructured. -/
def parseCharsAlt? (l : List Char) : Option JSNumber :=
  let cs0 := filterSep l
  let (cs, isBig) :=
    match stripBigList cs0.reverse with
    | some rest => (rest.reverse, true)
    | none => (cs0, false)
  if cs.isEmpty then none else oldCore cs isBig

theorem List.span_loop_eq {α : Type} (p : α → Bool) (as : List α) (acc : List α) :
    List.span.loop p as acc = (acc.reverse ++ as.takeWhile p, as.dropWhile p) := by
  induction as generalizing acc with
  | nil => simp [List.span.loop]
  | cons a as ih =>
    simp [List.span.loop]
    split <;> rename_i h
    · rw [ih (a :: acc)]
      simp [List.takeWhile, List.dropWhile, h]
    · simp [List.takeWhile, List.dropWhile, h]

theorem List.span_eq_takeWhile_dropWhile {α : Type} (p : α → Bool) (l : List α) :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, span_loop_eq]

theorem splitE_eq (cs : List Char) :
    (match cs.span (fun c => c ≠ 'e' && c ≠ 'E') with
     | (m, []) => (m, ([] : List Char))
     | (m, _ :: e) => (m, e)) = splitE cs := by
  simp only [List.span_eq_takeWhile_dropWhile]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = 'e'
    · subst h1; simp [splitE]
    · by_cases h2 : c = 'E'
      · subst h2; simp [splitE]
      · have hp : (decide (c ≠ 'e') && decide (c ≠ 'E')) = true := by simp [h1, h2]
        rw [List.takeWhile_cons, List.dropWhile_cons, ite_eq_left hp, ite_eq_left hp]
        have hsplit : splitE (c :: cs) = (c :: (splitE cs).1, (splitE cs).2) := by
          simp [splitE, h1, h2]
        rw [hsplit, ← ih]
        cases List.dropWhile (fun c => decide (c ≠ 'e') && decide (c ≠ 'E')) cs <;> rfl

theorem splitDot_eq (cs : List Char) :
    (match cs.span (· ≠ '.') with
     | (i, []) => (i, ([] : List Char))
     | (i, _ :: f) => (i, f)) = splitDot cs := by
  simp only [List.span_eq_takeWhile_dropWhile]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases h1 : c = '.'
    · subst h1; simp [splitDot]
    · have hp : decide (c ≠ '.') = true := by simp [h1]
      rw [List.takeWhile_cons, List.dropWhile_cons, ite_eq_left hp, ite_eq_left hp]
      have hsplit : splitDot (c :: cs) = (c :: (splitDot cs).1, (splitDot cs).2) := by
        simp [splitDot, h1]
      rw [hsplit, ← ih]
      cases List.dropWhile (fun c => decide (c ≠ '.')) cs <;> rfl

/-- The body of `parseCharsList?`, verbatim: what it computes once the
separators are gone and the `n` suffix has been read. -/
def parseCharsBody (cs : List Char) (isBig : Bool) : Option JSNumber := do
  let prefixed : Option (NumBase × List Char) :=
    match cs with
    | '0' :: c :: rest =>
        if c == 'x' || c == 'X' then some (.hexadecimal, rest)
        else if c == 'o' || c == 'O' then some (.octal, rest)
        else if c == 'b' || c == 'B' then some (.binary, rest)
        else if '0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7') then
          some (.octal, c :: rest)
        else none
    | _ => none
  match prefixed with
  | some (b, ds) =>
      let v ← digitsVal? b.radix ds
      some (if isBig then .bigint b v else (JSNumber.radix b v).normalize)
  | none => oldDecimal cs isBig

theorem parseCharsList?_eq_body (l : List Char) :
    parseCharsList? l =
      (if (l.filter (· ≠ '_')).isEmpty then none
       else
         let (cs, isBig) :=
           match (l.filter (· ≠ '_')).reverse with
           | 'n' :: rest => (rest.reverse, true)
           | _ => (l.filter (· ≠ '_'), false)
         if cs.isEmpty then none else parseCharsBody cs isBig) := rfl

/-- Reading the `n` suffix off the reversed spelling. -/
theorem strip_match (cs : List Char) :
    (match cs.reverse with
     | 'n' :: rest => (rest.reverse, true)
     | _ => (cs, false))
      = (match stripBigList cs.reverse with
         | some rest => (rest.reverse, true)
         | none => (cs, false)) := by
  cases h : cs.reverse with
  | nil => rfl
  | cons d ds =>
    by_cases hd : d = 'n'
    · subst hd; simp [stripBigList]
    · simp [stripBigList, hd]

theorem oldDecimal_eq_split (cs : List Char) (isBig : Bool) :
    oldDecimal cs isBig = oldDecimalSplit cs isBig := by
  simp only [oldDecimal, oldDecimalSplit, splitE_eq, splitDot_eq]

theorem parseCharsBody_eq_oldCore (cs : List Char) (isBig : Bool) :
    parseCharsBody cs isBig = oldCore cs isBig := by
  match cs with
  | [] => simp only [parseCharsBody, oldCore, oldDecimal_eq_split]
  | [c0] => simp only [parseCharsBody, oldCore, oldDecimal_eq_split]
  | c0 :: c1 :: rest1 =>
    by_cases h0 : c0 = '0'
    · subst h0
      simp only [parseCharsBody, oldCore, oldDecimal_eq_split, NumBase.radix]
      by_cases hx : c1 == 'x' || c1 == 'X'
      · simp only [ite_eq_left hx]; cases digitsVal? 16 rest1 <;> rfl
      · simp only [ite_eq_right hx]
        by_cases ho : c1 == 'o' || c1 == 'O'
        · simp only [ite_eq_left ho]; cases digitsVal? 8 rest1 <;> rfl
        · simp only [ite_eq_right ho]
          by_cases hb : c1 == 'b' || c1 == 'B'
          · simp only [ite_eq_left hb]; cases digitsVal? 2 rest1 <;> rfl
          · simp only [ite_eq_right hb]
            by_cases hoct : '0' ≤ c1 && c1 ≤ '7' && rest1.all (fun d => '0' ≤ d && d ≤ '7')
            · simp only [ite_eq_left hoct]; cases digitsVal? 8 (c1 :: rest1) <;> rfl
            · simp only [ite_eq_right hoct]
    · simp only [parseCharsBody, oldCore, oldDecimal_eq_split, NumBase.radix]
      split <;> rename_i heq <;> simp_all

theorem parseCharsList?_eq_alt (l : List Char) : parseCharsList? l = parseCharsAlt? l := by
  rw [parseCharsList?_eq_body, ← filterSep_eq_filter]
  simp only [parseCharsAlt?, strip_match, parseCharsBody_eq_oldCore]
  cases hf : filterSep l with
  | nil => simp [stripBigList]
  | cons a as => simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]

theorem octal_of_digit {c : Char} {d : Nat} (h : digitVal? c = some d) (hlt : d < 8) :
    ('0' ≤ c && c ≤ '7') = true := by
  have hc : c.toNat = c.val.toNat := rfl
  have e0 : ('0' : Char).toNat = 48 := rfl
  have ea : ('a' : Char).toNat = 97 := rfl
  have eA : ('A' : Char).toNat = 65 := rfl
  have v0 : ('0' : Char).val.toNat = 48 := rfl
  have v7 : ('7' : Char).val.toNat = 55 := rfl
  have v9 : ('9' : Char).val.toNat = 57 := rfl
  have va : ('a' : Char).val.toNat = 97 := rfl
  have vf : ('f' : Char).val.toNat = 102 := rfl
  have vA : ('A' : Char).val.toNat = 65 := rfl
  have vF : ('F' : Char).val.toNat = 70 := rfl
  simp only [digitVal?] at h
  by_cases h9 : ('0' ≤ c && c ≤ '9') = true
  · rw [ite_eq_left h9] at h
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h9 ⊢
    omega
  · rw [ite_eq_right h9] at h
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.le_def,
      UInt32.le_iff_toNat_le, Nat.not_le] at h9
    by_cases hf : ('a' ≤ c && c ≤ 'f') = true
    · rw [ite_eq_left hf] at h
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
        UInt32.le_iff_toNat_le] at hf
      omega
    · rw [ite_eq_right hf] at h
      by_cases hF : ('A' ≤ c && c ≤ 'F') = true
      · rw [ite_eq_left hF] at h
        simp only [Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
          UInt32.le_iff_toNat_le] at hF
        omega
      · rw [ite_eq_right hF] at h
        exact absurd h (by simp)

theorem digit_of_octal {c : Char} (h : ('0' ≤ c && c ≤ '7') = true) :
    ∃ d, digitVal? c = some d ∧ d < 8 := by
  have hc : c.toNat = c.val.toNat := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
    show ('0' : Char).val.toNat = 48 from rfl, show ('7' : Char).val.toNat = 55 from rfl] at h
  have h9 : ('0' ≤ c && c ≤ '9') = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
      show ('0' : Char).val.toNat = 48 from rfl, show ('9' : Char).val.toNat = 57 from rfl]
    omega
  refine ⟨c.toNat - '0'.toNat, ?_, ?_⟩
  · simp [digitVal?, h9]
  · simp only [hc, show ('0' : Char).toNat = 48 from rfl]
    omega

theorem foldStep8_isSome : ∀ (cs : List Char) (a : Nat),
    (foldStep 8 (some a) cs).isSome = cs.all (fun d => '0' ≤ d && d ≤ '7') := by
  intro cs
  induction cs with
  | nil => intro a; rfl
  | cons c cs ih =>
    intro a
    simp only [foldStep, List.all_cons]
    cases hdv : digitVal? c with
    | none =>
      have hc : ('0' ≤ c && c ≤ '7') = false := by
        by_cases hcon : ('0' ≤ c && c ≤ '7') = true
        · have ⟨d, hd, _⟩ := digit_of_octal hcon
          rw [hdv] at hd; cases hd
        · cases h : ('0' ≤ c && c ≤ '7')
          · rfl
          · contradiction
      simp [hc]
    | some d =>
      by_cases hlt : d < 8
      · have hc : ('0' ≤ c && c ≤ '7') = true := octal_of_digit hdv hlt
        simp only [ite_eq_left hlt, hc, Bool.true_and]
        exact ih _
      · have hc : ('0' ≤ c && c ≤ '7') = false := by
          by_cases hcon : ('0' ≤ c && c ≤ '7') = true
          · have ⟨d', hd', hlt'⟩ := digit_of_octal hcon
            rw [hdv, Option.some.injEq] at hd'
            omega
          · cases h : ('0' ≤ c && c ≤ '7')
            · rfl
            · contradiction
        simp [hlt, hc]

theorem digitsVal?_octal_guard (c : Char) (rest : List Char) :
    (digitsVal? 8 (c :: rest)).isSome
      = ('0' ≤ c && c ≤ '7' && rest.all (fun d => '0' ≤ d && d ≤ '7')) := by
  rw [digitsVal?_eq_foldStep]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [foldStep8_isSome]
  simp [List.all_cons]

/-- Looking for the `n` suffix while skipping the separators is looking for
it in the filtered list. -/
theorem bigSuffixAux_filter : ∀ (r : List Char),
    (bigSuffixAux r).map filterSep = stripBigList (filterSep r) := by
  intro r
  induction r with
  | nil => rfl
  | cons c cs ih =>
    simp only [bigSuffixAux, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu]; exact ih
    · rw [ite_eq_right hu, ite_eq_right hu]
      by_cases hn : c == 'n'
      · rw [ite_eq_left hn]; simp [stripBigList, hn]
      · rw [ite_eq_right hn]; simp [stripBigList, hn]

/-- Reading the `n` suffix in place, then filtering, is filtering, then
reading the `n` suffix. -/
theorem bigSuffixList_filter (l : List Char) :
    (filterSep (bigSuffixList l).1, (bigSuffixList l).2)
      = (match stripBigList (filterSep l).reverse with
         | some rest => (rest.reverse, true)
         | none => (filterSep l, false)) := by
  rw [show (filterSep l).reverse = filterSep l.reverse from (filterSep_reverse l).symm,
    ← bigSuffixAux_filter]
  simp only [bigSuffixList]
  cases h : bigSuffixAux l.reverse with
  | none => simp
  | some rs => simp [filterSep_reverse]

theorem oldExp_cons (c : Char) (ds : List Char) (hm : ¬ c = '-') (hp : ¬ c = '+') :
    oldExp (c :: ds) = (digitsVal? 10 (c :: ds)).map Int.ofNat := by
  unfold oldExp
  split <;> rename_i heq <;> simp_all

/-- Reading the exponent in place is reading it off the filtered list. -/
theorem expList?_eq (l : List Char) : expList? l = oldExp (filterSep l) := by
  have hf := nextCharList?_filter l
  cases h : nextCharList? l with
  | none =>
    rw [h] at hf
    simp only [Option.map_none] at hf
    cases hfl : filterSep l with
    | nil => simp [expList?, h, oldExp]
    | cons a as => rw [hfl] at hf; simp at hf
  | some r =>
    obtain ⟨c, cons, cs⟩ := r
    rw [h] at hf
    simp only [Option.map_some] at hf
    cases hfl : filterSep l with
    | nil => rw [hfl] at hf; simp at hf
    | cons a as =>
      rw [hfl] at hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, hcs⟩ := hf
      simp only [expList?, h, digitsList?_none, hcs, hfl]
      by_cases hm : c = '-'
      · subst hm; simp [oldExp]
      · by_cases hp : c = '+'
        · subst hp; simp [oldExp]
        · rw [ite_eq_right (by simpa using hm), ite_eq_right (by simpa using hp), oldExp_cons c as hm hp]

/-- The digits of the integer part of a mantissa, as the reader which was
replaced split them off: nothing at all once the decimal point has been
read. -/
def oldMantI (cs : List Char) (dot : Bool) : List Char :=
  if dot then [] else (splitDot (splitE cs).1).1

/-- The digits of the fractional part of a mantissa, as the reader which was
replaced split them off: everything, once the decimal point has been read. -/
def oldMantF (cs : List Char) (dot : Bool) : List Char :=
  if dot then (splitE cs).1 else (splitDot (splitE cs).1).2

/-- The characters the mantissa reader consumed do not matter to what the
value it read is: they are dropped. -/
theorem map_consumed (c : Char) (X : Option (Nat × Nat × List Char × List Char)) :
    (X.map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))).map
        (fun r => (r.1, r.2.1, filterSep r.2.2.2))
      = X.map (fun r => (r.1, r.2.1, filterSep r.2.2.2)) := by
  cases X <;> rfl

/-- Reading the mantissa in place, skipping the separators, is reading it
off the filtered list. -/
theorem mantissaList?_filter : ∀ (cs : List Char) (m nd nf : Nat) (dot : Bool),
    (mantissaList? cs m nd nf dot).map (fun r => (r.1, r.2.1, filterSep r.2.2.2))
      = (if nd == 0 && (oldMantI (filterSep cs) dot ++ oldMantF (filterSep cs) dot).isEmpty then
           none
         else
           (foldStep 10 (some m)
               (oldMantI (filterSep cs) dot ++ oldMantF (filterSep cs) dot)).map
             (fun m' => (m', nf + (oldMantF (filterSep cs) dot).length,
               (splitE (filterSep cs)).2))) := by
  intro cs
  induction cs with
  | nil =>
    intro m nd nf dot
    simp only [mantissaList?, filterSep_nil, oldMantI, oldMantF, splitE, splitDot]
    cases dot <;> by_cases hnd : nd == 0 <;> simp [hnd, foldStep]
  | cons c cs ih =>
    intro m nd nf dot
    simp only [mantissaList?, filterSep_cons]
    by_cases hu : c == '_'
    · rw [ite_eq_left hu, ite_eq_left hu, map_consumed]
      exact ih m nd nf dot
    · rw [ite_eq_right hu, ite_eq_right hu]
      by_cases hdot : c == '.'
      · have hc : c = '.' := by simpa using hdot
        subst hc
        rw [ite_eq_left hdot]
        have hsE : splitE ('.' :: filterSep cs) = ('.' :: (splitE (filterSep cs)).1,
            (splitE (filterSep cs)).2) := by simp [splitE]
        cases dot with
        | true =>
          rw [ite_eq_left rfl]
          simp [oldMantI, oldMantF, hsE, foldStep, show digitVal? '.' = none from rfl]
        | false =>
          rw [ite_eq_right (by simp), map_consumed, ih m nd nf true]
          have h1 : oldMantI ('.' :: filterSep cs) false = oldMantI (filterSep cs) true := by
            simp [oldMantI, hsE, splitDot]
          have h2 : oldMantF ('.' :: filterSep cs) false = oldMantF (filterSep cs) true := by
            simp [oldMantF, hsE, splitDot]
          rw [h1, h2]
          simp only [hsE]
      · rw [ite_eq_right hdot]
        have hcd : ¬ c = '.' := by simpa using hdot
        by_cases he : c == 'e' || c == 'E'
        · rw [ite_eq_left he]
          have hsE : splitE (c :: filterSep cs) = ([], filterSep cs) := by simp [splitE, he]
          by_cases hnd : nd == 0
          · simp [hnd, oldMantI, oldMantF, hsE, splitDot]
          · simp [hnd, oldMantI, oldMantF, hsE, splitDot, foldStep]
        · rw [ite_eq_right he]
          have hsE : splitE (c :: filterSep cs) = (c :: (splitE (filterSep cs)).1,
              (splitE (filterSep cs)).2) := by simp [splitE, he]
          have hsD : splitDot (c :: (splitE (filterSep cs)).1)
              = (c :: (splitDot (splitE (filterSep cs)).1).1,
                 (splitDot (splitE (filterSep cs)).1).2) := by simp [splitDot, hcd]
          have hIt : oldMantI (c :: filterSep cs) true = [] := by simp [oldMantI]
          have hIt' : oldMantI (filterSep cs) true = [] := by simp [oldMantI]
          have hFt : oldMantF (c :: filterSep cs) true
              = c :: oldMantF (filterSep cs) true := by simp [oldMantF, hsE]
          have hIf : oldMantI (c :: filterSep cs) false
              = c :: oldMantI (filterSep cs) false := by simp [oldMantI, hsE, hsD]
          have hFf : oldMantF (c :: filterSep cs) false
              = oldMantF (filterSep cs) false := by simp [oldMantF, hsE, hsD]
          cases hdv : digitVal? c with
          | none =>
            dsimp only
            cases dot with
            | true =>
              rw [hIt, hFt]
              simp [foldStep, hdv, hsE]
            | false =>
              rw [hIf, hFf]
              simp [foldStep, hdv, hsE]
          | some d =>
            dsimp only
            by_cases hlt : d < 10
            · rw [ite_eq_left hlt, map_consumed,
                ih (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot]
              cases dot with
              | true =>
                rw [hIt, hIt', hFt]
                simp only [hsE, List.nil_append, List.isEmpty_cons, Bool.and_false,
                  Bool.false_eq_true, ite_false, foldStep, hdv, ite_eq_left hlt, List.length_cons]
                match foldStep 10 (some (10 * m + d)) (oldMantF (filterSep cs) true) with
                | none => simp
                | some v => simp; omega
              | false =>
                rw [hIf, hFf]
                simp only [hsE, List.cons_append, List.isEmpty_cons, Bool.and_false,
                  Bool.false_eq_true, ite_false, foldStep, hdv, ite_eq_left hlt]
                simp
            · rw [ite_eq_right hlt]
              cases dot with
              | true =>
                rw [hIt, hFt]
                simp [foldStep, hdv, hlt, hsE]
              | false =>
                rw [hIf, hFf]
                simp [foldStep, hdv, hlt, hsE]

/-- A base ten literal, as the reader which was replaced read it, with the
two splits named. -/
def oldDecimalCore (cs : List Char) (isBig : Bool) : Option JSNumber :=
  if (oldMantI cs false ++ oldMantF cs false).isEmpty then none
  else
    match foldStep 10 (some 0) (oldMantI cs false ++ oldMantF cs false) with
    | none => none
    | some mantissa =>
        match oldExp (splitE cs).2 with
        | none => none
        | some e =>
            if isBig then
              (if (oldMantF cs false).isEmpty && e ≥ 0 then
                 some (.bigint .decimal (mantissa * powNat 10 e.toNat))
               else none)
            else some (JSNumber.decimal mantissa (e - Int.ofNat (oldMantF cs false).length)).normalize

/-- A concatenation is empty exactly when both of its parts are. -/
theorem isEmpty_append (l m : List Char) :
    (l ++ m).isEmpty = (l.isEmpty && m.isEmpty) := by
  cases l <;> simp

theorem oldDecimalSplit_eq_core (cs : List Char) (isBig : Bool) :
    oldDecimalSplit cs isBig = oldDecimalCore cs isBig := by
  simp only [oldDecimalSplit, oldDecimalCore, oldMantI, oldMantF, Bool.false_eq_true, ite_false,
    isEmpty_append]
  by_cases h1 : ((splitDot (splitE cs).1).1.isEmpty && (splitDot (splitE cs).1).2.isEmpty) = true
  · rw [ite_eq_left h1, ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_right h1]
    have h2 : ((splitDot (splitE cs).1).1 ++ (splitDot (splitE cs).1).2).isEmpty = false := by
      simp only [isEmpty_append, Bool.and_eq_true] at h1 ⊢
      simpa using h1
    rw [ite_eq_right h1, digitsVal?_eq_foldStep, ite_eq_right (by rw [h2]; simp)]
    cases foldStep 10 (some 0) ((splitDot (splitE cs).1).1 ++ (splitDot (splitE cs).1).2) with
    | none => rfl
    | some v => cases oldExp (splitE cs).2 <;> rfl

/-- Reading a base ten literal in place, skipping the separators, is reading
it off the filtered list. -/
theorem parseDecimalList?_filter (mid : List Char) (isBig : Bool) :
    parseDecimalList? mid isBig = oldDecimalCore (filterSep mid) isBig := by
  have hm := mantissaList?_filter mid 0 0 0 false
  simp only [beq_self_eq_true, Bool.true_and, Nat.zero_add] at hm
  cases hml : mantissaList? mid 0 0 0 false with
  | none =>
    rw [hml] at hm
    simp only [Option.map_none] at hm
    simp only [parseDecimalList?, hml, oldDecimalCore]
    by_cases hE : (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false).isEmpty = true
    · rw [ite_eq_left hE]
    · rw [ite_eq_right hE] at hm ⊢
      cases hfs : foldStep 10 (some 0)
          (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false) with
      | none => rfl
      | some v => rw [hfs] at hm; simp at hm
  | some r =>
    obtain ⟨m, nf, cons, rest⟩ := r
    rw [hml] at hm
    simp only [Option.map_some] at hm
    by_cases hE : (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false).isEmpty = true
    · rw [ite_eq_left hE] at hm; simp at hm
    · rw [ite_eq_right hE] at hm
      cases hfs : foldStep 10 (some 0)
          (oldMantI (filterSep mid) false ++ oldMantF (filterSep mid) false) with
      | none => rw [hfs] at hm; simp at hm
      | some v =>
        rw [hfs] at hm
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨hm1, hm2, hm3⟩ := hm
        subst hm1
        subst hm2
        simp only [parseDecimalList?, hml, oldDecimalCore, ite_eq_right hE, hfs, expList?_eq, hm3]
        cases oldExp (splitE (filterSep mid)).2 with
        | none => rfl
        | some e =>
          have hlen : ((oldMantF (filterSep mid) false).length == 0)
              = (oldMantF (filterSep mid) false).isEmpty := by
            cases oldMantF (filterSep mid) false <;> simp
          cases isBig <;> simp [hlen, ge_iff_le]

/-- The body of `parseList?`, once the `n` suffix has been read. -/
def parseListCore (mid : List Char) (isBig : Bool) : Option JSNumber :=
  match nextCharList? mid with
  | none => none
  | some (c0, _, rest0) =>
      if c0 == '0' then
        match nextCharList? rest0 with
        | none => parseDecimalList? mid isBig
        | some (c1, _, rest1) =>
            let base? : Option NumBase :=
              if c1 == 'x' || c1 == 'X' then some .hexadecimal
              else if c1 == 'o' || c1 == 'O' then some .octal
              else if c1 == 'b' || c1 == 'B' then some .binary
              else none
            match base? with
            | some b => (digitsList? b.radix rest1 none).map (ofRadixDigits isBig b)
            | none =>
                match digitsList? 8 rest0 none with
                | some v => some (ofRadixDigits isBig .octal v)
                | none => parseDecimalList? mid isBig
      else parseDecimalList? mid isBig

theorem parseList?_eq_core (l : List Char) :
    parseList? l = parseListCore (bigSuffixList l).1 (bigSuffixList l).2 := rfl

/-- The one pass reader, on the digits of the literal, computes what the
reader which was replaced computed on the filtered ones. -/
theorem parseListCore_eq (mid : List Char) (isBig : Bool) :
    parseListCore mid isBig =
      (if (filterSep mid).isEmpty then none else oldCore (filterSep mid) isBig) := by
  have h0 := nextCharList?_filter mid
  cases hn : nextCharList? mid with
  | none =>
    rw [hn] at h0
    simp only [Option.map_none] at h0
    have hf : filterSep mid = [] := by
      cases hfl : filterSep mid with
      | nil => rfl
      | cons a as => rw [hfl] at h0; simp at h0
    simp only [parseListCore, hn, hf, List.isEmpty_nil, ite_true]
  | some r0 =>
    obtain ⟨c0, cons0, rest0⟩ := r0
    rw [hn] at h0
    simp only [Option.map_some] at h0
    have hf : filterSep mid = c0 :: filterSep rest0 := by
      cases hfl : filterSep mid with
      | nil => rw [hfl] at h0; simp at h0
      | cons a as =>
        rw [hfl] at h0
        simp only [Option.some.injEq, Prod.mk.injEq] at h0
        obtain ⟨rfl, h⟩ := h0
        rw [h]
    rw [hf]
    simp only [parseListCore, hn, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    by_cases hz : c0 == '0'
    · have hc0 : c0 = '0' := by simpa using hz
      subst hc0
      rw [ite_eq_left hz]
      have h1 := nextCharList?_filter rest0
      cases hn1 : nextCharList? rest0 with
      | none =>
        rw [hn1] at h1
        simp only [Option.map_none] at h1
        have hf1 : filterSep rest0 = [] := by
          cases hfl : filterSep rest0 with
          | nil => rfl
          | cons a as => rw [hfl] at h1; simp at h1
        rw [hf1, parseDecimalList?_filter, hf, hf1, oldCore, oldDecimalSplit_eq_core]
        intro c rest hcon
        simp at hcon
      | some r1 =>
        obtain ⟨c1, cons1, rest1⟩ := r1
        rw [hn1] at h1
        simp only [Option.map_some] at h1
        have hf1 : filterSep rest0 = c1 :: filterSep rest1 := by
          cases hfl : filterSep rest0 with
          | nil => rw [hfl] at h1; simp at h1
          | cons a as =>
            rw [hfl] at h1
            simp only [Option.some.injEq, Prod.mk.injEq] at h1
            obtain ⟨rfl, h⟩ := h1
            rw [h]
        rw [hf1]
        simp only [oldCore, NumBase.radix, digitsList?_none, hf1]
        by_cases hx : c1 == 'x' || c1 == 'X'
        · simp only [ite_eq_left hx]
        · simp only [ite_eq_right hx]
          by_cases ho : c1 == 'o' || c1 == 'O'
          · simp only [ite_eq_left ho]
          · simp only [ite_eq_right ho]
            by_cases hb : c1 == 'b' || c1 == 'B'
            · simp only [ite_eq_left hb]
            · simp only [ite_eq_right hb]
              have hg := digitsVal?_octal_guard c1 (filterSep rest1)
              cases hdv : digitsVal? 8 (c1 :: filterSep rest1) with
              | some v =>
                rw [hdv] at hg
                simp only [Option.isSome_some] at hg
                rw [ite_eq_left hg.symm]
                rfl
              | none =>
                rw [hdv] at hg
                simp only [Option.isSome_none] at hg
                rw [ite_eq_right (by rw [← hg]; simp), parseDecimalList?_filter, hf, hf1,
                  oldDecimalSplit_eq_core]
    · rw [ite_eq_right hz, parseDecimalList?_filter, hf]
      have hoc : oldCore (c0 :: filterSep rest0) isBig
          = oldDecimalSplit (c0 :: filterSep rest0) isBig := by
        unfold oldCore
        split <;> rename_i heq <;> simp_all
      rw [hoc, oldDecimalSplit_eq_core]

theorem parseList?_eq_parseCharsList? (l : List Char) : parseList? l = parseCharsList? l := by
  rw [parseCharsList?_eq_alt, parseList?_eq_core, parseListCore_eq]
  have h := bigSuffixList_filter l
  simp only [parseCharsAlt?]
  rw [← h]

/-- The in-place reader reads exactly what the reader it replaced read. -/
theorem parse?_eq_parseChars? (raw : String) : parse? raw = parseChars? raw := by
  rw [parse?_eq_parseList?, parseChars?, parseList?_eq_parseCharsList?]

end JSNumber

end Language.JavaScript
