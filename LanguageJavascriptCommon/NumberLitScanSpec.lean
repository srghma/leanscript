/-
`Language.JavaScript.JSNumber.parse?` reads a numeric literal *in place*: it
scans the spelling by byte index, skipping the numeric separators where they
are written.  This module transcribes that reader on a `List Char`, as
`JSNumber.parseList?`, transcribes the reader which was replaced, as
`JSNumber.parseChars?`, and proves

* `JSNumber.parse?_eq_parseList?` : scanning the spelling by byte index is
  walking the list of its characters.

This is where the byte positions are reasoned about, with the `ByteScan`
toolkit of `LanguageJavascriptCommon.RegExpLitSpec`.  That the one pass reader
computes what the reader it replaced computed is proved in
`LanguageJavascriptCommon.NumberLitSpec`, which reads this module.
-/
import LanguageJavascriptCommon.RegExpLitSpec

set_option autoImplicit false

namespace Language.JavaScript

open ByteScan

namespace ByteScan

/-- The number of bytes a list of characters occupies does not depend on
their order. -/
theorem blen_reverse (l : List Char) : blen l.reverse = blen l := by
  induction l with
  | nil => rfl
  | cons c cs ih => simp [blen_append, ih, Nat.add_comm]

theorem utf8PrevAux_append (c : Char) (suf : List Char) : ∀ (pre : List Char) (i : Nat),
    String.Pos.Raw.utf8PrevAux (pre ++ c :: suf) ⟨i⟩ ⟨i + blen pre + c.utf8Size⟩
      = ⟨i + blen pre⟩ := by
  intro pre
  induction pre with
  | nil =>
    intro i
    have hle : (⟨i + 0 + c.utf8Size⟩ : String.Pos.Raw) ≤ (⟨i⟩ : String.Pos.Raw) + c := by
      simp [String.Pos.Raw.le_iff]
    simp only [List.nil_append, String.Pos.Raw.utf8PrevAux, blen_nil, ite_eq_left hle]
    simp
  | cons d ds ih =>
    intro i
    have hdpos := d.utf8Size_pos
    have hcpos := c.utf8Size_pos
    have hnle : ¬ ((⟨i + blen (d :: ds) + c.utf8Size⟩ : String.Pos.Raw)
        ≤ (⟨i⟩ : String.Pos.Raw) + d) := by
      simp only [String.Pos.Raw.le_iff, String.Pos.Raw.byteIdx_add_char, blen_cons]
      omega
    simp only [List.cons_append, String.Pos.Raw.utf8PrevAux, ite_eq_right hnle]
    have hadd : (⟨i⟩ : String.Pos.Raw) + d = ⟨i + d.utf8Size⟩ := rfl
    rw [hadd, show i + blen (d :: ds) + c.utf8Size
        = (i + d.utf8Size) + blen ds + c.utf8Size by simp only [blen_cons]; omega,
      ih (i + d.utf8Size)]
    simp only [blen_cons, String.Pos.Raw.mk.injEq]
    omega

/-- Stepping back from the position which follows `pre ++ [c]`. -/
theorem prev_eq {s : String} {pre suf : List Char} {c : Char}
    (h : s.toList = pre ++ c :: suf) :
    String.Pos.Raw.prev s ⟨blen pre + c.utf8Size⟩ = ⟨blen pre⟩ := by
  have : String.Pos.Raw.prev s ⟨blen pre + c.utf8Size⟩
      = String.Pos.Raw.utf8PrevAux (pre ++ c :: suf) ⟨0⟩ ⟨0 + blen pre + c.utf8Size⟩ := by
    rw [show 0 + blen pre + c.utf8Size = blen pre + c.utf8Size by omega, ← h]
    rfl
  rw [this, utf8PrevAux_append]
  simp

end ByteScan

namespace JSNumber

/-! ## The one pass reader, on a list of characters

Each function below is the list version of the scanner of the same name:
what the scanner does between two byte indices, it does on the characters
between them. -/

/-- The next character which is not a numeric separator, the characters
consumed to reach it (the separators and the character itself), and what
follows it. -/
def nextCharList? : List Char → Option (Char × List Char × List Char)
  | [] => none
  | c :: cs =>
      if c == '_' then (nextCharList? cs).map (fun r => (r.1, c :: r.2.1, r.2.2))
      else some (c, [c], cs)

/-- The value of the digits of `l` in base `radix`, `acc` being the value of
the digits read so far. -/
def digitsList? (radix : Nat) : List Char → Option Nat → Option Nat
  | [], acc => acc
  | c :: cs, acc =>
      if c == '_' then digitsList? radix cs acc
      else
        match digitVal? c with
        | none => none
        | some d =>
            if d < radix then digitsList? radix cs (some (radix * acc.getD 0 + d)) else none

/-- The mantissa of a base ten literal: its value, how many of its digits
are after the decimal point, the characters consumed (up to and including
the `e` which starts the exponent) and the characters which follow. -/
def mantissaList? : List Char → Nat → Nat → Nat → Bool →
    Option (Nat × Nat × List Char × List Char)
  | [], m, nd, nf, _ => if nd == 0 then none else some (m, nf, [], [])
  | c :: cs, m, nd, nf, dot =>
      if c == '_' then
        (mantissaList? cs m nd nf dot).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
      else if c == '.' then
        if dot then none
        else (mantissaList? cs m nd nf true).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
      else if c == 'e' || c == 'E' then
        if nd == 0 then none else some (m, nf, [c], cs)
      else
        match digitVal? c with
        | some d =>
            if d < 10 then
              (mantissaList? cs (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot).map
                (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
            else none
        | none => none

/-- The exponent written by `l`: a sign and at least one digit, or nothing
at all, which is an exponent of zero. -/
def expList? (l : List Char) : Option Int :=
  match nextCharList? l with
  | none => some 0
  | some (c, _, cs) =>
      if c == '-' then (digitsList? 10 cs none).map (fun n => -(Int.ofNat n))
      else if c == '+' then (digitsList? 10 cs none).map Int.ofNat
      else (digitsList? 10 l none).map Int.ofNat

/-- The `n` suffix of a `BigInt` literal, looked for at the end of the
reversed spelling. -/
def bigSuffixAux : List Char → Option (List Char)
  | [] => none
  | c :: rs => if c == '_' then bigSuffixAux rs else if c == 'n' then some rs else none

/-- The characters which spell the digits of the literal, and whether it is
a `BigInt` one. -/
def bigSuffixList (l : List Char) : List Char × Bool :=
  match bigSuffixAux l.reverse with
  | some rs => (rs.reverse, true)
  | none => (l, false)

/-- A base ten literal, written by `mid`. -/
def parseDecimalList? (mid : List Char) (isBig : Bool) : Option JSNumber :=
  match mantissaList? mid 0 0 0 false with
  | none => none
  | some (m, nf, _, rest) =>
      match expList? rest with
      | none => none
      | some e =>
          if isBig then
            if nf == 0 && 0 ≤ e then some (.bigint .decimal (m * powNat 10 e.toNat)) else none
          else some (JSNumber.decimal m (e - Int.ofNat nf)).normalize

/-- The one pass reader, on a list of characters: exactly what `parse?`
does, with the byte indices replaced by the characters they point at. -/
def parseList? (l : List Char) : Option JSNumber :=
  let (mid, isBig) := bigSuffixList l
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

/-! ## The reader which was replaced -/

/-- The value of a list of digits in base `radix`; `none` if the list is
empty, or holds a character which is not a digit of that base. -/
def digitsVal? (radix : Nat) : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => do
      let a ← acc
      let d ← digitVal? c
      if d < radix then some (radix * a + d) else none) (some 0)

/-- The reader a numeric literal used to be read with: the spelling becomes
a list of characters, the numeric separators are filtered out of it, and the
result is split with `List.span`. -/
def parseCharsList? (l : List Char) : Option JSNumber := do
  let cs := (l.filter (· ≠ '_'))
  if cs.isEmpty then none else
  let (cs, isBig) :=
    match cs.reverse with
    | 'n' :: rest => (rest.reverse, true)
    | _ => (cs, false)
  if cs.isEmpty then none else
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
  | none =>
      -- a base ten literal: `intPart [. fracPart] [e [+-] expPart]`
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
      let expValue : Option Int :=
        match expChars with
        | [] => some 0
        | '-' :: ds => (digitsVal? 10 ds).map (fun n => -(Int.ofNat n))
        | '+' :: ds => (digitsVal? 10 ds).map Int.ofNat
        | ds => (digitsVal? 10 ds).map Int.ofNat
      let e ← expValue
      if isBig then
        if fracChars.isEmpty && e ≥ 0 then
          some (.bigint .decimal (mantissa * powNat 10 e.toNat))
        else none
      else
        some (JSNumber.decimal mantissa (e - Int.ofNat fracChars.length)).normalize

/-- The reader a numeric literal used to be read with. -/
def parseChars? (raw : String) : Option JSNumber := parseCharsList? raw.toList

/-! ## Scanning by byte index is walking the list of characters -/

/-- What `nextCharList?` consumes is a prefix of its input. -/
theorem nextCharList?_split : ∀ (l : List Char) (c : Char) (cons rest : List Char),
    nextCharList? l = some (c, cons, rest) → l = cons ++ rest := by
  intro l
  induction l with
  | nil => intro c cons rest h; simp [nextCharList?] at h
  | cons d ds ih =>
    intro c cons rest h
    simp only [nextCharList?] at h
    by_cases hd : d == '_'
    · rw [ite_eq_left hd] at h
      cases hrec : nextCharList? ds with
      | none => rw [hrec] at h; simp at h
      | some r =>
        rw [hrec] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hcons, hrest⟩ := h
        subst hcons; subst hrest
        have := ih r.1 r.2.1 r.2.2 (by rw [hrec])
        simpa using this
    · rw [ite_eq_right hd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hc, hcons, hrest⟩ := h
      subst hc; subst hcons; subst hrest
      rfl

theorem nextChar?_eq (raw : String) : ∀ (suf pre post : List Char) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    nextChar? raw (blen pre + blen suf) fuel ⟨blen pre⟩
      = (nextCharList? suf).map (fun r => (r.1, (⟨blen pre + blen r.2.1⟩ : String.Pos.Raw))) := by
  intro suf
  induction suf with
  | nil =>
    intro pre post fuel _ _
    cases fuel <;> simp [nextChar?, nextCharList?]
  | cons c cs ih =>
    intro pre post fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      simp only [nextChar?, ite_eq_right hstop, hget, hnext, nextCharList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu]
        have hrec := ih (pre ++ [c]) post n (by rw [hs]; simp) (by simp at hfuel; omega)
        have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
          simp only [blen_append, blen_cons, blen_nil]; omega
        rw [hstop'] at hrec
        rw [hrec]
        cases nextCharList? cs with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
            String.Pos.Raw.mk.injEq, blen_append, blen_cons, blen_nil]
          exact ⟨trivial, by omega⟩
      · rw [ite_eq_right hu, ite_eq_right hu]
        simp only [Option.map_some,
          blen_append, blen_cons, blen_nil]

theorem digitsFrom?_eq (raw : String) : ∀ (suf pre post : List Char) (radix : Nat)
    (acc : Option Nat) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    digitsFrom? raw (blen pre + blen suf) radix fuel ⟨blen pre⟩ acc
      = digitsList? radix suf acc := by
  intro suf
  induction suf with
  | nil =>
    intro pre post radix acc fuel _ _
    cases fuel <;> simp [digitsFrom?, digitsList?]
  | cons c cs ih =>
    intro pre post radix acc fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
        simp only [blen_append, blen_cons, blen_nil]; omega
      have hrec : ∀ (a : Option Nat),
          digitsFrom? raw (blen pre + blen (c :: cs)) radix n ⟨blen (pre ++ [c])⟩ a
            = digitsList? radix cs a := by
        intro a
        have := ih (pre ++ [c]) post radix a n (by rw [hs]; simp) (by simp at hfuel; omega)
        rwa [hstop'] at this
      simp only [digitsFrom?, ite_eq_right hstop, hget, hnext, digitsList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu]; exact hrec acc
      · rw [ite_eq_right hu, ite_eq_right hu]
        cases hdv : digitVal? c with
        | none => rfl
        | some d =>
          by_cases hlt : d < radix
          · simp only [ite_eq_left hlt]; exact hrec _
          · simp only [ite_eq_right hlt]

/-- What `mantissaList?` consumes is a prefix of its input. -/
theorem mantissaList?_split : ∀ (l : List Char) (m nd nf : Nat) (dot : Bool)
    (m' nf' : Nat) (cons rest : List Char),
    mantissaList? l m nd nf dot = some (m', nf', cons, rest) → l = cons ++ rest := by
  intro l
  induction l with
  | nil =>
    intro m nd nf dot m' nf' cons rest h
    simp only [mantissaList?] at h
    by_cases hnd : nd == 0
    · rw [ite_eq_left hnd] at h; simp at h
    · rw [ite_eq_right hnd] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, hcons, hrest⟩ := h
      subst hcons; subst hrest; rfl
  | cons c cs ih =>
    intro m nd nf dot m' nf' cons rest h
    -- every branch but the `e` either prepends `c` to what is consumed, or fails
    have step : ∀ (a b e : Nat) (dt : Bool),
        (mantissaList? cs a b e dt).map (fun r => (r.1, r.2.1, c :: r.2.2.1, r.2.2.2))
          = some (m', nf', cons, rest) → c :: cs = cons ++ rest := by
      intro a b e dt hmap
      cases hrec : mantissaList? cs a b e dt with
      | none => rw [hrec] at hmap; simp at hmap
      | some r =>
        rw [hrec] at hmap
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨-, -, hcons, hrest⟩ := hmap
        subst hcons; subst hrest
        have := ih a b e dt r.1 r.2.1 r.2.2.1 r.2.2.2 (by rw [hrec])
        simpa using this
    simp only [mantissaList?] at h
    by_cases hu : c == '_'
    · rw [ite_eq_left hu] at h; exact step m nd nf dot h
    · rw [ite_eq_right hu] at h
      by_cases hdot : c == '.'
      · rw [ite_eq_left hdot] at h
        by_cases hd : dot
        · rw [ite_eq_left hd] at h; simp at h
        · rw [ite_eq_right hd] at h; exact step m nd nf true h
      · rw [ite_eq_right hdot] at h
        by_cases he : c == 'e' || c == 'E'
        · rw [ite_eq_left he] at h
          by_cases hnd : nd == 0
          · rw [ite_eq_left hnd] at h; simp at h
          · rw [ite_eq_right hnd] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, -, hcons, hrest⟩ := h
            subst hcons; subst hrest; rfl
        · rw [ite_eq_right he] at h
          cases hdv : digitVal? c with
          | none => simp [hdv] at h
          | some d =>
            simp only [hdv] at h
            by_cases hlt : d < 10
            · rw [ite_eq_left hlt] at h
              exact step (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot h
            · rw [ite_eq_right hlt] at h; simp at h

theorem mantissaFrom?_eq (raw : String) : ∀ (suf pre post : List Char)
    (m nd nf : Nat) (dot : Bool) (fuel : Nat),
    raw.toList = pre ++ suf ++ post → suf.length ≤ fuel →
    mantissaFrom? raw (blen pre + blen suf) fuel ⟨blen pre⟩ m nd nf dot
      = (mantissaList? suf m nd nf dot).map
          (fun r => (r.1, r.2.1, (⟨blen pre + blen r.2.2.1⟩ : String.Pos.Raw))) := by
  intro suf
  induction suf with
  | nil =>
    intro pre post m nd nf dot fuel _ _
    cases fuel <;> (cases hnd : nd == 0 <;> simp [mantissaFrom?, mantissaList?, hnd])
  | cons c cs ih =>
    intro pre post m nd nf dot fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hstop : ¬ (blen pre + blen (c :: cs) ≤ blen pre) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hs' : raw.toList = pre ++ c :: (cs ++ post) := by rw [hs]; simp
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs'
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs'
      have hstop' : blen (pre ++ [c]) + blen cs = blen pre + blen (c :: cs) := by
        simp only [blen_append, blen_cons, blen_nil]; omega
      have hrec : ∀ (a b e : Nat) (dt : Bool),
          mantissaFrom? raw (blen pre + blen (c :: cs)) n ⟨blen (pre ++ [c])⟩ a b e dt
            = ((mantissaList? cs a b e dt).map
                (fun r => (r.1, r.2.1, (⟨blen pre + blen (c :: r.2.2.1)⟩ : String.Pos.Raw)))) := by
        intro a b e dt
        have := ih (pre ++ [c]) post a b e dt n (by rw [hs]; simp) (by simp at hfuel; omega)
        rw [hstop'] at this
        rw [this]
        cases mantissaList? cs a b e dt with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq,
            String.Pos.Raw.mk.injEq, blen_append, blen_cons, blen_nil]
          exact ⟨trivial, trivial, by omega⟩
      simp only [mantissaFrom?, ite_eq_right hstop, hget, hnext, mantissaList?]
      by_cases hu : c == '_'
      · rw [ite_eq_left hu, ite_eq_left hu, hrec]
        cases mantissaList? cs m nd nf dot <;> rfl
      · rw [ite_eq_right hu, ite_eq_right hu]
        by_cases hdot : c == '.'
        · rw [ite_eq_left hdot, ite_eq_left hdot]
          by_cases hd : dot
          · rw [ite_eq_left hd, ite_eq_left hd]; rfl
          · rw [ite_eq_right hd, ite_eq_right hd, hrec]
            cases mantissaList? cs m nd nf true <;> rfl
        · rw [ite_eq_right hdot, ite_eq_right hdot]
          by_cases he : c == 'e' || c == 'E'
          · rw [ite_eq_left he, ite_eq_left he]
            by_cases hnd : nd == 0
            · rw [ite_eq_left hnd, ite_eq_left hnd]; rfl
            · rw [ite_eq_right hnd, ite_eq_right hnd]
              simp only [Option.map_some,
                blen_append, blen_cons, blen_nil]
          · rw [ite_eq_right he, ite_eq_right he]
            cases hdv : digitVal? c with
            | none => rfl
            | some d =>
              by_cases hlt : d < 10
              · simp only [ite_eq_left hlt]
                rw [hrec]
                cases mantissaList? cs (10 * m + d) (nd + 1)
                  (if dot then nf + 1 else nf) dot <;> rfl
              · simp only [ite_eq_right hlt]; rfl

theorem expFrom?_eq (raw : String) (suf pre post : List Char) (fuel : Nat)
    (h : raw.toList = pre ++ suf ++ post) (hfuel : suf.length ≤ fuel) :
    expFrom? raw (blen pre + blen suf) fuel ⟨blen pre⟩ = expList? suf := by
  have hnext := nextChar?_eq raw suf pre post fuel h hfuel
  simp only [expFrom?, expList?, hnext]
  cases hnc : nextCharList? suf with
  | none => rfl
  | some r =>
    obtain ⟨c, cons, rest⟩ := r
    have hsplit : suf = cons ++ rest := nextCharList?_split suf c cons rest hnc
    have hlen : rest.length ≤ fuel := by
      have : suf.length = cons.length + rest.length := by rw [hsplit]; simp
      omega
    have hpre : raw.toList = (pre ++ cons) ++ rest ++ post := by
      rw [h, hsplit]; simp
    have hstop : blen (pre ++ cons) + blen rest = blen pre + blen suf := by
      rw [hsplit]; simp only [blen_append]; omega
    have hdig : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen pre + blen suf) radix fuel ((⟨blen pre + blen cons⟩ :
            String.Pos.Raw)) acc = digitsList? radix rest acc := by
      intro radix acc
      have := digitsFrom?_eq raw rest (pre ++ cons) post radix acc fuel hpre hlen
      rw [hstop] at this
      simpa only [blen_append] using this
    have hdig0 : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen pre + blen suf) radix fuel ((⟨blen pre⟩ : String.Pos.Raw)) acc
          = digitsList? radix suf acc := by
      intro radix acc
      exact digitsFrom?_eq raw suf pre post radix acc fuel h hfuel
    simp only [Option.map_some]
    by_cases hm : c == '-'
    · rw [ite_eq_left hm, ite_eq_left hm, hdig]
    · rw [ite_eq_right hm, ite_eq_right hm]
      by_cases hp : c == '+'
      · rw [ite_eq_left hp, ite_eq_left hp, hdig]
      · rw [ite_eq_right hp, ite_eq_right hp, hdig0]

/-- The backward scan for the `n` suffix, on the reversed spelling: `rmid`
is what is left to scan, reversed, and `post` what has been scanned past
(only separators). -/
theorem bigSuffix_eq_aux (raw : String) : ∀ (rmid post : List Char) (fuel : Nat),
    raw.toList = rmid.reverse ++ post → rmid.length ≤ fuel →
    bigSuffix raw raw.utf8ByteSize fuel ⟨blen rmid⟩
      = (match bigSuffixAux rmid with
         | some rs => (blen rs, true)
         | none => (raw.utf8ByteSize, false)) := by
  intro rmid
  induction rmid with
  | nil =>
    intro post fuel _ _
    cases fuel <;> simp [bigSuffix, bigSuffixAux]
  | cons c rs ih =>
    intro post fuel hs hfuel
    have hpos := c.utf8Size_pos
    have hs' : raw.toList = rs.reverse ++ c :: post := by
      rw [hs]; simp
    have hblen : blen (c :: rs) = blen rs.reverse + c.utf8Size := by
      rw [blen_reverse]; simp only [blen_cons]; omega
    have hzero : ¬ ((⟨blen (c :: rs)⟩ : String.Pos.Raw).byteIdx = 0) := by
      simp only [blen_cons]; omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hprev : String.Pos.Raw.prev raw ⟨blen (c :: rs)⟩ = ⟨blen rs.reverse⟩ := by
        rw [hblen]; exact prev_eq hs'
      have hget : String.Pos.Raw.get raw ⟨blen rs.reverse⟩ = c := get_eq hs'
      have hrev : blen rs.reverse = blen rs := blen_reverse rs
      simp only [bigSuffix, hzero, hprev, hget, bigSuffixAux,
        ite_false, beq_iff_eq]
      by_cases hu : c = '_'
      · rw [ite_eq_left hu, ite_eq_left hu]
        have := ih (c :: post) n (by rw [hs]; simp) (by simp at hfuel; omega)
        rw [← hrev] at this
        exact this
      · rw [ite_eq_right hu, ite_eq_right hu]
        by_cases hn : c = 'n'
        · rw [ite_eq_left hn, ite_eq_left hn, hrev]
        · rw [ite_eq_right hn, ite_eq_right hn]

theorem bigSuffix_eq (raw : String) :
    bigSuffix raw raw.utf8ByteSize raw.utf8ByteSize ⟨raw.utf8ByteSize⟩
      = (blen (bigSuffixList raw.toList).1, (bigSuffixList raw.toList).2) := by
  have hlen : raw.toList.reverse.length ≤ raw.utf8ByteSize := by
    have := length_le_blen raw.toList
    simp only [blen_toList] at this
    simpa using this
  have hb : blen raw.toList.reverse = raw.utf8ByteSize := by
    rw [blen_reverse, blen_toList]
  have h := bigSuffix_eq_aux raw raw.toList.reverse [] raw.utf8ByteSize (by simp) hlen
  rw [hb] at h
  rw [h, bigSuffixList]
  cases bigSuffixAux raw.toList.reverse with
  | none => simp [blen_toList]
  | some rs => simp [blen_reverse]

/-- What the `n` suffix leaves is a prefix of the spelling. -/
theorem bigSuffixAux_split : ∀ (r rs : List Char), bigSuffixAux r = some rs → ∃ t, r = t ++ rs := by
  intro r
  induction r with
  | nil => intro rs h; simp [bigSuffixAux] at h
  | cons c cs ih =>
    intro rs h
    simp only [bigSuffixAux] at h
    by_cases hu : c == '_'
    · rw [ite_eq_left hu] at h
      obtain ⟨t, ht⟩ := ih rs h
      exact ⟨c :: t, by rw [ht]; simp⟩
    · rw [ite_eq_right hu] at h
      by_cases hn : c == 'n'
      · rw [ite_eq_left hn] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨[c], rfl⟩
      · rw [ite_eq_right hn] at h; simp at h

theorem bigSuffixList_split (l : List Char) : ∃ post, l = (bigSuffixList l).1 ++ post := by
  cases h : bigSuffixAux l.reverse with
  | none => exact ⟨[], by simp [bigSuffixList, h]⟩
  | some rs =>
    obtain ⟨t, ht⟩ := bigSuffixAux_split l.reverse rs h
    refine ⟨t.reverse, ?_⟩
    have hl : l = (t ++ rs).reverse := by rw [← ht]; simp
    simp only [bigSuffixList, h]
    rw [hl]; simp

/-- A prefix of the spelling has no more characters than the spelling has
bytes. -/
theorem length_le_utf8ByteSize {raw : String} {mid post : List Char}
    (h : raw.toList = mid ++ post) : mid.length ≤ raw.utf8ByteSize := by
  have hb : raw.toList.length ≤ raw.utf8ByteSize := by
    have := length_le_blen raw.toList
    simpa using this
  have : raw.toList.length = mid.length + post.length := by rw [h]; simp
  omega

theorem parseDecimal?_eq (raw : String) (mid post : List Char) (isBig : Bool)
    (h : raw.toList = mid ++ post) :
    parseDecimal? raw (blen mid) raw.utf8ByteSize isBig = parseDecimalList? mid isBig := by
  have hfuel : mid.length ≤ raw.utf8ByteSize := length_le_utf8ByteSize h
  have hm := mantissaFrom?_eq raw mid [] post 0 0 0 false raw.utf8ByteSize
    (by simpa using h) hfuel
  simp only [blen_nil, Nat.zero_add] at hm
  simp only [parseDecimal?, parseDecimalList?, hm]
  cases hml : mantissaList? mid 0 0 0 false with
  | none => rfl
  | some r =>
    obtain ⟨m, nf, cons, rest⟩ := r
    have hsplit : mid = cons ++ rest := mantissaList?_split mid 0 0 0 false m nf cons rest hml
    have hexp : expFrom? raw (blen mid) raw.utf8ByteSize ⟨blen cons⟩ = expList? rest := by
      have hpre : raw.toList = cons ++ rest ++ post := by simp [h, hsplit]
      have hlen : rest.length ≤ raw.utf8ByteSize := by
        have : mid.length = cons.length + rest.length := by rw [hsplit]; simp
        omega
      have hstop : blen cons + blen rest = blen mid := by
        rw [hsplit]; simp only [blen_append]
      have := expFrom?_eq raw rest cons post raw.utf8ByteSize hpre hlen
      rwa [hstop] at this
    simp only [Option.map_some, hexp]
    rfl

/-- The in-place reader reads the list of characters of its input. -/
theorem parse?_eq_parseList? (raw : String) : parse? raw = parseList? raw.toList := by
  obtain ⟨post, hpost⟩ := bigSuffixList_split raw.toList
  have hfuel : (bigSuffixList raw.toList).1.length ≤ raw.utf8ByteSize :=
    length_le_utf8ByteSize hpost
  have hbs := bigSuffix_eq raw
  -- the digits of the literal, and whether it is a `BigInt` one
  rcases hbl : bigSuffixList raw.toList with ⟨mid, isBig⟩
  rw [hbl] at hpost hbs hfuel
  simp only at hpost hbs hfuel
  have hnext0 : nextChar? raw (blen mid) raw.utf8ByteSize ⟨0⟩
      = (nextCharList? mid).map (fun r => (r.1, (⟨blen r.2.1⟩ : String.Pos.Raw))) := by
    have := nextChar?_eq raw mid [] post raw.utf8ByteSize (by simpa using hpost) hfuel
    simpa using this
  have hdec := parseDecimal?_eq raw mid post isBig hpost
  simp only [parse?, hbs, parseList?, hbl, hnext0, hdec]
  cases hnc : nextCharList? mid with
  | none => rfl
  | some r0 =>
    obtain ⟨c0, cons0, rest0⟩ := r0
    have hsplit0 : mid = cons0 ++ rest0 := nextCharList?_split mid c0 cons0 rest0 hnc
    have hpre0 : raw.toList = cons0 ++ rest0 ++ post := by simp [hpost, hsplit0]
    have hlen0 : rest0.length ≤ raw.utf8ByteSize := by
      have : mid.length = cons0.length + rest0.length := by rw [hsplit0]; simp
      omega
    have hstop0 : blen cons0 + blen rest0 = blen mid := by
      rw [hsplit0]; simp only [blen_append]
    have hnext1 : nextChar? raw (blen mid) raw.utf8ByteSize ⟨blen cons0⟩
        = (nextCharList? rest0).map
            (fun r => (r.1, (⟨blen cons0 + blen r.2.1⟩ : String.Pos.Raw))) := by
      have := nextChar?_eq raw rest0 cons0 post raw.utf8ByteSize hpre0 hlen0
      rwa [hstop0] at this
    have hdig0 : ∀ (radix : Nat) (acc : Option Nat),
        digitsFrom? raw (blen mid) radix raw.utf8ByteSize ⟨blen cons0⟩ acc
          = digitsList? radix rest0 acc := by
      intro radix acc
      have := digitsFrom?_eq raw rest0 cons0 post radix acc raw.utf8ByteSize hpre0 hlen0
      rwa [hstop0] at this
    simp only [Option.map_some, hnext1]
    by_cases hzero : c0 == '0'
    · rw [ite_eq_left hzero, ite_eq_left hzero]
      cases hnc1 : nextCharList? rest0 with
      | none => simp only [Option.map_none]
      | some r1 =>
        obtain ⟨c1, cons1, rest1⟩ := r1
        have hsplit1 : rest0 = cons1 ++ rest1 := nextCharList?_split rest0 c1 cons1 rest1 hnc1
        have hpre1 : raw.toList = (cons0 ++ cons1) ++ rest1 ++ post := by
          simp [hpost, hsplit0, hsplit1]
        have hlen1 : rest1.length ≤ raw.utf8ByteSize := by
          have : rest0.length = cons1.length + rest1.length := by rw [hsplit1]; simp
          omega
        have hstop1 : blen (cons0 ++ cons1) + blen rest1 = blen mid := by
          rw [hsplit0, hsplit1]; simp only [blen_append]; omega
        have hdig1 : ∀ (radix : Nat) (acc : Option Nat),
            digitsFrom? raw (blen mid) radix raw.utf8ByteSize ⟨blen cons0 + blen cons1⟩ acc
              = digitsList? radix rest1 acc := by
          intro radix acc
          have := digitsFrom?_eq raw rest1 (cons0 ++ cons1) post radix acc raw.utf8ByteSize
            hpre1 hlen1
          rw [hstop1] at this
          simpa only [blen_append] using this
        simp only [Option.map_some, hdig1, hdig0]
        rfl
    · rw [ite_eq_right hzero, ite_eq_right hzero]

end JSNumber

end Language.JavaScript
