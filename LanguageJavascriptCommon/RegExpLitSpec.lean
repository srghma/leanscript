/-
The in-place readers of `Language.JavaScript.RegExpFlags` and
`Language.JavaScript.RegExpLit` scan their input by byte index, so that
reading a regular expression literal allocates nothing but the pattern
itself.  This module proves that they compute exactly what the obvious,
slow reader computes: the one which turns the input into a `List Char` and
walks it, `RegExpFlags.readChars` and `RegExpLit.parseList?` below.

The main results are

* `RegExpFlags.parse?_eq_readChars` and `RegExpFlags.readChars_eq_foldl`,
  which relate the flags reader to the fold the flags used to be read with;
* `RegExpLit.parse?_eq_parseList?` and, through it,
  `RegExpLit.parse?_eq_parseAcc?`, which says that the in-place reader
  returns exactly what the reader it replaced returned — `parseAcc?` is
  that reader, transcribed.

They are proved from a small toolkit about the raw byte positions of a
string: `ByteScan.blen` is the number of bytes a list of characters
occupies, and the three lemmas `ByteScan.get_eq`, `ByteScan.next_eq` and
`ByteScan.extract_eq` say what `String.Pos.Raw.get`, `.next` and `.extract`
do at the position which follows a given prefix.
-/
import LanguageJavascriptCommon.Types

open NonEmpty.String

set_option autoImplicit false

namespace Language.JavaScript

/-! ## Byte positions of a list of characters -/

namespace ByteScan

/-- The number of bytes the characters of `l` occupy in UTF-8. -/
def blen : List Char → Nat
  | [] => 0
  | c :: cs => c.utf8Size + blen cs

@[simp] theorem blen_nil : blen [] = 0 := rfl

@[simp] theorem blen_cons (c : Char) (cs : List Char) :
    blen (c :: cs) = c.utf8Size + blen cs := rfl

@[simp] theorem blen_append (l m : List Char) : blen (l ++ m) = blen l + blen m := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [ih, Nat.add_assoc]

/-- A character takes at least one byte, so a list takes at least as many
bytes as it has characters. -/
theorem length_le_blen (l : List Char) : l.length ≤ blen l := by
  induction l with
  | nil => simp
  | cons c cs ih =>
    have := c.utf8Size_pos
    simp only [blen_cons, List.length_cons]
    omega

theorem blen_ofList (l : List Char) : blen l = (String.ofList l).utf8ByteSize := by
  induction l with
  | nil => simp [String.ofList_nil]
  | cons c cs ih =>
    have hsplit : String.ofList (c :: cs) = String.ofList [c] ++ String.ofList cs := by
      rw [← String.ofList_append]; rfl
    have hone : (String.ofList [c]).utf8ByteSize = c.utf8Size := by
      rw [← String.singleton_eq_ofList]; simp only [String.utf8ByteSize_singleton]
    rw [blen_cons, ih, hsplit, String.utf8ByteSize_append, hone]

/-- The bytes of a string are the bytes of its characters. -/
@[simp] theorem blen_toList (s : String) : blen s.toList = s.utf8ByteSize := by
  rw [blen_ofList, String.ofList_toList]

theorem utf8GetAux_append (c : Char) (suf : List Char) : ∀ (pre : List Char) (i : Nat),
    String.Pos.Raw.utf8GetAux (pre ++ c :: suf) ⟨i⟩ ⟨i + blen pre⟩ = c := by
  intro pre
  induction pre with
  | nil => intro i; simp [String.Pos.Raw.utf8GetAux]
  | cons d ds ih =>
    intro i
    have hpos := d.utf8Size_pos
    have hne : (⟨i⟩ : String.Pos.Raw) ≠ ⟨i + blen (d :: ds)⟩ := by
      intro h
      have h2 : i = i + blen (d :: ds) := congrArg String.Pos.Raw.byteIdx h
      simp only [blen_cons] at h2; omega
    simp only [List.cons_append, String.Pos.Raw.utf8GetAux, ite_eq_right hne]
    have hadd : (⟨i⟩ : String.Pos.Raw) + d = ⟨i + d.utf8Size⟩ := rfl
    rw [hadd, show i + blen (d :: ds) = (i + d.utf8Size) + blen ds by
      simp only [blen_cons]; omega]
    exact ih (i + d.utf8Size)

/-- The character at the position which follows the prefix `pre`. -/
theorem get_eq {s : String} {pre suf : List Char} {c : Char}
    (h : s.toList = pre ++ c :: suf) :
    String.Pos.Raw.get s ⟨blen pre⟩ = c := by
  have : String.Pos.Raw.get s ⟨blen pre⟩
      = String.Pos.Raw.utf8GetAux (pre ++ c :: suf) ⟨0⟩ ⟨0 + blen pre⟩ := by
    rw [show (0 : Nat) + blen pre = blen pre by omega, ← h]
    rfl
  rw [this, utf8GetAux_append]

/-- Advancing past the character which follows the prefix `pre`. -/
theorem next_eq {s : String} {pre suf : List Char} {c : Char}
    (h : s.toList = pre ++ c :: suf) :
    String.Pos.Raw.next s ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := by
  have hg := get_eq h
  simp only [String.Pos.Raw.next, hg, blen_append, blen_cons, blen_nil]
  rfl

theorem extract_go₂ : ∀ (mid rest : List Char) (k : Nat),
    String.Pos.Raw.extract.go₂ (mid ++ rest) ⟨k⟩ ⟨k + blen mid⟩ = mid := by
  intro mid
  induction mid with
  | nil =>
    intro rest k
    cases rest with
    | nil => simp [String.Pos.Raw.extract.go₂]
    | cons d ds => simp [String.Pos.Raw.extract.go₂]
  | cons d ds ih =>
    intro rest k
    have hpos := d.utf8Size_pos
    have hne : (⟨k⟩ : String.Pos.Raw) ≠ ⟨k + blen (d :: ds)⟩ := by
      intro h
      have h2 : k = k + blen (d :: ds) := congrArg String.Pos.Raw.byteIdx h
      simp only [blen_cons] at h2; omega
    simp only [List.cons_append, String.Pos.Raw.extract.go₂, ite_eq_right hne]
    have hadd : (⟨k⟩ : String.Pos.Raw) + d = ⟨k + d.utf8Size⟩ := rfl
    rw [hadd, show k + blen (d :: ds) = (k + d.utf8Size) + blen ds by
      simp only [blen_cons]; omega]
    exact congrArg (d :: ·) (ih rest (k + d.utf8Size))

theorem extract_go₁ (e : String.Pos.Raw) : ∀ (pre rest : List Char) (k : Nat),
    String.Pos.Raw.extract.go₁ (pre ++ rest) ⟨k⟩ ⟨k + blen pre⟩ e
      = String.Pos.Raw.extract.go₂ rest ⟨k + blen pre⟩ e := by
  intro pre
  induction pre with
  | nil =>
    intro rest k
    cases rest with
    | nil => simp [String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
    | cons d ds => simp [String.Pos.Raw.extract.go₁]
  | cons d ds ih =>
    intro rest k
    have hpos := d.utf8Size_pos
    have hne : (⟨k⟩ : String.Pos.Raw) ≠ ⟨k + blen (d :: ds)⟩ := by
      intro h
      have h2 : k = k + blen (d :: ds) := congrArg String.Pos.Raw.byteIdx h
      simp only [blen_cons] at h2; omega
    simp only [List.cons_append, String.Pos.Raw.extract.go₁, ite_eq_right hne]
    have hadd : (⟨k⟩ : String.Pos.Raw) + d = ⟨k + d.utf8Size⟩ := rfl
    rw [hadd, show k + blen (d :: ds) = (k + d.utf8Size) + blen ds by
      simp only [blen_cons]; omega]
    exact ih rest (k + d.utf8Size)

/-- Slicing out the segment `mid` of a string split as `pre ++ mid ++ rest`. -/
theorem extract_eq {s : String} {pre mid rest : List Char}
    (h : s.toList = pre ++ mid ++ rest) :
    String.Pos.Raw.extract s ⟨blen pre⟩ ⟨blen pre + blen mid⟩ = String.ofList mid := by
  cases mid with
  | nil => simp [String.Pos.Raw.extract, String.ofList_nil]
  | cons d ds =>
    have hpos := d.utf8Size_pos
    have hlt : ¬ (blen pre + blen (d :: ds) ≤ blen pre) := by simp only [blen_cons]; omega
    simp only [String.Pos.Raw.extract, ge_iff_le]
    rw [ite_eq_right (by simpa [String.Pos.Raw.le_iff] using hlt)]
    congr 1
    rw [h, List.append_assoc, show (0 : String.Pos.Raw) = ⟨0⟩ from rfl,
      show (⟨blen pre⟩ : String.Pos.Raw) = ⟨0 + blen pre⟩ by simp,
      extract_go₁ ⟨blen pre + blen (d :: ds)⟩ pre ((d :: ds) ++ rest) 0]
    simpa using extract_go₂ (d :: ds) rest (blen pre)

end ByteScan

open ByteScan

/-! ## The flags -/

namespace RegExpFlags

/-- Read the flags written by a list of characters, one at a time: the
straightforward reader `parse?` is an in-place version of. -/
def readChars (f : RegExpFlags) : List Char → Option RegExpFlags
  | [] => some f
  | c :: cs =>
      match f.add? c with
      | none => none
      | some f' => readChars f' cs

theorem scanFrom_eq (s : String) : ∀ (suf pre : List Char) (f : RegExpFlags) (fuel : Nat),
    s.toList = pre ++ suf → suf.length ≤ fuel →
    scanFrom s s.utf8ByteSize fuel ⟨blen pre⟩ f = f.readChars suf := by
  intro suf
  induction suf with
  | nil =>
    intro pre f fuel hs _
    have hstop : s.utf8ByteSize ≤ blen pre := by
      rw [← blen_toList s, hs]; simp
    cases fuel with
    | zero => simp [scanFrom, readChars, hstop]
    | succ n => simp [scanFrom, readChars, hstop]
  | cons c cs ih =>
    intro pre f fuel hs hfuel
    have hsize : s.utf8ByteSize = blen pre + (c.utf8Size + blen cs) := by
      rw [← blen_toList s, hs]; simp
    have hpos := c.utf8Size_pos
    have hstop : ¬ (s.utf8ByteSize ≤ blen pre) := by omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hget : String.Pos.Raw.get s ⟨blen pre⟩ = c := get_eq hs
      have hnext : String.Pos.Raw.next s ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs
      simp only [scanFrom, ite_eq_right hstop, hget, hnext, readChars]
      cases hadd : f.add? c with
      | none => rfl
      | some f' =>
        simp only []
        refine ih (pre ++ [c]) f' n ?_ ?_
        · rw [hs]; simp
        · simp at hfuel; omega

/-- The in-place reader of the flags reads exactly what the list based one
reads. -/
theorem parse?_eq_readChars (s : String) :
    parse? s = readChars {} s.toList := by
  have h := scanFrom_eq s s.toList [] {} (s.utf8ByteSize - 0) (by simp) ?_
  · simpa [parse?, parseRange?] using h
  · have := length_le_blen s.toList
    simp only [blen_toList] at this
    omega

/-- Reading a list of characters is reading the string they spell. -/
theorem readChars_ofList (l : List Char) : readChars {} l = parse? (String.ofList l) := by
  rw [parse?_eq_readChars, String.toList_ofList]

/-- Once a flag has been rejected, nothing can be read any more. -/
private theorem foldl_none (l : List Char) :
    l.foldl (fun (acc : Option RegExpFlags) c => acc.bind (fun f => f.add? c)) none
      = none := by
  induction l with
  | nil => rfl
  | cons c cs ih => simpa using ih

/-- `readChars` is the fold the flags used to be read with. -/
theorem readChars_eq_foldl : ∀ (l : List Char) (f : RegExpFlags),
    readChars f l
      = l.foldl (fun (acc : Option RegExpFlags) c => acc.bind (fun g => g.add? c)) (some f) := by
  intro l
  induction l with
  | nil => intro f; rfl
  | cons c cs ih =>
    intro f
    simp only [readChars, List.foldl_cons, Option.bind_some]
    cases f.add? c with
    | none => exact (foldl_none cs).symm
    | some f' => exact ih f'

end RegExpFlags

/-! ## The literal -/

namespace RegExpLit

/-- Split a list of characters at the `/` which closes the literal: the
pattern, and what follows the slash.  This is the straightforward reader
`scanClose` is an in-place version of. -/
def splitList? (inClass escaped : Bool) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: tl =>
      if escaped then (splitList? inClass false tl).map (fun r => (c :: r.1, r.2))
      else if inClass then (splitList? (c != ']') false tl).map (fun r => (c :: r.1, r.2))
      else if c == '\\' then (splitList? false true tl).map (fun r => (c :: r.1, r.2))
      else if c == '[' then (splitList? true false tl).map (fun r => (c :: r.1, r.2))
      else if c == '/' then some ([], tl)
      else (splitList? false false tl).map (fun r => (c :: r.1, r.2))

/-- What `splitList?` returns is a splitting of its input at a `/`. -/
theorem splitList?_eq : ∀ (cs : List Char) (inClass escaped : Bool) (pat rest : List Char),
    splitList? inClass escaped cs = some (pat, rest) → cs = pat ++ '/' :: rest := by
  intro cs
  induction cs with
  | nil => intro inClass escaped pat rest h; simp [splitList?] at h
  | cons c tl ih =>
    intro inClass escaped pat rest h
    -- every branch but the closing slash prepends `c` to the pattern
    have step : ∀ (ic e : Bool),
        (splitList? ic e tl).map (fun r => (c :: r.1, r.2)) = some (pat, rest) →
        c :: tl = pat ++ '/' :: rest := by
      intro ic e hmap
      cases hsplit : splitList? ic e tl with
      | none => rw [hsplit] at hmap; simp at hmap
      | some pr =>
        rw [hsplit] at hmap
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
        obtain ⟨hp, hr⟩ := hmap
        subst hp; subst hr
        have hpr : pr = (pr.1, pr.2) := rfl
        have := ih ic e pr.1 pr.2 (by rw [hsplit, ← hpr])
        simpa using this
    simp only [splitList?] at h
    by_cases hesc : escaped
    · rw [ite_eq_left hesc] at h; exact step inClass false h
    · rw [ite_eq_right hesc] at h
      by_cases hcls : inClass
      · rw [ite_eq_left hcls] at h; exact step (c != ']') false h
      · rw [ite_eq_right hcls] at h
        by_cases hbs : c == '\\'
        · rw [ite_eq_left hbs] at h; exact step false true h
        · rw [ite_eq_right hbs] at h
          by_cases hbr : c == '['
          · rw [ite_eq_left hbr] at h; exact step true false h
          · rw [ite_eq_right hbr] at h
            by_cases hsl : c == '/'
            · rw [ite_eq_left hsl] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hp, hr⟩ := h
              subst hp; subst hr
              have hc : c = '/' := by simpa using hsl
              subst hc; rfl
            · rw [ite_eq_right hsl] at h; exact step false false h

theorem scanClose_eq (raw : String) : ∀ (suf pre : List Char) (inClass escaped : Bool)
    (fuel : Nat), raw.toList = pre ++ suf → suf.length ≤ fuel →
    scanClose raw fuel ⟨blen pre⟩ inClass escaped
      = (splitList? inClass escaped suf).map (fun r => ⟨blen pre + blen r.1⟩) := by
  intro suf
  induction suf with
  | nil =>
    intro pre inClass escaped fuel hs _
    have hstop : raw.utf8ByteSize ≤ blen pre := by
      rw [← blen_toList raw, hs]; simp
    cases fuel with
    | zero => simp [scanClose, splitList?]
    | succ n => simp [scanClose, splitList?, hstop]
  | cons c cs ih =>
    intro pre inClass escaped fuel hs hfuel
    have hsize : raw.utf8ByteSize = blen pre + (c.utf8Size + blen cs) := by
      rw [← blen_toList raw, hs]; simp
    have hpos := c.utf8Size_pos
    have hstop : ¬ (raw.utf8ByteSize ≤ blen pre) := by omega
    cases fuel with
    | zero => simp at hfuel
    | succ n =>
      have hget : String.Pos.Raw.get raw ⟨blen pre⟩ = c := get_eq hs
      have hnext : String.Pos.Raw.next raw ⟨blen pre⟩ = ⟨blen (pre ++ [c])⟩ := next_eq hs
      have hs' : raw.toList = (pre ++ [c]) ++ cs := by rw [hs]; simp
      have hfuel' : cs.length ≤ n := by simp only [List.length_cons] at hfuel; omega
      have hblen : blen (pre ++ [c]) = blen pre + c.utf8Size := by simp
      -- the recursive call, whatever the two flags are
      have step : ∀ (ic e : Bool),
          scanClose raw n ⟨blen (pre ++ [c])⟩ ic e
            = (splitList? ic e cs).map
                (fun r => (⟨blen pre + (c.utf8Size + blen r.1)⟩ : String.Pos.Raw)) := by
        intro ic e
        rw [ih (pre ++ [c]) ic e n hs' hfuel']
        cases splitList? ic e cs with
        | none => rfl
        | some r =>
          simp only [Option.map_some, Option.some.injEq, String.Pos.Raw.mk.injEq, hblen]
          omega
      simp only [scanClose, ite_eq_right hstop, hget, hnext, splitList?]
      by_cases hesc : escaped
      · rw [ite_eq_left hesc, ite_eq_left hesc, step inClass false]
        cases splitList? inClass false cs <;> simp
      · rw [ite_eq_right hesc, ite_eq_right hesc]
        by_cases hcls : inClass
        · rw [ite_eq_left hcls, ite_eq_left hcls, step (c != ']') false]
          cases splitList? (c != ']') false cs <;> simp
        · rw [ite_eq_right hcls, ite_eq_right hcls]
          by_cases hbs : c == '\\'
          · rw [ite_eq_left hbs, ite_eq_left hbs, step false true]
            cases splitList? false true cs <;> simp
          · rw [ite_eq_right hbs, ite_eq_right hbs]
            by_cases hbr : c == '['
            · rw [ite_eq_left hbr, ite_eq_left hbr, step true false]
              cases splitList? true false cs <;> simp
            · rw [ite_eq_right hbr, ite_eq_right hbr]
              by_cases hsl : c == '/'
              · rw [ite_eq_left hsl, ite_eq_left hsl]; simp
              · rw [ite_eq_right hsl, ite_eq_right hsl, step false false]
                cases splitList? false false cs <;> simp

/-- Read a literal of the form `/source/flags` the slow way: turn the input
into a list of characters and walk it.  This is the specification of
`parse?`. -/
def parseList? (raw : String) : Option RegExpLit :=
  match raw.toList with
  | '/' :: rest => do
      let (pat, flagChars) ← splitList? false false rest
      let source ← NonEmptyString.fromString? (String.ofList pat)
      let flags ← RegExpFlags.readChars {} flagChars
      some ⟨source, flags⟩
  | _ => none

/-- The in-place reader of a regular expression literal reads exactly what
the list based one reads. -/
theorem parse?_eq_parseList? (raw : String) : parse? raw = parseList? raw := by
  rcases hraw : raw.toList with _ | ⟨c, rest⟩
  · have hempty : raw.utf8ByteSize = 0 := by rw [← blen_toList raw, hraw]; rfl
    simp [parse?, parseList?, hraw, hempty]
  · have hpos := c.utf8Size_pos
    have hsize : raw.utf8ByteSize = c.utf8Size + blen rest := by
      rw [← blen_toList raw, hraw]; simp
    have hnz : (raw.utf8ByteSize == 0) = false := by
      have : raw.utf8ByteSize ≠ 0 := by omega
      simp [this]
    have hget0' : String.Pos.Raw.get raw ⟨0⟩ = c := get_eq (pre := []) (by simpa using hraw)
    have hget0 : String.Pos.Raw.get raw 0 = c := hget0'
    by_cases hslash : c = '/'
    · subst hslash
      have hg : (raw.utf8ByteSize == 0 || String.Pos.Raw.get raw ⟨0⟩ != '/') = false := by
        rw [hget0']; simp [hnz]
      have hone : ('/' : Char).utf8Size = 1 := by decide
      have hstart : (⟨1⟩ : String.Pos.Raw) = ⟨blen ['/']⟩ := rfl
      have hfuel : rest.length ≤ raw.utf8ByteSize := by
        have := length_le_blen rest
        omega
      have hscan := scanClose_eq raw rest ['/'] false false raw.utf8ByteSize
        (by simpa using hraw) (by simpa using hfuel)
      simp only [parse?, hg, Bool.false_eq_true, ite_false, hstart, hscan, parseList?, hraw]
      cases hsplit : splitList? false false rest with
      | none => simp
      | some pr =>
        obtain ⟨pat, flagChars⟩ := pr
        have hrest : rest = pat ++ '/' :: flagChars :=
          splitList?_eq rest false false pat flagChars hsplit
        have hlist : raw.toList = ['/'] ++ pat ++ ('/' :: flagChars) := by
          rw [hraw, hrest]; simp
        have hextract : String.Pos.Raw.extract raw ⟨blen ['/']⟩ ⟨blen ['/'] + blen pat⟩
            = String.ofList pat := extract_eq hlist
        have hlist2 : raw.toList = ('/' :: (pat ++ ['/'])) ++ flagChars := by
          rw [hraw, hrest]; simp
        have hbytepos : blen ['/'] + blen pat + 1 = blen ('/' :: (pat ++ ['/'])) := by
          simp only [blen_cons, blen_append, blen_nil, hone]
          omega
        have hflagfuel : flagChars.length ≤ raw.utf8ByteSize - blen ('/' :: (pat ++ ['/'])) := by
          have hb : raw.utf8ByteSize = blen ('/' :: (pat ++ ['/'])) + blen flagChars := by
            rw [← blen_toList raw, hlist2]; simp; omega
          have hle := length_le_blen flagChars
          simp only [blen_cons, blen_append, blen_nil, hone] at hb ⊢
          omega
        have hflags := RegExpFlags.scanFrom_eq raw flagChars ('/' :: (pat ++ ['/'])) {}
          (raw.utf8ByteSize - blen ('/' :: (pat ++ ['/']))) hlist2 hflagfuel
        simp only [Option.map_some, hextract, RegExpFlags.parseRange?, hbytepos, hflags]
        cases hsrc : NonEmptyString.fromString? (String.ofList pat) with
        | none => simp only [Option.bind_eq_bind, Option.bind_some, hsrc, Option.bind_none]
        | some src =>
          cases hfl : RegExpFlags.readChars {} flagChars with
          | none =>
            simp only [Option.bind_eq_bind, Option.bind_some, hsrc, hfl, Option.bind_none]
          | some fl =>
            simp only [Option.bind_eq_bind, Option.bind_some, hsrc, hfl]
    · have hg : (raw.utf8ByteSize == 0 || String.Pos.Raw.get raw ⟨0⟩ != '/') = true := by
        rw [hget0']; simp [hslash]
      simp only [parse?, hg, ite_true]
      simp [parseList?, hraw, hslash]

/-- The accumulator based splitter the literal used to be read with. -/
def splitPatternAcc (acc : List Char) (inClass escaped : Bool) :
    List Char → Option (List Char × List Char)
  | [] => none
  | c :: tl =>
      if escaped then splitPatternAcc (c :: acc) inClass false tl
      else if inClass then splitPatternAcc (c :: acc) (c != ']') false tl
      else if c == '\\' then splitPatternAcc (c :: acc) false true tl
      else if c == '[' then splitPatternAcc (c :: acc) true false tl
      else if c == '/' then some (acc.reverse, tl)
      else splitPatternAcc (c :: acc) false false tl

/-- `splitList?` splits where the accumulator based splitter splits. -/
theorem splitPatternAcc_eq : ∀ (cs acc : List Char) (inClass escaped : Bool),
    splitPatternAcc acc inClass escaped cs
      = (splitList? inClass escaped cs).map (fun r => (acc.reverse ++ r.1, r.2)) := by
  intro cs
  induction cs with
  | nil => intro acc inClass escaped; rfl
  | cons c tl ih =>
    intro acc inClass escaped
    have step : ∀ (ic e : Bool),
        splitPatternAcc (c :: acc) ic e tl
          = ((splitList? ic e tl).map (fun r => (c :: r.1, r.2))).map
              (fun r => (acc.reverse ++ r.1, r.2)) := by
      intro ic e
      rw [ih (c :: acc) ic e]
      cases splitList? ic e tl with
      | none => rfl
      | some r => simp
    simp only [splitPatternAcc, splitList?]
    by_cases hesc : escaped
    · rw [ite_eq_left hesc, ite_eq_left hesc, step inClass false]
    · rw [ite_eq_right hesc, ite_eq_right hesc]
      by_cases hcls : inClass
      · rw [ite_eq_left hcls, ite_eq_left hcls, step (c != ']') false]
      · rw [ite_eq_right hcls, ite_eq_right hcls]
        by_cases hbs : c == '\\'
        · rw [ite_eq_left hbs, ite_eq_left hbs, step false true]
        · rw [ite_eq_right hbs, ite_eq_right hbs]
          by_cases hbr : c == '['
          · rw [ite_eq_left hbr, ite_eq_left hbr, step true false]
          · rw [ite_eq_right hbr, ite_eq_right hbr]
            by_cases hsl : c == '/'
            · rw [ite_eq_left hsl, ite_eq_left hsl]; simp
            · rw [ite_eq_right hsl, ite_eq_right hsl, step false false]

/-- The reader a regular expression literal used to be read with: the whole
input becomes a `List Char`, the pattern is accumulated character by
character, and the flags are read from a fresh string. -/
def parseAcc? (raw : String) : Option RegExpLit := do
  match raw.toList with
  | '/' :: rest =>
      let (pat, flagChars) ← splitPatternAcc [] false false rest
      let source ← NonEmptyString.fromString? (String.ofList pat)
      let flags ← RegExpFlags.parse? (String.ofList flagChars)
      some ⟨source, flags⟩
  | _ => none

/-- The in-place reader reads exactly what the reader it replaced read. -/
theorem parse?_eq_parseAcc? (raw : String) : parse? raw = parseAcc? raw := by
  rw [parse?_eq_parseList?]
  unfold parseList? parseAcc?
  match raw.toList with
  | [] => rfl
  | c :: rest =>
    by_cases hslash : c = '/'
    · subst hslash
      simp only [splitPatternAcc_eq rest [] false false, List.reverse_nil, List.nil_append]
      cases splitList? false false rest with
      | none => rfl
      | some r => simp [RegExpFlags.readChars_ofList]
    · simp [hslash]

end RegExpLit

end Language.JavaScript
