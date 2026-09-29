module

/-
Refined component types shared by the three JavaScript ASTs.

The three trees of this project — the faithful port in
`Language.JavaScript.Parser.AST`, the deterministic `MiniAST` and the scope
safe `BrujinAST` — used to describe the same things with different, and much
too wide, Lean types: a name was a `String` (so it could be empty), and a
numeric literal was a `String` too (so it could be `"potato"`).

This module collects the refined types all three of them use:

* `NonEmptyString` (from the `NonEmpty` library), a string which carries a
  proof that it is not `""`;
* `NonEmptyList` (from the `NonEmpty` library), a list which cannot be empty;
* `JSNumber`, a numeric literal *as a number* — an exact decimal, an exact
  natural number in base two, eight or sixteen, or a `BigInt`;
* `RegExpFlags` and `RegExpLit`, a regular expression literal with its flags
  (read by scanning the source in place; `LanguageJavascriptCommon.RegExpLitSpec`
  proves that this reads what the list based reader reads)
  as a record of booleans rather than an unchecked string;
* `JSStringSrc`, a string literal of the annotated tree — its quote and the
  source text between the quotes, so that the escapes the source wrote are
  kept and a literal can be neither unterminated nor closed by the wrong
  quote.  Numeric and regular expression literals are *not* kept this way:
  all three trees store their value (`JSNumber`, `RegExpLit`) and print it
  canonically.

Everything here lives in the `Language.JavaScript` namespace, which is the
parent of the namespace of each of the three trees, so the names are visible
inside all of them without an `open`.
-/

public import NonEmpty.String
public import NonEmpty.ListCorrectByConstruction.Basic

@[expose] public section

open NonEmpty.String

namespace NonEmpty.String.NonEmptyString

instance : Inhabited NonEmptyString := ⟨⟨"_", by decide⟩⟩

/-- The non-empty string `s`; a placeholder if `s` is empty. -/
def fromString! (s : String) : NonEmptyString :=
  if h : s ≠ "" then ⟨s, h⟩ else default

@[simp] theorem toString_fromString! {s : String} (h : s ≠ "") :
    (fromString! s).toString = s := by
  simp [fromString!, h]

/-- Append a possibly empty string on the right; the result is still not
empty. -/
def appendRight (s : NonEmptyString) (t : String) : NonEmptyString :=
  ⟨s.toString ++ t, fun h => s.isNonEmpty (String.append_eq_empty_iff.mp h).1⟩

/-- A single character, as a non-empty string. -/
def ofChar (c : Char) : NonEmptyString :=
  ⟨String.singleton c, by intro h; simp only [String.singleton_ne_empty] at h⟩

/-- The text of `raw` between two byte offsets, as a non-empty string;
`none` if there is none.

This is the *in place* reader: the text is sliced out of `raw` at the
offsets the lexer left, so the token text is never built as a string of its
own first, and the emptiness test is the byte size of the slice rather than
a comparison against `""`.  `NonEmptyString.ofRange?_eq` (in
`TokenTextSpec`) says that it reads what `fromString?` reads. -/
def ofRange? (raw : String) (start stop : String.Pos.Raw) : Option NonEmptyString :=
  let s := String.Pos.Raw.extract raw start stop
  if h : s.utf8ByteSize = 0 then none
  else some ⟨s, fun he => h (by rw [he]; rfl)⟩

/-- The text of `raw` between two byte offsets; a placeholder if there is
none. -/
def ofRange! (raw : String) (start stop : String.Pos.Raw) : NonEmptyString :=
  (ofRange? raw start stop).getD default

/-- The text of a substring of the input, as a non-empty string. -/
def ofSubstring? (ss : Substring.Raw) : Option NonEmptyString :=
  ofRange? ss.str ss.startPos ss.stopPos

/-- The text of a substring of the input; a placeholder if it is empty. -/
def ofSubstring! (ss : Substring.Raw) : NonEmptyString := (ofSubstring? ss).getD default

end NonEmpty.String.NonEmptyString

namespace Language.JavaScript

/-! ## Non-empty strings

Identifiers, labels, module names and the like are a `NonEmptyString` — a
string which carries a proof that it is not `""` — so that no tree of this
project can describe a program with a nameless name.  The type is the one
of the `NonEmpty` library; what this module adds are the readers the lexer
needs, which build one out of the source text in place. -/

export NonEmpty.String (NonEmptyString)


/-! ## Non-empty lists

Lists of the trees that cannot be empty (the links of an optional chain, the declarators of a
declaration, …) are a `NonEmptyList` of the `NonEmpty` library: the first element is a field
(`head`) rather than a proof, so the ASTs can nest it inside their own recursive types. -/

export NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-! ## Numeric literals

A numeric literal used to be stored as the text it was written with, which
made `JSDecimal "potato"` a perfectly good tree and made two spellings of
the same number two different trees.  `JSNumber` stores the *number*, in
all three trees, and `JSNumber.render` writes it back canonically. -/

/-- The base a numeric literal is written in. -/
inductive NumBase where
  /-- `0b1010` -/
  | binary
  /-- `0o17`, and the legacy `017` -/
  | octal
  /-- `17`, `1.5`, `1e3` -/
  | decimal
  /-- `0xff` -/
  | hexadecimal
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace NumBase

/-- The radix: 2, 8, 10 or 16. -/
def radix : NumBase → Nat
  | .binary => 2
  | .octal => 8
  | .decimal => 10
  | .hexadecimal => 16

/-- The `0b`/`0o`/`0x` prefix a literal in this base is written with; base
ten literals have none. -/
def prefixText : NumBase → String
  | .binary => "0b"
  | .octal => "0o"
  | .decimal => ""
  | .hexadecimal => "0x"

end NumBase

/-- A JavaScript numeric literal, as a number.

A JavaScript `Number` is an IEEE-754 double, but a *literal* is written in
decimal (or in base two, eight or sixteen), and the shortest decimal
spelling of a double is not something one wants to have to compute in order
to print a tree.  A literal is therefore stored exactly, the way it is
written:

* `decimal m e` is the base ten literal denoting exactly `m * 10 ^ e`;
  `1.5` is `decimal 15 (-1)` and `2e3` is `decimal 2 3`.  The
  representation is *canonical* — `normalize` removes the trailing zeros of
  the mantissa — so two spellings of the same number give equal values,
  which is what the deterministic AST needs;
* `radix b v` is `0b…`, `0o…` or `0x…`, denoting the natural number `v`
  exactly;
* `bigint b v` is a `BigInt` literal, `123n` or `0xffn`, of arbitrary
  precision.

A literal is never negative: `-1` is the unary minus applied to `1`. -/
inductive JSNumber where
  /-- A base ten literal denoting exactly `mantissa * 10 ^ exponent`. -/
  | decimal (mantissa : Nat) (exponent : Int)
  /-- A literal in base two, eight or sixteen. -/
  | radix (base : NumBase) (value : Nat)
  /-- A `BigInt` literal, written in `base`. -/
  | bigint (base : NumBase) (value : Nat)
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace JSNumber

/-- Strip the trailing zeros of a base ten mantissa, moving them into the
exponent; `fuel` bounds the number of steps, and `m` is always enough of
it, since each step divides `m` by ten.

The recursion is structural, on the fuel, rather than well founded on `m`,
so that the kernel can evaluate it: a literal of the annotated tree carries
a proof that its spelling parses, and `JSNumber.parse?` normalises through
this function. -/
def stripZerosAux : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | fuel + 1, m, e => if m % 10 == 0 then stripZerosAux fuel (m / 10) (e + 1) else (m, e)

/-- Strip the trailing zeros of a base ten mantissa, moving them into the
exponent. -/
def stripZeros (m : Nat) (e : Int) : Nat × Int :=
  if m == 0 then (0, 0) else stripZerosAux m m e

/-- The canonical form of a literal: the mantissa of a base ten literal has
no trailing zeros, zero is `decimal 0 0`, and a base ten `radix` literal is
a `decimal` one. -/
def normalize : JSNumber → JSNumber
  | .decimal m e => let (m', e') := stripZeros m e; .decimal m' e'
  | .radix .decimal v => let (m', e') := stripZeros v 0; .decimal m' e'
  | .radix b v => .radix b v
  | .bigint b v => .bigint b v

/-- The literal denoting the natural number `n` in base ten. -/
def ofNat (n : Nat) : JSNumber := normalize (.decimal n 0)

instance : OfNat JSNumber n := ⟨ofNat n⟩

/-- Whether the literal is a `BigInt` one. -/
def isBigInt : JSNumber → Bool
  | .bigint _ _ => true
  | _ => false

/-- The base the literal is written in. -/
def base : JSNumber → NumBase
  | .decimal _ _ => .decimal
  | .radix b _ => b
  | .bigint b _ => b

/-- `b ^ e`, as a plain function so that a literal value reduces. -/
def powNat (b e : Nat) : Nat := b ^ e

/-- The exact value of the literal, when it is an integer; `none` for a
base ten literal with a negative exponent. -/
def toNat? : JSNumber → Option Nat
  | .decimal m e => if e ≥ 0 then some (m * powNat 10 e.toNat) else none
  | .radix _ v => some v
  | .bigint _ v => some v

/-- The value of the literal as an IEEE-754 double.  This is the value the
JavaScript engine would compute; it is a best effort conversion and, like
JavaScript itself, it loses precision for values a double cannot hold. -/
def toFloat : JSNumber → Float
  | .decimal m e =>
      if e ≥ 0 then Float.ofNat (m * powNat 10 e.toNat)
      else Float.ofNat m / Float.ofNat (powNat 10 (-e).toNat)
  | .radix _ v => Float.ofNat v
  | .bigint _ v => Float.ofNat v

/-! ### Rendering -/

/-- The character a digit of value `d < 16` is written with. -/
def digitChar (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + d - 10)

/-- The digits of `n` in base `base`, most significant first, pushed straight
into `acc`: no list of characters is built on the way (`Nat.toDigits`, which
this replaced, builds one).  `fuel` bounds the number of digits — `n + 1` is
always enough, since each step divides `n` by `base` — so the spelling of a
literal is a structural definition and still reduces in the kernel.

`LanguageJavascriptCommon.LiteralPrintSpec` proves it gives, for every base up to
sixteen and every number, exactly the digits `Nat.toDigits` gives. -/
def digitsAux (base : Nat) : Nat → Nat → String → String
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let rest := n / base
      let acc := if rest == 0 then acc else digitsAux base fuel rest acc
      acc.push (digitChar (n % base))

/-- The spelling of `n` in base `base`. -/
def digitsOf (base : Nat) (n : Nat) : String :=
  if n == 0 then "0" else digitsAux base (n + 1) n ""

def repeatChar (c : Char) (n : Nat) : String := String.pushn "" c n

/-- Render a base ten literal `mantissa * 10 ^ exponent`, following the
`Number::toString` rules of ECMAScript: a plain decimal spelling when the
decimal point falls within a reasonable range, and the exponent form
otherwise.  Unlike ECMAScript, a positive exponent is written without a
`+`, the way `prettier` normalises it. -/
def renderDecimal (mantissa : Nat) (exponent : Int) : String :=
  if mantissa == 0 then "0"
  else
    let s := digitsOf 10 mantissa
    let k : Int := Int.ofNat s.length
    -- the value is `0.s * 10 ^ n`
    let n : Int := k + exponent
    if k ≤ n && n ≤ 21 then
      s ++ repeatChar '0' (n - k).toNat
    else if 0 < n && n ≤ 21 then
      -- a digit is one byte wide, so the point falls at the byte index `n`
      String.Pos.Raw.extract s ⟨0⟩ ⟨n.toNat⟩ ++ "." ++
        String.Pos.Raw.extract s ⟨n.toNat⟩ ⟨s.utf8ByteSize⟩
    else if -6 < n && n ≤ 0 then
      "0." ++ repeatChar '0' (-n).toNat ++ s
    else
      let head := String.Pos.Raw.extract s ⟨0⟩ ⟨1⟩
      let tail := String.Pos.Raw.extract s ⟨1⟩ ⟨s.utf8ByteSize⟩
      let e := n - 1
      (if tail.isEmpty then head else head ++ "." ++ tail) ++ "e" ++
        (if e < 0 then "-" ++ toString (-e) else toString e)

/-- The canonical spelling of the literal.  Letters are lower case, there
are no superfluous zeros, and the value is not changed. -/
def render (x : JSNumber) : String :=
  match x.normalize with
  | .decimal m e => renderDecimal m e
  | .radix b v => b.prefixText ++ digitsOf b.radix v
  | .bigint b v => b.prefixText ++ digitsOf b.radix v ++ "n"

/-- The canonical spelling of the literal; never empty. -/
def toNonEmptyString (x : JSNumber) : NonEmptyString := NonEmptyString.fromString! x.render

instance : ToString JSNumber := ⟨render⟩

/-! ### Parsing -/

/-- The value of the digit written `c`, in base sixteen; `none` if `c` is
not a digit. -/
def digitVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-! A numeric literal is read *in place*, by byte index, rather than by
turning its spelling into a list of characters and filtering the numeric
separators out of it: the reader below allocates nothing at all, and builds
no intermediate string.  A separator is skipped wherever it is met, which is
exactly what removing it beforehand did.

Every scanning function takes a `fuel` argument bounding the number of
characters left to read — the number of bytes left is always enough, since
every step consumes at least one byte — so that the recursion is structural
and a literal spelling still reduces in the kernel.

`LanguageJavascriptCommon.NumberLitSpec` proves that this reader returns, on every
input, exactly what the previous list based one returned. -/

/-- The next character at or after the byte index `p` which is not a numeric
separator, together with the index just after it; `none` once `stop` is
reached. -/
def nextChar? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Option (Char × String.Pos.Raw)
  | 0, _ => none
  | fuel + 1, p =>
      if stop ≤ p.byteIdx then none
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '_' then nextChar? raw stop fuel q else some (c, q)

/-- The value of the digits of `raw` between the byte index `p` and `stop`,
read in base `radix`, `acc` being the value of the digits read so far
(`none` when there are none yet).  It is `none` if the range holds no digit,
or a character which is not a digit of that base — the separators aside. -/
def digitsFrom? (raw : String) (stop radix : Nat) :
    Nat → String.Pos.Raw → Option Nat → Option Nat
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
      if stop ≤ p.byteIdx then acc
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '_' then digitsFrom? raw stop radix fuel q acc
        else
          match digitVal? c with
          | none => none
          | some d =>
              if d < radix then
                digitsFrom? raw stop radix fuel q (some (radix * acc.getD 0 + d))
              else none

/-- Read the mantissa of a base ten literal: its digits and at most one
decimal point, up to `stop` or to the `e` which starts the exponent.
Returns the value of the digits, how many of them are after the point, and
the byte index the exponent starts at; `none` if there is no digit, or a
character which belongs to neither part. -/
def mantissaFrom? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Nat → Nat → Nat → Bool → Option (Nat × Nat × String.Pos.Raw)
  | 0, p, m, nd, nf, _ => if nd == 0 then none else some (m, nf, p)
  | fuel + 1, p, m, nd, nf, dot =>
      if stop ≤ p.byteIdx then (if nd == 0 then none else some (m, nf, p))
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '_' then mantissaFrom? raw stop fuel q m nd nf dot
        else if c == '.' then
          if dot then none else mantissaFrom? raw stop fuel q m nd nf true
        else if c == 'e' || c == 'E' then
          if nd == 0 then none else some (m, nf, q)
        else
          match digitVal? c with
          | some d =>
              if d < 10 then
                mantissaFrom? raw stop fuel q (10 * m + d) (nd + 1) (if dot then nf + 1 else nf) dot
              else none
          | none => none

/-- Read the exponent of a base ten literal, written between the byte index
`p` and `stop`: a sign and at least one digit, or nothing at all, which is
an exponent of zero. -/
def expFrom? (raw : String) (stop : Nat) (fuel : Nat) (p : String.Pos.Raw) : Option Int :=
  match nextChar? raw stop fuel p with
  | none => some 0
  | some (c, q) =>
      if c == '-' then (digitsFrom? raw stop 10 fuel q none).map (fun n => -(Int.ofNat n))
      else if c == '+' then (digitsFrom? raw stop 10 fuel q none).map Int.ofNat
      else (digitsFrom? raw stop 10 fuel p none).map Int.ofNat

/-- Where the digits of `raw` end, and whether it is a `BigInt` literal:
scanning back from the byte index `p`, past the separators, an `n` is the
suffix of a `BigInt` and ends the digits.  `size` is the length of `raw` in
bytes, which is where the digits end otherwise. -/
def bigSuffix (raw : String) (size : Nat) : Nat → String.Pos.Raw → Nat × Bool
  | 0, _ => (size, false)
  | fuel + 1, p =>
      if p.byteIdx == 0 then (size, false)
      else
        let q := String.Pos.Raw.prev raw p
        let c := String.Pos.Raw.get raw q
        if c == '_' then bigSuffix raw size fuel q
        else if c == 'n' then (q.byteIdx, true)
        else (size, false)

/-- The literal of base `b` denoting `v`, as a `BigInt` literal or not. -/
def ofRadixDigits (isBig : Bool) (b : NumBase) (v : Nat) : JSNumber :=
  if isBig then .bigint b v else (JSNumber.radix b v).normalize

/-- Read a base ten literal, `intPart [. fracPart] [e [+-] expPart]`,
written in `raw` between the byte index zero and `stop`; `size` bounds the
number of characters left to read. -/
def parseDecimal? (raw : String) (stop size : Nat) (isBig : Bool) : Option JSNumber :=
  match mantissaFrom? raw stop size ⟨0⟩ 0 0 0 false with
  | none => none
  | some (m, nf, pe) =>
      match expFrom? raw stop size pe with
      | none => none
      | some e =>
          if isBig then
            if nf == 0 && 0 ≤ e then some (.bigint .decimal (m * powNat 10 e.toNat)) else none
          else some (JSNumber.decimal m (e - Int.ofNat nf)).normalize

/-- Read a numeric literal, as it is written in JavaScript source.  Accepts
the `0b`/`0o`/`0x` prefixes in either case, the legacy `0…` octal form,
numeric separators (`1_000`) and the `n` suffix of a `BigInt`.

The spelling is scanned in place, by byte index; nothing is allocated. -/
def parse? (raw : String) : Option JSNumber :=
  let size := raw.utf8ByteSize
  let (stop, isBig) := bigSuffix raw size size ⟨size⟩
  match nextChar? raw stop size ⟨0⟩ with
  | none => none
  | some (c0, p1) =>
      if c0 == '0' then
        match nextChar? raw stop size p1 with
        | none => parseDecimal? raw stop size isBig
        | some (c1, p2) =>
            let base? : Option NumBase :=
              if c1 == 'x' || c1 == 'X' then some .hexadecimal
              else if c1 == 'o' || c1 == 'O' then some .octal
              else if c1 == 'b' || c1 == 'B' then some .binary
              else none
            match base? with
            | some b =>
                (digitsFrom? raw stop b.radix size p2 none).map (ofRadixDigits isBig b)
            | none =>
                -- the legacy octal form: `0` and octal digits only
                match digitsFrom? raw stop 8 size p1 none with
                | some v => some (ofRadixDigits isBig .octal v)
                | none => parseDecimal? raw stop size isBig
      else parseDecimal? raw stop size isBig

/-- Read a numeric literal; zero if it is not one. -/
def parse! (raw : String) : JSNumber := (parse? raw).getD (.decimal 0 0)

end JSNumber

/-! ## Regular expression literals

A regular expression literal used to be the source text between and
including the slashes.  It is now the pattern and the flags, the flags being
a record of booleans rather than a string that could say anything.

Only the *code* of the regular expression is described here: the pattern is
kept as it is written, and nothing in this module tries to say what it
means.  Reading the pattern, compiling it and matching with it are the job
of the [`lean-regex`](https://github.com/pandaman64/lean-regex) library;
`LanguageJavascriptCommon.RegExpEngine` is the bridge to it, and every function
there is total or answers `none` — this project has no regular expression
engine of its own.

Note that a `RegExp` object with the `g` or `y` flag is **not** pure at run
time — `exec` and `test` update its `lastIndex` — which is why the flag is
recorded but no state is. -/

/-- The flags of a regular expression literal. -/
structure RegExpFlags where
  /-- `d`, `hasIndices`. -/
  hasIndices : Bool := false
  /-- `g`, `global`.  A global regular expression object is stateful. -/
  global : Bool := false
  /-- `i`, `ignoreCase`. -/
  ignoreCase : Bool := false
  /-- `m`, `multiline`. -/
  multiline : Bool := false
  /-- `s`, `dotAll`. -/
  dotAll : Bool := false
  /-- `u`, `unicode`. -/
  unicode : Bool := false
  /-- `v`, `unicodeSets`. -/
  unicodeSets : Bool := false
  /-- `y`, `sticky`.  A sticky regular expression object is stateful. -/
  sticky : Bool := false
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpFlags

/-- The flags, in the canonical order `dgimsuvy`. -/
def render (f : RegExpFlags) : String :=
  (if f.hasIndices then "d" else "") ++
  (if f.global then "g" else "") ++
  (if f.ignoreCase then "i" else "") ++
  (if f.multiline then "m" else "") ++
  (if f.dotAll then "s" else "") ++
  (if f.unicode then "u" else "") ++
  (if f.unicodeSets then "v" else "") ++
  (if f.sticky then "y" else "")

instance : ToString RegExpFlags := ⟨render⟩

/-- Add the flag written `c`; `none` if `c` is not a flag, or is one the
literal already has. -/
@[inline] def add? (f : RegExpFlags) (c : Char) : Option RegExpFlags :=
  match c with
  | 'd' => if f.hasIndices then none else some { f with hasIndices := true }
  | 'g' => if f.global then none else some { f with global := true }
  | 'i' => if f.ignoreCase then none else some { f with ignoreCase := true }
  | 'm' => if f.multiline then none else some { f with multiline := true }
  | 's' => if f.dotAll then none else some { f with dotAll := true }
  | 'u' => if f.unicode then none else some { f with unicode := true }
  | 'v' => if f.unicodeSets then none else some { f with unicodeSets := true }
  | 'y' => if f.sticky then none else some { f with sticky := true }
  | _ => none

/-- Read the flags written in `s` between `p` and the byte index `stop`,
adding them to `f`.

The characters are read in place, by byte index, so that reading the flags
of a literal costs no allocation at all: neither the list of the characters
of `s`, nor a copy of the text of the flags.  `fuel` bounds the number of
characters left to read; `stop - p` bytes is always enough, since every step
consumes at least one byte. -/
def scanFrom (s : String) (stop : Nat) :
    Nat → String.Pos.Raw → RegExpFlags → Option RegExpFlags
  | 0, p, f => if stop ≤ p.byteIdx then some f else none
  | fuel + 1, p, f =>
      if stop ≤ p.byteIdx then some f
      else
        match f.add? (String.Pos.Raw.get s p) with
        | none => none
        | some f' => scanFrom s stop fuel (String.Pos.Raw.next s p) f'

/-- Read the flags of `s` between the byte indices `start` and `stop`;
`none` if the text there contains an unknown or a repeated flag. -/
def parseRange? (s : String) (start stop : Nat) : Option RegExpFlags :=
  scanFrom s stop (stop - start) ⟨start⟩ {}

/-- Read a flag string; `none` if it contains an unknown or repeated
flag. -/
def parse? (s : String) : Option RegExpFlags := parseRange? s 0 s.utf8ByteSize

/-- Whether a `RegExp` object built with these flags keeps state between
calls: `g` and `y` make `exec`/`test` advance `lastIndex`. -/
def isStateful (f : RegExpFlags) : Bool := f.global || f.sticky

end RegExpFlags

/-- A regular expression literal: the pattern between the slashes, and the
flags after the closing one. -/
structure RegExpLit where
  /-- The pattern, without the delimiting slashes.  It cannot be empty:
  `//` starts a comment, and an empty pattern is written `/(?:)/`. -/
  source : NonEmptyString
  /-- The flags. -/
  flags : RegExpFlags := {}
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace RegExpLit

/-- The literal, as it is written in source: `/source/flags`. -/
def render (r : RegExpLit) : String :=
  "/" ++ r.source.toString ++ "/" ++ r.flags.render

/-- The literal, as it is written in source; never empty. -/
def toNonEmptyString (r : RegExpLit) : NonEmptyString := NonEmptyString.fromString! r.render

instance : ToString RegExpLit := ⟨render⟩

/-- The byte index of the `/` which closes the literal, scanning `raw` from
the byte index `p`.

The rule is the one the lexer scans a `RegExToken` with: outside a
character class a backslash escapes the character after it, `[` opens a
class and `/` closes the literal; inside a class nothing is special except
`]`, which closes the class.  Reading a literal therefore accepts exactly
the tokens the lexer produces.

The scan reads `raw` in place, one byte index at a time, so it allocates
nothing: no list of characters, no accumulator, and no intermediate copy of
the pattern.  `fuel` bounds the number of characters left to read; the
number of bytes left is always enough, since every step consumes at least
one byte. -/
def scanClose (raw : String) :
    Nat → String.Pos.Raw → Bool → Bool → Option String.Pos.Raw
  | 0, _, _, _ => none
  | fuel + 1, p, inClass, escaped =>
      if raw.utf8ByteSize ≤ p.byteIdx then none
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if escaped then scanClose raw fuel q inClass false
        else if inClass then scanClose raw fuel q (c != ']') false
        else if c == '\\' then scanClose raw fuel q false true
        else if c == '[' then scanClose raw fuel q true false
        else if c == '/' then some p
        else scanClose raw fuel q false false

/-- Read a literal of the form `/source/flags`.

The literal is scanned in place: the only string built is the pattern
itself, sliced out of `raw` in one go once the closing `/` has been found.
The flags are read straight from `raw`, and `raw` is never turned into a
list of characters. -/
def parse? (raw : String) : Option RegExpLit :=
  let size := raw.utf8ByteSize
  if size == 0 || String.Pos.Raw.get raw ⟨0⟩ != '/' then none
  else
    -- the pattern starts just after the opening `/`, which is one byte wide
    let start : String.Pos.Raw := ⟨1⟩
    match scanClose raw size start false false with
    | none => none
    | some close =>
        match NonEmptyString.fromString? (String.Pos.Raw.extract raw start close) with
        | none => none
        | some source =>
            match RegExpFlags.parseRange? raw (close.byteIdx + 1) size with
            | none => none
            | some flags => some ⟨source, flags⟩

/-- Read a literal of the form `/source/flags`; a placeholder if it is not
one. -/
def parse! (raw : String) : RegExpLit := (parse? raw).getD default

end RegExpLit

/-! ## Literals as they are written in source

The three trees store the *value* of a numeric and of a regular expression
literal — a `JSNumber`, a `RegExpLit` — and print it canonically, the way
`prettier` would: `0X1f` comes back as `0x1f`, `070` as `0o70`, `1.50` as
`1.5`.  Parsing and printing therefore do not preserve the exact source
spelling of a number or a pattern, only its meaning.

A string literal is different: the escapes it is written with (`\u0041`,
`\x41`, `A`) all denote the same characters, and rewriting them would be a
change of source, not a normalisation.  `JSStringSrc` keeps the quote and
the source text between the quotes, so a string literal of the annotated
tree can be neither unterminated nor terminated by the wrong quote by
construction. -/

/-- Which quote a string literal is written with. -/
inductive QuoteKind where
  /-- `'a'` -/
  | single
  /-- `"a"` -/
  | double
deriving Repr, BEq, DecidableEq, Inhabited, Hashable

namespace QuoteKind

/-- The quote character. -/
def char : QuoteKind → Char
  | .single => '\''
  | .double => '"'

/-- The quote character, as a string. -/
def text (q : QuoteKind) : String := String.singleton q.char

/-- The kind of quote `c` is, if it is one. -/
def ofChar? (c : Char) : Option QuoteKind :=
  if c == '\'' then some .single else if c == '"' then some .double else none

end QuoteKind

/-- A string literal of the annotated tree: the quote it is written with,
and the source text between the quotes — the escapes as they were written,
rather than the characters they denote. -/
structure JSStringSrc where
  /-- Whether the literal is written with `'` or with `"`. -/
  quote : QuoteKind
  /-- The source text between the quotes. -/
  body : String
deriving Repr, BEq, DecidableEq, Inhabited

namespace JSStringSrc

/-- The literal, as it is written in source, quotes included. -/
def render (s : JSStringSrc) : String := s.quote.text ++ s.body ++ s.quote.text

/-- The literal, as it is written in source; never empty. -/
def toNonEmptyString (s : JSStringSrc) : NonEmptyString :=
  ⟨s.render, by
    simp only [render, QuoteKind.text, ne_eq]
    intro h
    have h1 := (String.append_eq_empty_iff.mp h).1
    exact String.singleton_ne_empty (String.append_eq_empty_iff.mp h1).1⟩

instance : ToString JSStringSrc := ⟨render⟩

/-- The literal written `raw`, if `raw` is a quoted string.

The quotes are read at their byte indices and the body is sliced out in one
go; `raw` is never turned into a list of characters. -/
def ofString? (raw : String) : Option JSStringSrc :=
  let size := raw.utf8ByteSize
  if size == 0 then none
  else
    match QuoteKind.ofChar? (String.Pos.Raw.get raw ⟨0⟩) with
    | none => none
    | some q =>
        -- the opening quote is one byte wide, so the body starts at index one
        let close := String.Pos.Raw.prev raw ⟨size⟩
        if close.byteIdx == 0 then none
        else if String.Pos.Raw.get raw close == q.char then
          some ⟨q, String.Pos.Raw.extract raw ⟨1⟩ close⟩
        else none

/-- The literal written `raw`; the empty literal if `raw` is not a quoted
string. -/
def ofString! (raw : String) : JSStringSrc := (ofString? raw).getD default

/-- The literal written between two byte offsets of `raw`, if that is a
quoted string.

This is the *in place* reader the parser uses: the quotes are looked at
where the lexer left them and the body is sliced straight out of the input,
so the text of the token is not built first and sliced afterwards — the
only string built is the body itself.  `JSStringSrc.ofRange?_eq` (in
`TokenTextSpec`) says that it reads what `ofString?` reads. -/
def ofRange? (raw : String) (start stop : String.Pos.Raw) : Option JSStringSrc :=
  if stop.byteIdx ≤ start.byteIdx then none
  else
    match QuoteKind.ofChar? (String.Pos.Raw.get raw start) with
    | none => none
    | some q =>
        -- a quote is one byte wide, so the body starts one byte after the
        -- opening one
        let close := String.Pos.Raw.prev raw stop
        if close.byteIdx ≤ start.byteIdx then none
        else if String.Pos.Raw.get raw close == q.char then
          some ⟨q, String.Pos.Raw.extract raw ⟨start.byteIdx + 1⟩ close⟩
        else none

/-- The literal a substring of the input spells, if it is a quoted
string. -/
def ofSubstring? (ss : Substring.Raw) : Option JSStringSrc :=
  ofRange? ss.str ss.startPos ss.stopPos

end JSStringSrc

end Language.JavaScript

end
