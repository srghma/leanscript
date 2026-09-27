/-
Reading and writing the text of JavaScript literals.

A `MiniAST.MiniExpr.string` holds the characters the literal denotes, so
that `'a\n'` and `"a\u000a"` give the same node; the same holds of the text
of a JSX child, of the value of a JSX attribute and of the text of a
template literal.  This module is the boundary between those *values* and
the *source text* that denotes them:

* `decodeStringLiteral` reads a string literal, quotes included, and
  returns the characters it denotes;
* `encodeStringLiteral`, `encodeJSXText`, `encodeJSXAttrString` and
  `encodeTemplateText` write a value back as source text.

Nothing here mentions the syntax tree, so the printers of both trees share
it.

A literal is decoded, and a value encoded, *in place*: the source is read
by byte index and the result is built by pushing characters onto it, so
neither string is ever turned into a list of characters, and no
intermediate list or string is built.

Every scanning function takes a `fuel` argument bounding the number of
characters left to read; the number of bytes left is always enough, since
every step consumes at least one byte.
-/
import LanguageJavascriptCommon.Common

namespace Language.JavaScript.MiniAST

/-! ## Encoding a string literal -/

/-- Push the spelling of `c` in a literal quoted with `quote` onto `acc`. -/
private def pushEscaped (quote : Char) (acc : String) (c : Char) : String :=
  if c == quote then (acc.push '\\').push quote
  else if c == '\\' then (acc.push '\\').push '\\'
  else if c == '\n' then (acc.push '\\').push 'n'
  else if c == '\r' then (acc.push '\\').push 'r'
  else if c == '\t' then (acc.push '\\').push 't'
  else if c.toNat == 8 then (acc.push '\\').push 'b'
  else if c.toNat == 12 then (acc.push '\\').push 'f'
  else if c.toNat == 11 then (acc.push '\\').push 'v'
  else if c.toNat < 0x20 || c.toNat == 0x7F then
    let hex := Nat.toDigits 16 c.toNat
    let acc := (acc.push '\\').push 'x'
    let acc := if hex.length == 1 then acc.push '0' else acc
    hex.foldl (fun acc d => acc.push d) acc
  else acc.push c

/-- The quote a literal holding `value` is written with, given the quote
that is preferred (prettier's `singleQuote` chooses which that is): the
preferred one, unless the value holds more of it than of the other, in
which case writing the other escapes fewer characters. -/
def quoteFor (preferred : Char) (value : String) : Char :=
  let other := if preferred == '"' then '\'' else '"'
  let (pref, alt) :=
    value.foldl (fun (n : Nat × Nat) c =>
      if c == preferred then (n.1 + 1, n.2) else if c == other then (n.1, n.2 + 1) else n) (0, 0)
  if pref > alt then other else preferred

/-- Render a string value as a JavaScript literal, preferring `preferred`
as its quote. -/
def encodeStringLiteralQuoted (preferred : Char) (value : String) : String :=
  let quote := quoteFor preferred value
  (value.foldl (pushEscaped quote) (String.singleton quote)).push quote

/-- Render a string value as a JavaScript literal, with double quotes
preferred, which is prettier's default. -/
def encodeStringLiteral (value : String) : String :=
  encodeStringLiteralQuoted '"' value

/-! ## JSX text and attribute values -/

/-- Render the text of a JSX child, which holds the characters it denotes,
as it is written between the tags: the characters a parser would read as
markup, or as an entity, are written as entities themselves. -/
def encodeJSXText (value : String) : String :=
  value.foldl (fun acc c =>
    if c == '&' then acc ++ "&amp;"
    else if c == '<' then acc ++ "&lt;"
    else if c == '>' then acc ++ "&gt;"
    else if c == '{' then acc ++ "&#123;"
    else if c == '}' then acc ++ "&#125;"
    else acc.push c) ""

/-- Render the value of a JSX attribute as a quoted literal.  The quote is
the one that has to be written as an entity the fewer times, double quotes
when it is a draw, as prettier chooses it; the occurrences of that quote,
and every ampersand, are written as entities. -/
def encodeJSXAttrStringQuoted (preferred : Char) (value : String) : String :=
  let quote := quoteFor preferred value
  let body := value.foldl (fun acc c =>
    if c == '&' then acc ++ "&amp;"
    else if c == quote then acc ++ (if quote == '"' then "&quot;" else "&apos;")
    else acc.push c) ""
  (String.singleton quote ++ body).push quote

/-- Render the value of a JSX attribute with double quotes preferred,
which is prettier's default. -/
def encodeJSXAttrString (value : String) : String :=
  encodeJSXAttrStringQuoted '"' value

/-! ## Template literal text -/

/-- Push the spelling of `c` in a template literal onto `acc`; `c` is a
character other than the `$` of a `${`. -/
private def pushTemplateChar (acc : String) (c : Char) : String :=
  if c == '\\' then (acc.push '\\').push '\\'
  else if c == '`' then (acc.push '\\').push '`'
  else if c == '\r' then (acc.push '\\').push 'r'
  else acc.push c

/-- Render the text of a template literal, which holds the characters it
denotes, as it is written between the backticks: a backslash, a backtick
and the `${` which would start a substitution are escaped, and so is a
carriage return, which a parser would otherwise read as a line feed.  A
line feed itself stands as it is: a template literal may span lines. -/
def encodeTemplateText (value : String) : String :=
  -- a `$` is held back until the character after it is known, since it is
  -- escaped only when a `{` follows it
  let (acc, dollar) :=
    value.foldl (fun (st : String × Bool) c =>
      if st.2 then
        if c == '{' then (((st.1.push '\\').push '$').push '{', false)
        else if c == '$' then (st.1.push '$', true)
        else (pushTemplateChar (st.1.push '$') c, false)
      else if c == '$' then (st.1, true)
      else (pushTemplateChar st.1 c, false)) ("", false)
  if dollar then acc.push '$' else acc

/-! ## Decoding a string literal -/

private def isHighSurrogate (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDBFF
private def isLowSurrogate (n : Nat) : Bool := 0xDC00 ≤ n && n ≤ 0xDFFF

/-- The value of the `count` hexadecimal digits of `raw` at the byte index
`p`, and the index just after them; `none` if there are fewer than `count`
characters left, or one of them is not a digit. -/
private def hexRun? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Nat → Option (Nat × String.Pos.Raw)
  | 0, p, acc => some (acc, p)
  | count + 1, p, acc =>
      if stop ≤ p.byteIdx then none
      else
        match JSNumber.digitVal? (String.Pos.Raw.get raw p) with
        | none => none
        | some d => hexRun? raw stop count (String.Pos.Raw.next raw p) (16 * acc + d)

/-- The value of the hexadecimal digits of `raw` from the byte index `p` up
to a `}`, and the index just after the `}`; `none` if there is no digit, a
character which is not one, or no closing brace. -/
private def hexBrace? (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → Nat → Bool → Option (Nat × String.Pos.Raw)
  | 0, _, _, _ => none
  | fuel + 1, p, acc, any =>
      if stop ≤ p.byteIdx then none
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '}' then (if any then some (acc, q) else none)
        else
          match JSNumber.digitVal? c with
          | none => none
          | some d => hexBrace? raw stop fuel q (16 * acc + d) true

/-- The escape sequence written in `raw` at the byte index `p`, `bs` being
the index of the backslash which starts it: the characters it denotes,
pushed onto `acc`, and the index just after the sequence.  An unknown escape
stands for the escaped character itself, and an escape denoting no character
at all stands for the text it is written with. -/
private def decodeEscapeAt (raw : String) (stop : Nat) (bs p : String.Pos.Raw) (acc : String) :
    String × String.Pos.Raw :=
  -- the character of code `n`, or the source text of the escape if there is
  -- no such character
  let plain (n : Nat) (rest : String.Pos.Raw) : String × String.Pos.Raw :=
    if n.isValidChar then (acc.push (Char.ofNat n), rest)
    else (acc ++ String.Pos.Raw.extract raw bs rest, rest)
  let verbatim (rest : String.Pos.Raw) : String × String.Pos.Raw :=
    (acc ++ String.Pos.Raw.extract raw bs rest, rest)
  if stop ≤ p.byteIdx then (acc, p)
  else
    let c := String.Pos.Raw.get raw p
    let q := String.Pos.Raw.next raw p
    if c == 'n' then (acc.push '\n', q)
    else if c == 't' then (acc.push '\t', q)
    else if c == 'r' then (acc.push '\r', q)
    else if c == 'b' then (acc.push (Char.ofNat 8), q)
    else if c == 'f' then (acc.push (Char.ofNat 12), q)
    else if c == 'v' then (acc.push (Char.ofNat 11), q)
    else if c == '\n' then (acc, q)                       -- line continuation
    else if c == '\r' then
      if q.byteIdx < stop && String.Pos.Raw.get raw q == '\n' then
        (acc, String.Pos.Raw.next raw q)
      else (acc, q)
    else if c == 'x' then
      match hexRun? raw stop 2 q 0 with
      | some (n, r) => plain n r
      | none => (acc.push 'x', q)
    else if c == 'u' then
      if q.byteIdx < stop && String.Pos.Raw.get raw q == '{' then
        match hexBrace? raw stop stop (String.Pos.Raw.next raw q) 0 false with
        | some (n, r) => plain n r
        | none => (acc.push 'u', q)
      else
        match hexRun? raw stop 4 q 0 with
        | some (n, r) =>
            if isHighSurrogate n then
              -- combine with a following low surrogate, if there is one
              let r1 := String.Pos.Raw.next raw r
              let r2 := String.Pos.Raw.next raw r1
              if r.byteIdx < stop && String.Pos.Raw.get raw r == '\\' &&
                  r1.byteIdx < stop && String.Pos.Raw.get raw r1 == 'u' then
                match hexRun? raw stop 4 r2 0 with
                | some (m, r') =>
                    if isLowSurrogate m then
                      plain (0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)) r'
                    else verbatim r
                | none => verbatim r
              else verbatim r
            else plain n r
        | none => (acc.push 'u', q)
    else if c == '0' then
      if q.byteIdx < stop && '0' ≤ String.Pos.Raw.get raw q &&
          String.Pos.Raw.get raw q ≤ '9' then (acc.push '0', q)
      else (acc.push (Char.ofNat 0), q)
    else (acc.push c, q)

/-- Decode the text of `raw` between the byte index `p` and `stop`, pushing
the characters it denotes onto `acc`. -/
private def decodeFrom (raw : String) (stop : Nat) :
    Nat → String.Pos.Raw → String → String
  | 0, _, acc => acc
  | fuel + 1, p, acc =>
      if stop ≤ p.byteIdx then acc
      else
        let c := String.Pos.Raw.get raw p
        let q := String.Pos.Raw.next raw p
        if c == '\\' then
          let (acc, r) := decodeEscapeAt raw stop p q acc
          decodeFrom raw stop fuel r acc
        else decodeFrom raw stop fuel q (acc.push c)

/-- Decode a JavaScript string literal, given with its surrounding quotes,
into the characters it denotes. -/
def decodeStringLiteral (raw : String) : String :=
  let size := raw.utf8ByteSize
  if size == 0 then ""
  else
    let q := String.Pos.Raw.get raw ⟨0⟩
    if q == '"' || q == '\'' then
      -- a quote is one byte wide, so the body starts at index one
      let close := String.Pos.Raw.prev raw ⟨size⟩
      if 0 < close.byteIdx && String.Pos.Raw.get raw close == q then
        decodeFrom raw close.byteIdx size ⟨1⟩ ""
      else decodeFrom raw size size ⟨1⟩ ""
    else decodeFrom raw size size ⟨0⟩ ""

end Language.JavaScript.MiniAST
