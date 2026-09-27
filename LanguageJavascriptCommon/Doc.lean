import LanguageJavascriptCommon.Unicode

/-!
# A Wadler-style document algebra

The layout engine used by the JavaScript printer.  It follows the algorithm
of the `prettier` code formatter closely enough that the printer built on
top of it can reproduce prettier's output: groups are laid out flat when
their first line fits, a forced break propagates to every enclosing group,
and a conditional group picks the first of its two alternatives whose first
line fits.
-/

namespace Language.JavaScript.Doc

/-- Whether the group being laid out is flat or broken. -/
inductive Mode where
  | flat | broken
deriving Inhabited, BEq

/-- A document. -/
inductive Doc where
  /-- The empty document. -/
  | nil
  /-- Literal text.  It may contain newlines, in which case the current
  column is recomputed from the text. -/
  | text (s : String)
  /-- A space if the enclosing group is flat, a newline otherwise. -/
  | line
  /-- Nothing if the enclosing group is flat, a newline otherwise. -/
  | softline
  /-- A soft line which, when it does break, makes the group that follows
  it be measured again, as a hard line does.  It is the line break written
  between two children of a JSX element that stand next to one another
  with no whitespace between them: a parser reads the break as whitespace,
  and prettier lays a line break it reads out as a hard line. -/
  | softlineRemeasure
  /-- Always a newline; it also forces every enclosing group to break. -/
  | hardline
  /-- Nothing at all, but it forces every enclosing group to break. -/
  | breakParent
  | cat (a b : Doc)
  /-- Increase the indentation of the newlines inside by one step. -/
  | nest (n : Nat) (d : Doc)
  /-- Align what is inside `n` columns further to the right: prettier's
  `align`, which differs from `nest` only under `useTabs`, where it adds
  one tab rather than `n` columns. -/
  | align (n : Nat) (d : Doc)
  /-- Print flat if it fits, broken otherwise. -/
  | group (d : Doc)
  /-- A group whose mode -- flat or broken -- is recorded under `id`, so
  that an `ifBreakOf` written anywhere after it can ask for it.  It is
  prettier's `group(doc, { id })`. -/
  | groupId (id : Nat) (d : Doc)
  /-- Choose according to whether the group recorded under `id` was
  broken; a group that has not been laid out yet counts as flat, as it
  does in prettier.  It is prettier's `ifBreak(…, …, { groupId })`. -/
  | ifBreakOf (id : Nat) (whenBroken whenFlat : Doc)
  /-- Undo one step of indentation inside: prettier's `dedent`. -/
  | dedent (d : Doc)
  /-- The group modes recorded inside are forgotten again once the
  document has been laid out, so that two documents built independently
  may use the same group ids without one of them being asked about the
  other's group.  Prettier's group ids are unique symbols and need no
  such scope. -/
  | scopeIds (d : Doc)
  /-- The engine's marker for the end of a `scopeIds`: it restores the
  recorded modes it carries.  It is written by the engine alone, and
  never stands in a document a printer builds. -/
  | restoreIds (ms : List (Nat × Mode))
  /-- A group that is always broken; like `group`, it forces every
  enclosing group to break. -/
  | groupBreak (d : Doc)
  /-- Print `flatAlt` if its first line fits, `expanded` otherwise.  Unlike
  `group`, a forced break inside the alternatives does not propagate to the
  enclosing groups, so `flatAlt` may itself contain newlines. -/
  | condGroup (flatAlt expanded : Doc)
  /-- A space before `body`, or a newline and `n` more columns of
  indentation when the first line of `body` would not fit after the space.
  It is prettier's "fluid" layout of the right hand side of an
  assignment. -/
  | fluidLine (n : Nat) (body : Doc)
  /-- Choose according to whether the enclosing group is broken. -/
  | ifBreak (whenBroken whenFlat : Doc)
  /-- Prettier's `fill`: the parts alternate contents and separators, and
  as many contents as fit are put on each line. -/
  | fill (parts : List Doc)
  /-- `head` laid out as a group, followed by `body`, which is indented by
  `n` columns when that group breaks, and then by `tail`, which is printed
  only when that group breaks.  It is prettier's `indentIfBreak`, together
  with an `ifBreak`, applied to the group they name. -/
  | groupIndentIfBreak (n : Nat) (head body tail : Doc)
deriving Inhabited

namespace Doc

instance : Append Doc := ⟨Doc.cat⟩

/-- Concatenate a list of documents. -/
def concat : List Doc → Doc
  | [] => .nil
  | [d] => d
  | d :: ds => d ++ concat ds

/-- Concatenate a list of documents, separated by `sep`. -/
def joinWith (sep : Doc) : List Doc → Doc
  | [] => .nil
  | [d] => d
  | d :: ds => d ++ sep ++ joinWith sep ds

/-- How the engine spells indentation: with spaces, or with one tab for
each step, which is how prettier writes it under `useTabs`.  A tab counts
as `tabWidth` columns either way. -/
structure Indentation where
  /-- The number of columns of one indentation step. -/
  tabWidth : Nat := 2
  /-- Whether to write a tab for each step. -/
  useTabs : Bool := false
deriving Inhabited

/-- An indentation, as prettier builds it: the steps that have been
written, and the alignments that stand after them and have not.  An
alignment is written as spaces where it stands at the end -- prettier
flushes what is pending as spaces before it writes a line -- and as a tab
where a further step follows it, which is what makes `align` differ from
`nest` under `useTabs`.  Without tabs the two are the same, and only the
number of columns matters. -/
structure Ind where
  /-- The indentation already written: a number of tabs under `useTabs`,
  and a number of columns otherwise. -/
  written : Nat := 0
  /-- The alignments that stand after it, counted as tabs. -/
  pendingTabs : Nat := 0
  /-- The same alignments, counted as columns. -/
  pendingColumns : Nat := 0
deriving Inhabited

/-- The number of columns the indentation takes. -/
def Ind.columns (st : Indentation) (i : Ind) : Nat :=
  (if st.useTabs then st.tabWidth * i.written else i.written) + i.pendingColumns

/-- The text of the indentation. -/
def Ind.text (st : Indentation) (i : Ind) : String :=
  if st.useTabs then
    String.pushn (String.pushn "" '\t' i.written) ' ' i.pendingColumns
  else String.pushn "" ' ' (i.written + i.pendingColumns)

/-- One step further in, `n` columns wide: what a `nest` adds.  It flushes
the alignments that are pending, which under `useTabs` become tabs. -/
def Ind.indent (st : Indentation) (n : Nat) (i : Ind) : Ind :=
  if st.useTabs then { written := i.written + i.pendingTabs + 1 }
  else { written := i.written + i.pendingColumns + n }

/-- One step less of indentation: what a `dedent` removes.  Prettier pops
the last entry of its indentation stack; with the flat count kept here,
one step is one tab under `useTabs` and `tabWidth` columns otherwise. -/
def Ind.dedent (st : Indentation) (i : Ind) : Ind :=
  if st.useTabs then { i with written := i.written - 1 }
  else { i with written := i.written - st.tabWidth }

/-- An alignment of `n` columns: what an `align` adds. -/
def Ind.align (n : Nat) (i : Ind) : Ind :=
  { i with pendingTabs := i.pendingTabs + 1, pendingColumns := i.pendingColumns + n }

mutual

/-- The size of a document.  A `fill` counts double, plus one for each of
its parts, so that peeling two parts off it is a decrease. -/
def size : Doc → Nat
  | .nil | .text _ | .line | .softline | .softlineRemeasure | .hardline | .breakParent => 1
  | .cat a b => size a + size b + 1
  | .nest _ d => size d + 1
  | .align _ d => size d + 1
  | .group d => size d + 1
  | .groupId _ d => size d + 1
  | .ifBreakOf _ b f => size b + size f + 1
  | .dedent d => size d + 1
  | .scopeIds d => size d + 2
  | .restoreIds _ => 1
  | .groupBreak d => size d + 1
  | .condGroup a b => size a + size b + 1
  | .fluidLine _ d => size d + 1
  | .ifBreak b f => size b + size f + 1
  | .fill ps => 2 * sumSizes ps + 2 * ps.length + 1
  | .groupIndentIfBreak _ h b tl => size h + size b + size tl + 1

/-- The total size of a list of documents. -/
def sumSizes : List Doc → Nat
  | [] => 0
  | d :: ds => size d + sumSizes ds

end

mutual

/-- Force the document flat: every line becomes a space, every soft line
nothing, and every `ifBreak` its flat contents.  Hard lines stay, as
prettier's `removeLines` leaves them. -/
def removeLines : Doc → Doc
  | .line => .text " "
  | .softline | .softlineRemeasure => .nil
  | .cat a b => .cat (removeLines a) (removeLines b)
  | .nest n d => .nest n (removeLines d)
  | .align n d => .align n (removeLines d)
  | .group d => .group (removeLines d)
  | .groupId n d => .groupId n (removeLines d)
  | .ifBreakOf _ _ f => removeLines f
  | .dedent d => .dedent (removeLines d)
  | .scopeIds d => .scopeIds (removeLines d)
  | .groupBreak d => .group (removeLines d)
  | .condGroup a b => .condGroup (removeLines a) (removeLines b)
  -- a fluid line is a line and the document it may indent: flat, it is
  -- the space the line prints as, and the document with its lines
  -- removed as well
  | .fluidLine _ d => .cat (.text " ") (removeLines d)
  | .ifBreak _ f => removeLines f
  | .fill ps => .fill (removeLinesList ps)
  | .groupIndentIfBreak n h b tl =>
      .groupIndentIfBreak n (removeLines h) (removeLines b) (removeLines tl)
  | d => d

/-- `removeLines` on each of the documents. -/
def removeLinesList : List Doc → List Doc
  | [] => []
  | d :: ds => removeLines d :: removeLinesList ds

/-- Whether the document contains a break that is forced, which makes every
enclosing group break too.  A conditional group hides the breaks inside its
alternatives. -/
def hasForcedBreak : Doc → Bool
  | .hardline | .breakParent => true
  -- text which spans lines, as the text of a template literal may, breaks
  -- the line just as a hard line does
  | .text s => s.contains '\n'
  | .groupBreak _ => true
  | .cat a b => hasForcedBreak a || hasForcedBreak b
  | .nest _ d | .align _ d => hasForcedBreak d
  | .group d => hasForcedBreak d
  | .groupId _ d => hasForcedBreak d
  | .dedent d => hasForcedBreak d
  | .scopeIds d => hasForcedBreak d
  | .ifBreak b f => hasForcedBreak b || hasForcedBreak f
  | .ifBreakOf _ b f => hasForcedBreak b || hasForcedBreak f
  | .condGroup _ _ => false
  | .fluidLine _ d => hasForcedBreak d
  | .fill ps => hasForcedBreakList ps
  | .groupIndentIfBreak _ h b _ => hasForcedBreak h || hasForcedBreak b
  | _ => false

/-- Whether one of the documents contains a forced break. -/
def hasForcedBreakList : List Doc → Bool
  | [] => false
  | d :: ds => hasForcedBreak d || hasForcedBreakList ds

end

mutual

/-- Whether the document holds a line of any kind, so that it may be
broken over more than one line. -/
def canBreak : Doc → Bool
  | .line | .softline | .softlineRemeasure | .hardline => true
  | .text s => s.contains '\n'
  | .cat a b => canBreak a || canBreak b
  | .nest _ d | .align _ d | .group d | .groupBreak d | .fluidLine _ d
  | .groupId _ d | .dedent d | .scopeIds d => canBreak d
  | .condGroup a b => canBreak a || canBreak b
  | .ifBreak b f | .ifBreakOf _ b f => canBreak b || canBreak f
  | .fill ps => canBreakList ps
  | .groupIndentIfBreak _ h b tl => canBreak h || canBreak b || canBreak tl
  | _ => false

/-- Whether one of the documents holds a line. -/
def canBreakList : List Doc → Bool
  | [] => false
  | d :: ds => canBreak d || canBreakList ds

end

mutual

/-- The first character the document prints when it is laid out flat, if
it prints one at all.  A line prints as a space, a soft line as nothing;
the flat branch of a conditional is the one taken.  It answers what the
first token of a statement is, which is what decides whether a semicolon
has to be written in front of it under `semi: false`. -/
def firstFlatChar : Doc → Option Char
  | .nil | .breakParent | .softline | .softlineRemeasure | .restoreIds _ => none
  | .text s => s.front?
  | .line | .fluidLine _ _ => some ' '
  | .hardline => some '\n'
  | .cat a b => match firstFlatChar a with
    | some c => some c
    | none => firstFlatChar b
  | .nest _ d | .align _ d | .group d | .groupBreak d | .groupId _ d
  | .dedent d | .scopeIds d => firstFlatChar d
  | .condGroup a _ => firstFlatChar a
  | .ifBreak _ f | .ifBreakOf _ _ f => firstFlatChar f
  | .fill ps => firstFlatCharList ps
  | .groupIndentIfBreak _ h b _ => match firstFlatChar h with
    | some c => some c
    | none => firstFlatChar b

/-- The first character one of the documents prints. -/
def firstFlatCharList : List Doc → Option Char
  | [] => none
  | d :: ds => match firstFlatChar d with
    | some c => some c
    | none => firstFlatCharList ds

end

/-- The size of a work list. -/
def itemsSize : List (Ind × Mode × Doc) → Nat
  | [] => 0
  | (_, _, d) :: rest => d.size + itemsSize rest

/-- The parts of a `fill`, as work list items. -/
def fillItems (i : Ind) (m : Mode) : List Doc → List (Ind × Mode × Doc)
  | [] => []
  | d :: ds => (i, m, d) :: fillItems i m ds

@[simp] theorem itemsSize_fillItems (i : Ind) (m : Mode) (ds : List Doc) :
    itemsSize (fillItems i m ds ++ rest) = sumSizes ds + itemsSize rest := by
  induction ds with
  | nil => simp [fillItems, sumSizes]
  | cons d ds ih => simp [fillItems, sumSizes, itemsSize, ih]; omega

/-- The number of columns a character takes, the way prettier counts them:
a control character, a combining character and a variation selector take
none, an East Asian wide character takes two, and everything else takes
one. -/
def charWidth (c : Char) : Nat :=
  let cp := c.val
  if cp ≤ 0x1F || (0x7F ≤ cp && cp ≤ 0x9F) then 0
  else if 0x300 ≤ cp && cp ≤ 0x36F then 0
  else if 0xFE00 ≤ cp && cp ≤ 0xFE0F then 0
  else if Unicode.isWide c then 2
  else 1

/-- The number of columns a string takes: the sum of the widths of its
characters.  Prettier gives the same width to every character; it differs
only on a sequence of several code points which together denote one
emoji, such as a flag or a family, which it gives two columns to and this
gives the sum of the columns of its parts. -/
def stringWidth (s : String) : Nat := s.foldl (fun w c => w + charWidth c) 0

/-- The part of `s` which stands before its first newline. -/
def firstLineOf (s : String) : String := (s.takeWhile (· != '\n')).copy

/-- Whether the pending documents fit in `width` columns, that is, whether
what is printed before the first line break is at most `width` wide.

A line printed flat only takes up its column once something follows it on
the line: the space it prints is dropped when the line ends there.
`pending` records such a space, which the next piece of text pays for.
`flatOnly` is prettier's `mustBeFlat`, which the parts of a `fill` are
measured with: a group that has to break does not fit at all, rather than
ending the line being measured. -/
def fitsAux (st : Indentation) (modes : List (Nat × Mode)) (flatOnly : Bool) (width : Int)
    (pending : Bool) (items : List (Ind × Mode × Doc)) : Bool :=
  if width < 0 then false else
  match items with
  | [] => true
  | (i, m, d) :: rest =>
    match d with
    | .nil | .breakParent => fitsAux st modes flatOnly width pending rest
    | .text s =>
        if s.isEmpty then fitsAux st modes flatOnly width pending rest
        else if s.contains '\n' then
          -- the line ends inside the text: only what stands before the
          -- first newline is on the line being measured
          0 ≤ width - stringWidth (firstLineOf s) - (if pending then 1 else 0)
        else fitsAux st modes flatOnly (width - stringWidth s - (if pending then 1 else 0)) false rest
    | .line => match m with
      | .flat => fitsAux st modes flatOnly width true rest
      | .broken => true
    | .softline | .softlineRemeasure => match m with
      | .flat => fitsAux st modes flatOnly width pending rest
      | .broken => true
    -- a forced newline ends the line in either mode
    | .hardline => true
    | .cat a b => fitsAux st modes flatOnly width pending ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => fitsAux st modes flatOnly width pending ((i.indent st n, m, d) :: rest)
    | .align n d => fitsAux st modes flatOnly width pending ((i.align n, m, d) :: rest)
    | .group d | .groupId _ d =>
        if flatOnly && hasForcedBreak d then false
        else fitsAux st modes flatOnly width pending ((i, if hasForcedBreak d then .broken else m, d) :: rest)
    | .dedent d => fitsAux st modes flatOnly width pending ((i.dedent st, m, d) :: rest)
    | .scopeIds d =>
        fitsAux st modes flatOnly width pending ((i, m, d) :: (i, m, .restoreIds modes) :: rest)
    | .restoreIds ms => fitsAux st ms flatOnly width pending rest
    | .ifBreakOf id b f =>
        match modes.find? (fun p => p.1 == id) with
        | some (_, .broken) => fitsAux st modes flatOnly width pending ((i, m, b) :: rest)
        | _ => fitsAux st modes flatOnly width pending ((i, m, f) :: rest)
    | .groupBreak d =>
        if flatOnly then false else fitsAux st modes flatOnly width pending ((i, .broken, d) :: rest)
    | .condGroup a b => match m with
      | .flat => fitsAux st modes flatOnly width pending ((i, .flat, a) :: rest)
      | .broken => fitsAux st modes flatOnly width pending ((i, .broken, b) :: rest)
    | .fluidLine _ d => match m with
      | .flat => fitsAux st modes flatOnly width true ((i, .flat, d) :: rest)
      | .broken => true
    | .ifBreak b f => match m with
      | .flat => fitsAux st modes flatOnly width pending ((i, m, f) :: rest)
      | .broken => fitsAux st modes flatOnly width pending ((i, m, b) :: rest)
    | .fill ps => fitsAux st modes flatOnly width pending (fillItems i m ps ++ rest)
    | .groupIndentIfBreak _ h b tl =>
        if hasForcedBreak h then
          if flatOnly then false
          else
            fitsAux st modes flatOnly width pending
              ((i, .broken, h) :: (i, m, b) :: (i, .broken, tl) :: rest)
        else
          fitsAux st modes flatOnly width pending ((i, m, h) :: (i, m, b) :: rest)
termination_by itemsSize items
decreasing_by
  all_goals (simp only [itemsSize, size, itemsSize_fillItems]; omega)

/-- Whether the pending documents fit in `width` columns, given the modes
of the groups that have already been laid out. -/
def fits (st : Indentation) (modes : List (Nat × Mode)) (width : Int)
    (items : List (Ind × Mode × Doc)) : Bool :=
  fitsAux st modes false width false items

/-- Whether the pending documents fit in `width` columns, laid out flat
throughout: a group that has to break makes them not fit.  It is how
prettier measures the parts of a `fill`. -/
def fitsFlat (st : Indentation) (modes : List (Nat × Mode)) (width : Int)
    (items : List (Ind × Mode × Doc)) : Bool :=
  fitsAux st modes true width false items

/-- The column reached after emitting `s` starting at column `col`. -/
private def columnAfter (col : Nat) (s : String) : Nat :=
  s.foldl (fun c ch => if ch == '\n' then 0 else c + charWidth ch) col

/-- Whether the character is one a line break trims before it. -/
private def isTrimmable (c : Char) : Bool := c == ' ' || c == '\t'

/-- The byte index just past the last character of `s` which is not a
space or a tab; `fuel` bounds the scan, the number of bytes being enough
since every step moves back at least one. -/
private def trimEndPos (s : String) : Nat → String.Pos.Raw → String.Pos.Raw
  | 0, p => p
  | fuel + 1, p =>
      if p.byteIdx == 0 then p
      else
        let q := String.Pos.Raw.prev s p
        if isTrimmable (String.Pos.Raw.get s q) then trimEndPos s fuel q else p

/-- Drop the spaces and tabs at the end of `s`; a line break trims the
whitespace before it, as prettier's layout engine does.  The scan is
backwards from the end, so a string with nothing to trim — the usual case
— is returned as it stands, rather than copied. -/
private def trimEndString (s : String) : String :=
  let size := s.utf8ByteSize
  let stop := trimEndPos s size ⟨size⟩
  if stop.byteIdx == size then s else String.Pos.Raw.extract s ⟨0⟩ stop

/-- The output written so far, as the chunks of it in reverse order: a
chunk is appended in constant time, and the trailing whitespace a line
break drops is held by the last chunks alone, so trimming does not touch
the output as a whole.  Appending to one string instead would copy it
whenever it is trimmed, which makes laying out a large document take time
quadratic in its size. -/
private abbrev Out := List String

/-- Append a chunk to the output. -/
@[inline] private def Out.push (out : Out) (s : String) : Out :=
  if s.isEmpty then out else s :: out

/-- Drop the spaces and tabs at the end of the output. -/
private def Out.trimEnd : Out → Out
  | [] => []
  | c :: cs =>
      let t := trimEndString c
      if t.isEmpty then Out.trimEnd cs else t :: cs

/-- The output, as one string. -/
private def Out.toString (out : Out) : String :=
  String.join out.reverse

private def newlineWith (st : Indentation) (i : Ind) : String :=
  "\n" ++ i.text st

/-- Lay out a work list.  `remeasure` records that a forced newline was
printed inside a flat group, so that the next group has to be measured
again. -/
private def go (st : Indentation) (width : Nat) (modes : List (Nat × Mode)) (out : Out)
    (col : Nat) (remeasure : Bool) : List (Ind × Mode × Doc) → Out
  | [] => out
  | (i, m, d) :: rest =>
    match d with
    | .nil | .breakParent => go st width modes out col remeasure rest
    -- text which spans lines ends the line as a hard line does, which
    -- makes the group that follows it have to be measured again
    | .text s =>
        go st width modes (out.push s) (columnAfter col s)
          (remeasure || (m == .flat && s.contains '\n')) rest
    | .line => match m with
      | .flat => go st width modes (out.push " ") (col + 1) remeasure rest
      | .broken => go st width modes (out.trimEnd.push (newlineWith st i)) (i.columns st) remeasure rest
    | .softline => match m with
      | .flat => go st width modes out col remeasure rest
      | .broken => go st width modes (out.trimEnd.push (newlineWith st i)) (i.columns st) remeasure rest
    -- the line break it writes is one a parser reads as whitespace, which
    -- prettier lays out as a hard line: the group that follows it has to
    -- be measured again, as it would be after a hard line
    | .softlineRemeasure => match m with
      | .flat => go st width modes out col remeasure rest
      | .broken => go st width modes (out.trimEnd.push (newlineWith st i)) (i.columns st) true rest
    | .hardline =>
        go st width modes (out.trimEnd.push (newlineWith st i)) (i.columns st) (m == .flat || remeasure) rest
    | .cat a b => go st width modes out col remeasure ((i, m, a) :: (i, m, b) :: rest)
    | .nest n d => go st width modes out col remeasure ((i.indent st n, m, d) :: rest)
    | .align n d => go st width modes out col remeasure ((i.align n, m, d) :: rest)
    | .group d =>
        if m == .flat && !remeasure then
          go st width modes out col remeasure
            ((i, if hasForcedBreak d then .broken else .flat, d) :: rest)
        else
          let flat := !hasForcedBreak d && fits st modes ((width : Int) - col) ((i, .flat, d) :: rest)
          go st width modes out col false ((i, if flat then .flat else .broken, d) :: rest)
    | .groupBreak d => go st width modes out col remeasure ((i, .broken, d) :: rest)
    -- a group whose mode is recorded, so that an `ifBreakOf` that names it
    -- can ask for it later
    | .groupId id d =>
        if m == .flat && !remeasure then
          let gm : Mode := if hasForcedBreak d then .broken else .flat
          go st width ((id, gm) :: modes) out col remeasure ((i, gm, d) :: rest)
        else
          let flat := !hasForcedBreak d && fits st modes ((width : Int) - col) ((i, .flat, d) :: rest)
          let gm : Mode := if flat then .flat else .broken
          go st width ((id, gm) :: modes) out col false ((i, gm, d) :: rest)
    | .dedent d => go st width modes out col remeasure ((i.dedent st, m, d) :: rest)
    | .scopeIds d =>
        go st width modes out col remeasure ((i, m, d) :: (i, m, .restoreIds modes) :: rest)
    | .restoreIds ms => go st width ms out col remeasure rest
    | .ifBreakOf id b f =>
        match modes.find? (fun p => p.1 == id) with
        | some (_, .broken) => go st width modes out col remeasure ((i, m, b) :: rest)
        | _ => go st width modes out col remeasure ((i, m, f) :: rest)
    | .condGroup a b =>
        if m == .flat && !remeasure then
          go st width modes out col remeasure ((i, .flat, a) :: rest)
        else if fits st modes ((width : Int) - col) ((i, .flat, a) :: rest) then
          go st width modes out col false ((i, .flat, a) :: rest)
        else
          go st width modes out col false ((i, .broken, b) :: rest)
    | .fluidLine n d =>
        if (m == .flat && !remeasure)
            || fits st modes ((width : Int) - col) ((i, .flat, .line) :: (i, m, d) :: rest) then
          go st width modes (out.push " ") (col + 1) remeasure ((i, m, d) :: rest)
        else
          let j := i.indent st n
          go st width modes (out.trimEnd.push (newlineWith st j)) (j.columns st) remeasure ((j, m, d) :: rest)
    | .ifBreak b f => match m with
      | .flat => go st width modes out col remeasure ((i, m, f) :: rest)
      | .broken => go st width modes out col remeasure ((i, m, b) :: rest)
    | .groupIndentIfBreak n h b tl =>
        if m == .flat && !remeasure && !hasForcedBreak h then
          go st width modes out col remeasure ((i, .flat, h) :: (i, m, b) :: rest)
        else
          let flat := !hasForcedBreak h
            && fits st modes ((width : Int) - col) ((i, .flat, h) :: (i, m, b) :: rest)
          if flat then go st width modes out col false ((i, .flat, h) :: (i, m, b) :: rest)
          else
            go st width modes out col false
              ((i, .broken, h) :: (i.indent st n, m, b) :: (i, .broken, tl) :: rest)
    -- prettier's `fill`: put as many contents on the line as fit
    | .fill ps =>
      match ps with
      | [] => go st width modes out col remeasure rest
      -- a part which holds a group that has to break cannot be laid out
      -- flat, so it does not fit however much room is left
      | [c] =>
          let flat := fitsFlat st modes ((width : Int) - col) [(i, .flat, c)]
          go st width modes out col remeasure ((i, if flat then .flat else .broken, c) :: rest)
      | [c, w] =>
          let flat := fitsFlat st modes ((width : Int) - col) [(i, .flat, c)]
          let cm : Mode := if flat then .flat else .broken
          go st width modes out col remeasure ((i, cm, c) :: (i, cm, w) :: rest)
      | c :: w :: c2 :: tl =>
          let contentFits := fitsFlat st modes ((width : Int) - col) [(i, .flat, c)]
          let pairFits :=
            fitsFlat st modes ((width : Int) - col) [(i, .flat, c), (i, .flat, w), (i, .flat, c2)]
          let cm : Mode := if contentFits then .flat else .broken
          let wm : Mode := if pairFits then .flat else .broken
          go st width modes out col remeasure
            ((i, cm, c) :: (i, wm, w) :: (i, m, .fill (c2 :: tl)) :: rest)
termination_by items => itemsSize items
decreasing_by
  all_goals (simp only [itemsSize, size, sumSizes, List.length_cons]; omega)

/-- Lay out a document, breaking groups that do not fit into `width`
columns, writing indentation in the given style and ending every line
with `eol`.  Prettier converts the line endings of its whole output, so
the conversion here is of the rendered text as a whole, the newlines
inside a template literal included. -/
def renderWith (st : Indentation) (eol : String) (width : Nat) (d : Doc) : String :=
  let s := (go st width [] [] 0 false [({}, .broken, d)]).toString
  if eol == "\n" then s else s.replace "\n" eol

/-- Lay out a document, breaking groups that do not fit into `width`
columns, with prettier's default indentation of two spaces. -/
def render (width : Nat) (d : Doc) : String := renderWith {} "\n" width d

end Doc

end Language.JavaScript.Doc
