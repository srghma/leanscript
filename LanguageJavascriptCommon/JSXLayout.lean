import LanguageJavascriptCommon.Doc
import LanguageJavascriptCommon.StringLit
import LanguageJavascriptCommon.Options

/-!
# The layout of JSX

The parts of the JSX printer that work on documents alone: the way
prettier turns the children of an element into the parts of a `fill`, the
whitespace it has to write as `{" "}`, and the way it assembles an element
from its tags and its children.

Nothing here mentions a syntax tree, so the JavaScript printer
(`MiniAST.JSX` and `MiniAST.Printer`) and the TypeScript one
(`MiniTsAST.JSX` and `MiniTsAST.Printer`) share it; the traversal of the
tree itself, which is what differs between them, is in those modules.

The algorithm is prettier's `printJsxElement`: the children are laid out
as a `fill`, the runs of whitespace between them that a line break would
swallow are written as `{" "}`, and an element that holds a tag, more than
one attribute or more than one substitution is always broken.
-/

namespace Language.JavaScript.JSXLayout

open Language.JavaScript.Doc
open Language.JavaScript.MiniAST (encodeJSXText)

variable [o : Options]

/-- The number of columns of one indentation step: prettier's
`tabWidth`. -/
def jsxIndent : Nat := Options.tabWidth

/-- The document of a piece of text. -/
def tx (s : String) : Doc := .text s

/-! ## The parts of the children of an element -/

/-- One entry of the list prettier builds out of the children of an
element.  The entries alternate contents and separators; the separators
are the four kinds prettier uses, and a content is a document, `empty`
saying that it is the empty one it starts every gap with. -/
inductive JSXPart where
  /-- A content: a word of text, or a printed child. -/
  | content (empty : Bool) (d : Doc)
  /-- The separator between two words of the same run of text. -/
  | line
  /-- The separator that prints as nothing when the line does not break. -/
  | softline
  /-- The separator that always breaks. -/
  | hardline
  /-- A run of whitespace which a line break would swallow, and which is
  written `{" "}` when the line does break. -/
  | jsxWhitespace
deriving Inhabited

namespace JSXPart

/-- Whether the part is the empty content. -/
def isEmptyContent : JSXPart → Bool
  | .content e _ => e
  | _ => false

/-- Whether the part is a line of one of the three kinds, or the empty
content: the parts prettier trims from the ends of the list. -/
def isTrimmable : JSXPart → Bool
  | .content e _ => e
  | .line | .softline | .hardline => true
  | .jsxWhitespace => false

/-- Whether the part is a hard line. -/
def isHardline : JSXPart → Bool
  | .hardline => true
  | _ => false

/-- Whether the part is a soft line. -/
def isSoftline : JSXPart → Bool
  | .softline => true
  | _ => false

/-- Whether the part is a run of whitespace written `{" "}`. -/
def isJsxWhitespace : JSXPart → Bool
  | .jsxWhitespace => true
  | _ => false

end JSXPart

/-- The `{" "}` a run of whitespace is written as where the line breaks. -/
def rawJsxWhitespace : Doc := tx (if Options.singleQuote then "{' '}" else "{\" \"}")

/-- The document of a run of whitespace: a space while the line holds, and
`{" "}` followed by a line break when it does not. -/
def jsxWhitespaceDoc : Doc := .ifBreak (rawJsxWhitespace ++ .softline) (tx " ")

/-- The document a part prints as. -/
def JSXPart.doc : JSXPart → Doc
  | .content _ d => d
  | .line => .line
  -- a line break written where no whitespace stands between two children
  -- is one a parser reads as whitespace, which prettier lays out as a
  -- hard line when it reads the text back
  | .softline => .softlineRemeasure
  | .hardline => .hardline
  | .jsxWhitespace => jsxWhitespaceDoc

/-! ## Cleaning the list up -/

/-- Drop the pairs of parts that would print as two spaces, or as a line
break next to a run of whitespace, the way prettier does: it walks the
list from its end, and at every position either drops the part and the one
after it, or the two parts after it. -/
def jsxCleanup (containsText : Bool) : List JSXPart → List JSXPart
  | [] => []
  | x :: xs =>
    match jsxCleanup containsText xs with
    | [] => [x]
    | [y0] => if x.isEmptyContent && y0.isEmptyContent then [] else [x, y0]
    | y0 :: y1 :: rest =>
      let pairOfEmpties := x.isEmptyContent && y0.isEmptyContent
      let pairOfHardlines := x.isHardline && y0.isEmptyContent && y1.isHardline
      let lineThenWhitespace :=
        (x.isHardline || x.isSoftline) && y0.isEmptyContent && y1.isJsxWhitespace
      let whitespaceThenLine :=
        x.isJsxWhitespace && y0.isEmptyContent && (y1.isHardline || y1.isSoftline)
      let doubleWhitespace := x.isJsxWhitespace && y0.isEmptyContent && y1.isJsxWhitespace
      let mixedLines :=
        (x.isSoftline && y0.isEmptyContent && y1.isHardline)
          || (x.isHardline && y0.isEmptyContent && y1.isSoftline)
      if (pairOfHardlines && containsText) || pairOfEmpties || lineThenWhitespace
          || doubleWhitespace || mixedLines then
        y1 :: rest
      else if whitespaceThenLine then x :: rest
      else x :: y0 :: y1 :: rest

/-- Drop the lines and the empty contents at the end of the list. -/
def jsxTrimEnd (parts : List JSXPart) : List JSXPart :=
  (parts.reverse.dropWhile JSXPart.isTrimmable).reverse

/-- Drop the leading pairs of lines and empty contents. -/
def jsxTrimStart : List JSXPart → List JSXPart
  | a :: b :: rest =>
      if a.isTrimmable && b.isTrimmable then jsxTrimStart rest else a :: b :: rest
  | ps => ps

/-! ## The parts of the `fill` -/

/-- Build the parts of the `fill` the children are laid out as, and say
whether one of them forces the element to break.  It is prettier's last
pass over the list: a run of whitespace that stands alone, or at one of
the ends of the list, or right after a line break, is written `{" "}`
rather than left to the line to decide. -/
private def jsxGroupsAux (total : Nat) : Nat → Option JSXPart → Option JSXPart →
    List Doc → Bool → List JSXPart → List Doc × Bool
  | _, _, _, revC, forced, [] => (revC.reverse, forced)
  | h, prev1, prev2, revC, forced, v :: rest =>
    let merge (d : Doc) : List Doc :=
      match revC with
      | last :: cs => (last ++ d) :: cs
      | [] => [d]
    let pushSep (d : Doc) : List Doc := .nil :: d :: revC
    let handled : Option (List Doc) :=
      if v.isJsxWhitespace then
        if h == 1 && (prev1.map JSXPart.isEmptyContent).getD false then
          if total == 2 then some (merge rawJsxWhitespace)
          else some (pushSep (rawJsxWhitespace ++ .hardline))
        else if h + 1 == total then some (merge rawJsxWhitespace)
        else if (prev1.map JSXPart.isEmptyContent).getD false
            && (prev2.map JSXPart.isHardline).getD false then
          some (merge rawJsxWhitespace)
        else none
      else none
    match handled with
    | some revC' => jsxGroupsAux total (h + 1) (some v) prev1 revC' forced rest
    | none =>
      let d := v.doc
      let revC' := if h % 2 == 0 then merge d else pushSep d
      jsxGroupsAux total (h + 1) (some v) prev1 revC' (forced || Doc.hasForcedBreak d) rest

/-- The parts of the `fill` the children of an element are laid out as,
and whether one of them forces the element to break. -/
def jsxGroups (parts : List JSXPart) : List Doc × Bool :=
  jsxGroupsAux parts.length 0 none none [.nil] false parts

/-! ## Assembling an element -/

/-- The document of an element, from the documents of its tags and the
parts of its children.  `containsText` says that one of the children is
text, which is laid out as a `fill`; `forcedBreak` that the element is one
prettier always breaks. -/
def jsxElementDocOf (opening closing : Doc) (containsText forcedBreak : Bool)
    (parts : List JSXPart) : Doc :=
  let (groups, forcedInParts) := jsxGroups parts
  let inner := if containsText then .fill groups else Doc.groupBreak (Doc.concat groups)
  let multiline :=
    Doc.group (opening ++ .nest jsxIndent (.hardline ++ inner) ++ .hardline ++ closing)
  if forcedBreak || forcedInParts then multiline
  else
    .condGroup (.group (opening ++ Doc.concat (parts.map JSXPart.doc) ++ closing)) multiline

/-- The parentheses prettier writes around a JSX element that stands where
a line break would otherwise leave it beside other text: they are written
only when the element does not fit on the line it starts on.
`alwaysBreaks` says that the element is one prettier always writes on
lines of its own, and `noParens` that the element already stands between
parentheses written for it, so that only the line breaks are wanted. -/
def jsxWrapInParens (alwaysBreaks noParens : Bool) (d : Doc) : Doc :=
  let op : Doc := if noParens then .nil else .ifBreak (tx "(") .nil
  let cl : Doc := if noParens then .nil else .ifBreak (tx ")") .nil
  let body := op ++ .nest jsxIndent (.softline ++ d) ++ .softline ++ cl
  if alwaysBreaks then .groupBreak body else .group body

/-! ## Tags -/

/-- The opening tag of an element, from the document of the type arguments
it is read at, if the language has them, and the documents of its
attributes.  `selfClosing` says that the element has no children,
`oneStringAttr` that its only attribute is one whose value is a string
without a line break, which prettier never breaks the tag for, and `breaks`
that one of the attribute values holds a line break, which always breaks
it.  The type arguments of a component, `<Comp<string> />`, stand between
the name and the attributes, and break on their own once they no longer
fit.

Under `bracketSameLine` the `>` of a broken tag stands at the end of the
last attribute line rather than on a line of its own; the `/>` of a self
closing tag keeps its own line either way.  Under
`singleAttributePerLine` a tag of more than one attribute is always
broken. -/
def jsxOpeningDocOf (name : String) (typeArgs : Option Doc)
    (selfClosing oneStringAttr breaks : Bool) (attrs : List Doc) : Doc :=
  let nameDoc : Doc := match typeArgs with
    | none => tx ("<" ++ name)
    | some d => tx ("<" ++ name) ++ d
  if selfClosing && attrs.isEmpty then
    match typeArgs with
    | none => tx ("<" ++ name ++ " />")
    | some _ => nameDoc ++ tx " />"
  else if oneStringAttr then
    let head : Doc := match typeArgs with
      | none => tx ("<" ++ name ++ " ")
      | some _ => nameDoc ++ tx " "
    .group (head ++ Doc.concat attrs ++ tx (if selfClosing then " />" else ">"))
  else
    let attrsDoc := Doc.concat (attrs.map (fun a => Doc.line ++ a))
    let tail : Doc :=
      if selfClosing then .line ++ tx "/>"
      else if attrs.isEmpty || Options.bracketSameLine then tx ">"
      else .softline ++ tx ">"
    let body := nameDoc ++ .nest jsxIndent attrsDoc ++ tail
    if breaks || (Options.singleAttributePerLine && 1 < attrs.length) then .groupBreak body
    else .group body

/-! ## Text -/

/-- Whether the character is one JSX reads as whitespace. -/
def isJSXSpace (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t' || c == '\r'

/-- The words of a text: its runs of characters that are not whitespace.
The string is read as it stands, a character at a time, rather than turned
into a list of characters first. -/
def jsxWords (s : String) : List String :=
  -- `rev` holds the words already read, the last one first, and `word` the
  -- one being read
  let (rev, word) :=
    s.foldl (fun (st : List String × String) c =>
      if isJSXSpace c then (if st.2.isEmpty then st else (st.2 :: st.1, ""))
      else (st.1, st.2.push c)) ([], "")
  (if word.isEmpty then rev else word :: rev).reverse

/-- The first word of a text, or the empty string when it holds none. -/
def jsxFirstWord (s : String) : String := (jsxWords s).head?.getD ""

/-- Whether the text begins with whitespace. -/
def jsxStartsWithSpace (s : String) : Bool := !s.isEmpty && isJSXSpace s.front

/-- Whether the text ends with whitespace. -/
def jsxEndsWithSpace (s : String) : Bool := !s.isEmpty && isJSXSpace s.back

/-! ## Building the list of parts -/

/-- Add a content to the part being built: the parts hold the list in
reverse, so that the content being built is its head. -/
def jsxPushWord (rev : List JSXPart) (d : Doc) : List JSXPart :=
  match rev with
  | .content _ d0 :: cs => .content false (d0 ++ d) :: cs
  | cs => .content false d :: cs

/-- Add a separator, and the empty content that follows it.  The list
alternates contents and separators and begins with a content, so a
separator written before any content at all is given the empty content it
stands after. -/
def jsxPushSep (rev : List JSXPart) (s : JSXPart) : List JSXPart :=
  match rev with
  | [] => [.content true .nil, s, .content true .nil]
  | _ => .content true .nil :: s :: rev

/-- Add the words that follow the first one of a run of text, each on the
other side of a line from the one before it. -/
def jsxPushWords (rev : List JSXPart) : List String → List JSXPart
  | [] => rev
  | w :: ws => jsxPushWords (jsxPushWord (jsxPushSep rev .line) (tx (encodeJSXText w))) ws

/-- The separator prettier writes where no whitespace stands between two
children.  `selfClosing` says that one of the two is an element written
`<x />`, next to which a word of more than one character keeps its own
line. -/
def jsxSeparatorNoWhitespace (word : String) (selfClosing : Bool) : JSXPart :=
  if selfClosing then (if word.length == 1 then .softline else .hardline) else .softline

end Language.JavaScript.JSXLayout
