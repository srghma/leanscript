import LanguageJavascriptCommon.JSXLayout
import LanguageJavascriptCommon.PrinterCommon
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.ASTOps

/-!
# The JSX children of the JavaScript tree

The step from the JSX nodes of `MiniAST` to the documents
`JSXLayout` lays out: which children are text, which are elements written
`<x />`, and the parts the children of an element are read as.  The layout
itself — the `fill`, the runs of whitespace written `{" "}` and the tags —
is in `Language.JavaScript.JSXLayout`, which the TypeScript printer shares;
the traversal of an expression is in `MiniAST.Printer`.
-/

namespace Language.JavaScript.MiniAST.Printer

open Language.JavaScript.Doc
open Language.JavaScript.JSXLayout

variable [o : Options]

/-! ## The children of an element -/

/-- Whether the child is an element written `<x />`. -/
def jsxChildIsSelfClosing : MiniJSXChild → Bool
  | .node (.element _ _ none) => true
  | _ => false

/-- Whether the child is a nested element or fragment. -/
def jsxChildIsNode : MiniJSXChild → Bool
  | .node _ => true
  | _ => false

/-- Whether the child is a `{ }` substitution.  A `{" "}` is not one: a
parser reads it as the whitespace it stands for, and neither is a
`{...children}`, which a parser reads as a spread child of its own. -/
def jsxChildIsExpr : MiniJSXChild → Bool
  | .expr (.string " ") => false
  | .expr (.spread _) => false
  | .expr _ | .emptyExpr => true
  | _ => false

/-- Whether the child is text that is not empty; a `{" "}` is text. -/
def jsxChildIsText : MiniJSXChild → Bool
  | .text v => v != ""
  | .expr (.string " ") => true
  | _ => false

/-- The text of a child which is one, the empty string otherwise. -/
def jsxChildText : MiniJSXChild → String
  | .text v => v
  | .expr (.string " ") => " "
  | _ => ""

/-- Whether the child is one no source can hold, which is left out. -/
def jsxChildIsEmpty : MiniJSXChild → Bool
  | .text v => v == ""
  | _ => false

/-- Whether the element holds more than one `{ }` substitution, which
makes prettier break it. -/
def jsxHasSeveralExprs (kids : List MiniJSXChild) : Bool :=
  (kids.filter jsxChildIsExpr).length > 1

/-- Whether the expression is a template literal, tagged or not.  An
element whose only child is one holds it between its tags as it is. -/
def jsxIsTemplateExpr : MiniExpr → Bool
  | .template .. => true
  | _ => false

/-! ## Attributes -/

/-- Whether the only attribute of the element is one whose value is a
string without a line break, which prettier never breaks the tag for. -/
def jsxOneStringAttr : List MiniJSXAttribute → Bool
  | [.attr _ (some (.string v))] => !v.contains '\n'
  | _ => false

/-- Whether one of the attribute values holds a line break, which always
breaks the tag. -/
def jsxAttrsBreak (attrs : List MiniJSXAttribute) : Bool :=
  attrs.any fun
    | .attr _ (some (.string v)) => v.contains '\n'
    | _ => false

/-! ## Substitutions -/

/-- Whether the expression written in a `{ }` keeps the braces on its own
lines, rather than standing on a line of its own between them.
`inElement` says that the `{ }` is a child of an element rather than the
value of an attribute: a conditional or a binary expression written as a
child keeps the braces, and one written in an attribute does not. -/
def jsxInlinesContainer (inElement : Bool) : MiniExpr → Bool
  | .array _ | .object _ | .arrow .. | .func .. | .template .. => true
  -- a call keeps the braces on its line; a dynamic `import()`, which is
  -- not a call of the kind prettier means here, and a `new` do not
  | .call .. | .superCall _ => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call ..) => true
      | _ => false
  | .await a =>
      (match a with
        | .jsx _ => true
        | _ => jsxInlinesContainer false a)
  | .ternary .. | .binary .. => inElement
  | _ => false

/-- The `{ }` around an expression written as a child of an element or as
the value of an attribute, given the document of the expression.
`inElement` is as for `jsxInlinesContainer`. -/
def jsxContainerOf (inElement : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  if jsxInlinesContainer inElement e then .group (tx "{" ++ d ++ tx "}")
  else .group (tx "{" ++ .nest jsxIndent (.softline ++ d) ++ .softline ++ tx "}")

/-! ## The parts of the children -/

/-- One child of an element together with the document it prints as.  A
text child prints as the words this file lays out, and carries none. -/
abbrev JSXChildDoc := MiniJSXChild × Doc

/-- Merge the runs of text that stand next to one another, as a parser
reads them: two texts written one after the other are one text, and where
the words of a text fall decides the layout of the children. -/
def jsxMergeChildDocs : List JSXChildDoc → List JSXChildDoc
  | (.text a, _) :: (.text b, _) :: rest =>
      jsxMergeChildDocs ((MiniJSXChild.text (a ++ b), Doc.nil) :: rest)
  | c :: rest => c :: jsxMergeChildDocs rest
  | [] => []
termination_by kids => kids.length

/-- The parts the children of an element are laid out as, from the
children and the documents they print as; `rev` holds the parts already
built, in reverse.  The runs of text that stand next to one another have
to have been merged first. -/
def jsxChildPartsOf (rev : List JSXPart) : List JSXChildDoc → List JSXPart
  | [] => rev.reverse
  | (c, d) :: rest =>
    let nextSelfClosing := match rest with | (n, _) :: _ => jsxChildIsSelfClosing n | [] => false
    -- the separator that follows a child which is not text: a line of its
    -- own, unless text follows it on the same line
    let afterChild (selfClosing : Bool) : JSXPart :=
      match rest with
      | (n, _) :: _ =>
        if jsxChildIsText n then
          jsxSeparatorNoWhitespace (jsxFirstWord (jsxChildText n)) selfClosing
        else .hardline
      | [] => .hardline
    -- the words of a run of text, and the runs of whitespace around them
    let textParts (v : String) : List JSXPart :=
      match jsxWords v with
      -- whitespace on its own is a run of whitespace and nothing else
      | [] => jsxPushSep rev .jsxWhitespace
      | w :: ws =>
        let rev := if jsxStartsWithSpace v then jsxPushSep rev .jsxWhitespace else rev
        let rev := jsxPushWords (jsxPushWord rev (tx (encodeJSXText w))) ws
        let lastWord := (w :: ws).getLast (by simp)
        if jsxEndsWithSpace v then jsxPushSep rev .jsxWhitespace
        else jsxPushSep rev (jsxSeparatorNoWhitespace lastWord nextSelfClosing)
    match c with
    | .text "" => jsxChildPartsOf rev rest
    | .text v => jsxChildPartsOf (textParts v) rest
    -- `{" "}` is the whitespace it stands for
    | .expr (.string " ") => jsxChildPartsOf (textParts " ") rest
    | .expr _ | .emptyExpr =>
        jsxChildPartsOf (jsxPushSep (jsxPushWord rev d) (afterChild nextSelfClosing)) rest
    | .node _ =>
        jsxChildPartsOf (jsxPushSep (jsxPushWord rev d)
          (afterChild (jsxChildIsSelfClosing c || nextSelfClosing))) rest

/-- The document of an element or a fragment, from its tags, its children
and the parts they were laid out as.  `lone` is the document of a lone
template literal child, which the element holds between its tags as it is;
`multipleAttrs` says that the element has more than one attribute, which
always breaks it. -/
def jsxAssemble (opening closing : Doc) (multipleAttrs : Bool) (kids : List MiniJSXChild)
    (rawParts : List JSXPart) (lone : Option Doc) : Doc :=
  match lone with
  | some d => opening ++ d ++ closing
  | none =>
    let containsText := kids.any jsxChildIsText
    let parts := jsxTrimStart (jsxTrimEnd (jsxCleanup containsText rawParts))
    let forced := Doc.hasForcedBreak opening || kids.any jsxChildIsNode || multipleAttrs
      || jsxHasSeveralExprs kids
    jsxElementDocOf opening closing containsText forced parts

end Language.JavaScript.MiniAST.Printer
