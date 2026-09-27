/-
The parts of the printers that do not look at a syntax tree.

The JavaScript printer (`MiniAST.Printer`) and the TypeScript one
(`MiniTsAST.Printer`) walk two different trees, but a good deal of what
they do once they have reached a node is the same: the text and the
precedence of an operator, the layout of an argument list, of a block and
of a declaration, the shape of a number literal, and the widths and the
quotes prettier's options ask for.  Those functions are written once here,
in the namespace both printers open.

Like the printers, every function is read as a `Language.JavaScript.Options`,
prettier's options record, which it takes as an instance argument.
-/
import LanguageJavascriptCommon.Doc
import LanguageJavascriptCommon.StringLit
import LanguageJavascriptCommon.Options
import LanguageJavascriptCommon.Unicode

namespace Language.JavaScript.PrinterCommon

open Language.JavaScript.Doc
open Language.JavaScript.MiniAST
  (encodeStringLiteralQuoted encodeJSXAttrStringQuoted)

variable [o : Options]

/-! ## Widths and small documents -/

/-- Prettier's default line width, which the entry points that are given
no options lay out for. -/
def defaultWidth : Nat := 80

/-- The line width the layout aims at: prettier's `printWidth`. -/
def printWidth : Nat := Options.printWidth

/-- The number of columns of one indentation step: prettier's
`tabWidth`. -/
def indentWidth : Nat := Options.tabWidth

/-- Prettier's `tabWidth`, used by some of its heuristics. -/
def tabWidth : Nat := Options.tabWidth

/-- The document of a piece of text. -/
def t (s : String) : Doc := .text s

/-- Parenthesise a document. -/
def parens (d : Doc) : Doc := t "(" ++ d ++ t ")"

/-- Parenthesise `d` when `cond` holds. -/
def parenIf (cond : Bool) (d : Doc) : Doc := if cond then parens d else d

/-- The terminator of a statement: a semicolon, or nothing under
`semi: false`. -/
def semiDoc : Doc := t Options.semiText

/-- A string literal, quoted the way `singleQuote` asks for. -/
def strLit (s : String) : String := encodeStringLiteralQuoted Options.preferredQuote s

/-- The value of a JSX attribute, quoted the way `jsxSingleQuote` asks
for. -/
def jsxAttrLit (s : String) : String := encodeJSXAttrStringQuoted Options.preferredJSXQuote s

/-! ## Operators -/

/-- The text an operator is written with. -/
def binOpText : BinOp → String
  | .and => "&&" | .or => "||" | .coalesce => "??"
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .neq => "!=" | .strictEq => "===" | .strictNeq => "!=="
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .lsh => "<<" | .rsh => ">>" | .ursh => ">>>"
  | .plus => "+" | .minus => "-" | .times => "*" | .divide => "/" | .mod => "%"
  | .inOp => "in" | .instanceOf => "instanceof"

/-- Binary operator precedence, as prettier orders them; higher binds
tighter. -/
def binOpPrec : BinOp → Nat
  | .coalesce => 1
  | .or => 2
  | .and => 3
  | .bitOr => 4
  | .bitXor => 5
  | .bitAnd => 6
  | .eq | .neq | .strictEq | .strictNeq => 7
  | .lt | .le | .gt | .ge | .inOp | .instanceOf => 8
  | .lsh | .rsh | .ursh => 9
  | .plus | .minus => 10
  | .times | .divide | .mod => 11

/-- `&&`, `||` and `??`, the operators of a logical expression. -/
def isLogicalOp : BinOp → Bool
  | .and | .or | .coalesce => true
  | _ => false

def isEqualityOp : BinOp → Bool
  | .eq | .neq | .strictEq | .strictNeq => true
  | _ => false

def isMultiplicativeOp : BinOp → Bool
  | .times | .divide | .mod => true
  | _ => false

def isBitshiftOp : BinOp → Bool
  | .lsh | .rsh | .ursh => true
  | _ => false

def isBitwiseOp : BinOp → Bool
  | .bitAnd | .bitOr | .bitXor => true
  | o => isBitshiftOp o

/-- Whether a child operator of the same precedence may be flattened into
the operator chain of its parent. -/
def shouldFlatten (parentOp childOp : BinOp) : Bool :=
  binOpPrec parentOp == binOpPrec childOp
    && !(isEqualityOp parentOp && isEqualityOp childOp)
    && !((childOp == .mod && isMultiplicativeOp parentOp)
          || (parentOp == .mod && isMultiplicativeOp childOp))
    && !(childOp != parentOp && isMultiplicativeOp childOp && isMultiplicativeOp parentOp)
    && !(isBitshiftOp parentOp && isBitshiftOp childOp)

def unaryOpText : UnaryOp → String
  | .not => "!" | .tilde => "~" | .plus => "+" | .minus => "-"
  | .typeof => "typeof " | .void => "void " | .delete => "delete "
  | .preIncr => "++" | .preDecr => "--"

def postfixOpText : PostfixOp → String
  | .incr => "++" | .decr => "--"

def assignOpText : AssignOp → String
  | .assign => "="
  | .logicalAnd => "&&=" | .logicalOr => "||=" | .coalesce => "??="
  | .plus => "+=" | .minus => "-=" | .times => "*=" | .divide => "/=" | .mod => "%="
  | .lsh => "<<=" | .rsh => ">>=" | .ursh => ">>>="
  | .bitAnd => "&=" | .bitXor => "^=" | .bitOr => "|="

def varKindText : VarKind → String
  | .var => "var" | .let_ => "let" | .const => "const"

/-- Whether a binary operand needs parentheses inside a binary parent. -/
def binaryOperandParens (parentOp childOp : BinOp) (isLeft : Bool) : Bool :=
  if isLogicalOp parentOp && isLogicalOp childOp then parentOp != childOp
  else
    let pp := binOpPrec parentOp
    let cp := binOpPrec childOp
    if pp > cp then true
    else if pp == cp && !isLeft then true
    else if pp == cp && !shouldFlatten parentOp childOp then true
    else if pp < cp && childOp == .mod && (parentOp == .plus || parentOp == .minus) then true
    else if isBitwiseOp parentOp then true
    else false

/-! ## Where an expression stands -/

/-- Where the leftmost token of an expression stands, which says which
expressions the place forbids there. -/
inductive StartCtx where
  /-- Not a place where the leftmost token matters. -/
  | none
  /-- The start of an expression statement, which may not be read as a
  block, a function declaration or a class declaration. -/
  | statement
  /-- The start of the body of an arrow function, which may not be read as
  a block. -/
  | arrowBody
  /-- The start of the initialiser of a `for (;;)`, where the identifier
  `let` would be read as the keyword when a `[` follows it. -/
  | forInit
  /-- The start of the binder of a `for (... in ...)` or of a
  `for (... of ...)`, which may not be the identifier `let` at all. -/
  | forInHead
  /-- The leftmost token of the operand of an `await`.  Nothing may not be
  written there, but prettier does not group the parentheses an `await`
  standing here takes, so that they break with the line that holds the
  `await` which the operand belongs to. -/
  | awaitArgument
  /-- An argument of a call which is itself written directly in a `{ }` of
  a JSX element.  Prettier always writes a JSX element that is the body of
  an arrow function standing here on lines of its own. -/
  | jsxCallArg
  /-- The start of the body of an arrow function which is the argument of
  such a call. -/
  | jsxArrowBody
deriving BEq, Inhabited

/-- The kind of a node, as prettier distinguishes `BinaryExpression` from
`LogicalExpression`. -/
inductive BinKind where
  | logical | arith | other
deriving BEq, Inhabited

/-! ## Names and numbers -/

/-- A name prettier treats as a factory: it starts with a capital letter,
or consists of `_` and `$` only. -/
def isFactoryName (s : String) : Bool :=
  !s.isEmpty && (s.front.isUpper || s.all (fun ch => ch == '_' || ch == '$'))

/-- The length prettier calls short for the lone argument of a call: a
quarter of the line width. -/
def shortArgWidth : Nat := Options.printWidth / 4

/-- Whether a quoted property name can be written without its quotes: it
is one exactly when it is an ECMAScript 5 `IdentifierName`, whose
characters are those of the Unicode properties `ID_Start` and
`ID_Continue`. -/
def isIdentifierName (s : String) : Bool := Unicode.isIdentifierName s

/-- The literal a string of the shape `123` or `2.5` denotes; `none` for a
string of any other shape. -/
def simpleNumberOf (s : String) : Option JSNumber :=
  match s.splitOn "." with
  | [a] =>
      if a.length > 0 && a.all Char.isDigit then a.toNat?.map (fun m => .decimal m 0)
      else none
  | [a, b] =>
      if a.length > 0 && b.length > 0 && a.all Char.isDigit && b.all Char.isDigit then
        (a ++ b).toNat?.map (fun m => .decimal m (-(Int.ofNat b.length)))
      else none
  | _ => none

/-- Whether the string is a plain decimal number, as `123` or `2.5`, which
is moreover written the way JavaScript writes the number it denotes.  A
property name may lose its quotes only then: the name `01` is not the name
`1`, and the number `01` denotes is written `1`.  A number of more than
fifteen digits is left alone, since the double it rounds to may well be
written differently. -/
def isSimpleNumberString (s : String) : Bool :=
  match simpleNumberOf s with
  | none => false
  | some n =>
      n.render == s &&
        (match n.normalize with
          | .decimal m _ => (JSNumber.digitsOf 10 m).length ≤ 15
          | _ => false)

/-- Whether a character is one a parser reads as the continuation of the
statement before it, so that a statement beginning with it takes a
semicolon of its own under `semi: false`. -/
def isASIHazardChar (c : Char) : Bool :=
  c == '(' || c == '[' || c == '`' || c == '+' || c == '-' || c == '/' || c == '<'

/-! ## Lists, arguments and blocks -/

/-- A bracketed, comma separated list.  `spaced` says that the list is one
whose brackets prettier's `bracketSpacing` puts a space inside, and
`comma` which of prettier's `trailingComma` settings write a comma after
its last item. -/
def sepList (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then .ifBreak (t ",") .nil else .nil
    .group (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-- A bracketed, comma separated list that is not wrapped in a group of
its own: it breaks together with the group that encloses it. -/
def sepListOpen (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then .ifBreak (t ",") .nil else .nil
    t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer

/-- A bracketed, comma separated list that is always broken. -/
def sepListBroken (opener closer : String) (spaced : Bool) (comma : CommaKind)
    (items : List Doc) : Doc :=
  if items.isEmpty then t (opener ++ closer)
  else
    let br : Doc := if spaced && Options.bracketSpacing then .line else .softline
    let trailer : Doc := if Options.hasTrailingComma comma then t "," else .nil
    .groupBreak (t opener ++ .nest indentWidth (br ++ Doc.joinWith (t "," ++ .line) items ++ trailer)
      ++ br ++ t closer)

/-- The argument list of a call, hugging a first or a final function-like
argument the way prettier does.  `docs` are the arguments as they are
printed on their own, `hugFirstDocs` and `hugDocs` the same arguments with
the first, respectively the last, one printed as the layout prints an
argument it expands in place.  `openArgs` says that the call is a link of
a long curried chain, `f(a, b)(c)`, whose argument list prettier leaves
ungrouped: it then breaks together with the line that holds the call. -/
def argumentsDocOf (comma : CommaKind) (openArgs : Bool) (hookDeps forceBroken hugFirst canHug : Bool)
    (docs hugFirstDocs hugDocs : List Doc) : Doc :=
  match docs with
  | [] => t "()"
  | _ =>
    let allBroken := sepListBroken "(" ")" false comma docs
    -- `useEffect(() => { ... }, [a, b])` keeps the layout it is written in
    if hookDeps then t "(" ++ Doc.joinWith (t ", ") docs ++ t ")"
    else if forceBroken then allBroken
    else if hugFirst then
      let firstDoc := hugFirstDocs.headD Doc.nil
      let tailDocs := hugFirstDocs.drop 1
      if tailDocs.any Doc.hasForcedBreak then allBroken
      else
        let tail := Doc.concat (tailDocs.map (fun d => t ", " ++ d))
        let hug := t "(" ++ firstDoc ++ tail ++ t ")"
        let hugBroken := t "(" ++ .groupBreak firstDoc ++ tail ++ t ")"
        if Doc.hasForcedBreak firstDoc then
          .breakParent ++ .condGroup hugBroken allBroken
        else
          .condGroup hug (.condGroup hugBroken allBroken)
    else if !canHug then
      if openArgs then sepListOpen "(" ")" false comma docs
      else
        let shouldBreak := docs.any Doc.hasForcedBreak
        if shouldBreak then allBroken else sepList "(" ")" false comma docs
    else
      let headDocs := hugDocs.dropLast
      let lastDoc := hugDocs.getLastD Doc.nil
      if headDocs.any Doc.hasForcedBreak then allBroken
      else
        let head := Doc.concat (headDocs.map (fun d => d ++ t ", "))
        let hug := t "(" ++ head ++ lastDoc ++ t ")"
        let hugBroken := t "(" ++ head ++ .groupBreak lastDoc ++ t ")"
        if Doc.hasForcedBreak lastDoc then
          .breakParent ++ .condGroup hugBroken allBroken
        else
          .condGroup hug (.condGroup hugBroken allBroken)

/-- The argument list of an ordinary call, which gets a trailing comma
when it is broken over several lines. -/
def argumentsDoc : Bool → Bool → Bool → Bool → List Doc → List Doc → List Doc → Doc :=
  argumentsDocOf .all false

/-- The argument list of an ordinary call, which is left ungrouped when
the call is a link of a long curried chain. -/
def argumentsDocMaybeOpen (openArgs : Bool) :
    Bool → Bool → Bool → Bool → List Doc → List Doc → List Doc → Doc :=
  argumentsDocOf .all openArgs

/-- A brace enclosed statement list.  An empty body is written `{}` only
where prettier does so: in a function, a loop, or a `static` block. -/
def blockDocOf (collapseEmpty : Bool) (isEmpty : Bool) (inner : Doc) : Doc :=
  if isEmpty then
    if collapseEmpty then t "{}" else t "{" ++ .hardline ++ t "}"
  else t "{" ++ .nest indentWidth (.hardline ++ inner) ++ .hardline ++ t "}"

/-- The body attached to the head of an `if`, a loop or a `with`. -/
def clauseDoc (isBlock isEmptyStatement : Bool) (d : Doc) : Doc :=
  if isEmptyStatement then t ";"
  else if isBlock then t " " ++ d
  else .nest indentWidth (.line ++ d)

/-- A member access, given the documents of its object and of the access
itself. -/
def memberDocOf (inline : Bool) (objDoc lookup : Doc) : Doc :=
  objDoc ++ (if inline then lookup else .group (.nest indentWidth (.softline ++ lookup)))

/-- A computed member access, given the document of the index. -/
def indexLookupDoc (numeric : Bool) (d : Doc) : Doc :=
  if numeric then t "[" ++ d ++ t "]"
  else .group (t "[" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t "]")

/-- One `${…}` substitution of a template literal.  Prettier lays the
substitution out on one line, however long it is; only one that breaks of
itself is broken, and then the kind of expression says whether it is
indented. -/
def templateSubstDoc (indents : Bool) (d : Doc) : Doc :=
  let flat := Doc.render 1000000 d
  if !flat.any (· == '\n') then t "${" ++ t flat ++ t "}"
  else if indents then
    .group (t "${" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t "}")
  else .group (t "${" ++ d ++ t "}")

/-- The names a module is asked for with, whose one string argument
prettier writes on the line of the call, however long it is. -/
def requireLikeNames : List String :=
  ["require", "require.resolve", "require.resolve.paths", "import.meta.resolve"]

/-- The names of the calls of a test framework, whose arguments prettier
writes on the line of the call. -/
def testCallNames : List String :=
  ["it", "it.only", "it.skip", "describe", "describe.only", "describe.skip",
   "test", "test.only", "test.skip", "test.fixme", "test.step", "test.describe",
   "test.describe.only", "test.describe.skip", "test.describe.fixme",
   "test.describe.parallel", "test.describe.parallel.only", "test.describe.serial",
   "test.describe.serial.only", "skip", "xit", "xdescribe", "xtest", "fit",
   "fdescribe", "ftest"]

/-- The parts of a `fill`: the elements, with their commas, separated by
line breaks.  The comma of an element belongs to the element itself, so
that the width the layout measures counts it; `trailer` is what follows
the last element, which is the trailing comma when the array breaks. -/
def fillParts (trailer : Doc) : List Doc → List Doc
  | [] => []
  | [d] => [d ++ trailer]
  | d :: rest => (d ++ t ",") :: .line :: fillParts trailer rest

/-! ## Declarations -/

/-- The decorators in front of a class or of a class member, given their
documents. -/
def decoratorsPrefix (items : List Doc) : Doc :=
  if items.isEmpty then Doc.nil
  else .group (Doc.joinWith .line items ++ .line)

/-- The decorators of a class.  Prettier writes each of them on a line of
its own: they break every group they stand in.  The lines themselves are
ordinary ones, so that a class written where the whole line is laid out
flat, as a `{...expr}` child of a JSX element may be, keeps its
decorators on the line of the `class`. -/
def classDecoratorsPrefix (items : List Doc) : Doc :=
  if items.isEmpty then Doc.nil
  else .breakParent ++ Doc.joinWith .line items ++ .line

/-- The superclass of a class expression, given its document.  Prettier
puts the superclass of a class assigned to something in parentheses of
its own when it does not fit on the line of the `extends`. -/
def superClassDoc (ofAssign : Bool) (d : Doc) : Doc :=
  if ofAssign then
    .group (.ifBreak (t "(" ++ .nest indentWidth (.softline ++ d) ++ .softline ++ t ")") d)
  else d

/-- A declaration written with `keyword`, given the documents of its
declarators.  A declaration of several names, one of which is given a
value, always writes them on lines of their own. -/
def declarationDocOf (keyword : String) (isForInit hasValue : Bool) (docs : List Doc) : Doc :=
  let sep : Doc := if hasValue && !isForInit then .hardline else .line
  match docs with
  | [] => t keyword ++ (if isForInit then .nil else semiDoc)
  | first :: rest =>
    let firstDoc := if rest.isEmpty then first else .nest indentWidth first
    .group (t keyword ++ t " " ++ firstDoc
      ++ .nest indentWidth (Doc.concat (rest.map (fun d => t "," ++ sep ++ d)))
      ++ (if isForInit then .nil else semiDoc))

/-- A `var`, `let` or `const` declaration, given the documents of its
declarators. -/
def declarationDoc (kind : VarKind) (isForInit hasValue : Bool) (docs : List Doc) : Doc :=
  declarationDocOf (varKindText kind) isForInit hasValue docs

/-- What stands in front of the operator of a link of an operator chain: a
space, or, under `experimentalOperatorPosition: "start"`, nothing, since
the line that may break is written after it, in front of the operator
itself.  `inline` says that this is a link prettier never breaks in front
of. -/
def binOpLead (inline : Bool) : Doc :=
  if Options.operatorAtStart && !inline then .nil else t " "

/-- The operator of a link of an operator chain together with the operand
that follows it.  The line the chain breaks at stands after the operator,
or, under `experimentalOperatorPosition: "start"`, in front of it. -/
def binOpTail (op : BinOp) (inline : Bool) (operandDoc : Doc) : Doc :=
  if inline then t (binOpText op) ++ t " " ++ operandDoc
  else if Options.operatorAtStart then .line ++ t (binOpText op) ++ t " " ++ operandDoc
  else t (binOpText op) ++ .line ++ operandDoc

/-- The `with { type: "json" }` of an import; nothing when there is no
attribute.  The one attribute `type`, whose value is a string, is the one
every engine knows, and prettier keeps it on the line of the import
however long that line becomes; any other list of attributes is laid out
as an object literal is. -/
def importAttrsDoc (attrs : List ImportAttr) : Doc :=
  if attrs.isEmpty then Doc.nil
  else
    -- the attributes are names of an object as far as `quoteProps` is
    -- concerned: one of them that cannot lose its quotes quotes them all
    let quoteAll := Options.quoteProps == .consistent
      && attrs.any fun a => !isIdentifierName a.key && !isSimpleNumberString a.key
    let items := attrs.map fun a =>
      t ((if !quoteAll && isIdentifierName a.key then a.key else strLit a.key)
        ++ ": " ++ strLit a.value)
    let listDoc := sepList "{" "}" true .es5 items
    let isTypeOnly := match attrs with | [a] => a.key == "type" | _ => false
    t " with " ++ (if isTypeOnly then Doc.removeLines listDoc else listDoc)

/-! ## Rendering -/

/-- Lay out a document under the given options: at their `printWidth`,
with their indentation style, and with their line terminator. -/
def renderDoc (opts : Options) (d : Doc) : String :=
  Doc.renderWith { tabWidth := opts.tabWidth, useTabs := opts.useTabs }
    opts.endOfLine.text opts.printWidth d

end Language.JavaScript.PrinterCommon
