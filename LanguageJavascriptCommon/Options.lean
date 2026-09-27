/-!
# Prettier's options

The record of the formatting options the printers read, together with the
small vocabulary the printers use to ask questions of it.

Prettier's own options are described at
<https://prettier.io/docs/options>.  The ones that decide how JavaScript
and TypeScript are laid out are all here; the ones that select a file, a
parser or a plugin (`filepath`, `parser`, `rangeStart`, `rangeEnd`,
`requirePragma`, `insertPragma`, `embeddedLanguageFormatting`,
`vueIndentScriptAndStyle`, `htmlWhitespaceSensitivity`, `proseWrap`) have
no meaning for a printer that is handed a syntax tree, and are not here.
`objectWrap` and the experimental options are listed in `OPTIONS.md`,
which records what is implemented and what is not.

`Options` is a class, so that a printer function can take it as an
instance argument and every call inside the printer can leave it
implicit; `Language.JavaScript.defaultOptions` is prettier's default
configuration.
-/

namespace Language.JavaScript

/-- `quoteProps`: when the printer writes the quotes of a property name. -/
inductive QuoteProps where
  /-- `"as-needed"`: only where a property name requires them. -/
  | asNeeded
  /-- `"consistent"`: if one property of an object requires quotes, every
  property of that object is quoted. -/
  | consistent
  /-- `"preserve"`: a name the tree holds as a string keeps its quotes. -/
  | preserve
deriving BEq, Repr, Inhabited, DecidableEq

/-- `trailingComma`: where the printer writes a comma after the last item
of a list it has broken over several lines. -/
inductive TrailingComma where
  /-- `"none"`: nowhere. -/
  | none
  /-- `"es5"`: where ES5 allows one — arrays, objects, and, in
  TypeScript, tuple types, enums and type parameter declarations. -/
  | es5
  /-- `"all"`: also in call arguments and parameter lists. -/
  | all
deriving BEq, Repr, Inhabited, DecidableEq

/-- `arrowParens`: whether the sole parameter of an arrow function keeps
its parentheses. -/
inductive ArrowParens where
  /-- `"always"`: `(x) => x`. -/
  | always
  /-- `"avoid"`: `x => x`, where the parameter is a plain name. -/
  | avoid
deriving BEq, Repr, Inhabited, DecidableEq

/-- `experimentalOperatorPosition`: where the operator of a binary
expression stands once the expression is broken over several lines. -/
inductive OperatorPosition where
  /-- `"end"`: at the end of the line before the operand. -/
  | atEnd
  /-- `"start"`: at the start of the line of the operand. -/
  | atStart
deriving BEq, Repr, Inhabited, DecidableEq

/-- `endOfLine`: the line terminator the output is written with.
Prettier's `"auto"` reads the terminator out of the input text, which a
printer handed a syntax tree cannot do; it is not here. -/
inductive EndOfLine where
  | lf | crlf | cr
deriving BEq, Repr, Inhabited, DecidableEq

/-- The line terminator itself. -/
def EndOfLine.text : EndOfLine → String
  | .lf => "\n"
  | .crlf => "\r\n"
  | .cr => "\r"

/-- The kind of list a trailing comma is being asked about: which of
prettier's `trailingComma` settings write one there. -/
inductive CommaKind where
  /-- A list that never takes a trailing comma: one whose last item is a
  rest element, and a TypeScript type argument list. -/
  | never
  /-- A list that takes one from `"es5"` up: an array, an object, a
  destructuring pattern, a named import or export, and, in TypeScript, a
  tuple type, an enum body and a type parameter declaration. -/
  | es5
  /-- A list that takes one only at `"all"`: the arguments of a call and
  the parameters of a function. -/
  | all
deriving BEq, Repr, Inhabited, DecidableEq

/-- Prettier's options, as far as they decide the layout of JavaScript and
TypeScript.  The defaults are prettier's own. -/
class Options where
  /-- `printWidth`: the width the layout aims at. -/
  printWidth : Nat := 80
  /-- `tabWidth`: the number of columns of one indentation step. -/
  tabWidth : Nat := 2
  /-- `useTabs`: indent with tabs rather than spaces. -/
  useTabs : Bool := false
  /-- `semi`: end every statement with a semicolon. -/
  semi : Bool := true
  /-- `singleQuote`: prefer `'` to `"` for a string literal. -/
  singleQuote : Bool := false
  /-- `jsxSingleQuote`: prefer `'` to `"` for a JSX attribute. -/
  jsxSingleQuote : Bool := false
  /-- `quoteProps`: when a property name is quoted. -/
  quoteProps : QuoteProps := .asNeeded
  /-- `trailingComma`: where a broken list ends with a comma. -/
  trailingComma : TrailingComma := .all
  /-- `bracketSpacing`: spaces just inside the braces of an object. -/
  bracketSpacing : Bool := true
  /-- `bracketSameLine`: the `>` of a broken JSX opening element stands at
  the end of the last attribute line rather than on a line of its own. -/
  bracketSameLine : Bool := false
  /-- `arrowParens`: whether a sole arrow parameter keeps its
  parentheses. -/
  arrowParens : ArrowParens := .always
  /-- `singleAttributePerLine`: a JSX element with more than one attribute
  is always broken, one attribute to a line. -/
  singleAttributePerLine : Bool := false
  /-- `endOfLine`: the line terminator of the output. -/
  endOfLine : EndOfLine := .lf
  /-- `experimentalOperatorPosition`: where a broken binary expression
  writes its operator. -/
  operatorPosition : OperatorPosition := .atEnd
  /-- `experimentalTernaries`: lay a conditional expression out with the
  `?` at the end of the line of the test and the `:` in front of the
  alternate, rather than with both operators in front of their branch. -/
  experimentalTernaries : Bool := false
deriving Repr

/-- Prettier's default configuration. -/
@[reducible] def defaultOptions : Options := {}

instance : Inhabited Options := ⟨defaultOptions⟩

namespace Options

variable [o : Options]
include o

/-- The preferred quote of a string literal: `'` under `singleQuote`. -/
def preferredQuote : Char := if singleQuote then '\'' else '"'

/-- The preferred quote of a JSX attribute: `'` under `jsxSingleQuote`. -/
def preferredJSXQuote : Char := if jsxSingleQuote then '\'' else '"'

/-- Whether a list of the given kind ends with a comma when it is broken
over several lines. -/
def hasTrailingComma (k : CommaKind) : Bool :=
  match k, trailingComma with
  | .never, _ => false
  | _, .none => false
  | .es5, _ => true
  | .all, .all => true
  | .all, .es5 => false

/-- The text of a statement terminator: empty under `semi: false`. -/
def semiText : String := if semi then ";" else ""

/-- Whether a broken binary expression writes its operator at the start of
the line of the operand that follows it. -/
def operatorAtStart : Bool := operatorPosition == .atStart

end Options

/-! ## Reading options from the command line

The dump programs take their options as `name=value` arguments, spelled
the way prettier's own configuration spells them, so that the comparison
scripts can hand the same configuration to prettier and to the printer.
-/

namespace Options

/-- Apply one `name=value` setting.  An unknown name, or a value that does
not belong to its option, leaves the options as they are and is reported
in the second component. -/
def setOption (o : Options) (name value : String) : Options × Bool :=
  let bool? : Option Bool :=
    if value == "true" then some true else if value == "false" then some false else none
  match name with
  | "printWidth" => match value.toNat? with
    | some n => ({ o with printWidth := n }, true)
    | none => (o, false)
  | "tabWidth" => match value.toNat? with
    | some n => if n == 0 then (o, false) else ({ o with tabWidth := n }, true)
    | none => (o, false)
  | "useTabs" => match bool? with
    | some b => ({ o with useTabs := b }, true)
    | none => (o, false)
  | "semi" => match bool? with
    | some b => ({ o with semi := b }, true)
    | none => (o, false)
  | "singleQuote" => match bool? with
    | some b => ({ o with singleQuote := b }, true)
    | none => (o, false)
  | "jsxSingleQuote" => match bool? with
    | some b => ({ o with jsxSingleQuote := b }, true)
    | none => (o, false)
  | "bracketSpacing" => match bool? with
    | some b => ({ o with bracketSpacing := b }, true)
    | none => (o, false)
  | "bracketSameLine" => match bool? with
    | some b => ({ o with bracketSameLine := b }, true)
    | none => (o, false)
  | "singleAttributePerLine" => match bool? with
    | some b => ({ o with singleAttributePerLine := b }, true)
    | none => (o, false)
  | "quoteProps" =>
    if value == "as-needed" then ({ o with quoteProps := .asNeeded }, true)
    else if value == "consistent" then ({ o with quoteProps := .consistent }, true)
    else if value == "preserve" then ({ o with quoteProps := .preserve }, true)
    else (o, false)
  | "trailingComma" =>
    if value == "none" then ({ o with trailingComma := .none }, true)
    else if value == "es5" then ({ o with trailingComma := .es5 }, true)
    else if value == "all" then ({ o with trailingComma := .all }, true)
    else (o, false)
  | "arrowParens" =>
    if value == "always" then ({ o with arrowParens := .always }, true)
    else if value == "avoid" then ({ o with arrowParens := .avoid }, true)
    else (o, false)
  | "experimentalTernaries" => match bool? with
    | some b => ({ o with experimentalTernaries := b }, true)
    | none => (o, false)
  | "experimentalOperatorPosition" =>
    if value == "end" then ({ o with operatorPosition := .atEnd }, true)
    else if value == "start" then ({ o with operatorPosition := .atStart }, true)
    else (o, false)
  | "endOfLine" =>
    if value == "lf" then ({ o with endOfLine := .lf }, true)
    else if value == "crlf" then ({ o with endOfLine := .crlf }, true)
    else if value == "cr" then ({ o with endOfLine := .cr }, true)
    else (o, false)
  | _ => (o, false)

/-- Apply one command line argument of the shape `name=value`.  Anything
else is not a setting, and is reported as unrecognised. -/
def setArg (o : Options) (arg : String) : Options × Bool :=
  match arg.splitOn "=" with
  | [name, value] => setOption o name value
  | _ => (o, false)

/-- Read the `name=value` arguments of a command line, from `start`
onwards, returning the options and the arguments that were not settings. -/
def ofArgs (start : Options) (args : List String) : Options × List String :=
  args.foldl
    (fun (acc : Options × List String) arg =>
      let (o, ok) := setArg acc.1 arg
      if ok then (o, acc.2) else (acc.1, acc.2 ++ [arg]))
    (start, [])

end Options

end Language.JavaScript
