/-
The deterministic JavaScript syntax tree (`MiniAST`).

`Language.JavaScript.AST` is a faithful port of the Haskell
`language-javascript` AST: every node carries a `JSAnnot` recording the
source position and the comments and whitespace that preceded the token, so
that the printer can reproduce the layout of the input.  Two programs which
differ only in layout (`import  def  from 'mod'` versus `import def from
"mod"`) have *different* ASTs there.

`MiniAST` is the opposite: it stores only the meaning of the program.

* there are no annotations, so no positions, no comments and no whitespace;
* redundant syntax is normalised away — parentheses (the printer puts them
  back where the precedence requires them), automatic versus explicit
  semicolons, `new X` versus `new X()`, and the two spellings of a call;
* string literals hold their *decoded* value rather than the source text,
  and numeric literals are normalised.

Consequently the AST is *deterministic*: two sources that mean the same
thing give equal `MiniAST` values, and the printer turns a value back into
one canonical, opinionated rendering of it.

The refined component types it is phrased in terms of — `NonEmptyString`,
`NEList`, `JSNumber` and `RegExpLit` — are those of
`Language.JavaScript.Types`, and the leaf types it shares with the other
trees — the operators, `VarKind`, `MethodKind`, `Specifier`, `ImportAttr`
and `JSXName` — those of `Language.JavaScript.Common`.  Both live in
`Language.JavaScript`, the parent namespace of this one, so they are in
scope without an `open`.

This module holds the *definition* of the tree and nothing else: the types,
their default values, their equality, and the smart constructors that build
a value of a type whose fields are constrained.  The functions that read and
write the text of a literal are in `MiniAST.StringLit`, and the printer in
`MiniAST.Printer`.

The tree is a large family of mutually recursive types, and the `‹c›.inj`
theorems the compiler writes for a constructor by default — which say that
two equal applications of it agree argument by argument, and which only a
proof about the tree would use — cost more to check than everything else in
this file together.  They are turned off below.
-/
import LanguageJavascriptCommon.Common

open NonEmpty.String

set_option genInjectivity false

namespace Language.JavaScript.MiniAST

/-! ## Imports -/

/-- `import def, * as ns, { a, b as c } from "mod";`.  Each of the three
clauses is optional, but at least one of them has to be there. -/
structure MiniImportClause where
  /-- The default import, `import def from "mod"`. -/
  default_ : Option NonEmptyString
  /-- The namespace import, `import * as ns from "mod"`. -/
  namespace_ : Option NonEmptyString
  /-- The named imports, `import { a, b as c } from "mod"`. -/
  named : Option (List Specifier)
  /-- The module the names come from. -/
  mod : NonEmptyString
  /-- The import attributes, `with { type: "json" }`. -/
  attrs : List ImportAttr := []
  /-- An import must bind something. -/
  binds : default_.isSome ∨ namespace_.isSome ∨ named.isSome
deriving DecidableEq

instance : Inhabited MiniImportClause :=
  ⟨{ default_ := some default, namespace_ := .none, named := .none, mod := default,
     attrs := [], binds := Or.inl rfl }⟩

/-- An `import` declaration. -/
inductive MiniImportDeclaration where
  /-- `import "mod";`, possibly with import attributes. -/
  | bare (mod : NonEmptyString) (attrs : List ImportAttr)
  /-- `import ... from "mod";` -/
  | clause (clause : MiniImportClause)
deriving DecidableEq, Inhabited

/-! ## The syntax tree -/

mutual

/-- Expressions. -/
inductive MiniExpr where
  /-- An identifier. -/
  | ident (name : NonEmptyString)
  /-- A numeric literal, as the number it denotes. -/
  | number (value : JSNumber)
  /-- A string literal, holding the characters it denotes (not the source text). -/
  | string (value : String)
  /-- A regular expression literal: its pattern and its flags. -/
  | regex (re : RegExpLit)
  | null
  | true_
  | false_
  | this
  /-- `super.name`, the only forms `super` may be written in being a
  member access and a call; `super` on its own is not an expression. -/
  | superDot (name : NonEmptyString)
  /-- `super[idx]` -/
  | superIndex (idx : MiniExpr)
  /-- `super(args)`, the call to the constructor of the parent class. -/
  | superCall (args : List MiniExpr)
  /-- `new.target` -/
  | newTarget
  /-- `[a, , b]` -/
  | array (elements : List MiniArrayElement)
  /-- `{ a: 1 }` -/
  | object (properties : List MiniProperty)
  /-- `lhs op rhs`, for an assignment operator `op`. -/
  | assign (lhs : MiniExpr) (op : AssignOp) (rhs : MiniExpr)
  /-- A destructuring assignment, `[a, b] = xs` or `({ a } = o)`: the left
  hand side is a pattern rather than an expression. -/
  | assignPattern (lhs : MiniPattern) (rhs : MiniExpr)
  | await (expr : MiniExpr)
  /-- `callee(args)` -/
  | call (callee : MiniExpr) (args : List MiniExpr)
  /-- `obj.name` -/
  | dot (obj : MiniExpr) (name : NonEmptyString)
  /-- `obj.#name`, the access to a private class member. -/
  | privateDot (obj : MiniExpr) (name : NonEmptyString)
  /-- A private name used on its own, which only `#x in obj` allows. -/
  | privateName (name : NonEmptyString)
  /-- `obj[index]` -/
  | index (obj : MiniExpr) (idx : MiniExpr)
  /-- An optional chain expression. -/
  | chain (base : MiniExpr) (links : NEList MiniChainLink)
  /-- `import.meta` -/
  | importMeta
  /-- A dynamic import, `import(specifier)` or `import(specifier, options)`. -/
  | importCall (specifier : MiniExpr) (options : Option MiniExpr)
  /-- `class name extends heritage { body }` used as an expression. -/
  | classExpr (decorators : List MiniExpr) (name : Option NonEmptyString)
      (heritage : Option MiniExpr) (body : List MiniClassElement)
  /-- The comma operator, `lhs, rhs`. -/
  | seq (lhs : MiniExpr) (rhs : MiniExpr)
  | binary (lhs : MiniExpr) (op : BinOp) (rhs : MiniExpr)
  | postfix (expr : MiniExpr) (op : PostfixOp)
  /-- `cond ? thenE : elseE` -/
  | ternary (cond : MiniExpr) (thenE : MiniExpr) (elseE : MiniExpr)
  /-- `(params) => body`, and `async (params) => body` when `isAsync` is
  set. -/
  | arrow (isAsync : Bool) (params : List MiniParam) (body : MiniArrowBody)
  /-- A function expression; `isAsync` and `isGenerator` select `async` and `*`. -/
  | func (isAsync : Bool) (isGenerator : Bool) (name : Option NonEmptyString)
      (params : List MiniParam) (body : List MiniStatement)
  /-- `new callee(args)` -/
  | new (callee : MiniExpr) (args : List MiniExpr)
  /-- `...expr` -/
  | spread (expr : MiniExpr)
  /-- A template literal: an optional tag, the text before the first
  substitution, and one part per substitution. -/
  | template (tag : Option MiniExpr) (head : String) (parts : List MiniTemplatePart)
  | unary (op : UnaryOp) (expr : MiniExpr)
  /-- `yield expr` -/
  | yield (expr : Option MiniExpr)
  /-- `yield* expr` -/
  | yieldFrom (expr : MiniExpr)
  /-- A JSX element or fragment, `<div />` or `<>...</>`. -/
  | jsx (node : MiniJSXNode)

/-- A JSX element or fragment. -/
inductive MiniJSXNode where
  /-- `<name attrs>children</name>`, and `<name attrs />` when `children`
  is `none`. -/
  | element (name : JSXName) (attrs : List MiniJSXAttribute)
      (children : Option (List MiniJSXChild))
  /-- `<>children</>` -/
  | fragment (children : List MiniJSXChild)

/-- One attribute of a JSX element. -/
inductive MiniJSXAttribute where
  /-- `name`, `name="value"` or `name={expr}`. -/
  | attr (name : JSXName) (value : Option MiniJSXAttrValue)
  /-- `{...expr}` -/
  | spread (expr : MiniExpr)

/-- The value of a JSX attribute. -/
inductive MiniJSXAttrValue where
  /-- `name="value"`, holding the characters the value denotes. -/
  | string (value : String)
  /-- `name={expr}` -/
  | expr (e : MiniExpr)
  /-- `name=<x />`, an element written as the value with no braces. -/
  | node (n : MiniJSXNode)

/-- One child of a JSX element. -/
inductive MiniJSXChild where
  /-- Text.  It holds the characters it denotes; the characters a parser
  would read as markup are written as entities, and every run of
  whitespace in it is meaningful, as a run written on one line is: it is
  printed as `{" "}` where the line breaks there. -/
  | text (value : String)
  /-- `{expr}` -/
  | expr (e : MiniExpr)
  /-- `{}`, a substitution with nothing in it, which a source may hold
  where a comment stands between the braces. -/
  | emptyExpr
  /-- A nested element or fragment. -/
  | node (n : MiniJSXNode)

/-- One link of an optional chain: a member access or a call, `optional`
saying whether it is written with `?.`. -/
inductive MiniChainLink where
  /-- `.name` or `?.name` -/
  | dot (optional : Bool) (name : NonEmptyString)
  /-- `.#name` or `?.#name` -/
  | privateDot (optional : Bool) (name : NonEmptyString)
  /-- `[idx]` or `?.[idx]` -/
  | index (optional : Bool) (idx : MiniExpr)
  /-- `(args)` or `?.(args)` -/
  | call (optional : Bool) (args : List MiniExpr)

/-- A binding pattern. -/
inductive MiniPattern where
  /-- `x` -/
  | ident (name : NonEmptyString)
  /-- `[a, , b, ...r]` -/
  | array (elements : List MiniArrayPatternElem)
  /-- `{ a, b: c, ...r }`; `rest` is the `...r`, if there is one. -/
  | object (props : List MiniObjectPatternProp) (rest : Option MiniPattern)
  /-- `pat = value`: the value is used when what is matched is `undefined`. -/
  | withDefault (pat : MiniPattern) (value : MiniExpr)
  /-- A target which is not a binding, as in `[o.p] = xs`: the expression
  the value is assigned to.  A declaration cannot have one. -/
  | target (expr : MiniExpr)

/-- One element of an array pattern. -/
inductive MiniArrayPatternElem where
  /-- An elision, as in `[a, , b]`. -/
  | hole
  | elem (pat : MiniPattern)
  /-- `...rest`, which JavaScript only allows last. -/
  | rest (pat : MiniPattern)

/-- One property of an object pattern, `{ key: value }`; `{ a }` is the
property whose key is `a` and whose value is the pattern `a`. -/
structure MiniObjectPatternProp where
  /-- The property read from the object. -/
  key : MiniPropertyName
  /-- The pattern the property is matched against. -/
  value : MiniPattern

/-- A parameter of a function, an arrow or a method: a pattern, or a rest
parameter, which JavaScript only allows last. -/
inductive MiniParam where
  /-- An ordinary parameter, `x`, `x = 1` or `{ a, b }`. -/
  | plain (pat : MiniPattern)
  /-- `...rest` -/
  | rest (pat : MiniPattern)

/-- An element of an array literal; `hole` is an elision, as in `[1, , 2]`. -/
inductive MiniArrayElement where
  | elem (expr : MiniExpr)
  | hole

/-- The body of an arrow function. -/
inductive MiniArrowBody where
  | expr (expr : MiniExpr)
  | block (body : List MiniStatement)

/-- The `${...}` substitution of a template literal together with the text
following it. -/
structure MiniTemplatePart where
  /-- The substituted expression. -/
  expr : MiniExpr
  /-- The template text following the substitution. -/
  suffix : String

/-- The name of a property or method. -/
inductive MiniPropertyName where
  | ident (name : NonEmptyString)
  /-- A private name, `#x`, without its `#`; only a class member has one. -/
  | private_ (name : NonEmptyString)
  /-- A quoted name, holding the characters it denotes. -/
  | string (value : String)
  /-- A numeric name, as the number it denotes. -/
  | number (value : JSNumber)
  /-- `[expr]` -/
  | computed (expr : MiniExpr)

/-- A member of an object literal. -/
inductive MiniProperty where
  | keyValue (key : MiniPropertyName) (value : MiniExpr)
  /-- `{ x }` -/
  | shorthand (name : NonEmptyString)
  /-- `{ ...rest }` -/
  | spread (expr : MiniExpr)
  | method (kind : MethodKind) (key : MiniPropertyName) (params : List MiniParam)
      (body : List MiniStatement)

/-- A member of a class body: a method, a field or a static block. -/
inductive MiniClassElement where
  /-- A method, a generator, a getter or a setter. -/
  | method (decorators : List MiniExpr) (isStatic : Bool) (kind : MethodKind)
      (key : MiniPropertyName) (params : List MiniParam) (body : List MiniStatement)
  /-- A field, `x = 1;`, `#x;` or `static x = 1;`; `isAccessor` writes it
  with the `accessor` keyword, as `accessor x = 1;`. -/
  | field (decorators : List MiniExpr) (isStatic : Bool) (isAccessor : Bool)
      (key : MiniPropertyName) (init : Option MiniExpr)
  /-- A static initialisation block, `static { ... }`. -/
  | staticBlock (body : List MiniStatement)

/-- One declarator of a `var`/`let`/`const` statement. -/
structure MiniDeclarator where
  /-- The name, or destructuring pattern, being bound. -/
  lhs : MiniPattern
  /-- The initialiser, if any. -/
  init : Option MiniExpr

/-- The first clause of a `for (;;)` statement. -/
inductive MiniForInit where
  | none
  | expr (expr : MiniExpr)
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)

/-- The binder of a `for (... in ...)` or `for (... of ...)` statement:
either an assignment to something which already exists, or a declaration. -/
inductive MiniForHead where
  | pattern (lhs : MiniPattern)
  | decl (kind : VarKind) (lhs : MiniPattern)
  /-- `for (using x of xs)` and `for await (await using x of xs)`, the
  explicit resource management binders; `isAwait` selects the second. -/
  | usingDecl (isAwait : Bool) (lhs : MiniPattern)

/-- One `case`/`default` of a `switch`. -/
inductive MiniSwitchCase where
  | case (test : MiniExpr) (body : List MiniStatement)
  | default (body : List MiniStatement)

/-- The `catch` clause of a `try`; `guard` is the (non standard) `if` guard. -/
structure MiniCatchClause where
  /-- The bound exception. -/
  param : MiniPattern
  /-- The guard of a `catch (e if cond)` clause. -/
  guard : Option MiniExpr
  /-- The body. -/
  body : List MiniStatement

/-- The `finally` clause of a `try`. -/
inductive MiniFinallyClause where
  | none
  | some (body : List MiniStatement)

/-- What follows the block of a `try`.  A `try` needs at least one `catch`
or a `finally`, which this makes structurally impossible to violate. -/
inductive MiniTryTail where
  /-- At least one `catch` clause, and possibly a `finally`. -/
  | catches (catches : NEList MiniCatchClause) (fin : MiniFinallyClause)
  /-- No `catch` clause, only a `finally`. -/
  | finallyOnly (body : List MiniStatement)

/-- Statements. -/
inductive MiniStatement where
  | block (body : List MiniStatement)
  | break_ (label : Option NonEmptyString)
  | continue_ (label : Option NonEmptyString)
  /-- `class name extends heritage { body }` as a declaration. -/
  | classDecl (decorators : List MiniExpr) (name : NonEmptyString) (heritage : Option MiniExpr)
      (body : List MiniClassElement)
  /-- `var`/`let`/`const` declaration; it declares at least one name. -/
  | decl (kind : VarKind) (decls : NEList MiniDeclarator)
  /-- `using x = e;` and `await using x = e;`, the explicit resource
  management declarations; `isAwait` selects the second. -/
  | using_ (isAwait : Bool) (decls : NEList MiniDeclarator)
  /-- `debugger;` -/
  | debugger
  | doWhile (body : MiniStatement) (cond : MiniExpr)
  | for_ (init : MiniForInit) (cond : Option MiniExpr) (step : Option MiniExpr)
      (body : MiniStatement)
  | forIn (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  /-- `for (head of obj) body`, and `for await (head of obj) body` when
  `isAwait` is set. -/
  | forOf (isAwait : Bool) (head : MiniForHead) (obj : MiniExpr) (body : MiniStatement)
  | funcDecl (isAsync : Bool) (isGenerator : Bool) (name : NonEmptyString)
      (params : List MiniParam) (body : List MiniStatement)
  | if_ (cond : MiniExpr) (thenS : MiniStatement) (elseS : Option MiniStatement)
  | labelled (label : NonEmptyString) (stmt : MiniStatement)
  | empty
  /-- An expression statement. -/
  | expr (expr : MiniExpr)
  | return_ (expr : Option MiniExpr)
  | switch (disc : MiniExpr) (cases : List MiniSwitchCase)
  | throw (expr : MiniExpr)
  | try_ (body : List MiniStatement) (tail : MiniTryTail)
  | while_ (cond : MiniExpr) (body : MiniStatement)
  | with_ (obj : MiniExpr) (body : MiniStatement)

/-- An `export` declaration. -/
inductive MiniExportDeclaration where
  /-- `export { a } from "mod";`, possibly with import attributes. -/
  | fromClause (specs : List Specifier) (mod : NonEmptyString) (attrs : List ImportAttr)
  /-- `export { a };` -/
  | locals (specs : List Specifier)
  /-- `export * from "mod";` and `export * as ns from "mod";`; `alias_` is
  the `ns` of the second form. -/
  | all (alias_ : Option NonEmptyString) (mod : NonEmptyString) (attrs : List ImportAttr)
  /-- `export default <expression>;` -/
  | defaultExpr (expr : MiniExpr)
  /-- `export <declaration>` -/
  | decl (stmt : MiniStatement)

/-- A top level item: a statement, or an `import`/`export` declaration. -/
inductive MiniModuleItem where
  | stmt (stmt : MiniStatement)
  | importDecl (decl : MiniImportDeclaration)
  | exportDecl (decl : MiniExportDeclaration)

end

/-! ## Default values -/

instance : Inhabited MiniExpr := ⟨.null⟩
instance : Inhabited MiniStatement := ⟨.empty⟩
instance : Inhabited MiniPattern := ⟨.ident default⟩
instance : Inhabited MiniArrayPatternElem := ⟨.hole⟩
instance : Inhabited MiniObjectPatternProp := ⟨⟨.ident default, .ident default⟩⟩
instance : Inhabited MiniChainLink := ⟨.dot true default⟩
instance : Inhabited MiniJSXNode := ⟨.fragment []⟩
instance : Inhabited MiniJSXAttribute := ⟨.attr (.ident default) none⟩
instance : Inhabited MiniJSXAttrValue := ⟨.string ""⟩
instance : Inhabited MiniJSXChild := ⟨.text ""⟩
instance : Inhabited MiniParam := ⟨.plain (.ident default)⟩
instance : Inhabited MiniArrayElement := ⟨.hole⟩
instance : Inhabited MiniArrowBody := ⟨.block []⟩
instance : Inhabited MiniTemplatePart := ⟨⟨default, ""⟩⟩
instance : Inhabited MiniPropertyName := ⟨.ident default⟩
instance : Inhabited MiniProperty := ⟨.shorthand default⟩
instance : Inhabited MiniClassElement := ⟨.staticBlock []⟩
instance : Inhabited MiniDeclarator := ⟨⟨.ident default, none⟩⟩
instance : Inhabited MiniForInit := ⟨.none⟩
instance : Inhabited MiniForHead := ⟨.pattern default⟩
instance : Inhabited MiniSwitchCase := ⟨.default []⟩
instance : Inhabited MiniCatchClause := ⟨⟨.ident default, none, []⟩⟩
instance : Inhabited MiniFinallyClause := ⟨.none⟩
instance : Inhabited MiniTryTail := ⟨.finallyOnly []⟩
instance : Inhabited MiniExportDeclaration := ⟨.locals []⟩
instance : Inhabited MiniModuleItem := ⟨.stmt default⟩

/-- A whole program: a list of top level items. -/
structure MiniProgram where
  /-- The top level items. -/
  items : List MiniModuleItem
deriving Inhabited

/-! ## Equality -/

deriving instance BEq for MiniExpr, MiniStatement, MiniModuleItem

instance : BEq MiniProgram := ⟨fun a b => a.items == b.items⟩
end Language.JavaScript.MiniAST
