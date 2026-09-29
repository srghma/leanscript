/-
Component types shared by the JavaScript trees.

The deterministic tree (`MiniAST`) and the scope safe tree (`BrujinAST`)
describe the *same* language, so they agree on the small leaf types that
carry no syntax tree inside them: the operators, the keyword of a variable
declaration, the kind of a method, one `name as alias` of an import or
export clause, one import attribute, and the name of a JSX element or
attribute.  Those types live here, in the `Language.JavaScript` namespace —
the parent of the namespace of each tree, so they are visible from all of
them without an `open` — instead of in one tree, so that neither tree has to
depend on another only to name them.

`NonEmptyString`, the non empty string they are phrased in terms of, comes from
`Language.JavaScript.Types`, which is where the *refined* component types
(non empty strings and lists, numbers, regular expression literals) live.
-/
import LanguageJavascriptCommon.Types

open NonEmpty.String

namespace Language.JavaScript

/-! ## Operators -/

/-- Binary operators. -/
inductive BinOp where
  | and | or
  /-- `??`, the nullish coalescing operator. -/
  | coalesce
  | bitAnd | bitOr | bitXor
  | eq | neq | strictEq | strictNeq
  | lt | le | gt | ge
  | lsh | rsh | ursh
  | plus | minus | times | divide | mod
  /-- `**`, exponentiation (right associative; its left operand may not be a unary
  expression). -/
  | exp
  | inOp | instanceOf
deriving Repr, BEq, DecidableEq, Inhabited

/-- Prefix operators. -/
inductive UnaryOp where
  | not | tilde | plus | minus
  | typeof | void | delete
  | preIncr | preDecr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Postfix operators. -/
inductive PostfixOp where
  | incr | decr
deriving Repr, BEq, DecidableEq, Inhabited

/-- Assignment operators. -/
inductive AssignOp where
  | assign
  | plus | minus | times | divide | mod
  | lsh | rsh | ursh
  | bitAnd | bitXor | bitOr
  /-- `&&=` -/
  | logicalAnd
  /-- `||=` -/
  | logicalOr
  /-- `??=` -/
  | coalesce
deriving Repr, BEq, DecidableEq, Inhabited

/-- The keyword introducing a variable declaration. -/
inductive VarKind where
  | var | let_ | const
deriving Repr, BEq, DecidableEq, Inhabited

/-- What kind of method a member of an object or class literal is. -/
inductive MethodKind where
  /-- `m() {}` -/
  | normal
  /-- `*m() {}` -/
  | generator
  /-- `async m() {}` -/
  | async
  /-- `async *m() {}` -/
  | asyncGenerator
  /-- `get m() {}` -/
  | get
  /-- `set m(v) {}` -/
  | set
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## Import and export clauses -/

/-- One `name` or `name as alias` of an import or export clause. -/
structure Specifier where
  /-- The exported name. -/
  name : NonEmptyString
  /-- The local name, when it differs. -/
  alias_ : Option NonEmptyString
deriving Repr, BEq, DecidableEq, Inhabited

/-- One import attribute, `type: "json"`, of an `import` or of an
`export ... from` declaration.  Both the key — an identifier or a string
literal in source — and the value hold the characters they denote, so the
two ways of writing a key give the same value. -/
structure ImportAttr where
  /-- The key. -/
  key : String
  /-- The value. -/
  value : String
deriving Repr, BEq, DecidableEq, Inhabited

/-! ## JSX names -/

/-- The name of a JSX element, or of one of its attributes: a plain name,
a member of a name (`Foo.Bar`, which only an element has), or a namespaced
name (`svg:path`). -/
inductive JSXName where
  /-- `div`, `Foo`, `data-id` -/
  | ident (name : NonEmptyString)
  /-- `Foo.Bar` -/
  | member (obj : JSXName) (name : NonEmptyString)
  /-- `svg:path` -/
  | namespaced (ns : NonEmptyString) (name : NonEmptyString)
deriving Repr, BEq, DecidableEq, Inhabited

namespace JSXName

/-- The name, as it is written in source. -/
def render : JSXName → String
  | .ident n => n.toString
  | .member o n => o.render ++ "." ++ n.toString
  | .namespaced ns n => ns.toString ++ ":" ++ n.toString

instance : ToString JSXName := ⟨render⟩

end JSXName

end Language.JavaScript
