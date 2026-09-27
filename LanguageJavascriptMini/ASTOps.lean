/-
Small functions on the JavaScript syntax tree.

`MiniAST.AST` holds the *definition* of the tree and nothing else; the
functions that build or read a value of it live here, so that a change to
one of them does not rebuild the tree.
-/
import LanguageJavascriptMini.AST

open NonEmpty.String

namespace Language.JavaScript.MiniAST

/-! ## Import clauses -/

namespace MiniImportClause

/-- Build an import clause, checking that it binds something. -/
def mk? (default_ namespace_ : Option NonEmptyString) (named : Option (List Specifier))
    (mod : NonEmptyString) (attrs : List ImportAttr := []) : Option MiniImportClause :=
  if h : default_.isSome ∨ namespace_.isSome ∨ named.isSome then
    some ⟨default_, namespace_, named, mod, attrs, h⟩
  else
    Option.none

/-- Build an import clause; a placeholder if it binds nothing. -/
def mk! (default_ namespace_ : Option NonEmptyString) (named : Option (List Specifier))
    (mod : NonEmptyString) (attrs : List ImportAttr := []) : MiniImportClause :=
  (mk? default_ namespace_ named mod attrs).getD default

end MiniImportClause

end Language.JavaScript.MiniAST
