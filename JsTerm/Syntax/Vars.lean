module

public import JsTerm.Syntax.Vars.Rename
public import JsTerm.Syntax.Vars.Occs

/-!
# Variables of the JavaScript grammar: renaming, occurrences

The variables of `JsTerm` are typed de Bruijn indices into two contexts of variables (the
constants and the mutable variables) and one of join points.  This module gives the passes
of the conversion and of the printer the operations on them:

* **renaming** (`JsExpr.renameM`), in any monad: in `Id` it moves a term to a larger context
  (`JsExpr.wkC`, under a new binder); in `Option` it moves a term to a smaller one when it
  does not mention the variables left out (`JsExpr.closed?`: a term that mentions no variable
  at all is valid in every context);
* **occurrences** (`JsBlock.occs`): every read and assignment of a variable, with whether it
  is inside a closure or a loop (where it may be evaluated more than once).

The two are in `JsTerm/Syntax/Vars/`: `Rename.lean` and `Occs.lean`.
-/
