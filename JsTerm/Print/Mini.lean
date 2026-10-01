import JsTerm.Print.Mini.Block
import JsTerm.Lower.LocalHelpers

/-!
# Printing the JavaScript grammar with `LanguageJavascriptMini`

`MoreJs.JsModule.toJs m` is the text of the `.js` file of a module: a header comment, the
import of the runtime functions the module calls (`import { … } from "…/runtime.js";`), the
definitions of the operations the module writes itself (`localHelper?`: `List.append` on cons
cells, `JsTerm.Lower.LocalHelpers`), the constants its functions share (`const $tag0 = { tag: 0 };`), and the exported functions, all
converted to the JavaScript syntax tree of `LanguageJavascriptMini` (`MiniAST`) and printed by
its printer (prettier's style: two space indentation, double quotes, semicolons, 80 columns).

(These files are not `module`s: `LanguageJavascriptMini` is not written in the module
system, and a module cannot import a file that is not one.)

The helpers and the printer's state are in `JsTerm/Print/Mini/Basic.lean`, the conversion of
expressions and blocks in `JsTerm/Print/Mini/Block.lean`; this module prints functions and
modules.

The variables of the grammar are de Bruijn indices into three contexts (constants, mutable
variables, join points); the printer names them, from the hints of their binders: `x$1`,
`acc$2`, … (a counter per function, so that no name hides another), and the parameters of an
exported function keep their names.

The mapping is direct:

* an imported operation is a call of the runtime function of its name
  (`bigint_nat__lean_nat_div(a, b)`, `JsOpImported.runtimeName`), an inlined one its template
  (`a & b`, `BigInt(a)`);
* a function is an arrow of all its parameters (`(a, b) => …`), and a call passes them all
  (`f(a, b)`);
* `const`/`let`/assignment are the statements of the same name, a destructuring
  `const { _1: a, _3: c } = r;`;
* a case analysis on an enum or a union is a chain of `if (s === 0) … else if (s === 1) …
  else …` (on `s.tag` for a union, each arm taking the fields it uses apart);
* a join point `join x block rest` is `let x$k; j$k: { block }` followed by `rest`, and a jump
  to it `x$k = e; break j$k;` (no `break` at the end of the block, and no labelled block when
  every jump to it is at its end);
* a counting loop is `for (let i = 0n; i < n; i++) { … }` (`0` for a `number` counter), an
  element loop `for (const x of xs) { … }`, and the end of an iteration (`next`) nothing at
  the end of the body, `continue;` elsewhere; the last iteration of a counting loop only is
  `if (0n < n) { const i = n - 1n; … }` (labelled, `break j$k;`, when an iteration ends
  before its end);
* an arrow whose body is a single `return e` is printed `(x) => e`; a value never read is
  `undefined`.
-/

namespace MoreJs

open Language.JavaScript Language.JavaScript.MiniAST NonEmpty.String

/-! ## Functions and modules -/

/-- A function as an exported declaration: `export const name = (params) => { body };`.

    A definition without parameters (`JsFun.isConst`: its type is not a function) is a
    constant, `export const name = value;`, as purescript-backend-optimizer writes it,
    rather than a function of no arguments: the value is computed once, when the module is
    loaded (as Lean itself initialises a closed constant), and read without a call.  The
    translated program is pure and total, so computing it there instead of at each call does
    not change it.  A body that is not a single `return e` is computed by an arrow called on
    the spot, `export const name = (() => { … })();`. -/
def JsFun.toMini (f : JsFun) : MiniModuleItem :=
  let go : PM MiniModuleItem := do
    -- the parameters keep their names (a name met twice gets a fresh one)
    let params ← f.params.foldlM (fun (acc : Array String) (p, _) =>
      if acc.contains p then do return acc.push (← freshName p) else return acc.push p) #[]
    let sc : Scope := { c := params.toList.reverse.map ident }
    let e ← match f.delegate? with
      | some (w, lit) =>
        -- a call of the worker it shares (`JsTerm.Print.Share`)
        pure (.arrow false (params.toList.map fun p => MiniParam.plain (.ident (nes p)))
          (.expr (.call (ident w) (shapeExpr lit :: params.toList.map ident))))
      | none => arrowToMini sc params.toList f.body
    let e := if f.isConst then
        match e with
        | .arrow _ [] (.expr v) => v
        | e => .call e []
      else e
    let decl : MiniStatement := .decl .const ⟨⟨.ident (nes f.name), some e⟩, []⟩
    return if f.exported then .exportDecl (.decl decl) else .stmt decl
  go.run' {}

/-- The import of the functions `names` of the runtime `path`:
    `import { a, b } from "path";`. -/
def importToMini (path : String) (names : List String) : MiniModuleItem :=
  if names.isEmpty then .stmt .empty else
  .importDecl (.clause (MiniImportClause.mk none none
    (some (names.map fun n => Specifier.mk (nes n) none)) (nes path) [] (Or.inr (Or.inr rfl))))

/-- The comment above an exported function: its Lean name and the types of its parameters and
    result. -/
def JsFun.docComment (f : JsFun) : String :=
  let ps := f.params.map fun (x, ty) => s!" * @param \{{ty}} {x}"
  let notes := f.notes.map fun l => s!" * {l}"
  -- a constant has a type, a function a result
  let ret := if f.isConst then s!" * @type \{{f.ret}}" else s!" * @returns \{{f.ret}}"
  "\n".intercalate ([s!"/**", s!" * `{f.leanName}`"] ++ notes ++ ps ++ [ret, " */"])

/-- The text of the `.js` file of a module.  `header` are comment lines put first; `runtime`
    is how the module refers to the runtime (a path relative to the module,
    `../../runtime.js`). -/
def JsModule.toJs (m : JsModule) (header : List String) (runtime : String) : String :=
  let head := String.join (header.map fun l => s!"// {l}\n")
  let importsTxt := if m.imports.isEmpty then "" else
    printProgram ⟨[importToMini runtime m.imports]⟩ ++ "\n"
  let localsTxt := String.join (m.locals.filterMap fun n =>
    (localHelper? n).map (· ++ "\n"))
  let funs := m.funs.map fun f => f.docComment ++ "\n" ++ printProgram ⟨[f.toMini]⟩
  head ++ "\n" ++ importsTxt ++ localsTxt ++ "\n".intercalate funs

end MoreJs
