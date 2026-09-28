module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The JavaScript grammar

`LeanScript.Term` models Lean code: intrinsically typed, de Bruijn indexed, every redex that
could be computed computed.  The grammar here models the **JavaScript** the backend prints:
named variables, statements, `return`, loops with a mutable accumulator, and calls of the
runtime prelude.  Every binder records the `JsTerm` of what it binds, so a dump of a
program (`JsModule.pretty`, the `-JsTerm.txt` file) shows how each value is laid out.

The grammar is deliberately small; `JsTerm.PrintMini` maps it onto the full JavaScript
syntax tree of `LanguageJavascriptMini`, whose printer writes the `.js` file.

* **Expressions** (`JsExpr`): variables, literals, operators, calls of values and of runtime
  helpers (`helper`, a function of the prelude the program is printed with), arrows,
  arrays (records, unions, lists, generic arrays), typed arrays, indexing, conditionals.
* **Statements** (`JsStmt`): `const`, `let`, assignment, array destructuring, `return`,
  `if`/`else`, counting `for` loops, `for … of` loops, `throw`.

A function body is a list of statements every path of which ends in a `return` (or a
`throw`).
-/

namespace MoreJs

/-- A literal. -/
inductive JsLit where
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- An integer `number`. -/
  | int (n : Int)
  /-- A `BigInt`, `12n`. -/
  | bigint (n : Int)
  /-- A floating point `number`: `mantissa * 2 ^ exponent` (exactly), or a special value. -/
  | float (mantissa : Int) (exponent : Int)
  /-- `NaN`, `Infinity`, `-Infinity`. -/
  | special (name : String)
  /-- A string. -/
  | str (s : String)
  deriving Inhabited, Repr, BEq

/-- A binary operator. -/
inductive JsBinOp where
  | add | sub | mul | div | mod | pow
  | strictEq | strictNeq | lt | le | gt | ge
  | and | or
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  deriving Inhabited, Repr, BEq

/-- A unary operator. -/
inductive JsUnOp where
  | not | neg | bitNot
  deriving Inhabited, Repr, BEq

mutual
/-- Expressions. -/
inductive JsExpr where
  /-- A variable. -/
  | var (x : String)
  /-- A literal. -/
  | lit (l : JsLit)
  /-- `a op b`. -/
  | bin (op : JsBinOp) (a b : JsExpr)
  /-- `op a`. -/
  | un (op : JsUnOp) (a : JsExpr)
  /-- A call of a function of the runtime prelude, by name. -/
  | helper (name : String) (args : List JsExpr)
  /-- `f(args)`. -/
  | call (f : JsExpr) (args : List JsExpr)
  /-- `(params) => { body }`. -/
  | arrow (params : List String) (body : List JsStmt)
  /-- `[e₀, e₁, …]`: a record, a union (tag first), a list or a generic array. -/
  | array (elems : List JsExpr)
  /-- `Ctor.of(e₀, …)`: a typed array literal (`Uint8Array.of(1, 2)`). -/
  | typedArray (ctor : String) (elems : List JsExpr)
  /-- `e[i]`. -/
  | index (e : JsExpr) (i : Nat)
  /-- `e.name`. -/
  | member (e : JsExpr) (name : String)
  /-- `c ? a : b`. -/
  | cond (c a b : JsExpr)

/-- Statements. -/
inductive JsStmt where
  /-- `const x = e;` -/
  | const (x : String) (ty : JsTerm) (e : JsExpr)
  /-- `let x = e;` -/
  | letMut (x : String) (ty : JsTerm) (e : JsExpr)
  /-- `x = e;` -/
  | assign (x : String) (e : JsExpr)
  /-- `const [x₀, , x₂] = e;` (`none` skips a position). -/
  | destructure (xs : List (Option (String × JsTerm))) (e : JsExpr)
  /-- `return e;` -/
  | ret (e : JsExpr)
  /-- `if (c) { t } else { e }` (no `else` when `e` is empty). -/
  | ite (c : JsExpr) (t e : List JsStmt)
  /-- `for (let i = 0; i < n; i++) { body }`, the counter a `BigInt` when `big`. -/
  | forRange (i : String) (big : Bool) (n : JsExpr) (body : List JsStmt)
  /-- `for (const x of xs) { body }`. -/
  | forOf (x : String) (xs : JsExpr) (body : List JsStmt)
  /-- `throw new Error(msg);` -/
  | throw (msg : String)
end

instance : Inhabited JsExpr := ⟨.lit (.bool false)⟩
instance : Inhabited JsStmt := ⟨.throw "unreachable"⟩

/-- A top-level function: `export function name(params) { body }`. -/
structure JsFun where
  /-- The JavaScript name of the function. -/
  name : String
  /-- The Lean definition it was translated from. -/
  leanName : String
  /-- The parameters and their layouts. -/
  params : List (String × JsTerm)
  /-- The layout of the result. -/
  ret : JsTerm
  /-- The body; every path ends in a `return`. -/
  body : List JsStmt
  deriving Inhabited

/-- A function of the runtime prelude: its name and its JavaScript source. -/
structure JsHelper where
  /-- The name the program calls it by. -/
  name : String
  /-- Its declaration, in JavaScript. -/
  source : String
  deriving Inhabited

/-- A whole module: the runtime helpers it needs, and its exported functions. -/
structure JsModule where
  /-- The configuration it was generated with. -/
  config : JsConfig
  /-- The helpers of the runtime prelude it calls, each once, in order of first use. -/
  helpers : List JsHelper
  /-- The exported functions. -/
  funs : List JsFun
  deriving Inhabited

/-! ## The dump (`-JsTerm.txt`) -/

namespace JsLit

/-- The literal, as JavaScript source. -/
def pretty : JsLit → String
  | .bool b => toString b
  | .int n => toString n
  | .bigint n => toString n ++ "n"
  | .float m e => s!"({m} * 2 ** {e})"
  | .special n => n
  | .str s => s.quote

end JsLit

/-- The operator, as JavaScript source. -/
def JsBinOp.pretty : JsBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%" | .pow => "**"
  | .strictEq => "===" | .strictNeq => "!==" | .lt => "<" | .le => "<=" | .gt => ">"
  | .ge => ">=" | .and => "&&" | .or => "||" | .bitAnd => "&" | .bitOr => "|"
  | .bitXor => "^" | .shl => "<<" | .shr => ">>" | .ushr => ">>>"

/-- The operator, as JavaScript source. -/
def JsUnOp.pretty : JsUnOp → String
  | .not => "!" | .neg => "-" | .bitNot => "~"

mutual
/-- An expression, on one line (arrows break lines). -/
partial def JsExpr.pretty (ind : String) : JsExpr → String
  | .var x => x
  | .lit l => l.pretty
  | .bin op a b => s!"({a.pretty ind} {op.pretty} {b.pretty ind})"
  | .un op a => s!"{op.pretty}{a.pretty ind}"
  | .helper n args => n ++ "(" ++ ", ".intercalate (args.map (·.pretty ind)) ++ ")"
  | .call f args => f.pretty ind ++ "(" ++ ", ".intercalate (args.map (·.pretty ind)) ++ ")"
  | .arrow ps body =>
    "(" ++ ", ".intercalate ps ++ ") => {\n" ++ JsStmt.prettyBlock (ind ++ "  ") body ++ ind ++ "}"
  | .array es => "[" ++ ", ".intercalate (es.map (·.pretty ind)) ++ "]"
  | .typedArray c es => c ++ ".of(" ++ ", ".intercalate (es.map (·.pretty ind)) ++ ")"
  | .index e i => s!"{e.pretty ind}[{i}]"
  | .member e n => s!"{e.pretty ind}.{n}"
  | .cond c a b => s!"({c.pretty ind} ? {a.pretty ind} : {b.pretty ind})"

/-- A statement, indented by `ind`, ending in a new line. -/
partial def JsStmt.pretty (ind : String) : JsStmt → String
  | .const x ty e => s!"{ind}const {x} : {ty} = {e.pretty ind};\n"
  | .letMut x ty e => s!"{ind}let {x} : {ty} = {e.pretty ind};\n"
  | .assign x e => s!"{ind}{x} = {e.pretty ind};\n"
  | .destructure xs e =>
    let b := xs.map fun
      | some (x, ty) => s!"{x} : {ty}"
      | none => ""
    s!"{ind}const [{", ".intercalate b}] = {e.pretty ind};\n"
  | .ret e => s!"{ind}return {e.pretty ind};\n"
  | .ite c t e =>
    let head := s!"{ind}if ({c.pretty ind}) \{\n{JsStmt.prettyBlock (ind ++ "  ") t}{ind}}"
    if e.isEmpty then head ++ "\n"
    else head ++ s!" else \{\n{JsStmt.prettyBlock (ind ++ "  ") e}{ind}}\n"
  | .forRange i big n body =>
    let z := if big then "0n" else "0"
    s!"{ind}for (let {i} = {z}; {i} < {n.pretty ind}; {i}++) \{\n" ++
      JsStmt.prettyBlock (ind ++ "  ") body ++ ind ++ "}\n"
  | .forOf x xs body =>
    s!"{ind}for (const {x} of {xs.pretty ind}) \{\n" ++ JsStmt.prettyBlock (ind ++ "  ") body ++
      ind ++ "}\n"
  | .throw msg => s!"{ind}throw new Error({msg.quote});\n"

/-- Statements, each indented by `ind`. -/
partial def JsStmt.prettyBlock (ind : String) (ss : List JsStmt) : String :=
  String.join (ss.map (JsStmt.pretty ind))
end

/-- A function, for the dump. -/
def JsFun.pretty (f : JsFun) : String :=
  let ps := ", ".intercalate (f.params.map fun (x, ty) => s!"{x} : {ty}")
  s!"// {f.leanName}\nexport function {f.name}({ps}) : {f.ret} \{\n" ++
    JsStmt.prettyBlock "  " f.body ++ "}\n"

/-- A module, for the dump. -/
def JsModule.pretty (m : JsModule) : String :=
  s!"// configuration: {m.config.describe}\n" ++
  s!"// runtime helpers: {", ".intercalate (m.helpers.map (·.name))}\n\n" ++
  "\n".intercalate (m.funs.map JsFun.pretty)

end MoreJs

end
