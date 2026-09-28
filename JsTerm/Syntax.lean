module

public import JsTerm.Ty

@[expose] public section

set_option autoImplicit false

/-!
# The JavaScript grammar

`LeanScript.Term` models Lean code: intrinsically typed, de Bruijn indexed, every redex that
could be computed computed.  The grammar here models the **JavaScript** the backend prints:
an *untyped* subset of JavaScript, split into expressions and statements, with named
variables, `return`, loops with a mutable accumulator, calls of the runtime prelude, and join
points.

The grammar is deliberately small; `JsTerm.PrintMini` maps it onto the full JavaScript
syntax tree of `LanguageJavascriptMini`, whose printer writes the `.js` file.

* **Literals** (`JsLit`): booleans, numbers (a `Float`, JavaScript's `number`), `BigInt`s
  and strings.
* **Operators** are split by the type of their operands (`JsNumBinOp` on numbers,
  `JsBigIntBinOp` on `BigInt`s, `JsBoolBinOp` on booleans, `JsStrBinOp` on strings), except
  `===` / `!==`, which compare values of any type.
* **Expressions** (`JsExpr`): variables, literals, operators, calls of values and of runtime
  helpers (`helper`, a function of the prelude the program is printed with), arrow functions
  of zero or more parameters, object literals (records `{ _1: …, _2: … }` and unions
  `{ tag: i, _1: … }`), arrays (lists, generic arrays), typed arrays, indexing, member
  access, `new`, spreads, conditionals.
* **Statements** (`JsStmt`): `const`, `let`, assignment (to a variable, a member or an
  element), array and object destructuring, expression statements, `return`, `if`/`else`,
  counting `for` loops, `for … of` loops, `while` loops, `throw`, and **join points**:
  `join x block` is a labelled block (`L: { block }`) the statements of which may `jump` to
  it, which assigns the join point's variable `x` and leaves the block (`x = e; break L;`);
  the statements after the `join` statement are the body of the join point.  A jump names its
  join point by a **de Bruijn index**: `jump 0 e` leaves the innermost enclosing `join` block,
  `jump 1 e` the one around it, and so on (an arrow function starts afresh: a jump never leaves
  a function).

The runtime helpers a program calls (`JsHelper`) are written in this grammar too: the prelude
of a module is printed from it, like the exported functions.

A function body is a list of statements every path of which ends in a `return` (or a
`throw`), or, inside a `join` block, in a `jump`.
-/

namespace MoreJs

/-! ## Literals -/

/-- A literal. -/
inductive JsLit where
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- A `number`. -/
  | number (n : Float)
  /-- A `BigInt`, `12n`. -/
  | bigint (n : Int)
  /-- A string. -/
  | str (s : String)
  deriving Inhabited, Repr, BEq

/-- The integer `number` literal `n` (exact for `|n| ≤ 2^53`). -/
def JsLit.int (n : Int) : JsLit := .number (Float.ofInt n)

/-- The shape of a double: `NaN`, an infinity, or `± m * 2 ^ e` exactly. -/
inductive FloatParts where
  | nan
  | inf (neg : Bool)
  /-- `(neg ? -1 : 1) * m * 2 ^ e` (`m = 0` for the zeros). -/
  | finite (neg : Bool) (m : Nat) (e : Int)
  deriving Inhabited, Repr, BEq

/-- The shape of a double, read off its IEEE bits. -/
def floatParts (f : Float) : FloatParts :=
  let bits : Nat := f.toBits.toNat
  let neg : Bool := (bits / 2 ^ 63) % 2 == 1
  let ex : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let frac : Nat := bits % 2 ^ 52
  if ex == 2047 then
    if frac != 0 then .nan else .inf neg
  else if ex == 0 then .finite neg frac (-1074)
  else .finite neg (frac + 2 ^ 52) ((ex : Int) - 1075)

/-- The integer a finite double stands for, when it is one of absolute value `≤ 2^53`. -/
def floatSmallInt? (f : Float) : Option Int :=
  match floatParts f with
  | .finite neg m e =>
    let v? : Option Nat :=
      if e ≥ 0 then some (m * 2 ^ e.toNat)
      else if m % 2 ^ e.natAbs == 0 then some (m / 2 ^ e.natAbs) else none
    match v? with
    | some v => if v ≤ 2 ^ 53 then some (if neg then -(v : Int) else v) else none
    | none => none
  | _ => none

/-- The number of decimal digits of `n` (`1` for `0`). -/
def decDigits (n : Nat) : Nat := (toString n).length

/-- The shortest decimal `(digits, exponent)` with `digits * 10 ^ exponent` reading back as
    the double `m * 2 ^ e` (`m > 0`). -/
def shortestDecimal (m : Nat) (e : Int) : Nat × Int :=
  -- the exact value as `D * 10 ^ (-K)`
  let (D, K) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 0) else (m * 5 ^ e.natAbs, e.natAbs)
  let exact : Float := Float.ofScientific D true K
  let L := decDigits D
  let rec go (fuel k : Nat) : Nat × Int :=
    match fuel with
    | 0 => (D, -(K : Int))
    | fuel + 1 =>
      if k ≥ L then (D, -(K : Int)) else
      let drop := L - k
      let q := D / 10 ^ drop
      let r := D % 10 ^ drop
      let q := if 2 * r ≥ 10 ^ drop then q + 1 else q
      let ex : Int := (drop : Int) - K
      let f : Float := if ex ≥ 0 then Float.ofScientific q false ex.toNat
        else Float.ofScientific q true ex.natAbs
      if f.toBits == exact.toBits then (q, ex) else go fuel (k + 1)
  go 20 1

/-- A `number`, as JavaScript source: an integer when it is a small one, otherwise the
    shortest decimal that reads back as the same double (`NaN`, `Infinity`, `-Infinity`,
    `-0` for the special values). -/
def numberSource (f : Float) : String :=
  match floatSmallInt? f, floatParts f with
  | some 0, .finite true _ _ => "-0"
  | some n, _ => toString n
  | none, .nan => "NaN"
  | none, .inf neg => if neg then "-Infinity" else "Infinity"
  | none, .finite neg m e =>
    let (d, ex) := shortestDecimal m e
    (if neg then "-" else "") ++ toString d ++ (if ex == 0 then "" else s!"e{ex}")

/-! ## Operators, by the type of their operands -/

/-- A binary operator on `number`s. -/
inductive JsNumBinOp where
  | add | sub | mul | div | mod | pow
  | lt | le | gt | ge
  | bitAnd | bitOr | bitXor | shl | shr | ushr
  deriving Inhabited, Repr, BEq

/-- A binary operator on `BigInt`s (there is no `>>>` on `BigInt`s; `**` is left out, as the
    printer's syntax tree has no exponent operator and `Math.pow` does not take `BigInt`s). -/
inductive JsBigIntBinOp where
  | add | sub | mul | div | mod
  | lt | le | gt | ge
  | bitAnd | bitOr | bitXor | shl | shr
  deriving Inhabited, Repr, BEq

/-- A binary operator on booleans. -/
inductive JsBoolBinOp where
  | and | or
  deriving Inhabited, Repr, BEq

/-- A binary operator on strings. -/
inductive JsStrBinOp where
  /-- `a + b`. -/
  | concat
  | lt | le | gt | ge
  deriving Inhabited, Repr, BEq

/-- A binary operator: one of a type, or the strict (in)equality of any two values. -/
inductive JsBinOp where
  | num (op : JsNumBinOp)
  | bigint (op : JsBigIntBinOp)
  | bool (op : JsBoolBinOp)
  | str (op : JsStrBinOp)
  /-- `===`. -/
  | strictEq
  /-- `!==`. -/
  | strictNeq
  deriving Inhabited, Repr, BEq

/-- A unary operator on `number`s. -/
inductive JsNumUnOp where
  | neg | bitNot
  deriving Inhabited, Repr, BEq

/-- A unary operator on `BigInt`s. -/
inductive JsBigIntUnOp where
  | neg | bitNot
  deriving Inhabited, Repr, BEq

/-- A unary operator on booleans. -/
inductive JsBoolUnOp where
  | not
  deriving Inhabited, Repr, BEq

/-- A unary operator. -/
inductive JsUnOp where
  | num (op : JsNumUnOp)
  | bigint (op : JsBigIntUnOp)
  | bool (op : JsBoolUnOp)
  deriving Inhabited, Repr, BEq

/-! ## Expressions and statements -/

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
  /-- `(params) => { body }`: a function of zero or more parameters. -/
  | arrow (params : List String) (body : List JsStmt)
  /-- `[e₀, e₁, …]`: a list or a generic array. -/
  | array (elems : List JsExpr)
  /-- `Ctor.of(e₀, …)`: a typed array literal (`Uint8Array.of(1, 2)`). -/
  | typedArray (ctor : String) (elems : List JsExpr)
  /-- `e[i]`. -/
  | index (e : JsExpr) (i : Nat)
  /-- `e.name`. -/
  | member (e : JsExpr) (name : String)
  /-- `c ? a : b`. -/
  | cond (c a b : JsExpr)
  /-- `{ k₀: e₀, k₁: e₁, … }`: an object literal (a record `{ _1: …, _2: … }`, a union
      `{ tag: 0, _1: … }`, a memoised delay). -/
  | object (fields : List (String × JsExpr))
  /-- `e[i]`, indexed by an expression. -/
  | at (e i : JsExpr)
  /-- `new C(args)`. -/
  | new (ctor : JsExpr) (args : List JsExpr)
  /-- `...e`, inside an array literal or the arguments of a call. -/
  | spread (e : JsExpr)

/-- Statements. -/
inductive JsStmt where
  /-- `const x = e;` -/
  | const (x : String) (e : JsExpr)
  /-- `let x = e;`, or `let x;` -/
  | letMut (x : String) (e : Option JsExpr)
  /-- `x = e;` -/
  | assign (x : String) (e : JsExpr)
  /-- `const [x₀, , x₂] = e;` (`none` skips a position). -/
  | destructure (xs : List (Option String)) (e : JsExpr)
  /-- `const { k₀: x₀, k₁: x₁ } = e;`: the properties `kᵢ` of the object `e`, named `xᵢ`. -/
  | destructureObj (binds : List (String × String)) (e : JsExpr)
  /-- `o.name = e;` -/
  | setMember (o : JsExpr) (name : String) (e : JsExpr)
  /-- `o[i] = e;` -/
  | setAt (o i e : JsExpr)
  /-- `e;`, an expression evaluated for its effect. -/
  | expr (e : JsExpr)
  /-- `while (c) { body }`. -/
  | while (c : JsExpr) (body : List JsStmt)
  /-- `return e;` -/
  | ret (e : JsExpr)
  /-- `if (c) { t } else { e }` (no `else` when `e` is empty). -/
  | ite (c : JsExpr) (t e : List JsStmt)
  /-- `for (let i = 0; i < n; i++) { body }`, the counter a `BigInt` when `big`. -/
  | forRange (i : String) (big : Bool) (n : JsExpr) (body : List JsStmt)
  /-- `for (const x of xs) { body }`. -/
  | forOf (x : String) (xs : JsExpr) (body : List JsStmt)
  /-- `throw new C(msg);` (`C` an error class: `Error`, `RangeError`, …). -/
  | throw (ctor : String) (msg : String)
  /-- A join point: the labelled block `L: { block }`, whose statements may `jump` to it
      (de Bruijn index `0` inside `block`), assigning `x` (declared before, `let x;`).  The
      statements after it are the body of the join point. -/
  | join (x : String) (block : List JsStmt)
  /-- `x = e; break L;`, where `L` and `x` are the label and the variable of the enclosing
      `join` block of de Bruijn index `j`. -/
  | jump (j : Nat) (e : JsExpr)
end

instance : Inhabited JsExpr := ⟨.lit (.bool false)⟩
instance : Inhabited JsStmt := ⟨.throw "Error" "unreachable"⟩

/-- A top-level function: `export const name = (params) => { body };`.  The layouts of its
    parameters and of its result are not part of the (untyped) grammar: they are only
    written in the comment above it. -/
structure JsFun where
  /-- The JavaScript name of the function. -/
  name : String
  /-- The Lean definition it was translated from. -/
  leanName : String
  /-- The parameters (zero or more). -/
  params : List String
  /-- The body; every path ends in a `return`. -/
  body : List JsStmt
  /-- The layouts of the parameters (for the comment). -/
  paramTys : List JsTerm := []
  /-- The layout of the result (for the comment). -/
  ret : JsTerm
  deriving Inhabited

/-- A function of the runtime prelude, `function name(params) { body }`, written in the
    grammar itself. -/
structure JsHelper where
  /-- The name the program calls it by. -/
  name : String
  /-- Its parameters. -/
  params : List String
  /-- Its body; every path ends in a `return` (or a `throw`). -/
  body : List JsStmt
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

/-! ## The dump (`-JsTerm-*.txt`) -/

namespace JsLit

/-- The literal, as JavaScript source. -/
def pretty : JsLit → String
  | .bool b => toString b
  | .number f => numberSource f
  | .bigint n => toString n ++ "n"
  | .str s => s.quote

end JsLit

/-- The operator, as JavaScript source. -/
def JsNumBinOp.pretty : JsNumBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%" | .pow => "**"
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^" | .shl => "<<" | .shr => ">>"
  | .ushr => ">>>"

/-- The operator, as JavaScript source. -/
def JsBigIntBinOp.pretty : JsBigIntBinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^" | .shl => "<<" | .shr => ">>"

/-- The operator, as JavaScript source. -/
def JsBinOp.pretty : JsBinOp → String
  | .num op => op.pretty
  | .bigint op => op.pretty
  | .bool .and => "&&" | .bool .or => "||"
  | .str .concat => "+" | .str .lt => "<" | .str .le => "<=" | .str .gt => ">"
  | .str .ge => ">="
  | .strictEq => "===" | .strictNeq => "!=="

/-- The operator, as JavaScript source. -/
def JsUnOp.pretty : JsUnOp → String
  | .num .neg | .bigint .neg => "-"
  | .num .bitNot | .bigint .bitNot => "~"
  | .bool .not => "!"

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
  | .object fs =>
    if fs.isEmpty then "{}" else
    "{ " ++ ", ".intercalate (fs.map fun (k, e) => s!"{k}: {e.pretty ind}") ++ " }"
  | .at e i => s!"{e.pretty ind}[{i.pretty ind}]"
  | .new c args => "new " ++ c.pretty ind ++ "(" ++ ", ".intercalate (args.map (·.pretty ind)) ++ ")"
  | .spread e => "..." ++ e.pretty ind

/-- A statement, indented by `ind`, ending in a new line. -/
partial def JsStmt.pretty (ind : String) : JsStmt → String
  | .const x e => s!"{ind}const {x} = {e.pretty ind};\n"
  | .letMut x (some e) => s!"{ind}let {x} = {e.pretty ind};\n"
  | .letMut x none => s!"{ind}let {x};\n"
  | .assign x e => s!"{ind}{x} = {e.pretty ind};\n"
  | .destructure xs e =>
    let b := xs.map fun
      | some x => x
      | none => ""
    s!"{ind}const [{", ".intercalate b}] = {e.pretty ind};\n"
  | .destructureObj bs e =>
    let b := bs.map fun (k, x) => if k == x then k else s!"{k}: {x}"
    s!"{ind}const \{ {", ".intercalate b} } = {e.pretty ind};\n"
  | .setMember o n e => s!"{ind}{o.pretty ind}.{n} = {e.pretty ind};\n"
  | .setAt o i e => s!"{ind}{o.pretty ind}[{i.pretty ind}] = {e.pretty ind};\n"
  | .expr e => s!"{ind}{e.pretty ind};\n"
  | .while c body =>
    s!"{ind}while ({c.pretty ind}) \{\n" ++ JsStmt.prettyBlock (ind ++ "  ") body ++ ind ++ "}\n"
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
  | .throw c msg => s!"{ind}throw new {c}({msg.quote});\n"
  | .join x block =>
    s!"{ind}join {x} \{\n" ++ JsStmt.prettyBlock (ind ++ "  ") block ++ ind ++ "}\n"
  | .jump j e => s!"{ind}jump {j} {e.pretty ind};\n"

/-- Statements, each indented by `ind`. -/
partial def JsStmt.prettyBlock (ind : String) (ss : List JsStmt) : String :=
  String.join (ss.map (JsStmt.pretty ind))
end

/-- A function, for the dump. -/
def JsFun.pretty (f : JsFun) : String :=
  s!"// {f.leanName}\nexport const {f.name} = ({", ".intercalate f.params}) => \{\n" ++
    JsStmt.prettyBlock "  " f.body ++ "};\n"

/-- A helper of the runtime prelude, for the dump. -/
def JsHelper.pretty (h : JsHelper) : String :=
  s!"function {h.name}({", ".intercalate h.params}) \{\n" ++ JsStmt.prettyBlock "  " h.body ++ "}\n"

/-- A module, for the dump. -/
def JsModule.pretty (m : JsModule) : String :=
  s!"// runtime helpers: {", ".intercalate (m.helpers.map (·.name))}\n\n" ++
  String.join (m.helpers.map fun h => h.pretty ++ "\n") ++
  "\n".intercalate (m.funs.map JsFun.pretty)

end MoreJs

end
