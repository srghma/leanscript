import JsTerm.Syntax
import LanguageJavascriptMini.Printer

/-!
# Printing the JavaScript grammar with `LanguageJavascriptMini`

`MoreJs.JsModule.toJs m` is the text of the `.js` file of a module: a header comment, the
runtime helpers the module calls (their JavaScript source, `MoreJs.JsHelper`), and the
exported functions, each converted to the JavaScript syntax tree of
`LanguageJavascriptMini` (`MiniAST`) and printed by its printer (prettier's style: two
space indentation, double quotes, semicolons, 80 columns).

(This file is not a `module`: `LanguageJavascriptMini` is not written in the module
system, and a module cannot import a file that is not one.)

The mapping is direct: a `const`/`let` is a declaration, a destructuring `const [a, , b] = e`
an array pattern, a counting loop a `for (let i = 0n; i < n; i++)`, an arrow whose body is a
single `return e` is printed `(x) => e`, and an `if` whose `else` branch is a single `if`
is printed `else if`.  Floats are printed as the shortest decimal that reads back as the
same double.
-/

namespace MoreJs

open Language.JavaScript Language.JavaScript.MiniAST NonEmpty.String

/-- A non-empty string (the grammar never produces an empty name). -/
def nes (s : String) : NonEmptyString :=
  (NonEmptyString.fromString? s).getD ⟨"_", by decide⟩

/-- An identifier. -/
def ident (s : String) : MiniExpr := .ident (nes s)

/-- A non-negative integer as a numeric literal. -/
def natNum (n : Nat) : MiniExpr := .number (.decimal n 0)

/-- An integer, with a unary minus when it is negative. -/
def intNum (n : Int) : MiniExpr :=
  if n < 0 then .unary .minus (natNum n.natAbs) else natNum n.natAbs

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

/-- A literal. -/
def litExpr : JsLit → MiniExpr
  | .bool true => .true_
  | .bool false => .false_
  | .int n => intNum n
  | .bigint n =>
    let b : MiniExpr := .number (.bigint .decimal n.natAbs)
    if n < 0 then .unary .minus b else b
  | .float m e =>
    let (d, ex) := shortestDecimal m.natAbs e
    let num : MiniExpr := .number (.decimal d ex)
    if m < 0 then .unary .minus num else num
  | .special "NaN" => ident "NaN"
  | .special "-Infinity" => .unary .minus (ident "Infinity")
  | .special n => ident n
  | .str s => .string s

/-- A binary operator. -/
def binOp : JsBinOp → Option BinOp
  | .add => some .plus | .sub => some .minus | .mul => some .times | .div => some .divide
  | .mod => some .mod | .pow => none | .strictEq => some .strictEq
  | .strictNeq => some .strictNeq | .lt => some .lt | .le => some .le | .gt => some .gt
  | .ge => some .ge | .and => some .and | .or => some .or | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr | .bitXor => some .bitXor | .shl => some .lsh | .shr => some .rsh
  | .ushr => some .ursh

/-- A unary operator. -/
def unOp : JsUnOp → UnaryOp
  | .not => .not | .neg => .minus | .bitNot => .tilde

mutual
/-- An expression as a `MiniAST` expression. -/
partial def exprToMini : JsExpr → MiniExpr
  | .var x => ident x
  | .lit l => litExpr l
  | .bin op a b => match binOp op with
    | some o => .binary (exprToMini a) o (exprToMini b)
    | none => .call (.dot (ident "Math") (nes "pow")) [exprToMini a, exprToMini b]
  | .un op a => .unary (unOp op) (exprToMini a)
  | .helper n args => .call (ident n) (args.map exprToMini)
  | .call f args => .call (exprToMini f) (args.map exprToMini)
  | .arrow ps body =>
    let params := ps.map fun p => MiniParam.plain (.ident (nes p))
    match body with
    | [.ret e] => .arrow false params (.expr (exprToMini e))
    | _ => .arrow false params (.block (stmtsToMini body))
  | .array es => .array (es.map fun e => .elem (exprToMini e))
  | .typedArray c es => .call (.dot (ident c) (nes "of")) (es.map exprToMini)
  | .index e i => .index (exprToMini e) (natNum i)
  | .member e n => .dot (exprToMini e) (nes n)
  | .cond c a b => .ternary (exprToMini c) (exprToMini a) (exprToMini b)

/-- A statement as a `MiniAST` statement. -/
partial def stmtToMini : JsStmt → MiniStatement
  | .const x _ e => .decl .const ⟨⟨.ident (nes x), some (exprToMini e)⟩, []⟩
  | .letMut x _ e => .decl .let_ ⟨⟨.ident (nes x), some (exprToMini e)⟩, []⟩
  | .assign x e => .expr (.assign (ident x) .assign (exprToMini e))
  | .destructure xs e =>
    let elems := xs.map fun
      | some (x, _) => MiniArrayPatternElem.elem (.ident (nes x))
      | none => .hole
    -- trailing holes are dropped (`[a, ,]` is `[a]`)
    let elems := (elems.reverse.dropWhile fun | .hole => true | _ => false).reverse
    .decl .const ⟨⟨.array elems, some (exprToMini e)⟩, []⟩
  | .ret e => .return_ (some (exprToMini e))
  | .ite c t e =>
    let els : Option MiniStatement := match e with
      | [] => none
      | [s@(.ite ..)] => some (stmtToMini s)
      | ss => some (.block (stmtsToMini ss))
    .if_ (exprToMini c) (.block (stmtsToMini t)) els
  | .forRange i big n body =>
    let zero : MiniExpr := if big then .number (.bigint .decimal 0) else natNum 0
    .for_ (.decl .let_ ⟨⟨.ident (nes i), some zero⟩, []⟩)
      (some (.binary (ident i) .lt (exprToMini n)))
      (some (.postfix (ident i) .incr)) (.block (stmtsToMini body))
  | .forOf x xs body =>
    .forOf false (.decl .const (.ident (nes x))) (exprToMini xs) (.block (stmtsToMini body))
  | .throw msg => .throw (.new (ident "Error") [.string msg])

/-- Statements. -/
partial def stmtsToMini (ss : List JsStmt) : List MiniStatement := ss.map stmtToMini
end

/-- A function as an exported declaration. -/
def JsFun.toMini (f : JsFun) : MiniModuleItem :=
  .exportDecl (.decl (.funcDecl false false (nes f.name)
    (f.params.map fun (x, _) => .plain (.ident (nes x))) (stmtsToMini f.body)))

/-- The comment above an exported function: its Lean name, and the layouts of its
    parameters and result. -/
def JsFun.docComment (f : JsFun) : String :=
  let ps := f.params.map fun (x, ty) => s!" * @param \{{ty}} {x}"
  "\n".intercalate (["/**", s!" * `{f.leanName}`"] ++ ps ++ [s!" * @returns \{{f.ret}}", " */"])

/-- The text of the `.js` file of a module.  `header` are comment lines put first. -/
def JsModule.toJs (m : JsModule) (header : List String) : String :=
  let head := String.join (header.map fun l => s!"// {l}\n")
  let helpers := if m.helpers.isEmpty then "" else
    "// ---- runtime helpers ----\n\n" ++ "\n\n".intercalate (m.helpers.map (·.source)) ++ "\n\n" ++
    "// ---- exported functions ----\n"
  let funs := m.funs.map fun f =>
    f.docComment ++ "\n" ++ printProgram ⟨[f.toMini]⟩
  head ++ "\n" ++ helpers ++ "\n" ++ "\n".intercalate funs

end MoreJs
