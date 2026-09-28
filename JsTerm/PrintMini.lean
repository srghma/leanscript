import JsTerm.Syntax
import LanguageJavascriptMini.Printer

/-!
# Printing the JavaScript grammar with `LanguageJavascriptMini`

`MoreJs.JsModule.toJs m` is the text of the `.js` file of a module: a header comment, the
imports of the runtime functions the module calls (`import { … } from "…/runtime/….mjs";`),
the constants its functions share (`const $c1 = { tag: 0 };`), and the exported functions,
all converted to the JavaScript syntax tree of
`LanguageJavascriptMini` (`MiniAST`) and printed by its printer (prettier's style: two
space indentation, double quotes, semicolons, 80 columns).

(This file is not a `module`: `LanguageJavascriptMini` is not written in the module
system, and a module cannot import a file that is not one.)

The mapping is direct: a `const`/`let` is a declaration, a destructuring `const [a, , b] = e`
an array pattern, a counting loop a `for (let i = 0n; i < n; i++)`, an arrow whose body is a
single `return e` is printed `(x) => e`, and an `if` whose `else` branch is a single `if`
is printed `else if`.  A join point `join x block` is the **labelled block** `j$k: { … }`
(`k` counting the join points of the function from the outside in, so nested blocks have
different labels) and a jump of de Bruijn index `i` is `x = e; break j$k;` for the variable
and the label of the `i`-th enclosing block.  An exported function is
`export const f = (x, y) => { … };`, a shared constant `const $c1 = e;`, a record
`{ _1: a, _2: b }`, a union `{ tag: 1, _1: a }`, and taking one apart
`const { _1: x, _3: z } = r;`.  Numbers are printed as integers when they are small
integers, otherwise as the shortest decimal that reads back as the same double.
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

/-- A `number` literal. -/
def numberExpr (f : Float) : MiniExpr :=
  match floatSmallInt? f, floatParts f with
  | some 0, .finite true _ _ => .unary .minus (natNum 0)
  | some n, _ => intNum n
  | none, .nan => ident "NaN"
  | none, .inf neg => if neg then .unary .minus (ident "Infinity") else ident "Infinity"
  | none, .finite neg m e =>
    let (d, ex) := shortestDecimal m e
    let num : MiniExpr := .number (.decimal d ex)
    if neg then .unary .minus num else num

/-- A literal. -/
def litExpr : JsLit → MiniExpr
  | .bool true => .true_
  | .bool false => .false_
  | .number f => numberExpr f
  | .bigint n =>
    let b : MiniExpr := .number (.bigint .decimal n.natAbs)
    if n < 0 then .unary .minus b else b
  | .str s => .string s

/-- An arithmetic or bitwise operator (`none` for `**`, printed `Math.pow(a, b)`). -/
def numBinOp : JsNumBinOp → Option BinOp
  | .add => some .plus | .sub => some .minus | .mul => some .times | .div => some .divide
  | .mod => some .mod | .pow => none | .lt => some .lt | .le => some .le | .gt => some .gt
  | .ge => some .ge | .bitAnd => some .bitAnd | .bitOr => some .bitOr
  | .bitXor => some .bitXor | .shl => some .lsh | .shr => some .rsh | .ushr => some .ursh

/-- An operator on `BigInt`s. -/
def bigIntBinOp : JsBigIntBinOp → BinOp
  | .add => .plus | .sub => .minus | .mul => .times | .div => .divide | .mod => .mod
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge | .bitAnd => .bitAnd
  | .bitOr => .bitOr | .bitXor => .bitXor | .shl => .lsh | .shr => .rsh

/-- A binary operator (`none` for `**` on numbers). -/
def binOp : JsBinOp → Option BinOp
  | .num op => numBinOp op
  | .bigint op => some (bigIntBinOp op)
  | .bool .and => some .and
  | .bool .or => some .or
  | .str .concat => some .plus
  | .str .lt => some .lt | .str .le => some .le | .str .gt => some .gt | .str .ge => some .ge
  | .strictEq => some .strictEq
  | .strictNeq => some .strictNeq

/-- A unary operator. -/
def unOp : JsUnOp → UnaryOp
  | .bool .not => .not
  | .num .neg | .bigint .neg => .minus
  | .num .bitNot | .bigint .bitNot => .tilde

/-- Where the statements are printed: the join points around them (innermost first, each as
    its label and variable) and how many join points the function has so far (for fresh
    labels). -/
structure JoinCtx where
  joins : List (String × String) := []
  next : Nat := 1

mutual
/-- An expression as a `MiniAST` expression. -/
partial def exprToMini (c : JoinCtx) : JsExpr → MiniExpr
  | .var x => ident x
  | .lit l => litExpr l
  | .bin op a b => match binOp op with
    | some o => .binary (exprToMini c a) o (exprToMini c b)
    | none => .call (.dot (ident "Math") (nes "pow")) [exprToMini c a, exprToMini c b]
  | .un op a => .unary (unOp op) (exprToMini c a)
  | .helper n args => .call (ident n) (args.map (exprToMini c))
  | .call f args => .call (exprToMini c f) (args.map (exprToMini c))
  | .arrow ps body =>
    let params := ps.map fun p => MiniParam.plain (.ident (nes p))
    -- a function starts afresh: no jump leaves it (the labels stay distinct all the same)
    let c' : JoinCtx := { joins := [], next := c.next }
    match body with
    | [.ret e] => .arrow false params (.expr (exprToMini c' e))
    | _ => .arrow false params (.block (stmtsToMini c' body))
  | .array es => .array (es.map fun e => .elem (exprToMini c e))
  | .typedArray k es => .call (.dot (ident k) (nes "of")) (es.map (exprToMini c))
  | .index e i => .index (exprToMini c e) (natNum i)
  | .member e n => .dot (exprToMini c e) (nes n)
  | .cond k a b => .ternary (exprToMini c k) (exprToMini c a) (exprToMini c b)
  | .object fs => .object (fs.map fun (k, e) => .keyValue (.ident (nes k)) (exprToMini c e))
  | .at e i => .index (exprToMini c e) (exprToMini c i)
  | .new k args => .new (exprToMini c k) (args.map (exprToMini c))
  | .spread e => .spread (exprToMini c e)

/-- A statement as `MiniAST` statements (a jump is two: the assignment and the `break`). -/
partial def stmtToMini (c : JoinCtx) : JsStmt → List MiniStatement
  | .const x e => [.decl .const ⟨⟨.ident (nes x), some (exprToMini c e)⟩, []⟩]
  | .letMut x e => [.decl .let_ ⟨⟨.ident (nes x), e.map (exprToMini c)⟩, []⟩]
  | .assign x e => [.expr (.assign (ident x) .assign (exprToMini c e))]
  | .destructure xs e =>
    let elems := xs.map fun
      | some x => MiniArrayPatternElem.elem (.ident (nes x))
      | none => .hole
    -- trailing holes are dropped (`[a, ,]` is `[a]`)
    let elems := (elems.reverse.dropWhile fun | .hole => true | _ => false).reverse
    [.decl .const ⟨⟨.array elems, some (exprToMini c e)⟩, []⟩]
  | .destructureObj bs e =>
    let props := bs.map fun (k, x) => MiniObjectPatternProp.mk (.ident (nes k)) (.ident (nes x))
    [.decl .const ⟨⟨.object props none, some (exprToMini c e)⟩, []⟩]
  | .setMember o n e => [.expr (.assign (.dot (exprToMini c o) (nes n)) .assign (exprToMini c e))]
  | .setAt o i e =>
    [.expr (.assign (.index (exprToMini c o) (exprToMini c i)) .assign (exprToMini c e))]
  | .expr e => [.expr (exprToMini c e)]
  | .while k body => [.while_ (exprToMini c k) (.block (stmtsToMini c body))]
  | .ret e => [.return_ (some (exprToMini c e))]
  | .ite k t e =>
    let els : Option MiniStatement := match e with
      | [] => none
      | [s@(.ite ..)] => match stmtToMini c s with
        | [m] => some m
        | ms => some (.block ms)
      | ss => some (.block (stmtsToMini c ss))
    [.if_ (exprToMini c k) (.block (stmtsToMini c t)) els]
  | .forRange i big n body =>
    let zero : MiniExpr := if big then .number (.bigint .decimal 0) else natNum 0
    [.for_ (.decl .let_ ⟨⟨.ident (nes i), some zero⟩, []⟩)
      (some (.binary (ident i) .lt (exprToMini c n)))
      (some (.postfix (ident i) .incr)) (.block (stmtsToMini c body))]
  | .forOf x xs body =>
    [.forOf false (.decl .const (.ident (nes x))) (exprToMini c xs) (.block (stmtsToMini c body))]
  | .throw k msg => [.throw (.new (ident k) [.string msg])]
  | .join x block =>
    let label := s!"j${c.next}"
    let c' : JoinCtx := { joins := (label, x) :: c.joins, next := c.next + 1 }
    [.labelled (nes label) (.block (stmtsToMini c' block))]
  | .jump j e =>
    match c.joins[j]? with
    | some (label, x) =>
      [.expr (.assign (ident x) .assign (exprToMini c e)), .break_ (some (nes label))]
    | none => [.throw (.new (ident "Error") [.string s!"LeanScript: jump to an unknown join point {j}"])]

/-- Statements.  (The labels of sibling join points are distinct too: each `join` takes the
    next number, whatever its depth.) -/
partial def stmtsToMini (c : JoinCtx) (ss : List JsStmt) : List MiniStatement :=
  (ss.foldl (fun (acc : Array MiniStatement × Nat) s =>
    let (ms, next) := acc
    let out := stmtToMini { c with next } s
    (ms ++ out, next + joinCount s)) (#[], c.next)).1.toList

/-- The number of join points a statement declares (outside of its arrows are counted too:
    they only need to differ, not to be dense). -/
partial def joinCount : JsStmt → Nat
  | .join _ b => 1 + (b.map joinCount).sum
  | .ite _ t e => (t.map joinCount).sum + (e.map joinCount).sum
  | .forRange _ _ _ b | .forOf _ _ b | .while _ b => (b.map joinCount).sum
  | _ => 0
end

/-- A function as an exported declaration: `export const name = (params) => { body };`. -/
def JsFun.toMini (f : JsFun) : MiniModuleItem :=
  let params := f.params.map fun x => MiniParam.plain (.ident (nes x))
  let body : MiniArrowBody := match f.body with
    | [.ret e] => .expr (exprToMini {} e)
    | _ => .block (stmtsToMini {} f.body)
  .exportDecl (.decl (.decl .const ⟨⟨.ident (nes f.name), some (.arrow false params body)⟩, []⟩))

/-- The import of the functions `names` of the runtime module `path`:
    `import { a, b } from "path";`. -/
def importToMini (path : String) (names : List String) : MiniModuleItem :=
  if names.isEmpty then .stmt .empty else
  .importDecl (.clause (MiniImportClause.mk none none
    (some (names.map fun n => Specifier.mk (nes n) none)) (nes path) [] (Or.inr (Or.inr rfl))))

/-- A constant shared by the functions of a module: `const name = e;`. -/
def constToMini (name : String) (e : JsExpr) : MiniModuleItem :=
  .stmt (.decl .const ⟨⟨.ident (nes name), some (exprToMini {} e)⟩, []⟩)

/-- The comment above an exported function: its Lean name, and the layouts of its
    parameters and result. -/
def JsFun.docComment (f : JsFun) : String :=
  let ps := (f.params.zip f.paramTys).map fun (x, ty) => s!" * @param \{{ty}} {x}"
  "\n".intercalate (["/**", s!" * `{f.leanName}`"] ++ ps ++ [s!" * @returns \{{f.ret}}", " */"])

/-- The text of the `.js` file of a module.  `header` are comment lines put first;
    `runtimeDir` is how the module refers to the directory of the runtime modules (a path
    relative to the module, `../../runtime`). -/
def JsModule.toJs (m : JsModule) (header : List String) (runtimeDir : String) : String :=
  let head := String.join (header.map fun l => s!"// {l}\n")
  let imports := RtFile.all.filterMap fun f =>
    let ns := (m.imports.filter (·.file == f)).map (·.name)
    if ns.isEmpty then none else some (importToMini s!"{runtimeDir}/{f.fileName}" ns)
  let importsTxt := if imports.isEmpty then "" else printProgram ⟨imports⟩ ++ "\n"
  let constsTxt := if m.consts.isEmpty then "" else
    printProgram ⟨m.consts.map fun (x, e) => constToMini x e⟩ ++ "\n"
  let funs := m.funs.map fun f =>
    f.docComment ++ "\n" ++ printProgram ⟨[f.toMini]⟩
  head ++ "\n" ++ importsTxt ++ constsTxt ++ "\n".intercalate funs

end MoreJs
