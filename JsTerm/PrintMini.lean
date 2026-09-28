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

The variables of the grammar are de Bruijn indices; the printer names them, from the hints
of their binders: `x$1`, `acc$2`, … (a counter per function, so that no name hides another),
and the parameters of an exported function keep their names.

The mapping is direct: a `const`/`let` is a declaration, a destructuring `const [a, , b] = e`
an array pattern, a counting loop a `for (let i = 0n; i < n; i++)`, an arrow whose body is a
single `return e` is printed `(x) => e`, and an `if` whose `else` branch is a single `if`
is printed `else if`.  A join point `join m block` is the **labelled block** `j$k: { … }`
(`k` counting the join points of the function, so nested blocks have different labels) and a
jump of de Bruijn index `i` is `x = e; break j$k;` for the variable (the mutable variable `m`
of the join point) and the label of the `i`-th enclosing block.  An exported function is
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

/-- The names of the variables in scope where the statements are printed: the constants and
    the mutable variables (innermost first, as the de Bruijn indices count), and the join
    points around them (innermost first, each as its label and the name of its variable). -/
structure Scope where
  c : List String := []
  m : List String := []
  joins : List (String × String) := []

/-- The printer's counters: of the names of the local variables and of the labels, which it
    chooses (`x$1`, `acc$2`, …, from the hints of the binders; `j$1`, `j$2`, … for the labels
    of the join points).  A name of a function's variables is never met twice, so no name
    ever hides another. -/
structure PrintSt where
  names : Nat := 1
  labels : Nat := 1

/-- The printer. -/
abbrev PM := StateM PrintSt

/-- A new name, from the hint of a binder: `hint$k`. -/
def freshName (hint : String) : PM String :=
  modifyGet fun s => (s!"{hint}${s.names}", { s with names := s.names + 1 })

/-- A new label, `j$k`. -/
def freshLabel : PM String :=
  modifyGet fun s => (s!"j${s.labels}", { s with labels := s.labels + 1 })

/-- The name of a variable (`undefined` for an index out of scope, which a well-formed body
    never has). -/
def nameAt (names : List String) (i : Nat) : MiniExpr := ident (names.getD i "undefined")

mutual
/-- An expression as a `MiniAST` expression. -/
partial def exprToMini (sc : Scope) : JsExpr → PM MiniExpr
  | .cvar i => pure (nameAt sc.c i)
  | .mvar i => pure (nameAt sc.m i)
  | .global x => pure (ident x)
  | .lit l => pure (litExpr l)
  | .bin op a b => do
    let a ← exprToMini sc a
    let b ← exprToMini sc b
    return match binOp op with
      | some o => .binary a o b
      | none => .call (.dot (ident "Math") (nes "pow")) [a, b]
  | .un op a => return .unary (unOp op) (← exprToMini sc a)
  | .helper n args => return .call (ident n) (← args.mapM (exprToMini sc))
  | .call f args => return .call (← exprToMini sc f) (← args.mapM (exprToMini sc))
  | .arrow ps body => do
    let names ← ps.mapM freshName
    let params := names.map fun p => MiniParam.plain (.ident (nes p))
    -- a function starts afresh: no jump leaves it
    let sc' : Scope := { c := names.reverse ++ sc.c, m := sc.m, joins := [] }
    match body with
    | [.ret e] => return .arrow false params (.expr (← exprToMini sc' e))
    | _ => return .arrow false params (.block (← stmtsToMini sc' body))
  | .array es => return .array ((← es.mapM (exprToMini sc)).map .elem)
  | .typedArray k es => return .call (.dot (ident k) (nes "of")) (← es.mapM (exprToMini sc))
  | .index e i => return .index (← exprToMini sc e) (natNum i)
  | .member e n => return .dot (← exprToMini sc e) (nes n)
  | .cond k a b => return .ternary (← exprToMini sc k) (← exprToMini sc a) (← exprToMini sc b)
  | .object fs => return .object (← fs.mapM fun (k, e) => do
      return .keyValue (.ident (nes k)) (← exprToMini sc e))
  | .at e i => return .index (← exprToMini sc e) (← exprToMini sc i)
  | .new k args => return .new (← exprToMini sc k) (← args.mapM (exprToMini sc))
  | .spread e => return .spread (← exprToMini sc e)

/-- A statement as `MiniAST` statements (a jump is two: the assignment and the `break`), and
    the scope of the statements after it. -/
partial def stmtToMini (sc : Scope) : JsStmt → PM (List MiniStatement × Scope)
  | .const x e => do
    let e ← exprToMini sc e
    let n ← freshName x
    return ([.decl .const ⟨⟨.ident (nes n), some e⟩, []⟩], { sc with c := n :: sc.c })
  | .letMut x e => do
    let e ← e.mapM (exprToMini sc)
    let n ← freshName x
    return ([.decl .let_ ⟨⟨.ident (nes n), e⟩, []⟩], { sc with m := n :: sc.m })
  | .assign x e => do
    return ([.expr (.assign (nameAt sc.m x) .assign (← exprToMini sc e))], sc)
  | .destructure xs e => do
    let e ← exprToMini sc e
    let names ← xs.mapM fun x => x.mapM freshName
    let elems := names.map fun
      | some x => MiniArrayPatternElem.elem (.ident (nes x))
      | none => .hole
    -- trailing holes are dropped (`[a, ,]` is `[a]`)
    let elems := (elems.reverse.dropWhile fun | .hole => true | _ => false).reverse
    return ([.decl .const ⟨⟨.array elems, some e⟩, []⟩],
      { sc with c := (names.filterMap id).reverse ++ sc.c })
  | .destructureObj bs e => do
    let e ← exprToMini sc e
    let names ← bs.mapM fun (_, x) => freshName x
    let props := (bs.zip names).map fun ((k, _), x) =>
      MiniObjectPatternProp.mk (.ident (nes k)) (.ident (nes x))
    return ([.decl .const ⟨⟨.object props none, some e⟩, []⟩],
      { sc with c := names.reverse ++ sc.c })
  | .setMember o n e => do
    return ([.expr (.assign (.dot (← exprToMini sc o) (nes n)) .assign (← exprToMini sc e))], sc)
  | .setAt o i e => do
    let o ← exprToMini sc o
    let i ← exprToMini sc i
    return ([.expr (.assign (.index o i) .assign (← exprToMini sc e))], sc)
  | .expr e => do return ([.expr (← exprToMini sc e)], sc)
  | .while k body => do
    return ([.while_ (← exprToMini sc k) (.block (← stmtsToMini sc body))], sc)
  | .ret e => do return ([.return_ (some (← exprToMini sc e))], sc)
  | .ite k t e => do
    let k ← exprToMini sc k
    let t ← stmtsToMini sc t
    let els : Option MiniStatement ← match e with
      | [] => pure none
      | [s@(.ite ..)] => do
        match (← stmtToMini sc s).1 with
        | [m] => pure (some m)
        | ms => pure (some (.block ms))
      | ss => do pure (some (.block (← stmtsToMini sc ss)))
    return ([.if_ k (.block t) els], sc)
  | .forRange i big n body => do
    let n ← exprToMini sc n
    let x ← freshName i
    let zero : MiniExpr := if big then .number (.bigint .decimal 0) else natNum 0
    let body ← stmtsToMini { sc with c := x :: sc.c } body
    return ([.for_ (.decl .let_ ⟨⟨.ident (nes x), some zero⟩, []⟩)
      (some (.binary (ident x) .lt n))
      (some (.postfix (ident x) .incr)) (.block body)], sc)
  | .forOf x xs body => do
    let xs ← exprToMini sc xs
    let n ← freshName x
    let body ← stmtsToMini { sc with c := n :: sc.c } body
    return ([.forOf false (.decl .const (.ident (nes n))) xs (.block body)], sc)
  | .throw k msg => return ([.throw (.new (ident k) [.string msg])], sc)
  | .join x block => do
    let label ← freshLabel
    let v := sc.m.getD x "undefined"
    let block ← stmtsToMini { sc with joins := (label, v) :: sc.joins } block
    return ([.labelled (nes label) (.block block)], sc)
  | .jump j e => do
    let e ← exprToMini sc e
    match sc.joins[j]? with
    | some (label, x) =>
      return ([.expr (.assign (ident x) .assign e), .break_ (some (nes label))], sc)
    | none =>
      return ([.throw (.new (ident "Error")
        [.string s!"LeanScript: jump to an unknown join point {j}"])], sc)

/-- Statements, each in the scope the ones before it leave. -/
partial def stmtsToMini (sc : Scope) : List JsStmt → PM (List MiniStatement)
  | [] => pure []
  | s :: ss => do
    let (ms, sc') ← stmtToMini sc s
    return ms ++ (← stmtsToMini sc' ss)
end

/-- A function as an exported declaration: `export const name = (params) => { body };`. -/
def JsFun.toMini (f : JsFun) : MiniModuleItem :=
  let go : PM MiniModuleItem := do
    -- the parameters keep their names (a name met twice gets a fresh one)
    let params ← f.params.foldlM (fun (acc : Array String) p =>
      if acc.contains p then do return acc.push (← freshName p) else return acc.push p) #[]
    let sc : Scope := { c := params.toList.reverse }
    let ps := params.toList.map fun x => MiniParam.plain (.ident (nes x))
    let body : MiniArrowBody ← match f.body with
      | [.ret e] => do pure (.expr (← exprToMini sc e))
      | _ => do pure (.block (← stmtsToMini sc f.body))
    return .exportDecl (.decl (.decl .const ⟨⟨.ident (nes f.name), some (.arrow false ps body)⟩, []⟩))
  go.run' {}

/-- The import of the functions `names` of the runtime module `path`:
    `import { a, b } from "path";`. -/
def importToMini (path : String) (names : List String) : MiniModuleItem :=
  if names.isEmpty then .stmt .empty else
  .importDecl (.clause (MiniImportClause.mk none none
    (some (names.map fun n => Specifier.mk (nes n) none)) (nes path) [] (Or.inr (Or.inr rfl))))

/-- A constant shared by the functions of a module: `const name = e;`. -/
def constToMini (name : String) (e : JsExpr) : MiniModuleItem :=
  .stmt (.decl .const ⟨⟨.ident (nes name), some ((exprToMini {} e).run' {})⟩, []⟩)

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
