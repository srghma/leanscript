import JsTerm.Vars
import LanguageJavascriptMini.Printer

/-!
# Printing the JavaScript grammar with `LanguageJavascriptMini`

`MoreJs.JsModule.toJs m` is the text of the `.js` file of a module: a header comment, the
import of the runtime functions the module calls (`import { … } from "…/runtime.js";`), the
constants its functions share (`const $tag0 = { tag: 0 };`), and the exported functions, all
converted to the JavaScript syntax tree of `LanguageJavascriptMini` (`MiniAST`) and printed by
its printer (prettier's style: two space indentation, double quotes, semicolons, 80 columns).

(This file is not a `module`: `LanguageJavascriptMini` is not written in the module
system, and a module cannot import a file that is not one.)

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

/-- A non-empty string (the grammar never produces an empty name). -/
def nes (s : String) : NonEmptyString :=
  (NonEmptyString.fromString? s).getD ⟨"_", by decide⟩

/-- An identifier. -/
def ident (s : String) : MiniExpr := .ident (nes s)

/-- A dotted global name as an expression: `Uint8Array.from`. -/
def dotted (s : String) : MiniExpr :=
  match s.splitOn "." with
  | [] => ident s
  | x :: xs => xs.foldl (fun e m => .dot e (nes m)) (ident x)

/-- A non-negative integer as a numeric literal. -/
def natNum (n : Nat) : MiniExpr := .number (.decimal n 0)

/-- An integer, with a unary minus when it is negative. -/
def intNum (n : Int) : MiniExpr :=
  if n < 0 then .unary .minus (natNum n.natAbs) else natNum n.natAbs

/-- A `BigInt` literal. -/
def bigintNum (n : Int) : MiniExpr :=
  let b : MiniExpr := .number (.bigint .decimal n.natAbs)
  if n < 0 then .unary .minus b else b

/-- A `number` literal. -/
def numberExpr : NumberForm → MiniExpr
  | .nan => ident "NaN"
  | .infinity neg => if neg then .unary .minus (ident "Infinity") else ident "Infinity"
  | .negZero => .unary .minus (natNum 0)
  | .int n => intNum n
  | .decimal neg d ex =>
    let num : MiniExpr := .number (.decimal d ex)
    if neg then .unary .minus num else num

/-- A literal, by its shape. -/
partial def shapeExpr : JsLitShape → MiniExpr
  | .bool true => .true_
  | .bool false => .false_
  | .number f => numberExpr f
  | .bigint n => bigintNum n
  | .str s => .string s
  | .array es => .array (es.map fun e => .elem (shapeExpr e))

/-- The binary operator of the syntax tree written `op`. -/
def binOpOf? : String → Option BinOp
  | "+" => some .plus | "-" => some .minus | "*" => some .times | "/" => some .divide
  | "%" => some .mod | "<" => some .lt | "<=" => some .le | ">" => some .gt | ">=" => some .ge
  | "===" => some .strictEq | "!==" => some .strictNeq | "&" => some .bitAnd
  | "|" => some .bitOr | "^" => some .bitXor | "<<" => some .lsh | ">>" => some .rsh
  | ">>>" => some .ursh | "&&" => some .and | "||" => some .or
  | _ => none

/-- The prefix operator of the syntax tree written `op`. -/
def unOpOf : String → UnaryOp
  | "~" => .tilde | "!" => .not | "+" => .plus
  | _ => .minus

/-- The template of an inlined operation, over its (printed) arguments. -/
partial def inlineToMini (args : Array MiniExpr) : JsInline → MiniExpr
  | .arg i => args.getD i (ident "undefined")
  | .bin op a b =>
    let a := inlineToMini args a
    let b := inlineToMini args b
    match binOpOf? op with
    | some o => .binary a o b
    | none => .call (ident "undefined") [a, b]
  | .un op a => .unary (unOpOf op) (inlineToMini args a)
  | .call f as => .call (dotted f) (as.map (inlineToMini args))
  | .new c as => .new (dotted c) (as.map (inlineToMini args))
  | .num n => intNum n
  | .big n => bigintNum n
  | .emptyArray => .array []
  | .member a f => .dot (inlineToMini args a) (nes f)

/-- How the end of an iteration (`next`) is written where it is not the end of the body. -/
inductive LoopExit where
  /-- Not in the body of a loop. -/
  | none
  /-- `continue;`. -/
  | cont
  /-- `break label;` (the last iteration only, a labelled `if`). -/
  | brk (label : String)

/-- The names of the variables in scope where the statements are printed: the constants and
    the mutable variables (innermost first, as the de Bruijn indices count), the join points
    around them (innermost first, each as its label and the name of its variable), and how an
    iteration of the enclosing loop ends. -/
structure Scope where
  c : List String := []
  m : List String := []
  joins : List (String × String) := []
  loop : LoopExit := .none

/-- Where a block ends: at the end of the body of a loop (a `next` there is nothing), at the
    end of the labelled block of the innermost join point (a jump to it needs no `break`). -/
structure Tail where
  loop : Bool := false
  join : Bool := false

/-- The printer's counters: of the names of the local variables and of the labels, which it
    chooses (`x$1`, `acc$2`, … from the hints of the binders; `j$1`, `j$2`, … for the labels).
    A name is never met twice in a function, so no name ever hides another. -/
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

/-- The name of a variable (`undefined` for an index out of scope, which a well-typed body
    never has). -/
def nameAt (names : List String) (i : Nat) : MiniExpr := ident (names.getD i "undefined")

/-- `const x = e;`. -/
def constDecl (x : String) (e : MiniExpr) : MiniStatement :=
  .decl .const ⟨⟨.ident (nes x), some e⟩, []⟩

/-- A statement from a list of them. -/
def asStmt : List MiniStatement → MiniStatement
  | [s] => s
  | ss => .block ss

/-- The chain `if (t₀) { b₀ } else if (t₁) { b₁ } … else { bₙ }` of the arms of a case
    analysis (the last arm needs no test). -/
def ifChain : List (MiniExpr × List MiniStatement) → List MiniStatement
  | [] => [.throw (.new (ident "Error") [.string "LeanScript: an empty case analysis"])]
  | [(_, b)] => b
  | (t, b) :: rest =>
    let els := match ifChain rest with
      | [s@(.if_ ..)] => s
      | ss => .block ss
    [.if_ t (.block b) (some els)]

/-! ## Where an iteration ends early -/

mutual
/-- Does an iteration of the block end (`next`) somewhere other than at its end (`tail`
    says whether the end of the block is the end of the iteration)? -/
partial def JsBlock.earlyNext {C M J : List JsTy} {k : JsEnd} (tail : Bool) :
    JsBlock C M J k → Bool
  | .next => !tail
  | .const _ _ r | .letMut _ _ r | .assign _ _ r | .destructure _ _ r => r.earlyNext tail
  | .ite _ t e => t.earlyNext tail || e.earlyNext tail
  | .enumCases _ arms => arms.earlyNext tail
  | .unionCases _ arms => arms.earlyNext tail
  | .join _ b r => b.earlyNext false || r.earlyNext tail
  | .forRange _ _ _ _ r | .lastIter _ _ _ _ r | .forOf _ _ _ _ r => r.earlyNext tail
  | .ret _ | .jump _ _ | .throw _ => false
/-- `earlyNext` of the arms of an enum's case analysis. -/
partial def JsEnumArms.earlyNext {C M J : List JsTy} {k : JsEnd} {n : Nat} (tail : Bool) :
    JsEnumArms C M J k n → Bool
  | .nil => false
  | .cons b rest => b.earlyNext tail || rest.earlyNext tail
/-- `earlyNext` of the arms of a union's case analysis. -/
partial def JsUnionArms.earlyNext {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (tail : Bool) : JsUnionArms C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.earlyNext tail || rest.earlyNext tail
end

mutual
/-- Does the block jump to the join point of index `i` somewhere other than at its end (`tail`
    says whether the end of the block is the end of the labelled block of that join point)? -/
partial def JsBlock.earlyJump {C M J : List JsTy} {k : JsEnd} (i : Nat) (tail : Bool) :
    JsBlock C M J k → Bool
  | .jump j _ => j.index == i && !tail
  | .const _ _ r | .letMut _ _ r | .assign _ _ r | .destructure _ _ r => r.earlyJump i tail
  | .ite _ t e => t.earlyJump i tail || e.earlyJump i tail
  | .enumCases _ arms => arms.earlyJump i tail
  | .unionCases _ arms => arms.earlyJump i tail
  | .join _ b r => b.earlyJump (i + 1) false || r.earlyJump i tail
  | .forRange _ _ _ _ r | .lastIter _ _ _ _ r | .forOf _ _ _ _ r => r.earlyJump i tail
  | .ret _ | .next | .throw _ => false
/-- `earlyJump` of the arms of an enum's case analysis. -/
partial def JsEnumArms.earlyJump {C M J : List JsTy} {k : JsEnd} {n : Nat} (i : Nat)
    (tail : Bool) : JsEnumArms C M J k n → Bool
  | .nil => false
  | .cons b rest => b.earlyJump i tail || rest.earlyJump i tail
/-- `earlyJump` of the arms of a union's case analysis. -/
partial def JsUnionArms.earlyJump {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (i : Nat) (tail : Bool) : JsUnionArms C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.earlyJump i tail || rest.earlyJump i tail
end

/-! ## The conversion -/

/-- The literal `0` of a counter (`0n` for a `BigInt`). -/
def natLitOf {N : JsTy} (nt : JsNatTy N) (n : Nat) : MiniExpr :=
  match nt with
  | .bigint_nat => bigintNum n
  | .uint53 => natNum n

mutual
/-- An expression as a `MiniAST` expression. -/
partial def exprToMini {C M : List JsTy} {τ : JsTy} (sc : Scope) : JsExpr C M τ → PM MiniExpr
  | .cvar x => pure (nameAt sc.c x.index)
  | .mvar x => pure (nameAt sc.m x.index)
  | .global n _ => pure (ident n)
  | .lit l => pure (shapeExpr l.shape)
  | .imported op args => do
    return .call (ident op.runtimeName) (op.extraArgs.map dotted ++ (← argsToMini sc args))
  | .inlined op args => do return inlineToMini (← argsToMini sc args).toArray op.template
  | .unreachable _ => pure (ident "undefined")
  | .app f as => do return .call (← exprToMini sc f) (← argsToMini sc as)
  | .lam (σs := σs) hints body => do
    let xs ← (List.range σs.length).mapM fun i => freshName (hints.getD i "x")
    -- a function starts afresh: no jump leaves it, and it is no iteration of a loop
    arrowToMini { c := xs.reverse ++ sc.c, m := sc.m } xs body
  | .record_mk fs => do
    let es ← argsToMini sc fs
    return .object (es.zipIdx.map fun (e, i) => .keyValue (.ident (nes (fieldKey i))) e)
  | .union_mk ix args => do
    let es ← argsToMini sc args
    return .object (.keyValue (.ident (nes "tag")) (natNum ix.index) ::
      es.zipIdx.map fun (e, i) => .keyValue (.ident (nes (fieldKey i))) e)
  | .enum_mk _ shift i => pure (intNum (shift + i.val))
  | .array_mk (.generic _) ps => do return .array ((← partsToMini sc ps).map .elem)
  | .array_mk (.typed t) ps => do
    return .call (.dot (ident t.kind.ctorName) (nes "of")) (← partsToMini sc ps)
  | .list_mk ps => do return .array ((← partsToMini sc ps).map .elem)
  | .cond c a b => do
    return .ternary (← exprToMini sc c) (← exprToMini sc a) (← exprToMini sc b)

/-- An arrow function of parameters `ps` (already in `sc`). -/
partial def arrowToMini {C M : List JsTy} {τ : JsTy} (sc : Scope) (ps : List String)
    (body : JsBlock C M [] (.ret τ)) : PM MiniExpr := do
  let params := ps.map fun p => MiniParam.plain (.ident (nes p))
  match body with
  | .ret e => return .arrow false params (.expr (← exprToMini sc e))
  | _ => return .arrow false params (.block (← blockToMini sc {} body))

/-- Arguments. -/
partial def argsToMini {C M σs : List JsTy} (sc : Scope) : JsArgs C M σs → PM (List MiniExpr)
  | .nil => pure []
  | .cons a as => do return (← exprToMini sc a) :: (← argsToMini sc as)

/-- The parts of an array literal (a spread `...a`). -/
partial def partsToMini {C M : List JsTy} {A E : JsTy} (sc : Scope) :
    JsParts C M A E → PM (List MiniExpr)
  | .nil => pure []
  | .elem e rest => do return (← exprToMini sc e) :: (← partsToMini sc rest)
  | .spread a rest => do return .spread (← exprToMini sc a) :: (← partsToMini sc rest)

/-- The subject of a case analysis or the bound of a loop: itself when it is an atom,
    otherwise a new constant (`const s$k = e;`) holding it. -/
partial def bindSubject {C M : List JsTy} {τ : JsTy} (sc : Scope) (hint : String)
    (e : JsExpr C M τ) : PM (List MiniStatement × MiniExpr) := do
  let m ← exprToMini sc e
  if e.isAtom then return ([], m) else
  let s ← freshName hint
  return ([constDecl s m], ident s)

/-- A block as `MiniAST` statements. -/
partial def blockToMini {C M J : List JsTy} {k : JsEnd} (sc : Scope) (tl : Tail) :
    JsBlock C M J k → PM (List MiniStatement)
  | .ret e => do return [.return_ (some (← exprToMini sc e))]
  | .next =>
    if tl.loop then pure [] else
    match sc.loop with
    | .cont => pure [.continue_ none]
    | .brk l => pure [.break_ (some (nes l))]
    | .none => pure []
  | .jump j e => do
    let e ← exprToMini sc e
    match sc.joins[j.index]? with
    | some (label, x) =>
      let set : MiniStatement := .expr (.assign (ident x) .assign e)
      if j.index == 0 && tl.join then return [set]
      else return [set, .break_ (some (nes label))]
    | none =>
      return [.throw (.new (ident "Error") [.string s!"LeanScript: an unknown join point"])]
  | .throw msg => pure [.throw (.new (ident "Error") [.string msg])]
  | .const hint e rest => do
    let e ← exprToMini sc e
    let x ← freshName hint
    return constDecl x e :: (← blockToMini { sc with c := x :: sc.c } tl rest)
  | .letMut hint e rest => do
    let e ← exprToMini sc e
    let x ← freshName hint
    return .decl .let_ ⟨⟨.ident (nes x), some e⟩, []⟩ ::
      (← blockToMini { sc with m := x :: sc.m } tl rest)
  | .assign x e rest => do
    let e ← exprToMini sc e
    return .expr (.assign (nameAt sc.m x.index) .assign e) :: (← blockToMini sc tl rest)
  | .destructure e sel rest => do
    let e ← exprToMini sc e
    let (d, sc') ← destructureToMini sc e sel.binds
    return d ++ (← blockToMini sc' tl rest)
  | .ite c t e => do
    let c ← exprToMini sc c
    let t ← blockToMini sc tl t
    let e ← blockToMini sc tl e
    let els := match e with
      | [s@(.if_ ..)] => s
      | ss => .block ss
    return [.if_ c (.block t) (some els)]
  | .enumCases (shift := shift) e arms => do
    let (pre, s) ← bindSubject sc "s" e
    let arms ← enumArmsToMini sc tl s shift 0 arms
    return pre ++ ifChain arms
  | .unionCases e arms => do
    let (pre, s) ← bindSubject sc "s" e
    let arms ← unionArmsToMini sc tl s 0 arms
    return pre ++ ifChain arms
  | .join hint block rest => do
    let x ← freshName hint
    -- the labelled block is only needed when a jump leaves it before its end; otherwise its
    -- statements run on into `rest` (every name of a function is distinct)
    let early := block.earlyJump 0 true
    let label ← if early then freshLabel else pure ""
    let b ← blockToMini { sc with joins := (label, x) :: sc.joins } { join := true } block
    let r ← blockToMini { sc with c := x :: sc.c } tl rest
    let decl : MiniStatement := .decl .let_ ⟨⟨.ident (nes x), none⟩, []⟩
    if early then return decl :: .labelled (nes label) (.block b) :: r
    else return decl :: b ++ r
  | .forRange hint nt n body rest => do
    let (pre, n) ← bindSubject sc "n" n
    let i ← freshName hint
    let b ← blockToMini { c := i :: sc.c, m := sc.m, loop := .cont } { loop := true } body
    let r ← blockToMini sc tl rest
    return pre ++ .for_ (.decl .let_ ⟨⟨.ident (nes i), some (natLitOf nt 0)⟩, []⟩)
      (some (.binary (ident i) .lt n)) (some (.postfix (ident i) .incr)) (.block b) :: r
  | .lastIter hint nt n body rest => do
    let (pre, n) ← bindSubject sc "n" n
    let i ← freshName hint
    let early := body.earlyNext true
    let label ← if early then freshLabel else pure ""
    let b ← blockToMini { c := i :: sc.c, m := sc.m, loop := .brk label } { loop := true } body
    let r ← blockToMini sc tl rest
    let s : MiniStatement := .if_ (.binary (natLitOf nt 0) .lt n)
      (.block (constDecl i (.binary n .minus (natLitOf nt 1)) :: b)) none
    return pre ++ (if early then .labelled (nes label) s else s) :: r
  | .forOf hint _ xs body rest => do
    let xs ← exprToMini sc xs
    let x ← freshName hint
    let b ← blockToMini { c := x :: sc.c, m := sc.m, loop := .cont } { loop := true } body
    let r ← blockToMini sc tl rest
    return .forOf false (.decl .const (.ident (nes x))) xs (.block b) :: r

/-- `const { _1: a, _3: c } = e;` for the fields `binds` keeps (none when it keeps none), and
    the scope with them bound (the last one innermost). -/
partial def destructureToMini (sc : Scope) (e : MiniExpr) (binds : List (Nat × String)) :
    PM (List MiniStatement × Scope) := do
  if binds.isEmpty then return ([], sc) else
  let names ← binds.mapM fun (_, x) => freshName x
  let props := (binds.zip names).map fun ((i, _), x) =>
    MiniObjectPatternProp.mk (.ident (nes (fieldKey i))) (.ident (nes x))
  return ([.decl .const ⟨⟨.object props none, some e⟩, []⟩],
    { sc with c := names.reverse ++ sc.c })

/-- The arms of a case analysis on an enum, each with its test (`s === shift + i`). -/
partial def enumArmsToMini {C M J : List JsTy} {k : JsEnd} {n : Nat} (sc : Scope) (tl : Tail)
    (s : MiniExpr) (shift : Int) (i : Nat) :
    JsEnumArms C M J k n → PM (List (MiniExpr × List MiniStatement))
  | .nil => pure []
  | .cons b rest => do
    let b ← blockToMini sc tl b
    return (.binary s .strictEq (intNum (shift + i)), b) ::
      (← enumArmsToMini sc tl s shift (i + 1) rest)

/-- The arms of a case analysis on a union, each with its test (`s.tag === i`), taking the
    fields it uses apart. -/
partial def unionArmsToMini {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (sc : Scope)
    (tl : Tail) (s : MiniExpr) (i : Nat) :
    JsUnionArms C M J k cs → PM (List (MiniExpr × List MiniStatement))
  | .nil => pure []
  | .cons sel b rest => do
    let (d, sc') ← destructureToMini sc s sel.binds
    let b ← blockToMini sc' tl b
    return (.binary (.dot s (nes "tag")) .strictEq (natNum i), d ++ b) ::
      (← unionArmsToMini sc tl s (i + 1) rest)
end

/-! ## Functions and modules -/

/-- A function as an exported declaration: `export const name = (params) => { body };`. -/
def JsFun.toMini (f : JsFun) : MiniModuleItem :=
  let go : PM MiniModuleItem := do
    -- the parameters keep their names (a name met twice gets a fresh one)
    let params ← f.params.foldlM (fun (acc : Array String) (p, _) =>
      if acc.contains p then do return acc.push (← freshName p) else return acc.push p) #[]
    let sc : Scope := { c := params.toList.reverse }
    let e ← arrowToMini sc params.toList f.body
    return .exportDecl (.decl (.decl .const ⟨⟨.ident (nes f.name), some e⟩, []⟩))
  go.run' {}

/-- The import of the functions `names` of the runtime `path`:
    `import { a, b } from "path";`. -/
def importToMini (path : String) (names : List String) : MiniModuleItem :=
  if names.isEmpty then .stmt .empty else
  .importDecl (.clause (MiniImportClause.mk none none
    (some (names.map fun n => Specifier.mk (nes n) none)) (nes path) [] (Or.inr (Or.inr rfl))))

/-- A constant shared by the functions of a module: `const name = e;`. -/
def JsConst.toMini (c : JsConst) : MiniModuleItem :=
  .stmt (constDecl c.name ((exprToMini {} c.e).run' {}))

/-- The comment above an exported function: its Lean name, and the types of its parameters
    and result. -/
def JsFun.docComment (f : JsFun) : String :=
  let ps := f.params.map fun (x, ty) => s!" * @param \{{ty}} {x}"
  "\n".intercalate ([s!"/**", s!" * `{f.leanName}`"] ++ ps ++ [s!" * @returns \{{f.ret}}", " */"])

/-- The text of the `.js` file of a module.  `header` are comment lines put first; `runtime`
    is how the module refers to the runtime (a path relative to the module,
    `../../runtime.js`). -/
def JsModule.toJs (m : JsModule) (header : List String) (runtime : String) : String :=
  let head := String.join (header.map fun l => s!"// {l}\n")
  let importsTxt := if m.imports.isEmpty then "" else
    printProgram ⟨[importToMini runtime m.imports]⟩ ++ "\n"
  let constsTxt := if m.consts.isEmpty then "" else
    printProgram ⟨m.consts.map JsConst.toMini⟩ ++ "\n"
  let funs := m.funs.map fun f => f.docComment ++ "\n" ++ printProgram ⟨[f.toMini]⟩
  head ++ "\n" ++ importsTxt ++ constsTxt ++ "\n".intercalate funs

end MoreJs
