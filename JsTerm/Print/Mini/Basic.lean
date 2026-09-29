import JsTerm.Syntax.Vars
import JsTerm.Syntax.Pretty
import LanguageJavascriptMini.Printer

/-!
# Printing the JavaScript grammar: helpers, the printer's state, early ends of iterations

The pieces of `MoreJs.JsModule.toJs` (`JsTerm.Print.Mini`) that do not walk the grammar:
building `MiniAST` names, numbers, literals and inlined templates; the names in scope
(`Scope`) and the printer's counters (`PM`); and whether an iteration of a loop ends before
the end of its body (`JsBlock.earlyNext`), which decides how `next` is written.

(Not a `module`: `LanguageJavascriptMini` is not written in the module system.)
-/

namespace MoreJs

variable {S : JsSig}

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

/-- `-x` for a negative sign. -/
def withSign (s : Float.Model.UnpackedFloat.Sign) (x : MiniExpr) : MiniExpr :=
  match s with
  | .negative => .unary .minus x
  | .positive => x

/-- A `number` literal. -/
def numberExpr : NumberForm → MiniExpr
  | .int n => intNum n
  | .float .notANumber => ident "NaN"
  | .float (.infinity s) => withSign s (ident "Infinity")
  | .float (.zero s) => withSign s (natNum 0)
  | .float (.finite s m e _) => withSign s (.number (NumberForm.finiteDecimal m e))

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
  | "%" => some .mod | "**" => some .exp | "<" => some .lt | "<=" => some .le | ">" => some .gt
  | ">=" => some .ge
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
  c : List MiniExpr := []
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

/-- The expression a constant is printed as: its name, or the read of a field (`x._1`) it
    stands for (`undefined` for an index out of scope). -/
def exprAt (es : List MiniExpr) (i : Nat) : MiniExpr := es.getD i (ident "undefined")

/-- `const x = e;`. -/
def constDecl (x : String) (e : MiniExpr) : MiniStatement :=
  .decl .const ⟨⟨.ident (nes x), some e⟩, []⟩

/-- A statement from a list of them. -/
def asStmt : List MiniStatement → MiniStatement
  | [s] => s
  | ss => .block ss

/-- How many times the statements assign the variable of a join point `x` (`x = e;`, possibly
    in an `if` or a block: the only statements a jump to it is written in). -/
partial def assignsTo (x : String) (ss : List MiniStatement) : Nat :=
  ss.foldl (fun n s => n + go s) 0
where
  /-- In one statement. -/
  go : MiniStatement → Nat
    | .expr (.assign (.ident y) _ _) => if y == nes x then 1 else 0
    | .if_ _ t e => go t + (e.map go).getD 0
    | .block ss => assignsTo x ss
    | .labelled _ s => go s
    | _ => 0

/-- The negation of a condition: `a !== b` for `a === b`, `c` for `!c`, `!c` otherwise. -/
def negateCond : MiniExpr → MiniExpr
  | .binary a .strictEq b => .binary a .strictNeq b
  | .binary a .strictNeq b => .binary a .strictEq b
  | .unary .not c => c
  | .true_ => .false_
  | .false_ => .true_
  | c => .unary .not c

/-- Is the expression short enough to be an arm of `c ? a : b` (a name, a literal, a field)? -/
def isSimpleMini : MiniExpr → Bool
  | .ident _ | .number _ | .string _ | .true_ | .false_ | .null => true
  | .dot e _ => isSimpleMini e
  | .unary .minus e => isSimpleMini e
  | _ => false

/-- Does evaluating the condition have no effect (a comparison of names, literals and
    fields)? -/
def isPureCond : MiniExpr → Bool
  | .binary a op b =>
    isSimpleMini a && isSimpleMini b &&
      (match op with | .strictEq | .strictNeq | .lt | .le | .gt | .ge => true | _ => false)
  | .unary .not c => isPureCond c
  | c => isSimpleMini c

/-- `if (c) { t } else { e }`, written as short as it can be: no `else` when `e` is empty,
    `if (!c) { e }` when `t` is, `return c;` for `if (c) { return true; } else { return false; }`,
    `return c ? a : b;` when both arms return a name or a literal, nothing when both are
    empty and `c` has no effect, no `else` after a `then` that ends in a `return` (or `throw`,
    `break`, `continue`), and `else if` for an `else` that is a single `if`. -/
def mkIf (c : MiniExpr) (t e : List MiniStatement) : List MiniStatement :=
  match t, e with
  | [.return_ (some .true_)], [.return_ (some .false_)] => [.return_ (some c)]
  | [.return_ (some .false_)], [.return_ (some .true_)] => [.return_ (some (negateCond c))]
  | [.return_ (some a)], [.return_ (some b)] =>
    if isSimpleMini a && isSimpleMini b then [.return_ (some (.ternary c a b))]
    else .if_ c (.block t) none :: e
  | [], [] => if isPureCond c then [] else [.if_ c (.block []) none]
  | t, [] => [.if_ c (.block t) none]
  | [], e => [.if_ (negateCond c) (.block e) none]
  | t, e =>
    if endsAbruptly t then .if_ c (.block t) none :: e
    else [.if_ c (.block t) (some (asStmt' e))]
where
  /-- Does the block end in a `return`, `throw`, `break` or `continue` (so that an `else`
      after it is not needed: every name of a function is distinct)? -/
  endsAbruptly (ss : List MiniStatement) : Bool :=
    match ss.getLast? with
    | some (.return_ _) | some (.throw _) | some (.break_ _) | some (.continue_ _) => true
    | _ => false
  /-- An `else`: a single `if` as it is (`else if`), otherwise a block. -/
  asStmt' : List MiniStatement → MiniStatement
    | [s@(.if_ ..)] => s
    | ss => .block ss

/-- The chain `if (t₀) { b₀ } else if (t₁) { b₁ } … else { bₙ }` of the arms of a case
    analysis (the last arm needs no test), written as short as it can be (`mkIf`). -/
def ifChain : List (MiniExpr × List MiniStatement) → List MiniStatement
  | [] => [.throw (.new (ident "Error") [.string "LeanScript: an empty case analysis"])]
  | [(_, b)] => b
  | (t, b) :: rest => mkIf t b (ifChain rest)

/-! ## Where an iteration ends early -/

mutual
/-- Does an iteration of the block end (`next`) somewhere other than at its end (`tail`
    says whether the end of the block is the end of the iteration)? -/
partial def JsBlock.earlyNext {C M J : List JsTy} {k : JsEnd} (tail : Bool) :
    JsBlock S C M J k → Bool
  | .next => !tail
  | .const _ _ r | .letMut _ _ r | .assign _ _ r | .destructure _ _ r => r.earlyNext tail
  | .ite _ t e => t.earlyNext tail || e.earlyNext tail
  | .enumCases _ arms => arms.earlyNext tail
  | .unionCases _ arms => arms.earlyNext tail
  | .join _ b r => b.earlyNext false || r.earlyNext tail
  | .forRange _ _ _ _ r | .forOf _ _ _ _ r | .funs _ _ r => r.earlyNext tail
  | .ret _ | .jump _ _ | .throw _ => false
/-- `earlyNext` of the arms of an enum's case analysis. -/
partial def JsEnumArms.earlyNext {C M J : List JsTy} {k : JsEnd} {n : Nat} (tail : Bool) :
    JsEnumArms S C M J k n → Bool
  | .nil => false
  | .cons b rest => b.earlyNext tail || rest.earlyNext tail
/-- `earlyNext` of the arms of a union's case analysis. -/
partial def JsUnionArms.earlyNext {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (tail : Bool) : JsUnionArms S C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.earlyNext tail || rest.earlyNext tail
end

mutual
/-- Does the block jump to the join point of index `i` somewhere other than at its end (`tail`
    says whether the end of the block is the end of the labelled block of that join point)? -/
partial def JsBlock.earlyJump {C M J : List JsTy} {k : JsEnd} (i : Nat) (tail : Bool) :
    JsBlock S C M J k → Bool
  | .jump j _ => j.index == i && !tail
  | .const _ _ r | .letMut _ _ r | .assign _ _ r | .destructure _ _ r => r.earlyJump i tail
  | .ite _ t e => t.earlyJump i tail || e.earlyJump i tail
  | .enumCases _ arms => arms.earlyJump i tail
  | .unionCases _ arms => arms.earlyJump i tail
  | .join _ b r => b.earlyJump (i + 1) false || r.earlyJump i tail
  | .forRange _ _ _ _ r | .forOf _ _ _ _ r | .funs _ _ r => r.earlyJump i tail
  | .ret _ | .next | .throw _ => false
/-- `earlyJump` of the arms of an enum's case analysis. -/
partial def JsEnumArms.earlyJump {C M J : List JsTy} {k : JsEnd} {n : Nat} (i : Nat)
    (tail : Bool) : JsEnumArms S C M J k n → Bool
  | .nil => false
  | .cons b rest => b.earlyJump i tail || rest.earlyJump i tail
/-- `earlyJump` of the arms of a union's case analysis. -/
partial def JsUnionArms.earlyJump {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (i : Nat) (tail : Bool) : JsUnionArms S C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.earlyJump i tail || rest.earlyJump i tail
end

end MoreJs
