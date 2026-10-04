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

/-- The name recorded for the value of a join point that the statements after it do not
    read (`let x;` is not written, and a jump to it assigns nothing). -/
def unreadJoinVar : String := "$unread"

/-- The printer's counters: of the names of the local variables and of the labels, which it
    chooses (`x$1`, `acc$2`, … from the hints of the binders; `j$1`, `j$2`, … for the labels).
    A name is never met twice in a function, so no name ever hides another. -/
structure PrintSt where
  names : Nat := 1
  labels : Nat := 1
  /-- The names without a counter in use in the function: its parameters and the names
      `niceName` gave (every name `freshName` gives has a `$`, so it is never one of them). -/
  taken : List String := []
  /-- The names of the module (its functions, the runtime functions it imports, its own
      helpers), which a local name must not hide. -/
  globals : List String := []

/-- The printer. -/
abbrev PM := StateM PrintSt

/-- A new name, from the hint of a binder: `hint$k`. -/
def freshName (hint : String) : PM String :=
  modifyGet fun s => (s!"{hint}${s.names}", { s with names := s.names + 1 })

/-- The reserved words of JavaScript and the global names the printed code may read (the
    templates of the inlined operations call `BigInt`, `Math`, `Number`, `String`; a `throw`
    builds an `Error`): a local name is never one of them. -/
def jsReservedNames : List String :=
  ["await", "break", "case", "catch", "class", "const", "continue", "debugger", "default",
   "delete", "do", "else", "enum", "export", "extends", "false", "finally", "for",
   "function", "if", "implements", "import", "in", "instanceof", "interface", "let", "new",
   "null", "package", "private", "protected", "public", "return", "static", "super",
   "switch", "this", "throw", "true", "try", "typeof", "var", "void", "while", "with",
   "yield", "async", "of", "get", "set", "arguments", "eval", "undefined", "NaN", "Infinity",
   "globalThis", "BigInt", "Math", "Number", "String", "Error", "Array", "Object", "Symbol",
   "JSON", "Boolean", "Date", "RegExp", "Map", "Set", "Promise", "Reflect", "Proxy",
   "isNaN", "isFinite", "parseInt", "parseFloat", "console", "require", "module",
   "exports"]

/-- A name made of ASCII letters and digits, starting with a letter. -/
def isPlainName (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha && c.toNat < 128) && cs.all fun c => c.isAlphanum && c.toNat < 128
  | [] => false

/-- A new name from a hint, written without a counter when the hint is a plain name that is
    free (not a parameter or another name given so, not a name of the module, not reserved),
    otherwise `freshName hint`.  Either way no name of the function hides another, or a name
    of the module or of JavaScript. -/
def niceName (hint : String) : PM String := do
  let s ← get
  if isPlainName hint && hint.length ≤ 16 && !s.taken.contains hint &&
      !s.globals.contains hint && !jsReservedNames.contains hint then
    set { s with taken := hint :: s.taken }
    return hint
  else freshName hint

/-- The name of a local variable written without a counter (a parameter, or a name `niceName`
    gave), when the expression is one. -/
def plainLocal? : MiniExpr → PM (Option String)
  | .ident x => do return if (← get).taken.contains x.toString then some x.toString else none
  | _ => pure none

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
    `break`, `continue`), `else if` for an `else` that is a single `if`, and one test
    `if (c && b) { … }` for an `if` whose only statement is an `if`, neither with an `else`. -/
def mkIf (c : MiniExpr) (t e : List MiniStatement) : List MiniStatement :=
  match t, e with
  -- `if (c) { if (b) { s } }` is `if (c && b) { s }` (`b` is evaluated exactly when it was)
  | [.if_ b s none], [] => [.if_ (.binary c .and b) s none]
  | [], [.if_ b s none] => [.if_ (andNot c b) s none]
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
  /-- `!c && b`, just `b` when `b` implies `!c`: `x === l₁` and `x === l₂` for two different
      literals that are non-negative integers or strings (two different such literals are
      two different values). -/
  andNot (c b : MiniExpr) : MiniExpr :=
    let distinctLits (l₁ l₂ : MiniExpr) : Bool := l₁ != l₂ && match l₁, l₂ with
      | .number (.decimal _ 0), .number (.decimal _ 0) => true
      | .string _, .string _ => true
      | _, _ => false
    match c, b with
    | .binary x .strictEq l₁, .binary y .strictEq l₂ =>
      if x == y && distinctLits l₁ l₂ then b else .binary (negateCond c) .and b
    | _, _ => .binary (negateCond c) .and b
  /-- An `else`: a single `if` as it is (`else if`), otherwise a block. -/
  asStmt' : List MiniStatement → MiniStatement
    | [s@(.if_ ..)] => s
    | ss => .block ss

/-- The names a condition without effect reads (names, literals and fields, compared, negated
    and joined by `&&` and `||`), or `none` for any other expression. -/
partial def pureCondNames? : MiniExpr → Option (List NonEmptyString)
  | .ident x => some [x]
  | .number _ | .string _ | .true_ | .false_ | .null => some []
  | .dot e _ => pureCondNames? e
  | .unary .not e | .unary .minus e => pureCondNames? e
  | .binary a op b =>
    match op with
    | .strictEq | .strictNeq | .lt | .le | .gt | .ge | .and | .or => do
      return (← pureCondNames? a) ++ (← pureCondNames? b)
    | _ => none
  | _ => none

/-- `const { _1: a, … } = s;` followed by `if (c) { S }` alone (no `else`, nothing after it),
    with `c` a condition without effect that reads none of the names of the pattern (and `s` a
    name or a field), is `if (c) { const { _1: a, … } = s; S }`: the fields are then only read
    on the path that uses them, and the `if` can be merged with a test around it
    (`if (s.tag === 1 && c) { … }`, `mkIf`).  Reading fields has no effect, so reading them
    after `c`, or not at all when `c` is false, changes nothing. -/
def sinkPattern (d b : List MiniStatement) : List MiniStatement :=
  match d, b with
  | [dd@(.decl .const ⟨⟨.object props none, some src⟩, []⟩)], [.if_ c s none] =>
    let names := props.filterMap fun p => match p.value with
      | .ident x => some x
      | _ => none
    let body := match s with
      | .block ss => ss
      | s => [s]
    match pureCondNames? c with
    | some ns =>
      if isSimpleMini src && names.length == props.length && !ns.any names.contains then
        [.if_ c (.block (dd :: body)) none]
      else d ++ b
    | none => d ++ b
  | _, _ => d ++ b

/-- The chain `if (t₀) { b₀ } else if (t₁) { b₁ } … else { bₙ }` of the arms of a case
    analysis (the last arm needs no test), written as short as it can be (`mkIf`). -/
def ifChain : List (MiniExpr × List MiniStatement) → List MiniStatement
  | [] => [.throw (.new (ident "Error") [.string "LeanScript: an empty case analysis"])]
  | [(_, b)] => b
  | (t, b) :: rest => mkIf t b (ifChain rest)

/-- The chain of the arms of a case analysis, each with its test and its key (the dump of the
    arm: two arms of the same key are the same statements), the arms of the same key written
    once, under one test `t₀ || t₂`.  The arms written last, without a test, are the most
    frequent ones (on a tie, those whose statements are empty, a jump to the end of the block
    of a join point; then the last ones). -/
def groupedChain (arms : List ((MiniExpr × List MiniStatement) × String)) : List MiniStatement :=
  -- the groups, in the order of their first arm: the key, the tests, the statements
  let groups : Array (String × Array MiniExpr × List MiniStatement) :=
    arms.foldl (fun acc ((t, b), key) =>
      match acc.findIdx? (·.1 == key) with
      | some i => acc.modify i fun (k, ts, b') => (k, ts.push t, b')
      | none => acc.push (key, #[t], b)) #[]
  if groups.size ≤ 1 && arms.length ≥ 1 then (groups[0]?.map (·.2.2)).getD [] else
  if groups.size ≤ 1 then ifChain (arms.map (·.1)) else
  let score (i : Nat) : Nat × Nat × Nat :=
    let g := groups[i]!
    (g.2.1.size, if g.2.2.isEmpty then 1 else 0, i)
  let better (a b : Nat × Nat × Nat) : Bool :=
    a.1 > b.1 || (a.1 == b.1 && (a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.2.2 > b.2.2)))
  let dflt := (List.range groups.size).foldl
    (fun best i => if better (score i) (score best) then i else best) 0
  let tested := (groups.toList.zipIdx.filter (·.2 != dflt)).map fun ((_, ts, b), _) =>
    ((ts.toList.tail.foldl (fun acc t => .binary acc .or t) ts[0]!), b)
  ifChain (tested ++ [(.true_, groups[dflt]!.2.2)])

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
  | .countdown _ _ _ _ _ r => r.earlyNext tail
  | .forExit _ _ _ _ _ r => r.earlyNext tail
  | .tick _ _ b r | .natCase _ _ _ b r => b.earlyNext false || r.earlyNext tail
  | .ret _ | .jump _ _ | .throw _ | .raise _ => false
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
  | .countdown _ _ _ _ _ r => r.earlyJump i tail
  | .forExit _ _ _ _ _ r => r.earlyJump i tail
  | .tick _ _ b r | .natCase _ _ _ b r => b.earlyJump i false || r.earlyJump i tail
  | .ret _ | .next | .throw _ | .raise _ => false
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

/-! ## Hash maps with string keys -/

/-- Can the string be written after a dot (`m.k`): an identifier name (a reserved word is one,
    `m.class` is valid)? -/
def isIdentName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    let start (c : Char) : Bool := c.isAlpha || c == '_' || c == '$'
    start c && cs.all fun c => start c || c.isDigit

/-- The property `k` of the object `m`: `m.k` when the key is a string literal that is an
    identifier name, `m[k]` otherwise. -/
def strMapProp (m k : MiniExpr) (lit : Option String) : MiniExpr :=
  match lit with
  | some s => if isIdentName s then .dot m (nes s) else .index m k
  | none => .index m k

/-- `Object.f(args)`. -/
def objectCall (f : String) (args : List MiniExpr) : MiniExpr :=
  .call (.dot (ident "Object") (nes f)) args

/-- The JavaScript of an operation on a hash map with string keys that is written inline
    (`JsStrMapOp.inline`), on the JavaScript of its arguments `es` (`infos`: whether each is an
    atom, and the string of a string literal); `N` is the representation of a natural number
    (the answer of `size`). -/
def strMapInlineToMini (op : JsStrMapOp) (N : JsTy) (es : List MiniExpr)
    (infos : List (Bool × Option String)) : MiniExpr :=
  let e (i : Nat) : MiniExpr := es.getD i (ident "undefined")
  let lit (i : Nat) : Option String := infos[i]?.bind (·.2)
  let safe (i : Nat) : Bool := match lit i with
    | some s => !objectProtoNames.contains s
    | none => false
  -- the value of the key `k` of `m`, or the default `d`
  let lookup (mi ki di : Nat) : MiniExpr :=
    let p := strMapProp (e mi) (e ki) (lit ki)
    if safe ki then .binary p .coalesce (e di)
    else .ternary (objectCall "hasOwn" [e mi, e ki]) p (e di)
  let length : MiniExpr := .dot (objectCall "keys" [e 0]) (nes "length")
  match op with
  | .getBang => lookup 1 2 0
  | .getD => lookup 0 1 2
  | .contains => objectCall "hasOwn" [e 0, e 1]
  | .emptyWithCapacity => .object []
  | .insert =>
    let key : MiniPropertyName := match lit 1 with
      | some s => if isIdentName s && s != "__proto__" then .ident (nes s) else .computed (e 1)
      | none => .computed (e 1)
    .object [.spread (e 0), .keyValue key (e 2)]
  | .size => if N == .terminal .bigint_nat then .call (ident "BigInt") [length] else length
  | .isEmpty => .binary length .strictEq (natNum 0)
  | .keys | .keysArray => objectCall "keys" [e 0]
  | .values | .valuesArray => objectCall "values" [e 0]
  | _ => .call (ident op.runtimeName) es

end MoreJs
