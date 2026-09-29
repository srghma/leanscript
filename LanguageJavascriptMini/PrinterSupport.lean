import LanguageJavascriptCommon.Doc
import LanguageJavascriptCommon.PrinterCommon
import LanguageJavascriptCommon.StringLit
import LanguageJavascriptMini.AST
import LanguageJavascriptMini.ASTOps
import LanguageJavascriptCommon.Unicode
import LanguageJavascriptMini.JSX
import LanguageJavascriptCommon.Options

open NonEmpty.String

/-!
# The printer: the tests it makes its decisions by

The part of the `MiniAST` printer which does not walk the tree: the
positions an expression may stand in, the parenthesisation and layout
tests read off a node, and the small documents built from a name or a
key.  `LanguageJavascriptMini.Printer` imports this module and adds the
mutually recursive printer proper.
-/

namespace Language.JavaScript.MiniAST

open Language.JavaScript.Doc
open Language.JavaScript.PrinterCommon
open Language.JavaScript.JSXLayout

namespace Printer

variable [o : Options]

/-! ## Operators -/

/-! ## Positions -/

/-- The syntactic position an expression is printed in.  It decides both
the parentheses the expression needs and, for a binary expression, how its
operator chain is laid out. -/
inductive Pos where
  /-- An expression statement. -/
  | statement
  /-- The condition of an `if`, `while`, `switch` or `do ... while`. -/
  | ifTest
  /-- The object of a `with`.  It stands between parentheses like the
  condition of a `while`, but prettier does not treat those parentheses as
  the ones of a condition: a binary expression written here is laid out as
  it is anywhere else, and so is grouped and indented. -/
  | withObject
  /-- The initialiser or the update of a `for (;;)`. -/
  | forHeadPart
  /-- The test of a `for (;;)`. -/
  | forTest
  /-- An operand of a comma operator in the head of a `for (;;)`; `tail`
  says that it is not the first one, and so already stands inside the
  indentation the chain gives its operands. -/
  | forSeqTail (tail : Bool)
  /-- The argument of `return` or `throw`. -/
  | returnThrow
  /-- Inside `[ ]`. -/
  | computed
  /-- Inside a `${ }` substitution of a template literal. -/
  | templateSubst
  /-- Another operand of the comma operator.  `indented` says that the
  chain indents the operands after the first, which it does when the chain
  is an expression statement; `tail` that this operand is not the first
  one, and so already stands inside that indentation. -/
  | seqTail (indented tail : Bool)
  /-- An argument of a call, an element of an array, ... -/
  | arg
  /-- An element of an array literal. -/
  | arrayElement
  /-- The value a `case` of a `switch` is compared with. -/
  | caseTest
  /-- The object a `for (... in ...)` or a `for (... of ...)` walks. -/
  | forInObject
  /-- The expression of a `{ }` substitution written as a child of a JSX
  element. -/
  | jsxChildExpr
  /-- The expression of a `{ }` value of a JSX attribute. -/
  | jsxAttrExpr
  /-- An argument of a call or of a `new`. -/
  | callArg
  /-- An argument of a call of a test framework, whose arguments prettier
  keeps on the line of the call; a function written here keeps its whole
  parameter list on one line as well. -/
  | testCallArg
  /-- The argument of a call that the layout may expand in place, keeping
  the rest of the call on one line.  `sole` says that it is the only
  argument, where a function expression keeps its parameter list on one
  line only when every parameter is a plain identifier; `newExpr` that the
  call is a `new`, where the parameter list keeps its own layout; `first`
  that it is the first argument rather than the last one, where a function
  expression keeps its own layout as well. -/
  | hugArg (sole newExpr first : Bool)
  /-- The right hand side of an assignment or of a declarator.  `nested`
  says that the assignment is not itself an expression statement or a
  declaration, so that a further assignment here is laid out as a link of
  a chain; `inlineMembers` that the assignment is one whose left hand side
  is not a plain identifier, which keeps the member accesses of the right
  hand side on the line of their object; `ofAssign` that the parent is an
  assignment expression, rather than a declarator or a default value;
  `arrowChain` that the assignment lays a chain of arrow functions written
  here out as the tail of a chain of assignments, which always breaks the
  signatures of the chain. -/
  | assignRhs (nested inlineMembers ofAssign arrowChain : Bool)
  /-- The value of a property of an object literal, or of a class field;
  `accessor` says that it is the value of a field written with the
  `accessor` keyword, whose operator chains prettier indents once more
  than those of an ordinary field. -/
  | propValue (accessor classField : Bool)
  /-- The body of an arrow function. -/
  | arrowBody
  /-- The body of an arrow function that is itself expanded in place as
  the argument of a call. -/
  | hugArrowBody
  /-- The operand of `...`. -/
  | spreadArg
  /-- The operand of the `...` of a `{...children}` written as a child of
  a JSX element, which takes fewer parentheses than the operand of a `...`
  written anywhere else: the braces around it already delimit it. -/
  | jsxSpreadChildArg
  /-- The argument of `yield` or of `yield*`.  It needs the same
  parentheses as an argument of a call, but a conditional expression in a
  chain written here is indented inside the parentheses it needs. -/
  | yieldArg
  /-- The consequent of a conditional expression.  `outerIndents` says
  that the conditional itself stands in a `return`, a `throw`, or the
  arguments or the callee of a call or a `new`, where prettier indents the
  operator chain of a binary expression written here; `jsx` that the chain
  of conditionals this one belongs to holds a JSX element, which prettier
  lays the whole chain out for. -/
  | ternaryBranch (outerIndents jsx : Bool)
  /-- The alternate of a conditional expression; `outerIndents` and `jsx`
  are as for the consequent. -/
  | ternaryAlternate (outerIndents jsx : Bool)
  /-- The condition of a conditional expression; `outerIndents` is as for
  the consequent. -/
  | ternaryTest (outerIndents : Bool)
  /-- The operand of a prefix or postfix operator. -/
  | unaryArg
  /-- The operand of `await`.  It needs the same parentheses as the
  operand of a prefix operator, but a binary expression here is laid out
  as it is anywhere else, rather than breaking between the parentheses. -/
  | awaitArg
  /-- The object of a member access.  `computed` says that the access is
  written `[ ]` rather than `.`; `extra` that the chain the access belongs
  to stands in one of the places prettier indents a conditional expression
  inside the parentheses it needs: the right hand side of an assignment,
  or the argument of `return`, `throw`, `await` or a unary operator;
  `inline` that the chain is assigned to something other than a plain
  identifier, which keeps the access on the line of its object. -/
  | memberObject (computed extra inline : Bool)
  /-- The left hand side of an assignment. -/
  | assignTarget
  /-- The tag of a tagged template literal. -/
  | templateTag
  /-- The callee of a `new`. -/
  | newCallee
  /-- The expression of a decorator, `@expr`.  It is parenthesised as the
  object of a member access is, but a member access written here keeps
  the line of its object, as prettier writes the `.` of a decorator. -/
  | decorator
  /-- The callee of a call.  `extra` is as for the object of a member
  access; `parentArgs` is the number of arguments the call itself takes,
  which decides whether a call written here is a link of a long curried
  chain, `f(a, b)(c)`. -/
  | callee (extra : Bool) (parentArgs : Nat)
  /-- The `extends` clause of a class. -/
  | classHeritage
  /-- An operand of a binary or logical operator. -/
  | binOperand (op : BinOp) (isLeft : Bool)
  /-- Any other position; parentheses as for an argument. -/
  | generic
deriving BEq, Inhabited

/-- The precedence an expression must have not to be parenthesised. -/
def Pos.minPrec : Pos → Nat
  | .statement | .ifTest | .withObject | .forHeadPart | .forTest | .forSeqTail .. | .returnThrow
  | .computed | .templateSubst | .seqTail .. => 0
  | .arg | .arrayElement | .caseTest | .forInObject | .jsxChildExpr | .jsxAttrExpr
  | .callArg | .testCallArg | .hugArg .. | .assignRhs .. | .propValue .. | .arrowBody
  | .yieldArg
  | .hugArrowBody | .spreadArg | .jsxSpreadChildArg | .ternaryBranch ..
  | .ternaryAlternate .. | .generic => 1
  | .ternaryTest .. => 3
  | .unaryArg | .awaitArg => 14
  | .memberObject .. | .assignTarget | .templateTag | .callee .. | .newCallee
  | .classHeritage | .decorator => 16
  | .binOperand op _ => 2 + binOpPrec op

/-- The precedence of an expression, from 0 for the comma operator to 17
for a primary expression. -/
def exprPrec : MiniExpr → Nat
  | .seq _ _ => 0
  | .assign .. | .assignPattern .. | .arrow .. | .yield _ | .yieldFrom _ | .spread _ => 1
  | .ternary .. => 2
  | .binary _ op _ => 2 + binOpPrec op
  | .unary .. | .await _ => 14
  | .postfix .. => 15
  | .call .. | .dot .. | .privateDot .. | .index .. | .new .. | .chain ..
  | .importCall .. => 16
  | .superDot .. | .superIndex .. | .superCall .. => 16
  | .template (some _) _ _ => 16
  | _ => 17

/-- The position the parenthesisation rules use: the positions that differ
only in the layout they ask for are the same for them. -/
def Pos.forParens : Pos → Pos
  | .withObject => .ifTest
  | .testCallArg => .callArg
  | .assignTarget | .templateTag | .memberObject .. | .decorator =>
      .memberObject false false false
  | .newCallee | .callee .. => .callee false 0
  | .hugArg .. => .hugArg false false false
  | .yieldArg | .arrayElement | .caseTest | .forInObject | .jsxChildExpr | .jsxAttrExpr => .arg
  | .assignRhs .. => .assignRhs false false false false
  | .ternaryBranch .. => .ternaryBranch false false
  | .ternaryAlternate .. => .ternaryAlternate false false
  | .ternaryTest _ => .ternaryTest false
  | p => p

/-- Whether the position is the object of a member access. -/
def isMemberObjectPos : Pos → Bool
  | .memberObject .. => true
  | _ => false

/-- Whether the position is the callee of a call. -/
def isCalleePos : Pos → Bool
  | .callee .. => true
  | _ => false

/-- Whether the position is the right hand side of an assignment or of a
declarator. -/
def isAssignRhsPos : Pos → Bool
  | .assignRhs .. => true
  | _ => false

/-- Whether prettier parenthesises a JSX element written here.  It writes
no parentheses where a `<` can only be read as the start of an element:
an expression statement, an element of an array literal, an argument of a
call or of a `new`, an operand of a binary or logical operator, a branch
of a conditional, either side of an assignment, the value of a property of
an object literal, the body of an arrow function, the argument of
`return`, `throw` or `yield`, what is exported by default, and anything
written inside a JSX element.  Everywhere else it writes them. -/
def jsxNeedsParens : Pos → Bool
  | .statement | .arrayElement | .arg | .generic => false
  | .callArg | .testCallArg | .hugArg .. => false
  | .assignRhs .. | .assignTarget => false
  | .binOperand .. => false
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => false
  | .arrowBody | .hugArrowBody => false
  | .propValue _ classField => classField
  | .returnThrow | .yieldArg => false
  | .jsxChildExpr | .jsxAttrExpr => false
  | _ => true

/-- Whether prettier writes no parentheses of its own around a JSX
element standing here: it does not where the element already stands
between delimiters of its own, that is, as a statement, an element of an
array literal, an argument of a call, a branch of a conditional, or inside
a `{ }` of another element.  The callee of a call and of a `new` are of
that kind too: the parentheses a `<` asks for there are written around the
element as it stands, rather than around lines of its own. -/
def jsxNoWrapPos : Pos → Bool
  | .statement | .arrayElement | .callArg | .testCallArg | .hugArg .. => true
  | .jsxChildExpr | .jsxAttrExpr => true
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => true
  | .callee .. | .newCallee => true
  | _ => false

/-- Whether the expression has to be parenthesised in this position. -/
def needsParens (pos0 : Pos) (e : MiniExpr) : Bool :=
  let pos := pos0.forParens
  match e with
  | .binary _ op _ =>
      match pos with
      | .binOperand pop isLeft => binaryOperandParens pop op isLeft
      | .unaryArg | .awaitArg | .callee .. | .spreadArg | .memberObject ..
      | .classHeritage => true
      | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => op == .coalesce
      | _ => exprPrec e < pos.minPrec
  -- `await await a`: an `await` written as the operand of another one
  -- keeps no parentheses, while a `yield` written there does
  | .await _ =>
      match pos with
      | .awaitArg => false
      | .unaryArg | .spreadArg | .memberObject .. | .callee ..
      | .ternaryTest .. => true
      | .binOperand .. => true
      | _ => exprPrec e < pos.minPrec
  | .yield _ | .yieldFrom _ =>
      match pos with
      | .unaryArg | .awaitArg | .spreadArg | .memberObject .. | .callee ..
      | .ternaryTest .. => true
      | .binOperand .. => true
      | _ => exprPrec e < pos.minPrec
  | .seq _ _ =>
      match pos with
      | .forHeadPart | .forTest | .forSeqTail .. | .seqTail .. => false
      | _ => true
  -- An assignment is parenthesised everywhere but in an expression
  -- statement, in the head of a `for (;;)` and on the right of another
  -- assignment; `const x = (a = 1);` is parenthesised, since the
  -- declarator is not an assignment expression
  | .assign _ _ _ =>
      match pos0 with
      | .statement | .forHeadPart | .forSeqTail .. => false
      | .assignRhs _ _ ofAssign _ => !ofAssign
      | _ => true
  -- `({ a } = o);`: an assignment to an object pattern is parenthesised
  -- even as a statement of its own, since it would otherwise be read as a
  -- block
  | .assignPattern l _ =>
      match pos0 with
      | .statement => (match l with | .object .. => true | _ => false)
      | .forHeadPart | .forSeqTail .. => false
      | .assignRhs _ _ ofAssign _ => !ofAssign
      | _ => true
  -- `f(...(a ? b : c))`: a conditional spread needs parentheses.  Under
  -- `experimentalTernaries` a conditional written as the test of another
  -- takes none: the layout writes the two of them as one chain
  | .ternary .. =>
      pos == .spreadArg
        || (if Options.experimentalTernaries && (match pos with
              | .ternaryTest _ => true | _ => false) then false
            else exprPrec e < pos.minPrec)
  -- `(void a) in b`: a unary operand of `in` or of `instanceof` keeps its
  -- parentheses on the left of the operator
  -- an update written with `++` or `--` is not one of them
  | .unary uop _ =>
      (uop != .preIncr && uop != .preDecr &&
        match pos with
        | .binOperand op true => op == .inOp || op == .instanceOf || op == .exp
        | _ => false)
        || exprPrec e < pos.minPrec
  -- `(x) => ({ a: 1 })`: an object literal body needs parentheses
  | .object _ => pos == .arrowBody || pos == .hugArrowBody
  -- `(5).toFixed()`: a number needs parentheses to be the object of a
  -- `.`, which a `BigInt` literal, written with its `n`, does not
  | .number (.bigint ..) => exprPrec e < pos.minPrec
  | .number _ => isMemberObjectPos pos
  -- `(a?.b).c` is not `a?.b.c`, so the parentheses have to stay
  | .chain _ _ => isMemberObjectPos pos || isCalleePos pos
  | .jsx _ => jsxNeedsParens pos0
  -- `(function () {})()` and ``(function () {})`t` ``: a function
  -- expression keeps its parentheses as the callee of a call and as the
  -- tag of a template, but a class expression does not
  | .func .. => isCalleePos pos || pos0 == .templateTag || exprPrec e < pos.minPrec
  | .classExpr .. => exprPrec e < pos.minPrec
  | _ => exprPrec e < pos.minPrec

/-- Whether the expression is a class expression which has decorators.
Prettier breaks the parentheses such a class takes, so that the decorators
stand on lines of their own inside them. -/
def isDecoratedClass : MiniExpr → Bool
  | .classExpr (_ :: _) _ _ _ => true
  | _ => false

/-- The parentheses the expression `e` takes, given the document it prints
as.  A decorated class expression breaks inside them. -/
def parenIfExpr (cond : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  if !cond then d
  else if isDecoratedClass e then
    t "(" ++ .nest indentWidth (.hardline ++ d) ++ .hardline ++ t ")"
  else parens d

/-- An expression in position `pos`, given the document it prints as. -/
def inPos (pos : Pos) (e : MiniExpr) (d : Doc) : Doc := parenIfExpr (needsParens pos e) e d

/-- Whether a conditional expression in the object of a member access, or
in the callee of a call, that stands here is indented inside the
parentheses it needs.  Prettier does so when the chain that holds it is
the right hand side of an assignment or of a declarator, or the argument
of `return`, `throw`, `await`, `yield` or a unary operator. -/
def extraIndentRoot : Pos → Bool
  | .assignRhs .. | .returnThrow | .unaryArg | .awaitArg | .yieldArg => true
  | .memberObject _ extra _ => extra
  | .callee extra _ => extra
  | _ => false

/-- Whether prettier lets the parentheses an `await` expression takes here
break, writing its operand on a line of its own inside them.  It does so
where the `await` is the object of a member access or the callee of a
call, which are the places the parentheses come from; the callee of a
`new` and the tag of a template literal are not among them. -/
def awaitBreaksInParens : Pos → Bool
  | .memberObject .. | .callee .. => true
  | _ => false

/-- Whether the position is the test, the consequent or the alternate of a
conditional expression. -/
def isTernaryPos : Pos → Bool
  | .ternaryTest .. | .ternaryBranch .. | .ternaryAlternate .. => true
  | _ => false

/-- For a position inside a conditional expression: whether the
conditional itself stands where prettier indents the operator chain of a
binary expression written in it. -/
def ternaryOuterIndents : Pos → Bool
  | .ternaryTest g | .ternaryBranch g _ | .ternaryAlternate g _ => g
  | _ => false

/-- Whether a conditional expression in this position is the child of a
`return`, of a `throw`, or of a call or a `new`, which is what decides
whether the operator chain of a binary expression inside the conditional
is indented. -/
def ternaryParentIndents : Pos → Bool
  | .returnThrow | .callArg | .hugArg .. | .callee .. | .newCallee => true
  | _ => false

/-- Whether prettier keeps the member accesses of a chain that stands here
on the line of their object: the chain is assigned to something other than
a plain identifier. -/
def inlineMemberRoot : Pos → Bool
  | .assignRhs _ inline _ _ => inline
  | .memberObject _ _ inline => inline
  -- the left hand side of an assignment is a member access itself, and so
  -- is not a plain identifier
  | .assignTarget => true
  -- prettier looks past the accesses of a chain for what holds it, so
  -- every access of the callee of a `new` keeps its line
  | .newCallee => true
  | _ => false

/-- The position of the object of a member access that stands in `pos`;
`computed` says that the access is written `[ ]`. -/
def memberObjectPos (computed : Bool) (pos : Pos) : Pos :=
  .memberObject computed (extraIndentRoot pos) (inlineMemberRoot pos)

/-- The position of the callee of a call that stands in `pos` and takes
`parentArgs` arguments. -/
def calleePos (pos : Pos) (parentArgs : Nat) : Pos :=
  .callee (extraIndentRoot pos) parentArgs

/-- Whether a call with `argCount` arguments written in `pos` is a link of
a long curried chain, `f(a, b)(c)`: it is the callee of a call that takes
fewer arguments than it does, and at least one.  Prettier leaves the
argument list of such a call ungrouped, so that it breaks together with
the line that holds the call rather than on its own. -/
def isLongCurriedCall (pos : Pos) (argCount : Nat) : Bool :=
  match pos with
  | .callee _ parentArgs => 0 < parentArgs && parentArgs < argCount
  | _ => false

/-- Whether the expression is one prettier counts as a call: an ordinary
call, a call of `super`, a dynamic `import()`, or an optional chain whose
last link is a call.  A `new` is not one of them. -/
def isCallLikeExpr : MiniExpr → Bool
  | .call .. | .superCall .. | .importCall .. => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call ..) => true
      | _ => false
  | _ => false

/-- Whether the expression may not be written at the start of a statement,
because it would be read as a block, a function declaration or a class
declaration. -/
def cannotStartStatement : MiniExpr → Bool
  | .object _ | .func .. | .classExpr .. => true
  | _ => false

/-- Whether the link of an optional chain is written with `?.`. -/
def chainLinkIsOptional : MiniChainLink → Bool
  | .dot o _ | .privateDot o _ | .index o _ | .call o _ => o

/-- Whether the link of an optional chain is a call. -/
def chainLinkIsCall : MiniChainLink → Bool
  | .call .. => true
  | _ => false

/-- Whether an optional chain used as the base of another one merges into
it: it does when the link that follows it is optional, which makes the
parentheses around the base unnecessary. -/
def chainMergesBase (links : NonEmptyList MiniChainLink) : Bool := chainLinkIsOptional links.head

/-- Whether the leftmost token of the expression opens a function or a
class expression, so that `export default` in front of it would be read as
a declaration.  `pos` is the position the expression itself stands in: the
walk stops at a subexpression which is parenthesised there, since the
parentheses are then the leftmost token.  A call or a tagged template
whose callee is a function expression is one such place. -/
def startsWithFunctionOrClassAt (merged : Bool) (pos : Pos) (e : MiniExpr) : Bool :=
  -- an optional chain that merges into the one which holds it keeps no
  -- parentheses of its own, so the walk goes on into its base
  let isChain := match e with | .chain .. => true | _ => false
  if needsParens pos e && !(merged && isChain) then false
  else
    match e with
    | .func .. | .classExpr .. => true
    | .binary l op _ => startsWithFunctionOrClassAt false (.binOperand op true) l
    | .assign l _ _ => startsWithFunctionOrClassAt false .assignTarget l
    | .seq l _ => startsWithFunctionOrClassAt false (.seqTail false false) l
    | .ternary c _ _ => startsWithFunctionOrClassAt false (.ternaryTest false) c
    | .postfix l _ => startsWithFunctionOrClassAt false .unaryArg l
    | .dot o _ | .privateDot o _ | .index o _ =>
        startsWithFunctionOrClassAt false (.memberObject false false false) o
    | .template (some tag) _ _ => startsWithFunctionOrClassAt false .templateTag tag
    | .call callee _ => startsWithFunctionOrClassAt false (.callee false 0) callee
    | .chain base links =>
        -- the base of a chain stands in parentheses unless the first link
        -- of the chain is optional, which merges the two
        startsWithFunctionOrClassAt (chainMergesBase links)
          (.memberObject false false false) base
    | _ => false

/-- Whether the leftmost token of an expression written after
`export default` opens a function or a class expression. -/
def startsWithFunctionOrClass (e : MiniExpr) : Bool :=
  startsWithFunctionOrClassAt false .generic e

/-- Whether the expression is the identifier `let`, which is a keyword
where a declaration may stand. -/
def isLetIdent : MiniExpr → Bool
  | .ident n => n.toString == "let"
  | _ => false

/-- Whether the position is the object of a `[ ]` access, where the
identifier `let` is read as the keyword of a declaration. -/
def isComputedMemberObjectPos : Pos → Bool
  | .memberObject computed _ _ => computed
  | _ => false

/-- Whether the expression needs parentheses because of what stands to its
left.  `pos` is the position of the expression itself, which says whether
a `[` follows the identifier `let` written here. -/
def cannotStartWith : StartCtx → Pos → MiniExpr → Bool
  | .none, _, _ => false
  | .awaitArgument, _, _ => false
  | .forInit, pos, e => isLetIdent e && isComputedMemberObjectPos pos
  | .forInHead, _, e => isLetIdent e
  | .statement, pos, e =>
      cannotStartStatement e || (isLetIdent e && isComputedMemberObjectPos pos)
  | .arrowBody, _, .object _ => true
  | .arrowBody, _, _ => false
  | .jsxArrowBody, _, .object _ => true
  | .jsxArrowBody, _, _ => false
  | .jsxCallArg, _, _ => false

/-- The start context an argument of a call is printed with.  The mark
that says the call stands directly in a `{ }` of a JSX element belongs to
an arrow function written as the argument itself: a JSX element deeper
inside another kind of argument, such as the test of a conditional, is
not one prettier writes on lines of its own. -/
def argStartCtx (st : StartCtx) : MiniExpr → StartCtx
  | .arrow .. => st
  | _ => .none

/-- An expression in position `pos`, where `atStart` says what it is the
leftmost part of, so that an object literal, a function or a class
expression there needs parentheses. -/
def inPosStart (atStart : StartCtx) (pos : Pos) (e : MiniExpr) (d : Doc) : Doc :=
  parenIf (needsParens pos e || cannotStartWith atStart pos e) d

/-! ## Small predicates on expressions -/

def isLogicalExpr : MiniExpr → Bool
  | .binary _ op _ => isLogicalOp op
  | _ => false

def isBinaryish : MiniExpr → Bool
  | .binary .. => true
  | _ => false

def binKind : MiniExpr → BinKind
  | .binary _ op _ => if isLogicalOp op then .logical else .arith
  | _ => .other

/-- The last operand of a chain of the same logical operator that leans to
the right: the right hand operand of the chain once it is rebalanced.  A
chain of one logical operator is written without parentheses, so a tree
which leans to the right is read back as one which leans to the left, and
it is the operand of the tree so read that the layout looks at. -/
def logicalLastOperand (op : BinOp) : MiniExpr → MiniExpr
  | .binary l rop r =>
      if isLogicalOp op && rop == op then logicalLastOperand op r else .binary l rop r
  | e => e

/-- A logical expression whose right operand is a non-empty object or
array literal, or a JSX element, is kept on one line. -/
def shouldInlineLogical : MiniExpr → Bool
  | .binary _ op r =>
      isLogicalOp op &&
        (match logicalLastOperand op r with
          | .object (_ :: _) => true
          | .array (_ :: _) => true
          | .jsx _ => true
          | _ => false)
  | _ => false

def isFunctionLike : MiniExpr → Bool
  | .func .. | .arrow .. => true
  | _ => false

def isNumericLit : MiniExpr → Bool
  | .number _ => true
  | _ => false

def isStringLit : MiniExpr → Bool
  | .string _ => true
  | _ => false

/-- `this`, or an identifier. -/
def isSingleWord : MiniExpr → Bool
  | .ident _ | .this | .privateName _ => true
  | _ => false

def isLiteralExpr : MiniExpr → Bool
  | .number _ | .string _ | .regex _ | .null | .true_ | .false_ => true
  | _ => false

/-- Whether the expression is one of the simple arguments prettier allows
in a member chain that is printed on one line. -/
def isSimpleCallArgument : Nat → MiniExpr → Bool
  | 0, _ => false
  | _ + 1, .regex r => r.source.toString.length ≤ 5
  | d + 1, e =>
    match e with
    | .number _ | .string _ | .null | .true_ | .false_ => true
    | .ident _ | .this | .privateName _ => true
    -- a tagged template is not one of them
    | .template none head parts =>
        !head.contains '\n' && simpleTemplateParts d parts
    | .object props => simpleProps d props
    | .array els => simpleElements d els
    | .call f args => isSimpleCallArgument (d + 1) f && args.length ≤ d + 1 && simpleArgs d args
    | .new f args => isSimpleCallArgument (d + 1) f && args.length ≤ d + 1 && simpleArgs d args
    | .dot o _ => isSimpleCallArgument (d + 1) o
    | .privateDot o _ => isSimpleCallArgument (d + 1) o
    | .index o i => isSimpleCallArgument (d + 1) o && isSimpleCallArgument (d + 1) i
    | .unary op a =>
        (op == .not || op == .minus || op == .plus || op == .tilde
          || op == .preIncr || op == .preDecr)
          && isSimpleCallArgument (d + 1) a
    | .postfix a _ => isSimpleCallArgument (d + 1) a
    | .chain base ⟨hd, tl⟩ =>
        isSimpleCallArgument (d + 1) base && simpleChainLink d hd && simpleChainLinks d tl
    -- a dynamic `import()` is call-like, but has no callee to look at
    | .importCall spec options =>
        (match options with
          | none => true
          | some o => 2 ≤ d + 1 && isSimpleCallArgument d o)
          && isSimpleCallArgument d spec
    | _ => false
where
  simpleArgs (d : Nat) : List MiniExpr → Bool
    | [] => true
    | a :: rest => isSimpleCallArgument d a && simpleArgs d rest
  simpleElements (d : Nat) : List MiniArrayElement → Bool
    | [] => true
    | .hole :: rest => simpleElements d rest
    | .elem a :: rest => isSimpleCallArgument d a && simpleElements d rest
  simpleProps (d : Nat) : List MiniProperty → Bool
    | [] => true
    | .shorthand _ :: rest => simpleProps d rest
    | .keyValue k v :: rest =>
        (match k with | .computed _ => false | _ => true)
          && isSimpleCallArgument d v && simpleProps d rest
    | _ => false
  simpleTemplateParts (d : Nat) : List MiniTemplatePart → Bool
    | [] => true
    | ⟨e, suffix⟩ :: rest =>
        isSimpleCallArgument d e && !suffix.contains '\n' && simpleTemplateParts d rest
  simpleChainLink (d : Nat) : MiniChainLink → Bool
    | .dot .. | .privateDot .. => true
    | .index _ i => isSimpleCallArgument (d + 1) i
    | .call _ args => args.length ≤ d + 1 && simpleArgs d args
  simpleChainLinks (d : Nat) : List MiniChainLink → Bool
    | [] => true
    | l :: rest => simpleChainLink d l && simpleChainLinks d rest

/-- Whether `e` is a chain of member accesses ending in an identifier or
`this`, which prettier breaks after the `=` of an assignment. -/
def isMemberExpressionChain : MiniExpr → Bool
  | .dot o _ | .privateDot o _ | .index o _ =>
      match o with
      | .ident _ | .this => true
      | _ => isMemberExpressionChain o
  | _ => false

/-- Whether the lone argument of a call is short enough for the call to
keep its line. -/
def isLoneShortArgument : MiniExpr → Bool
  | .this => true
  | .ident n => n.toString.length ≤ shortArgWidth
  | .string s => (strLit s).length ≤ shortArgWidth
  | .number _ => true
  -- `++x` and `--x` update what they read, and are not unary operators to
  -- prettier, which does not read through them
  | .unary .preIncr _ | .unary .preDecr _ => false
  -- the argument of any unary operator, `!` and `typeof` included, is
  -- read through
  | .unary _ a => isLoneShortArgument a
  | .regex r => r.source.toString.length ≤ shortArgWidth
  -- a template literal of no substitution, whose text is short and stands
  -- on one line
  | .template none head [] =>
      (encodeTemplateText head).length ≤ shortArgWidth && !head.contains '\n'
  | .call (.ident n) [] => n.toString.length + 2 ≤ shortArgWidth
  | e => isLiteralExpr e

/-- Whether the arguments of a call let the call keep its line: there are
none, or there is one short one. -/
def argumentsAreShort : List MiniExpr → Bool
  | [] => true
  | [a] => isLoneShortArgument a
  | _ => false

/-- Whether the links of an optional chain, outermost first, make a chain
prettier considers poorly breakable.  `baseOk` says whether the base of
the chain is one. -/
def linksArePoorlyBreakable (baseOk : Bool) : List MiniChainLink → Bool
  | [] => baseOk
  | .call _ args :: rest =>
      argumentsAreShort args
        && (match rest with
            -- the callee of the call is itself a call
            | .call .. :: _ => false
            | _ => linksArePoorlyBreakable baseOk rest)
  | _ :: rest => linksArePoorlyBreakable baseOk rest

/-- Whether `e` is a chain of member accesses and calls whose calls have
no argument, or one short argument. -/
def isPoorlyBreakableChain : Bool → MiniExpr → Bool
  -- the callee is read through, whatever it is: a member access, a
  -- parenthesised optional chain, or a call of its own
  | _, .call f args => argumentsAreShort args && isPoorlyBreakableChain true f
  | _, .dot o _ | _, .privateDot o _ | _, .index o _ => isPoorlyBreakableChain true o
  | _, .chain base ⟨hd, tl⟩ =>
      linksArePoorlyBreakable (isPoorlyBreakableChain true base) (hd :: tl).reverse
  | deep, .ident _ => deep
  | deep, .this => deep
  | _, _ => false

/-- Whether a property name has to keep its quotes: it is a string that is
neither an identifier name nor the plain spelling of the number it
denotes.  Under `quoteProps: "consistent"` one such name among the
properties of an object, of a class or of a pattern quotes them all. -/
def keyNeedsQuotes : MiniPropertyName → Bool
  | .string v => !isIdentifierName v && !isSimpleNumberString v
  | _ => false

/-- Whether every name of a list of property names is written quoted:
`quoteProps: "consistent"` and one of them that cannot lose its
quotes. -/
def quoteAllKeys (keys : List MiniPropertyName) : Bool :=
  Options.quoteProps == .consistent && keys.any keyNeedsQuotes

/-- The names of the properties of an object literal. -/
def propertyKeys : List MiniProperty → List MiniPropertyName
  | [] => []
  | .keyValue k _ :: rest | .method _ k _ _ :: rest => k :: propertyKeys rest
  | _ :: rest => propertyKeys rest

/-- Whether the properties of an object literal are all written quoted. -/
def quoteAllProps (props : List MiniProperty) : Bool := quoteAllKeys (propertyKeys props)

/-- The names of the members of a class. -/
def classElemKeys : List MiniClassElement → List MiniPropertyName
  | [] => []
  | .method _ _ _ k _ _ :: rest | .field _ _ _ k _ :: rest => k :: classElemKeys rest
  | _ :: rest => classElemKeys rest

/-- Whether the members of a class are all written quoted. -/
def quoteAllMembers (body : List MiniClassElement) : Bool := quoteAllKeys (classElemKeys body)

/-- The names bound by an object pattern. -/
def objectPatternKeys : List MiniObjectPatternProp → List MiniPropertyName
  | [] => []
  | ⟨key, _⟩ :: rest => key :: objectPatternKeys rest

/-- Whether the names bound by an object pattern are all written
quoted. -/
def quoteAllPatternKeys (props : List MiniObjectPatternProp) : Bool :=
  quoteAllKeys (objectPatternKeys props)

/-! ## Semicolons -/

/-- Whether the name is one of `static`, `get` and `set` written as a
plain identifier: a field of that name and no value keeps its semicolon
under `semi: false`, since the line that follows it would otherwise be
read as its value. -/
def keyIsStaticGetSet : MiniPropertyName → Bool
  | .ident n => n.toString == "static" || n.toString == "get" || n.toString == "set"
  | _ => false

/-- Whether the name is `in` or `instanceof`, which a member written after
a field would be read as an operator of. -/
def keyIsInOrInstanceof : MiniPropertyName → Bool
  | .ident n => n.toString == "in" || n.toString == "instanceof"
  | _ => false

/-- Whether the name is a computed one, `[e]`. -/
def keyIsComputed : MiniPropertyName → Bool
  | .computed _ => true
  | _ => false

/-- Under `semi: false`, whether the member written after a field would be
read as part of that field, so that the field keeps its semicolon: it is
prettier's `shouldPrintSemicolonAfterClassProperty`. -/
def memberFollowsField : Option MiniClassElement → Bool
  | none => false
  | some (.staticBlock _) => false
  -- an `accessor` field is not one prettier reads a computed name as
  -- the continuation of: only the `in` and `instanceof` rule applies
  | some (.field _ isStatic isAccessor key _) =>
      !isStatic && (keyIsInOrInstanceof key || (!isAccessor && keyIsComputed key))
  | some (.method _ isStatic kind key _ _) =>
      !isStatic
        && (keyIsInOrInstanceof key
            || (match kind with
                | .get | .set | .async | .asyncGenerator => false
                | .generator => true
                | .normal => keyIsComputed key))

/-- The semicolon written after a class field: always under `semi: true`,
and under `semi: false` only where a parser would otherwise read on. -/
def fieldSemiDoc (key : MiniPropertyName) (init : Option MiniExpr)
    (next : Option MiniClassElement) : Doc :=
  if Options.semi then t ";"
  else if init.isNone && keyIsStaticGetSet key then t ";"
  else if memberFollowsField next then t ";"
  else .nil

/-- Whether the leftmost token of the expression is a prefix `++` or `--`.
Prettier reads such a statement as one that needs no semicolon in front of
it, although it begins with `+` or `-`. -/
def startsWithPrefixUpdate : MiniExpr → Bool
  | .unary .preIncr _ | .unary .preDecr _ => true
  | .binary l _ _ | .seq l _ | .assign l _ _ => startsWithPrefixUpdate l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ => startsWithPrefixUpdate o
  | .call f _ => startsWithPrefixUpdate f
  | .postfix e _ => startsWithPrefixUpdate e
  | .ternary c _ _ => startsWithPrefixUpdate c
  | .template (some tag) _ _ => startsWithPrefixUpdate tag
  | _ => false

/-! ## Layout helpers -/

/-- Whether the only parameter of a function is one prettier writes out
between the parentheses of the function, as in `function ({\n  a,\n}) {}`:
it destructures an object or an array, possibly with a plain default
value. -/
def shouldHugTheOnlyParameter : List MiniParam → Bool
  | [.plain p] =>
      let rec destructures : MiniPattern → Bool
        | .object .. | .array .. => true
        | _ => false
      match p with
      | .withDefault q v =>
          destructures q &&
            (match v with
              | .ident _ => true
              | .object [] => true
              | .array [] => true
              | _ => false)
      | q => destructures q
  | _ => false

/-- Whether the parameters of an arrow function are written without their
parentheses: `arrowParens: "avoid"`, and one parameter which is a plain
name -- not a rest element, a pattern or a name with a default value. -/
def arrowParensAvoided : List MiniParam → Bool
  | [.plain (.ident _)] => Options.arrowParens == .avoid
  | _ => false

/-- Whether the leftmost token of the expression is that of an arrow
function whose parameters prettier writes between parentheses.  Such a
statement is one prettier guards under `semi: false`, even where the
arrow is written `async` first and so does not itself begin with `(`. -/
def startsWithParenArrow : MiniExpr → Bool
  | .arrow _ params _ => !arrowParensAvoided params
  | .binary l _ _ | .seq l _ | .assign l _ _ => startsWithParenArrow l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ => startsWithParenArrow o
  | .call f _ => startsWithParenArrow f
  | .postfix e _ => startsWithParenArrow e
  | .ternary c _ _ => startsWithParenArrow c
  | .template (some tag) _ _ => startsWithParenArrow tag
  | _ => false

/-- Under `semi: false`, the semicolon prettier writes in front of an
expression statement of a statement list whose first token would
otherwise continue the statement before it. -/
def asiGuard (s : MiniStatement) (d : Doc) : Doc :=
  if Options.semi then d
  else
    match s with
    | .expr e =>
        if startsWithParenArrow e then t ";" ++ d
        else
          match Doc.firstFlatChar d with
          | some c =>
              if isASIHazardChar c
                  && !((c == '+' || c == '-') && startsWithPrefixUpdate e) then
                t ";" ++ d
              else d
          | none => d
    | _ => d

/-- A parameter list.  `hug` says that the list is the one object or array
pattern prettier writes out between the parentheses of the function. -/
def paramsDocOf (hug restLast : Bool) (items : List Doc) : Doc :=
  if hug then t "(" ++ Doc.concat items ++ t ")"
  else sepList "(" ")" false (if restLast then .never else .all) items

/-- Whether the statement can end with an `if` that has no `else`, so that
an `else` written after it would be read as belonging to that `if`. -/
def endsWithDanglingIf : MiniStatement → Bool
  | .if_ _ _ none => true
  | .if_ _ _ (some e) => endsWithDanglingIf e
  | .while_ _ b | .with_ _ b | .labelled _ b => endsWithDanglingIf b
  | .for_ _ _ _ b | .forIn _ _ b | .forOf _ _ _ b => endsWithDanglingIf b
  | _ => false

/-! ## Member chains -/

/-- What one element of a member chain is. -/
inductive ChainKind where
  | base | dot | index | call
deriving BEq, Inhabited

/-- One element of a member chain, together with what the layout
heuristics need to know about it. -/
structure ChainItem where
  /-- The kind of the element. -/
  kind : ChainKind
  /-- Its document. -/
  doc : Doc
  /-- For an index: whether the property is a number. -/
  numericIndex : Bool := false
  /-- For a `.name` access: the name. -/
  name : String := ""
  /-- For the base: whether it is `this`. -/
  isThis : Bool := false
  /-- For the base: its name, if it is an identifier. -/
  identName : String := ""
  /-- For the base: whether it is a call. -/
  isCallBase : Bool := false
  /-- For a call: whether all of its arguments are simple. -/
  simpleArgs : Bool := true
  /-- For a call: whether one of its arguments is a function. -/
  functionArg : Bool := false
  /-- For a call, or a base that is one: whether it has an argument. -/
  hasArgs : Bool := false
deriving Inhabited

/-- Whether the element continues a member chain, rather than ending it. -/
def ChainItem.isMemberish (i : ChainItem) : Bool := i.kind == .dot || i.kind == .index

/-- A `.` or `[]` access. -/
def isMemberish : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | _ => false

/-- Whether the first token of the expression is the `{` of an object
literal, so that the expression has to be parenthesised where a statement,
or the body of an arrow function, may not start with one. -/
def startsWithObjectLiteral : MiniExpr → Bool
  | .object _ => true
  | .call (.func ..) _ => false
  | .template (some (.func ..)) _ _ => false
  | .binary l _ _ | .assign l _ _ | .seq l _ => startsWithObjectLiteral l
  | .dot o _ | .privateDot o _ | .index o _ | .chain o _ | .postfix o _ =>
      startsWithObjectLiteral o
  | .call f _ => startsWithObjectLiteral f
  | .ternary c _ _ => startsWithObjectLiteral c
  | .template (some tag) _ _ => startsWithObjectLiteral tag
  | _ => false

/-- A conditional expression that does not start with an object literal.
Prettier keeps one on the line of the `=>` of an arrow function, and puts
parentheses around it when it stays on that line. -/
def isPlainConditional : MiniExpr → Bool
  | .ternary c _ _ => !startsWithObjectLiteral c
  | _ => false

/-- Whether the expression is a JSX element or fragment. -/
def isJsxExpr : MiniExpr → Bool
  | .jsx _ => true
  | _ => false

/-- Whether the expression is a conditional expression. -/
def consIsTernaryOf : MiniExpr → Bool
  | .ternary .. => true
  | _ => false

/-- Whether the chain of conditionals rooted at the expression holds a JSX
element in one of its tests or branches.  Prettier lays such a chain out
the way it lays JSX out. -/
def ternaryChainHasJsx : MiniExpr → Bool
  | .ternary c a b =>
      isJsxExpr c || isJsxExpr a || isJsxExpr b
        || ternaryChainHasJsx c || ternaryChainHasJsx a || ternaryChainHasJsx b
  | _ => false

/-! ## Conditional expressions under `experimentalTernaries`

Prettier's experimental layout of a conditional writes the `?` at the end
of the line of the test and the `:` in front of the alternate, and lays a
chain of conditionals out as a list of cases.  The helpers here are the
ones its rules ask about: how many nodes the test is made of, and whether
the consequent is a short expression.
-/

mutual

/-- The number of nodes the babel syntax tree of the expression holds,
counted the way prettier's `getNodeContentCount` counts them: the
properties of a node which are nodes themselves, recursively, and not the
ones which are lists of nodes. -/
def babelNodeCount : MiniExpr → Nat
  | .ident _ | .number _ | .string _ | .regex _ | .null | .true_ | .false_
  | .this | .privateName _ => 0
  -- `new.target` and `import.meta` hold the two names they are made of
  | .newTarget | .importMeta => 2
  -- a list of nodes is not read: the elements of an array, the properties
  -- of an object, the operands of the comma operator and the arguments of
  -- a call are not counted
  | .array _ | .object _ | .seq _ _ => 0
  | .superDot _ => 2
  | .superIndex i => 2 + babelNodeCount i
  | .superCall _ => 1
  | .assign l _ r => 2 + babelNodeCount l + babelNodeCount r
  | .assignPattern _ r => 2 + babelNodeCount r
  | .await e | .unary _ e | .postfix e _ | .spread e | .yieldFrom e => 1 + babelNodeCount e
  | .yield none => 0
  | .yield (some e) => 1 + babelNodeCount e
  | .call f _ | .new f _ => 1 + babelNodeCount f
  | .importCall spec opts =>
      1 + babelNodeCount spec
        + (match opts with | some o => 1 + babelNodeCount o | none => 0)
  | .dot o _ | .privateDot o _ => 2 + babelNodeCount o
  | .index o i => 2 + babelNodeCount o + babelNodeCount i
  | .chain b links => babelNodeCount b + babelChainLinksCount links.toList
  | .classExpr _ name heritage _ =>
      1 + (if name.isSome then 1 else 0)
        + (match heritage with | some h => 1 + babelNodeCount h | none => 0)
  | .func _ _ name _ _ => 1 + (if name.isSome then 1 else 0)
  | .arrow _ _ body => 1 + (match body with | .expr e => babelNodeCount e | .block _ => 0)
  | .binary l _ r => 2 + babelNodeCount l + babelNodeCount r
  | .ternary c a b => 3 + babelNodeCount c + babelNodeCount a + babelNodeCount b
  | .template none _ _ => 0
  | .template (some tag) _ _ => 2 + babelNodeCount tag
  -- an element holds its opening element, and its closing one where it
  -- has children; each of them holds its name
  | .jsx (.element _ _ children) => if children.isSome then 4 else 2
  | .jsx (.fragment _) => 2
termination_by e => sizeOf e
decreasing_by
  all_goals try (obtain ⟨hd, tl⟩ := links)
  all_goals simp +arith

/-- The nodes the links of an optional chain hold. -/
def babelChainLinksCount : List MiniChainLink → Nat
  | [] => 0
  | l :: rest =>
      (match l with
        | .dot _ _ | .privateDot _ _ => 2
        | .index _ i => 2 + babelNodeCount i
        | .call _ _ => 1)
      + babelChainLinksCount rest
termination_by ls => sizeOf ls

end

/-- Whether the expression is made of few enough nodes: prettier's
`isSmallNode`, which its experimental layout of a conditional asks of the
test. -/
def isSmallNode (limit : Nat) (e : MiniExpr) : Bool := babelNodeCount e ≤ limit

/-- Whether the expression is one prettier counts as short for its width:
`isSimpleExpressionByWidth`, which measures the text of a name, of a
string or of a regular expression against a quarter of the print width.
Its experimental layout of a conditional asks it of the consequent. -/
def isShortExpr : MiniExpr → Bool
  | .this => true
  | .ident n => 4 * n.toString.length ≤ Options.printWidth
  -- a signed numeric literal is short whatever it holds
  | .unary .plus (.number _) | .unary .minus (.number _) => true
  | .regex r => 4 * r.source.toString.length ≤ Options.printWidth
  | .string v => 4 * (strLit v).length ≤ Options.printWidth
  | .template none head [] =>
      4 * head.length ≤ Options.printWidth && !head.contains '\n'
  -- `++x` and `--x` are updates, not unary operators, and are not short
  | .unary .preIncr _ | .unary .preDecr _ => false
  | .unary _ e => isShortExpr e
  | .call (.ident n) [] => 4 * n.toString.length + 8 ≤ Options.printWidth
  | e => isLiteralExpr e

/-- Whether the expression is `null` or `undefined`.  A branch of a
conditional laid out for JSX which is one takes no parentheses. -/
def isNilExpr : MiniExpr → Bool
  | .null => true
  | .ident n => n.toString == "undefined"
  | _ => false

/-- Whether prettier keeps the body of an arrow function on the line of
its `=>`.  A chain of arrow functions that is always broken does not keep
a conditional body on that line. -/
def keepsArrowBodyOnLine (breakChain : Bool) : MiniExpr → Bool
  | .object _ | .array _ | .arrow .. => true
  | .jsx _ => true
  | .seq _ _ => true
  | e => !breakChain && isPlainConditional e

/-- The parameter lists of the arrow functions of a chain, and the body at
the end of the chain. -/
def arrowChainParts (params : List MiniParam) :
    MiniArrowBody → List (List MiniParam) × MiniArrowBody
  | .expr (.arrow _ ps b) =>
      let (rest, body) := arrowChainParts ps b
      (params :: rest, body)
  | b => ([params], b)

/-- Whether the parameter is a plain identifier.  Prettier always breaks a
chain of arrow functions one of whose parameters is not one. -/
def paramIsPlainIdent : MiniParam → Bool
  | .plain (.ident _) => true
  | _ => false

/-- Whether prettier keeps the body of a chain of arrow functions on the
line of the last `=>` of the chain. -/
def arrowBodyStaysOnLine (breakChain : Bool) : MiniArrowBody → Bool
  | .block _ => true
  | .expr e => keepsArrowBodyOnLine breakChain e

/-- What the body of an arrow function is the start of: an object literal
written there needs parentheses, unless the body is a sequence expression
or an assignment, which is parenthesised as a whole anyway. -/
def arrowBodyStart : MiniExpr → StartCtx
  | .seq _ _ | .assign .. => .none
  | _ => .arrowBody

/-- The same, for the body of an arrow function which is the argument of a
call written directly in a `{ }` of a JSX element: a JSX element there
stands on lines of its own, and an object literal needs parentheses
unless the body is parenthesised as a whole anyway. -/
def jsxArrowBodyStart : MiniExpr → StartCtx
  | .seq _ _ | .assign .. => .none
  | _ => .jsxArrowBody

/-- Whether the body of the arrow function is a chain of further arrow
functions, which prettier lays out as one unit. -/
def isArrowChainBody : MiniArrowBody → Bool
  | .expr (.arrow ..) => true
  | _ => false

/-- Whether the position is an argument of a call, or an operand of a
binary operator, where prettier indents the tail of a chain of arrow
functions. -/
def indentsArrowChainTail : Pos → Bool
  | .callArg | .hugArg .. => true
  | .binOperand .. => true
  | _ => false

/-- Whether the position is one where prettier lets a chain of arrow
functions start on a line of its own. -/
def breaksBeforeArrowChain : Pos → Bool
  | .callee .. | .assignRhs .. | .propValue .. => true
  | _ => false

/-- Whether the assignment the chain of arrow functions is the right hand
side of is the tail of a chain of assignments, which always breaks the
signatures of the chain. -/
def breaksArrowChainSignatures : Pos → Bool
  | .assignRhs _ _ _ b => b
  | _ => false

/-- The body of an arrow function that is an expression, with the space or
the line in front of it, given the document of the expression.  `chained`
says whether the arrow function is part of a chain of arrow functions,
whose body the chain lays out itself.  `hugged` says that the arrow
function is the argument of a call that the layout expands in place, where
a body that leaves the line of the `=>` takes the trailing comma of the
argument list with it and the closing parenthesis of the call keeps its
own line.  `jsxParent` says that the arrow function is written straight
inside a `{ }` of a JSX element, which likewise leaves the closing brace
its own line once the body leaves the line of the `=>`. -/
def arrowExprBodyOf (chained breakChain hugged jsxParent : Bool) (e : MiniExpr) (d : Doc) : Doc :=
  let trailer : Doc :=
    (if hugged && Options.hasTrailingComma .all then .ifBreak (t ",") .nil else .nil)
      ++ (if hugged || jsxParent then .softline else .nil)
  if !breakChain && isPlainConditional e then
    -- a conditional body keeps the line of the `=>`, in parentheses while
    -- it fits on it
    t " " ++ .group (.ifBreak .nil (t "(") ++ .nest indentWidth (.softline ++ d)
      ++ .ifBreak .nil (t ")") ++ trailer)
  else if keepsArrowBodyOnLine breakChain e then t " " ++ d
  else if chained then .nest indentWidth (.line ++ d) ++ trailer
  else .group (.nest indentWidth (.line ++ d) ++ trailer)

/-- The layout of an arrow function, or of a chain of them, given the
documents of its signatures and the document of its body, the space or the
line in front of the body included. -/
def arrowLayoutOf (pos : Pos) (breakChain bodyOnSameLine : Bool)
    (sigDocs : List Doc) (bodyPart : Doc) : Doc :=
  match sigDocs with
  | [] => bodyPart
  | [sig] => .group (sig ++ t " =>" ++ bodyPart)
  | sig :: rest =>
    let arrowSep : Doc := t " =>" ++ .line
    let grp (d : Doc) : Doc := if breakChain then .groupBreak d else .group d
    let sigsDoc : Doc :=
      if indentsArrowChainTail pos then
        grp (sig ++ t " =>" ++ .nest indentWidth (.line ++ Doc.joinWith arrowSep rest))
      else if breaksBeforeArrowChain pos then grp (Doc.joinWith arrowSep sigDocs)
      else grp (.nest indentWidth (Doc.joinWith arrowSep sigDocs))
    let isCallee := isCalleePos pos
    let head : Doc :=
      if breaksBeforeArrowChain pos then
        (if (isCallee && !bodyOnSameLine) || breaksArrowChainSignatures pos then
            Doc.breakParent
          else .nil)
          ++ .nest indentWidth (.softline ++ sigsDoc)
      else sigsDoc
    .group (.groupIndentIfBreak indentWidth (head ++ t " =>") bodyPart
      (if isCallee then .softline else .nil))

/-- Whether the node is part of the spine of a member chain. -/
def isChainNode : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .call f _ => isChainNode f
  | _ => false

/-- Whether the node is one whose elements a member chain is made of,
rather than the base the chain starts from.  A call belongs to the chain
only when its callee does: `f().a.b` starts from the whole `f()`, whereas
`a.b().c` starts from `a`. -/
def isChainSpine : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. | .chain .. => true
  | .call f _ => isChainNode f || (match f with | .call .. => true | _ => false)
  | _ => false

/-- Whether the node is read through by the member chain layout: a member
access is, and so is a call whose callee is a member access or a call
itself, which is how prettier takes a curried call, `f(a, b)(c)`, into the
chain that holds it. -/
def isChainSpineNode : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .call f _ => isMemberish f || isCallLikeExpr f
  | _ => false

/-- Split the elements of a chain into the groups prettier lays out, one
per line when the chain breaks. -/
private def chainGroups (baseIsCall : Bool) : List ChainItem → List (List ChainItem)
  | [] => [[]]
  | items =>
    let (first, rest) := takeFirst items
    let (first, rest) :=
      if baseIsCall then (first, rest) else
        let (more, rest) := takeMembers rest
        (first ++ more, rest)
    first :: laterGroups false [] rest
where
  /-- As many calls, and numeric index accesses, as there are. -/
  takeFirst : List ChainItem → List ChainItem × List ChainItem
    | [] => ([], [])
    | i :: rest =>
        if i.kind == .call || (i.kind == .index && i.numericIndex) then
          let (taken, rest) := takeFirst rest
          (i :: taken, rest)
        else ([], i :: rest)
  /-- Then as many member accesses as there are, but not the last one. -/
  takeMembers : List ChainItem → List ChainItem × List ChainItem
    | i :: j :: rest =>
        if i.isMemberish && j.isMemberish then
          let (taken, rest) := takeMembers (j :: rest)
          (i :: taken, rest)
        else ([], i :: j :: rest)
    | items => ([], items)
  laterGroups (seenCall : Bool) (current : List ChainItem) :
      List ChainItem → List (List ChainItem)
    | [] => if current.isEmpty then [] else [current]
    | i :: rest =>
        if seenCall && i.isMemberish && !(i.kind == .index && i.numericIndex) then
          current :: laterGroups (i.kind == .call) [i] rest
        else
          laterGroups (seenCall || i.kind == .call) (current ++ [i]) rest

/-- Whether the group that follows the head of the chain stays on the line
of the head: prettier merges it when the head is `this`, a factory, or a
short identifier at the start of a statement, or when the group starts
with a computed access. -/
def chainShouldMerge (isStatement : Bool) (base : ChainItem)
    (groups : List (List ChainItem)) : Bool :=
  let laterGroups := groups.tail
  let hasComputed :=
    match laterGroups.head? with
    | some (i :: _) => i.kind == .index
    | _ => false
  let shouldNotWrap :=
    match groups.headD [] with
    | [] =>
        base.isThis ||
          (base.identName != "" &&
            (isFactoryName base.identName ||
              (isStatement && base.identName.length ≤ tabWidth) || hasComputed))
    | g =>
        match g.getLast? with
        | some i => i.kind == .dot && (isFactoryName i.name || hasComputed)
        | none => false
  !laterGroups.isEmpty && shouldNotWrap

/-- Whether prettier lays the elements out with the member chain layout,
rather than simply writing them one after the other: it does so when more
than one group is left once the head, and the group merged into it, are
taken away. -/
def chainItemsAreMemberChain (isStatement : Bool) (items : List ChainItem) : Bool :=
  match items with
  | [] => false
  | base :: links =>
    let groups := chainGroups base.isCallBase links
    let laterGroups := groups.tail
    let cutoffGroups :=
      if chainShouldMerge isStatement base groups then laterGroups.tail else laterGroups
    cutoffGroups.length > 1

/-- Lay out a member chain.  `curried` says that the chain is a call which
is a link of a long curried chain, `a.f(x, y)(z)`: prettier then leaves a
chain short enough to be written on one line ungrouped, so that it breaks
with the call that holds it. -/
def memberChainDoc (isStatement curried : Bool) (items : List ChainItem) : Doc :=
  match items with
  | [] => .nil
  | base :: links =>
    let groups := chainGroups base.isCallBase links
    let groupDoc (g : List ChainItem) : Doc := Doc.concat (g.map (·.doc))
    let firstDoc : Doc := base.doc ++ groupDoc (groups.headD [])
    let laterGroups := groups.tail
    let shouldMerge := chainShouldMerge isStatement base groups
    let oneLine : Doc := firstDoc ++ Doc.concat (laterGroups.map groupDoc)
    let cutoffGroups := if shouldMerge then laterGroups.tail else laterGroups
    let mergedDoc : Doc :=
      if shouldMerge then groupDoc (laterGroups.headD []) else .nil
    if cutoffGroups.length ≤ 1 then (if curried then oneLine else .group oneLine)
    else
      let expanded : Doc :=
        firstDoc ++ mergedDoc
          ++ .nest indentWidth
              (.hardline ++ Doc.joinWith .hardline (cutoffGroups.map groupDoc))
      let callCount := (if base.isCallBase then 1 else 0)
        + (links.filter (·.kind == .call)).length
      let anyComplexArgs := (base.isCallBase && !base.simpleArgs)
        || links.any (fun i => i.kind == .call && !i.simpleArgs)
      let allDocs := firstDoc :: laterGroups.map groupDoc
      let earlyBreak := (allDocs.dropLast).any Doc.hasForcedBreak
      let lastGroupBreaks :=
        match laterGroups.getLast? with
        | some g =>
            (match g.getLast? with | some i => i.kind == .call | none => false)
              && Doc.hasForcedBreak (groupDoc g)
              && ((base.isCallBase && base.functionArg)
                  || (links.dropLast).any (fun i => i.kind == .call && i.functionArg))
        | none => false
      if (callCount > 2 && anyComplexArgs) || earlyBreak || lastGroupBreaks then
        .group expanded
      else
        (if Doc.hasForcedBreak oneLine then .breakParent else .nil)
          ++ .condGroup oneLine expanded

/-- Whether the expression is a call with at least one argument; the call
at the end of an optional chain counts. -/
def isCallWithArgs : MiniExpr → Bool
  | .call _ args => !args.isEmpty
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call _ args) => !args.isEmpty
      | _ => false
  | _ => false

/-- Whether prettier keeps a member access on the line of its object,
rather than letting the line break in front of the access, given what the
object of the access is.  `objIsChain` says that the object is laid out as
a member chain, which the access of an assigned chain keeps its line
for. -/
def memberInlines (pos : Pos) (objIsIdent objIsCallWithArgs objIsChain propIsIdent : Bool) :
    Bool :=
  pos == .newCallee
    -- the chain is assigned to something other than a plain identifier
    || inlineMemberRoot pos
    || (propIsIdent && objIsIdent && !isMemberObjectPos pos)
    || ((isAssignRhsPos pos || pos == .assignTarget) && (objIsCallWithArgs || objIsChain))

/-- Whether the first link of a chain is a computed access: the parentheses
that a base may need then stay tight against the `[` that follows them,
whereas a `.` access is allowed to go on a line of its own. -/
def chainStartsComputed (links : NonEmptyList MiniChainLink) : Bool :=
  match links.head with
  | .index .. => true
  | _ => false

/-- The position of the base of an optional chain that stands in `pos`:
the base is the callee of the first link when that link is a call, and
the object of a member access otherwise. -/
def chainBasePos (pos : Pos) (links : NonEmptyList MiniChainLink) : Pos :=
  match links.head with
  | .call _ args => calleePos pos args.length
  | _ =>
      -- a call among the links stands between the base and whatever holds
      -- the chain: the accesses inside the base then take a line of their
      -- own, whatever the chain is written in
      if links.toList.any chainLinkIsCall then
        .memberObject (chainStartsComputed links) (extraIndentRoot pos) false
      else memberObjectPos (chainStartsComputed links) pos

/-- The base of a member chain.  A parenthesised optional chain stands
for the expression written inside the parentheses: when that ends with a
call, the base is a call of the chain that holds it. -/
def chainBaseItem (e : MiniExpr) (d : Doc) : ChainItem :=
  let baseArgs : Option (List MiniExpr) :=
    match e with
    | .call _ args => some args
    | .chain _ links =>
        (match links.toList.getLast? with
          | some (.call _ args) => some args
          | _ => none)
    | _ => none
  { kind := .base, doc := d,
    isThis := (match e with | .this => true | _ => false),
    identName := (match e with | .ident n => n.toString | _ => ""),
    isCallBase := baseArgs.isSome,
    simpleArgs := (match baseArgs with
      | some args => args.all (isSimpleCallArgument 2)
      | none => true),
    functionArg := (match baseArgs with
      | some args => args.any isFunctionLike
      | none => false),
    hasArgs := (match baseArgs with | some args => !args.isEmpty | none => false) }

/-- One call of a member chain. -/
def chainCallItem (args : List MiniExpr) (d : Doc) : ChainItem :=
  { kind := .call, doc := d,
    simpleArgs := args.all (isSimpleCallArgument 2),
    functionArg := args.any isFunctionLike,
    hasArgs := !args.isEmpty }

/-- Split the elements of a chain after its last call: what comes before
is laid out as a member chain, and the member accesses that follow it are
laid out one by one, as prettier prints the member expressions that hold
the chain. -/
def splitAfterLastCall (items : List ChainItem) : List ChainItem × List ChainItem :=
  let rec lastCall (idx found : Nat) : List ChainItem → Nat
    | [] => found
    | i :: rest => lastCall (idx + 1) (if i.kind == .call then idx + 1 else found) rest
  let k := lastCall 0 1 items
  (items.take k, items.drop k)

/-- The elements of the links of an optional chain, without their
documents. -/
def chainLinkShapeItem : MiniChainLink → ChainItem
  | .dot _ n => { kind := .dot, name := n.toString, doc := .nil }
  | .privateDot _ n => { kind := .dot, name := n.toString, doc := .nil }
  | .index _ i => { kind := .index, numericIndex := isNumericLit i, doc := .nil }
  | .call _ args => chainCallItem args .nil

/-- The elements of the member chain whose last node is `e`, without their
documents: what the layout heuristics need in order to tell whether the
chain is one prettier lays out as a member chain. -/
def chainShapeItems : MiniExpr → List ChainItem
  | .dot o n =>
      (if isChainNode o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .dot, name := n.toString, doc := .nil }]
  | .privateDot o n =>
      (if isChainNode o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .dot, name := n.toString, doc := .nil }]
  | .index o i =>
      (if isChainNode o then chainShapeItems o else [chainBaseItem o .nil])
        ++ [{ kind := .index, numericIndex := isNumericLit i, doc := .nil }]
  | .call f args =>
      (if isChainNode f then chainShapeItems f else [chainBaseItem f .nil])
        ++ [chainCallItem args .nil]
  | .chain b links =>
      (if isChainSpine b then chainShapeItems b else [chainBaseItem b .nil])
        ++ links.toList.map chainLinkShapeItem
  | e => [chainBaseItem e .nil]

/-- Whether prettier lays the expression out with the member chain layout.
The right hand side of an assignment that it does lay out that way is not
one it breaks the line after the operator for: the chain breaks on its own
instead. -/
def printsAsMemberChain (e : MiniExpr) : Bool :=
  match e with
  | .call f _ =>
      isMemberish f
        && chainItemsAreMemberChain false (splitAfterLastCall (chainShapeItems e)).1
  | .chain _ _ =>
      chainItemsAreMemberChain false (splitAfterLastCall (chainShapeItems e)).1
  | _ => false

/-- Whether one of the calls along the spine of the expression is laid out
with the member chain layout. -/
def spineHasMemberChain : MiniExpr → Bool
  | .call f args => printsAsMemberChain (.call f args) || spineHasMemberChain f
  | .dot o _ | .privateDot o _ | .index o _ => spineHasMemberChain o
  -- the base of an optional chain may be a chain of its own, laid out
  -- with the member chain layout inside the parentheses it needs
  | .chain b links => printsAsMemberChain (.chain b links) || spineHasMemberChain b
  | _ => false

/-- Whether the document of the expression is a member chain: prettier
lays the expression out as one, or it is a member access whose object is,
which passes the member chain layout on.  -/
def docIsMemberChain : MiniExpr → Bool
  | .dot o _ | .privateDot o _ | .index o _ => docIsMemberChain o
  | e => printsAsMemberChain e

/-- Whether prettier keeps a member access on the line of its object,
rather than letting the line break in front of the access. -/
def memberAccessInlines (pos : Pos) (obj : MiniExpr) (propIsIdent : Bool) : Bool :=
  memberInlines pos (match obj with | .ident _ => true | _ => false)
    (isCallWithArgs obj) (docIsMemberChain obj) propIsIdent

/-! ## Assignments -/

/-- Whether prettier breaks the line after the `=` of an assignment whose
right hand side is `rhs`. -/
def shouldBreakAfterOperator (shortKey : Bool) (rhs : MiniExpr) : Bool :=
  match rhs with
  | .binary .. => !shouldInlineLogical rhs
  | .seq _ _ => true
  -- under `experimentalTernaries` it is a chain of conditionals, rather
  -- than an operator chain in the test, that breaks the line
  | .ternary test a b =>
      if Options.experimentalTernaries then
        (match a with | .ternary .. => true | _ => false)
          || (match b with | .ternary .. => true | _ => false)
      else isBinaryish test && !shouldInlineLogical test
  | .classExpr decorators _ _ _ => !decorators.isEmpty
  | _ =>
    if shortKey then false
    else
      let rec strip : MiniExpr → MiniExpr
        | .unary _ a => strip a
        | .await a => strip a
        | .yield (some a) => strip a
        | e => e
      let node := strip rhs
      isStringLit node ||
        (isPoorlyBreakableChain false node && !spineHasMemberChain node)

/-- The expression whose shape decides the layout of `key: value` in an
object pattern: prettier chooses that layout as it chooses the layout of
an assignment, reading the pattern as the right hand side.  A pattern
which is not a plain name or an assignment target has no layout of its
own, and `null` stands for it, since the choice is the same for every
such shape. -/
def patternLayoutExpr : MiniPattern → MiniExpr
  | .ident n => .ident n
  | .target e => e
  | _ => .null

/-- Whether the right hand side is one prettier never breaks after the
operator for. -/
def neverBreakAfterOperator (shortKey : Bool) (rhs : MiniExpr) : Bool :=
  shortKey ||
    (match rhs with
      | .template _ _ _ => true
      | .true_ | .false_ => true
      -- a `BigInt` literal is not a numeric literal to prettier, and does
      -- not keep the line of the operator
      | .number (.bigint ..) => false
      | .number _ => true
      | .classExpr .. => true
      | _ => false)

/-- Whether the expression is an assignment. -/
def isAssignExpr : MiniExpr → Bool
  | .assign .. | .assignPattern .. => true
  | _ => false

/-- Whether the expression is an arrow function whose body is another
arrow function, which the tail of a chain of assignments keeps on the line
of its operator. -/
def isArrowChainExpr : MiniExpr → Bool
  | .arrow _ _ (.expr (.arrow ..)) => true
  | _ => false

/-- The layouts prettier chooses between for an assignment, a declarator,
a property or a field. -/
inductive AssignLayout where
  /-- Break after the operator; the two sides then break on their own. -/
  | breakAfterOperator
  /-- Never break after the operator. -/
  | neverBreakAfterOperator
  /-- Keep the right hand side on the line while its first line fits. -/
  | fluid
  /-- Break the left hand side first. -/
  | breakLhs
  /-- A link of a chain of assignments: once one of them breaks, they all
  do, and the links are not indented. -/
  | chain
  /-- The last link of a chain of assignments. -/
  | chainTail
  /-- The last link of a chain of assignments, a chain of arrow functions
  that keeps the line of the operator. -/
  | chainTailArrowChain
deriving BEq, Inhabited

/-- Prettier's choice of layout.  `nodeIsAssign` says that the node is an
assignment expression, rather than a declarator, a property or a field;
`parentIsAssign` that it stands on the right of an assignment or of a
declarator; `grandparentIsStatement` that that assignment is itself an
expression statement or a declaration, which keeps a chain of two
assignments out of the chain layout.  `complexLhs` asks for the left hand
side to be broken first, and `leftCanBreak` says that the left hand side
holds a line. -/
def chooseAssignLayout (nodeIsAssign parentIsAssign grandparentIsStatement
    complexLhs leftCanBreak shortKey : Bool) (rhs : MiniExpr) : AssignLayout :=
  let isTail := !isAssignExpr rhs
  if nodeIsAssign && parentIsAssign && (!isTail || !grandparentIsStatement) then
    if !isTail then .chain
    else if isArrowChainExpr rhs then .chainTailArrowChain
    else .chainTail
  else if !isTail && (match rhs with
      | .assign _ _ r => isAssignExpr r
      | .assignPattern _ r => isAssignExpr r
      | _ => false) then
    -- the head of a chain of more than two assignments
    .breakAfterOperator
  -- `const x = require("a/long/module/path");` keeps the line of the `=`
  else if (match rhs with | .call (.ident n) _ => n.toString == "require" | _ => false) then
    .neverBreakAfterOperator
  else if complexLhs then .breakLhs
  else if shouldBreakAfterOperator shortKey rhs then .breakAfterOperator
  else if !leftCanBreak && neverBreakAfterOperator shortKey rhs then
    .neverBreakAfterOperator
  else .fluid

/-- An assignment, a declarator, a property or a field, given its layout
and the documents of its two sides. -/
def assignmentDocOf (layout : AssignLayout) (leftDoc : Doc) (op : String)
    (rightDoc : Doc) : Doc :=
  match layout with
  | .breakAfterOperator =>
      .group (.group leftDoc ++ t op ++ .group (.nest indentWidth (.line ++ rightDoc)))
  | .neverBreakAfterOperator => .group (.group leftDoc ++ t op ++ t " " ++ rightDoc)
  -- prettier's "fluid" layout: keep the right hand side on the line when
  -- its first line fits, and break after the operator otherwise
  | .fluid => .group (.group leftDoc ++ t op ++ .fluidLine indentWidth rightDoc)
  | .breakLhs => .group (leftDoc ++ t op ++ t " " ++ .group rightDoc)
  -- the links of a chain of assignments are not wrapped in groups of
  -- their own: once one of them breaks, the whole chain breaks
  | .chain => .group leftDoc ++ t op ++ .line ++ rightDoc
  | .chainTail => .group leftDoc ++ t op ++ .nest indentWidth (.line ++ rightDoc)
  | .chainTailArrowChain => .group leftDoc ++ t op ++ rightDoc

/-- An assignment, a declarator, a property or a field, given the
documents of its two sides. -/
def assignmentDoc (shortKey : Bool) (leftDoc : Doc) (op : String) (rhs : MiniExpr)
    (rightDoc : Doc) : Doc :=
  assignmentDocOf
    (chooseAssignLayout false false false false (Doc.canBreak leftDoc) shortKey rhs)
    leftDoc op rightDoc

/-- The member accesses that trail the last call of a chain, added to the
document of what comes before them. -/
def chainTrailingAux (pos : Pos) (objIsIdent objIsCall objIsChain : Bool) (acc : Doc) :
    List ChainItem → Doc
  | [] => acc
  | i :: rest =>
      let p : Pos := if rest.isEmpty then pos else memberObjectPos false pos
      let inline :=
        i.kind == .index || memberInlines p objIsIdent objIsCall objIsChain (i.kind == .dot)
      -- the member chain layout of the object carries over to the accesses
      -- that trail it
      chainTrailingAux pos false false objIsChain (memberDocOf inline acc i.doc) rest

/-- Lay out an optional chain, given its elements.  A chain that holds no
call at all is not a member chain to prettier, which prints it as the
member accesses it is made of: the accesses are not grouped together, so
that the chain does not have to be laid out flat as a whole. -/
def chainAssemble (pos : Pos) (items : List ChainItem) : Doc :=
  let (head, trailing) := splitAfterLastCall items
  let noCalls := !items.any (fun i => i.kind == .call || i.isCallBase)
  let headDoc := memberChainDoc (pos == .statement && trailing.isEmpty) noCalls head
  if trailing.isEmpty then headDoc
  else
    let objIsIdent :=
      head.length == 1 && (match head.head? with | some i => i.identName != "" | none => false)
    let objIsCall :=
      match head.getLast? with
      | some i => (i.kind == .call || i.isCallBase) && i.hasArgs
      | none => false
    chainTrailingAux pos objIsIdent objIsCall
      (chainItemsAreMemberChain false head) headDoc trailing

/-- Whether the last link of an optional chain is a member access rather
than a call. -/
def chainEndsInMember (links : NonEmptyList MiniChainLink) : Bool :=
  match links.toList.getLast? with
  | some (.call ..) => false
  | _ => true

/-- Whether prettier indents the substitution of a template literal that
it has to break. -/
def templateSubstIndents : MiniExpr → Bool
  | .ident _ | .dot .. | .privateDot .. | .index .. | .ternary .. | .seq _ _
  | .binary .. => true
  | .chain _ links => chainEndsInMember links
  | _ => false

/-! ## Arguments that may be hugged -/

/-- A tag that tells the kinds of expression apart. -/
def nodeTag : MiniExpr → Nat
  | .ident _ => 0 | .number _ => 1 | .string _ => 2 | .regex _ => 3
  | .null => 4 | .true_ => 5 | .false_ => 6 | .this => 7
  | .superDot _ => 8 | .superIndex _ => 9 | .superCall _ => 10
  | .newTarget => 11 | .array _ => 12 | .object _ => 13
  | .assign .. => 14 | .assignPattern .. => 15 | .await _ => 16
  | .call .. => 17 | .dot .. => 18 | .privateDot .. => 19
  | .privateName _ => 20 | .index .. => 21 | .chain .. => 22
  | .importMeta => 23 | .importCall .. => 24 | .classExpr .. => 25
  | .seq .. => 26 | .binary .. => 27 | .postfix .. => 28 | .ternary .. => 29
  | .arrow .. => 30 | .func .. => 31 | .new .. => 32 | .spread _ => 33
  | .template .. => 34 | .unary .. => 35 | .yield _ => 36 | .yieldFrom _ => 37
  | .jsx _ => 38

/-- Whether the argument is one prettier may expand in place, keeping the
rest of the call on one line.  `inChain` says that the argument is the
body of an arrow function that is itself such an argument, where a
conditional or a call does not count. -/
def couldExpandArg (inChain : Bool) : MiniExpr → Bool
  | .object (_ :: _) => true
  | .array (_ :: _) => true
  | .func .. => true
  | .arrow _ _ body =>
      match body with
      | .block _ => true
      | .expr e =>
        match e with
        | .object _ | .array _ | .jsx _ => true
        | .arrow .. => couldExpandArg true e
        | .ternary .. | .call .. => !inChain
        -- an optional chain that ends in a call is a call too
        | .chain _ links =>
            !inChain && (match links.toList.getLast? with
              | some (.call ..) => true
              | _ => false)
        | _ => false
  | _ => false

/-- Prettier's `isHopefullyShortCallArgument`, the test the second
argument of a call has to pass for its first argument to be hugged. -/
def isHopefullyShortCallArgument (e : MiniExpr) : Bool :=
  match e with
  | .call _ args => args.length ≤ 1 && isSimpleCallArgument 2 e
  | .new _ args => args.length ≤ 1 && isSimpleCallArgument 2 e
  -- a chain that ends in a call is a call too
  | .chain _ links =>
      (match links.toList.getLast? with
        | some (.call _ args) => args.length ≤ 1
        | _ => true)
      && isSimpleCallArgument 2 e
  | .importCall _ options => options.isNone && isSimpleCallArgument 2 e
  | .binary l _ r => isSimpleCallArgument 1 l && isSimpleCallArgument 1 r
  | .regex _ => true
  | _ => isSimpleCallArgument 2 e

/-- Whether the first argument of a call may be hugged: the call takes a
function and one short second argument, as in `setTimeout(() => {…}, 0)`. -/
def canHugFirstArg (args : List MiniExpr) : Bool :=
  match args with
  | [first, second] =>
      (match first with
        | .func .. => true
        | .arrow _ _ (.block _) => true
        | _ => false)
      && (match second with
          | .func .. | .arrow .. | .ternary .. => false
          | _ => true)
      && isHopefullyShortCallArgument second
      && !couldExpandArg false second
  | _ => false

/-- The arguments of a call, of a `new` or of the call at the end of an
optional chain. -/
def callArgumentsOf : MiniExpr → Option (List MiniExpr)
  | .call _ args => some args
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.call _ args) => some args
      | _ => none
  | _ => none

/-- Whether the arguments are those of a composition of functions, as in
`pipe(map((x) => x), filter((x) => y))`: more than one of them is a
function, or one of them is a call that takes a function.  Prettier always
breaks such an argument list. -/
def isFunctionCompositionArguments (args : List MiniExpr) : Bool :=
  args.length > 1 && go 0 args
where
  go (count : Nat) : List MiniExpr → Bool
    | [] => false
    | a :: rest =>
        if isFunctionLike a then count ≥ 1 || go (count + 1) rest
        else
          match callArgumentsOf a with
          | some cargs => cargs.any isFunctionLike || go count rest
          | none => go count rest

/-- Whether the expression is a numeric literal which is not a `BigInt`
one; prettier treats the two as different kinds of literal. -/
def isPlainNumberLit : MiniExpr → Bool
  | .number (.bigint ..) => false
  | .number _ => true
  | _ => false

/-- Whether every element of the array is a number, possibly signed.  A
`BigInt` literal is not a number here, and neither is a hole. -/
def isNumberArray (els : List MiniArrayElement) : Bool :=
  !els.isEmpty && els.all (fun e =>
    match e with
    | .elem (.unary op e) => (op == .plus || op == .minus) && isPlainNumberLit e
    | .elem e => isPlainNumberLit e
    | _ => false)

/-- Whether prettier fills the lines with the elements of the array
instead of putting one element on each line: it does so when the array
holds more than one element and every one of them is a number, possibly
signed. -/
def isConciselyPrintedArray (els : List MiniArrayElement) : Bool :=
  els.length > 1 && isNumberArray els

/-- Whether the last argument of a call may be hugged. -/
def canHugLastArg (args : List MiniExpr) : Bool :=
  match args.reverse with
  | [] => false
  | last :: rest =>
      couldExpandArg false last
        && (match rest with
            | [] => true
            | p :: _ => nodeTag p != nodeTag last)
        && !(args.length == 2
              && (match rest with
                  | .arrow .. :: _ => true
                  | _ => false)
              && (match last with | .array _ => true | _ => false))
        -- `f(a, [1, 2, 3])`: an array of numbers, which the layout fills,
        -- is not hugged when it is not the only argument
        && !(args.length > 1
              && (match last with | .array els => isNumberArray els | _ => false))

/-- Whether the arguments are those of a call of a React hook with a
dependency array, as `useEffect(() => { ... }, [a, b])` and
`useImperativeHandle(ref, () => { ... }, [a, b])` are, which prettier
writes as it finds them. -/
def isHookCallWithDepsArray (args : List MiniExpr) : Bool :=
  let callbackAndDeps (fn deps : MiniExpr) : Bool :=
    (match fn with | .arrow _ [] (.block _) => true | _ => false)
      && (match deps with | .array _ => true | _ => false)
  match args with
  | [fn, deps] => callbackAndDeps fn deps
  | [first, fn, deps] =>
      (match first with | .ident _ => true | _ => false) && callbackAndDeps fn deps
  | _ => false

/-! ## The calls prettier keeps on one line -/

/-- The dotted name a callee is written with, as `require.resolve`;
`none` when the callee is not a chain of plain names. -/
def dottedCalleeName : MiniExpr → Option String
  | .ident n => some n.toString
  | .importMeta => some "import.meta"
  | .dot o n => (dottedCalleeName o).map (fun s => s ++ "." ++ n.toString)
  | _ => none

/-- Whether the callee is written with one of `names`. -/
def calleeNamed (names : List String) (callee : MiniExpr) : Bool :=
  match dottedCalleeName callee with
  | some s => names.contains s
  | none => false

/-- `require("mod")` and the other calls which ask for a module by name. -/
def isRequireLikeCall (callee : MiniExpr) (args : List MiniExpr) : Bool :=
  match args with
  | [a] => isStringLit a && calleeNamed requireLikeNames callee
  | _ => false

/-- A module definition of CommonJS or of AMD: `require` of several
arguments, and the `define` of a module, which only stands as a statement
of its own. -/
def isModuleDefinitionCall (parentIsStatement : Bool) (callee : MiniExpr)
    (args : List MiniExpr) : Bool :=
  match callee with
  | .ident n =>
      if n.toString == "require" then
        (match args with | [a] => isStringLit a | _ => args.length > 1)
      else if n.toString == "define" && parentIsStatement then
        (match args with
          | [_] => true
          | [.array _, _] => true
          | [a, .array _, _] => isStringLit a
          | _ => false)
      else false
  | _ => false

/-- One of the names an Angular test is wrapped in. -/
def isAngularWrapperName : MiniExpr → Bool
  | .ident n =>
      n.toString == "async" || n.toString == "inject" || n.toString == "fakeAsync" || n.toString == "waitForAsync"
  | _ => false

/-- A call of one of the wrappers an Angular test is written with. -/
def isAngularTestWrapper : MiniExpr → Bool
  | .call callee _ => isAngularWrapperName callee
  | _ => false

/-- `beforeEach` and the other names a test framework sets a test up
with. -/
def isUnitTestSetupName : MiniExpr → Bool
  | .ident n =>
      n.toString == "beforeEach" || n.toString == "beforeAll" || n.toString == "afterEach"
        || n.toString == "afterAll"
  | _ => false

/-- A function expression or an arrow function. -/
def isFunctionOrArrowExpr : MiniExpr → Bool
  | .func .. | .arrow .. => true
  | _ => false

/-- A function expression, or an arrow function whose body is a block. -/
def isFunctionOrArrowWithBlock : MiniExpr → Bool
  | .func .. => true
  | .arrow _ _ (.block _) => true
  | _ => false

/-- The number of parameters of a function expression or an arrow. -/
def exprParamCount : MiniExpr → Nat
  | .func _ _ _ ps _ => ps.length
  | .arrow _ ps _ => ps.length
  | _ => 0

/-- Whether the expression is the name a test is given: a string literal
or a template literal. -/
def isTestName : MiniExpr → Bool
  | .string _ => true
  | .template none _ _ => true
  | _ => false

/-- Whether the call is one of a test framework, as `it("name", () => {})`
and `beforeEach(inject(f))` are.  `parentIsTest` says that the call is an
argument of a test call, where the wrapper an Angular test is written with
is one as well. -/
def isTestCallOf (parentIsTest : Bool) (callee : MiniExpr) (args : List MiniExpr) : Bool :=
  match args with
  | [a] =>
      (isUnitTestSetupName callee && isAngularTestWrapper a)
        || (parentIsTest && isAngularWrapperName callee && isFunctionOrArrowExpr a)
  | [a, b] =>
      isTestName a && calleeNamed testCallNames callee
        && (isFunctionOrArrowExpr b || isAngularTestWrapper b)
  | [a, b, c] =>
      isTestName a && calleeNamed testCallNames callee && isNumericLit c
        && ((isFunctionOrArrowWithBlock b && exprParamCount b ≤ 1) || isAngularTestWrapper b)
  | _ => false

/-- Whether prettier writes the arguments of the call on the line of the
call, however long they are.  `parentIsStatement` says that the call is an
expression statement of its own, which only the `define` of an AMD module
asks about. -/
def callArgsStayOnLine (parentIsStatement parentIsTest : Bool) (callee : MiniExpr)
    (args : List MiniExpr) : Bool :=
  isRequireLikeCall callee args || isModuleDefinitionCall parentIsStatement callee args
    || isTestCallOf parentIsTest callee args

/-- Can this expression stand inside the callee of a `new`, as the object
a property is read off, without parentheses around the whole callee?  It
has to be a member expression that does not itself contain a call; a JSX
element standing there takes parentheses of its own. -/
def newCalleeObjOk : MiniExpr → Bool
  -- a call inside the callee would be read as the call of the `new`
  | .call .. | .superCall .. | .importCall .. | .chain .. => false
  | .dot o _ => newCalleeObjOk o
  | .privateDot o _ => newCalleeObjOk o
  | .index o _ => newCalleeObjOk o
  | .template (some tag) _ _ => newCalleeObjOk tag
  -- an operator binds less tightly than `new`, so it keeps its parentheses
  | .postfix .. | .unary .. | .await _ | .yield _ | .yieldFrom _ | .spread _
  | .arrow .. | .func .. | .classExpr .. | .assign .. | .assignPattern ..
  | .seq _ _ | .binary .. | .ternary .. => false
  | _ => true

/-- Can this expression be the callee of a `new` without parentheses? -/
def newCalleeOk : MiniExpr → Bool
  -- `new (<div />)()`: an element written as the callee itself is
  -- parenthesised, as prettier parenthesises it everywhere a tag may not
  -- stand alone
  | .jsx _ => false
  | e => newCalleeObjOk e

/-- Would printing `op` directly in front of `e` run the two operators
together, as `-` in front of `-1` would give `--1`? -/
def unaryClash (op : UnaryOp) (e : MiniExpr) : Bool :=
  match e with
  | .unary op' _ =>
      let plusLike (o : UnaryOp) := o == .plus || o == .preIncr
      let minusLike (o : UnaryOp) := o == .minus || o == .preDecr
      (plusLike op && plusLike op') || (minusLike op && minusLike op')
  | _ => false

/-- Whether an expression needs parentheses around the whole of it when it
is printed as a statement.  An object literal, a function or a class
expression at the start of the statement is parenthesised on its own, by
`inPosStart`. -/
def needsStatementParens : MiniExpr → Bool
  | .call f _ => needsStatementParens f
  | .dot o _ | .privateDot o _ | .index o _ | .postfix o _ | .chain o _ =>
      needsStatementParens o
  | .binary l _ _ | .assign l _ _ => needsStatementParens l
  | .ternary c _ _ => needsStatementParens c
  | .template (some tag) _ _ => needsStatementParens tag
  | _ => false

/-- Whether the last parameter is a rest parameter, which forbids the
trailing comma. -/
def restLast (params : List MiniParam) : Bool :=
  match params.getLast? with
  | some (.rest _) => true
  | _ => false

/-- Whether the statement is a block. -/
def isBlockStmt : MiniStatement → Bool
  | .block _ => true
  | _ => false

/-- Whether the statement is a string literal on its own, which is a
directive where a program or a function body starts. -/
def isStringStmt : MiniStatement → Bool
  | .expr (.string _) => true
  | _ => false

/-- Whether the statement is the empty statement, `;`. -/
def isEmptyStmt : MiniStatement → Bool
  | .empty => true
  | _ => false

/-- Whether the statement is an `if`. -/
def isIfStmt : MiniStatement → Bool
  | .if_ .. => true
  | _ => false

/-- Whether the body holds no statement but `;`, which prettier drops. -/
def bodyIsEmpty (body : List MiniStatement) : Bool := body.all isEmptyStmt

/-- The width of a property key, when it prints as plain text. -/
def keyTextWidth : MiniPropertyName → Option Nat
  | .ident n => some (Doc.stringWidth n.toString)
  | .private_ n => some (Doc.stringWidth n.toString + 1)
  | .number n => some (Doc.stringWidth n.render)
  | .string v =>
      if isIdentifierName v then some (Doc.stringWidth v)
      else some (Doc.stringWidth (strLit v))
  | .computed _ => none

/-- A logical expression whose right operand is a non-empty object or
array literal is kept on one line. -/
def shouldInlineLogicalOf (op : BinOp) (r : MiniExpr) : Bool :=
  isLogicalOp op &&
    (match r with
      | .object (_ :: _) => true
      | .array (_ :: _) => true
      | .jsx _ => true
      | _ => false)

/-- Whether the element is an array or an object literal of more than one
item, and which of the two it is. -/
def arrayElemKind : MiniArrayElement → Option (Bool × Nat)
  | .elem (.array xs) => some (true, xs.length)
  | .elem (.object ps) => some (false, ps.length)
  | _ => none

/-- Whether every element is an array, or every element is an object, each
of more than one item; prettier then breaks the array. -/
def allElemsAreMultiItem : Option Bool → List MiniArrayElement → Bool
  | _, [] => true
  | k, e :: rest =>
      match arrayElemKind e with
      | none => false
      | some (isArr, n) =>
          n > 1 && (match k with | none => true | some k' => k' == isArr)
            && allElemsAreMultiItem (some isArr) rest

/-- An array literal, given the documents of its elements. -/
def arrayDocOf (els : List MiniArrayElement) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let lastIsHole := match els.getLast? with
      | some .hole => true
      | _ => false
    -- an elision at the end needs its comma in both layouts
    let trailer : Doc :=
      if lastIsHole then t ","
      else if Options.hasTrailingComma .es5 then .ifBreak (t ",") .nil else .nil
    let body : Doc :=
      if isConciselyPrintedArray els then
        -- the trailing comma is part of the last element, and it is
        -- written exactly when the array itself breaks
        if lastIsHole then .fill (fillParts (t ",") items)
        else if Options.hasTrailingComma .es5 then
          .ifBreak (.fill (fillParts (t ",") items)) (.fill (fillParts .nil items))
        else .fill (fillParts .nil items)
      else Doc.joinWith (t "," ++ .line) items ++ trailer
    let contents := t "[" ++ .nest indentWidth (.softline ++ body) ++ .softline ++ t "]"
    if els.length > 1 && allElemsAreMultiItem none els then .groupBreak contents
    else .group contents

/-- An array pattern, given the documents of its elements. -/
def arrayPatternDocOf (els : List MiniArrayPatternElem) (items : List Doc) : Doc :=
  if els.isEmpty then t "[]"
  else
    let trailer : Doc := match els.getLast? with
      | some .hole => t ","
      | some (.rest _) => Doc.nil
      | _ => if Options.hasTrailingComma .es5 then .ifBreak (t ",") .nil else .nil
    .group (t "[" ++ .nest indentWidth
      (.softline ++ Doc.joinWith (t "," ++ .line) items ++ trailer) ++ .softline ++ t "]")

/-- Whether prettier forces an object pattern to break: one of its
properties destructures into a pattern of its own. -/
def objectPatternForcesBreak : List MiniObjectPatternProp → Bool
  | [] => false
  | ⟨_, value⟩ :: rest =>
      (match value with
        | .object .. | .array .. => true
        | _ => false)
      || objectPatternForcesBreak rest

/-- May the property `key: value` of an object pattern be written in the
short form, as `{ a }` or `{ a = 1 }`? -/
def patternShorthand (key : MiniPropertyName) (value : MiniPattern) : Bool :=
  match key, value with
  | .ident k, .ident v => k == v
  | .ident k, .withDefault (.ident v) _ => k == v
  | _, _ => false

/-- Whether prettier breaks the left hand side of a declarator or of a
destructuring assignment first: it destructures more than two properties
and one of them is written out, or has a default value. -/
def patternIsComplexDestructuring : MiniPattern → Bool
  | .object props _ =>
      props.length > 2 && props.any (fun p =>
        !patternShorthand p.key p.value
          || (match p.value with | .withDefault .. => true | _ => false))
  | _ => false

/-- A class body, given the documents of its members. -/
def classBodyOf (body : List MiniClassElement) (items : List Doc) : Doc :=
  if body.isEmpty then t "{}"
  else
    t "{" ++ .nest indentWidth (.hardline ++ Doc.joinWith .hardline items)
      ++ .hardline ++ t "}"

/-- Whether the superclass of a class is a property read.  Prettier writes
the `extends` of such a class on a line of its own when the header does
not fit; the `extends` of a call, or of a plain name, stays where it is. -/
def heritageIsMember : MiniExpr → Bool
  | .dot .. | .privateDot .. | .index .. => true
  | .chain _ links =>
      match links.toList.getLast? with
      | some (.dot ..) | some (.privateDot ..) | some (.index ..) => true
      | _ => false
  | _ => false

/-- A class, given the documents of its decorators, of its heritage clause
and of its members.  `ownLine` says that prettier writes the `extends` on
a line of its own when the header does not fit, which it does when the
superclass is a property read; the brace of a non-empty body then stands
on a line of its own too. -/
def classDocOf (decorators : List Doc) (name : Option NonEmptyString) (ownLine : Bool)
    (heritage : Doc) (body : List MiniClassElement) (items : List Doc) : Doc :=
  let nameDoc := match name with | none => Doc.nil | some n => t (" " ++ n.toString)
  let bodyDoc := classBodyOf body items
  let headDoc :=
    if ownLine then
      let broken :=
        nameDoc ++ .nest indentWidth (.hardline ++ t "extends " ++ .group heritage)
          ++ (if body.isEmpty then t " " else .hardline)
      if heritage.hasForcedBreak then broken
      else .condGroup (nameDoc ++ t " extends " ++ heritage ++ t " ") broken
    else nameDoc ++ t " extends " ++ heritage ++ t " "
  classDecoratorsPrefix decorators
    ++ t "class"
    ++ (match heritage with
        | .nil => nameDoc ++ t " "
        | _ => headDoc)
    ++ bodyDoc

/-- A function, given the documents of its parameters and of its body.
`hugParams` says that the function is an argument the layout expands in
place, where prettier puts the whole parameter list on one line. -/
def functionDocOf (hugParams isAsync isGen : Bool) (name : Option NonEmptyString)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  let paramsDoc :=
    let d := paramsDocOf (shouldHugTheOnlyParameter params) (restLast params) paramItems
    if hugParams then Doc.removeLines d else d
  t (if isAsync then "async function" else "function")
    ++ t (if isGen then "*" else "")
    ++ (match name with | none => t " " | some n => t (" " ++ n.toString))
    ++ paramsDoc ++ t " "
    ++ blockDocOf true (bodyIsEmpty body) bodyInner

/-- A method, given the documents of its name, its parameters and its
body. -/
def methodDocOf (kind : MethodKind) (key : Doc)
    (params : List MiniParam) (paramItems : List Doc)
    (body : List MiniStatement) (bodyInner : Doc) : Doc :=
  let prefix_ := match kind with
    | .normal => ""
    | .generator => "*"
    | .async => "async "
    | .asyncGenerator => "async *"
    | .get => "get "
    | .set => "set "
  t prefix_ ++ key ++ paramsDocOf (shouldHugTheOnlyParameter params) (restLast params) paramItems ++ t " "
    ++ blockDocOf true (bodyIsEmpty body) bodyInner

/-- Whether the right operand continues a chain of the same logical
operator.  Prettier rebalances `a && (b && c)` into `(a && b) && c` before
it lays it out, so that the operands of such a chain are laid out
together. -/
def rightContinuesLogicalChain (op : BinOp) : MiniExpr → Bool
  | .binary _ rop _ => isLogicalOp op && rop == op
  | _ => false

/-- The first operand of a chain of the same logical operator that leans
to the right: the operand that follows the operator of the chain once it
is rebalanced, and whose shape says whether the line may break in front of
it. -/
def logicalFirstOperand (op : BinOp) : MiniExpr → MiniExpr
  | .binary l rop r =>
      if isLogicalOp op && rop == op then logicalFirstOperand op l else .binary l rop r
  | e => e

/-- Whether the left operand is a chain of the same precedence, to be
flattened into the operator chain of its parent. -/
def shouldFlattenLeft (op : BinOp) : MiniExpr → Bool
  | .binary _ lop _ => shouldFlatten op lop
  | _ => false

/-- The operator and the right operand of a binary expression, given the
document of the operand. -/
def binaryTailWith (parentKind : BinKind) (insideParens : Bool)
    (l : MiniExpr) (op : BinOp) (r : MiniExpr) (rightDoc : Doc) : List Doc :=
  let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
  -- the operand the line would break in front of is the first one of
  -- the right hand chain, since prettier rebalances the chain
  let inline := shouldInlineLogicalOf op (logicalFirstOperand op r)
  let right : Doc := binOpTail op inline rightDoc
  let shouldGroup :=
    !(insideParens && nodeKind == .logical)
      && parentKind != nodeKind
      && binKind l != nodeKind
      && binKind r != nodeKind
  [binOpLead inline, if shouldGroup then .group right else right]

/-- The kind of the parent of a binary expression in this position. -/
def parentBinKind : Pos → BinKind
  | .binOperand pop _ => if isLogicalOp pop then .logical else .arith
  | _ => .other

/-- A binary expression, laid out according to its position, given the
documents of its operator chain. -/
def binaryLayoutWith (pos : Pos) (l : MiniExpr) (op : BinOp) (r : MiniExpr)
    (parts : List Doc) : Doc :=
  if pos == .ifTest then Doc.concat parts
  -- the operands of a chain of the same logical operator that leans to
  -- the right belong to the chain of the parent: prettier rebalances the
  -- chain, which leaves them neither grouped nor indented again
  else if (match pos with
      | .binOperand pop false => isLogicalOp op && pop == op
      | _ => false) then
    Doc.concat parts
  else
    match pos with
    -- `(\n  a &&\n  b\n).call()`: a binary expression breaks between the
    -- parentheses in the callee of a call, in the operand of a unary
    -- operator and in the object of a `.` access, but not in the object of
    -- a `[ ]` access
    | .callee .. | .unaryArg | .memberObject false .. =>
        .group (.nest indentWidth (.softline ++ Doc.concat parts) ++ .softline)
    | _ =>
      let shouldNotIndent :=
        pos == .returnThrow || pos == .arrowBody || pos == .forHeadPart
          || pos == .forTest
          || (isTernaryPos pos && !ternaryOuterIndents pos)
          || pos == .templateSubst
          -- the `{ }` of an attribute of a JSX element indents already
          || pos == .jsxAttrExpr
      let shouldIndentIfInlining :=
        isAssignRhsPos pos || (match pos with | .propValue false _ => true | _ => false)
      -- the checks are those of the rebalanced chain, whose right hand
      -- operand is the last one of the chain and whose left hand operand
      -- is the rest of it
      let inline := shouldInlineLogicalOf op (logicalLastOperand op r)
      let samePrecedenceSub :=
        rightContinuesLogicalChain op r ||
          match l with
          | .binary _ lop _ => shouldFlatten op lop
          | _ => false
      if shouldNotIndent || (inline && !samePrecedenceSub)
          || (!inline && shouldIndentIfInlining) then
        .group (Doc.concat parts)
      -- a JSX element written as the last operand stands outside the
      -- chain, which lets the operands before it hold one line while the
      -- element is written over several, and is indented again only where
      -- that chain does break
      else if isJsxExpr (logicalLastOperand op r) && parts.length > 1 then
        let init := parts.dropLast
        let chain :=
          Doc.concat (init.take 1) ++ .nest indentWidth (Doc.concat (init.drop 1))
        .group (.groupIndentIfBreak indentWidth chain (parts.getLastD .nil) .nil)
      else
        .group (Doc.concat (parts.take 1) ++ .nest indentWidth (Doc.concat (parts.drop 1)))


end Printer

end Language.JavaScript.MiniAST
