import LanguageJavascriptMini.PrinterSupport
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
# The printer

A printer for `MiniAST` that reproduces the output of the `prettier` code
formatter.  It is read as a `Language.JavaScript.Options`, prettier's
options record, which every function of the printer takes as an instance
argument; `Language.JavaScript.defaultOptions` is prettier's default
style (two space indentation, eighty column lines, double quotes,
semicolons and trailing commas).

The layout decisions follow prettier's: the precedence-and-clarity
parenthesisation rules, the flattening of binary operator chains, the
assignment layouts, the member chain layout, and the hugging of a final
function argument.
-/

namespace Language.JavaScript.MiniAST

open Language.JavaScript.Doc
open Language.JavaScript.PrinterCommon
open Language.JavaScript.JSXLayout

namespace Printer

variable [o : Options]

/-! ## The printing context -/

/-- Whether the expression applies the `in` operator. -/
def isInOperator : MiniExpr → Bool
  | .binary _ .inOp _ => true
  | _ => false

/-- What the printer has to know about the place the tree it walks stands
in.  The head of a `for (;;)` is read with the `in` operator ruled out, so
prettier parenthesises every `in` written anywhere inside it, however deep;
`inForInit` says that this is such a place.  Since the printer of a head is
the very printer being defined, it is passed here as `forInit`. -/
structure PrintCtx where
  /-- Whether this stands inside the first clause of a `for (;;)`. -/
  inForInit : Bool
  /-- How the first clause of a `for (;;)` is printed. -/
  forInit : MiniForInit → Doc

section

variable (ctx : PrintCtx)

-- the printer is one large mutual block; elaborating it takes more than
-- the default budget
set_option maxHeartbeats 1000000 in
mutual

/-- Whether the expression has to be parenthesised in this position.  An
`in` operator in the head of a `for (;;)` always is. -/
def needsParensC (pos : Pos) (e : MiniExpr) : Bool :=
  needsParens pos e || (ctx.inForInit && isInOperator e)

/-- An expression in position `pos`, given the document it prints as. -/
def inPosC (pos : Pos) (e : MiniExpr) (d : Doc) : Doc := parenIfExpr (needsParensC pos e) e d

/-- An expression in position `pos`, where `atStart` says what it is the
leftmost part of, so that an object literal, a function or a class
expression there needs parentheses. -/
def inPosStartC (atStart : StartCtx) (pos : Pos) (e : MiniExpr) (d : Doc) : Doc :=
  parenIfExpr (needsParensC pos e || cannotStartWith atStart pos e) e d

/-- The statements of one `case` of a `switch`, given their documents. -/
def caseBodyWith (body : List MiniStatement) (docs : List Doc) : Doc :=
  match body.filter (fun s => !isEmptyStmt s) with
  | [] => Doc.nil
  | [.block _] => t " " ++ Doc.joinWith .hardline docs
  | _ => .nest indentWidth (.hardline ++ Doc.joinWith .hardline docs)

/-- The condition of an `if`, a `while` or a `do ... while`, given the
document of the condition itself. -/
def conditionWith (e : MiniExpr) (d : Doc) : Doc :=
  let inline :=
    match e with
    -- `if (!(a || b))` is kept as it is
    | .unary .not (.binary _ op _) => isLogicalOp op
    | .unary .not (.unary .not (.binary _ op _)) => isLogicalOp op
    | _ => false
  if inline then d else .group (.nest indentWidth (.softline ++ d) ++ .softline)

/-- The body attached to the head of a statement, given its document. -/
def bodyClauseWith (s : MiniStatement) (d : Doc) : Doc :=
  clauseDoc (isBlockStmt s) (isEmptyStmt s) d

/-- The argument of a `return` or a `throw`, given its document. -/
def returnArgWith (e : MiniExpr) (d : Doc) : Doc :=
  match e with
  -- under `experimentalTernaries` a chain of conditionals keeps the
  -- parentheses of a broken operator chain
  | .ternary _ a b =>
      if Options.experimentalTernaries
          && ((match a with | .ternary .. => true | _ => false)
              || (match b with | .ternary .. => true | _ => false)) then
        .group (.ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d)
          ++ .softline ++ .ifBreak (t ")") .nil)
      else d
  | .binary .. =>
      .group (.ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d)
        ++ .softline ++ .ifBreak (t ")") .nil)
  | _ => d

/-- An expression, without the parentheses its position may require. -/
def exprCore (atStart : StartCtx) (pos : Pos) : MiniExpr → Doc
  | .ident n => t n.toString
  | .number n => t n.render
  | .string v => t (strLit v)
  | .regex r => t r.render
  | .null => t "null"
  | .true_ => t "true"
  | .false_ => t "false"
  | .this => t "this"
  | .newTarget => t "new.target"
  | .importMeta => t "import.meta"
  | .privateName n => t ("#" ++ n.toString)
  -- `super` is not an identifier, so prettier lets the line break in
  -- front of the access as it does for any other object
  | .superDot n =>
      -- the access that a call is made on is laid out as a chain, whose
      -- one link stays on the line of `super`
      let called := match pos with | .callee .. => true | _ => false
      memberDocOf (called || memberInlines pos false false false true)
        (t "super") (t ("." ++ n.toString))
  | .superIndex i =>
      t "super"
        ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i))
  | .superCall args =>
      t "super" ++ argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none false args) (argHugDocs .none false args)
  | .array els => arrayDocOf els (arrayItemDocs els)
  | .object props => sepList "{" "}" true .es5 (propertyDocsOf (quoteAllProps props) props)
  | .assign l op r =>
      -- the right hand side of an assignment that is not a statement of
      -- its own is a link of a chain of assignments; one of an assignment
      -- whose left hand side is not a plain identifier keeps its member
      -- accesses on the line of their object
      let leftIsIdent := match l with | .ident _ => true | _ => false
      let grandparentIsStatement := match pos with | .assignRhs n _ _ _ => !n | _ => false
      let leftDoc := inPosStartC atStart .assignTarget l (exprCore atStart .assignTarget l)
      let layout :=
        chooseAssignLayout true (isAssignRhsPos pos) grandparentIsStatement false
          (Doc.canBreak leftDoc) false r
      let rhsPos : Pos :=
        .assignRhs (pos != .statement) (!leftIsIdent) true (layout == .chainTailArrowChain)
      assignmentDocOf layout
        leftDoc (" " ++ assignOpText op) (inPosC rhsPos r (exprCore .none rhsPos r))
  | .assignPattern l r =>
      let leftDoc := assignTargetPatternDoc l
      let grandparentIsStatement := match pos with | .assignRhs n _ _ _ => !n | _ => false
      let layout :=
        chooseAssignLayout true (isAssignRhsPos pos) grandparentIsStatement
          (patternIsComplexDestructuring l) (Doc.canBreak leftDoc) false r
      let rhsPos : Pos :=
        .assignRhs (pos != .statement) true true (layout == .chainTailArrowChain)
      assignmentDocOf layout leftDoc " =" (inPosC rhsPos r (exprCore .none rhsPos r))
  | .await e =>
      let inner := t "await " ++ inPosC .awaitArg e (exprCore .awaitArgument .awaitArg e)
      if awaitBreaksInParens pos then
        -- the parentheses break with the line the `await` stands on; when
        -- the `await` itself opens the operand of another one, prettier
        -- leaves the decision to the line that holds them both
        let parts := Doc.nest indentWidth (.softline ++ inner) ++ .softline
        if atStart == .awaitArgument then parts else .group parts
      else inner
  | .call f args =>
      -- a `require` of a module, a module definition and a call of a test
      -- framework keep their arguments on the line of the call
      let parentIsTest := pos == .testCallArg
      let stay := callArgsStayOnLine (pos == .statement) parentIsTest f args
      -- an argument of a call written directly in a `{ }` of a JSX
      -- element is marked, so that a JSX element which is the body of an
      -- arrow function written here keeps its own lines
      let ast : StartCtx := if pos == .jsxChildExpr || pos == .jsxAttrExpr then .jsxCallArg else .none
      -- prettier asks whether the call is a test call without looking at
      -- the call that holds it when it decides that the parameters of a
      -- function argument stay on one line, so the function written
      -- inside an Angular wrapper keeps an ordinary parameter list
      let docs :=
        if isTestCallOf false f args then testArgDocs ast args else argDocs ast args
      let argsDoc := argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (stay || isHookCallWithDepsArray args) (isFunctionCompositionArguments args)
        (canHugFirstArg args)
        (canHugLastArg args) docs (argHugFirstDocs ast false args) (argHugDocs ast false args)
      if isMemberish f && !stay then
        memberChainDoc (pos == .statement) (isLongCurriedCall pos args.length)
          (chainItemsOf (calleePos pos args.length) atStart false true f
            ++ [chainCallItem args argsDoc])
      else
        let cpos := calleePos pos args.length
        let whole := inPosStartC atStart cpos f (exprCore atStart cpos f) ++ argsDoc
        -- a call of a call is grouped as a whole, so that the argument
        -- list of the callee, which is left ungrouped when the call is a
        -- link of a curried chain, breaks with the line they share
        if isCallLikeExpr f then .group whole else whole
  | .dot o n =>
      let opos := memberObjectPos false pos
      memberDocOf (memberAccessInlines pos o true)
        (inPosStartC atStart opos o (exprCore atStart opos o))
        (t ("." ++ n.toString))
  | .privateDot o n =>
      let opos := memberObjectPos false pos
      memberDocOf (memberAccessInlines pos o false)
        (inPosStartC atStart opos o (exprCore atStart opos o))
        (t (".#" ++ n.toString))
  | .index o i =>
      let opos := memberObjectPos true pos
      inPosStartC atStart opos o (exprCore atStart opos o)
        ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i))
  | .chain base links =>
      let bpos := chainBasePos pos links
      chainAssemble pos
        ((if isChainSpine base then
            chainItemsOf bpos atStart (chainMergesBase links)
              (links.toList.any chainLinkIsCall) base
          else [chainBaseItem base (inPosStartC atStart bpos base
                  (exprCore atStart bpos base))])
          ++ chainLinkItemsNE
              -- the call at the end of a chain written directly in a `{ }`
              -- of a JSX element marks its arguments, as a plain call does
              (if pos == .jsxChildExpr || pos == .jsxAttrExpr then .jsxCallArg else .none)
              links)
  | .importCall spec none =>
      -- a plain `import("module")` is never broken, however long the name
      if (match spec with | .string _ => true | _ => false) then
        t "import(" ++ inPosC .callArg spec (exprCore .none .callArg spec) ++ t ")"
      else
        -- otherwise the arguments are laid out like those of any other
        -- call, except that a dynamic import takes no trailing comma
        let args := [spec]
        let pOnly : Pos := .hugArg true false false
        let pFirst : Pos := .hugArg false false true
        .group (t "import"
          ++ argumentsDocOf .never false (isHookCallWithDepsArray args)
              (isFunctionCompositionArguments args) (canHugFirstArg args)
              (canHugLastArg args)
              [inPosC .callArg spec (exprCore .none .callArg spec)]
              [inPosC pFirst spec (exprCore .none pFirst spec)]
              [inPosC pOnly spec (exprCore .none pOnly spec)])
  | .importCall spec (some o) =>
      let args := [spec, o]
      let pLast : Pos := .hugArg false false false
      let pFirst : Pos := .hugArg false false true
      let specDoc := inPosC .callArg spec (exprCore .none .callArg spec)
      let oDoc := inPosC .callArg o (exprCore .none .callArg o)
      .group (t "import"
        ++ argumentsDocOf .never false (isHookCallWithDepsArray args)
            (isFunctionCompositionArguments args) (canHugFirstArg args)
            (canHugLastArg args) [specDoc, oDoc]
            [inPosC pFirst spec (exprCore .none pFirst spec), oDoc]
            [specDoc, inPosC pLast o (exprCore .none pLast o)])
  | .classExpr decorators name heritage body =>
      let ofAssign := match pos with | .assignRhs _ _ a _ => a | _ => false
      classDocOf (decoratorDocs decorators) name
        (match heritage with
          | none => false
          | some e => !ofAssign && heritageIsMember e)
        (match heritage with
          | none => Doc.nil
          | some e =>
            superClassDoc ofAssign
              (inPosC .classHeritage e (exprCore .none .classHeritage e)))
        body (classElemDocsOf (quoteAllMembers body) body)
  | .seq l r =>
      -- the operands after the first of a comma operator that is an
      -- expression statement, or the head of a `for (;;)`, are indented
      let inFor :=
        match pos with
        | .forHeadPart | .forTest | .forSeqTail _ => true
        | _ => false
      let indented :=
        match pos with
        | .statement | .forHeadPart | .forTest | .forSeqTail _ => true
        | .seqTail ind _ => ind
        | _ => false
      -- a comma operator inside another one is one chain with it: it is
      -- not grouped again, and only the outermost one indents
      let inChain :=
        match pos with
        | .seqTail .. | .forSeqTail .. => true
        | _ => false
      let isTail :=
        match pos with
        | .seqTail _ tl => tl
        | .forSeqTail tl => tl
        | _ => false
      let leftPos : Pos := if inFor then .forSeqTail isTail else .seqTail indented isTail
      let rightPos : Pos := if inFor then .forSeqTail true else .seqTail indented true
      -- the operands of a comma operator that is the expression of a
      -- `return` or of a `throw`, or the body of an arrow function, stand
      -- between the parentheses of their own when they break
      let wrapped :=
        match pos with
        | .returnThrow | .arrowBody | .hugArrowBody => true
        | _ => false
      let tail := t "," ++ .line ++ inPosC rightPos r (exprCore .none rightPos r)
      let body := inPosStartC atStart leftPos l (exprCore atStart leftPos l)
        ++ (if indented && !isTail then Doc.nest indentWidth tail else tail)
      if inChain then body
      else if wrapped then
        .group (.ifBreak (.nest indentWidth (.softline ++ body) ++ .softline) body)
      else .group body
  | .binary l op r =>
      let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
      let insideParens := pos == .ifTest
      let leftParts : List Doc :=
        if shouldFlattenLeft op l then binaryParts atStart nodeKind insideParens l
        else
          [Doc.group (inPosStartC atStart (.binOperand op true) l
            (exprCore atStart (.binOperand op true) l))]
      binaryLayoutWith pos l op r
        (leftParts
          ++ (if rightContinuesLogicalChain op r then logicalRightParts op r
              else binaryTailWith (parentBinKind pos) insideParens l op r
                (inPosC (.binOperand op false) r (exprCore .none (.binOperand op false) r))))
  | .postfix e op =>
      inPosStartC atStart .unaryArg e (exprCore atStart .unaryArg e) ++ t (postfixOpText op)
  | .ternary c a b =>
      if Options.experimentalTernaries then
        -- prettier's experimental layout: the `?` stands at the end of the
        -- line of the test and the `:` in front of the alternate, and a
        -- chain of conditionals reads as a list of cases
        let consIsTernary := match a with | .ternary .. => true | _ => false
        let altIsTernary := match b with | .ternary .. => true | _ => false
        let parentIsTernary := isTernaryPos pos
        let inTest := match pos with | .ternaryTest .. => true | _ => false
        let inAlternate := match pos with | .ternaryAlternate .. => true | _ => false
        -- the conditional continues a chain: its alternate is one, or it
        -- is written as the alternate of one
        let chainTail := altIsTernary || inAlternate
        let bigTabs := 2 < tabWidth || Options.useTabs
        -- whether the conditional stands in the `{ }` of a JSX element:
        -- prettier asks that the chain this conditional belongs to is
        -- written in such a `{ }`, and that the conditional itself is not
        -- the one straight inside the `{ }` of an attribute
        let inChain := parentIsTernary && !inTest
        let inheritedJsx :=
          match pos with
          | .ternaryBranch _ j | .ternaryAlternate _ j => j
          | _ => false
        let jsxRoot := if inChain then inheritedJsx else pos == .jsxChildExpr
        -- what the branches of this conditional inherit: a conditional
        -- written in the `{ }` of an attribute passes the flag on, since
        -- what stands inside it is no longer straight inside the `{ }`
        let jsxInner :=
          if inChain then inheritedJsx else pos == .jsxChildExpr || pos == .jsxAttrExpr
        let gp := ternaryParentIndents pos
        let testPos : Pos := .ternaryTest gp
        let consPos : Pos := .ternaryBranch gp jsxInner
        let altPos : Pos := .ternaryAlternate gp jsxInner
        let testDoc := inPosStartC atStart testPos c (exprCore atStart testPos c)
        let consDoc := inPosC consPos a (exprCore .none consPos a)
        let altDoc := inPosC altPos b (exprCore .none altPos b)
        -- a conditional whose consequent is short is written as a case:
        -- the test and the consequent hold one line, and the alternate
        -- stands under them
        let shortCons :=
          !chainTail && !parentIsTernary
            && (if jsxRoot then (match a with | .null => true | _ => false)
                else isShortExpr a && isSmallNode 3 c)
        let groupTest :=
          chainTail || (parentIsTernary && isSmallNode 1 c) || shortCons
        let parens (d : Doc) : Doc :=
          .ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d) ++ .softline
            ++ .ifBreak (t ")") .nil
        let testPart : Doc :=
          .groupId 0 (parens testDoc
            ++ (match c with | .ternary .. => Doc.breakParent | _ => .nil) ++ t " ?")
        let consPart : Doc :=
          .nest indentWidth
            ((if consIsTernary || (jsxRoot && (isJsxExpr a || parentIsTernary || chainTail))
                then .hardline else .line)
              ++ consDoc)
        let head : Doc :=
          if groupTest then
            .groupId 1 (testPart
              ++ (if chainTail then consPart else .ifBreakOf 0 consPart (.group consPart)))
          else testPart ++ consPart
        let altBody : Doc :=
          if shortCons then .ifBreakOf 1 altDoc (.dedent (parens altDoc)) else altDoc
        let sep : Doc :=
          if altIsTernary then .hardline
          else if shortCons then .ifBreakOf 1 .line (t " ")
          else .line
        let pad : Doc :=
          if altIsTernary || !bigTabs then t " "
          else
            let filler := t (if Options.useTabs then "\t" else String.pushn "" ' ' (tabWidth - 1))
            if groupTest then
              .ifBreakOf 1 filler
                (.ifBreak (if chainTail || shortCons then t " " else filler) (t " "))
            else .ifBreak filler (t " ")
        let altPart : Doc :=
          if altIsTernary then altBody
          else
            .group (.nest indentWidth altBody
              ++ (if jsxRoot && !shortCons then .softline else .nil))
        let memberParent := match pos with | .memberObject false _ _ => true | _ => false
        let chainRootAssign := extraIndentRoot pos && (isMemberObjectPos pos || isCalleePos pos)
        -- a chain of conditionals always breaks
        let forced := consIsTernary || altIsTernary
        let body : Doc :=
          head ++ sep ++ t ":" ++ pad ++ altPart
            ++ (if memberParent && !chainRootAssign then .softline else .nil)
            ++ (if forced then Doc.breakParent else .nil)
        -- the right hand side of an assignment that is not one prettier
        -- breaks the line after the operator for
        -- a field written with the `accessor` keyword is not one of the
        -- nodes prettier reads an assignment layout from
        let assignNoBreak :=
          (isAssignRhsPos pos
            || (match pos with | .propValue accessor _ => !accessor | _ => false))
            && !forced
        Doc.scopeIds
          (if assignNoBreak then .group (.nest indentWidth (.softline ++ .group body))
            else if pos == .returnThrow && !forced then .group (.nest indentWidth body)
            else if chainRootAssign then .group (.nest indentWidth (.softline ++ body))
            else if !inChain then .group body
            else body)
      else
      -- a chain of conditionals is laid out as one unit: the branches of a
      -- conditional inside a conditional are neither grouped nor indented
      -- again, and each level is aligned two columns further
      let consIsTernary := match a with | .ternary .. => true | _ => false
      -- a binary expression in the conditional is indented when the
      -- conditional itself is an argument of a call or of a `new`, or the
      -- expression of a `return` or of a `throw`
      let gp := ternaryParentIndents pos
      let inChain :=
        match pos with | .ternaryBranch .. | .ternaryAlternate .. => true | _ => false
      -- a chain of conditionals that holds a JSX element anywhere is laid
      -- out the way prettier lays JSX out
      let jsxMode :=
        match pos with
        | .ternaryBranch _ j | .ternaryAlternate _ j => j
        | _ => ternaryChainHasJsx (.ternary c a b)
      let testPos : Pos := .ternaryTest gp
      let consPos : Pos := .ternaryBranch gp jsxMode
      let altPos : Pos := .ternaryAlternate gp jsxMode
      let testDoc := inPosStartC atStart testPos c (exprCore atStart testPos c)
      let test :=
        if (match pos with | .ternaryAlternate .. => true | _ => false) then Doc.align 2 testDoc
        else testDoc
      -- the chain that holds the conditional stands where prettier
      -- indents the whole of it inside the parentheses it needs
      let extraIndent := extraIndentRoot pos && (isMemberObjectPos pos || isCalleePos pos)
      let atRoot := (match pos with | .ternaryTest .. => true | _ => false) || extraIndent
      if jsxMode then
        -- each branch which is neither `null` nor a further conditional
        -- stands between parentheses of its own where the chain breaks
        let wrap (d : Doc) : Doc :=
          .ifBreak (t "(") .nil ++ .nest indentWidth (.softline ++ d) ++ .softline
            ++ .ifBreak (t ")") .nil
        let consDoc := inPosC consPos a (exprCore .none consPos a)
        let altDoc := inPosC altPos b (exprCore .none altPos b)
        let parts := t " ? " ++ (if isNilExpr a then consDoc else wrap consDoc)
          ++ t " : " ++ (if consIsTernaryOf b || isNilExpr b then altDoc else wrap altDoc)
        let body := test ++ parts
        let result := if inChain then body else Doc.group body
        if atRoot then .group (.nest indentWidth (.softline ++ result) ++ .softline) else result
      else
      -- a branch stands two columns further in, written as a step of its
      -- own where the indentation is tabs
      let branch (d : Doc) : Doc := if Options.useTabs then Doc.nest indentWidth d else Doc.align 2 d
      let consDoc := branch (inPosC consPos a (exprCore .none consPos a))
      let altDoc := branch (inPosC altPos b (exprCore .none altPos b))
      -- the branches of a conditional which is itself the consequent of
      -- one stand `tabWidth - 2` columns further in; with tabs they stand
      -- where they are, prettier writing the step it removes back again
      let chainAlign (d : Doc) : Doc :=
        match pos with
        | .ternaryBranch .. =>
            if Options.useTabs || tabWidth ≤ 2 then d else Doc.align (tabWidth - 2) d
        | _ => d
      let parts := chainAlign (Doc.line ++ t "? "
        ++ (if consIsTernary then Doc.ifBreak .nil (t "(") else .nil)
        ++ consDoc
        ++ (if consIsTernary then Doc.ifBreak .nil (t ")") else .nil)
        ++ .line ++ t ": " ++ altDoc)
      -- `(a\n  ? b\n  : c\n).call()`: the closing parenthesis of a
      -- conditional in the object of a `.` access keeps its own line
      let closing : Doc :=
        if !extraIndent && (match pos with | .memberObject false .. => true | _ => false) then
          .softline
        else .nil
      let body := test ++ (if inChain then parts else Doc.nest indentWidth parts) ++ closing
      let result := if inChain then body else Doc.group body
      if atRoot then .group (.nest indentWidth (.softline ++ result) ++ .softline)
      else result
  | .arrow isAsync params body =>
      -- an arrow function expanded in place as the argument of a call is
      -- not laid out as a chain, and its parameter list keeps its line
      let expanded := (match pos with | .hugArg .. => true | _ => false) || pos == .hugArrowBody
      let sig :=
        let d := t (if isAsync then "async " else "")
          ++ arrowParamsDocOf params (paramDocs params)
        -- the parameters of an arrow written as the argument of a call of
        -- a test framework stay on the line of the call
        if expanded || pos == .testCallArg then Doc.removeLines d else d
      -- an arrow function written straight inside a `{ }` of a JSX
      -- element leaves the closing brace its own line once it breaks
      let jsxParent := pos == .jsxAttrExpr || pos == .jsxChildExpr
      if !expanded && isArrowChainBody body then
        let (paramss, tail) := arrowChainParts params body
        let breakChain := paramss.any (fun ps => !ps.all paramIsPlainIdent)
        let (sigs, bodyPart) := arrowChainDocs breakChain jsxParent body
        arrowLayoutOf pos breakChain (arrowBodyStaysOnLine breakChain tail)
          (sig :: sigs) bodyPart
      else
        arrowLayoutOf pos false true [sig]
          (arrowBodyDoc false false (atStart == .jsxCallArg) jsxParent
            (if expanded then .hugArrowBody else .arrowBody) body)
  | .func isAsync isGen name params body =>
      functionDocOf
        (pos == .testCallArg ||
          match pos with
          | .hugArg sole newExpr first =>
              !newExpr && !first && (!sole || params.all paramIsPlainIdent)
          | _ => false)
        isAsync isGen name params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs true true body))
  | .new callee args =>
      t "new "
        ++ parenIfExpr (!newCalleeOk callee) callee (exprCore .none .newCallee callee)
        ++ argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none true args) (argHugDocs .none true args)
  | .spread e => t "..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e)
  | .template tag head parts =>
      (match tag with
        | none => Doc.nil
        | some tg => inPosStartC atStart .templateTag tg (exprCore atStart .templateTag tg))
        ++ t "`" ++ t (encodeTemplateText head) ++ templatePartsAux .nil parts ++ t "`"
  | .unary op e =>
      t (unaryOpText op)
        ++ (if unaryClash op e then parens (exprCore .none .unaryArg e)
            else inPosC .unaryArg e (exprCore .none .unaryArg e))
  | .jsx n =>
      -- a JSX element that stands where a line break would leave it
      -- beside other text is written between parentheses of its own when
      -- it does not fit on the line it starts on
      let d := jsxNodeDoc n
      if jsxNoWrapPos pos then d
      else jsxWrapInParens (atStart == .jsxArrowBody) (jsxNeedsParens pos) d
  | .yield none => t "yield"
  | .yield (some e) => t "yield " ++ inPosC .yieldArg e (exprCore .none .yieldArg e)
  | .yieldFrom e => t "yield* " ++ inPosC .yieldArg e (exprCore .none .yieldArg e)

/-- The operands and operators of a chain of binary operators of the same
precedence, as the list prettier lays out together. -/
def binaryParts (atStart : StartCtx) (parentKind : BinKind) (insideParens : Bool) :
    MiniExpr → List Doc
  | .binary l op r =>
      let nodeKind : BinKind := if isLogicalOp op then .logical else .arith
      let leftParts : List Doc :=
        if shouldFlattenLeft op l then binaryParts atStart nodeKind insideParens l
        else
          [Doc.group (inPosStartC atStart (.binOperand op true) l
            (exprCore atStart (.binOperand op true) l))]
      leftParts
        ++ (if rightContinuesLogicalChain op r then logicalRightParts op r
            else binaryTailWith parentKind insideParens l op r
              (inPosC (.binOperand op false) r (exprCore .none (.binOperand op false) r)))
  | _ => []

/-- The parts of the operands of a chain of the same logical operator that
leans to the right, which is called on such a chain alone.  Prettier
rebalances the chain, so its operands belong to the chain around it: each
of them is written after the operator, on a line of its own, unless it is
one prettier keeps on the line of the operator, that is, a JSX element or
a non-empty object or array literal. -/
def logicalRightParts (op : BinOp) : MiniExpr → List Doc
  | .binary rl _ rr =>
      (if rightContinuesLogicalChain op rl then logicalRightParts op rl
        else
          [binOpLead (shouldInlineLogicalOf op rl),
            binOpTail op (shouldInlineLogicalOf op rl)
              (inPosC (.binOperand op false) rl (exprCore .none (.binOperand op false) rl))])
      ++ (if rightContinuesLogicalChain op rr then logicalRightParts op rr
        else
          [binOpLead (shouldInlineLogicalOf op rr),
            binOpTail op (shouldInlineLogicalOf op rr)
              (inPosC (.binOperand op false) rr (exprCore .none (.binOperand op false) rr))])
  | _ => []

/-- The elements of a member chain whose last node is `e`, followed by the
elements of the links of an optional chain that continues it.  `pos` is
the position of `e` itself, which the objects and the callees inside it
inherit.  `underCall` says that a call of the chain is written around `e`,
which is what takes the calls written inside it into the chain: prettier
reads a chain out from the outermost call whose callee is a member
access, so a call which stands above every call of the chain is printed
on its own instead. -/
def chainItemsOf (pos : Pos) (atStart : StartCtx) (merge underCall : Bool) :
    MiniExpr → List ChainItem
  | .dot o n =>
      let opos := memberObjectPos false pos
      (if isChainSpineNode o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .dot, doc := t ("." ++ n.toString), name := n.toString }]
  | .privateDot o n =>
      let opos := memberObjectPos false pos
      (if isChainSpineNode o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .dot, doc := t (".#" ++ n.toString), name := n.toString }]
  | .index o i =>
      let opos := memberObjectPos true pos
      (if isChainSpineNode o then chainItemsOf opos atStart false underCall o
        else [chainBaseItem o (inPosStartC atStart opos o
                (exprCore atStart opos o))])
        ++ [{ kind := .index, numericIndex := isNumericLit i,
              doc := indexLookupDoc (isNumericLit i)
                (inPosC .computed i (exprCore .none .computed i)) }]
  | .call f args =>
      let cpos := calleePos pos args.length
      let argsDoc := argumentsDocMaybeOpen (isLongCurriedCall pos args.length)
        (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs .none args) (argHugFirstDocs .none false args) (argHugDocs .none false args)
      -- a call whose arguments stay on its line is one element of the
      -- chain, printed as it is anywhere else
      if !underCall && callArgsStayOnLine false false f args then
        [chainBaseItem (.call f args)
          (inPosStartC atStart cpos f (exprCore atStart cpos f)
            ++ argumentsDoc true false false false
                (if isTestCallOf false f args then testArgDocs .none args else argDocs .none args) [] [])]
      else if !underCall && !isMemberish f then
        -- the chain starts below this call: it is printed as it is
        -- anywhere else, and the chain of its callee stands inside it
        [chainBaseItem (.call f args)
          (let whole := inPosStartC atStart cpos f (exprCore atStart cpos f) ++ argsDoc
            if isCallLikeExpr f then .group whole else whole)]
      else
      (if isChainSpineNode f then chainItemsOf cpos atStart false true f
        else [chainBaseItem f (inPosStartC atStart cpos f (exprCore atStart cpos f))])
        ++ [chainCallItem args argsDoc]
  | .chain b links =>
      -- the chain merges into the one that holds it when the link that
      -- follows it is optional; otherwise it is a parenthesised base
      let bpos := chainBasePos pos links
      let hasCallLink := links.toList.any chainLinkIsCall
      let inner :=
        let innerStart : StartCtx := if merge then atStart else .none
        let innerUnder := hasCallLink || (merge && underCall)
        (if isChainSpine b then chainItemsOf bpos innerStart (chainMergesBase links) innerUnder b
          else [chainBaseItem b (inPosStartC innerStart bpos b
                  (exprCore innerStart bpos b))])
          ++ chainLinkItemsNE .none links
      if merge then inner
      else [chainBaseItem (.chain b links) (t "(" ++ chainAssemble .arg inner ++ t ")")]
  | e => [chainBaseItem e .nil]

/-- The elements of the links of an optional chain. -/
def chainLinkItemsNE (lastCtx : StartCtx) (links : NonEmptyList MiniChainLink) : List ChainItem :=
  chainLinkItem (if links.tail.isEmpty then lastCtx else .none) links.head
    :: chainLinkItems lastCtx links.tail

/-- The elements of the links of an optional chain. -/
def chainLinkItems (lastCtx : StartCtx) : List MiniChainLink → List ChainItem
  | [] => []
  | l :: rest =>
      chainLinkItem (if rest.isEmpty then lastCtx else .none) l :: chainLinkItems lastCtx rest

/-- The element of one link of an optional chain. -/
def chainLinkItem (lastCtx : StartCtx) : MiniChainLink → ChainItem
  | .dot optional n =>
      { kind := .dot, name := n.toString,
        doc := t ((if optional then "?." else ".") ++ n.toString) }
  | .privateDot optional n =>
      { kind := .dot, name := n.toString,
        doc := t ((if optional then "?.#" else ".#") ++ n.toString) }
  | .index optional i =>
      { kind := .index, numericIndex := isNumericLit i,
        doc := t (if optional then "?." else "")
          ++ indexLookupDoc (isNumericLit i) (inPosC .computed i (exprCore .none .computed i)) }
  | .call optional args =>
      chainCallItem args (t (if optional then "?." else "")
          ++ argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
        (canHugLastArg args) (argDocs lastCtx args) (argHugFirstDocs lastCtx false args)
          (argHugDocs lastCtx false args))

/-- The arguments of a call or of a `new`. -/
def argDocs (st : StartCtx) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a) :: argDocs st rest

/-- The arguments of a call of a test framework. -/
def testArgDocs (st : StartCtx) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      inPosC .testCallArg a (exprCore (argStartCtx st a) .testCallArg a) :: testArgDocs st rest

/-- The arguments of a call, with the last one printed as the layout
prints an argument it expands in place.  `newExpr` says that the call is a
`new`. -/
def argHugDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | [a] =>
      let p : Pos := .hugArg true newExpr false
      [inPosC p a (exprCore (argStartCtx st a) p a)]
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a)
        :: argHugTailDocs st newExpr rest

/-- The arguments that follow the first one of a call of more than one
argument, with the last one printed as the layout prints an argument it
expands in place. -/
def argHugTailDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | [a] =>
      let p : Pos := .hugArg false newExpr false
      [inPosC p a (exprCore (argStartCtx st a) p a)]
  | a :: rest =>
      inPosC .callArg a (exprCore (argStartCtx st a) .callArg a)
        :: argHugTailDocs st newExpr rest

/-- The arguments of a call, with the first one printed as the layout
prints an argument it expands in place.  `newExpr` says that the call is a
`new`. -/
def argHugFirstDocs (st : StartCtx) (newExpr : Bool) : List MiniExpr → List Doc
  | [] => []
  | a :: rest =>
      let p : Pos := .hugArg false newExpr true
      inPosC p a (exprCore (argStartCtx st a) p a) :: argDocs st rest

-- ### JSX

/-- One attribute of a JSX element. -/
def jsxAttrDoc : MiniJSXAttribute → Doc
  | .spread e => t "{..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e) ++ t "}"
  | .attr name none => t name.render
  | .attr name (some (.string v)) => t (name.render ++ "=" ++ jsxAttrLit v)
  | .attr name (some (.expr e)) =>
      t (name.render ++ "=")
        ++ jsxContainerOf false e (inPosC .jsxAttrExpr e (exprCore .none .jsxAttrExpr e))
  -- `name=<x />`, an element written as the value with no braces
  | .attr name (some (.node n)) => t (name.render ++ "=") ++ jsxNodeDoc n

/-- The attributes of a JSX element. -/
def jsxAttrDocs : List MiniJSXAttribute → List Doc
  | [] => []
  | a :: rest => jsxAttrDoc a :: jsxAttrDocs rest

/-- The children of an element, each with the document it prints as; a
text child prints as its words, which `jsxChildPartsOf` lays out, so it
carries none. -/
def jsxChildDocs : List MiniJSXChild → List JSXChildDoc
  | [] => []
  | c :: rest =>
    let d : Doc :=
      match c with
      -- `{...children}`, whose operand stands between the braces as it is
      | .expr (.spread e) =>
          t "{..." ++ inPosC .jsxSpreadChildArg e (exprCore .none .jsxSpreadChildArg e) ++ t "}"
      | .expr e => jsxContainerOf true e (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e))
      | .node n => jsxNodeDoc n
      -- `{}`, which holds nothing at all
      | .emptyExpr => t "{}"
      | .text _ => .nil
    (c, d) :: jsxChildDocs rest

/-- A JSX element or fragment, without the parentheses its position may
ask for. -/
def jsxNodeDoc : MiniJSXNode → Doc
  | .element name attrs children =>
    let opening := jsxOpeningDocOf name.render none children.isNone
      (jsxOneStringAttr attrs) (jsxAttrsBreak attrs) (jsxAttrDocs attrs)
    match children with
    | none => opening
    | some kids0 =>
      -- two texts written next to one another are one text to a parser
      let pairs := jsxMergeChildDocs (jsxChildDocs kids0)
      let kids := pairs.map Prod.fst
      let closing := t ("</" ++ name.render ++ ">")
      if kids.all jsxChildIsEmpty then opening ++ closing
      else
        jsxAssemble opening closing (attrs.length > 1) kids (jsxChildPartsOf [] pairs)
          (match kids0 with
            | [.expr e] =>
              if jsxIsTemplateExpr e then
                some (jsxContainerOf true e
                  (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e)))
              else none
            | _ => none)
  | .fragment kids0 =>
      let pairs := jsxMergeChildDocs (jsxChildDocs kids0)
      let kids := pairs.map Prod.fst
      jsxAssemble (t "<>") (t "</>") false kids (jsxChildPartsOf [] pairs)
        (match kids0 with
          | [.expr e] =>
            if jsxIsTemplateExpr e then
              some (jsxContainerOf true e
                (inPosC .jsxChildExpr e (exprCore .none .jsxChildExpr e)))
            else none
          | _ => none)

/-- The decorators of a class or of a class member, each written `@expr`. -/
def decoratorDocs : List MiniExpr → List Doc
  | [] => []
  | d :: rest =>
      (t "@" ++ inPosC .decorator d (exprCore .none .decorator d)) :: decoratorDocs rest

/-- A binding pattern.  `exempt` says whether the pattern stands in one of
the positions where prettier does not force an object pattern that
destructures further to break: a parameter list, a default value or the
parameter of a `catch`. -/
def patternDoc (exempt : Bool) : MiniPattern → Doc
  | .ident n => t n.toString
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .object props none =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props
      if !exempt && objectPatternForcesBreak props then sepListBroken "{" "}" true .es5 items
      else sepList "{" "}" true .es5 items
  | .object props (some r) =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props ++ [t "..." ++ patternDoc false r]
      if !exempt && objectPatternForcesBreak props then sepListBroken "{" "}" true .never items
      else sepList "{" "}" true .never items
  | .withDefault p v => patternDoc true p ++ t " = " ++ inPosC .arg v (exprCore .none .arg v)
  | .target e => inPosC .arg e (exprCore .none .arg e)

/-- The left hand side of a declarator or of a destructuring assignment.
Prettier leaves an object pattern that stands there ungrouped -- the
assignment layout is what groups it -- so that the pattern breaks along
with the assignment. -/
def assignTargetPatternDoc : MiniPattern → Doc
  | .object props none =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props
      if objectPatternForcesBreak props then sepListBroken "{" "}" true .es5 items
      else sepListOpen "{" "}" true .es5 items
  | .object props (some r) =>
      let items := objectPatternPropDocsOf (quoteAllPatternKeys props) props ++ [t "..." ++ patternDoc false r]
      if objectPatternForcesBreak props then sepListBroken "{" "}" true .never items
      else sepListOpen "{" "}" true .never items
  | .ident n => t n.toString
  | .array els => arrayPatternDocOf els (arrayPatternElemDocs els)
  | .withDefault p v => patternDoc true p ++ t " = " ++ inPosC .arg v (exprCore .none .arg v)
  | .target e => inPosC .arg e (exprCore .none .arg e)

def arrayPatternElemDocs : List MiniArrayPatternElem → List Doc
  | [] => []
  | .hole :: rest => Doc.nil :: arrayPatternElemDocs rest
  | .elem p :: rest => patternDoc false p :: arrayPatternElemDocs rest
  | .rest p :: rest => (t "..." ++ patternDoc false p) :: arrayPatternElemDocs rest

def objectPatternPropDocsOf (quoteAll : Bool) : List MiniObjectPatternProp → List Doc
  | [] => []
  | ⟨key, value⟩ :: rest =>
      (if patternShorthand key value then patternDoc false value
        else
          -- prettier lays `key: value` out as it lays an assignment out,
          -- so that the line may break after the colon
          let short := match keyTextWidth key with
            | some w => w < tabWidth + 3
            | none => false
          assignmentDoc short (propertyKeyDoc quoteAll key) ":" (patternLayoutExpr value)
            (patternDoc false value))
        :: objectPatternPropDocsOf quoteAll rest

/-- The elements of an array literal; an elision prints as nothing. -/
def arrayItemDocs : List MiniArrayElement → List Doc
  | [] => []
  | .elem e :: rest => inPosC .arrayElement e (exprCore .none .arrayElement e) :: arrayItemDocs rest
  | .hole :: rest => Doc.nil :: arrayItemDocs rest

/-- The `${…}` substitutions of a template literal, and the text between
them. -/
def templatePartsAux (acc : Doc) : List MiniTemplatePart → Doc
  | [] => acc
  | ⟨e, suffix⟩ :: rest =>
      templatePartsAux
        (acc ++ templateSubstDoc (templateSubstIndents e)
            (inPosC .templateSubst e (exprCore .none .templateSubst e))
          ++ t (encodeTemplateText suffix)) rest

/-- The name of a property or of a method.  Under `quoteProps:
"as-needed"`, prettier's default, a quoted name that is a valid
identifier -- or the plain spelling of a number -- loses its quotes;
under `"preserve"` it keeps them; and `quoteAll`, which
`quoteProps: "consistent"` sets when a sibling name cannot lose its
quotes, quotes every name that can be written quoted. -/
def propertyKeyDoc (quoteAll : Bool) : MiniPropertyName → Doc
  | .ident n => if quoteAll then t (strLit n.toString) else t n.toString
  | .private_ n => t ("#" ++ n.toString)
  | .string v =>
      if Options.quoteProps == .preserve || quoteAll then t (strLit v)
      else if isIdentifierName v then t v
      else if isSimpleNumberString v then t v
      else t (strLit v)
  -- a number prettier writes as a quoted name only when it is the plain
  -- spelling of what it denotes: `1e3` and `0x10` stay as they are
  | .number n => if quoteAll && isSimpleNumberString n.render then t (strLit n.render) else t n.render
  | .computed e => t "[" ++ inPosC .arg e (exprCore .none .arg e) ++ t "]"

def propertyDoc (quoteAll : Bool) : MiniProperty → Doc
  | .keyValue k v =>
      let short := match keyTextWidth k with
        | some w => w < tabWidth + 3
        | none => false
      assignmentDoc short (propertyKeyDoc quoteAll k) ":" v
        (inPosC (.propValue false false) v (exprCore .none (.propValue false false) v))
  | .shorthand n => t n.toString
  | .spread e => t "..." ++ inPosC .spreadArg e (exprCore .none .spreadArg e)
  | .method kind key params body =>
      methodDocOf kind (propertyKeyDoc quoteAll key) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs true true body))

def propertyDocsOf (quoteAll : Bool) : List MiniProperty → List Doc
  | [] => []
  | p :: rest => propertyDoc quoteAll p :: propertyDocsOf quoteAll rest

/-- One parameter. -/
def paramDoc : MiniParam → Doc
  | .plain p => patternDoc true p
  | .rest p => t "..." ++ patternDoc true p

def paramDocs : List MiniParam → List Doc
  | [] => []
  | p :: rest => paramDoc p :: paramDocs rest

def classElemDoc (quoteAll : Bool) (next : Option MiniClassElement) : MiniClassElement → Doc
  | .method decorators isStatic kind key params body =>
      decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ methodDocOf kind (propertyKeyDoc quoteAll key) params (paramDocs params) body
            (Doc.joinWith .hardline (statementDocs true true body))
  | .field decorators isStatic isAccessor key init =>
      -- the decorators stand inside the left hand side of the assignment,
      -- as prettier writes them: a field which has one is a field whose
      -- left hand side holds a line, and so is never one whose value
      -- keeps the line of the `=` whatever it is
      let headDoc := decoratorsPrefix (decoratorDocs decorators)
        ++ (if isStatic then t "static " else Doc.nil)
        ++ (if isAccessor then t "accessor " else Doc.nil)
      (match init with
        | none => headDoc ++ propertyKeyDoc quoteAll key
        | some e =>
            let valuePos : Pos := .propValue isAccessor true
            assignmentDoc false (headDoc ++ propertyKeyDoc quoteAll key) " =" e
              (inPosC valuePos e (exprCore .none valuePos e)))
        ++ fieldSemiDoc key init next
  | .staticBlock body =>
      -- a string literal statement of a static block cannot be read as a
      -- directive, and so is never parenthesised
      t "static " ++ blockDocOf true (bodyIsEmpty body)
        (Doc.joinWith .hardline (statementDocs false false body))

def classElemDocsOf (quoteAll : Bool) : List MiniClassElement → List Doc
  | [] => []
  | el :: rest => classElemDoc quoteAll rest.head? el :: classElemDocsOf quoteAll rest

/-- The parameter list of an arrow function, which `arrowParens: "avoid"`
writes without its parentheses when it is one plain name. -/
def arrowParamsDocOf (params : List MiniParam) (items : List Doc) : Doc :=
  if arrowParensAvoided params then Doc.concat items
  else paramsDocOf (shouldHugTheOnlyParameter params) (restLast params) items

/-- The body of an arrow function, with the space or the line in front. -/
def arrowBodyDoc (chained breakChain jsxArg jsxParent : Bool) (bodyPos : Pos) :
    MiniArrowBody → Doc
  | .block body =>
      t " " ++ blockDocOf true (bodyIsEmpty body) (Doc.joinWith .hardline (statementDocs true true body))
  | .expr e =>
      let st : StartCtx := if jsxArg then jsxArrowBodyStart e else arrowBodyStart e
      arrowExprBodyOf chained breakChain (bodyPos == .hugArrowBody) jsxParent e
        (inPosStartC st bodyPos e (exprCore st bodyPos e))

/-- The signatures of the arrow functions that follow the first one of a
chain, and the document of the body at the end of the chain. -/
def arrowChainDocs (breakChain jsxParent : Bool) : MiniArrowBody → List Doc × Doc
  | .expr (.arrow isAsync ps b) =>
      let (sigs, bodyPart) := arrowChainDocs breakChain jsxParent b
      ((t (if isAsync then "async " else "")
          ++ arrowParamsDocOf ps (paramDocs ps)) :: sigs,
        bodyPart)
  | .expr e =>
      ([], arrowExprBodyOf true breakChain false jsxParent e
            (inPosStartC (arrowBodyStart e) .arrowBody e
              (exprCore (arrowBodyStart e) .arrowBody e)))
  | .block body =>
      ([], t " " ++ blockDocOf true (bodyIsEmpty body)
            (Doc.joinWith .hardline (statementDocs true true body)))

def declaratorDoc : MiniDeclarator → Doc
  | ⟨lhs, init⟩ =>
      match init with
      | none => patternDoc false lhs
      | some e =>
          -- `const x = (a = 1);`: an assignment used as an initialiser is
          -- parenthesised, which the position it stands in asks for
          let init :=
            inPosC (.assignRhs false false false false) e
              (exprCore .none (.assignRhs false false false false) e)
          let leftDoc := assignTargetPatternDoc lhs
          let leftCanBreak := Doc.canBreak leftDoc
          let complexLhs :=
            patternIsComplexDestructuring lhs
              || (leftCanBreak && (match e with | .arrow .. => true | _ => false))
          assignmentDocOf
            (chooseAssignLayout false false false complexLhs leftCanBreak false e)
            leftDoc " =" init

def declaratorDocs : List MiniDeclarator → List Doc
  | [] => []
  | d :: rest => declaratorDoc d :: declaratorDocs rest

def forInitDoc : MiniForInit → Doc
  | .none => Doc.nil
  | .expr e => inPosStartC .forInit .forHeadPart e (exprCore .forInit .forHeadPart e)
  | .decl kind ⟨hd, tl⟩ =>
      declarationDoc kind true
        (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)

/-- The binder of a `for (... in ...)` or of a `for (... of ...)`.  It may
not start with the identifier `let`, which is parenthesised there. -/
def forHeadDoc : MiniForHead → Doc
  | .pattern (.ident n) => if n.toString == "let" then t "(let)" else t n.toString
  | .pattern (.target e) => inPosStartC .forInHead .arg e (exprCore .forInHead .arg e)
  | .pattern p => patternDoc false p
  | .decl kind lhs => t (varKindText kind ++ " ") ++ patternDoc false lhs
  | .usingDecl isAwait lhs =>
      t (if isAwait then "await using " else "using ") ++ patternDoc false lhs

def switchCaseDoc : MiniSwitchCase → Doc
  | .case test body =>
      t "case " ++ inPosC .caseTest test (exprCore .none .caseTest test) ++ t ":"
        ++ caseBodyWith body (statementDocs false false body)
  | .default body => t "default:" ++ caseBodyWith body (statementDocs false false body)

def switchCaseDocs : List MiniSwitchCase → List Doc
  | [] => []
  | c :: rest => switchCaseDoc c :: switchCaseDocs rest

def catchDoc (collapseEmpty : Bool) : MiniCatchClause → Doc
  | ⟨param, guard, body⟩ =>
      t " catch (" ++ patternDoc true param
        ++ (match guard with
            | none => Doc.nil
            | some g => t " if " ++ inPosC .ifTest g (exprCore .none .ifTest g))
        ++ t ") " ++ blockDocOf collapseEmpty (bodyIsEmpty body)
            (Doc.joinWith .hardline (statementDocs true false body))

def catchDocsAux (collapseEmpty : Bool) (acc : Doc) : List MiniCatchClause → Doc
  | [] => acc
  | c :: rest => catchDocsAux collapseEmpty (acc ++ catchDoc collapseEmpty c) rest

def tryTailDoc : MiniTryTail → Doc
  | .finallyOnly body =>
      t " finally " ++ blockDocOf false (bodyIsEmpty body)
        (Doc.joinWith .hardline (statementDocs true false body))
  | .catches ⟨hd, tl⟩ fin =>
      let hasFinally := match fin with | .none => false | .some _ => true
      catchDocsAux (!hasFinally) (catchDoc (!hasFinally) hd) tl
        ++ (match fin with
            | .none => Doc.nil
            | .some body =>
                t " finally " ++ blockDocOf false (bodyIsEmpty body)
                  (Doc.joinWith .hardline (statementDocs true false body)))

/-- A statement.  `collapseEmpty` says whether an empty block body is
written `{}`, which prettier does for the body of a loop and of a
function, but not for the body of an `if` or of a `for ... of`. -/
def statementDoc (collapseEmpty inList : Bool) : MiniStatement → Doc
  | .block body =>
      blockDocOf collapseEmpty (bodyIsEmpty body) (Doc.joinWith .hardline (statementDocs true false body))
  | .break_ none => t "break" ++ semiDoc
  | .break_ (some l) => t ("break " ++ l.toString) ++ semiDoc
  | .continue_ none => t "continue" ++ semiDoc
  | .continue_ (some l) => t ("continue " ++ l.toString) ++ semiDoc
  | .classDecl decorators name heritage body =>
      -- prettier puts a decorated declaration and its decorators in a
      -- group of their own, which the decorators then break; a decorated
      -- class *expression* is left ungrouped, and so keeps its decorators
      -- on its line where the line around it is laid out flat
      (if decorators.isEmpty then id else Doc.group)
        (classDocOf (decoratorDocs decorators) (some name)
          (match heritage with | none => false | some e => heritageIsMember e)
          (match heritage with
            | none => Doc.nil
            | some e => inPosC .classHeritage e (exprCore .none .classHeritage e))
          body (classElemDocsOf (quoteAllMembers body) body))
  | .decl kind ⟨hd, tl⟩ =>
      declarationDoc kind false (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)
  | .using_ isAwait ⟨hd, tl⟩ =>
      declarationDocOf (if isAwait then "await using" else "using") false
        (hd.init.isSome || tl.any (fun d => d.init.isSome))
        (declaratorDoc hd :: declaratorDocs tl)
  | .debugger => t "debugger" ++ semiDoc
  | .doWhile body cond =>
      .group (t "do" ++ bodyClauseWith body (statementDoc true false body))
        ++ (if isBlockStmt body then t " " else .hardline)
        ++ t "while (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond)) ++ t ")"
        ++ semiDoc
  | .for_ init cond step body =>
      let noHead := (match init with | .none => true | _ => false)
        && cond.isNone && step.isNone
      if noHead then .group (t "for (;;)" ++ bodyClauseWith body (statementDoc true false body))
      else
        .group (t "for ("
          ++ .group (.nest indentWidth
              (.softline ++ ctx.forInit init ++ t ";" ++ .line
                ++ (match cond with
                    | none => Doc.nil
                    | some c => inPosC .forTest c (exprCore .none .forTest c))
                ++ t ";"
                ++ (match step with
                    | none => Doc.nil
                    | some s => .line ++ inPosC .forHeadPart s (exprCore .none .forHeadPart s)))
              ++ .softline)
          ++ t ")" ++ bodyClauseWith body (statementDoc true false body))
  | .forIn head obj body =>
      .group (t "for (" ++ forHeadDoc head ++ t " in "
        ++ inPosC .forInObject obj (exprCore .none .forInObject obj) ++ t ")"
          ++ bodyClauseWith body (statementDoc false false body))
  | .forOf isAwait head obj body =>
      .group (t (if isAwait then "for await (" else "for (") ++ forHeadDoc head ++ t " of "
        ++ inPosC .forInObject obj (exprCore .none .forInObject obj) ++ t ")"
          ++ bodyClauseWith body (statementDoc false false body))
  | .funcDecl isAsync isGen name params body =>
      functionDocOf false isAsync isGen (some name) params (paramDocs params) body
        (Doc.joinWith .hardline (statementDocs true true body))
  | .if_ cond thenS elseS =>
      -- `if (a) { if (b) c; } else d`: the consequent is written in a
      -- block when it could swallow the `else`
      let braced := elseS.isSome && !isBlockStmt thenS && endsWithDanglingIf thenS
      let thenDoc :=
        if braced then blockDocOf false false (statementDoc true false thenS)
        else statementDoc false false thenS
      let thenClause :=
        if braced then clauseDoc true false thenDoc else bodyClauseWith thenS thenDoc
      let opening :=
        .group (t "if (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond)) ++ t ")" ++ thenClause)
      match elseS with
      | none => opening
      | some e =>
          opening
            ++ (if braced || isBlockStmt thenS then t " " else .hardline)
            ++ t "else"
            ++ .group
                (if isEmptyStmt e then t ";"
                  else if isBlockStmt e || isIfStmt e then t " " ++ statementDoc false false e
                  else .nest indentWidth (.line ++ statementDoc false false e))
  | .labelled l s =>
      if isEmptyStmt s then t (l.toString ++ ":;") else t (l.toString ++ ": ") ++ statementDoc false false s
  | .empty => t ";"
  | .expr e =>
      let outer := needsParensC .statement e || cannotStartStatement e
      -- the parentheses an object literal, a function or a class
      -- expression takes at the start of a statement belong to it, and are
      -- written even when the statement takes parentheses of its own
      let inner : StartCtx := if cannotStartStatement e then .none else .statement
      let d := parenIfExpr outer e (exprCore inner .statement e)
      -- a string literal statement of a program or of a block is
      -- parenthesised, so that it is not read as a directive
      let directiveLike := inList && (match e with | .string _ => true | _ => false)
      if !outer && (needsStatementParens e || directiveLike) then parens d ++ semiDoc
      else d ++ semiDoc
  | .return_ none => t "return" ++ semiDoc
  | .return_ (some e) =>
      t "return " ++ returnArgWith e (inPosC .returnThrow e (exprCore .none .returnThrow e))
        ++ semiDoc
  | .throw e =>
      t "throw " ++ returnArgWith e (inPosC .returnThrow e (exprCore .none .returnThrow e))
        ++ semiDoc
  | .switch disc cases =>
      .group (t "switch ("
          ++ .nest indentWidth (.softline ++ inPosC .ifTest disc (exprCore .none .ifTest disc))
          ++ .softline ++ t ")")
        ++ t " {"
        ++ (if cases.isEmpty then Doc.nil
            else .nest indentWidth (.hardline ++ Doc.joinWith .hardline (switchCaseDocs cases)))
        ++ .hardline ++ t "}"
  | .try_ body tail =>
      t "try " ++ blockDocOf false (bodyIsEmpty body)
          (Doc.joinWith .hardline (statementDocs true false body))
        ++ tryTailDoc tail
  | .while_ cond body =>
      .group (t "while (" ++ conditionWith cond (inPosC .ifTest cond (exprCore .none .ifTest cond)) ++ t ")" ++ bodyClauseWith body (statementDoc true false body))
  | .with_ obj body =>
      .group (t "with ("
        ++ conditionWith obj (inPosC .withObject obj (exprCore .none .withObject obj))
        ++ t ")" ++ bodyClauseWith body (statementDoc false false body))

/-- The statements of a body; the empty statement is dropped.  `inList`
says whether the statements are those of a program or of a block, where a
string literal statement that is not a directive is parenthesised;
`prologue` says whether a string literal statement here would still be one
of the directives of a program or of a function body. -/
def statementDocs (inList prologue : Bool) : List MiniStatement → List Doc
  | [] => []
  | .empty :: rest => statementDocs inList prologue rest
  | s :: rest =>
      let directive := prologue && isStringStmt s
      asiGuard s (statementDoc false (inList && !directive) s)
        :: statementDocs inList directive rest

end
end

/-- The head of a `for (;;)`: the place where prettier parenthesises every
`in` operator written in it. -/
partial def forInitHeadDoc (init : MiniForInit) : Doc :=
  forInitDoc { inForInit := true, forInit := forInitHeadDoc } init

/-- The context anything outside the head of a `for (;;)` is printed in. -/
def topCtx : PrintCtx := { inForInit := false, forInit := forInitHeadDoc }

/-! ### Document builders for AST nodes -/

/-- An expression in position `pos`. -/
def exprDoc (pos : Pos) (e : MiniExpr) : Doc := inPos pos e (exprCore topCtx .none pos e)

/-- The object of a `.` or `[]` access. -/
def memberObjectDoc (e : MiniExpr) : Doc := exprDoc (.memberObject false false false) e

/-- The callee of a call. -/
def calleeDoc (e : MiniExpr) : Doc := exprDoc (.callee false 0) e

/-- The argument list of a call. -/
def argsDoc (args : List MiniExpr) : Doc :=
  argumentsDoc (isHookCallWithDepsArray args) (isFunctionCompositionArguments args) (canHugFirstArg args)
    (canHugLastArg args) (argDocs topCtx .none args) (argHugFirstDocs topCtx .none false args)
    (argHugDocs topCtx .none false args)

/-- A parameter list. -/
def paramsDoc (params : List MiniParam) : Doc :=
  paramsDocOf (shouldHugTheOnlyParameter params) (restLast params) (paramDocs topCtx params)

def arrayDoc (els : List MiniArrayElement) : Doc := arrayDocOf els (arrayItemDocs topCtx els)

def classBodyDoc (body : List MiniClassElement) : Doc :=
  classBodyOf body (classElemDocsOf topCtx (quoteAllMembers body) body)

def classElementDoc (el : MiniClassElement) : Doc := classElemDoc topCtx false none el

/-- A binding pattern. -/
def patternDocOf (p : MiniPattern) : Doc := patternDoc topCtx false p

/-- One decorator, `@expr`. -/
def decoratorDoc (e : MiniExpr) : Doc := t "@" ++ exprDoc .decorator e

def classDoc (decorators : List MiniExpr) (name : Option NonEmptyString)
    (heritage : Option MiniExpr) (body : List MiniClassElement) : Doc :=
  classDocOf (decoratorDocs topCtx decorators) name
    (match heritage with | none => false | some e => heritageIsMember e)
    (match heritage with
      | none => Doc.nil
      | some e => exprDoc .classHeritage e)
    body (classElemDocsOf topCtx (quoteAllMembers body) body)

def methodDoc (kind : MethodKind) (key : MiniPropertyName)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  methodDocOf kind (propertyKeyDoc topCtx false key) params (paramDocs topCtx params) body
    (Doc.joinWith .hardline (statementDocs topCtx true true body))

def functionDoc (isAsync isGen : Bool) (name : Option NonEmptyString)
    (params : List MiniParam) (body : List MiniStatement) : Doc :=
  functionDocOf false isAsync isGen name params (paramDocs topCtx params) body
    (Doc.joinWith .hardline (statementDocs topCtx true true body))

/-- A statement list, one statement per line. -/
def statementsDoc (body : List MiniStatement) : Doc :=
  Doc.joinWith .hardline (statementDocs topCtx true false body)

/-- A brace enclosed statement list. -/
def blockDoc (body : List MiniStatement) : Doc :=
  blockDocOf false (bodyIsEmpty body) (statementsDoc body)

/-- The name of a property or of a method. -/
def propertyNameDoc (k : MiniPropertyName) : Doc := propertyKeyDoc topCtx false k

/-! ## Modules -/

def specifierDoc (s : Specifier) : Doc :=
  t s.name.toString ++ (match s.alias_ with | none => Doc.nil | some a => t (" as " ++ a.toString))

/-- The `{ a, b as c }` of an import or export clause.  A clause of
exactly one named specifier which stands alone -- with no default and no
namespace specifier beside it -- is never broken, however long the line
becomes; every other clause is a list which breaks one specifier to a
line.  `withStandalone` says whether a default or namespace specifier
stands beside these. -/
def specifiersDoc (specs : List Specifier) (withStandalone : Bool := false) : Doc :=
  match specs with
  | [sp] => if withStandalone then sepList "{" "}" true .es5 [specifierDoc sp]
            else
              let pad := if Options.bracketSpacing then " " else ""
              t ("{" ++ pad) ++ specifierDoc sp ++ t (pad ++ "}")
  | _ => sepList "{" "}" true .es5 (specs.map specifierDoc)

def importDoc : MiniImportDeclaration → Doc
  | .bare mod attrs =>
      t ("import " ++ strLit mod.toString) ++ importAttrsDoc attrs ++ semiDoc
  | .clause c =>
      let standalone : List Doc :=
        (match c.default_ with | none => [] | some d => [t d.toString])
        ++ (match c.namespace_ with | none => [] | some n => [t ("* as " ++ n.toString)])
      let parts : List Doc :=
        standalone
        -- an empty list of named imports is written out only when it is
        -- the whole clause: `import d, {} from "m"` binds `d` alone
        ++ (match c.named with
            | none => []
            | some [] => if standalone.isEmpty then [specifiersDoc []] else []
            | some specs => [specifiersDoc specs !standalone.isEmpty])
      t "import " ++ Doc.joinWith (t ", ") parts
        ++ t (" from " ++ strLit c.mod.toString) ++ importAttrsDoc c.attrs ++ semiDoc

def exportDoc : MiniExportDeclaration → Doc
  | .fromClause specs mod attrs =>
      t "export " ++ specifiersDoc specs ++ t (" from " ++ strLit mod.toString)
        ++ importAttrsDoc attrs ++ semiDoc
  | .locals specs => t "export " ++ specifiersDoc specs ++ semiDoc
  | .all alias_ mod attrs =>
      t "export *"
        ++ (match alias_ with | none => Doc.nil | some n => t (" as " ++ n.toString))
        ++ t (" from " ++ strLit mod.toString) ++ importAttrsDoc attrs ++ semiDoc
  -- `export default function () {}` and `export default class {}` are
  -- declarations, which take no semicolon; anything whose leftmost token
  -- opens a function or a class is parenthesised, so that it is not read
  -- as one of them
  | .defaultExpr (.func isAsync isGen name params body) =>
      t "export default " ++ functionDoc isAsync isGen name params body
  -- the decorators of an exported class stand on their own line, below
  -- the `export` keyword
  | .defaultExpr (.classExpr decorators name heritage body) =>
      t "export default" ++ (if decorators.isEmpty then t " " else Doc.hardline)
        ++ classDoc decorators name heritage body
  | .defaultExpr e =>
      t "export default "
        ++ parenIfExpr (needsParens .generic e || startsWithFunctionOrClass e) e
            (exprCore topCtx .none .generic e)
        ++ semiDoc
  | .decl (.classDecl decorators name heritage body) =>
      t "export" ++ (if decorators.isEmpty then t " " else Doc.hardline)
        ++ classDoc decorators (some name) heritage body
  | .decl s => t "export " ++ statementDoc topCtx false false s

/-- One item of a program.  `inList` says that a string literal statement
here is no longer one of the directives of the program, and so is
parenthesised. -/
def moduleItemDoc (inList : Bool) : MiniModuleItem → Doc
  | .stmt s => asiGuard s (statementDoc topCtx false inList s)
  | .importDecl d => importDoc d
  | .exportDecl d => exportDoc d

/-- Whether the item is a string literal statement, which is a directive
where a program starts. -/
def isStringItem : MiniModuleItem → Bool
  | .stmt s => isStringStmt s
  | _ => false

/-- The documents of the items of a program.  `prologue` says whether a
string literal statement here is still one of the directives of the
program. -/
def moduleItemDocs (prologue : Bool) : List MiniModuleItem → List Doc
  | [] => []
  | i :: rest =>
      let directive := prologue && isStringItem i
      moduleItemDoc (!directive) i :: moduleItemDocs directive rest

/-- Whether the item is an empty statement, which prettier drops. -/
def isEmptyItem : MiniModuleItem → Bool
  | .stmt s => isEmptyStmt s
  | _ => false

def programDoc (p : MiniProgram) : Doc :=
  Doc.joinWith .hardline (moduleItemDocs true (p.items.filter (fun i => !isEmptyItem i)))

end Printer

/-! ## Entry points -/

/-- Print a program under the given options, preceded by the interpreter
directive (the `#!` line) the file starts with, if it has one.  Prettier
writes the directive on the first line and keeps its text as it finds
it. -/
def printFileWith (opts : Options) (interpreter : Option String) (p : MiniProgram) : String :=
  let eol := opts.endOfLine.text
  let shebang := match interpreter with | none => "" | some s => "#!" ++ s ++ eol
  -- a program prettier writes nothing for -- one with no items, or one
  -- whose items are all the empty statement, which prettier drops -- is
  -- not a blank line either
  if (p.items.filter (fun i => !Printer.isEmptyItem i)).isEmpty then shebang
  else shebang ++ renderDoc opts (Printer.programDoc (o := opts) p) ++ eol

/-- Print a program under the given options. -/
def printProgramWith (opts : Options) (p : MiniProgram) : String :=
  printFileWith opts none p

/-- Print a program in the canonical style, at a given line width,
preceded by the interpreter directive the file starts with, if it has
one. -/
def printFileWidth (interpreter : Option String) (width : Nat) (p : MiniProgram) : String :=
  printFileWith { printWidth := width } interpreter p

/-- Print a program in the canonical style, at a given line width. -/
def printProgramWidth (width : Nat) (p : MiniProgram) : String :=
  printFileWidth none width p

/-- Print a program in the canonical style: two space indentation, double
quotes, semicolons, and lines of at most 80 columns. -/
def printProgram (p : MiniProgram) : String :=
  printProgramWith defaultOptions p

/-- Print a file in the canonical style: the interpreter directive, if the
file has one, and then the program. -/
def printFile (interpreter : Option String) (p : MiniProgram) : String :=
  printFileWith defaultOptions interpreter p

/-- Print a single statement under the given options. -/
def printStatementWith (opts : Options) (s : MiniStatement) : String :=
  renderDoc opts (Printer.statementDoc (o := opts) Printer.topCtx false true s)

/-- Print a single statement. -/
def printStatement (s : MiniStatement) : String :=
  printStatementWith defaultOptions s

/-- Print a single expression under the given options. -/
def printExprWith (opts : Options) (e : MiniExpr) : String :=
  renderDoc opts (Printer.exprDoc (o := opts) .statement e)

/-- Print a single expression. -/
def printExpr (e : MiniExpr) : String :=
  printExprWith defaultOptions e

end Language.JavaScript.MiniAST
