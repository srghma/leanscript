import JsTerm.Print.Mini.Basic

/-!
# Printing the JavaScript grammar: expressions and blocks

The conversion of the expressions (`exprToMini`) and blocks (`blockToMini`) of the grammar to
`MiniAST` expressions and statements, as described in `JsTerm.Print.Mini`.

(Not a `module`: `LanguageJavascriptMini` is not written in the module system.)
-/

namespace MoreJs

variable {S : JsSig}

open Language.JavaScript Language.JavaScript.MiniAST NonEmpty.String

/-! ## The conversion -/

/-- The literal `0` of a counter (`0n` for a `BigInt`). -/
def natLitOf {N : JsTy} (nt : JsNatTy N) (n : Nat) : MiniExpr :=
  match nt with
  | .bigint_nat => bigintNum n
  | .uint53 => natNum n

/-- A `number` holding a natural number, at the representation `nt`: itself, or `BigInt(e)`. -/
def natOfNumber {N : JsTy} (nt : JsNatTy N) (e : MiniExpr) : MiniExpr :=
  match nt with
  | .bigint_nat => .call (ident "BigInt") [e]
  | .uint53 => e

/-! ## Decimal digits in a concatenation -/

/-- Is the expression the decimal digits of a number, `String(x)` (`Nat.repr`, `Int.repr`)? -/
def JsExpr.isDigits {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .inlined op _ => op.name.endsWith "__lean_nat_repr" || op.name.endsWith "__lean_int_repr"
  | _ => false

/-- `x` when the printed expression is `String(x)`. -/
def unDigits : MiniExpr → MiniExpr
  | .call _ [x] => x
  | e => e

/-- The printed arguments of an inlined operation, where it is a concatenation of strings
    (`a + b`, `String.append`) one of whose operands is the decimal digits of a number
    `String(x)`: that operand written `x` (`"n: " + n`).  JavaScript's `+` converts a number,
    or a `BigInt`, to its decimal digits when the other operand is a string, as `String` does,
    so only one of the two operands is written without its `String`: the other one is still a
    string. -/
def concatDigits {C M : List JsTy} {e : Effectfulness} {t : MayThrow} {σs : List JsTy}
    {τ : JsTy} (op : JsOpInlinable e t σs τ) (args : JsArgs S C M σs) (es : List MiniExpr) :
    List MiniExpr :=
  if !op.name.startsWith "string__lean_string_append" then es else
  match args, es with
  | .cons a (.cons b .nil), [x, y] =>
    if b.isDigits then [x, unDigits y]
    else if a.isDigits then [unDigits x, y]
    else es
  | _, _ => es

/-- The dump of each arm of a case analysis on a union (with the fields it takes apart). -/
partial def JsUnionArms.keys {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → List String
  | .nil => []
  | .cons sel b rest => (toString (sel.binds.map (·.1)) ++ b.pretty "") :: rest.keys

/-- The dump of each arm of a case analysis on an enum. -/
partial def JsEnumArms.keys {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → List String
  | .nil => []
  | .cons b rest => b.pretty "" :: rest.keys

/-! ## Fields read once -/

/-- Where the value a pattern takes apart comes from, for reading its fields in place: `none`
    when they cannot be (an expression that is not a variable), `some none` when it never
    changes (a constant, a module constant, or the new constant holding the subject of a case
    analysis, `bound`), `some (some m)` when it is the mutable variable `m`. -/
def JsExpr.fieldSource {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) (bound : Bool := false) :
    Option (Option Nat) :=
  match e with
  | .cvar _ => some none
  | .mvar m => some (some m.index)
  | .fold _ e | .unfold _ e => e.fieldSource bound
  | _ => if bound then some none else none

/-- The fields (by their positions `j` among the `n` a pattern binds) that the block after the
    pattern may read in place (`x._1` instead of `const { _1: f } = x; … f …`): the value keeps
    holding the same record in the whole block (`src`: it is not a mutable variable the block
    assigns), and the block reads the field exactly once, outside loops and closures (so the
    field is still read once, and a closure does not keep the whole record alive); a field the
    block never reads is never bound. -/
def readInPlace {C M J : List JsTy} {k : JsEnd} (src : Option (Option Nat)) (n : Nat)
    (rest : JsBlock S C M J k) : Nat → Bool :=
  match src with
  | none => fun _ => false
  | some m =>
    let occs := rest.occs
    let stable := match m with
      | none => true
      | some m => !occs.any fun o => o.write && o.is ⟨true, m⟩
    let uses j := occs.filter fun o => !o.isMut && o.idx == n - 1 - j
    -- a field the block never reads is not bound
    if !stable then fun j => (uses j).isEmpty else
    fun j =>
      let us := uses j
      us.isEmpty || (us.size == 1 && !us.any (·.again))

mutual
/-- An expression as a `MiniAST` expression. -/
partial def exprToMini {C M : List JsTy} {τ : JsTy} (sc : Scope) : JsExpr S C M τ → PM MiniExpr
  | .cvar x => pure (exprAt sc.c x.index)
  | .mvar x => pure (nameAt sc.m x.index)
  | .lit l => pure (shapeExpr l.shape)
  | .imported op args => do
    return .call (ident op.runtimeName) (op.extraArgs.map dotted ++ (← argsToMini sc args))
  | .inlined op args => do
    let es ← argsToMini sc args
    return inlineToMini (concatDigits op args es).toArray op.template
  | .unreachable _ => pure (ident "undefined")
  | .app f as => do return .call (← exprToMini sc f) (← argsToMini sc as)
  | .lam (σs := σs) hints body => do
    let xs ← (List.range σs.length).mapM fun i => freshName (hints.getD i "x")
    -- a function starts afresh: no jump leaves it, and it is no iteration of a loop
    arrowToMini { c := xs.reverse.map ident ++ sc.c, m := sc.m } xs body
  | .record_mk fs => do
    let es ← argsToMini sc fs
    return .object (es.zipIdx.map fun (e, i) => .keyValue (.ident (nes (fieldKey i))) e)
  | .union_mk (id := id) ix args => do
    let es ← argsToMini sc args
    -- a constructor without fields of a union whose constructors without fields are numbers
    -- (`JsRepr.smallIntNullary`) is its position
    if es.isEmpty && S.reprOf id == .smallIntNullary then return natNum ix.index
    return .object (.keyValue (.ident (nes "tag")) (natNum ix.index) ::
      es.zipIdx.map fun (e, i) => .keyValue (.ident (nes (fieldKey i))) e)
  | .enum_mk _ shift i => pure (intNum (shift + i.val))
  | .enumIndex (shift := shift) nt e => do
    let x ← exprToMini sc e
    let i : MiniExpr :=
      if shift = 0 then x
      else if shift < 0 then .binary x .plus (natNum shift.natAbs)
      else .binary x .minus (natNum shift.natAbs)
    return natOfNumber nt i
  | .enumEq a b => do return .binary (← exprToMini sc a) .strictEq (← exprToMini sc b)
  | .index _ nt a i => do
    let a ← exprToMini sc a
    let i : MiniExpr ← match nt.isBigInt, i.natLit? with
      | true, some k => pure (natNum k)
      | true, none => do pure (.call (ident "Number") [← exprToMini sc i])
      | false, _ => exprToMini sc i
    return .index a i
  | .array_mk (.generic _) ps => do return .array ((← partsToMini sc ps).map .elem)
  | .array_mk (.typed t) ps => do
    return .call (.dot (ident t.kind.ctorName) (nes "of")) (← partsToMini sc ps)
  | .list_mk ps => do return .array ((← partsToMini sc ps).map .elem)
  | .listOp op args => do return .call (ident op.runtimeName) (← argsToMini sc args)
  -- one layer in or out of a declared datatype: nothing at run time
  | .fold _ e | .unfold _ e => exprToMini sc e
  | .global name => pure (ident name)
  | .cond c a b => do
    let c ← exprToMini sc c
    match ← exprToMini sc a, ← exprToMini sc b with
    | .true_, .false_ => return c
    | .false_, .true_ => return negateCond c
    -- a boolean `c ? a : false` is `c && a`, and `c ? true : b` is `c || b` (the operators
    -- evaluate their right operand exactly when the conditional does, and answer the same
    -- boolean)
    | a, .false_ => return .binary c .and a
    | .true_, b => return .binary c .or b
    | a, b => return .ternary c a b

/-- An arrow function of parameters `ps` (already in `sc`). -/
partial def arrowToMini {C M : List JsTy} {τ : JsTy} (sc : Scope) (ps : List String)
    (body : JsBlock S C M [] (.ret τ)) : PM MiniExpr := do
  let params := ps.map fun p => MiniParam.plain (.ident (nes p))
  match body with
  | .ret e => return .arrow false params (.expr (← exprToMini sc e))
  | _ =>
    match ← blockToMini sc {} body with
    | [.return_ (some e)] => return .arrow false params (.expr e)
    | ss => return .arrow false params (.block ss)

/-- Arguments. -/
partial def argsToMini {C M σs : List JsTy} (sc : Scope) : JsArgs S C M σs → PM (List MiniExpr)
  | .nil => pure []
  | .cons a as => do return (← exprToMini sc a) :: (← argsToMini sc as)

/-- The parts of an array literal (a spread `...a`). -/
partial def partsToMini {C M : List JsTy} {A E : JsTy} (sc : Scope) :
    JsParts S C M A E → PM (List MiniExpr)
  | .nil => pure []
  | .elem e rest => do return (← exprToMini sc e) :: (← partsToMini sc rest)
  | .spread a rest => do return .spread (← exprToMini sc a) :: (← partsToMini sc rest)

/-- The subject of a case analysis or the bound of a loop: itself when it is an atom,
    otherwise a new constant (`const s$k = e;`) holding it. -/
partial def bindSubject {C M : List JsTy} {τ : JsTy} (sc : Scope) (hint : String)
    (e : JsExpr S C M τ) : PM (List MiniStatement × MiniExpr) := do
  let m ← exprToMini sc e
  if e.isAtom then return ([], m) else
  let s ← freshName hint
  return ([constDecl s m], ident s)

/-- A block as `MiniAST` statements. -/
partial def blockToMini {C M J : List JsTy} {k : JsEnd} (sc : Scope) (tl : Tail) :
    JsBlock S C M J k → PM (List MiniStatement)
  | .ret e => do return [.return_ (some (← exprToMini sc e))]
  | .next =>
    if tl.loop then pure [] else
    match sc.loop with
    | .cont => pure [.continue_ none]
    | .brk l => pure [.break_ (some (nes l))]
    | .none => pure []
  | .jump j e => do
    -- a jump passing no value (`undefined`, to a shared tail, `JsTerm.Lower.ShareTail`)
    -- assigns nothing
    let noValue := match e with
      | .unreachable _ => true
      | _ => false
    let e ← exprToMini sc e
    match sc.joins[j.index]? with
    -- the exit of a loop followed by `return` of what it passes (`countdown`): `return e;`
    | some (_, "") => return [.return_ (some e)]
    | some (label, x) =>
      let set : List MiniStatement := if noValue then [] else
        if x == unreadJoinVar then [.expr e] else [.expr (.assign (ident x) .assign e)]
      if j.index == 0 && tl.join then return set
      else return set ++ [.break_ (some (nes label))]
    | none =>
      return [.throw (.new (ident "Error") [.string s!"LeanScript: an unknown join point"])]
  | .throw msg => pure [.throw (.new (ident "Error") [.string msg])]
  | .raise e => do return [.throw (.new (ident "Error") [← exprToMini sc e])]
  | .const hint e rest => do
    -- a constant read once, where its computation can be moved to (not in a loop or a closure,
    -- nothing in between that the move would reorder): its value written there
    if constInline e rest then
      let m ← exprToMini sc e
      return ← blockToMini { sc with c := m :: sc.c } tl rest
    let e ← exprToMini sc e
    let x ← freshName hint
    return constDecl x e :: (← blockToMini { sc with c := ident x :: sc.c } tl rest)
  | .letMut hint e rest => do
    let e ← exprToMini sc e
    let x ← freshName hint
    return .decl .let_ ⟨⟨.ident (nes x), some e⟩, []⟩ ::
      (← blockToMini { sc with m := x :: sc.m } tl rest)
  | .assign x e rest => do
    let e ← exprToMini sc e
    let v := nameAt sc.m x.index
    -- `x = c ? a : x;` is `if (c) x = a;` (and `x = c ? x : b;` is `if (!c) x = b;`)
    let s : MiniStatement := match e with
      | .ternary c a b =>
        if b == v then .if_ c (.block [.expr (.assign v .assign a)]) none
        else if a == v then .if_ (negateCond c) (.block [.expr (.assign v .assign b)]) none
        else .expr (.assign v .assign e)
      | _ => .expr (.assign v .assign e)
    return s :: (← blockToMini sc tl rest)
  | .destructure e sel rest => do
    let src := e.fieldSource
    let e ← exprToMini sc e
    let n := sel.binds.length
    let (d, sc') ← destructureToMini sc e sel.binds (readInPlace src n rest)
    return sinkPattern d (← blockToMini sc' tl rest)
  | .ite c t e => do
    let c ← exprToMini sc c
    let t ← blockToMini sc tl t
    let e ← blockToMini sc tl e
    return mkIf c t e
  | .enumCases (shift := shift) e arms => do
    let (pre, s) ← bindSubject sc "s" e
    let keys := arms.keys
    let arms ← enumArmsToMini sc tl s shift 0 arms
    return pre ++ groupedChain (arms.zip keys)
  | .unionCases (id := id) e arms => do
    let (pre, s) ← bindSubject sc "s" e
    -- arms that are all written the same (`if (x.tag === 0) { const { _1: f } = x; return f; }
    -- else { const { _1: f } = x; return f; }`) are written once, without a test
    let src := e.fieldSource (bound := !e.isAtom)
    if let some b ← sameUnionArms sc tl s src arms then return pre ++ b
    let keys := arms.keys
    let arms ← unionArmsToMini sc tl s src (S.reprOf id == .smallIntNullary) 0 arms
    return pre ++ groupedChain (arms.zip keys)
  | .join hint block rest => do
    -- a value that `rest` does not read is not kept (no `let x;`)
    let read := rest.mentions ⟨false, 0⟩
    let x ← if read then freshName hint else pure unreadJoinVar
    -- the labelled block is only needed when a jump leaves it before its end; otherwise its
    -- statements run on into `rest` (every name of a function is distinct)
    let early := block.earlyJump 0 true
    let label ← if early then freshLabel else pure ""
    let b ← blockToMini { sc with joins := (label, x) :: sc.joins } { join := true } block
    let r ← blockToMini { sc with c := ident x :: sc.c } tl rest
    let decl : MiniStatement := .decl .let_ ⟨⟨.ident (nes x), none⟩, []⟩
    if !read then
      return (if early then [.labelled (nes label) (.block b)] else b) ++ r
    if early then return decl :: .labelled (nes label) (.block b) :: r
    -- `let x; …; x = e;` with no other assignment of `x` is `…; const x = e;`
    match b.getLast? with
    | some (.expr (.assign (.ident y) .assign e)) =>
      if y == nes x && assignsTo x b == 1 then return b.dropLast ++ constDecl x e :: r
      else return decl :: b ++ r
    | _ => return decl :: b ++ r
  | .forRange hint nt n body rest => do
    let (pre, n) ← bindSubject sc "n" n
    let i ← freshName hint
    let b ← blockToMini { c := ident i :: sc.c, m := sc.m, loop := .cont } { loop := true } body
    let r ← blockToMini sc tl rest
    return pre ++ .for_ (.decl .let_ ⟨⟨.ident (nes i), some (natLitOf nt 0)⟩, []⟩)
      (some (.binary (ident i) .lt n)) (some (.postfix (ident i) .incr)) (.block b) :: r
  | .countdown hint nt n base step rest => do
    let n ← exprToMini sc n
    let j ← freshName hint
    -- `return x` of what the loop passes: every exit is `return e;`
    let direct := match rest with
      | .ret (.cvar .zero) => true
      | _ => false
    let x ← if direct then pure "" else freshName "r"
    let label ← if direct then pure "" else freshLabel
    let sc' : Scope := { c := sc.c, m := j :: sc.m, joins := [(label, x)], loop := .cont }
    let b ← blockToMini sc' {} base
    let s ← blockToMini sc' { loop := true } step
    let test : MiniExpr := .binary (ident j) .strictEq (natLitOf nt 0)
    -- the base ends the loop (it jumps out): no `else` is needed
    let body : List MiniStatement :=
      .if_ test (.block b) none :: .expr (.postfix (ident j) .decr) :: s
    let loop : MiniStatement := .while_ .true_ (.block body)
    let decl : MiniStatement := .decl .let_ ⟨⟨.ident (nes j), some n⟩, []⟩
    if direct then return [decl, loop]
    let r ← blockToMini { sc with c := ident x :: sc.c } tl rest
    return decl :: .decl .let_ ⟨⟨.ident (nes x), none⟩, []⟩ :: .labelled (nes label) loop :: r
  | .tick nt j base rest => do
    let v := nameAt sc.m j.index
    let b ← blockToMini sc {} base
    let r ← blockToMini sc tl rest
    return .if_ (.binary v .strictEq (natLitOf nt 0)) (.block b) none ::
      .expr (.postfix v .decr) :: r
  | .natCase hint nt n zero succ => do
    let (pre, m) ← bindSubject sc "n" n
    let z ← blockToMini sc {} zero
    let p : MiniExpr := .binary m .minus (natLitOf nt 1)
    -- the predecessor read once, not in a loop or a closure: written at its use
    let us := succ.occs.filter fun o => !o.isMut && o.idx == 0
    let once := us.size == 1 && !us.any (·.again) && !(n matches .mvar _)
    let test : MiniStatement := .if_ (.binary m .strictEq (natLitOf nt 0)) (.block z) none
    if once then
      return pre ++ test :: (← blockToMini { sc with c := p :: sc.c } tl succ)
    let x ← freshName hint
    return pre ++ test :: constDecl x p :: (← blockToMini { sc with c := ident x :: sc.c } tl succ)
  | .forOf hint _ xs body rest => do
    let xs ← exprToMini sc xs
    let x ← freshName hint
    let b ← blockToMini { c := ident x :: sc.c, m := sc.m, loop := .cont } { loop := true } body
    let r ← blockToMini sc tl rest
    return .forOf false (.decl .const (.ident (nes x))) xs (.block b) :: r
  | .funs (τs := τs) hints defs rest => do
    -- consecutive `const`s: every definition is an arrow function, which reads the others
    -- only when it is called, once they are all defined
    let xs ← (List.range τs.length).mapM fun i => freshName (hints.getD i "f")
    let sc' := { sc with c := xs.reverse.map ident ++ sc.c }
    let ds ← argsToMini sc' defs
    let r ← blockToMini sc' tl rest
    return (xs.zip ds).map (fun (x, d) => constDecl x d) ++ r

/-- `const { _1: a, _3: c } = e;` for the fields `binds` keeps (none when it keeps none), and
    the scope with them bound (the last one innermost).  A field `inPlace` says (by its position
    in `binds`) is not bound: it is read in place, `e._2`. -/
partial def destructureToMini (sc : Scope) (e : MiniExpr) (binds : List (Nat × String))
    (inPlace : Nat → Bool := fun _ => false) : PM (List MiniStatement × Scope) := do
  if binds.isEmpty then return ([], sc) else
  let fs ← binds.zipIdx.mapM fun ((i, x), j) =>
    if inPlace j then pure (i, none) else do return (i, some (← freshName x))
  let props := fs.filterMap fun (i, x?) => x?.map fun x =>
    MiniObjectPatternProp.mk (.ident (nes (fieldKey i))) (.ident (nes x))
  let es := fs.map fun (i, x?) => match x? with
    | some x => ident x
    | none => .dot e (nes (fieldKey i))
  let d := if props.isEmpty then [] else [.decl .const ⟨⟨.object props none, some e⟩, []⟩]
  return (d, { sc with c := es.reverse ++ sc.c })

/-- The arms of a case analysis on an enum, each with its test (`s === shift + i`). -/
partial def enumArmsToMini {C M J : List JsTy} {k : JsEnd} {n : Nat} (sc : Scope) (tl : Tail)
    (s : MiniExpr) (shift : Int) (i : Nat) :
    JsEnumArms S C M J k n → PM (List (MiniExpr × List MiniStatement))
  | .nil => pure []
  | .cons b rest => do
    let b ← blockToMini sc tl b
    return (.binary s .strictEq (intNum (shift + i)), b) ::
      (← enumArmsToMini sc tl s shift (i + 1) rest)

/-- The statements of every arm of a case analysis on a union, when there are two arms or
    more and they are all the same (each written from the same state of the printer): the
    statements, the printer's state being the one after the first arm.  The arms are first
    compared as dumps (`JsBlock.pretty`), so that they are only written more than once when
    they are likely to be the same. -/
partial def sameUnionArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (sc : Scope)
    (tl : Tail) (s : MiniExpr) (src : Option (Option Nat)) (arms : JsUnionArms S C M J k cs) :
    PM (Option (List MiniStatement)) := do
  let keys := arms.keys
  match keys with
  | k₀ :: k₁ :: ks =>
    if !(k₁ :: ks).all (· == k₀) then return none
    let st₀ ← get
    let bodies ← arms.bodiesFrom sc tl s src st₀
    match bodies with
    | (b₀, st₁) :: rest =>
      if rest.all (·.1 == b₀) then
        set st₁
        return some b₀
      else
        set st₀
        return none
    | [] => set st₀; return none
  | _ => return none

/-- The statements of each arm of a case analysis on a union (taking its fields apart), each
    written from the printer's state `st`, with the state after it. -/
partial def JsUnionArms.bodiesFrom {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (sc : Scope) (tl : Tail) (s : MiniExpr) (src : Option (Option Nat)) (st : PrintSt) :
    JsUnionArms S C M J k cs → PM (List (List MiniStatement × PrintSt))
  | .nil => pure []
  | .cons sel b rest => do
    set st
    let (d, sc') ← destructureToMini sc s sel.binds (readInPlace src sel.binds.length b)
    let b ← blockToMini sc' tl b
    let st' ← get
    return (d ++ b, st') :: (← rest.bodiesFrom sc tl s src st)

/-- The arms of a case analysis on a union, each with its test (`s.tag === i`), taking the
    fields it uses apart.  When the constructors without fields are numbers (`small`,
    `JsRepr.smallIntNullary`), the test of a constructor without fields is `s === i` (and the
    one of a constructor with fields still `s.tag === i`: a number has no `tag`). -/
partial def unionArmsToMini {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (sc : Scope)
    (tl : Tail) (s : MiniExpr) (src : Option (Option Nat)) (small : Bool) (i : Nat) :
    JsUnionArms S C M J k cs → PM (List (MiniExpr × List MiniStatement))
  | .nil => pure []
  | .cons (fs := fs) sel b rest => do
    let (d, sc') ← destructureToMini sc s sel.binds (readInPlace src sel.binds.length b)
    let b ← blockToMini sc' tl b
    let test : MiniExpr :=
      if small && fs.isEmpty then .binary s .strictEq (natNum i)
      else .binary (.dot s (nes "tag")) .strictEq (natNum i)
    return (test, sinkPattern d b) :: (← unionArmsToMini sc tl s src small (i + 1) rest)
end

end MoreJs
