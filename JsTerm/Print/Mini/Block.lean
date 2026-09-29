import JsTerm.Print.Mini.Basic

/-!
# Printing the JavaScript grammar: expressions and blocks

The conversion of the expressions (`exprToMini`) and blocks (`blockToMini`) of the grammar to
`MiniAST` expressions and statements, as described in `JsTerm.Print.Mini`.

(Not a `module`: `LanguageJavascriptMini` is not written in the module system.)
-/

namespace MoreJs

open Language.JavaScript Language.JavaScript.MiniAST NonEmpty.String

/-! ## The conversion -/

/-- The literal `0` of a counter (`0n` for a `BigInt`). -/
def natLitOf {N : JsTy} (nt : JsNatTy N) (n : Nat) : MiniExpr :=
  match nt with
  | .bigint_nat => bigintNum n
  | .uint53 => natNum n

/-- The dump of each arm of a case analysis on a union (with the fields it takes apart). -/
partial def JsUnionArms.keys {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → List String
  | .nil => []
  | .cons sel b rest => (toString (sel.binds.map (·.1)) ++ b.pretty "") :: rest.keys

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
    let c ← exprToMini sc c
    match ← exprToMini sc a, ← exprToMini sc b with
    | .true_, .false_ => return c
    | .false_, .true_ => return negateCond c
    | a, b => return .ternary c a b

/-- An arrow function of parameters `ps` (already in `sc`). -/
partial def arrowToMini {C M : List JsTy} {τ : JsTy} (sc : Scope) (ps : List String)
    (body : JsBlock C M [] (.ret τ)) : PM MiniExpr := do
  let params := ps.map fun p => MiniParam.plain (.ident (nes p))
  match body with
  | .ret e => return .arrow false params (.expr (← exprToMini sc e))
  | _ =>
    match ← blockToMini sc {} body with
    | [.return_ (some e)] => return .arrow false params (.expr e)
    | ss => return .arrow false params (.block ss)

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
    return mkIf c t e
  | .enumCases (shift := shift) e arms => do
    let (pre, s) ← bindSubject sc "s" e
    let arms ← enumArmsToMini sc tl s shift 0 arms
    return pre ++ ifChain arms
  | .unionCases e arms => do
    let (pre, s) ← bindSubject sc "s" e
    -- arms that are all written the same (`if (x.tag === 0) { const { _1: f } = x; return f; }
    -- else { const { _1: f } = x; return f; }`) are written once, without a test
    if let some b ← sameUnionArms sc tl s arms then return pre ++ b
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
    -- `let x; …; x = e;` with no other assignment of `x` is `…; const x = e;`
    match b.getLast? with
    | some (.expr (.assign (.ident y) .assign e)) =>
      if y == nes x && assignsTo x b == 1 then return b.dropLast ++ constDecl x e :: r
      else return decl :: b ++ r
    | _ => return decl :: b ++ r
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

/-- The statements of every arm of a case analysis on a union, when there are two arms or
    more and they are all the same (each written from the same state of the printer): the
    statements, the printer's state being the one after the first arm.  The arms are first
    compared as dumps (`JsBlock.pretty`), so that they are only written more than once when
    they are likely to be the same. -/
partial def sameUnionArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (sc : Scope)
    (tl : Tail) (s : MiniExpr) (arms : JsUnionArms C M J k cs) :
    PM (Option (List MiniStatement)) := do
  let keys := arms.keys
  match keys with
  | k₀ :: k₁ :: ks =>
    if !(k₁ :: ks).all (· == k₀) then return none
    let st₀ ← get
    let bodies ← arms.bodiesFrom sc tl s st₀
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
    (sc : Scope) (tl : Tail) (s : MiniExpr) (st : PrintSt) :
    JsUnionArms C M J k cs → PM (List (List MiniStatement × PrintSt))
  | .nil => pure []
  | .cons sel b rest => do
    set st
    let (d, sc') ← destructureToMini sc s sel.binds
    let b ← blockToMini sc' tl b
    let st' ← get
    return (d ++ b, st') :: (← rest.bodiesFrom sc tl s st)

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

end MoreJs
