module

public import JsTerm.Passes.Cleanup

@[expose] public section

set_option autoImplicit false

/-!
# Calls of the closures of a module, inlined

Hoisting (`JsTerm.Passes.Hoist`) moves every closure that captures nothing to the top of the
module (`const $k1 = (x$1, x$2) => x$1;`).  Many of them only compute an expression of their
parameters: the base case of a loop (`$k1(x$3, x$4)` is `x$3`), a helper Lean inlined only
partly (`$k1(n + 1)` with `$k1 = (x) => x * 2`).  `JsModule.inlineConsts` replaces a call of
such a closure by its body, its arguments for its parameters, when the closure is called
from one place only (it is then dropped) or its body is small.

A call `$k(a₁, …, aₙ)` evaluates its arguments left to right, and then the body.  The
inlining is written as the block `const x₁ = a₁; …; const xₙ = aₙ; return body;` whose
constants are then propagated by the rules the backend already uses
(`copyPropagates`: a variable or a literal for every read of it; `inlineOnceNode`: a value
read once, before anything that could have an effect or fail; and an unused value that has
no effect and cannot fail is dropped).  The call is replaced only when every constant goes
this way (the block is `return e;`), so the arguments are still evaluated once each, in the
same order relative to everything that could have an effect or fail.  As for `inlineOnce`, a
function with a closure that assigns a mutable variable it captures is left alone.
-/

namespace MoreJs

/-! ## Which constants a module reads -/

/-- A function on the expressions of every context, folded over. -/
structure JsExprFold (α : Type) where
  run : (C M : List JsTy) → (τ : JsTy) → JsExpr C M τ → α → α

mutual
/-- `f` folded over every expression node of an expression (itself first), closures
    included. -/
partial def JsExpr.foldNodes {α : Type} (f : JsExprFold α) {C M : List JsTy} {τ : JsTy}
    (e : JsExpr C M τ) (acc : α) : α :=
  let acc := f.run _ _ _ e acc
  match e with
  | .imported _ as | .inlined _ as | .record_mk as | .union_mk _ as | .listOp _ as =>
    as.foldNodes f acc
  | .app g as => as.foldNodes f (g.foldNodes f acc)
  | .lam _ b => b.foldNodes f acc
  | .array_mk _ ps | .list_mk ps => ps.foldNodes f acc
  | .cond c a b => b.foldNodes f (a.foldNodes f (c.foldNodes f acc))
  | _ => acc
/-- `foldNodes` of arguments. -/
partial def JsArgs.foldNodes {α : Type} (f : JsExprFold α) {C M σs : List JsTy}
    (as : JsArgs C M σs) (acc : α) : α :=
  match as with
  | .nil => acc
  | .cons a as => as.foldNodes f (a.foldNodes f acc)
/-- `foldNodes` of the parts of an array literal. -/
partial def JsParts.foldNodes {α : Type} (f : JsExprFold α) {C M : List JsTy} {A E : JsTy}
    (ps : JsParts C M A E) (acc : α) : α :=
  match ps with
  | .nil => acc
  | .elem e rest | .spread e rest => rest.foldNodes f (e.foldNodes f acc)
/-- `foldNodes` of the expressions of a block. -/
partial def JsBlock.foldNodes {α : Type} (f : JsExprFold α) {C M J : List JsTy} {k : JsEnd}
    (b : JsBlock C M J k) (acc : α) : α :=
  match b with
  | .ret e | .jump _ e => e.foldNodes f acc
  | .next | .throw _ => acc
  | .const _ e rest | .letMut _ e rest | .assign _ e rest | .destructure e _ rest =>
    rest.foldNodes f (e.foldNodes f acc)
  | .ite c t e => e.foldNodes f (t.foldNodes f (c.foldNodes f acc))
  | .enumCases e arms => arms.foldNodes f (e.foldNodes f acc)
  | .unionCases e arms => arms.foldNodes f (e.foldNodes f acc)
  | .join _ b rest => rest.foldNodes f (b.foldNodes f acc)
  | .forRange _ _ n b rest | .lastIter _ _ n b rest =>
    rest.foldNodes f (b.foldNodes f (n.foldNodes f acc))
  | .forOf _ _ xs b rest => rest.foldNodes f (b.foldNodes f (xs.foldNodes f acc))
/-- `foldNodes` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.foldNodes {α : Type} (f : JsExprFold α) {C M J : List JsTy} {k : JsEnd}
    {n : Nat} (arms : JsEnumArms C M J k n) (acc : α) : α :=
  match arms with
  | .nil => acc
  | .cons b rest => rest.foldNodes f (b.foldNodes f acc)
/-- `foldNodes` of the arms of a case analysis on a union. -/
partial def JsUnionArms.foldNodes {α : Type} (f : JsExprFold α) {C M J : List JsTy}
    {k : JsEnd} {cs : List (List JsTy)} (arms : JsUnionArms C M J k cs) (acc : α) : α :=
  match arms with
  | .nil => acc
  | .cons _ b rest => rest.foldNodes f (b.foldNodes f acc)
end

/-- The module constants an expression node mentions. -/
def globalsFold : JsExprFold (Array String) :=
  ⟨fun _ _ _ e acc => match e with
    | .global n _ => acc.push n
    | _ => acc⟩

/-- The records and constructors with fields an expression node builds. -/
def recordsFold : JsExprFold Nat :=
  ⟨fun _ _ _ e acc => match e with
    | .record_mk .. => acc + 1
    | .union_mk _ (.cons ..) => acc + 1
    | .listOp (.cons _) _ => acc + 1
    | _ => acc⟩

/-- The closures an expression node is. -/
def lamsFold : JsExprFold Nat :=
  ⟨fun _ _ _ e acc => match e with
    | .lam .. => acc + 1
    | _ => acc⟩

/-! ## Binding and propagating the arguments -/

/-- `const x₁ = a₁; …; const xₙ = aₙ; b`: the arguments bound in order, the last one
    innermost, as the parameters of a closure. -/
def JsArgs.bindConsts {C M J : List JsTy} {k : JsEnd} :
    {σs : List JsTy} → JsArgs C M σs → JsBlock (pushAll σs C) M J k → JsBlock C M J k
  | [], .nil, b => b
  | _ :: _, .cons a as, b => .const "x" a (JsArgs.bindConsts as.wkC b)

/-- The body of a closure of the module (over its parameters only), over the parameters bound
    in front of it in any context. -/
def JsExpr.overParams {C M : List JsTy} {σs : List JsTy} {τ : JsTy}
    (b : JsExpr (pushAll σs []) [] τ) : JsExpr (pushAll σs C) M τ :=
  Id.run (b.renameM (JsRenM.liftAll σs (fun x => nomatch x)) (fun x => nomatch x))

/-- The largest number of calls a closure passed as an argument is inlined into. -/
def lamMaxUses : Nat := 4

mutual
/-- `const x = e; rest` simplified if `x` can be propagated (see the module doc).  A closure
    `e` (which reads the variables it captures when it is called, wherever it is written) is
    also propagated into every call of `x` when that leaves no closure more to create: each
    `x(a)` becomes `((y) => body)(a)`, beta-reduced.  A record or a constructor of constants
    and literals is propagated into the patterns and case analyses that take it apart
    (`destructKnownNode`, `unionKnownNode`) when that leaves it built once at most, not in a
    loop or a closure. -/
partial def bindNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if copyPropagates e rest then rest.subst (JsSubst.inst e) else
    let uses := (rest.occs.filter (·.is ⟨false, 0⟩)).size
    if uses == 1 && rest.headRead == .found then rest.subst (JsSubst.inst e) else
    if uses == 0 && e.firstRead (C.length + 1) == .clean then
      match rest.renameM (m := Option) JsRen.strengthen (fun x => some x) with
      | some r => r
      | none => b
    else
    match e, rest with
    | f@(.lam _ (.ret _)), rest =>
      if uses == 0 || uses > lamMaxUses then b else
      let r := (rest.subst (JsSubst.inst f)).mapBU ⟨fun _ _ _ e => betaInlineNode e⟩ .id
      if r.foldNodes lamsFold 0 == rest.foldNodes lamsFold 0 then r else b
    | e@(.record_mk _), rest => knownValue e rest b
    | e@(.union_mk _ _), rest => knownValue e rest b
    | _, _ => b
  | b => b
where
  /-- `const x = e; rest` (the block `b`), `e` a record or a constructor of constants and
      literals, with `e` propagated into the case analyses of `x`. -/
  knownValue {C M J : List JsTy} {k : JsEnd} {τ : JsTy} (e : JsExpr C M τ)
      (rest : JsBlock (τ :: C) M J k) (b : JsBlock C M J k) : JsBlock C M J k :=
    let occs := rest.occs.filter (·.is ⟨false, 0⟩)
    if !e.isConstValue || occs.any (fun o => o.again || o.inClosure) then b else
    let r := (rest.subst (JsSubst.inst e)).mapBU .id
      ⟨fun _ _ _ _ b => destructKnownNode (unionKnownNode b)⟩
    if r.foldNodes recordsFold 0 ≤ rest.foldNodes recordsFold 0 + 1 then r else b

/-- The expression `body` (over the parameters bound in front of it) with the arguments `as`
    for its parameters, if they all propagate (see the module doc). -/
partial def inlineBodyIn? {C M σs : List JsTy} {τ : JsTy} (body : JsExpr (pushAll σs C) M τ)
    (as : JsArgs C M σs) : Option (JsExpr C M τ) :=
  let b : JsBlock C M [] (.ret τ) := as.bindConsts (.ret body)
  match b.mapBU .id ⟨fun _ _ _ _ b => bindNode b⟩ with
  | .ret e => some e
  | _ => none

/-- A closure called where it is written, `((x) => e)(a)`, beta-reduced if its arguments
    propagate. -/
partial def betaInlineNode {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : JsExpr C M τ :=
  match e with
  | .app (.lam _ (.ret body)) as => (inlineBodyIn? body as).getD e
  | e => e
end

/-- The body of a closure of the module with the arguments `as` for its parameters. -/
def inlineBody? {C M σs : List JsTy} {τ : JsTy} (body : JsExpr (pushAll σs []) [] τ)
    (as : JsArgs C M σs) : Option (JsExpr C M τ) :=
  inlineBodyIn? body.overParams as

/-! ## The closures that can be inlined -/

/-- A closure of the module that returns an expression of its parameters. -/
structure InlineCand where
  name : String
  params : List JsTy
  ret : JsTy
  body : JsExpr (pushAll params []) [] ret

mutual
/-- The number of nodes of an expression (a closure counts as many). -/
partial def JsExpr.size {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Nat
  | .imported _ as | .inlined _ as | .record_mk as | .union_mk _ as | .listOp _ as => as.size + 1
  | .app f as => f.size + as.size + 1
  | .lam .. => 100
  | .array_mk _ ps | .list_mk ps => ps.size + 1
  | .cond c a b => c.size + a.size + b.size + 1
  | _ => 1
/-- The number of nodes of arguments. -/
partial def JsArgs.size {C M σs : List JsTy} : JsArgs C M σs → Nat
  | .nil => 0
  | .cons a as => a.size + as.size
/-- The number of nodes of the parts of an array literal. -/
partial def JsParts.size {C M : List JsTy} {A E : JsTy} : JsParts C M A E → Nat
  | .nil => 0
  | .elem e rest | .spread e rest => e.size + rest.size
end

/-- The closure a module constant is, if it returns an expression. -/
def JsConst.inlineCand? (c : JsConst) : Option InlineCand :=
  match c with
  | ⟨name, _, .lam (σs := σs) (τ := τ) _ (.ret b)⟩ => some ⟨name, σs, τ, b⟩
  | _ => none

/-- The body of a candidate at the type of a call. -/
def castBody {σs₀ σs : List JsTy} {τ₀ τ : JsTy} (h₁ : σs₀ = σs) (h₂ : τ₀ = τ)
    (b : JsExpr (pushAll σs₀ []) [] τ₀) : JsExpr (pushAll σs []) [] τ := by
  subst h₁; subst h₂; exact b

/-- A call of one of the candidates `cands`, or of a closure written where it is called,
    inlined if its arguments propagate. -/
def inlineCallRw (cands : Array InlineCand) : JsExprRewrite :=
  ⟨fun _ _ τ e => match e with
    | .app (σs := σs) (.global n _) as =>
      match cands.find? (·.name == n) with
      | some ⟨_, ps, r, body⟩ =>
        if h : ps = σs ∧ r = τ then (inlineBody? (castBody h.1 h.2 body) as).getD e else e
      | none => e
    | e => betaInlineNode e⟩

/-- The module constants the constants and functions mention (with repetitions). -/
def moduleGlobals (consts : List JsConst) (funs : List JsFun) : Array String :=
  let acc := consts.foldl (fun acc c => c.e.foldNodes globalsFold acc) #[]
  funs.foldl (fun acc f => f.body.foldNodes globalsFold acc) acc

/-- The constants something still mentions: the others are dropped (until none is). -/
partial def dropUnused (consts : List JsConst) (funs : List JsFun) : List JsConst :=
  let used := moduleGlobals consts funs
  let consts' := consts.filter fun c => used.contains c.name
  if consts'.length == consts.length then consts else dropUnused consts' funs

/-! ## The pass -/

/-- The largest body inlined at every call (a closure called from one place only is inlined
    whatever its size). -/
def inlineMaxSize : Nat := 5

/-! ## Closures with a block for body, called once in tail position -/

mutual
/-- A block under more join points (after the ones it may jump to). -/
partial def JsBlock.wkJ {C M J : List JsTy} {k : JsEnd} (K : List JsTy) :
    JsBlock C M J k → JsBlock C M (J ++ K) k
  | .ret e => .ret e
  | .next => .next
  | .jump j e => .jump (j.appendR K) e
  | .throw msg => .throw msg
  | .const x e rest => .const x e (rest.wkJ K)
  | .letMut x e rest => .letMut x e (rest.wkJ K)
  | .assign x e rest => .assign x e (rest.wkJ K)
  | .destructure e sel rest => .destructure e sel (rest.wkJ K)
  | .ite c t e => .ite c (t.wkJ K) (e.wkJ K)
  | .enumCases e arms => .enumCases e (arms.wkJ K)
  | .unionCases e arms => .unionCases e (arms.wkJ K)
  | .join x b rest => .join x (b.wkJ K) (rest.wkJ K)
  | .forRange x nt n b rest => .forRange x nt n b (rest.wkJ K)
  | .lastIter x nt n b rest => .lastIter x nt n b (rest.wkJ K)
  | .forOf x l xs b rest => .forOf x l xs b (rest.wkJ K)
/-- `wkJ` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.wkJ {C M J : List JsTy} {k : JsEnd} {n : Nat} (K : List JsTy) :
    JsEnumArms C M J k n → JsEnumArms C M (J ++ K) k n
  | .nil => .nil
  | .cons b rest => .cons (b.wkJ K) (rest.wkJ K)
/-- `wkJ` in the arms of a case analysis on a union. -/
partial def JsUnionArms.wkJ {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (K : List JsTy) : JsUnionArms C M J k cs → JsUnionArms C M (J ++ K) k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.wkJ K) (rest.wkJ K)
end

/-- A closure of the module whose body is a block. -/
structure InlineBlockCand where
  name : String
  params : List JsTy
  ret : JsTy
  body : JsBlock (pushAll params []) [] [] (.ret ret)

/-- The closure a module constant is, if its body is a block other than `return e;` (and no
    closure of it assigns a variable it captures). -/
def JsConst.inlineBlockCand? (c : JsConst) : Option InlineBlockCand :=
  match c with
  | ⟨_, _, .lam _ (.ret _)⟩ => none
  | ⟨name, _, .lam (σs := σs) (τ := τ) _ b⟩ =>
    if b.closureWrites then none else some ⟨name, σs, τ, b⟩
  | _ => none

/-- The body of a block candidate at the type of a call. -/
def castBlock {σs₀ σs : List JsTy} {τ₀ τ : JsTy} (h₁ : σs₀ = σs) (h₂ : τ₀ = τ)
    (b : JsBlock (pushAll σs₀ []) [] [] (.ret τ₀)) : JsBlock (pushAll σs []) [] [] (.ret τ) := by
  subst h₁; subst h₂; exact b

/-- `return f(a₁, …, aₙ);`, `f` a closure of the module whose body is a block: that block,
    after `const x₁ = a₁; …; const xₙ = aₙ;` (propagated as far as they go).  The body
    returns what the call returned, and its jumps are to its own join points. -/
def inlineTailCall {C M J σs : List JsTy} {τ : JsTy}
    (body : JsBlock (pushAll σs []) [] [] (.ret τ)) (as : JsArgs C M σs) : JsBlock C M J (.ret τ) :=
  let b : JsBlock (pushAll σs C) M [] (.ret τ) :=
    Id.run (body.renameM (JsRenM.liftAll σs (fun x => nomatch x)) (fun x => nomatch x))
  let b : JsBlock (pushAll σs C) M J (.ret τ) := List.nil_append J ▸ b.wkJ J
  (as.bindConsts b).mapBU .id ⟨fun _ _ _ _ b => bindNode b⟩

/-- A call of one of the block candidates `cands` in tail position, inlined. -/
def inlineTailNode (cands : Array InlineBlockCand) :
    {C M J : List JsTy} → {k : JsEnd} → JsBlock C M J k → JsBlock C M J k
  | _, _, _, _, .ret (τ := τ) (.app (σs := σs) (.global n _) as) =>
    let b := .ret (.app (.global n (.fn σs τ)) as)
    match cands.find? (·.name == n) with
    | some ⟨_, ps, r, body⟩ =>
      if h : ps = σs ∧ r = τ then inlineTailCall (castBlock h.1 h.2 body) as else b
    | none => b
  | _, _, _, _, b => b

/-- One round of inlining: the calls of the candidates in the functions and in the other
    constants, then the constants nobody mentions dropped. -/
def inlineConstsRound (isFun : JsConst → Bool) (consts : List JsConst) (funs : List JsFun) :
    List JsConst × List JsFun :=
  let used := moduleGlobals consts funs
  let cands := (consts.filterMap JsConst.inlineCand?).toArray.filter fun c =>
    used.count c.name == 1 || c.body.size ≤ inlineMaxSize
  let rw := inlineCallRw cands
  -- a closure whose body is a block, called once, in tail position
  let blockCands := (consts.filter fun c => used.count c.name == 1 && !isFun c).filterMap
    JsConst.inlineBlockCand? |>.toArray
  let funs := funs.map fun f =>
    if f.body.closureWrites then f else
    { f with body := f.body.mapBU rw ⟨fun _ _ _ _ b => inlineTailNode blockCands b⟩ }
  let consts := consts.map fun c =>
    if c.e.closureWrites then c else
    -- a candidate is not inlined into itself (its body only mentions others)
    { c with e := c.e.mapBU (inlineCallRw (cands.filter (·.name != c.name))) .id }
  (dropUnused consts funs, funs)

/-- Inline the calls of the closures of a module (see the module doc), in two rounds (a body
    inlined can call another closure).  A closure whose body is a block is not inlined when
    `isFun` says it is the same as an exported function (which `JsModule.shareFuns` calls
    instead). -/
def inlineConsts (isFun : JsConst → Bool) (consts : List JsConst) (funs : List JsFun) :
    List JsConst × List JsFun :=
  let (consts, funs) := inlineConstsRound isFun consts funs
  inlineConstsRound isFun consts funs

end MoreJs

end
