module

public import JsTerm.Syntax.Vars.Occs
public import JsTerm.Syntax.Vars.Rename
public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Recursive functions of a module called by their name

`Term` has no global definitions: a function calling another one of the module has it inlined,
and a function defined by structural recursion is a fold, which the conversion writes as a local
recursive function (`JsTerm.Lower.DataRec`) called once:

```js
export const renderExpr = (a) => {             export const renderExpr = (a) => {
  const go0$1 = (v$2) => { … go0$1(…) … };   ⟶    … renderExpr(…) …
  return go0$1(a);                             };
};
export const test1 = (a) => {                  export const test1 = (a) => {
  const go0$3 = (v$4) => { … go0$3(…) … };        … renderExpr(f$1) …
  … go0$3(f$1) …                               };
};
```

This pass links them back (`linkGlobals`), on the functions of a module:

* **direct recursion** (`JsFun.direct?`): a function whose body only defines one local function,
  which reads none of its parameters, and returns the call of it on all the parameters in order,
  *is* that local function: its body becomes the body of the local function, each recursive
  call a call of the exported function by its name (`JsExpr.global`);
* **calls by name** (`JsBlock.linkFuns`): a local function (`const go = (…) => B; rest`) whose
  code is the code of such a function `f` of the module (the same dump, `JsBlock.pretty`, once
  both are written with their recursive calls as calls of `f`, and `B` reads nothing else) is
  not defined again: `rest` calls `f`.

Both rewrites keep what the code computes: the functions are the same code, the local function
closed over nothing, so calling the function of the module is calling the same code.  A function
of the module is only called by name from a function after it, or from any function when no
constant of the module (a value computed when the module is loaded) comes before it, so that
nothing reads it before it is defined.
-/

namespace MoreJs

variable {S : JsSig}

/-- What each constant becomes: another constant, or a top-level function of the module by its
    name (`none`: it may not be read). -/
abbrev JsSubG (Γ Δ : List JsTy) : Type := ∀ {τ : JsTy}, JsMem Γ τ → Option (JsMem Δ τ ⊕ String)

namespace JsSubG

/-- Under a new binder (renamed to itself). -/
def lift {Γ Δ : List JsTy} {σ : JsTy} (r : JsSubG Γ Δ) : JsSubG (σ :: Γ) (σ :: Δ) := fun x =>
  match x with
  | .zero => some (.inl .zero)
  | .succ x => (r x).map (Sum.map JsMem.succ id)

/-- Under the binders of a pattern. -/
def liftAll {Γ Δ : List JsTy} : (us : List JsTy) → JsSubG Γ Δ → JsSubG (pushAll us Γ) (pushAll us Δ)
  | [], r => r
  | _ :: us, r => liftAll us (lift r)

end JsSubG

mutual
/-- Substitute the constants of an expression (`JsSubG`), rename its mutable variables. -/
def JsExpr.substG {C M C' M' : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M') {τ : JsTy} :
    JsExpr S C M τ → Option (JsExpr S C' M' τ)
  | .cvar x => match rc x with
    | some (.inl y) => some (.cvar y)
    | some (.inr g) => some (.global g)
    | none => none
  | .mvar x => .mvar <$> rm x
  | .lit l => pure (.lit l)
  | .imported op as => .imported op <$> as.substG rc rm
  | .inlined op as => .inlined op <$> as.substG rc rm
  | .unreachable t => pure (.unreachable t)
  | .app f as => return .app (← f.substG rc rm) (← as.substG rc rm)
  | .lam (σs := σs) xs b => .lam xs <$> b.substG (JsSubG.liftAll σs rc) rm
  | .record_mk fs => .record_mk <$> fs.substG rc rm
  | .union_mk ix as => .union_mk ix <$> as.substG rc rm
  | .enum_mk n s i => pure (.enum_mk n s i)
  | .enumIndex nt e => .enumIndex nt <$> e.substG rc rm
  | .enumEq a b => return .enumEq (← a.substG rc rm) (← b.substG rc rm)
  | .index l nt a i => return .index l nt (← a.substG rc rm) (← i.substG rc rm)
  | .array_mk l ps => .array_mk l <$> ps.substG rc rm
  | .list_mk ps => .list_mk <$> ps.substG rc rm
  | .cond c a b => return .cond (← c.substG rc rm) (← a.substG rc rm) (← b.substG rc rm)
  | .listOp op as => .listOp op <$> as.substG rc rm
  | .fold i e => .fold i <$> e.substG rc rm
  | .unfold i e => .unfold i <$> e.substG rc rm
  | .global name => pure (.global name)

/-- `substG` of arguments. -/
def JsArgs.substG {C M C' M' : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M')
    {σs : List JsTy} : JsArgs S C M σs → Option (JsArgs S C' M' σs)
  | .nil => pure .nil
  | .cons a as => return .cons (← a.substG rc rm) (← as.substG rc rm)

/-- `substG` of the parts of an array literal. -/
def JsParts.substG {C M C' M' : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M')
    {A E : JsTy} : JsParts S C M A E → Option (JsParts S C' M' A E)
  | .nil => pure .nil
  | .elem e rest => return .elem (← e.substG rc rm) (← rest.substG rc rm)
  | .spread a rest => return .spread (← a.substG rc rm) (← rest.substG rc rm)

/-- `substG` of a block. -/
def JsBlock.substG {C M C' M' J : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M')
    {k : JsEnd} : JsBlock S C M J k → Option (JsBlock S C' M' J k)
  | .ret e => .ret <$> e.substG rc rm
  | .next => pure .next
  | .jump j e => .jump j <$> e.substG rc rm
  | .throw msg => pure (.throw msg)
  | .const x e rest => return .const x (← e.substG rc rm) (← rest.substG rc.lift rm)
  | .letMut x e rest => return .letMut x (← e.substG rc rm) (← rest.substG rc (JsRenM.lift rm))
  | .assign x e rest => return .assign (← rm x) (← e.substG rc rm) (← rest.substG rc rm)
  | .destructure (us := us) e sel rest =>
    return .destructure (← e.substG rc rm) sel (← rest.substG (JsSubG.liftAll us rc) rm)
  | .ite c t e => return .ite (← c.substG rc rm) (← t.substG rc rm) (← e.substG rc rm)
  | .enumCases e arms => return .enumCases (← e.substG rc rm) (← arms.substG rc rm)
  | .unionCases e arms => return .unionCases (← e.substG rc rm) (← arms.substG rc rm)
  | .join x b rest => return .join x (← b.substG rc rm) (← rest.substG rc.lift rm)
  | .forRange x nt n b rest =>
    return .forRange x nt (← n.substG rc rm) (← b.substG rc.lift rm) (← rest.substG rc rm)
  | .forOf x l xs b rest =>
    return .forOf x l (← xs.substG rc rm) (← b.substG rc.lift rm) (← rest.substG rc rm)
  | .countdown x nt n b s rest =>
    return .countdown x nt (← n.substG rc rm) (← b.substG rc (JsRenM.lift rm))
      (← s.substG rc (JsRenM.lift rm)) (← rest.substG rc.lift rm)
  | .tick nt j b rest => return .tick nt (← rm j) (← b.substG rc rm) (← rest.substG rc rm)
  | .natCase x nt n z s =>
    return .natCase x nt (← n.substG rc rm) (← z.substG rc rm) (← s.substG rc.lift rm)
  | .funs (τs := τs) xs defs rest =>
    return .funs xs (← defs.substG (JsSubG.liftAll τs rc) rm)
      (← rest.substG (JsSubG.liftAll τs rc) rm)

/-- `substG` of the arms of a case analysis on an enum. -/
def JsEnumArms.substG {C M C' M' J : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M')
    {k : JsEnd} {n : Nat} : JsEnumArms S C M J k n → Option (JsEnumArms S C' M' J k n)
  | .nil => pure .nil
  | .cons b rest => return .cons (← b.substG rc rm) (← rest.substG rc rm)

/-- `substG` of the arms of a case analysis on a union. -/
def JsUnionArms.substG {C M C' M' J : List JsTy} (rc : JsSubG C C') (rm : JsRenM Option M M')
    {k : JsEnd} {cs : List (List JsTy)} : JsUnionArms S C M J k cs → Option (JsUnionArms S C' M' J k cs)
  | .nil => pure .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.substG (JsSubG.liftAll us rc) rm) (← rest.substG rc rm)
end

/-! ## Views -/

/-- A block defining one local function, `const go = (xs) => body; rest`: the types of the
    parameters and the result of the function, its body, and the rest. -/
structure OneFun (S : JsSig) (C M J : List JsTy) (k : JsEnd) where
  σs : List JsTy
  ρ : JsTy
  body : JsBlock S (pushAll σs (JsTy.fn σs ρ :: C)) M [] (.ret ρ)
  rest : JsBlock S (JsTy.fn σs ρ :: C) M J k

/-- The local function a block defines first, when it is its only definition. -/
def JsBlock.oneFun? {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Option (OneFun S C M J k)
  | .funs (τs := [_]) _ (.cons (.lam (σs := σs) (τ := ρ) _ body) .nil) rest =>
    some { σs, ρ, body, rest }
  | _ => none

/-- The indices of the arguments of a call, when they are all constants. -/
def JsArgs.cvarIdxs? {C M σs : List JsTy} : JsArgs S C M σs → Option (List Nat)
  | .nil => some []
  | .cons (.cvar x) as => (x.index :: ·) <$> as.cvarIdxs?
  | .cons _ _ => none

/-- `return f(a₁, …)` (or `const x = f(a₁, …); return x;`), `f` and the `aᵢ` constants: their
    indices. -/
def JsBlock.retCallIdxs? {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Option (Nat × List Nat)
  | .ret (.app (.cvar f) as) => (f.index, ·) <$> as.cvarIdxs?
  | .const _ (.app (.cvar f) as) (.ret (.cvar x)) =>
    if x.index == 0 then (f.index, ·) <$> as.cvarIdxs? else none
  | _ => none

/-- The body of a local function (`OneFun`) in the context of its parameters alone, its
    recursive calls calls of `self`, when it reads nothing else. -/
def OneFun.closedBody? {C M J : List JsTy} {k : JsEnd} (o : OneFun S C M J k) (self : String) :
    Option (JsBlock S (pushAll o.σs []) [] [] (.ret o.ρ)) :=
  let r0 : JsSubG (JsTy.fn o.σs o.ρ :: C) [] := fun x => match x with
    | .zero => some (.inr self)
    | .succ _ => none
  o.body.substG (JsSubG.liftAll o.σs r0) (fun _ => none)

/-- The placeholder name of the function itself in the dumps compared (`JsFun.linkKey`). -/
def selfPlaceholder : String := "$self"

/-! ## Direct recursion -/

/-- The function as its local function, called by name (see the module doc), if its body is
    `const go = (xs) => B; return go(params);`. -/
def JsFun.direct? (f : JsFun) (self : String := f.name) :
    Option (JsBlock f.sig (pushAll (f.params.map (·.2)) []) [] [] (.ret f.ret)) := do
  if f.delegate?.isSome || f.params.isEmpty then none
  let o ← f.body.oneFun?
  let n := f.params.length
  let (g, as) ← o.rest.retCallIdxs?
  unless g == 0 && as == (List.range n).map (fun i => n - i) do none
  let b ← o.closedBody? self
  if h : o.σs = f.params.map (·.2) ∧ o.ρ = f.ret then
    some (by obtain ⟨h1, h2⟩ := h; rw [h1, h2] at b; exact b)
  else none

/-- What a local function must be to be `f` (after `direct?`): the types of its parameters and
    result, and the dump of its code with its recursive calls calls of `selfPlaceholder`. -/
def JsFun.linkKey? (f : JsFun) : Option (List JsTy × JsTy × String) :=
  (f.direct? selfPlaceholder).map fun b => (f.params.map (·.2), f.ret, b.pretty "")

/-! ## Calls by name -/

mutual
/-- `linkFuns` in the closures of an expression. -/
partial def JsExpr.linkFuns {C M : List JsTy} {τ : JsTy} (tbl : List (List JsTy × JsTy × String × String)) :
    JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => .imported op (as.linkFuns tbl)
  | .inlined op as => .inlined op (as.linkFuns tbl)
  | .app f as => .app (f.linkFuns tbl) (as.linkFuns tbl)
  | .lam hints body => .lam hints (body.linkFuns tbl)
  | .record_mk fs => .record_mk (fs.linkFuns tbl)
  | .union_mk ix as => .union_mk ix (as.linkFuns tbl)
  | .enumIndex nt e => .enumIndex nt (e.linkFuns tbl)
  | .enumEq a b => .enumEq (a.linkFuns tbl) (b.linkFuns tbl)
  | .index l nt a i => .index l nt (a.linkFuns tbl) (i.linkFuns tbl)
  | .array_mk l ps => .array_mk l (ps.linkFuns tbl)
  | .list_mk ps => .list_mk (ps.linkFuns tbl)
  | .cond c a b => .cond (c.linkFuns tbl) (a.linkFuns tbl) (b.linkFuns tbl)
  | .listOp op as => .listOp op (as.linkFuns tbl)
  | .fold i e => .fold i (e.linkFuns tbl)
  | .unfold i e => .unfold i (e.linkFuns tbl)
  | e => e
/-- `linkFuns` of arguments. -/
partial def JsArgs.linkFuns {C M σs : List JsTy} (tbl : List (List JsTy × JsTy × String × String)) :
    JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons (a.linkFuns tbl) (as.linkFuns tbl)
/-- `linkFuns` of the parts of an array literal. -/
partial def JsParts.linkFuns {C M : List JsTy} {A E : JsTy}
    (tbl : List (List JsTy × JsTy × String × String)) : JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem (e.linkFuns tbl) (rest.linkFuns tbl)
  | .spread a rest => .spread (a.linkFuns tbl) (rest.linkFuns tbl)
/-- Every local function (`const go = (xs) => B; rest`) that is a function of the module
    listed in `tbl` (its parameter types, result type, `linkKey?` dump and name) is not
    defined: `rest` calls the function of the module.  Bottom-up. -/
partial def JsBlock.linkFuns {C M J : List JsTy} {k : JsEnd}
    (tbl : List (List JsTy × JsTy × String × String)) : JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret (e.linkFuns tbl)
  | .next => .next
  | .jump j e => .jump j (e.linkFuns tbl)
  | .throw m => .throw m
  | .const x e rest => .const x (e.linkFuns tbl) (rest.linkFuns tbl)
  | .letMut x e rest => .letMut x (e.linkFuns tbl) (rest.linkFuns tbl)
  | .assign x e rest => .assign x (e.linkFuns tbl) (rest.linkFuns tbl)
  | .destructure e sel rest => .destructure (e.linkFuns tbl) sel (rest.linkFuns tbl)
  | .ite c t e => .ite (c.linkFuns tbl) (t.linkFuns tbl) (e.linkFuns tbl)
  | .enumCases e arms => .enumCases (e.linkFuns tbl) (arms.linkFuns tbl)
  | .unionCases e arms => .unionCases (e.linkFuns tbl) (arms.linkFuns tbl)
  | .join x block rest => .join x (block.linkFuns tbl) (rest.linkFuns tbl)
  | .forRange x nt n body rest => .forRange x nt (n.linkFuns tbl) (body.linkFuns tbl) (rest.linkFuns tbl)
  | .forOf x l xs body rest => .forOf x l (xs.linkFuns tbl) (body.linkFuns tbl) (rest.linkFuns tbl)
  | .countdown x nt n base step rest =>
    .countdown x nt (n.linkFuns tbl) (base.linkFuns tbl) (step.linkFuns tbl) (rest.linkFuns tbl)
  | .tick nt j base rest => .tick nt j (base.linkFuns tbl) (rest.linkFuns tbl)
  | .natCase x nt n zero succ => .natCase x nt (n.linkFuns tbl) (zero.linkFuns tbl) (succ.linkFuns tbl)
  | b@(.funs hints defs rest) =>
    let keep : JsBlock S C M J k := .funs hints (defs.linkFuns tbl) (rest.linkFuns tbl)
    match b.oneFun? with
    | none => keep
    | some o =>
      match o.closedBody? selfPlaceholder with
      | none => keep
      | some cb =>
        let key := cb.pretty ""
        match tbl.find? fun (σs, ρ, k', _) => σs == o.σs && ρ == o.ρ && k' == key with
        | none => keep
        | some (_, _, _, name) =>
          let rc : JsSubG (JsTy.fn o.σs o.ρ :: C) C := fun x => match x with
            | .zero => some (.inr name)
            | .succ y => some (.inl y)
          match o.rest.substG rc (fun x => some x) with
          | some r => r.linkFuns tbl
          | none => keep
/-- `linkFuns` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.linkFuns {C M J : List JsTy} {k : JsEnd} {n : Nat}
    (tbl : List (List JsTy × JsTy × String × String)) : JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons (b.linkFuns tbl) (rest.linkFuns tbl)
/-- `linkFuns` in the arms of a case analysis on a union. -/
partial def JsUnionArms.linkFuns {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (tbl : List (List JsTy × JsTy × String × String)) : JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.linkFuns tbl) (rest.linkFuns tbl)
end

/-- Link the recursive functions of a module (see the module doc): each function that is its
    local function is written directly (`JsFun.direct?`), and every local function of the
    module that is the code of such a function is a call of it by name (`JsBlock.linkFuns`),
    when that function is defined before, or no constant of the module comes before it. -/
def linkGlobals (funs : List JsFun) : List JsFun :=
  let firstConst : Nat := (funs.findIdx? JsFun.isConst).getD funs.length
  -- the functions that can be called by name: the first version of each Lean definition
  -- (a later one owns some parameter and may update it in place)
  let entries : List (Nat × List JsTy × JsTy × String × String) :=
    funs.zipIdx.filterMap fun (f, i) =>
      if funs.take i |>.any (·.leanName == f.leanName) then none else
      (f.linkKey?).map fun (σs, ρ, key) => (i, σs, ρ, key, f.name)
  funs.zipIdx.map fun (f, i) =>
    let f := match f.direct? with
      | some b => { f with body := b }
      | none => f
    let tbl := entries.filterMap fun (j, σs, ρ, key, name) =>
      if j == i then none
      else if j < i || j < firstConst then some (σs, ρ, key, name) else none
    if tbl.isEmpty then f else { f with body := f.body.linkFuns tbl }

end MoreJs

end
