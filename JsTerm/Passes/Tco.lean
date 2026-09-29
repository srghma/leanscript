module

public import JsTerm.Passes.Unbox

@[expose] public section

set_option autoImplicit false

/-!
# Loops of tail calls

A structurally recursive function whose recursive call is a tail call with other arguments,
`f (n + 1) x = f n (g n x)`, is a `Nat.rec` whose accumulator is a function; the conversion
writes it as a loop building a chain of closures, called once at the end:

```
let acc = base;
for (let i = 0; i < n; i++) { const a = acc; acc = (x) => { …; return a(g(i, x)); }; }
return acc(init);
```

The call runs the closure of the last iteration first (`i = n - 1`), whose tail call runs the
one before, …, down to `base`.  `tcoNode` writes it as a loop over the parameters instead,
counting down, with no closure and no call per iteration (and no stack growing with `n`):

```
let x = init;
for (let j = 0; j < n; j++) { const i = n - 1 - j; …; x = g(i, x); }
return base(x);
```

It applies when every path of the closure's body ends in a tail call of `a` (`return a(…)`,
or a `throw`), `a` is not used otherwise, and no closure of the function reads a mutable
variable (the closures would read them later).  Not proved (`JsTerm` has no semantics);
checked by the snapshots.
-/

namespace MoreJs

/-- `n - 1 - j` at a natural-number representation (`j < n`), with the operations of the
    runtime. -/
def JsNatTy.revIndex {C M : List JsTy} {N : JsTy} (nt : JsNatTy N) (n j : JsExpr C M N) :
    JsExpr C M N :=
  match nt with
  | .bigint_nat =>
    .imported .bigint_nat__lean_nat_sub
      (.cons (.imported .bigint_nat__lean_nat_sub (.cons n (.cons (.lit (.bigint_nat 1)) .nil)))
        (.cons j .nil))
  | .uint53 =>
    .imported .uint53__lean_nat_sub
      (.cons (.imported .uint53__lean_nat_sub
          (.cons n (.cons (.lit (.uint53 1 (by decide))) .nil)))
        (.cons j .nil))

/-- The pattern that keeps every field, with the hints `hs`. -/
def JsSel.all : (ts : List JsTy) → List String → JsSel ts ts
  | [], _ => .nil
  | _ :: ts, hs => .keep (hs.headD "x") (JsSel.all ts hs.tail)

/-- The variables, as arguments. -/
def JsVars.toArgs {C M : List JsTy} : {ts : List JsTy} → JsVars M ts → JsArgs C M ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (.mvar v) vs.toArgs

/-- What `JsBlock.tco` knows: the index of the closure `a` among the constants, the renaming
    of the mutable variables, and the variables holding the parameters. -/
structure Tco (M M' : List JsTy) (σs : List JsTy) (τ : JsTy) where
  a : Nat
  ren : JsRenM Option M M'
  vars : JsVars M' σs
  /-- The variables of the answer and of whether it is known, when the body can return
      without a tail call. -/
  early : Option (JsMem M' τ × JsMem M' (.terminal .bool)) := none

/-- Under one more mutable variable. -/
def Tco.liftM {M M' σs : List JsTy} {τ σ : JsTy} (u : Tco M M' σs τ) :
    Tco (σ :: M) (σ :: M') σs τ :=
  { a := u.a, ren := JsRenM.lift u.ren, vars := u.vars.succ,
    early := u.early.map fun (r, d) => (.succ r, .succ d) }

/-- Under `c` more constants. -/
def Tco.underC {M M' σs : List JsTy} {τ : JsTy} (u : Tco M M' σs τ) (c : Nat) : Tco M M' σs τ :=
  { u with a := u.a + c }

/-- An expression, which must not mention `a`. -/
def Tco.expr {M M' σs : List JsTy} {ρ : JsTy} (u : Tco M M' σs ρ) {C : List JsTy} {τ : JsTy}
    (e : JsExpr C M τ) : Option (JsExpr C M' τ) :=
  if e.mentions ⟨false, u.a⟩ then none else e.renameM (fun x => some x) u.ren

/-- A block (a loop body, or a block that does not return), which must not mention `a`. -/
def Tco.block {M M' σs : List JsTy} {ρ : JsTy} (u : Tco M M' σs ρ) {C J : List JsTy} {k : JsEnd}
    (b : JsBlock C M J k) : Option (JsBlock C M' J k) :=
  if b.mentions ⟨false, u.a⟩ then none else b.renameM (fun x => some x) u.ren

mutual
/-- The body of the closure with every `return a(args)` an assignment of the parameters and the
    end of the iteration; `none` if some path returns otherwise, or `a` is used otherwise. -/
partial def JsBlock.tco {M M' σs : List JsTy} {τ : JsTy} (u : Tco M M' σs τ) {C J : List JsTy} :
    JsBlock C M J (.ret τ) → Option (JsBlock C M' J .loop)
  | .ret (.app (σs := σs') (.cvar x) args) =>
    if x.index != u.a then none else
    if h : σs' = σs then do
      let args : JsArgs C M σs := h ▸ args
      if (args.occsAt {}).any (·.is ⟨false, u.a⟩) then none else
      let args ← args.renameM (fun x => some x) u.ren
      return JsArgs.assignChain u.vars args .next
    else none
  | .ret e =>
    match u.early with
    | some (r, d) => do
      let e ← u.expr e
      return .assign r e (.assign d (.lit (.bool true)) .next)
    | none => none
  | .throw msg => some (.throw msg)
  | .jump j e => return .jump j (← u.expr e)
  | .const x e rest => return .const x (← u.expr e) (← rest.tco (u.underC 1))
  | .letMut x e rest => return .letMut x (← u.expr e) (← rest.tco u.liftM)
  | .assign x e rest => return .assign (← u.ren x) (← u.expr e) (← rest.tco u)
  | .destructure (us := us) e sel rest =>
    return .destructure (← u.expr e) sel (← rest.tco (u.underC us.length))
  | .ite c t e => return .ite (← u.expr c) (← t.tco u) (← e.tco u)
  | .enumCases e arms => return .enumCases (← u.expr e) (← arms.tco u)
  | .unionCases e arms => return .unionCases (← u.expr e) (← arms.tco u)
  | .join x b rest => return .join x (← b.tco u) (← rest.tco (u.underC 1))
  | .forRange x nt n b rest =>
    return .forRange x nt (← u.expr n) (← (u.underC 1).block b) (← rest.tco u)
  | .lastIter x nt n b rest =>
    return .lastIter x nt (← u.expr n) (← (u.underC 1).block b) (← rest.tco u)
  | .forOf x l xs b rest =>
    return .forOf x l (← u.expr xs) (← (u.underC 1).block b) (← rest.tco u)
/-- `tco` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.tco {M M' σs : List JsTy} {τ : JsTy} (u : Tco M M' σs τ) {C J : List JsTy}
    {n : Nat} : JsEnumArms C M J (.ret τ) n → Option (JsEnumArms C M' J .loop n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.tco u) (← rest.tco u)
/-- `tco` in the arms of a case analysis on a union. -/
partial def JsUnionArms.tco {M M' σs : List JsTy} {τ : JsTy} (u : Tco M M' σs τ) {C J : List JsTy}
    {cs : List (List JsTy)} : JsUnionArms C M J (.ret τ) cs → Option (JsUnionArms C M' J .loop cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.tco (u.underC us.length)) (← rest.tco u)
end

/-- The accumulator loop of a tail-recursive function, as the parts `tcoNode` needs: the
    closure of an iteration (its parameters' hints and body) and the call after the loop. -/
structure TcoLoop (C M J : List JsTy) (k : JsEnd) where
  σs : List JsTy
  τ : JsTy
  N : JsTy
  nt : JsNatTy N
  hint : String
  base : JsExpr C M (.fn σs τ)
  n : JsExpr C (.fn σs τ :: M) N
  hints : List String
  body : JsBlock (pushAll σs (.fn σs τ :: N :: C)) (.fn σs τ :: M) [] (.ret τ)
  init : JsArgs C (.fn σs τ :: M) σs
  hk : k = .ret τ

/-- `return f(args);`, taken apart. -/
def JsBlock.retApp? {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k →
    Option ((σs : List JsTy) × (τ : JsTy) × JsExpr C M (.fn σs τ) × JsArgs C M σs ×
      PLift (k = .ret τ))
  | .ret (.app (σs := σs) (τ := τ) f args) => some ⟨σs, τ, f, args, ⟨rfl⟩⟩
  | _ => none

/-- Is the expression the innermost mutable variable? -/
def JsExpr.isMvar0 {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .mvar x => x.index == 0
  | _ => false

/-- `let x = e; for (…) { body } rest`, taken apart. -/
def JsBlock.letMutFor? {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k →
    Option ((F : JsTy) × String × JsExpr C M F × (N : JsTy) × JsNatTy N × JsExpr C (F :: M) N ×
      JsBlock (N :: C) (F :: M) [] .loop × JsBlock C (F :: M) J k)
  | .letMut (τ := F) h base (.forRange (N := N) _ nt n body rest) =>
    some ⟨F, h, base, N, nt, n, body, rest⟩
  | _ => none

/-- `const x = e; rest`, taken apart. -/
def JsBlock.constView? {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k →
    Option ((A : JsTy) × JsExpr C M A × JsBlock (A :: C) M J k)
  | .const (τ := A) _ e rest => some ⟨A, e, rest⟩
  | _ => none

/-- `x = e;` and the end of the iteration, taken apart. -/
def JsBlock.assignNext? {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k →
    Option ((τ : JsTy) × JsMem M τ × JsExpr C M τ)
  | .assign (τ := τ) x e .next => some ⟨τ, x, e⟩
  | _ => none

/-- `(x₁, …) => { B }`, taken apart. -/
def JsExpr.lamView? {C M : List JsTy} {τ : JsTy} : JsExpr C M τ →
    Option ((σs : List JsTy) × (ρ : JsTy) × List String × JsBlock (pushAll σs C) M [] (.ret ρ))
  | .lam (σs := σs) (τ := ρ) hints B => some ⟨σs, ρ, hints, B⟩
  | _ => none

/-- `let acc = base; for (…) { const a = acc; acc = (x) => { B }; } return acc(init);`, taken
    apart. -/
def JsBlock.tcoLoop? {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) :
    Option (TcoLoop C M J k) := do
  let ⟨F, h, base, N, nt, n, body, rest⟩ ← b.letMutFor?
  let ⟨A, ea, body⟩ ← body.constView?
  if !ea.isMvar0 then none
  let ⟨τy, y, el⟩ ← body.assignNext?
  if y.index != 0 then none
  let ⟨σs, τ, hints, B⟩ ← el.lamView?
  let ⟨σs₂, τ₂, f, init, ⟨hk⟩⟩ ← rest.retApp?
  if !f.isMvar0 then none
  if hF : F = .fn σs τ then
    if hA : A = .fn σs τ then
      if h₂ : σs₂ = σs ∧ τ₂ = τ then
        let _ := τy
        return (by
          obtain ⟨h₁, h₂⟩ := h₂
          subst hF hA h₁ h₂
          exact ⟨_, _, _, nt, h, base, n, hints, B, init, hk⟩)
      else none
    else none
  else none

/-- The renaming of the mutable variables that drops the accumulator for the variables of the
    parameters. -/
def JsRen.accToParams {M : List JsTy} {F : JsTy} (σs : List JsTy) :
    JsRenM Option (F :: M) (pushAll σs M) := JsRen.replaceHeadAll σs

/-- The renaming that drops the innermost variable (which must not occur), then renames the
    others by `r`. -/
def JsRen.dropHeadThen {Γ Δ : List JsTy} {σ : JsTy} (r : JsRenM Id Γ Δ) :
    JsRenM Option (σ :: Γ) Δ := fun x =>
  match x with
  | .zero => none
  | .succ x => some (r x)

/-- The loop of a tail-recursive function over its parameters, the mutable variables `M`
    being seen as `Γ` (`wk`), with the variables of an early answer when the body has some. -/
def tcoBuild {C M J : List JsTy} {k : JsEnd} (L : TcoLoop C M J k) (Γ : List JsTy)
    (wk : JsRenM Id M Γ) (early : Option (JsMem Γ L.τ × JsMem Γ (.terminal .bool))) :
    Option (JsBlock C Γ J k) := do
  let F := JsTy.fn L.σs L.τ
  let M' := pushAll L.σs Γ
  let vars : JsVars M' L.σs := JsVars.init L.σs
  let ren : JsRenM Option (F :: M) M' := JsRen.dropHeadThen (fun x => JsRen.skipAll L.σs (wk x))
  -- the initial arguments, before the loop (so the bound is evaluated after them)
  let init ← L.init.renameM (fun x => some x) (JsRen.dropHeadThen wk)
  if !L.n.discardable && !init.discardable then none
  let n' ← L.n.renameM (fun x => some x) ren
  let earlyM : Option (JsMem M' L.τ × JsMem M' (.terminal .bool)) :=
    early.map fun (r, d) => (JsRen.skipAll L.σs r, JsRen.skipAll L.σs d)
  -- the body: `a` is the constant just below the parameters
  let u : Tco (F :: M) M' L.σs L.τ := { a := L.σs.length, ren, vars, early := earlyM }
  let B ← L.body.tco u
  let B ← B.renameM (JsRenM.liftAll L.σs JsRen.strengthen) (fun x => some x)
  -- under the new counter `j`, the old one is `n - 1 - j`
  let B : JsBlock (pushAll L.σs (L.N :: L.N :: C)) M' [] .loop :=
    Id.run (B.renameM (JsRenM.liftAll L.σs (JsRenM.lift JsRen.succ)) JsRen.id)
  let B : JsBlock (L.N :: L.N :: C) M' [] .loop := JsSel.readVars (JsSel.all L.σs L.hints) vars B
  let body : JsBlock (L.N :: C) M' [] .loop := .const "i" (L.nt.revIndex n'.wkC (.cvar .zero)) B
  let body := match earlyM with
    | none => body
    | some (_, d) => .ite (.mvar d) .next body
  let base' : JsExpr C M' F := Id.run (L.base.renameM JsRen.id (fun x => JsRen.skipAll L.σs (wk x)))
  let call : JsExpr C M' L.τ := .app base' vars.toArgs
  let answer : JsExpr C M' L.τ := match earlyM with
    | none => call
    | some (r, d) => .cond (.mvar d) (.mvar r) call
  let rest : JsBlock C M' J k := L.hk ▸ (.ret answer : JsBlock C M' J (.ret L.τ))
  return JsArgs.letChain (L.hints.headD "x") init (.forRange "j" L.nt n' body rest)

/-- The loop of a tail-recursive function over its parameters (see above); when the body can
    also return without a tail call, the answer and whether it is known are two more
    variables (`let r; let done = false;`), the iterations after it do nothing, and the
    answer is `done ? r : base(x)`. -/
def tcoNode (noCapture : Bool) {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) :
    JsBlock C M J k :=
  if !noCapture then b else
  match b.tcoLoop? with
  | none => b
  | some L =>
    if !L.base.discardable then b else
    match tcoBuild L M (fun x => x) none with
    | some r => r
    | none =>
      let Γ := JsTy.terminal .bool :: L.τ :: M
      match tcoBuild L Γ (fun x => .succ (.succ x)) (some (.succ .zero, .zero)) with
      | some r => .letMut "r" (.unreachable L.τ) (.letMut "done" (.lit (.bool false)) r)
      | none => b

/-! ## Calls of known functions -/

/-- Arguments under one more constant. -/
def JsArgs.wkC {C M σs : List JsTy} {σ : JsTy} (as : JsArgs C M σs) : JsArgs (σ :: C) M σs :=
  Id.run (as.renameM JsRen.succ JsRen.id)

/-- The substitution of the arguments for the parameters of a function (its innermost
    constants, the last one innermost). -/
def JsSubst.params {C M : List JsTy} : {σs : List JsTy} → JsArgs C M σs →
    JsSubst (pushAll σs C) M C M
  | [], .nil => { c := fun x => .cvar x, m := JsRen.id }
  | _ :: _, .cons a as =>
    let s₁ := JsSubst.params as.wkC
    { c := fun x => (s₁.c x).subst (JsSubst.inst a), m := JsRen.id }

/-- `((x) => e)(a)` with atoms for arguments: `e` with the arguments for the parameters. -/
def betaNode {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → JsExpr C M τ
  | e@(.app (.lam _ (.ret body)) args) =>
    if args.allAtoms then body.subst (JsSubst.params args) else e
  | e => e

/-- `betaNode`, as a rewrite of every expression. -/
def betaRw : JsExprRewrite := ⟨fun _ _ _ e => betaNode e⟩

end MoreJs

end
