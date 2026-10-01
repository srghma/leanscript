module

public import LeanScript.Term.Optimize.OpenCallEval
public import LeanScript.Term.Optimize.InlineSubstEval
public import LeanScript.Term.Optimize.Count

@[expose] public section

set_option autoImplicit false

/-!
# Delays that only force another delay

A known delay whose body only forces another delay and answers its value,

```
val k := lazy (let x := e (); ret x)        -- `() => e()` in JavaScript
val k := thunk (let x := force e; ret x)
```

is that other delay: a delay denotes the value it holds (`Ty.den` of `.lazy τ` is `Ty.den` of
`τ`), so `k` and `e` have the same value.  `Term.delayEta` replaces every mention of such a `k`
by `e` (`AInfo`, `PExpr.subA`), so that the `val` becomes dead and is dropped by `Term.dce`.  The
translation of `fun (f : Unit → Bool) (a b : Unit) => f a`, which wraps `f` into a new delay
`() => f()`, becomes `fun f => f` (`Tests/SnapshotsPBOPure/EsPrecedence01.lean`).

Only an `e` of the level of `k` replaces it, so the walk keeps every level index: it never
changes the shape of a statement, only the pure expressions in it.

**Proved:** `Term.delayEta_eval` (the value does not change) and `Term.numCalls_delayEta` (the
number of calls does not change).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## What is known -/

/-- For each known value in scope, a pure expression of the current contexts, of the same type
    and level, with the same value (when one is known). -/
structure AInfo (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Type where
  get : ∀ {ty : Ty ks} {o : Lvl}, KVar Φ ty o → Option (PExpr Δ Φ Γ ty o)

/-- Nothing is known. -/
def AInfo.empty {Φ : KCtx ks} {Γ : UCtx ks} : AInfo Δ Φ Γ := ⟨fun _ => none⟩

/-- The lookup under one more known binder. -/
def AInfo.consGet {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) :
    {b : KBinder ks} → Option (PExpr Δ Φ Γ b.ty b.lv) → {ty : Ty ks} → {o : Lvl} →
    KVar (b :: Φ) ty o → Option (PExpr Δ (b :: Φ) Γ ty o)
  | _, new, _, _, .head => new.bind (·.rename KRen.wk1 URen.id)
  | _, _, _, _, .tail k => (I.get k).bind (·.rename KRen.wk1 URen.id)

/-- Under one more known binder, whose value is `new` (when known). -/
def AInfo.cons {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} (new : Option (PExpr Δ Φ Γ b.ty b.lv))
    (I : AInfo Δ Φ Γ) : AInfo Δ (b :: Φ) Γ :=
  ⟨fun k => I.consGet new k⟩

/-- Under the unknowns `bs`. -/
def AInfo.wkN {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) (bs : UCtx ks) : AInfo Δ Φ (bs ++ Γ) :=
  ⟨fun k => (I.get k).bind (·.rename KRen.id (URen.wkN bs))⟩

/-- Under one more unknown. -/
def AInfo.wk1 {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) (b : UBinder ks) :
    AInfo Δ Φ (b :: Γ) :=
  ⟨fun k => (I.get k).bind (·.rename KRen.id URen.wk1)⟩

/-- `I` describes the values of `κ`. -/
def AInfo.Agree {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    Prop :=
  ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (e : PExpr Δ Φ Γ ty o), I.get k = some e →
    e.eval κ ρ = κ.get k

/-! ## Delays that force a delay -/

/-- `c` is `e ()` and `b` is `ret x` for the result `x` of `c`: the delay `e`. -/
def Comp.lazyEtaWith {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} {τ : Ty ks false}
    {u : Usage01ω} {o' : Lvl} : {σ : Ty ks} → {ℓ : Nat} → Comp Δ d Φ Γ σ ℓ →
    Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ.relax js o' → Option ((ℓ : Nat) × PExpr Δ Φ Γ (.lazy τ) (some ℓ))
  | _, _, .lazy_force (τ := τ') e, b =>
      if h : τ' = τ then b.retHead?.map fun _ => ⟨_, h ▸ e⟩ else none
  | _, _, .app _ _ _, _ => none
  | _, _, .share _, _ => none
  | _, _, .nat_rec _ _ _ _, _ => none
  | _, _, .array_foldl _ _ _ _, _ => none
  | _, _, .data_rec _ _ _ _ _ _ _, _ => none
  | _, _, .data_brec _ _ _ _ _ _ _ _, _ => none
  | _, _, .thunk_force _, _ => none

/-- `c` is `force e` and `b` is `ret x` for the result `x` of `c`: the delay `e`. -/
def Comp.thunkEtaWith {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} {τ : Ty ks false}
    {u : Usage01ω} {o' : Lvl} : {σ : Ty ks} → {ℓ : Nat} → Comp Δ d Φ Γ σ ℓ →
    Term Δ d Φ (⟨σ, u, d⟩ :: Γ) τ.relax js o' → Option ((ℓ : Nat) × PExpr Δ Φ Γ (.thunk τ) (some ℓ))
  | _, _, .thunk_force (τ := τ') e, b =>
      if h : τ' = τ then b.retHead?.map fun _ => ⟨_, h ▸ e⟩ else none
  | _, _, .app _ _ _, _ => none
  | _, _, .share _, _ => none
  | _, _, .nat_rec _ _ _ _, _ => none
  | _, _, .array_foldl _ _ _ _, _ => none
  | _, _, .data_rec _ _ _ _ _ _ _, _ => none
  | _, _, .data_brec _ _ _ _ _ _ _ _, _ => none
  | _, _, .lazy_force _, _ => none

/-- `let x := e (); ret x`: the delay `e`. -/
def Term.lazyForceRet? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} {τ : Ty ks false} :
    {o : Lvl} → Term Δ d Φ Γ τ.relax js o → Option ((ℓ : Nat) × PExpr Δ Φ Γ (.lazy τ) (some ℓ))
  | _, .letE _ c b => c.lazyEtaWith b
  | _, .ret _ => none
  | _, .letV _ _ _ => none
  | _, .record_casesOn _ _ _ => none
  | _, .branch _ => none
  | _, .jump _ _ => none

/-- `let x := force e; ret x`: the delay `e`. -/
def Term.thunkForceRet? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} {τ : Ty ks false} :
    {o : Lvl} → Term Δ d Φ Γ τ.relax js o → Option ((ℓ : Nat) × PExpr Δ Φ Γ (.thunk τ) (some ℓ))
  | _, .letE _ c b => c.thunkEtaWith b
  | _, .ret _ => none
  | _, .letV _ _ _ => none
  | _, .record_casesOn _ _ _ => none
  | _, .branch _ => none
  | _, .jump _ _ => none

/-- A lazy delay whose open body only forces the delay `e` is `e`, when `e` has its level. -/
def Body.lazyAlias? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} :
    {o : Lvl} → Body Δ d Φ Γ [] τ.relax o → Option (PExpr Δ Φ Γ (.lazy τ) o)
  | _, .closed _ => none
  | _, .opened (m := m) t _ =>
      t.lazyForceRet?.bind fun r => if h : r.1 = m then some (h ▸ r.2) else none

/-- A memoised delay whose open body only forces the delay `e` is `e`, when `e` has its level. -/
def Body.thunkAlias? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks false} :
    {o : Lvl} → Body Δ d Φ Γ [] τ.relax o → Option (PExpr Δ Φ Γ (.thunk τ) o)
  | _, .closed _ => none
  | _, .opened (m := m) t _ =>
      t.thunkForceRet?.bind fun r => if h : r.1 = m then some (h ▸ r.2) else none

/-- What a value is equal to: a delay whose open body only forces the delay `e` is `e`, when
    `e` has the level of the value. -/
def Val.delayAlias? : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ ty o → Option (PExpr Δ Φ Γ ty o)
  | _, _, _, _, _, .lazy_mk b => b.lazyAlias?
  | _, _, _, _, _, .thunk_mk b => b.thunkAlias?
  | _, _, _, _, _, .lam _ => none
  | _, _, _, _, _, .record_mk _ => none
  | _, _, _, _, _, .union_mk _ _ => none
  | _, _, _, _, _, .array_mk _ => none
  | _, _, _, _, _, .list_mk _ => none
  | _, _, _, _, _, .data_in _ _ _ => none

/-! ## Replacing the known values in pure expressions -/

mutual
/-- Replace the known values described by `I` in a neutral expression. -/
def Neu.subA {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) :
    {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j n => .data_out b j (n.subA I)
  | _, _, .cond c a b => .cond (c.subA I) (a.subA I) (b.subA I)
  | _, _, .extern e args h => .extern e (args.subA I) h
/-- Replace the known values described by `I` in a pure expression. -/
def PExpr.subA {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu (n.subA I)
  | _, _, .kvar k => (I.get k).getD (.kvar k)
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk (args.subA I)
  | _, _, .union_mk ix args => .union_mk ix (args.subA I)
  | _, _, .array_mk es => .array_mk (es.subA I)
  | _, _, .list_mk es => .list_mk (es.subA I)
  | _, _, .data_in b j e => .data_in b j (e.subA I)
/-- Replace the known values described by `I` in arguments. -/
def Args.subA {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) :
    {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons (a.subA I) (as.subA I)
/-- Replace the known values described by `I` in the elements of a literal. -/
def Elems.subA {Φ : KCtx ks} {Γ : UCtx ks} (I : AInfo Δ Φ Γ) :
    {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons (e.subA I) (es.subA I)
end

/-! ## The walk -/

mutual
/-- `Term.deWalk` in a value. -/
def Val.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → AInfo Δ Φ Γ → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b, I => .lam (b.deWalk I)
  | _, _, _, _, _, .thunk_mk b, I => .thunk_mk (b.deWalk I)
  | _, _, _, _, _, .lazy_mk b, I => .lazy_mk (b.deWalk I)
  | _, _, _, _, _, .record_mk args, I => .record_mk (args.subA I)
  | _, _, _, _, _, .union_mk ix args, I => .union_mk ix (args.subA I)
  | _, _, _, _, _, .array_mk es, I => .array_mk (es.subA I)
  | _, _, _, _, _, .list_mk es, I => .list_mk (es.subA I)
  | _, _, _, _, _, .data_in b j e, I => .data_in b j (e.subA I)
/-- `Term.deWalk` in a body: nothing is known in a closed body. -/
def Body.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → AInfo Δ Φ Γ → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t, _ => .closed (t.deWalk AInfo.empty)
  | _, _, _, bs, _, _, .opened t h, I => .opened (t.deWalk (I.wkN bs)) h
/-- `Term.deWalk` in a computation. -/
def Comp.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → AInfo Δ Φ Γ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h, I => .app (f.subA I) (a.subA I) h
  | _, _, _, _, _, .share n, I => .share (n.subA I)
  | _, _, _, _, _, .nat_rec n z s h, I => .nat_rec (n.subA I) (z.subA I) (s.deWalk I) h
  | _, _, _, _, _, .array_foldl a z s h, I => .array_foldl (a.subA I) (z.subA I) (s.deWalk I) h
  | _, _, _, _, _, .data_rec b ρ us brs j e h, I =>
      .data_rec b ρ us (fun i => (brs i).deWalk I) j (e.subA I) h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h, I =>
      .data_brec b ρ k us (fun i => (brs i).deWalk I) j (e.subA I) h
  | _, _, _, _, _, .thunk_force e, I => .thunk_force (e.subA I)
  | _, _, _, _, _, .lazy_force e, I => .lazy_force (e.subA I)
/-- **The walk**, knowing `I` about the known values in scope; every level is kept. -/
def Term.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → AInfo Δ Φ Γ → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e, I => .ret (e.subA I)
  | _, _, _, _, _, _, .letV u v b, I =>
      let v' := v.deWalk I
      .letV u v' (b.deWalk (I.cons v'.delayAlias?))
  | _, _, _, _, _, _, .letE u c b, I => .letE u (c.deWalk I) (b.deWalk (I.wk1 _))
  | _, _, _, _, _, _, .record_casesOn us n b, I => .record_casesOn us (n.subA I) (b.deWalk (I.wkN _))
  | _, _, _, _, _, _, .branch br, I => .branch (br.deWalk I)
  | _, _, _, _, _, _, .jump j e, I => .jump j (e.subA I)
/-- `Term.deWalk` in a branch. -/
def Branch.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → AInfo Δ Φ Γ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e, I => .ite (c.subA I) (t.deWalk I) (e.deWalk I)
  | _, _, _, _, _, _, .enum_casesOn e bs, I => .enum_casesOn (e.subA I) (fun i => (bs i).deWalk I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => .union_casesOn (e.subA I) (bs.deWalk I)
  | _, _, _, _, _, _, .join σ u uₓ body main, I =>
      .join σ u uₓ (body.deWalk (I.wk1 _)) (main.deWalk I)
/-- `Term.deWalk` in the branches of a union's case analysis. -/
def Branches.deWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → AInfo Δ Φ Γ → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I =>
      .two us₁ us₂ (b₁.deWalk (I.wkN _)) (b₂.deWalk (I.wkN _))
  | _, _, _, _, _, _, _, _, .cons us b bs, I => .cons us (b.deWalk (I.wkN _)) (bs.deWalk I)
end

/-- **Delays that only force another delay, replaced by that delay.** -/
def Term.delayEta {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.deWalk AInfo.empty

end LeanScript

end
