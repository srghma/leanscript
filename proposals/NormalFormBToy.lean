module

/-!
# Toy: proposal B, two contexts (companion of `proposals/NormalFormProposals.md`, §B)

Not part of the Lake build; check with

```
lake env lean proposals/NormalFormBToy.lean
```

A cut-down version of proposal B of the document, over the same small language as
`proposals/NormalFormToy.lean` (types `nat`, `bool`, `fn`; the externs `add` and `lt`; `let`,
`if`, application and `Nat.rec`).  A statement has **two** contexts:

* `Φ`, the **known** values: bound by `letV` to a closure (`Val.lam`).  A known value is used
  by name (`PExpr.kvar`) as an operand, but it is never neutral, so it is never called or taken
  apart: `Comp.app` needs a `Neu` function;
* `Γ`, the **unknowns**: parameters of closures, binders of loops, and results of
  computations (`letE`), every one of which eliminates a neutral expression.

In this toy only closures are shared (the only non-first-order values of the toy), so `letV`
is restricted to function types.  It checks:

1. there is no neutral expression and no computation without an unknown, whatever the known
   values are (`Neu.not_closed`, `Comp.not_closed`: `Γ = []`, any `Φ`);
2. a closed statement is a chain of `letV`s ending in `ret v` (`Term.closed_chain`);
3. at a first-order type the answer at the end of that chain is the quotation of the value
   of the whole statement (`Term.closed_endsWith_quote`), whatever values the known context
   holds: no `kvar` can occur in it, because every known value is a closure.  So two closed
   statements with the same value end in the same literal (`Term.closed_endsWith_of_run_eq`);
   the chains of `letV`s in front of it may still differ (dead `letV`s, see the document);
4. the old counterexample `ret (3 + 4)` is ill-typed (`addT_rejected`), and so is the call of
   a known closure (`knownCall_rejected`), while sharing a closure by name is allowed
   (`shareTwice`).
-/

@[expose] public section

set_option autoImplicit false

namespace NFBToy

inductive Ty where
  | nat | bool | fn (a b : Ty)
  deriving DecidableEq

abbrev Ty.Den : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .fn a b => a.Den → b.Den

abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | head {Γ : Ctx} {τ : Ty} : Var (τ :: Γ) τ
  | tail {Γ : Ctx} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

abbrev Env : Ctx → Type
  | [] => Unit
  | τ :: Γ => τ.Den × Env Γ

def Var.get : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Env Γ → τ.Den
  | _ :: _, _, .head, ρ => ρ.1
  | _ :: _, _, .tail x, ρ => x.get ρ.2

inductive Extern : List Ty → Ty → Type where
  | add : Extern [.nat, .nat] .nat
  | lt : Extern [.nat, .nat] .bool

abbrev DenList : List Ty → Type
  | [] => Unit
  | τ :: σs => τ.Den × DenList σs

def Extern.eval : {σs : List Ty} → {τ : Ty} → Extern σs τ → DenList σs → τ.Den
  | _, _, .add, (a, b, ()) => a + b
  | _, _, .lt, (a, b, ()) => decide (a < b)

mutual
/-- Neutral: stuck on an *unknown* (a variable of `Γ`, never of `Φ`). -/
inductive Neu : Ctx → Ctx → Ty → Type where
  | var {Φ Γ : Ctx} {τ : Ty} : Var Γ τ → Neu Φ Γ τ
  /-- An extern call with at least one neutral argument. -/
  | extern {Φ Γ : Ctx} {σs : List Ty} {τ : Ty} : Extern σs τ → StuckArgs Φ Γ σs → Neu Φ Γ τ

/-- Arguments of which at least one is neutral (the first neutral one is `here`). -/
inductive StuckArgs : Ctx → Ctx → List Ty → Type where
  | here {Φ Γ : Ctx} {σ : Ty} {σs : List Ty} : Neu Φ Γ σ → Args Φ Γ σs → StuckArgs Φ Γ (σ :: σs)
  | there {Φ Γ : Ctx} {σ : Ty} {σs : List Ty} :
      PExpr Φ Γ σ → StuckArgs Φ Γ σs → StuckArgs Φ Γ (σ :: σs)

inductive Args : Ctx → Ctx → List Ty → Type where
  | nil {Φ Γ : Ctx} : Args Φ Γ []
  | cons {Φ Γ : Ctx} {σ : Ty} {σs : List Ty} : PExpr Φ Γ σ → Args Φ Γ σs → Args Φ Γ (σ :: σs)

/-- Pure expressions: a neutral one, a known value by name, or a literal.  Closures are not
    pure expressions: they are `Val`s, bound by `letV`. -/
inductive PExpr : Ctx → Ctx → Ty → Type where
  | neu {Φ Γ : Ctx} {τ : Ty} : Neu Φ Γ τ → PExpr Φ Γ τ
  | kvar {Φ Γ : Ctx} {τ : Ty} : Var Φ τ → PExpr Φ Γ τ
  | natLit {Φ Γ : Ctx} : Nat → PExpr Φ Γ .nat
  | boolLit {Φ Γ : Ctx} : Bool → PExpr Φ Γ .bool

/-- Values worth sharing: closures.  The body sees the known values and the unknowns, plus
    its parameter (an unknown). -/
inductive Val : Ctx → Ctx → Ty → Type where
  | lam {Φ Γ : Ctx} {σ τ : Ty} : Term Φ (σ :: Γ) τ → Val Φ Γ (.fn σ τ)

/-- Computations: every one eliminates a neutral expression. -/
inductive Comp : Ctx → Ctx → Ty → Type where
  | app {Φ Γ : Ctx} {σ τ : Ty} : Neu Φ Γ (.fn σ τ) → PExpr Φ Γ σ → Comp Φ Γ τ
  | share {Φ Γ : Ctx} {τ : Ty} : Neu Φ Γ τ → Comp Φ Γ τ
  | nat_rec {Φ Γ : Ctx} {τ : Ty} :
      Neu Φ Γ .nat → PExpr Φ Γ τ → Term Φ (τ :: .nat :: Γ) τ → Comp Φ Γ τ

inductive Term : Ctx → Ctx → Ty → Type where
  | ret {Φ Γ : Ctx} {τ : Ty} : PExpr Φ Γ τ → Term Φ Γ τ
  /-- Share a known value (a closure) by name. -/
  | letV {Φ Γ : Ctx} {σ τ ρ : Ty} : Val Φ Γ (.fn σ τ) → Term (.fn σ τ :: Φ) Γ ρ → Term Φ Γ ρ
  /-- Bind an unknown: the result of a computation. -/
  | letE {Φ Γ : Ctx} {σ τ : Ty} : Comp Φ Γ σ → Term Φ (σ :: Γ) τ → Term Φ Γ τ
  | ite {Φ Γ : Ctx} {τ : Ty} : Neu Φ Γ .bool → Term Φ Γ τ → Term Φ Γ τ → Term Φ Γ τ
end

mutual
def Neu.eval {Φ Γ : Ctx} {τ : Ty} (κ : Env Φ) (ρ : Env Γ) : Neu Φ Γ τ → τ.Den
  | .var x => x.get ρ
  | .extern e as => e.eval (as.eval κ ρ)
def StuckArgs.eval {Φ Γ : Ctx} {σs : List Ty} (κ : Env Φ) (ρ : Env Γ) :
    StuckArgs Φ Γ σs → DenList σs
  | .here n as => (n.eval κ ρ, as.eval κ ρ)
  | .there p as => (p.eval κ ρ, as.eval κ ρ)
def Args.eval {Φ Γ : Ctx} {σs : List Ty} (κ : Env Φ) (ρ : Env Γ) : Args Φ Γ σs → DenList σs
  | .nil => ()
  | .cons p as => (p.eval κ ρ, as.eval κ ρ)
def PExpr.eval {Φ Γ : Ctx} {τ : Ty} (κ : Env Φ) (ρ : Env Γ) : PExpr Φ Γ τ → τ.Den
  | .neu n => n.eval κ ρ
  | .kvar x => x.get κ
  | .natLit n => n
  | .boolLit b => b
def Val.eval {Φ Γ : Ctx} {τ : Ty} (κ : Env Φ) (ρ : Env Γ) : Val Φ Γ τ → τ.Den
  | .lam body => fun x => body.eval κ (x, ρ)
def Comp.eval {Φ Γ : Ctx} {τ : Ty} (κ : Env Φ) (ρ : Env Γ) : Comp Φ Γ τ → τ.Den
  | .app f a => f.eval κ ρ (a.eval κ ρ)
  | .share n => n.eval κ ρ
  | .nat_rec n z s =>
      Nat.rec (motive := fun _ => _) (z.eval κ ρ) (fun k acc => s.eval κ (acc, k, ρ)) (n.eval κ ρ)
def Term.eval {Φ Γ : Ctx} {τ : Ty} (κ : Env Φ) (ρ : Env Γ) : Term Φ Γ τ → τ.Den
  | .ret p => p.eval κ ρ
  | .letV v b => b.eval (v.eval κ ρ, κ) ρ
  | .letE c b => b.eval κ (c.eval κ ρ, ρ)
  | .ite c t e => if c.eval κ ρ then t.eval κ ρ else e.eval κ ρ
end

/-- The value of a statement with no unknown and no known value. -/
def Term.run {τ : Ty} (t : Term [] [] τ) : τ.Den := t.eval () ()

/-! ## 1. Nothing neutral is closed, whatever is known -/

mutual
theorem Neu.not_closed {Φ : Ctx} {τ : Ty} : Neu Φ [] τ → False
  | .var x => nomatch x
  | .extern _ as => as.not_closed
theorem StuckArgs.not_closed {Φ : Ctx} {σs : List Ty} : StuckArgs Φ [] σs → False
  | .here n _ => n.not_closed
  | .there _ as => as.not_closed
end

theorem Comp.not_closed {Φ : Ctx} {τ : Ty} : Comp Φ [] τ → False
  | .app f _ => f.not_closed
  | .share n => n.not_closed
  | .nat_rec n _ _ => n.not_closed

/-! ## 2. A closed statement is a chain of `letV`s ending in `ret` -/

/-- A chain of shared values ending in an answer. -/
inductive Term.IsChain : {Φ : Ctx} → {τ : Ty} → Term Φ [] τ → Prop where
  | ret {Φ : Ctx} {τ : Ty} (v : PExpr Φ [] τ) : Term.IsChain (.ret v)
  | letV {Φ : Ctx} {σ τ ρ : Ty} (v : Val Φ [] (.fn σ τ)) (b : Term (.fn σ τ :: Φ) [] ρ) :
      Term.IsChain b → Term.IsChain (.letV v b)

/-- **T1 for proposal B.** -/
theorem Term.closed_chain {Φ : Ctx} {τ : Ty} : (t : Term Φ [] τ) → t.IsChain
  | .ret v => .ret v
  | .letV v b => .letV v b b.closed_chain
  | .letE c _ => c.not_closed.elim
  | .ite c _ _ => c.not_closed.elim

/-! ## 3. At a first-order type, the answer is the quotation of the value -/

/-- First-order types: their values are finite trees of literals. -/
inductive Ty.FO : Ty → Prop where
  | nat : Ty.FO .nat
  | bool : Ty.FO .bool

/-- Read a value back as a pure expression (in any contexts). -/
def PExpr.quote {Φ Γ : Ctx} : (τ : Ty) → τ.FO → τ.Den → PExpr Φ Γ τ
  | .nat, _, n => .natLit n
  | .bool, _, b => .boolLit b

/-- Every known value is a closure. -/
def Ctx.AllFn (Φ : Ctx) : Prop := ∀ τ ∈ Φ, ∃ a b, τ = .fn a b

theorem Var.mem {Φ : Ctx} {τ : Ty} : Var Φ τ → τ ∈ Φ
  | .head => List.mem_cons_self
  | .tail x => List.mem_cons_of_mem _ x.mem

/-- No known value of a first-order type: a `kvar` never has one. -/
theorem Var.not_fo {Φ : Ctx} {τ : Ty} (hΦ : Φ.AllFn) (h : τ.FO) (x : Var Φ τ) : False := by
  obtain ⟨a, b, rfl⟩ := hΦ τ x.mem
  nomatch h

theorem PExpr.closed_eq_quote {Φ : Ctx} {τ : Ty} (hΦ : Φ.AllFn) (h : τ.FO) (κ : Env Φ)
    (v : PExpr Φ [] τ) : v = PExpr.quote τ h (v.eval κ ()) := by
  cases v with
  | neu n => exact n.not_closed.elim
  | kvar x => exact (x.not_fo hΦ h).elim
  | natLit _ => rfl
  | boolLit _ => rfl

/-- `t` is a chain of `letV`s ending in `ret a`, where `a` is a pure expression that makes
    sense in every known context (a literal, say). -/
inductive Term.EndsWith {τ : Ty} (a : (Φ' : Ctx) → PExpr Φ' [] τ) : {Φ : Ctx} → Term Φ [] τ → Prop where
  | ret {Φ : Ctx} : Term.EndsWith a (.ret (a Φ))
  | letV {Φ : Ctx} {σ τ' : Ty} (v : Val Φ [] (.fn σ τ')) (b : Term (.fn σ τ' :: Φ) [] τ) :
      Term.EndsWith a b → Term.EndsWith a (.letV v b)

theorem Ctx.AllFn.cons {Φ : Ctx} {σ τ : Ty} (hΦ : Φ.AllFn) : Ctx.AllFn (.fn σ τ :: Φ) := by
  intro τ' hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact ⟨σ, τ, rfl⟩
  · exact hΦ τ' hm

/-- **T2 for proposal B**: at a first-order type, a closed statement whose known values are
    closures is a chain of `letV`s ending in `ret` of the quotation of its own value. -/
theorem Term.closed_endsWith_quote {τ : Ty} (h : τ.FO) :
    {Φ : Ctx} → Φ.AllFn → (t : Term Φ [] τ) → (κ : Env Φ) →
      t.EndsWith (fun _ => PExpr.quote τ h (t.eval κ ()))
  | _, hΦ, .ret v, κ => by
      have e := PExpr.closed_eq_quote hΦ h κ v
      show Term.EndsWith (fun _ => PExpr.quote τ h (v.eval κ ())) (.ret v)
      generalize v.eval κ () = x at e ⊢
      subst e
      exact .ret
  | _, hΦ, .letV v b, κ => by
      show Term.EndsWith (fun _ => PExpr.quote τ h (b.eval (v.eval κ (), κ) ())) (.letV v b)
      exact .letV v b (Term.closed_endsWith_quote h hΦ.cons b (v.eval κ (), κ))
  | _, _, .letE c _, _ => c.not_closed.elim
  | _, _, .ite c _ _, _ => c.not_closed.elim

/-- So two closed statements of a first-order type with the same value end in the same
    literal.  The chains of shared values before it may differ (see the document on dead
    `letV`s). -/
theorem Term.closed_endsWith_of_run_eq {τ : Ty} (h : τ.FO) (t u : Term [] [] τ)
    (e : t.run = u.run) : t.EndsWith (fun _ => PExpr.quote τ h u.run) := by
  rw [← e]
  exact t.closed_endsWith_quote h (fun _ hm => by cases hm) ()

/-! ## 4. What is ill-typed and what is allowed -/

/-- `ret (3 + 4)` needs a neutral argument for `add`, and a literal is not neutral. -/
theorem addT_rejected {Φ : Ctx} (as : StuckArgs Φ [] [.nat, .nat]) : False := as.not_closed

/-- A known closure cannot be called: the function of `app` is neutral, and a `Neu` never
    mentions `Φ` except inside `StuckArgs` arguments, so with no unknown there is no `Neu`
    at all, and a known closure can only be β-reduced by the normaliser. -/
theorem knownCall_rejected {Φ : Ctx} {σ τ : Ty} (f : Neu (.fn σ τ :: Φ) [] (.fn σ τ)) : False :=
  f.not_closed

/-- `fun n => let f := fun x => x + n; g f + g f` with `g` the first parameter:
    the closure `f` is shared by name (`letV`), passed twice to the unknown `g`. -/
def shareTwice : Term [] [] (.fn (.fn (.fn .nat .nat) .nat) (.fn .nat .nat)) :=
  -- fun g => fun n => letV f := (fun x => x + n); let a := g f; let b := g f; a + b
  .letV (.lam
      (.letV (.lam
          (.letV (.lam (.ret (.neu (.extern .add (.here (.var .head)
              (.cons (.neu (.var (.tail .head))) .nil))))))
            (.letE (.app (.var (.tail .head)) (.kvar .head))
              (.letE (.app (.var (.tail (.tail .head))) (.kvar .head))
                (.ret (.neu (.extern .add (.here (.var (.tail .head))
                  (.cons (.neu (.var .head)) .nil)))))))))
        (.ret (.kvar .head))))
    (.ret (.kvar .head))

example : shareTwice.run (fun f => f 1) 10 = 22 := rfl

end NFBToy

end
