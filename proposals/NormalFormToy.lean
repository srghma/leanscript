module

/-!
# Toy: normal forms by construction (companion of `proposals/NormalFormProposals.md`)

Not part of the Lake build; check with

```
lake env lean proposals/NormalFormToy.lean
```

A cut-down version of proposal A of the document (types `nat`, `bool`, `fn`; the externs
`add` and `lt`; `let`, `if`, application and `Nat.rec`).  It checks the Lean-level claims:

1. with the *stuck* discipline (a neutral expression always contains a variable; an extern
   needs at least one neutral argument; every elimination takes a neutral expression;
   closures are pure expressions, so every variable in scope is an unknown), there is **no
   closed neutral expression** and **no closed computation** (`Neu.not_closed`,
   `Comp.not_closed`);
2. hence a closed statement is `ret v` (`Term.closed_ret`), and at a first-order type it is
   the quotation of its own value (`Term.closed_eq_quote`), so evaluation of closed terms is
   injective (`Term.closed_run_injective`);
3. the old counterexample `ret (3 + 4)` is ill-typed (`addT_rejected`).
-/

@[expose] public section

set_option autoImplicit false

namespace NFToy

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
/-- Neutral: stuck on a variable. -/
inductive Neu : Ctx → Ty → Type where
  | var {Γ : Ctx} {τ : Ty} : Var Γ τ → Neu Γ τ
  /-- An extern call with at least one neutral argument. -/
  | extern {Γ : Ctx} {σs : List Ty} {τ : Ty} : Extern σs τ → StuckArgs Γ σs → Neu Γ τ

/-- Arguments of which at least one is neutral (the first neutral one is `here`). -/
inductive StuckArgs : Ctx → List Ty → Type where
  | here {Γ : Ctx} {σ : Ty} {σs : List Ty} : Neu Γ σ → Args Γ σs → StuckArgs Γ (σ :: σs)
  | there {Γ : Ctx} {σ : Ty} {σs : List Ty} : PExpr Γ σ → StuckArgs Γ σs → StuckArgs Γ (σ :: σs)

inductive Args : Ctx → List Ty → Type where
  | nil {Γ : Ctx} : Args Γ []
  | cons {Γ : Ctx} {σ : Ty} {σs : List Ty} : PExpr Γ σ → Args Γ σs → Args Γ (σ :: σs)

/-- Pure expressions: a neutral one or an introduction form (closures included). -/
inductive PExpr : Ctx → Ty → Type where
  | neu {Γ : Ctx} {τ : Ty} : Neu Γ τ → PExpr Γ τ
  | natLit {Γ : Ctx} : Nat → PExpr Γ .nat
  | boolLit {Γ : Ctx} : Bool → PExpr Γ .bool
  | lam {Γ : Ctx} {σ τ : Ty} : Term (σ :: Γ) τ → PExpr Γ (.fn σ τ)

/-- Computations: every one eliminates a neutral expression. -/
inductive Comp : Ctx → Ty → Type where
  | app {Γ : Ctx} {σ τ : Ty} : Neu Γ (.fn σ τ) → PExpr Γ σ → Comp Γ τ
  | share {Γ : Ctx} {τ : Ty} : Neu Γ τ → Comp Γ τ
  | nat_rec {Γ : Ctx} {τ : Ty} : Neu Γ .nat → PExpr Γ τ → Term (τ :: .nat :: Γ) τ → Comp Γ τ

inductive Term : Ctx → Ty → Type where
  | ret {Γ : Ctx} {τ : Ty} : PExpr Γ τ → Term Γ τ
  | letE {Γ : Ctx} {σ τ : Ty} : Comp Γ σ → Term (σ :: Γ) τ → Term Γ τ
  | ite {Γ : Ctx} {τ : Ty} : Neu Γ .bool → Term Γ τ → Term Γ τ → Term Γ τ
end

mutual
def Neu.eval {Γ : Ctx} {τ : Ty} (ρ : Env Γ) : Neu Γ τ → τ.Den
  | .var x => x.get ρ
  | .extern e as => e.eval (as.eval ρ)
def StuckArgs.eval {Γ : Ctx} {σs : List Ty} (ρ : Env Γ) : StuckArgs Γ σs → DenList σs
  | .here n as => (n.eval ρ, as.eval ρ)
  | .there p as => (p.eval ρ, as.eval ρ)
def Args.eval {Γ : Ctx} {σs : List Ty} (ρ : Env Γ) : Args Γ σs → DenList σs
  | .nil => ()
  | .cons p as => (p.eval ρ, as.eval ρ)
def PExpr.eval {Γ : Ctx} {τ : Ty} (ρ : Env Γ) : PExpr Γ τ → τ.Den
  | .neu n => n.eval ρ
  | .natLit n => n
  | .boolLit b => b
  | .lam body => fun x => body.eval (x, ρ)
def Comp.eval {Γ : Ctx} {τ : Ty} (ρ : Env Γ) : Comp Γ τ → τ.Den
  | .app f a => f.eval ρ (a.eval ρ)
  | .share n => n.eval ρ
  | .nat_rec n z s =>
      Nat.rec (motive := fun _ => _) (z.eval ρ) (fun k acc => s.eval (acc, k, ρ)) (n.eval ρ)
def Term.eval {Γ : Ctx} {τ : Ty} (ρ : Env Γ) : Term Γ τ → τ.Den
  | .ret p => p.eval ρ
  | .letE c b => b.eval (c.eval ρ, ρ)
  | .ite c t e => if c.eval ρ then t.eval ρ else e.eval ρ
end

/-- The value of a closed statement. -/
def Term.run {τ : Ty} (t : Term [] τ) : τ.Den := t.eval ()

/-! ## 1. Nothing neutral is closed -/

mutual
theorem Neu.not_closed {τ : Ty} : Neu [] τ → False
  | .var x => nomatch x
  | .extern _ as => as.not_closed
theorem StuckArgs.not_closed {σs : List Ty} : StuckArgs [] σs → False
  | .here n _ => n.not_closed
  | .there _ as => as.not_closed
end

theorem Comp.not_closed {τ : Ty} : Comp [] τ → False
  | .app f _ => f.not_closed
  | .share n => n.not_closed
  | .nat_rec n _ _ => n.not_closed

/-! ## 2. A closed statement is a value -/

theorem Term.closed_ret {τ : Ty} : (t : Term [] τ) → ∃ v, t = .ret v
  | .ret v => ⟨v, rfl⟩
  | .letE c _ => c.not_closed.elim
  | .ite c _ _ => c.not_closed.elim

/-- First-order types: their values are finite trees of literals. -/
inductive Ty.FO : Ty → Prop where
  | nat : Ty.FO .nat
  | bool : Ty.FO .bool

/-- Read a value back as a closed pure expression. -/
def PExpr.quote : (τ : Ty) → τ.FO → τ.Den → PExpr [] τ
  | .nat, _, n => .natLit n
  | .bool, _, b => .boolLit b

theorem PExpr.closed_eq_quote {τ : Ty} (h : τ.FO) (v : PExpr [] τ) :
    v = PExpr.quote τ h (v.eval ()) := by
  cases v with
  | neu n => exact n.not_closed.elim
  | natLit _ => rfl
  | boolLit _ => rfl
  | lam _ => nomatch h

/-- **The closed-term theorem**: at a first-order type a closed statement is `ret` of the
    quotation of its own value. -/
theorem Term.closed_eq_quote {τ : Ty} (h : τ.FO) (t : Term [] τ) :
    t = .ret (PExpr.quote τ h t.run) := by
  obtain ⟨v, rfl⟩ := t.closed_ret
  exact congrArg Term.ret (PExpr.closed_eq_quote h v)

theorem Term.closed_run_injective {τ : Ty} (h : τ.FO) (t u : Term [] τ) (e : t.run = u.run) :
    t = u := by
  rw [t.closed_eq_quote h, u.closed_eq_quote h, e]

/-! ## 3. The old counterexample no longer typechecks -/

/-- `ret (3 + 4)` needs a neutral argument for `add`, and a literal is not neutral. -/
theorem addT_rejected (as : StuckArgs [] [.nat, .nat]) : False := as.not_closed

/-- An open term may still call `add` (on a variable), and it computes. -/
def incr : Term [.nat] .nat :=
  .ret (.neu (.extern .add (.here (.var .head) (.cons (.natLit 1) .nil))))

example : incr.eval (41, ()) = 42 := rfl

/-- A closure is a value: `fun x => x + 1` is closed and `ret`-shaped. -/
def incrFn : Term [] (.fn .nat .nat) := .ret (.lam incr)

example : incrFn.run 1 = 2 := rfl

end NFToy

end
