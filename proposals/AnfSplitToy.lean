module

/-!
# Toy: a three-layer A-normal grammar (`PExpr` / `Comp` / `Expr`) for LeanScript

Companion of `proposals/AnfSplitProposals.md`.  Not part of the Lake build; check with

```
lake env lean proposals/AnfSplitToy.lean
```

It checks, on a cut-down type grammar (`nat`, `bool`, `fn`, `array`), the Lean-level claims
of proposal 1 of the document:

1. `PExpr` (call-free, binder-free values) is an ordinary inductive, **not** mutual with the
   statements; only `Comp` and `Expr` are mutual;
2. the join-point scope needs no path conditions: without `G`/`Q` it is just the list of the
   parameter types of the join points, and a join point is a closure (so no `wk` constructor);
3. the three evaluators are total and structural (no fuel, no `partial`), including `lam`,
   the folds and `join`/`jump`;
4. programs compute by `rfl`, including a non-tail `if` written with a join point.

A pitfall met while writing it: Lean turns the context `Γ` of `PExpr` into an inductive
*parameter* (it is the same in every constructor), and then `PExpr.eval` is only structural if
`Γ` is bound before the colon.  Without `termination_by structural` Lean silently falls back
to well-founded recursion, and every `rfl` test fails.
-/

@[expose] public section

set_option autoImplicit false

namespace AnfToy

/-! ## Types, variables, environments -/

inductive Ty where
  | nat
  | bool
  | fn (a b : Ty)
  | array (t : Ty)
  deriving DecidableEq, Repr

@[reducible] def Ty.den : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .fn a b => a.den → b.den
  | .array t => Array t.den

inductive Var : List Ty → Ty → Type where
  | head {Γ : List Ty} {t : Ty} : Var (t :: Γ) t
  | tail {Γ : List Ty} {s t : Ty} : Var Γ t → Var (s :: Γ) t
  deriving DecidableEq, Repr

@[reducible] def Env : List Ty → Type
  | [] => Unit
  | t :: ts => t.den × Env ts

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.den
  | _ :: _, _, .head, e => e.1
  | _ :: _, _, .tail x, e => x.get e.2

/-! ## Layer 1: call-free values (not mutual with the statements) -/

mutual
/-- Call-free, binder-free expressions: variables, literals, cheap externs.  They may be
    duplicated or dropped freely (the language is pure). -/
inductive PExpr : List Ty → Ty → Type where
  | var {Γ : List Ty} {t : Ty} : Var Γ t → PExpr Γ t
  | nat {Γ : List Ty} : Nat → PExpr Γ .nat
  | bool {Γ : List Ty} : Bool → PExpr Γ .bool
  /-- A cheap pure extern (in LeanScript: `Term.extern` restricted to a `cheap` flag). -/
  | extern {Γ : List Ty} {σs : List Ty} {t : Ty} (name : String) (f : Env σs → t.den) :
      PExprs Γ σs → PExpr Γ t
inductive PExprs : List Ty → List Ty → Type where
  | nil {Γ : List Ty} : PExprs Γ []
  | cons {Γ : List Ty} {s : Ty} {σs : List Ty} : PExpr Γ s → PExprs Γ σs → PExprs Γ (s :: σs)
end

mutual
def PExpr.eval {Γ : List Ty} : {t : Ty} → PExpr Γ t → Env Γ → t.den
  | _, .var x, e => x.get e
  | _, .nat n, _ => n
  | _, .bool b, _ => b
  | _, .extern _ f as, e => f (as.eval e)
  termination_by structural _ p => p
def PExprs.eval {Γ : List Ty} : {σs : List Ty} → PExprs Γ σs → Env Γ → Env σs
  | _, .nil, _ => ()
  | _, .cons p ps, e => (p.eval e, ps.eval e)
  termination_by structural _ ps => ps
end

/-! ## Layers 2 and 3: computations and statements -/

/-- The join points in scope, for statements of result type `t`: the closures of their
    bodies. -/
@[reducible] def JEnv (t : Ty) : List Ty → Type
  | [] => Unit
  | s :: js => (s.den → t.den) × JEnv t js

def Var.getJ {t : Ty} : {js : List Ty} → {s : Ty} → Var js s → JEnv t js → s.den → t.den
  | _ :: _, _, .head, je => je.1
  | _ :: _, _, .tail x, je => x.getJ je.2

mutual
/-- A computation: one step whose value a `let` binds. -/
inductive Comp : List Ty → Ty → Type where
  /-- a call of a function value -/
  | app {Γ : List Ty} {a b : Ty} : PExpr Γ (.fn a b) → PExpr Γ a → Comp Γ b
  /-- a function value (a `let`-bound lambda, as `Code.fun` in Lean's LCNF) -/
  | lam {Γ : List Ty} {a b : Ty} : Expr (a :: Γ) b [] → Comp Γ (.fn a b)
  /-- a shared call-free value -/
  | share {Γ : List Ty} {t : Ty} : PExpr Γ t → Comp Γ t
  /-- `Array.foldl`: the body binds the element (index `0`) and the accumulator (index `1`) -/
  | foldl {Γ : List Ty} {s u : Ty} : PExpr Γ (.array s) → PExpr Γ u →
      Expr (s :: u :: Γ) u [] → Comp Γ u
  /-- `Nat.rec`: the body binds the answer (index `0`) and the predecessor (index `1`) -/
  | natRec {Γ : List Ty} {u : Ty} : PExpr Γ .nat → PExpr Γ u → Expr (u :: .nat :: Γ) u [] →
      Comp Γ u
/-- A statement: `let`s of computations ending in a tail. -/
inductive Expr : List Ty → Ty → List Ty → Type where
  | ret {Γ : List Ty} {t : Ty} {js : List Ty} : PExpr Γ t → Expr Γ t js
  | ite {Γ : List Ty} {t : Ty} {js : List Ty} : PExpr Γ .bool → Expr Γ t js → Expr Γ t js →
      Expr Γ t js
  | letE {Γ : List Ty} {t : Ty} {js : List Ty} {u : Ty} : Comp Γ u → Expr (u :: Γ) t js →
      Expr Γ t js
  | join {Γ : List Ty} {t : Ty} {js : List Ty} (s : Ty) : Expr (s :: Γ) t js →
      Expr Γ t (s :: js) → Expr Γ t js
  | jump {Γ : List Ty} {t : Ty} {js : List Ty} {s : Ty} : Var js s → PExpr Γ s → Expr Γ t js
end

/-- `Nat.rec` with a non-dependent motive. -/
def natIter {α : Type} (z : α) (s : Nat → α → α) : Nat → α
  | 0 => z
  | n + 1 => s n (natIter z s n)

mutual
def Comp.eval : {Γ : List Ty} → {u : Ty} → Comp Γ u → Env Γ → u.den
  | _, _, .app f a, e => f.eval e (a.eval e)
  | _, _, .lam b, e => fun v => b.eval (v, e) ()
  | _, _, .share p, e => p.eval e
  | _, _, .foldl a z b, e => (a.eval e).foldl (fun acc x => b.eval (x, acc, e) ()) (z.eval e)
  | _, _, .natRec n z b, e => natIter (z.eval e) (fun k acc => b.eval (acc, k, e) ()) (n.eval e)
  termination_by structural _ _ c => c
def Expr.eval : {Γ : List Ty} → {t : Ty} → {js : List Ty} → Expr Γ t js → Env Γ → JEnv t js →
    t.den
  | _, _, _, .ret p, e, _ => p.eval e
  | _, _, _, .ite c a b, e, je => cond (c.eval e) (a.eval e je) (b.eval e je)
  | _, _, _, .letE c k, e, je => k.eval (c.eval e, e) je
  | _, _, _, .join _ body m, e, je => m.eval e (fun v => body.eval (v, e) je, je)
  | _, _, _, .jump j p, e, je => j.getJ je (p.eval e)
  termination_by structural _ _ _ s => s
end

/-! ## Examples -/

def add {Γ : List Ty} (a b : PExpr Γ .nat) : PExpr Γ .nat :=
  .extern "Nat.add" (σs := [.nat, .nat]) (fun v => v.1 + v.2.1) (.cons a (.cons b .nil))

def v0 {Γ : List Ty} {t : Ty} : PExpr (t :: Γ) t := .var .head
def v1 {Γ : List Ty} {s t : Ty} : PExpr (s :: t :: Γ) t := .var (.tail .head)
def v2 {Γ : List Ty} {r s t : Ty} : PExpr (r :: s :: t :: Γ) t := .var (.tail (.tail .head))

/-- `fun (xs : Array Nat) => xs.foldl (· + ·) 0`: the fold is a `Comp`, bound by `let`. -/
def sumArr : Expr [.array .nat] .nat [] :=
  .letE (.foldl v0 (.nat 0) (.ret (add v1 v0))) (.ret v0)

example : sumArr.eval (#[1, 2, 3, 4], ()) () = 10 := rfl

/-- A non-tail `if` with a call in it, `(if c then f 1 else 2) + 10`, captured with a join
    point for the rest of the computation:
    `join j (v) := ret (v + 10) in if c then (let r := f 1; jump j r) else jump j 2`. -/
def nonTailIf : Expr [.bool, .fn .nat .nat] .nat [] :=
  .join .nat (.ret (add v0 (.nat 10)))
    (.ite v0
      (.letE (.app v1 (.nat 1)) (.jump .head v0))
      (.jump .head (.nat 2)))

example : nonTailIf.eval (true, (· * 7), ()) () = 17 := rfl
example : nonTailIf.eval (false, (· * 7), ()) () = 12 := rfl

/-- A `let`-bound lambda used twice: `let g := fun x => x + x; let a := g 3; g a`. -/
def lamTwice : Expr [] .nat [] :=
  .letE (.lam (.ret (add v0 v0)))
    (.letE (.app v0 (.nat 3))
      (.letE (.app v1 v0) (.ret v0)))

example : lamTwice.eval () () = 12 := rfl

end AnfToy

end
