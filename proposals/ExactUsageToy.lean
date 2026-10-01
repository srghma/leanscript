module

/-!
# Toy: exact usages by construction (companion of `proposals/ExactUsageProposals.md`)

Not part of the Lake build; check with

```
lake env lean proposals/ExactUsageToy.lean
```

A cut-down version of `LeanScript.Term` with the **three contexts** of the real language:

* `Φ`, the known values (bound by `letV` to a closure);
* `Γ`, the unknowns (closure parameters, results of calls `letE`, join-point parameters);
* `J`, the join points (bound by `join`, used by `jump`).

The grammar (`RTerm`, untyped, de Bruijn) is

```
e ::= uvar i | kvar i | lit n | e + e
t ::= ret e
    | letV (fun x => t) t       -- val k := fun x => body; t     (k : Φ, x : Γ of the body)
    | letE e e t                -- let x := f a; t               (x : Γ)
    | ifz e t t                 -- a branch: the arms take the maximum
    | join t t                  -- join j x := body; main        (x : Γ of body, j : J of main)
    | jump j e
```

`RTerm.cnt s i t` is **the truth**: the exact usage (`UsageN`, `0, 1, 2, …, ω`) of the
variable at de Bruijn position `i` of context `s` in `t` (sum along a path, maximum over the
arms of a branch, `ω` inside a closure body).  It is what `Term.dce` recounts today.

Each proposal of the document has its own typed `Term` here (namespaces `P1` … `P4`), with

* the erasure to `RTerm`, and
* the **exactness theorem**: every usage the typed term carries is `RTerm.cnt` of its erasure;
  so the usage cannot be wrong, and a term whose annotation differs from the recount does not
  exist (`… .binder_exact`, `… .unique`).
-/

@[expose] public section

set_option autoImplicit false

namespace EUToy

/-! ## Usages: `UsageN` (`0 … ω`) and `UsageNPos` (`1 … ω`) -/

/-- An exact usage: a number of uses, or `ω` (unboundedly many: inside a closure body). -/
inductive UsageN where
  | fin (n : Nat)
  | omega
  deriving DecidableEq, Repr

namespace UsageN

instance (n : Nat) : OfNat UsageN n := ⟨.fin n⟩

/-- Literals are `fin n` (the simp normal form). -/
@[simp] theorem ofNat_eq (n : Nat) : (OfNat.ofNat n : UsageN) = fin n := rfl

/-- Two parts that both run. -/
def add : UsageN → UsageN → UsageN
  | fin a, fin b => fin (a + b)
  | _, _ => omega

instance : Add UsageN := ⟨add⟩

/-- Two arms of a branch, only one of which runs. -/
def max : UsageN → UsageN → UsageN
  | fin a, fin b => fin (Nat.max a b)
  | _, _ => omega

/-- Inside a body that may run any number of times. -/
def scale : UsageN → UsageN
  | fin 0 => fin 0
  | _ => omega

@[simp] theorem fin_add_fin (a b : Nat) : fin a + fin b = fin (a + b) := rfl
@[simp] theorem omega_add (u : UsageN) : omega + u = omega := by cases u <;> rfl
@[simp] theorem add_omega (u : UsageN) : u + omega = omega := by cases u <;> rfl
@[simp] theorem zero_add (u : UsageN) : fin 0 + u = u := by cases u <;> simp
@[simp] theorem add_zero (u : UsageN) : u + fin 0 = u := by cases u <;> simp
@[simp] theorem scale_zero : scale (fin 0) = fin 0 := rfl
@[simp] theorem max_fin (a b : Nat) : max (fin a) (fin b) = fin (Nat.max a b) := rfl

theorem add_assoc (a b c : UsageN) : a + b + c = a + (b + c) := by
  cases a <;> cases b <;> cases c <;> simp [Nat.add_assoc]

theorem add_comm (a b : UsageN) : a + b = b + a := by
  cases a <;> cases b <;> simp [Nat.add_comm]

/-- `a + ω·b`. -/
def addScale (a b : UsageN) : UsageN := a + b.scale

/-- `max (c + a) (c + b) = c + max a b`: counting up along a path and then taking the
    maximum over the arms is the same as adding the maximum. -/
theorem add_max (c a b : UsageN) : max (c + a) (c + b) = c + max a b := by
  cases c <;> cases a <;> cases b <;> simp [max, Nat.add_max_add_left]

end UsageN

/-- A usage of a **definition** binder: `1 … ω`, never `0` (an unused definition is dead). -/
inductive UsageNPos where
  | succ (n : Nat)      -- `n + 1` uses
  | omega
  deriving DecidableEq, Repr

def UsageNPos.toN : UsageNPos → UsageN
  | succ n => .fin (n + 1)
  | omega => .omega

theorem UsageNPos.toN_ne_zero (u : UsageNPos) : u.toN ≠ 0 := by
  cases u <;> simp [toN, OfNat.ofNat]

/-- A non-zero `UsageN` as a `UsageNPos` (the elaborator's only way to make one). -/
def UsageN.toPos? : UsageN → Option UsageNPos
  | .fin 0 => none
  | .fin (n + 1) => some (.succ n)
  | .omega => some .omega

/-! ## Types, raw terms and the reference count -/

inductive Ty where
  | nat
  | fn (σ τ : Ty)
  deriving DecidableEq, Repr

abbrev Ty.Den : Ty → Type
  | .nat => Nat
  | .fn σ τ => σ.Den → τ.Den

def Ty.dflt : (τ : Ty) → τ.Den
  | .nat => 0
  | .fn _ τ => fun _ => τ.dflt

/-- Raw (erased) pure expressions. -/
inductive RExpr where
  | uvar (i : Nat)
  | kvar (i : Nat)
  | lit (n : Nat)
  | add (a b : RExpr)
  deriving DecidableEq, Repr

/-- Raw (erased) statements. -/
inductive RTerm where
  | ret (e : RExpr)
  | letV (body t : RTerm)
  | letE (f a : RExpr) (t : RTerm)
  | ifz (e : RExpr) (t₁ t₂ : RTerm)
  | join (body main : RTerm)
  | jump (j : Nat) (e : RExpr)
  deriving DecidableEq, Repr

/-- The three contexts. -/
inductive Kd where
  | k | u | j
  deriving DecidableEq, Repr

/-- The position of variable `i` of context `s` under one binder of context `b`. -/
def Kd.up (s b : Kd) (i : Nat) : Nat := if s = b then i + 1 else i

/-- One use exactly when the context and the position agree. -/
def hit (s s' : Kd) (i i' : Nat) : UsageN := if s = s' ∧ i = i' then 1 else 0

def RExpr.cnt (s : Kd) (i : Nat) : RExpr → UsageN
  | .uvar x => hit s .u i x
  | .kvar x => hit s .k i x
  | .lit _ => 0
  | .add a b => a.cnt s i + b.cnt s i

/-- **The reference count**: the exact usage of variable `i` of context `s`. -/
def RTerm.cnt (s : Kd) (i : Nat) : RTerm → UsageN
  | .ret e => e.cnt s i
  | .letV b t =>
      (if s = .j then 0 else (b.cnt s (Kd.up s .u i)).scale) + t.cnt s (Kd.up s .k i)
  | .letE f a t => f.cnt s i + a.cnt s i + t.cnt s (Kd.up s .u i)
  | .ifz e t₁ t₂ => e.cnt s i + UsageN.max (t₁.cnt s i) (t₂.cnt s i)
  | .join b m => b.cnt s (Kd.up s .u i) + m.cnt s (Kd.up s .j i)
  | .jump x e => hit s .j i x + e.cnt s i

/-! ## Proposal 1: quantitative contexts (QTT-style splitting) -/

namespace P1

/-- A context: types with **the exact usage** of each variable in the term typed in it. -/
abbrev Ctx := List (Ty × UsageN)

/-- The three contexts, each entry carrying its counter. -/
structure Ctxs where
  k : Ctx
  u : Ctx
  j : Ctx

def Ctx.useAt : Ctx → Nat → UsageN
  | [], _ => 0
  | (_, u) :: _, 0 => u
  | _ :: Γ, i + 1 => Ctx.useAt Γ i

def Ctxs.useAt (C : Ctxs) : Kd → Nat → UsageN
  | .k => C.k.useAt
  | .u => C.u.useAt
  | .j => C.j.useAt

/-- Every variable is used `0` times. -/
inductive Ctx.Zero : Ctx → Type
  | nil : Ctx.Zero []
  | cons {Γ : Ctx} {τ : Ty} : Ctx.Zero Γ → Ctx.Zero ((τ, 0) :: Γ)

/-- `Γ₁ + Γ₂ = Γ`, pointwise, same types (the context of two parts that both run). -/
inductive Ctx.Add : Ctx → Ctx → Ctx → Type
  | nil : Ctx.Add [] [] []
  | cons {Γ₁ Γ₂ Γ : Ctx} {τ : Ty} {u₁ u₂ : UsageN} :
      Ctx.Add Γ₁ Γ₂ Γ → Ctx.Add ((τ, u₁) :: Γ₁) ((τ, u₂) :: Γ₂) ((τ, u₁ + u₂) :: Γ)

/-- `max Γ₁ Γ₂ = Γ`, pointwise (the context of two arms of a branch). -/
inductive Ctx.Max : Ctx → Ctx → Ctx → Type
  | nil : Ctx.Max [] [] []
  | cons {Γ₁ Γ₂ Γ : Ctx} {τ : Ty} {u₁ u₂ : UsageN} :
      Ctx.Max Γ₁ Γ₂ Γ → Ctx.Max ((τ, u₁) :: Γ₁) ((τ, u₂) :: Γ₂) ((τ, UsageN.max u₁ u₂) :: Γ)

/-- `ω · Γ = Γ'` (the context of a closure body, seen from outside). -/
inductive Ctx.Scale : Ctx → Ctx → Type
  | nil : Ctx.Scale [] []
  | cons {Γ Γ' : Ctx} {τ : Ty} {u : UsageN} :
      Ctx.Scale Γ Γ' → Ctx.Scale ((τ, u) :: Γ) ((τ, u.scale) :: Γ')

/-! The relations are `Type`-valued: their witnesses are taken apart by `Term.eval` (they
carry the information of which entry goes where). -/

abbrev Ctxs.Zero (C : Ctxs) : Type := C.k.Zero × C.u.Zero × C.j.Zero
abbrev Ctxs.Add (C₁ C₂ C : Ctxs) : Type := Ctx.Add C₁.k C₂.k C.k × Ctx.Add C₁.u C₂.u C.u × Ctx.Add C₁.j C₂.j C.j
abbrev Ctxs.Max (C₁ C₂ C : Ctxs) : Type := Ctx.Max C₁.k C₂.k C.k × Ctx.Max C₁.u C₂.u C.u × Ctx.Max C₁.j C₂.j C.j
abbrev Ctxs.Scale (C C' : Ctxs) : Type := Ctx.Scale C.k C'.k × Ctx.Scale C.u C'.u × Ctx.Scale C.j C'.j

/-- A variable: its entry says `1`, every other entry says `0`.  There is no way to mention a
    variable whose counter is `0`, nor to leave a counter `1` unused. -/
inductive Var : Ctx → Ty → Type
  | head {Γ : Ctx} {τ : Ty} : Ctx.Zero Γ → Var ((τ, 1) :: Γ) τ
  | tail {Γ : Ctx} {σ τ : Ty} : Var Γ τ → Var ((σ, 0) :: Γ) τ

def Var.index {Γ : Ctx} {τ : Ty} : Var Γ τ → Nat
  | .head _ => 0
  | .tail x => x.index + 1

inductive PExpr : Ctxs → Ty → Type
  | uvar {C : Ctxs} {τ : Ty} : Ctx.Zero C.k → Var C.u τ → Ctx.Zero C.j → PExpr C τ
  | kvar {C : Ctxs} {τ : Ty} : Var C.k τ → Ctx.Zero C.u → Ctx.Zero C.j → PExpr C τ
  | lit {C : Ctxs} (n : Nat) : C.Zero → PExpr C .nat
  | add {C₁ C₂ C : Ctxs} : PExpr C₁ .nat → PExpr C₂ .nat → Ctxs.Add C₁ C₂ C → PExpr C .nat

inductive Term : Ctxs → Ty → Type
  | ret {C : Ctxs} {τ : Ty} : PExpr C τ → Term C τ
  /-- `val k [u] := fun x [ux] => body; t`.  `u` is the head counter of `t`'s known context,
      `ux` the head counter of `body`'s unknown context: both are read by the type checker,
      and `u` cannot be `0` (it is a `UsageNPos`): a dead `letV` is ill-typed. -/
  | letV {Φb Γb Jb : Ctx} {C₁ C₂ C : Ctxs} {σ₁ σ₂ τ : Ty} (u : UsageNPos) (ux : UsageN) :
      Term ⟨Φb, (σ₁, ux) :: Γb, Jb⟩ σ₂ → Ctx.Zero Jb → Ctxs.Scale ⟨Φb, Γb, Jb⟩ C₁ →
      Term ⟨(.fn σ₁ σ₂, u.toN) :: C₂.k, C₂.u, C₂.j⟩ τ → Ctxs.Add C₁ C₂ C → Term C τ
  /-- `let x [u] := f a; t`. -/
  | letE {C₁ C₂ C₁₂ C₃ C : Ctxs} {σ ρ τ : Ty} (u : UsageNPos) :
      PExpr C₁ (.fn σ ρ) → PExpr C₂ σ → Ctxs.Add C₁ C₂ C₁₂ →
      Term ⟨C₃.k, (ρ, u.toN) :: C₃.u, C₃.j⟩ τ → Ctxs.Add C₁₂ C₃ C → Term C τ
  | ifz {C₁ C₂ C₃ C₄ C : Ctxs} {τ : Ty} :
      PExpr C₁ .nat → Term C₂ τ → Term C₃ τ → Ctxs.Max C₂ C₃ C₄ → Ctxs.Add C₁ C₄ C → Term C τ
  /-- `join j [u] (x [ux]) := body; main`. -/
  | join {C₁ C₂ C : Ctxs} {σ τ : Ty} (u : UsageNPos) (ux : UsageN) :
      Term ⟨C₁.k, (σ, ux) :: C₁.u, C₁.j⟩ τ → Term ⟨C₂.k, C₂.u, (σ, u.toN) :: C₂.j⟩ τ →
      Ctxs.Add C₁ C₂ C → Term C τ
  | jump {Φ₁ Γ₁ J₁ : Ctx} {C₂ C : Ctxs} {σ τ : Ty} :
      Ctx.Zero Φ₁ → Ctx.Zero Γ₁ → Var J₁ σ → PExpr C₂ σ → Ctxs.Add ⟨Φ₁, Γ₁, J₁⟩ C₂ C → Term C τ

/-! ### Erasure -/

def PExpr.erase {C : Ctxs} {τ : Ty} : PExpr C τ → RExpr
  | .uvar _ x _ => .uvar x.index
  | .kvar x _ _ => .kvar x.index
  | .lit n _ => .lit n
  | .add a b _ => .add a.erase b.erase

def Term.erase {C : Ctxs} {τ : Ty} : Term C τ → RTerm
  | .ret e => .ret e.erase
  | .letV _ _ b _ _ t _ => .letV b.erase t.erase
  | .letE _ f a _ t _ => .letE f.erase a.erase t.erase
  | .ifz e t₁ t₂ _ _ => .ifz e.erase t₁.erase t₂.erase
  | .join _ _ b m _ => .join b.erase m.erase
  | .jump _ _ x e _ => .jump x.index e.erase

/-! ### Evaluation: the usages play no part -/

abbrev Env : Ctx → Type
  | [] => Unit
  | (τ, _) :: Γ => τ.Den × Env Γ

abbrev JEnv (ρ : Ty) : Ctx → Type
  | [] => Unit
  | (σ, _) :: J => (σ.Den → ρ.Den) × JEnv ρ J

def Var.get {Γ : Ctx} {τ : Ty} : Var Γ τ → Env Γ → τ.Den
  | .head _, (v, _) => v
  | .tail x, (_, ρ) => x.get ρ

def Var.getJ {J : Ctx} {σ ρ : Ty} : Var J σ → JEnv ρ J → σ.Den → ρ.Den
  | .head _, (k, _) => k
  | .tail x, (_, κ) => x.getJ κ

def JEnv.dflt (ρ : Ty) : (J : Ctx) → JEnv ρ J
  | [] => ()
  | (_, _) :: J => (fun _ => ρ.dflt, JEnv.dflt ρ J)

/-- Pointwise addition only splits the counters: the values are shared. -/
def Ctx.Add.left : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Add Γ₁ Γ₂ Γ → Env Γ → Env Γ₁
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.left ρ)
def Ctx.Add.right : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Add Γ₁ Γ₂ Γ → Env Γ → Env Γ₂
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.right ρ)
def Ctx.Max.left : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Max Γ₁ Γ₂ Γ → Env Γ → Env Γ₁
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.left ρ)
def Ctx.Max.right : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Max Γ₁ Γ₂ Γ → Env Γ → Env Γ₂
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.right ρ)
def Ctx.Scale.back : {Γ Γ' : Ctx} → Ctx.Scale Γ Γ' → Env Γ' → Env Γ
  | [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.back ρ)
def Ctx.Add.leftJ {ρ : Ty} : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Add Γ₁ Γ₂ Γ → JEnv ρ Γ → JEnv ρ Γ₁
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.leftJ ρ)
def Ctx.Add.rightJ {ρ : Ty} : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Add Γ₁ Γ₂ Γ → JEnv ρ Γ → JEnv ρ Γ₂
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.rightJ ρ)
def Ctx.Max.leftJ {ρ : Ty} : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Max Γ₁ Γ₂ Γ → JEnv ρ Γ → JEnv ρ Γ₁
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.leftJ ρ)
def Ctx.Max.rightJ {ρ : Ty} : {Γ₁ Γ₂ Γ : Ctx} → Ctx.Max Γ₁ Γ₂ Γ → JEnv ρ Γ → JEnv ρ Γ₂
  | [], [], [], _, _ => ()
  | (_, _) :: _, (_, _) :: _, (_, _) :: _, .cons h, (v, ρ) => (v, h.rightJ ρ)

def PExpr.eval {C : Ctxs} {τ : Ty} : PExpr C τ → Env C.k → Env C.u → τ.Den
  | .uvar _ x _, _, ρ => x.get ρ
  | .kvar x _ _, κ, _ => x.get κ
  | .lit n _, _, _ => n
  | .add a b h, κ, ρ =>
      a.eval (h.1.left κ) (h.2.1.left ρ) + b.eval (h.1.right κ) (h.2.1.right ρ)

def Term.eval {C : Ctxs} {τ : Ty} : Term C τ → Env C.k → Env C.u → JEnv τ C.j → τ.Den
  | .letV (Jb := Jb) _ _ b _ hs t h, κ, ρ, jκ =>
      let clo := fun v =>
        b.eval (hs.1.back (h.1.left κ)) (v, hs.2.1.back (h.2.1.left ρ)) (JEnv.dflt _ Jb)
      t.eval (clo, h.1.right κ) (h.2.1.right ρ) (h.2.2.rightJ jκ)
  | .ret e, κ, ρ, _ => e.eval κ ρ
  | .letE _ f a h₁ t h, κ, ρ, jκ =>
      let κ₁₂ := h.1.left κ
      let ρ₁₂ := h.2.1.left ρ
      let r := f.eval (h₁.1.left κ₁₂) (h₁.2.1.left ρ₁₂) (a.eval (h₁.1.right κ₁₂) (h₁.2.1.right ρ₁₂))
      t.eval (h.1.right κ) (r, h.2.1.right ρ) (h.2.2.rightJ jκ)
  | .ifz e t₁ t₂ hm h, κ, ρ, jκ =>
      let κ₄ := h.1.right κ
      let ρ₄ := h.2.1.right ρ
      let j₄ := h.2.2.rightJ jκ
      if e.eval (h.1.left κ) (h.2.1.left ρ) = 0 then
        t₁.eval (hm.1.left κ₄) (hm.2.1.left ρ₄) (hm.2.2.leftJ j₄)
      else
        t₂.eval (hm.1.right κ₄) (hm.2.1.right ρ₄) (hm.2.2.rightJ j₄)
  | .join _ _ b m h, κ, ρ, jκ =>
      let k := fun v => b.eval (h.1.left κ) (v, h.2.1.left ρ) (h.2.2.leftJ jκ)
      m.eval (h.1.right κ) (h.2.1.right ρ) (k, h.2.2.rightJ jκ)
  | .jump _ _ x e h, κ, ρ, jκ =>
      x.getJ (h.2.2.leftJ jκ) (e.eval (h.1.right κ) (h.2.1.right ρ))

/-! ### Exactness -/

@[simp] theorem Ctx.Zero.useAt {Γ : Ctx} (h : Ctx.Zero Γ) (i : Nat) : Γ.useAt i = 0 := by
  induction h generalizing i with
  | nil => rfl
  | cons _ ih => cases i <;> simp [Ctx.useAt, ih]

theorem Ctx.Add.useAt {Γ₁ Γ₂ Γ : Ctx} (h : Ctx.Add Γ₁ Γ₂ Γ) (i : Nat) :
    Γ.useAt i = Γ₁.useAt i + Γ₂.useAt i := by
  induction h generalizing i with
  | nil => rfl
  | cons _ ih => cases i <;> simp [Ctx.useAt, ih]

theorem Ctx.Max.useAt {Γ₁ Γ₂ Γ : Ctx} (h : Ctx.Max Γ₁ Γ₂ Γ) (i : Nat) :
    Γ.useAt i = UsageN.max (Γ₁.useAt i) (Γ₂.useAt i) := by
  induction h generalizing i with
  | nil => rfl
  | cons _ ih => cases i <;> simp [Ctx.useAt, ih]

theorem Ctx.Scale.useAt {Γ Γ' : Ctx} (h : Ctx.Scale Γ Γ') (i : Nat) :
    Γ'.useAt i = (Γ.useAt i).scale := by
  induction h generalizing i with
  | nil => rfl
  | cons _ ih => cases i <;> simp [Ctx.useAt, ih]

theorem Ctxs.Zero.useAt {C : Ctxs} (h : C.Zero) (s : Kd) (i : Nat) : C.useAt s i = 0 := by
  cases s <;> simp [Ctxs.useAt, h.1.useAt, h.2.1.useAt, h.2.2.useAt]

theorem Ctxs.Add.useAt {C₁ C₂ C : Ctxs} (h : Ctxs.Add C₁ C₂ C) (s : Kd) (i : Nat) :
    C.useAt s i = C₁.useAt s i + C₂.useAt s i := by
  cases s <;> simp [Ctxs.useAt, h.1.useAt, h.2.1.useAt, h.2.2.useAt]

theorem Ctxs.Max.useAt {C₁ C₂ C : Ctxs} (h : Ctxs.Max C₁ C₂ C) (s : Kd) (i : Nat) :
    C.useAt s i = UsageN.max (C₁.useAt s i) (C₂.useAt s i) := by
  cases s <;> simp [Ctxs.useAt, h.1.useAt, h.2.1.useAt, h.2.2.useAt]

theorem Ctxs.Scale.useAt {C C' : Ctxs} (h : Ctxs.Scale C C') (s : Kd) (i : Nat) :
    C'.useAt s i = (C.useAt s i).scale := by
  cases s <;> simp [Ctxs.useAt, h.1.useAt, h.2.1.useAt, h.2.2.useAt]

theorem Var.useAt {Γ : Ctx} {τ : Ty} (x : Var Γ τ) (i : Nat) :
    Γ.useAt i = if i = x.index then 1 else 0 := by
  induction x generalizing i with
  | head h => cases i <;> simp [Ctx.useAt, Var.index, h.useAt]
  | tail x ih => cases i <;> simp [Ctx.useAt, Var.index, ih]

theorem PExpr.exact {C : Ctxs} {τ : Ty} (e : PExpr C τ) (s : Kd) (i : Nat) :
    e.erase.cnt s i = C.useAt s i := by
  induction e with
  | uvar hΦ x hJ =>
      cases s <;> simp [PExpr.erase, RExpr.cnt, hit, Ctxs.useAt, hΦ.useAt, hJ.useAt, x.useAt]
  | kvar x hΓ hJ =>
      cases s <;> simp [PExpr.erase, RExpr.cnt, hit, Ctxs.useAt, hΓ.useAt, hJ.useAt, x.useAt]
  | lit n h => simp [PExpr.erase, RExpr.cnt, h.useAt]
  | add a b h iha ihb => simp [PExpr.erase, RExpr.cnt, iha, ihb, h.useAt]

/-- **Exactness**: the counters of the contexts are the reference counts of the erasure. -/
theorem Term.exact {C : Ctxs} {τ : Ty} (t : Term C τ) (s : Kd) (i : Nat) :
    t.erase.cnt s i = C.useAt s i := by
  induction t generalizing i with
  | ret e => exact e.exact s i
  | letV u ux b hJ hs t h ihb iht =>
      simp only [Term.erase, RTerm.cnt, iht, ihb, h.useAt, hs.useAt]
      cases s <;> simp [Kd.up, Ctxs.useAt, Ctx.useAt, hJ.useAt]
  | letE u f a h₁ t h iht =>
      simp only [Term.erase, RTerm.cnt, iht, f.exact, a.exact, h.useAt, h₁.useAt]
      cases s <;> simp [Kd.up, Ctxs.useAt, Ctx.useAt]
  | ifz e t₁ t₂ hm h ih₁ ih₂ =>
      simp [Term.erase, RTerm.cnt, ih₁, ih₂, e.exact, h.useAt, hm.useAt]
  | join u ux b m h ihb ihm =>
      simp only [Term.erase, RTerm.cnt, ihb, ihm, h.useAt]
      cases s <;> simp [Kd.up, Ctxs.useAt, Ctx.useAt]
  | jump hΦ hΓ x e h =>
      simp only [Term.erase, RTerm.cnt, e.exact, h.useAt]
      cases s <;> simp [hit, Ctxs.useAt, hΦ.useAt, hΓ.useAt, x.useAt, eq_comm]

/-- In particular, the annotation of every binder is the recount of its scope: the head
    counter of the context of the scope (the `u`/`ux` of `letV`, `letE`, `join`, …). -/
theorem Term.binder_exact {Φ Γ J : Ctx} {ρ τ : Ty} {u : UsageN} (s : Kd)
    (t : Term (match s with
      | .k => ⟨(ρ, u) :: Φ, Γ, J⟩ | .u => ⟨Φ, (ρ, u) :: Γ, J⟩ | .j => ⟨Φ, Γ, (ρ, u) :: J⟩) τ) :
    u = t.erase.cnt s 0 := by
  rw [t.exact]; cases s <;> rfl

/-- **Uniqueness**: two terms with the same erasure have the same counters: there is no
    second, wrong, annotation of the same program. -/
theorem Term.unique {C C' : Ctxs} {τ : Ty} (t : Term C τ) (t' : Term C' τ)
    (h : t.erase = t'.erase) (s : Kd) (i : Nat) : C.useAt s i = C'.useAt s i := by
  rw [← t.exact, ← t'.exact, h]

/-! ### The example of `AssocArrayAppend`

`val k1 := fun x2 => ret (x2 + (x2 + (x2 + x2))); ret k1`: `x2` is used `4` times and `k1`
once; these are the only annotations that type-check.  The contexts must be written out:
the split of the counters is an input of the typing rules (the price of proposal 1). -/

/-- `x + x` in the context `[x ↦ 2]`. -/
def twoX : PExpr ⟨[], [(.nat, 2)], []⟩ .nat :=
  .add (C₁ := ⟨[], [(.nat, 1)], []⟩) (C₂ := ⟨[], [(.nat, 1)], []⟩)
    (.uvar .nil (.head .nil) .nil) (.uvar .nil (.head .nil) .nil)
    ⟨.nil, .cons .nil, .nil⟩

def fourX : PExpr ⟨[], [(.nat, 4)], []⟩ .nat :=
  .add twoX twoX ⟨.nil, .cons .nil, .nil⟩

def assocExample : Term ⟨[], [], []⟩ (.fn .nat .nat) :=
  .letV (Φb := []) (Γb := []) (Jb := []) (C₁ := ⟨[], [], []⟩) (C₂ := ⟨[], [], []⟩)
    (.succ 0) 4 (.ret fourX) .nil ⟨.nil, .nil, .nil⟩
    (.ret (.kvar (.head .nil) .nil .nil)) ⟨.nil, .nil, .nil⟩

example : assocExample.eval () () () 5 = 20 := rfl
example : assocExample.erase =
    .letV (.ret (.add (.add (.uvar 0) (.uvar 0)) (.add (.uvar 0) (.uvar 0)))) (.ret (.kvar 0)) :=
  rfl

/-- The wrong annotation of the unoptimised snapshot, `x2 [ω]`, does not type-check:
    the body's counter for `x2` is `4`, so `ux := .omega` cannot be given. -/
example (b : Term ⟨[], [(.nat, .omega)], []⟩ .nat) : b.erase ≠ (Term.ret fourX).erase := by
  intro h
  have := Term.unique b (.ret fourX) h .u 0
  simp [Ctxs.useAt, Ctx.useAt, OfNat.ofNat] at this

end P1

/-! ## Proposal 2: input/output counters (Hodas–Miller style, `{Γ} t : τ {Δ}`) -/

namespace P2

/-- The types of the three contexts (as today: the values do not depend on the counters). -/
structure TCtx where
  k : List Ty
  u : List Ty
  j : List Ty

/-- A counter vector, parallel to a context of types: the uses **so far**, entry by entry.
    Missing entries are `0`, so `[]` is the all-zero vector of any length. -/
abbrev Cnt := List UsageN

/-- The counters of the three contexts: the *fractional environment* of the judgement. -/
structure Cnts where
  k : Cnt
  u : Cnt
  j : Cnt

def Cnt.at : Cnt → Nat → UsageN
  | [], _ => 0
  | u :: _, 0 => u
  | _ :: c, i + 1 => Cnt.at c i

/-- One more use of entry `i`. -/
def Cnt.hit : Cnt → Nat → Cnt
  | [], 0 => [1]
  | [], i + 1 => 0 :: Cnt.hit [] i
  | u :: c, 0 => (u + 1) :: c
  | u :: c, i + 1 => u :: Cnt.hit c i

/-- Pointwise, padding with `0`. -/
def Cnt.zip (f : UsageN → UsageN → UsageN) : Cnt → Cnt → Cnt
  | [], d => d.map (f 0)
  | c, [] => c.map (f · 0)
  | u :: c, v :: d => f u v :: Cnt.zip f c d

def Cnts.hit (c : Cnts) : Kd → Nat → Cnts
  | .k, i => ⟨c.k.hit i, c.u, c.j⟩
  | .u, i => ⟨c.k, c.u.hit i, c.j⟩
  | .j, i => ⟨c.k, c.u, c.j.hit i⟩

/-- The counters after one of two arms: the larger one, entry by entry. -/
def Cnts.max (c d : Cnts) : Cnts :=
  ⟨Cnt.zip UsageN.max c.k d.k, Cnt.zip UsageN.max c.u d.u, Cnt.zip UsageN.max c.j d.j⟩

/-- `c + ω·d` on the known values and the unknowns: the uses `d` of a closure body (counted
    from `0`, locally) seen from outside. -/
def Cnts.addScale (c : Cnts) (dk du : Cnt) : Cnts :=
  ⟨Cnt.zip UsageN.addScale c.k dk, Cnt.zip UsageN.addScale c.u du, c.j⟩

def Cnts.at (c : Cnts) : Kd → Nat → UsageN
  | .k => c.k.at
  | .u => c.u.at
  | .j => c.j.at

inductive Var : List Ty → Ty → Type
  | head {Γ : List Ty} {τ : Ty} : Var (τ :: Γ) τ
  | tail {Γ : List Ty} {σ τ : Ty} : Var Γ τ → Var (σ :: Γ) τ

def Var.index {Γ : List Ty} {τ : Ty} : Var Γ τ → Nat
  | .head => 0
  | .tail x => x.index + 1

/-- `{c} e : τ {c'}`: evaluating `e` with the uses `c` so far leaves the uses `c'`.  The
    output is **computed** from the input (no splitting to guess): `uvar` bumps one counter,
    `add` threads them left to right. -/
inductive PExpr (Γ : TCtx) : Cnts → Ty → Cnts → Type
  | uvar {c : Cnts} {τ : Ty} (x : Var Γ.u τ) : PExpr Γ c τ (c.hit .u x.index)
  | kvar {c : Cnts} {τ : Ty} (x : Var Γ.k τ) : PExpr Γ c τ (c.hit .k x.index)
  | lit {c : Cnts} (n : Nat) : PExpr Γ c .nat c
  | add {c₀ c₁ c₂ : Cnts} : PExpr Γ c₀ .nat c₁ → PExpr Γ c₁ .nat c₂ → PExpr Γ c₀ .nat c₂

/-- `{cᵢ} t : τ {cₒ}`.  A binder enters its scope with counter `0` and leaves it with counter
    `u`: the annotation is **the output counter of the bound variable**, read off the type. -/
inductive Term : TCtx → Cnts → Ty → Cnts → Type
  | ret {Γ : TCtx} {c₀ c₁ : Cnts} {τ : Ty} : PExpr Γ c₀ τ c₁ → Term Γ c₀ τ c₁
  /-- `val k [u] := fun x [ux] => body; t`: the body is counted locally from `0` (it sees no
      join point), and its uses are scaled to `ω` outside. -/
  | letV {Γ : TCtx} {c₀ : Cnts} {dk du dj k₃ u₃ j₃ : Cnt} {σ₁ σ₂ τ : Ty} (u : UsageNPos)
      (ux : UsageN) :
      Term ⟨Γ.k, σ₁ :: Γ.u, []⟩ ⟨[], [0], []⟩ σ₂ ⟨dk, ux :: du, dj⟩ →
      Term ⟨.fn σ₁ σ₂ :: Γ.k, Γ.u, Γ.j⟩ ⟨0 :: (c₀.addScale dk du).k, (c₀.addScale dk du).u, c₀.j⟩ τ
        ⟨u.toN :: k₃, u₃, j₃⟩ →
      Term Γ c₀ τ ⟨k₃, u₃, j₃⟩
  /-- `let x [u] := f a; t`. -/
  | letE {Γ : TCtx} {c₀ c₁ c₂ : Cnts} {k₃ u₃ j₃ : Cnt} {σ ρ τ : Ty} (u : UsageNPos) :
      PExpr Γ c₀ (.fn σ ρ) c₁ → PExpr Γ c₁ σ c₂ →
      Term ⟨Γ.k, ρ :: Γ.u, Γ.j⟩ ⟨c₂.k, 0 :: c₂.u, c₂.j⟩ τ ⟨k₃, u.toN :: u₃, j₃⟩ →
      Term Γ c₀ τ ⟨k₃, u₃, j₃⟩
  /-- The arms start from the same counters; the branch leaves the larger of their outputs. -/
  | ifz {Γ : TCtx} {c₀ c₁ c₂ c₃ : Cnts} {τ : Ty} :
      PExpr Γ c₀ .nat c₁ → Term Γ c₁ τ c₂ → Term Γ c₁ τ c₃ → Term Γ c₀ τ (c₂.max c₃)
  /-- `join j [u] (x [ux]) := body; main`: the body and the main part are on one path. -/
  | join {Γ : TCtx} {c₀ : Cnts} {k₁ u₁ j₁ k₂ u₂ j₂ : Cnt} {σ τ : Ty} (u : UsageNPos)
      (ux : UsageN) :
      Term ⟨Γ.k, σ :: Γ.u, Γ.j⟩ ⟨c₀.k, 0 :: c₀.u, c₀.j⟩ τ ⟨k₁, ux :: u₁, j₁⟩ →
      Term ⟨Γ.k, Γ.u, σ :: Γ.j⟩ ⟨k₁, u₁, 0 :: j₁⟩ τ ⟨k₂, u₂, u.toN :: j₂⟩ →
      Term Γ c₀ τ ⟨k₂, u₂, j₂⟩
  | jump {Γ : TCtx} {c₀ c₁ : Cnts} {σ τ : Ty} (x : Var Γ.j σ) :
      PExpr Γ (c₀.hit .j x.index) σ c₁ → Term Γ c₀ τ c₁

/-! ### Erasure and evaluation (no casts: the values only depend on the types) -/

def PExpr.erase {Γ : TCtx} {c c' : Cnts} {τ : Ty} : PExpr Γ c τ c' → RExpr
  | .uvar x => .uvar x.index
  | .kvar x => .kvar x.index
  | .lit n => .lit n
  | .add a b => .add a.erase b.erase

def Term.erase {Γ : TCtx} {c c' : Cnts} {τ : Ty} : Term Γ c τ c' → RTerm
  | .ret e => .ret e.erase
  | .letV _ _ b t => .letV b.erase t.erase
  | .letE _ f a t => .letE f.erase a.erase t.erase
  | .ifz e t₁ t₂ => .ifz e.erase t₁.erase t₂.erase
  | .join _ _ b m => .join b.erase m.erase
  | .jump x e => .jump x.index e.erase

abbrev Env : List Ty → Type
  | [] => Unit
  | τ :: Γ => τ.Den × Env Γ

abbrev JEnv (ρ : Ty) : List Ty → Type
  | [] => Unit
  | σ :: J => (σ.Den → ρ.Den) × JEnv ρ J

def Var.get {Γ : List Ty} {τ : Ty} : Var Γ τ → Env Γ → τ.Den
  | .head, (v, _) => v
  | .tail x, (_, ρ) => x.get ρ

def Var.getJ {J : List Ty} {σ ρ : Ty} : Var J σ → JEnv ρ J → σ.Den → ρ.Den
  | .head, (k, _) => k
  | .tail x, (_, κ) => x.getJ κ

def PExpr.eval {Γ : TCtx} {c c' : Cnts} {τ : Ty} : PExpr Γ c τ c' → Env Γ.k → Env Γ.u → τ.Den
  | .uvar x, _, ρ => x.get ρ
  | .kvar x, κ, _ => x.get κ
  | .lit n, _, _ => n
  | .add a b, κ, ρ => a.eval κ ρ + b.eval κ ρ

def Term.eval {Γ : TCtx} {c c' : Cnts} {τ : Ty} :
    Term Γ c τ c' → Env Γ.k → Env Γ.u → JEnv τ Γ.j → τ.Den
  | .ret e, κ, ρ, _ => e.eval κ ρ
  | .letV _ _ b t, κ, ρ, jκ => t.eval (fun v => b.eval κ (v, ρ) (), κ) ρ jκ
  | .letE _ f a t, κ, ρ, jκ => t.eval κ (f.eval κ ρ (a.eval κ ρ), ρ) jκ
  | .ifz e t₁ t₂, κ, ρ, jκ => if e.eval κ ρ = 0 then t₁.eval κ ρ jκ else t₂.eval κ ρ jκ
  | .join _ _ b m, κ, ρ, jκ => m.eval κ ρ (fun v => b.eval κ (v, ρ) jκ, jκ)
  | .jump x e, κ, ρ, jκ => x.getJ jκ (e.eval κ ρ)

/-! ### Exactness: output = input + reference count -/

@[simp] theorem Cnt.at_nil (i : Nat) : Cnt.at [] i = 0 := by cases i <;> rfl

theorem Cnt.at_hit (c : Cnt) (i j : Nat) :
    (c.hit i).at j = c.at j + (if j = i then 1 else 0) := by
  induction c generalizing i j with
  | nil =>
      induction i generalizing j with
      | zero => cases j <;> simp [Cnt.hit, Cnt.at]
      | succ i ih => cases j <;> simp [Cnt.hit, Cnt.at, ih]
  | cons u c ih => cases i <;> cases j <;> simp [Cnt.hit, Cnt.at, ih]

theorem Cnt.at_map (g : UsageN → UsageN) (hg : g 0 = 0) (c : Cnt) (i : Nat) :
    Cnt.at (c.map g) i = g (Cnt.at c i) := by
  induction c generalizing i with
  | nil => simpa using hg.symm
  | cons u c ih => cases i <;> simp [Cnt.at, ih]

theorem Cnt.at_zip (f : UsageN → UsageN → UsageN) (hf : f 0 0 = 0) (c d : Cnt) (i : Nat) :
    Cnt.at (Cnt.zip f c d) i = f (Cnt.at c i) (Cnt.at d i) := by
  induction c generalizing d i with
  | nil =>
      rw [show Cnt.zip f [] d = d.map (f 0) from rfl, Cnt.at_map _ hf]
      simp
  | cons u c ih =>
      cases d with
      | nil =>
          rw [show Cnt.zip f (u :: c) [] = (u :: c).map (f · 0) from rfl,
            Cnt.at_map (fun x => f x 0) hf]
          simp
      | cons v d => cases i <;> simp [Cnt.zip, Cnt.at, ih]

@[simp] theorem Cnt.at_zip_max (c d : Cnt) (i : Nat) :
    (Cnt.zip UsageN.max c d).at i = UsageN.max (c.at i) (d.at i) :=
  Cnt.at_zip _ rfl c d i

@[simp] theorem Cnt.at_zip_addScale (c d : Cnt) (i : Nat) :
    (Cnt.zip UsageN.addScale c d).at i = c.at i + (d.at i).scale :=
  Cnt.at_zip _ rfl c d i

@[simp] theorem Cnt.at_zero_single (i : Nat) : Cnt.at [0] i = 0 := by cases i <;> simp [Cnt.at]

theorem Cnts.at_hit (c : Cnts) (s s' : Kd) (i i' : Nat) :
    (c.hit s' i').at s i = c.at s i + EUToy.hit s s' i i' := by
  cases s <;> cases s' <;> simp [Cnts.hit, Cnts.at, Cnt.at_hit, EUToy.hit]

theorem Cnts.at_max (c d : Cnts) (s : Kd) (i : Nat) :
    (c.max d).at s i = UsageN.max (c.at s i) (d.at s i) := by
  cases s <;> simp [Cnts.max, Cnts.at]

theorem PExpr.exact {Γ : TCtx} {c c' : Cnts} {τ : Ty} (e : PExpr Γ c τ c') (s : Kd) (i : Nat) :
    c'.at s i = c.at s i + e.erase.cnt s i := by
  induction e with
  | uvar x => simp [PExpr.erase, RExpr.cnt, Cnts.at_hit]
  | kvar x => simp [PExpr.erase, RExpr.cnt, Cnts.at_hit]
  | lit n => simp [PExpr.erase, RExpr.cnt]
  | add a b iha ihb => simp [PExpr.erase, RExpr.cnt, iha, ihb, UsageN.add_assoc]

/-- **Exactness**: the output counters are the input counters plus the reference counts of
    the erasure.  So every annotation, read off an output counter, is the recount. -/
theorem Term.exact {Γ : TCtx} {c c' : Cnts} {τ : Ty} (t : Term Γ c τ c') (s : Kd) (i : Nat) :
    c'.at s i = c.at s i + t.erase.cnt s i := by
  induction t generalizing i with
  | ret e => exact e.exact s i
  | letV u ux b t ihb iht =>
      have hb := ihb (Kd.up s .u i)
      have ht := iht (Kd.up s .k i)
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, Cnts.at, Cnt.at, Cnts.addScale] at hb ht ⊢ <;>
        simp [ht, hb, UsageN.add_assoc]
  | letE u f a t iht =>
      have ht := iht (Kd.up s .u i)
      have hf := f.exact s i
      have ha := a.exact s i
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, Cnts.at, Cnt.at] at ht hf ha ⊢ <;>
        simp [ht, hf, ha, UsageN.add_assoc]
  | ifz e t₁ t₂ ih₁ ih₂ =>
      simp [Term.erase, RTerm.cnt, Cnts.at_max, ih₁, ih₂, e.exact, UsageN.add_max,
        UsageN.add_assoc]
  | join u ux b m ihb ihm =>
      have hb := ihb (Kd.up s .u i)
      have hm := ihm (Kd.up s .j i)
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, Cnts.at, Cnt.at] at hb hm ⊢ <;>
        simp [hb, hm, UsageN.add_assoc]
  | jump x e =>
      have he := e.exact s i
      simp [Term.erase, RTerm.cnt, he, Cnts.at_hit, UsageN.add_assoc]

/-- A closed statement starts from no uses: its output counters **are** the reference counts. -/
theorem Term.exact_closed {Γ : TCtx} {c' : Cnts} {τ : Ty} (t : Term Γ ⟨[], [], []⟩ τ c')
    (s : Kd) (i : Nat) : c'.at s i = t.erase.cnt s i := by
  rw [t.exact]; cases s <;> simp [Cnts.at]

/-! ### The example of `AssocArrayAppend`: the counters are computed by Lean

Only the input counters are written; the output counters, and so `ux = 4` and `u = 1`, are
found by unification.  Writing `ux := .omega` (the unoptimised snapshot) is a type error. -/

/-- The body `x2 + x2 + x2 + x2`, started with the counter of `x2` at `0`: Lean computes the
    output counters (`x2 ↦ 4`). -/
def body4 : (c : Cnts) × Term ⟨[], [.nat], []⟩ ⟨[], [0], []⟩ .nat c :=
  ⟨_, .ret (.add (.add (.uvar .head) (.uvar .head)) (.add (.uvar .head) (.uvar .head)))⟩

example : body4.1 = ⟨[], [4], []⟩ := rfl

/-- The scope `ret k1`, started with the counter of `k1` at `0` (`k1 ↦ 1`). -/
def retK : (c : Cnts) × Term ⟨[.fn .nat .nat], [], []⟩ ⟨[0], [], []⟩ (.fn .nat .nat) c :=
  ⟨_, .ret (.kvar .head)⟩

example : retK.1 = ⟨[1], [], []⟩ := rfl

/-- `val k1 [1] := fun x2 [4] => …; ret k1`: the only annotations that type-check. -/
def assocExample : Term ⟨[], [], []⟩ ⟨[], [], []⟩ (.fn .nat .nat) ⟨[], [], []⟩ :=
  .letV (.succ 0) (.fin 4) body4.2 retK.2

example : assocExample.eval () () () 5 = 20 := rfl

/-- The annotations of the unoptimised snapshot (`k1 [ω]`, `x2 [ω]`) are type errors. -/
example : True := by
  fail_if_success
    exact (fun (_ : Term ⟨[], [], []⟩ ⟨[], [], []⟩ (.fn .nat .nat) ⟨[], [], []⟩) => True.intro)
      (.letV (.succ 0) .omega body4.2 retK.2)
  fail_if_success
    exact (fun (_ : Term ⟨[], [], []⟩ ⟨[], [], []⟩ (.fn .nat .nat) ⟨[], [], []⟩) => True.intro)
      (.letV .omega (.fin 4) body4.2 retK.2)
  trivial

end P2

/-! ## Proposal 3: the usages as a synthesised index (like `Lvl` today) -/

namespace P3

open P2 (TCtx Cnt Cnts Var Env JEnv Var.get Var.getJ)

/-- The usage vector of one use of variable `i` of context `s`. -/
def Cnt.one : Nat → Cnt
  | 0 => [1]
  | i + 1 => 0 :: Cnt.one i

def Cnts.one : Kd → Nat → Cnts
  | .k, i => ⟨Cnt.one i, [], []⟩
  | .u, i => ⟨[], Cnt.one i, []⟩
  | .j, i => ⟨[], [], Cnt.one i⟩

/-- The head (`0` for the empty vector) and the tail: the usage of the innermost variable,
    and the usages of the others. -/
def Cnt.hd : Cnt → UsageN
  | [] => 0
  | u :: _ => u

def Cnt.tl : Cnt → Cnt
  | [] => []
  | _ :: c => c

def Cnts.add (c d : Cnts) : Cnts :=
  ⟨P2.Cnt.zip (· + ·) c.k d.k, P2.Cnt.zip (· + ·) c.u d.u, P2.Cnt.zip (· + ·) c.j d.j⟩

def Cnts.max (c d : Cnts) : Cnts :=
  ⟨P2.Cnt.zip UsageN.max c.k d.k, P2.Cnt.zip UsageN.max c.u d.u, P2.Cnt.zip UsageN.max c.j d.j⟩

/-- `ω·b + t`, the usages of `val k := fun x => b; t` outside of it. -/
def UsageN.scaleAdd (a b : UsageN) : UsageN := a.scale + b

def Cnts.letV (b t : Cnts) : Cnts :=
  ⟨P2.Cnt.zip UsageN.scaleAdd b.k (Cnt.tl t.k), P2.Cnt.zip UsageN.scaleAdd (Cnt.tl b.u) t.u, t.j⟩

/-- The usage vector of a term **is its type index**, computed by the constructors (as the level
    `Lvl` is today).  A binder stores no annotation: its usage is the head of its scope's vector
    (`Term.letV.use`), and a definition binder requires that head to be non-zero. -/
inductive PExpr : TCtx → Ty → Cnts → Type
  | uvar {Γ : TCtx} {τ : Ty} (x : Var Γ.u τ) : PExpr Γ τ (Cnts.one .u x.index)
  | kvar {Γ : TCtx} {τ : Ty} (x : Var Γ.k τ) : PExpr Γ τ (Cnts.one .k x.index)
  | lit {Γ : TCtx} (n : Nat) : PExpr Γ .nat ⟨[], [], []⟩
  | add {Γ : TCtx} {U₁ U₂ : Cnts} : PExpr Γ .nat U₁ → PExpr Γ .nat U₂ → PExpr Γ .nat (Cnts.add U₁ U₂)

inductive Term : TCtx → Ty → Cnts → Type
  | ret {Γ : TCtx} {τ : Ty} {U : Cnts} : PExpr Γ τ U → Term Γ τ U
  | letV {Γ : TCtx} {σ₁ σ₂ τ : Ty} {Ub Ut : Cnts} :
      Term ⟨Γ.k, σ₁ :: Γ.u, []⟩ σ₂ Ub → Term ⟨.fn σ₁ σ₂ :: Γ.k, Γ.u, Γ.j⟩ τ Ut →
      Cnt.hd Ut.k ≠ 0 → Term Γ τ (Cnts.letV Ub Ut)
  | letE {Γ : TCtx} {σ ρ τ : Ty} {Uf Ua Ut : Cnts} :
      PExpr Γ (.fn σ ρ) Uf → PExpr Γ σ Ua → Term ⟨Γ.k, ρ :: Γ.u, Γ.j⟩ τ Ut →
      Cnt.hd Ut.u ≠ 0 → Term Γ τ (Cnts.add (Cnts.add Uf Ua) ⟨Ut.k, Cnt.tl Ut.u, Ut.j⟩)
  | ifz {Γ : TCtx} {τ : Ty} {Ue U₁ U₂ : Cnts} :
      PExpr Γ .nat Ue → Term Γ τ U₁ → Term Γ τ U₂ → Term Γ τ (Cnts.add Ue (Cnts.max U₁ U₂))
  | join {Γ : TCtx} {σ τ : Ty} {Ub Um : Cnts} :
      Term ⟨Γ.k, σ :: Γ.u, Γ.j⟩ τ Ub → Term ⟨Γ.k, Γ.u, σ :: Γ.j⟩ τ Um →
      Cnt.hd Um.j ≠ 0 → Term Γ τ (Cnts.add ⟨Ub.k, Cnt.tl Ub.u, Ub.j⟩ ⟨Um.k, Um.u, Cnt.tl Um.j⟩)
  | jump {Γ : TCtx} {σ τ : Ty} {Ue : Cnts} (x : Var Γ.j σ) :
      PExpr Γ σ Ue → Term Γ τ (Cnts.add (Cnts.one .j x.index) Ue)

/-- The annotations, for printing: read off the indices, never stored. -/
def Term.letV.use {Ut : Cnts} (_ : Cnt.hd Ut.k ≠ 0) : UsageN := Cnt.hd Ut.k
def Term.letV.paramUse (Ub : Cnts) : UsageN := Cnt.hd Ub.u

def PExpr.erase {Γ : TCtx} {τ : Ty} {U : Cnts} : PExpr Γ τ U → RExpr
  | .uvar x => .uvar x.index
  | .kvar x => .kvar x.index
  | .lit n => .lit n
  | .add a b => .add a.erase b.erase

def Term.erase {Γ : TCtx} {τ : Ty} {U : Cnts} : Term Γ τ U → RTerm
  | .ret e => .ret e.erase
  | .letV b t _ => .letV b.erase t.erase
  | .letE f a t _ => .letE f.erase a.erase t.erase
  | .ifz e t₁ t₂ => .ifz e.erase t₁.erase t₂.erase
  | .join b m _ => .join b.erase m.erase
  | .jump x e => .jump x.index e.erase

def PExpr.eval {Γ : TCtx} {τ : Ty} {U : Cnts} : PExpr Γ τ U → Env Γ.k → Env Γ.u → τ.Den
  | .uvar x, _, ρ => x.get ρ
  | .kvar x, κ, _ => x.get κ
  | .lit n, _, _ => n
  | .add a b, κ, ρ => a.eval κ ρ + b.eval κ ρ

def Term.eval {Γ : TCtx} {τ : Ty} {U : Cnts} : Term Γ τ U → Env Γ.k → Env Γ.u → JEnv τ Γ.j → τ.Den
  | .ret e, κ, ρ, _ => e.eval κ ρ
  | .letV b t _, κ, ρ, jκ => t.eval (fun v => b.eval κ (v, ρ) (), κ) ρ jκ
  | .letE f a t _, κ, ρ, jκ => t.eval κ (f.eval κ ρ (a.eval κ ρ), ρ) jκ
  | .ifz e t₁ t₂, κ, ρ, jκ => if e.eval κ ρ = 0 then t₁.eval κ ρ jκ else t₂.eval κ ρ jκ
  | .join b m _, κ, ρ, jκ => m.eval κ ρ (fun v => b.eval κ (v, ρ) jκ, jκ)
  | .jump x e, κ, ρ, jκ => x.getJ jκ (e.eval κ ρ)

/-! ### Exactness: the index is the reference count -/

theorem Cnt.at_one (i j : Nat) : P2.Cnt.at (Cnt.one i) j = if j = i then 1 else 0 := by
  induction i generalizing j with
  | zero => cases j <;> simp [Cnt.one, P2.Cnt.at]
  | succ i ih => cases j <;> simp [Cnt.one, P2.Cnt.at, ih]

theorem Cnt.at_tl (c : Cnt) (i : Nat) : P2.Cnt.at (Cnt.tl c) i = P2.Cnt.at c (i + 1) := by
  cases c <;> simp [Cnt.tl, P2.Cnt.at]

theorem Cnt.hd_eq (c : Cnt) : Cnt.hd c = P2.Cnt.at c 0 := by
  cases c <;> rfl

@[simp] theorem Cnt.at_zip_add (c d : Cnt) (i : Nat) :
    P2.Cnt.at (P2.Cnt.zip (· + ·) c d) i = P2.Cnt.at c i + P2.Cnt.at d i :=
  P2.Cnt.at_zip _ rfl c d i

@[simp] theorem Cnt.at_zip_scaleAdd (c d : Cnt) (i : Nat) :
    P2.Cnt.at (P2.Cnt.zip UsageN.scaleAdd c d) i = (P2.Cnt.at c i).scale + P2.Cnt.at d i :=
  P2.Cnt.at_zip _ rfl c d i

theorem Cnts.at_add (c d : Cnts) (s : Kd) (i : Nat) : (Cnts.add c d).at s i = c.at s i + d.at s i := by
  cases s <;> simp [Cnts.add, P2.Cnts.at]

theorem Cnts.at_max (c d : Cnts) (s : Kd) (i : Nat) :
    (Cnts.max c d).at s i = UsageN.max (c.at s i) (d.at s i) := by
  cases s <;> simp [Cnts.max, P2.Cnts.at]

theorem Cnts.at_one (s s' : Kd) (i i' : Nat) : (Cnts.one s' i').at s i = hit s s' i i' := by
  cases s <;> cases s' <;> simp [Cnts.one, P2.Cnts.at, Cnt.at_one, hit]

theorem PExpr.exact {Γ : TCtx} {τ : Ty} {U : Cnts} (e : PExpr Γ τ U) (s : Kd) (i : Nat) :
    U.at s i = e.erase.cnt s i := by
  induction e with
  | uvar x => simp [PExpr.erase, RExpr.cnt, Cnts.at_one]
  | kvar x => simp [PExpr.erase, RExpr.cnt, Cnts.at_one]
  | lit n => cases s <;> simp [PExpr.erase, RExpr.cnt, P2.Cnts.at]
  | add a b iha ihb => simp [PExpr.erase, RExpr.cnt, Cnts.at_add, iha, ihb]

/-- **Exactness**: the index of a term is the reference count of its erasure. -/
theorem Term.exact {Γ : TCtx} {τ : Ty} {U : Cnts} (t : Term Γ τ U) (s : Kd) (i : Nat) :
    U.at s i = t.erase.cnt s i := by
  induction t generalizing i with
  | ret e => exact e.exact s i
  | letV b t _ ihb iht =>
      have hb := ihb (Kd.up s .u i)
      have ht := iht (Kd.up s .k i)
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, Cnts.letV, P2.Cnts.at, Cnt.at_tl] at hb ht ⊢ <;>
        simp [hb, ht]
  | letE f a t _ iht =>
      have ht := iht (Kd.up s .u i)
      rw [Cnts.at_add, Cnts.at_add, f.exact, a.exact]
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, P2.Cnts.at, Cnt.at_tl] at ht ⊢ <;> simp [ht]
  | ifz e t₁ t₂ ih₁ ih₂ =>
      simp [Term.erase, RTerm.cnt, Cnts.at_add, Cnts.at_max, ih₁, ih₂, e.exact]
  | join b m _ ihb ihm =>
      have hb := ihb (Kd.up s .u i)
      have hm := ihm (Kd.up s .j i)
      rw [Cnts.at_add]
      cases s <;> simp [Term.erase, RTerm.cnt, Kd.up, P2.Cnts.at, Cnt.at_tl] at hb hm ⊢ <;>
        simp [hb, hm]
  | jump x e =>
      simp [Term.erase, RTerm.cnt, Cnts.at_add, Cnts.at_one, e.exact]

/-- The annotation read off a `letV` is the recount of its scope. -/
theorem Term.letV_use_exact {Ut : Cnts} {Γ : TCtx} {τ : Ty} (t : Term Γ τ Ut) (h : Cnt.hd Ut.k ≠ 0) :
    Term.letV.use h = t.erase.cnt .k 0 := by
  rw [← t.exact]; simp [Term.letV.use, Cnt.hd_eq, P2.Cnts.at]

/-! ### The example of `AssocArrayAppend` -/

def assocExample : (U : Cnts) × Term ⟨[], [], []⟩ (.fn .nat .nat) U :=
  ⟨_, .letV (.ret (.add (.add (.uvar .head) (.uvar .head)) (.add (.uvar .head) (.uvar .head))))
    (.ret (.kvar .head)) (by decide)⟩

example : assocExample.2.eval () () () 5 = 20 := rfl

/-- The annotations are read off: `x2 ↦ 4`, `k1 ↦ 1`. -/
example : (match assocExample with
    | ⟨_, .letV (Ub := Ub) (Ut := Ut) _ _ _⟩ => (Cnt.hd Ub.u, Cnt.hd Ut.k)
    | _ => (0, 0)) = (4, 1) := rfl

end P3

/-! ## Proposal 4: annotations as a checked cache (smart constructors, no new indices) -/

namespace P4

/-- The syntax with the annotations stored at the binders, as today (`u` for definitions,
    `ux` for parameters).  The type of the terms does not change. -/
inductive ATerm where
  | ret (e : RExpr)
  | letV (u ux : UsageN) (body t : ATerm)
  | letE (u : UsageN) (f a : RExpr) (t : ATerm)
  | ifz (e : RExpr) (t₁ t₂ : ATerm)
  | join (u ux : UsageN) (body main : ATerm)
  | jump (j : Nat) (e : RExpr)
  deriving DecidableEq, Repr

def ATerm.erase : ATerm → RTerm
  | .ret e => .ret e
  | .letV _ _ b t => .letV b.erase t.erase
  | .letE _ f a t => .letE f a t.erase
  | .ifz e t₁ t₂ => .ifz e t₁.erase t₂.erase
  | .join _ _ b m => .join b.erase m.erase
  | .jump j e => .jump j e

/-- The annotation pass (`Term.dce` without the dropping): every binder gets its recount. -/
def annotate : RTerm → ATerm
  | .ret e => .ret e
  | .letV b t => .letV (t.cnt .k 0) (b.cnt .u 0) (annotate b) (annotate t)
  | .letE f a t => .letE (t.cnt .u 0) f a (annotate t)
  | .ifz e t₁ t₂ => .ifz e (annotate t₁) (annotate t₂)
  | .join b m => .join (m.cnt .j 0) (b.cnt .u 0) (annotate b) (annotate m)
  | .jump j e => .jump j e

theorem erase_annotate : (r : RTerm) → (annotate r).erase = r
  | .ret _ => rfl
  | .letV b t => by simp [annotate, ATerm.erase, erase_annotate b, erase_annotate t]
  | .letE _ _ t => by simp [annotate, ATerm.erase, erase_annotate t]
  | .ifz _ t₁ t₂ => by
      simp [annotate, ATerm.erase, erase_annotate t₁, erase_annotate t₂]
  | .join b m => by simp [annotate, ATerm.erase, erase_annotate b, erase_annotate m]
  | .jump _ _ => rfl

/-- **Exact** annotations: the term is the annotation of its own erasure. -/
def ATerm.Exact (a : ATerm) : Prop := a = annotate a.erase

instance (a : ATerm) : Decidable a.Exact := inferInstanceAs (Decidable (a = _))

/-- The terms the rest of the compiler sees: annotated, with the proof that the annotations
    are exact.  Only the smart constructors below build them. -/
abbrev ETerm := { a : ATerm // a.Exact }

def ETerm.ret (e : RExpr) : ETerm := ⟨.ret e, rfl⟩

def ETerm.letV (b t : ETerm) : ETerm :=
  ⟨.letV (t.1.erase.cnt .k 0) (b.1.erase.cnt .u 0) b.1 t.1, by
    simp only [ATerm.Exact, ATerm.erase, annotate]; rw [← b.2, ← t.2]⟩

def ETerm.letE (f a : RExpr) (t : ETerm) : ETerm :=
  ⟨.letE (t.1.erase.cnt .u 0) f a t.1, by
    simp only [ATerm.Exact, ATerm.erase, annotate]; rw [← t.2]⟩

def ETerm.ifz (e : RExpr) (t₁ t₂ : ETerm) : ETerm :=
  ⟨.ifz e t₁.1 t₂.1, by
    simp only [ATerm.Exact, ATerm.erase, annotate]; rw [← t₁.2, ← t₂.2]⟩

def ETerm.join (b m : ETerm) : ETerm :=
  ⟨.join (m.1.erase.cnt .j 0) (b.1.erase.cnt .u 0) b.1 m.1, by
    simp only [ATerm.Exact, ATerm.erase, annotate]; rw [← b.2, ← m.2]⟩

def ETerm.jump (j : Nat) (e : RExpr) : ETerm := ⟨.jump j e, rfl⟩

/-- Exactness: the stored annotation of a `letV` is the recount of its scope. -/
theorem ETerm.letV_exact (t : ETerm) (u ux : UsageN) (b : ATerm)
    (h : (ATerm.letV u ux b t.1).Exact) : u = t.1.erase.cnt .k 0 ∧ ux = b.erase.cnt .u 0 := by
  simp only [ATerm.Exact, ATerm.erase, annotate, ATerm.letV.injEq] at h
  exact ⟨h.1, h.2.1⟩

/-- Uniqueness: an exact term is determined by its erasure. -/
theorem ETerm.unique (a b : ETerm) (h : a.1.erase = b.1.erase) : a = b :=
  Subtype.ext (by rw [a.2, b.2, h])

/-- The wrong annotation of the unoptimised snapshot is not `Exact` (decided). -/
example : ¬ (ATerm.letV .omega .omega
    (.ret (.add (.add (.uvar 0) (.uvar 0)) (.add (.uvar 0) (.uvar 0)))) (.ret (.kvar 0))).Exact := by
  decide

/-- The smart constructors find `k1 ↦ 1`, `x2 ↦ 4`. -/
example : (ETerm.letV (.ret (.add (.add (.uvar 0) (.uvar 0)) (.add (.uvar 0) (.uvar 0))))
    (.ret (.kvar 0))).1 =
    .letV 1 4 (.ret (.add (.add (.uvar 0) (.uvar 0)) (.add (.uvar 0) (.uvar 0)))) (.ret (.kvar 0)) := by
  decide

end P4

end EUToy
