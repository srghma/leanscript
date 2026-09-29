module

public import LeanScript.Term.Rename.Eval
public import LeanScript.Term.Optimize.Count

@[expose] public section

set_option autoImplicit false

/-!
# Inlining known closures that compute an expression

A known closure whose body is closed and only computes a pure expression of its parameter,

```
val k := fun x => (closed) ret e[x]
…
let y := k a            -- `a` open, so the normal form keeps the call
```

is inlined at its calls: `let y := k a` becomes `let y := share e[a]` when `e[a]` is a neutral
expression of the level of the call (`Term.inlineKnown`).  Dead-code elimination then drops
`k` when nothing else refers to it.  This is the Term-level counterpart of the first case of
the former module-level `inlineConsts` of the JavaScript backend ("the closures of the module
that only compute an expression are inlined where they are called").

The walk carries, for each known variable in scope, what is known about its value
(`KInfo`): the expression its closure computes, as an expression of the *current* known
context (`ExprFn`).  Going under a `val` weakens the information (`KInfo.cons`), entering a
closed body keeps only what can be seen from it (`KInfo.toClosed`).

**Proved:** `Term.inlineKnown_eval` (the value does not change) and
`Term.numCalls_inlineKnown` (no call is added).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Known closures computing an expression -/

/-- A closure of type `ty = σ → τ` that computes the pure expression `body` of its parameter,
    in the known context `Φ`. -/
structure ExprFn (Δ : DSig ks) (Φ : KCtx ks) (ty : Ty ks) where
  σ : Ty ks
  τ : Ty ks
  hty : ty = .fn σ τ
  u : Usage01ω
  lv : Nat
  o : Lvl
  body : PExpr Δ Φ [⟨σ, u, lv⟩] τ o

/-- `f` describes the value `x` in the known environment `κ`. -/
def ExprFn.Sem {Φ : KCtx ks} {ty : Ty ks} (f : ExprFn Δ Φ ty) (κ : KEnv Δ Φ)
    (x : Ty.Den Δ ty) : Prop :=
  ∀ v : Ty.Den Δ f.σ, (cast (congrArg (Ty.Den Δ) f.hty) x : Ty.Den Δ (.fn f.σ f.τ)) v =
    f.body.eval κ (Tuple.cons v Tuple.nil)

/-- Move the description along a renaming of the known values. -/
def ExprFn.rename {Φ Φ' : KCtx ks} (rk : KRen Φ Φ') {ty : Ty ks} (f : ExprFn Δ Φ ty) :
    Option (ExprFn Δ Φ' ty) :=
  (f.body.rename rk URen.id).map fun b => ⟨f.σ, f.τ, f.hty, f.u, f.lv, f.o, b⟩

/-- What is known about the known values in scope. -/
structure KInfo (Δ : DSig ks) (Φ : KCtx ks) : Type where
  /-- The description of a known variable's value, if any. -/
  get : ∀ {ty : Ty ks} {o : Lvl}, KVar Φ ty o → Option (ExprFn Δ Φ ty)

/-- Nothing is known. -/
def KInfo.empty {Φ : KCtx ks} : KInfo Δ Φ := ⟨fun _ => none⟩

/-- One more known binder: weakening. -/
def KRen.wk1 {Φ : KCtx ks} {b : KBinder ks} : KRen Φ (b :: Φ) := fun x => some (.tail x)

/-- The lookup under one more known binder. -/
def KInfo.consGet {Φ : KCtx ks} (I : KInfo Δ Φ) :
    {b : KBinder ks} → Option (ExprFn Δ Φ b.ty) → {ty : Ty ks} → {o : Lvl} →
    KVar (b :: Φ) ty o → Option (ExprFn Δ (b :: Φ) ty)
  | _, new, _, _, .head => new.bind (·.rename KRen.wk1)
  | _, _, _, _, .tail k => (I.get k).bind (·.rename KRen.wk1)

/-- What is known under one more known binder, whose value is described by `new`. -/
def KInfo.cons {Φ : KCtx ks} {b : KBinder ks} (new : Option (ExprFn Δ Φ b.ty))
    (I : KInfo Δ Φ) : KInfo Δ (b :: Φ) :=
  ⟨fun k => I.consGet new k⟩

/-- Seen from a closed body. -/
def KInfo.toClosed {Φ : KCtx ks} (I : KInfo Δ Φ) : KInfo Δ (KCtx.closedOnly Φ) :=
  ⟨fun k => (I.get k.unmask).bind (·.rename (fun x => x.mask))⟩

/-- `I` describes the values of `κ`. -/
def KInfo.Agree {Φ : KCtx ks} (I : KInfo Δ Φ) (κ : KEnv Δ Φ) : Prop :=
  ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (f : ExprFn Δ Φ ty), I.get k = some f →
    f.Sem κ (κ.get k)

/-! ## Substituting the argument -/

/-- A pure expression that is a neutral expression. -/
def PExpr.toNeu? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} :
    {o : Lvl} → PExpr Δ Φ Γ τ o → Option ((ℓ : Nat) × Neu Δ Φ Γ τ ℓ)
  | _, .neu n => some ⟨_, n⟩
  | _, _ => none

section Subst
variable {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {lv : Nat} {oa : Lvl}

mutual
/-- Substitute `a` for the parameter in a neutral expression (`none` when the result would
    take a value that is not neutral apart). -/
def Neu.inl (a : PExpr Δ Φ Γ σ oa) : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ [⟨σ, u, lv⟩] τ ℓ → Option ((o' : Lvl) × PExpr Δ Φ Γ τ o')
  | _, _, .var (.head _) => some ⟨_, a⟩
  | _, _, .var (.tail x) => nomatch x
  | _, _, .data_out b j n => do
      let r ← Neu.inl a n
      let m ← r.2.toNeu?
      pure ⟨_, .neu (.data_out b j m.2)⟩
  | _, _, .cond c x y => do
      let r ← Neu.inl a c
      let m ← r.2.toNeu?
      let x' ← PExpr.inl a x
      let y' ← PExpr.inl a y
      pure ⟨_, .neu (.cond m.2 x'.2 y'.2)⟩
  | _, _, .extern e args _ => do
      let r ← Args.inl a args
      match r with
      | ⟨some _, args'⟩ => pure ⟨_, .neu (.extern e args' rfl)⟩
      | ⟨none, _⟩ => none
/-- Substitute `a` for the parameter in a pure expression. -/
def PExpr.inl (a : PExpr Δ Φ Γ σ oa) : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ [⟨σ, u, lv⟩] τ o → Option ((o' : Lvl) × PExpr Δ Φ Γ τ o')
  | _, _, .neu n => Neu.inl a n
  | _, _, .kvar k => some ⟨_, .kvar k⟩
  | _, _, .lit p v => some ⟨_, .lit p v⟩
  | _, _, .enum_mk s i => some ⟨_, .enum_mk s i⟩
  | _, _, .record_mk args => (Args.inl a args).map fun r => ⟨_, .record_mk r.2⟩
  | _, _, .union_mk ix args => (Args.inl a args).map fun r => ⟨_, .union_mk ix r.2⟩
  | _, _, .array_mk es => (Elems.inl a es).map fun r => ⟨_, .array_mk r.2⟩
  | _, _, .list_mk es => (Elems.inl a es).map fun r => ⟨_, .list_mk r.2⟩
  | _, _, .data_in b j e => (PExpr.inl a e).map fun r => ⟨_, .data_in b j r.2⟩
/-- Substitute `a` for the parameter in arguments. -/
def Args.inl (a : PExpr Δ Φ Γ σ oa) : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ [⟨σ, u, lv⟩] σs o → Option ((o' : Lvl) × Args Δ Φ Γ σs o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons x xs => do
      let x' ← PExpr.inl a x
      let xs' ← Args.inl a xs
      pure ⟨_, .cons x'.2 xs'.2⟩
/-- Substitute `a` for the parameter in elements. -/
def Elems.inl (a : PExpr Δ Φ Γ σ oa) : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ [⟨σ, u, lv⟩] t o → Option ((o' : Lvl) × Elems Δ Φ Γ t o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons x xs => do
      let x' ← PExpr.inl a x
      let xs' ← Elems.inl a xs
      pure ⟨_, .cons x'.2 xs'.2⟩
end

end Subst

/-- The expression computed by the closure `f` applied to `a`. -/
def ExprFn.apply {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {oa : Lvl} :
    ExprFn Δ Φ (.fn σ τ) → PExpr Δ Φ Γ σ oa → Option ((o' : Lvl) × PExpr Δ Φ Γ τ o')
  | ⟨σ', τ', _, _, _, _, body⟩, a =>
      if hs : σ' = σ ∧ τ' = τ then
        PExpr.inl a (hs.2 ▸ hs.1 ▸ body : PExpr Δ Φ [⟨σ, _, _⟩] τ _)
      else none

/-- A computation sharing the pure expression, when it is neutral and of level `ℓ`. -/
def PExpr.asShare {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    {o' : Lvl} → PExpr Δ Φ Γ τ o' → Option (Comp Δ d Φ Γ τ ℓ)
  | _, .neu (ℓ := ℓ') n => if hl : ℓ' = ℓ then some (.share (hl ▸ n)) else none
  | _, _ => none

/-- The call `f a`, with `f` inlined when it is a known closure computing an expression. -/
def Comp.inlApp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {of oa : Lvl} {ℓ : Nat}
    (I : KInfo Δ Φ) (f : PExpr Δ Φ Γ (.fn σ τ) of) (a : PExpr Δ Φ Γ σ oa)
    (h : Lvl.meet of oa = some ℓ) : Comp Δ d Φ Γ τ ℓ :=
  match f with
  | .kvar k => ((I.get k).bind fun e => (e.apply a).bind fun r => r.2.asShare).getD (.app (.kvar k) a h)
  | f => .app f a h

/-- What a value tells about itself: a closure with a closed body `ret e`. -/
def Val.exprFn? : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ ty o → Option (ExprFn Δ Φ ty)
  | _, _, _, _, _, .lam (.closed (.ret p)) =>
      (p.rename (fun x => some x.unmask) URen.id).map fun p' => ⟨_, _, rfl, _, _, _, p'⟩
  | _, _, _, _, _, _ => none

/-! ## The walk -/

mutual
/-- `Term.inlWalk` inside the bodies of a value. -/
def Val.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → KInfo Δ Φ → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b, I => .lam (b.inlWalk I)
  | _, _, _, _, _, .thunk_mk b, I => .thunk_mk (b.inlWalk I)
  | _, _, _, _, _, .lazy_mk b, I => .lazy_mk (b.inlWalk I)
  | _, _, _, _, _, .record_mk args, _ => .record_mk args
  | _, _, _, _, _, .union_mk ix args, _ => .union_mk ix args
  | _, _, _, _, _, .array_mk es, _ => .array_mk es
  | _, _, _, _, _, .list_mk es, _ => .list_mk es
  | _, _, _, _, _, .data_in b j e, _ => .data_in b j e
/-- `Term.inlWalk` in a body. -/
def Body.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → KInfo Δ Φ → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t, I => .closed (t.inlWalk I.toClosed)
  | _, _, _, _, _, _, .opened t h, I => .opened (t.inlWalk I) h
/-- `Term.inlWalk` in a computation: calls of known closures computing an expression are
    inlined. -/
def Comp.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → KInfo Δ Φ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h, I => Comp.inlApp I f a h
  | _, _, _, _, _, .share n, _ => .share n
  | _, _, _, _, _, .nat_rec n z s h, I => .nat_rec n z (s.inlWalk I) h
  | _, _, _, _, _, .array_foldl a z s h, I => .array_foldl a z (s.inlWalk I) h
  | _, _, _, _, _, .data_rec b ρ us brs j e h, I =>
      .data_rec b ρ us (fun i => (brs i).inlWalk I) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h, I =>
      .data_brec b ρ k us (fun i => (brs i).inlWalk I) j e h
  | _, _, _, _, _, .thunk_force e, _ => .thunk_force e
  | _, _, _, _, _, .lazy_force e, _ => .lazy_force e
/-- **The inlining walk**, knowing `I` about the known values in scope. -/
def Term.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → KInfo Δ Φ → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e, _ => .ret e
  | _, _, _, _, _, _, .letV u v b, I =>
      let v' := v.inlWalk I
      .letV u v' (b.inlWalk (KInfo.cons v'.exprFn? I))
  | _, _, _, _, _, _, .letE u c b, I => .letE u (c.inlWalk I) (b.inlWalk I)
  | _, _, _, _, _, _, .record_casesOn us n b, I => .record_casesOn us n (b.inlWalk I)
  | _, _, _, _, _, _, .branch br, I => .branch (br.inlWalk I)
  | _, _, _, _, _, _, .jump j e, _ => .jump j e
/-- `Term.inlWalk` in a branch. -/
def Branch.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → KInfo Δ Φ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e, I => .ite c (t.inlWalk I) (e.inlWalk I)
  | _, _, _, _, _, _, .enum_casesOn e bs, I => .enum_casesOn e (fun i => (bs i).inlWalk I)
  | _, _, _, _, _, _, .union_casesOn e bs, I => .union_casesOn e (bs.inlWalk I)
  | _, _, _, _, _, _, .join σ u uₓ body main, I => .join σ u uₓ (body.inlWalk I) (main.inlWalk I)
/-- `Term.inlWalk` in the branches of a union's case analysis. -/
def Branches.inlWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → KInfo Δ Φ → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I => .two us₁ us₂ (b₁.inlWalk I) (b₂.inlWalk I)
  | _, _, _, _, _, _, _, _, .cons us b bs, I => .cons us (b.inlWalk I) (bs.inlWalk I)
end

/-- **Inline the known closures that compute an expression** at their calls. -/
def Term.inlineKnown {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.inlWalk KInfo.empty

end LeanScript

end
