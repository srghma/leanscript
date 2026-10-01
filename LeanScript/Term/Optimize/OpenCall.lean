module

public import LeanScript.Term.Optimize.InlineRetEval

@[expose] public section

set_option autoImplicit false

/-!
# Calls of known closures with an open body that compute an expression

`Term.inlineKnown` inlines the calls of a known closure whose **closed** body is `ret e`.  A
closure whose body is `ret e` but mentions an unknown bound outside of it (an *open* body, such
as `fun _ => f` for a field `f`, which is what `Function.const` and `fun g => g x` become) is
not inlined there, because its expression is not one of the known context alone.

`Term.ocWalk` carries, for each known variable in scope that is such a closure, its expression
as one of the *current* known and unknown contexts (`OpenFnE`, moved along the binders it goes
under, `OInfo`), and replaces a call `let y := k a` by `let y := share e[a]` when `e[a]` (the
parameter replaced by `a`, `PExpr.subst`) is neutral.  `a` must cost nothing to repeat, or the
parameter be used at most once.  The level may change (`Term.keepLvl` where it is recorded).

**Proved:** `Term.openCall_eval` (the value does not change) and `Term.numCalls_openCall` (no
call is added: a call becomes a shared expression).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- A closure of type `ty = σ → τ` that computes the pure expression `body` of its parameter,
    in the known context `Φ` and the unknown context `Γ`. -/
structure OpenFnE (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) (ty : Ty ks) where
  σ : Ty ks
  τ : Ty ks
  hty : ty = .fn σ τ
  u : Usage01ω
  L : Nat
  o : Lvl
  body : PExpr Δ Φ (⟨σ, u, L⟩ :: Γ) τ o

/-- `f` describes the value `x` in the environments `κ`, `ρ`. -/
def OpenFnE.Sem {Φ : KCtx ks} {Γ : UCtx ks} {ty : Ty ks} (f : OpenFnE Δ Φ Γ ty) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (x : Ty.Den Δ ty) : Prop :=
  ∀ v : Ty.Den Δ f.σ, (cast (congrArg (Ty.Den Δ) f.hty) x : Ty.Den Δ (.fn f.σ f.τ)) v =
    f.body.eval κ (Tuple.cons v ρ)

/-- Move the description along renamings. -/
def OpenFnE.rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ')
    {ty : Ty ks} (f : OpenFnE Δ Φ Γ ty) : Option (OpenFnE Δ Φ' Γ' ty) :=
  (f.body.rename rk (URen.lift ru _)).map fun b => ⟨f.σ, f.τ, f.hty, f.u, f.L, f.o, b⟩

/-- What is known about the known values in scope. -/
structure OInfo (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Type where
  get : ∀ {ty : Ty ks} {o : Lvl}, KVar Φ ty o → Option (OpenFnE Δ Φ Γ ty)

/-- Nothing is known. -/
def OInfo.empty {Φ : KCtx ks} {Γ : UCtx ks} : OInfo Δ Φ Γ := ⟨fun _ => none⟩

/-- The lookup under one more known binder. -/
def OInfo.consGet {Φ : KCtx ks} {Γ : UCtx ks} (I : OInfo Δ Φ Γ) :
    {b : KBinder ks} → Option (OpenFnE Δ Φ Γ b.ty) → {ty : Ty ks} → {o : Lvl} →
    KVar (b :: Φ) ty o → Option (OpenFnE Δ (b :: Φ) Γ ty)
  | _, new, _, _, .head => new.bind (·.rename KRen.wk1 URen.id)
  | _, _, _, _, .tail k => (I.get k).bind (·.rename KRen.wk1 URen.id)

/-- Under one more known binder, whose value is described by `new`. -/
def OInfo.cons {Φ : KCtx ks} {Γ : UCtx ks} {b : KBinder ks} (new : Option (OpenFnE Δ Φ Γ b.ty))
    (I : OInfo Δ Φ Γ) : OInfo Δ (b :: Φ) Γ :=
  ⟨fun k => I.consGet new k⟩

/-- Under the unknowns `bs`. -/
def OInfo.wkN {Φ : KCtx ks} {Γ : UCtx ks} (I : OInfo Δ Φ Γ) (bs : UCtx ks) : OInfo Δ Φ (bs ++ Γ) :=
  ⟨fun k => (I.get k).bind (·.rename KRen.id (URen.wkN bs))⟩

/-- Under one more unknown. -/
def OInfo.wk1 {Φ : KCtx ks} {Γ : UCtx ks} (I : OInfo Δ Φ Γ) (b : UBinder ks) :
    OInfo Δ Φ (b :: Γ) :=
  ⟨fun k => (I.get k).bind (·.rename KRen.id URen.wk1)⟩

/-- `I` describes the values of `κ`. -/
def OInfo.Agree {Φ : KCtx ks} {Γ : UCtx ks} (I : OInfo Δ Φ Γ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    Prop :=
  ∀ {ty : Ty ks} {o : Lvl} (k : KVar Φ ty o) (f : OpenFnE Δ Φ Γ ty), I.get k = some f →
    f.Sem κ ρ (κ.get k)

/-- The answer of a statement that is `ret e`. -/
def Term.asRet? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} :
    {o : Lvl} → Term Δ d Φ Γ τ js o → Option ((o' : Lvl) × PExpr Δ Φ Γ τ o')
  | _, .ret e => some ⟨_, e⟩
  | _, _ => none

/-- What a value tells about itself: a closure whose open body is `ret e`. -/
def Val.openFnE? : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {ty : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ ty o → Option (OpenFnE Δ Φ Γ ty)
  | _, _, _, _, _, .lam (.opened t _) => t.asRet?.map fun p => ⟨_, _, rfl, _, _, _, p.2⟩
  | _, _, _, _, _, _ => none

/-- The expression `f` computes, its parameter replaced by `a`. -/
def OpenFnE.apply {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {oa : Lvl}
    (f : OpenFnE Δ Φ Γ (.fn σ τ)) (a : PExpr Δ Φ Γ σ oa) : Option ((o : Lvl) × PExpr Δ Φ Γ τ o) :=
  match f with
  | ⟨σ', τ', _, u, _, _, body⟩ =>
      if hs : σ' = σ ∧ τ' = τ then
        if a.isCheap || u.atMostOnce then
          (hs.2 ▸ hs.1 ▸ body : PExpr Δ Φ (⟨σ, u, _⟩ :: Γ) τ _).subst KLRen.id
            (USub.cons ⟨_, a⟩ (USub.ofRen ULRen.idL))
        else none
      else none

/-- A call of a known closure computing an open expression, as a shared neutral expression. -/
def Comp.openCall? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} {ℓ : Nat}
    (I : OInfo Δ Φ Γ) : Comp Δ d Φ Γ σ ℓ → Option ((ℓ' : Nat) × Comp Δ d Φ Γ σ ℓ')
  | .app (.kvar k) a _ =>
      (I.get k).bind fun f => (f.apply a).bind fun p => p.2.toNeu?.map fun n => ⟨_, .share n.2⟩
  | _ => none

/-! ## The walk -/

mutual
/-- `Term.ocWalk` inside the bodies of a value (the level of the value is kept). -/
def Val.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → OInfo Δ Φ Γ → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b, I => .lam (b.ocWalk I)
  | _, _, _, _, _, .thunk_mk b, I => .thunk_mk (b.ocWalk I)
  | _, _, _, _, _, .lazy_mk b, I => .lazy_mk (b.ocWalk I)
  | _, _, _, _, _, .record_mk args, _ => .record_mk args
  | _, _, _, _, _, .union_mk ix args, _ => .union_mk ix args
  | _, _, _, _, _, .array_mk es, _ => .array_mk es
  | _, _, _, _, _, .list_mk es, _ => .list_mk es
  | _, _, _, _, _, .data_in b j e, _ => .data_in b j e
/-- `Term.ocWalk` in a body: nothing is known in a closed body (level free there), the level is
    kept in an open one. -/
def Body.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → OInfo Δ Φ Γ → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t, _ => .closed (t.ocWalk OInfo.empty).2
  | _, _, _, bs, _, _, .opened t h, I => .opened (t.keepLvl (t.ocWalk (I.wkN bs))) h
/-- `Term.ocWalk` in the bodies of a computation. -/
def Comp.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → OInfo Δ Φ Γ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h, _ => .app f a h
  | _, _, _, _, _, .share n, _ => .share n
  | _, _, _, _, _, .nat_rec n z s h, I => .nat_rec n z (s.ocWalk I) h
  | _, _, _, _, _, .array_foldl a z s h, I => .array_foldl a z (s.ocWalk I) h
  | _, _, _, _, _, .data_rec b ρ us brs j e h, I =>
      .data_rec b ρ us (fun i => (brs i).ocWalk I) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h, I =>
      .data_brec b ρ k us (fun i => (brs i).ocWalk I) j e h
  | _, _, _, _, _, .thunk_force e, _ => .thunk_force e
  | _, _, _, _, _, .lazy_force e, _ => .lazy_force e
/-- **The walk**, knowing `I` about the known values in scope; the level may change. -/
def Term.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → OInfo Δ Φ Γ → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, .ret e, _ => ⟨_, .ret e⟩
  | _, _, _, _, _, _, .letV u v b, I =>
      let v' := v.ocWalk I
      ⟨_, .letV u v' (b.ocWalk (I.cons v'.openFnE?)).2⟩
  | _, _, _, _, _, _, .letE u c b, I =>
      let c' := c.ocWalk I
      let c'' := (c'.openCall? I).getD ⟨_, c'⟩
      ⟨_, .letE u c''.2 (b.ocWalk (I.wk1 _)).2⟩
  | _, _, _, _, _, _, .record_casesOn us n b, I => ⟨_, .record_casesOn us n (b.ocWalk (I.wkN _)).2⟩
  | _, _, _, _, _, _, .branch br, I => ⟨_, .branch (br.ocWalk I).2⟩
  | _, _, _, _, _, _, .jump j e, _ => ⟨_, .jump j e⟩
/-- `Term.ocWalk` in a branch. -/
def Branch.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → OInfo Δ Φ Γ → (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, .ite c t e, I => ⟨_, .ite c (t.ocWalk I).2 (e.ocWalk I).2⟩
  | _, _, _, _, _, _, .enum_casesOn e bs, I =>
      ⟨_, .enum_casesOn e (fun i => ((bs i).ocWalk I).2)⟩
  | _, _, _, _, _, _, .union_casesOn e bs, I => ⟨_, .union_casesOn e (bs.ocWalk I).2⟩
  | _, _, _, _, _, _, .join σ u uₓ body main, I =>
      ⟨_, .join σ u uₓ (body.ocWalk (I.wk1 _)).2 (main.ocWalk I).2⟩
/-- `Term.ocWalk` in the branches of a union's case analysis. -/
def Branches.ocWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → OInfo Δ Φ Γ → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, I =>
      ⟨_, .two us₁ us₂ (b₁.ocWalk (I.wkN _)).2 (b₂.ocWalk (I.wkN _)).2⟩
  | _, _, _, _, _, _, _, _, .cons us b bs, I =>
      ⟨_, .cons us (b.ocWalk (I.wkN _)).2 (bs.ocWalk I).2⟩
end

/-- **Calls of known closures with an open body computing an expression, inlined.**  At the
    top the level is kept. -/
def Term.openCall {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.keepLvl (t.ocWalk OInfo.empty)

end LeanScript

end
