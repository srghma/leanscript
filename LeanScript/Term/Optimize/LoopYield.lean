module

public import LeanScript.Term.Optimize.JoinCtor
public import LeanScript.Term.Optimize.Fields

@[expose] public section

set_option autoImplicit false

/-!
# A loop whose state is always the same constructor

```
let x := nat_rec n (C a) (fun acc i => case acc of | … | C f => B | …); rest
```

When the initial state of a loop is a constructor literal `C a` of a union (`C` has one field),
the step takes the state apart, and the arm of `C` answers `C e` on every path (`ret (C e)`,
including in the join points of the arm), the state is `C` at every iteration: the other arms
are never run.  The loop is then written over the field of `C` alone:

```
let y := nat_rec n a (fun f i => B'); rest[x := C y]
```

where `B'` is the arm of `C` with `f` the new state and every answer `C e` replaced by `e`
(`Term.unCtor`).  The substitution in `rest` (`Term.subst`) reduces the case analyses of `x`,
which now has a known constructor.

This is what a `for` loop of `Id.run do` becomes: its state is a `ForInStep` (`done` /
`yield`), and a loop without `break` or `return` answers `yield` on every path, so its state
is the mutable variables themselves (a record of them, or the one variable), not a
`ForInStep` around them.

The same walk also drops a case analysis whose statement only rebuilds the record
(`Term.recordEta`: `let ⟨a, b⟩ := x; ret ⟨a, b⟩` is `ret x`), which is how the answer of such a
loop over a record of mutable variables ends.

The rewrite is kept only when it adds no call and keeps the level index where it is recorded.
The walk is `Term.yieldWalk`, the pass `Term.loopYield`.

**Proved:** `Term.loopYield_eval` (the value does not change, in any environment,
`LeanScript.Term.Optimize.LoopYieldEval`) and `Term.numCalls_loopYield` (no call is added).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## The pieces -/

/-- The fields of a constructor literal `ix' args`, as those of the constructor `ix`, when it
    is the same constructor (the same position in the union). -/
def CtorIx.sameArgs? {Φ : KCtx ks} {Γ : UCtx ks} {o : Lvl} : {bs : List Bool} →
    {cs : Ctors ks bs} → {b b' : Bool} → {c : Ctor ks b} → {c' : Ctor ks b'} →
    CtorIx cs c → CtorIx cs c' → Args Δ Φ Γ c'.binds o → Option (Args Δ Φ Γ c.binds o)
  | _, _, _, _, _, _, .two₁, .two₁, a => some a
  | _, _, _, _, _, _, .two₂, .two₂, a => some a
  | _, _, _, _, _, _, .head, .head, a => some a
  | _, _, _, _, _, _, .tail i, .tail j, a => CtorIx.sameArgs? i j a
  | _, _, _, _, _, _, _, _, _ => none

/-- The one field of a constructor with one field. -/
def Args.one {Φ : KCtx ks} {Γ : UCtx ks} {σ : Ty ks} :
    {o : Lvl} → Args Δ Φ Γ [σ] o → (o' : Lvl) × PExpr Δ Φ Γ σ o'
  | _, .cons a .nil => ⟨_, a⟩

/-- The field of `e` when it is the literal `ix a` (of the constructor `ix`, one field). -/
def PExpr.ctorField? {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {σ : Ty ks} (ix : CtorIx cs (.fields (.one σ))) {o : Lvl}
    (e : PExpr Δ Φ Γ (.union cs (h := h)) o) : Option ((o' : Lvl) × PExpr Δ Φ Γ σ o') := do
  let ⟨_, _, ix', _, args⟩ ← e.unionLit?
  let args ← CtorIx.sameArgs? ix ix' args
  pure (Args.one args)

/-- The literal `ix x` of the innermost unknown `x` (of the field's type), as a value of `τ`. -/
def PExpr.ctorOfHead {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {σ τ : Ty ks} {u : Usage01ω} {L : Nat}
    (ix : CtorIx cs (.fields (.one σ))) (hτ : τ = Ty.union cs (h := h)) (hu : u ≠ .zero) :
    PExpr Δ Φ (⟨σ, u, L⟩ :: Γ) τ (Lvl.meet (some L) none) :=
  hτ ▸ PExpr.union_mk ix (.cons (.neu (.var (.head hu))) .nil)

/-! ## Answers `ix e` written `e` -/

section UnCtor
variable {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {σ : Ty ks}
  (ix : CtorIx cs (.fields (.one σ))) {τ : Ty ks} (hτ : τ = Ty.union cs (h := h))

mutual
/-- The statement with every answer `ix e` replaced by `e` (in the join points too); `none` if
    an answer is not a literal of the constructor `ix`. -/
def Term.unCtor : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o : Lvl} →
    Term Δ D Φ Γ τ js o → Option ((o' : Lvl) × Term Δ D Φ Γ σ js o')
  | _, _, _, _, _, .ret e => ((hτ ▸ e : PExpr Δ _ _ (.union cs (h := h)) _).ctorField? ix).map fun p => ⟨_, .ret p.2⟩
  | _, _, _, _, _, .letV u v b => (b.unCtor).map fun p => ⟨_, .letV u v p.2⟩
  | _, _, _, _, _, .letE u c b => (b.unCtor).map fun p => ⟨_, .letE u c p.2⟩
  | _, _, _, _, _, .record_casesOn us n b =>
      (b.unCtor).map fun p => ⟨_, .record_casesOn us n p.2⟩
  | _, _, _, _, _, .branch br => (br.unCtor).map fun p => ⟨_, .branch p.2⟩
  | _, _, _, _, _, .jump j e => some ⟨_, .jump j e⟩
/-- `Term.unCtor` in a branch. -/
def Branch.unCtor : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {ℓ : Nat} →
    Branch Δ D Φ Γ τ js ℓ → Option ((ℓ' : Nat) × Branch Δ D Φ Γ σ js ℓ')
  | _, _, _, _, _, .ite c t e => do
      let t ← t.unCtor
      let e ← e.unCtor
      pure ⟨_, .ite c t.2 e.2⟩
  | _, _, _, _, _, .enum_casesOn e bs => do
      let bs ← Fin.optAll (fun i => (bs i).unCtor)
      pure ⟨_, .enum_casesOn e (fun i => (bs i).2)⟩
  | _, _, _, _, _, .union_casesOn e bs => (bs.unCtor).map fun p => ⟨_, .union_casesOn e p.2⟩
  | _, _, _, _, _, .join σ' u uₓ body main => do
      let body ← body.unCtor
      let main ← main.unCtor
      pure ⟨_, .join σ' u uₓ body.2 main.2⟩
/-- `Term.unCtor` in the branches of a union's case analysis. -/
def Branches.unCtor : {D : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs' : List Bool} →
    {cs' : Ctors ks bs'} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ D Φ Γ cs' τ js o →
    Option ((o' : Lvl) × Branches Δ D Φ Γ cs' σ js o')
  | _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => do
      let b₁ ← b₁.unCtor
      let b₂ ← b₂.unCtor
      pure ⟨_, .two us₁ us₂ b₁.2 b₂.2⟩
  | _, _, _, _, _, _, _, .cons us b bs => do
      let b ← b.unCtor
      let bs ← bs.unCtor
      pure ⟨_, .cons us b.2 bs.2⟩
end

end UnCtor

/-! ## The step of the loop -/

/-- What the step of a loop over the state `τ` becomes when the state is always the constructor
    `ix` (of `τ = union cs`, one field of type `σ`): a step over the field. -/
structure YieldStep (Δ : DSig ks) (D : Nat) (Φ : KCtx ks) (X : UCtx ks) (τ : Ty ks)
    (u₂ : Usage01ω) where
  bs : List Bool
  cs : Ctors ks bs
  h : UnionShape bs
  hτ : τ = Ty.union cs (h := h)
  σ : Ty ks
  ix : CtorIx cs (.fields (.one σ))
  o : Lvl
  step : Term Δ D Φ (⟨σ, .many, D⟩ :: ⟨.nat, u₂, D⟩ :: X) σ [] o

/-- The constructor of a literal, when it has one field. -/
def PExpr.oneFieldCtor? {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} {o : Lvl} (e : PExpr Δ Φ Γ (.union cs (h := h)) o) :
    Option ((σ : Ty ks) × CtorIx cs (.fields (.one σ))) :=
  match e.unionLit? with
  | some ⟨true, .fields (.one σ), ix, _, _⟩ => some ⟨σ, ix⟩
  | _ => none

/-- The substitution of the arm of `ix`, under its field `f`, into the new step: `f` is the new
    state, the old state is not used (the substitution fails if it is), the counter and the
    rest are kept. -/
def USub.yieldStep {Φ : KCtx ks} {X : UCtx ks} {τ σ : Ty ks} {u₁ u₂ : Usage01ω} {D : Nat}
    (us : List Usage01ω) :
    USub Δ Φ (UCtx.annot D [σ] us ++ ⟨τ, u₁, D⟩ :: ⟨.nat, u₂, D⟩ :: X)
      (⟨σ, .many, D⟩ :: ⟨.nat, u₂, D⟩ :: X) :=
  USub.ofArgs (USub.consOpt Option.none (USub.wkU (USub.ofRen ULRen.idL) _)) D [σ] us
    (.cons (.neu (.var (.head (by decide)))) .nil)

/-- The step of a loop over the state `τ`, written over the field of the constructor that
    `pick` chooses, when the step takes the state apart and the arm of that constructor answers
    it on every path. -/
def Term.yieldStep? {D : Nat} {Φ : KCtx ks} {X : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage01ω}
    {o : Lvl} (pick : {bs : List Bool} → (cs : Ctors ks bs) → (h : UnionShape bs) →
      τ = Ty.union cs (h := h) → Option ((σ : Ty ks) × CtorIx cs (.fields (.one σ))))
    (t : Term Δ D Φ (⟨τ, u₁, D⟩ :: ⟨.nat, u₂, D⟩ :: X) τ [] o) :
    Option (YieldStep Δ D Φ X τ u₂) :=
  match t.caseJoin? with
  | some (.union bs cs h hτ _ brs) => do
      let ⟨σ, ix⟩ ← pick cs h hτ
      let sel := brs.select ix
      let arm ← sel.2.2.subst (D' := D) KLRen.id (USub.yieldStep sel.1) JRen.id
      let step ← arm.2.unCtor ix hτ
      pure ⟨bs, cs, h, hτ, σ, ix, _, step.2⟩
  | _ => none

/-- The body of a loop over the field of the state, with its constructor. -/
structure YieldBody (Δ : DSig ks) (d : Nat) (Φ : KCtx ks) (Γ : UCtx ks) (τ : Ty ks)
    (u₂ : Usage01ω) where
  bs : List Bool
  cs : Ctors ks bs
  h : UnionShape bs
  hτ : τ = Ty.union cs (h := h)
  σ : Ty ks
  ix : CtorIx cs (.fields (.one σ))
  os : Lvl
  body : Body Δ d Φ Γ [⟨σ, .many, d + 1⟩, ⟨.nat, u₂, d + 1⟩] σ os

/-- `Term.yieldStep?` in the body of a loop.  An open body stays open: it must still mention
    something from outside. -/
def Body.yieldStep? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {u₁ u₂ : Usage01ω}
    {o : Lvl} (pick : {bs : List Bool} → (cs : Ctors ks bs) → (h : UnionShape bs) →
      τ = Ty.union cs (h := h) → Option ((σ : Ty ks) × CtorIx cs (.fields (.one σ)))) :
    Body Δ d Φ Γ [⟨τ, u₁, d + 1⟩, ⟨.nat, u₂, d + 1⟩] τ o → Option (YieldBody Δ d Φ Γ τ u₂)
  | .closed t => (Term.yieldStep? (X := []) pick t).map fun Y =>
      ⟨Y.bs, Y.cs, Y.h, Y.hτ, Y.σ, Y.ix, _, .closed Y.step⟩
  | .opened t _ =>
      match Term.yieldStep? (X := Γ) pick t with
      | some ⟨bs, cs, h, hτ, σ, ix, some m, step⟩ =>
          if hm : m ≤ d then some ⟨bs, cs, h, hτ, σ, ix, _, .opened step hm⟩ else none
      | _ => none

/-- `let x := c; b` (both already walked): when `c` is a loop whose state is always the same
    constructor (one field), the loop over that field, and `b` with `x` the constructor around
    its answer (`Term.subst`, which reduces the case analyses of `x`).  Kept when no call is
    added. -/
def Term.loopYieldLet {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ τ' : Ty ks} {js : JCtx ks}
    {ℓ : Nat} {o' : Lvl} (u : Usage1ω) (c : Comp Δ d Φ Γ τ ℓ)
    (b : Term Δ d Φ (⟨τ, u.toUsage01ω, d⟩ :: Γ) τ' js o') : (o : Lvl) × Term Δ d Φ Γ τ' js o :=
  match c with
  | .nat_rec (on := on) n z s _ =>
      match s.yieldStep? (fun _ _ hτ => (hτ ▸ z : PExpr Δ Φ Γ (.union _) _).oneFieldCtor?) with
      | none => ⟨_, .letE u c b⟩
      | some Y =>
          match (Y.hτ ▸ z : PExpr Δ Φ Γ (.union Y.cs (h := Y.h)) _).ctorField? Y.ix with
          | none => ⟨_, .letE u c b⟩
          | some a =>
              match hl : Lvl.meet (Lvl.meet on a.1) Y.os with
              | none => ⟨_, .letE u c b⟩
              | some _ =>
                  let lit : PExpr Δ Φ (⟨Y.σ, u.toUsage01ω, d⟩ :: Γ) τ _ :=
                    PExpr.ctorOfHead Y.ix Y.hτ (Usage1ω.toUsage01ω_ne_zero u)
                  match b.subst (D' := d) KLRen.id
                      (USub.cons ⟨_, lit⟩ (USub.wkU (USub.ofRen ULRen.idL) _)) JRen.id with
                  | none => ⟨_, .letE u c b⟩
                  | some b' =>
                      if (Comp.nat_rec n a.2 Y.body hl).numCalls + b'.2.numCalls ≤
                          c.numCalls + b.numCalls then
                        ⟨_, .letE u (.nat_rec n a.2 Y.body hl) b'.2⟩
                      else ⟨_, .letE u c b⟩
  | _ => ⟨_, .letE u c b⟩

/-! ## A record rebuilt from its fields is the record -/

/-- The unknown that a pure expression is, if it is one. -/
def PExpr.var? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} :
    {o : Lvl} → PExpr Δ Φ Γ τ o → Option ((ℓ : Nat) × UVar Γ τ ℓ)
  | _, .neu (.var x) => some ⟨_, x⟩
  | _, _ => none

/-- The arguments are exactly the unknowns `fv`, in order. -/
def Args.areVars {Φ : KCtx ks} {Γ : UCtx ks} {d : Nat} :
    {ts : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ ts o → FieldVars Γ d ts → Bool
  | [], _, .nil, .nil => true
  | _ :: _, _, .cons a as, .cons (some y) fv =>
      (match a.var? with
       | some ⟨_, x⟩ => x.index == y.index
       | none => false) && as.areVars fv
  | _ :: _, _, .cons _ _, .cons none _ => false

/-- `let ⟨fs⟩ := n; b` (`b` already walked): when `b` answers the record rebuilt from the
    fields `fs`, in order, it is the record `n` itself:
    `let ⟨a, b⟩ := x; ret ⟨a, b⟩` is `ret x`. -/
def Term.recordEta {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks}
    {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o' : Lvl} (us : List Usage01ω)
    (n : Neu Δ Φ Γ (.record t fs) ℓ)
    (b : Term Δ d Φ (UCtx.annot d (t :: fs.toList) us ++ Γ) τ js o') :
    (o : Lvl) × Term Δ d Φ Γ τ js o :=
  if h : τ = Ty.record t fs then
    match b with
    | .ret e =>
        match (h ▸ e : PExpr Δ Φ _ (.record t fs) _).recordLit? with
        | some ⟨_, args⟩ =>
            if args.areVars (FieldVars.ofAnnot Γ d (t :: fs.toList) us) then
              ⟨_, .ret (h ▸ PExpr.neu n)⟩
            else ⟨_, .record_casesOn us n b⟩
        | none => ⟨_, .record_casesOn us n b⟩
    | _ => ⟨_, .record_casesOn us n b⟩
  else ⟨_, .record_casesOn us n b⟩

/-! ## The walk -/

mutual
/-- `Term.yieldWalk` inside the bodies of a value (the level of the value is kept). -/
def Val.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.yieldWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.yieldWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.yieldWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.yieldWalk` in a body: free in a closed body, level kept in an open one. -/
def Body.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.yieldWalk.2
  | _, _, _, _, _, _, .opened t h => .opened (t.keepLvl t.yieldWalk) h
/-- `Term.yieldWalk` in the bodies of a computation. -/
def Comp.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.yieldWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.yieldWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).yieldWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).yieldWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The walk**: every loop whose state is always the same constructor is written over the
    field of that constructor (`Term.loopYieldLet`); the level may change. -/
def Term.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, .ret e => ⟨_, .ret e⟩
  | _, _, _, _, _, _, .letV u v b => ⟨_, .letV u v.yieldWalk b.yieldWalk.2⟩
  | _, _, _, _, _, _, .letE u c b => Term.loopYieldLet u c.yieldWalk b.yieldWalk.2
  | _, _, _, _, _, _, .record_casesOn us n b => Term.recordEta us n b.yieldWalk.2
  | _, _, _, _, _, _, .branch br => ⟨_, .branch br.yieldWalk.2⟩
  | _, _, _, _, _, _, .jump j e => ⟨_, .jump j e⟩
/-- `Term.yieldWalk` in a branch. -/
def Branch.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, .ite c t e => ⟨_, .ite c t.yieldWalk.2 e.yieldWalk.2⟩
  | _, _, _, _, _, _, .enum_casesOn e bs => ⟨_, .enum_casesOn e (fun i => (bs i).yieldWalk.2)⟩
  | _, _, _, _, _, _, .union_casesOn e bs => ⟨_, .union_casesOn e bs.yieldWalk.2⟩
  | _, _, _, _, _, _, .join σ u uₓ body main => ⟨_, .join σ u uₓ body.yieldWalk.2 main.yieldWalk.2⟩
/-- `Term.yieldWalk` in the branches of a union's case analysis. -/
def Branches.yieldWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => ⟨_, .two us₁ us₂ b₁.yieldWalk.2 b₂.yieldWalk.2⟩
  | _, _, _, _, _, _, _, _, .cons us b bs => ⟨_, .cons us b.yieldWalk.2 bs.yieldWalk.2⟩
end

/-- **Loops whose state is always the same constructor, written over its field.**  At the top
    the level is kept. -/
def Term.loopYield {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  t.keepLvl t.yieldWalk

end LeanScript

end
