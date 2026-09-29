module

public import LeanScript.Term.Rename.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Renamings that change levels and depths

`Term.rename` (`LeanScript.Term.Rename.Basic`) keeps the level of every variable, so a statement
keeps its depth and its level.  To inline the body of a closure where it is called, the body
must move to another depth: its parameters and the unknowns it binds were at the depth of the
closure plus one, they end up at the depth of the call.

`Term.relvl` renames the variables of a statement along maps that may change their levels
(`ULRen`, `KLRen`), and moves it from depth `D` to depth `D'`: each binder of the statement at
depth `D` is rebound at `D'`, each binder of a body inside (depth `D + 1`) at `D' + 1`, and so
on.  The levels of the result are recomputed; the side conditions that depend on them (an open
body mentions something bound outside of it, `m ≤ D'`; a computation, an extern call keeps an
open operand) are checked, and the renaming fails (`none`) when one does not hold.

`Term.relvl_eval` (`LeanScript.Term.Rename.RelevelEval`): when the maps agree with the
environments, the renamed statement has the same value.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Maps -/

/-- A partial renaming of unknowns that may change their levels. -/
abbrev ULRen (Γ Γ' : UCtx ks) : Type :=
  ∀ {τ : Ty ks} {ℓ : Nat}, UVar Γ τ ℓ → Option ((ℓ' : Nat) × UVar Γ' τ ℓ')

/-- A partial renaming of known values that may change their levels. -/
abbrev KLRen (Φ Φ' : KCtx ks) : Type :=
  ∀ {τ : Ty ks} {o : Lvl}, KVar Φ τ o → Option ((o' : Lvl) × KVar Φ' τ o')

/-- The binders `bs`, all at level `L`. -/
def UCtx.setLv (L : Nat) : UCtx ks → UCtx ks
  | [] => []
  | b :: bs => ⟨b.ty, b.use, L⟩ :: UCtx.setLv L bs

/-- The same values, for the binders moved to level `L`. -/
def UEnv.setLv (L : Nat) : {bs : UCtx ks} → UEnv Δ bs → UEnv Δ (UCtx.setLv L bs)
  | [], _ => PUnit.unit
  | _ :: _, vs => Tuple.cons vs.head (UEnv.setLv L vs.tail)

/-- A level as `some ℓ`, when it is one. -/
def Lvl.some? : (o : Lvl) → Option ((ℓ : Nat) ×' o = some ℓ)
  | some ℓ => some ⟨ℓ, rfl⟩
  | none => none

/-- Under one more binder, moved to level `L'`. -/
def ULRen.lift {Γ Γ' : UCtx ks} (r : ULRen Γ Γ') (σ : Ty ks) (u : Usage01ω) (L L' : Nat) :
    ULRen (⟨σ, u, L⟩ :: Γ) (⟨σ, u, L'⟩ :: Γ')
  | _, _, .head h => some ⟨L', .head h⟩
  | _, _, .tail x => (r x).map fun p => ⟨p.1, .tail p.2⟩

/-- Under the binders `bs`, moved to level `L'`. -/
def ULRen.liftSet {Γ Γ' : UCtx ks} (r : ULRen Γ Γ') (L' : Nat) :
    (bs : UCtx ks) → ULRen (bs ++ Γ) (UCtx.setLv L' bs ++ Γ')
  | [] => r
  | b :: bs => ULRen.lift (ULRen.liftSet r L' bs) b.ty b.use b.lv L'

/-- The binders `bs` alone, moved to level `L'`. -/
def ULRen.setLvOnly (L' : Nat) : (bs : UCtx ks) → ULRen bs (UCtx.setLv L' bs)
  | [] => fun x => nomatch x
  | b :: bs => ULRen.lift (ULRen.setLvOnly L' bs) b.ty b.use b.lv L'

/-- Under the fields of a case analysis, moved from level `L` to level `L'`. -/
def ULRen.liftAnnot {Γ Γ' : UCtx ks} (r : ULRen Γ Γ') (L L' : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) →
    ULRen (UCtx.annot L ts us ++ Γ) (UCtx.annot L' ts us ++ Γ')
  | [], _ => r
  | t :: ts, [] => ULRen.lift (ULRen.liftAnnot r L L' ts []) t .many L L'
  | t :: ts, u :: us => ULRen.lift (ULRen.liftAnnot r L L' ts us) t u L L'

/-- Under one more known binder, whose level becomes `o'`. -/
def KLRen.lift {Φ Φ' : KCtx ks} (r : KLRen Φ Φ') (σ : Ty ks) (u : Usage1ω) (o o' : Lvl) :
    KLRen (⟨σ, u, o, true⟩ :: Φ) (⟨σ, u, o', true⟩ :: Φ')
  | _, _, .head => some ⟨o', .head⟩
  | _, _, .tail x => (r x).map fun p => ⟨p.1, .tail p.2⟩

/-- As seen from closed bodies. -/
def KLRen.closedOnly {Φ Φ' : KCtx ks} (r : KLRen Φ Φ') :
    KLRen (KCtx.closedOnly Φ) (KCtx.closedOnly Φ') :=
  fun x => (r x.unmask).bind fun p => p.2.mask.map fun y => ⟨p.1, y⟩

/-! ## Pure expressions -/

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KLRen Φ Φ') (ru : ULRen Γ Γ')

mutual
/-- Rename a neutral expression, recomputing its level. -/
def Neu.relvl : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Option ((ℓ' : Nat) × Neu Δ Φ' Γ' τ ℓ')
  | _, _, .var x => (ru x).map fun p => ⟨_, .var p.2⟩
  | _, _, .data_out b j n => (Neu.relvl n).map fun p => ⟨_, .data_out b j p.2⟩
  | _, _, .cond c a b => do
      let c ← Neu.relvl c
      let a ← PExpr.relvl a
      let b ← PExpr.relvl b
      pure ⟨_, .cond c.2 a.2 b.2⟩
  | _, _, .extern e args _ => do
      let as ← Args.relvl args
      let h ← Lvl.some? as.1
      pure ⟨_, .extern e as.2 h.2⟩
/-- Rename a pure expression, recomputing its level. -/
def PExpr.relvl : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    Option ((o' : Lvl) × PExpr Δ Φ' Γ' τ o')
  | _, _, .neu n => (Neu.relvl n).map fun p => ⟨_, .neu p.2⟩
  | _, _, .kvar k => (rk k).map fun p => ⟨_, .kvar p.2⟩
  | _, _, .lit p v => some ⟨_, .lit p v⟩
  | _, _, .enum_mk s i => some ⟨_, .enum_mk s i⟩
  | _, _, .record_mk args => (Args.relvl args).map fun p => ⟨_, .record_mk p.2⟩
  | _, _, .union_mk ix args => (Args.relvl args).map fun p => ⟨_, .union_mk ix p.2⟩
  | _, _, .array_mk es => (Elems.relvl es).map fun p => ⟨_, .array_mk p.2⟩
  | _, _, .list_mk es => (Elems.relvl es).map fun p => ⟨_, .list_mk p.2⟩
  | _, _, .data_in b j e => (PExpr.relvl e).map fun p => ⟨_, .data_in b j p.2⟩
/-- Rename arguments, recomputing their level. -/
def Args.relvl : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Option ((o' : Lvl) × Args Δ Φ' Γ' σs o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons a as => do
      let a ← PExpr.relvl a
      let as ← Args.relvl as
      pure ⟨_, .cons a.2 as.2⟩
/-- Rename elements, recomputing their level. -/
def Elems.relvl : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    Option ((o' : Lvl) × Elems Δ Φ' Γ' t o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons e es => do
      let e ← PExpr.relvl e
      let es ← Elems.relvl es
      pure ⟨_, .cons e.2 es.2⟩
end

end Layer1

/-! ## Statements -/

mutual
/-- Rename a value and move it from depth `D` to depth `D'`. -/
def Val.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' → ULRen Γ Γ' →
    {τ : Ty ks} → {o : Lvl} → Val Δ D Φ Γ τ o → Option ((o' : Lvl) × Val Δ D' Φ' Γ' τ o')
  | _, _, _, _, _, _, rk, ru, _, _, .lam b => (b.relvl rk ru).map fun p => ⟨_, .lam p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .thunk_mk b => (b.relvl rk ru).map fun p => ⟨_, .thunk_mk p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .lazy_mk b => (b.relvl rk ru).map fun p => ⟨_, .lazy_mk p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .record_mk args =>
      (args.relvl rk ru).map fun p => ⟨_, .record_mk p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .union_mk ix args =>
      (args.relvl rk ru).map fun p => ⟨_, .union_mk ix p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .array_mk es => (es.relvl rk ru).map fun p => ⟨_, .array_mk p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .list_mk es => (es.relvl rk ru).map fun p => ⟨_, .list_mk p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .data_in b j e =>
      (e.relvl rk ru).map fun p => ⟨_, .data_in b j p.2⟩
/-- Rename a body and move it from depth `D` to depth `D'` (its binders from `D + 1` to
    `D' + 1`). -/
def Body.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' → ULRen Γ Γ' →
    {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} → Body Δ D Φ Γ bs τ o →
    Option ((o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o')
  | _, D', _, _, _, _, rk, _, bs, _, _, .closed t =>
      (t.relvl (D' := D' + 1) (KLRen.closedOnly rk) (ULRen.setLvOnly (D' + 1) bs) JRen.nil).map
        fun p => ⟨_, .closed p.2⟩
  | _, D', _, _, _, _, rk, ru, bs, _, _, .opened t _ => do
      let p ← t.relvl (D' := D' + 1) rk (ULRen.liftSet ru (D' + 1) bs) JRen.nil
      let m ← Lvl.some? p.1
      if hm : m.1 ≤ D' then pure ⟨_, .opened (m.2 ▸ p.2) hm⟩ else none
/-- Rename a computation and move it from depth `D` to depth `D'`. -/
def Comp.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' → ULRen Γ Γ' →
    {τ : Ty ks} → {ℓ : Nat} → Comp Δ D Φ Γ τ ℓ → Option ((ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ')
  | _, _, _, _, _, _, rk, ru, _, _, .app f a _ => do
      let f ← f.relvl rk ru
      let a ← a.relvl rk ru
      let h ← Lvl.some? (Lvl.meet f.1 a.1)
      pure ⟨_, .app f.2 a.2 h.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .share n => (n.relvl rk ru).map fun p => ⟨_, .share p.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .nat_rec n z s _ => do
      let n ← n.relvl rk ru
      let z ← z.relvl rk ru
      let s ← s.relvl rk ru
      let h ← Lvl.some? (Lvl.meet (Lvl.meet n.1 z.1) s.1)
      pure ⟨_, .nat_rec n.2 z.2 s.2 h.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .array_foldl a z s _ => do
      let a ← a.relvl rk ru
      let z ← z.relvl rk ru
      let s ← s.relvl rk ru
      let h ← Lvl.some? (Lvl.meet (Lvl.meet a.1 z.1) s.1)
      pure ⟨_, .array_foldl a.2 z.2 s.2 h.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .data_rec b ρ us brs j e _ => do
      let brs ← Fin.optAll (fun i => (brs i).relvl rk ru)
      let e ← e.relvl rk ru
      let h ← Lvl.some? (Lvl.meet e.1 (Lvl.meetFin _ (fun i => (brs i).1)))
      pure ⟨_, .data_rec b ρ us (fun i => (brs i).2) j e.2 h.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .data_brec b ρ k us brs j e _ => do
      let brs ← Fin.optAll (fun i => (brs i).relvl rk ru)
      let e ← e.relvl rk ru
      let h ← Lvl.some? (Lvl.meet e.1 (Lvl.meetFin _ (fun i => (brs i).1)))
      pure ⟨_, .data_brec b ρ k us (fun i => (brs i).2) j e.2 h.2⟩
  | _, _, _, _, _, _, rk, ru, _, _, .thunk_force e => do
      let e ← e.relvl rk ru
      let h ← Lvl.some? e.1
      pure ⟨_, .thunk_force (h.2 ▸ e.2)⟩
  | _, _, _, _, _, _, rk, ru, _, _, .lazy_force e => do
      let e ← e.relvl rk ru
      let h ← Lvl.some? e.1
      pure ⟨_, .lazy_force (h.2 ▸ e.2)⟩
/-- Rename a statement and move it from depth `D` to depth `D'`. -/
def Term.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → ULRen Γ Γ' → JRen js js' → {τ : Ty ks} → {o : Lvl} →
    Term Δ D Φ Γ τ js o → Option ((o' : Lvl) × Term Δ D' Φ' Γ' τ js' o')
  | _, _, _, _, _, _, _, _, rk, ru, _, _, _, .ret e => (e.relvl rk ru).map fun p => ⟨_, .ret p.2⟩
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .letV (σ := σ) (o := o) u v b => do
      let v ← v.relvl rk ru
      let b ← b.relvl (KLRen.lift rk σ u o v.1) ru rj
      pure ⟨_, .letV u v.2 b.2⟩
  | D, D', _, _, _, _, _, _, rk, ru, rj, _, _, .letE (σ := σ) u c b => do
      let c ← c.relvl rk ru
      let b ← b.relvl (D' := D') rk (ULRen.lift ru σ u.toUsage01ω D D') rj
      pure ⟨_, .letE u c.2 b.2⟩
  | D, D', _, _, _, _, _, _, rk, ru, rj, _, _, .record_casesOn (t := t) (fs := fs) us n b => do
      let n ← n.relvl rk ru
      let b ← b.relvl (D' := D') rk (ULRen.liftAnnot ru D D' (t :: fs.toList) us) rj
      pure ⟨_, .record_casesOn us n.2 b.2⟩
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .branch br =>
      (br.relvl rk ru rj).map fun p => ⟨_, .branch p.2⟩
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .jump j e => do
      let j ← rj j
      let e ← e.relvl rk ru
      pure ⟨_, .jump j e.2⟩
/-- Rename a branch and move it from depth `D` to depth `D'`. -/
def Branch.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → ULRen Γ Γ' → JRen js js' → {τ : Ty ks} → {ℓ : Nat} →
    Branch Δ D Φ Γ τ js ℓ → Option ((ℓ' : Nat) × Branch Δ D' Φ' Γ' τ js' ℓ')
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .ite c t e => do
      let c ← c.relvl rk ru
      let t ← t.relvl rk ru rj
      let e ← e.relvl rk ru rj
      pure ⟨_, .ite c.2 t.2 e.2⟩
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .enum_casesOn e bs => do
      let e ← e.relvl rk ru
      let bs ← Fin.optAll (fun i => (bs i).relvl rk ru rj)
      pure ⟨_, .enum_casesOn e.2 (fun i => (bs i).2)⟩
  | _, _, _, _, _, _, _, _, rk, ru, rj, _, _, .union_casesOn e bs => do
      let e ← e.relvl rk ru
      let bs ← bs.relvl rk ru rj
      pure ⟨_, .union_casesOn e.2 bs.2⟩
  | D, D', _, _, _, _, _, _, rk, ru, rj, _, _, .join σ u uₓ body main => do
      let body ← body.relvl (D' := D') rk (ULRen.lift ru σ uₓ D D') rj
      let main ← main.relvl rk ru (JRen.lift rj _)
      pure ⟨_, .join σ u uₓ body.2 main.2⟩
/-- Rename the branches of a union's case analysis and move them from depth `D` to `D'`. -/
def Branches.relvl : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → ULRen Γ Γ' → JRen js js' → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → {o : Lvl} → Branches Δ D Φ Γ cs τ js o →
    Option ((o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o')
  | D, D', _, _, _, _, _, _, rk, ru, rj, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂ => do
      let b₁ ← b₁.relvl (D' := D') rk (ULRen.liftAnnot ru D D' c₁.binds us₁) rj
      let b₂ ← b₂.relvl (D' := D') rk (ULRen.liftAnnot ru D D' c₂.binds us₂) rj
      pure ⟨_, .two us₁ us₂ b₁.2 b₂.2⟩
  | D, D', _, _, _, _, _, _, rk, ru, rj, _, _, _, _, .cons (c := c) us b bs => do
      let b ← b.relvl (D' := D') rk (ULRen.liftAnnot ru D D' c.binds us) rj
      let bs ← bs.relvl rk ru rj
      pure ⟨_, .cons us b.2 bs.2⟩
end

end LeanScript

end
