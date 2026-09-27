module

public import LeanScript.NTerm.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Partial renamings of normal-form terms

A renaming maps the variables of one context to those of another, preserving their types
(and, for known values, their openness).  Here renamings are **partial**
(`URen Γ Γ' := UVar Γ τ → Option (UVar Γ' τ)`): renaming a term fails (`none`) when a variable
it uses has no image.  This covers at once

* **strengthening**: dropping a binder that is not used (the head maps to `none`);
* **re-annotation**: changing the usage of a binder (the head maps to the head of the new
  context when its usage is not `zero`, to `none` otherwise).

Renaming also fails when an open body (`Body.opened`, which needs an unknown in scope) would
end up with no unknown in scope.

`Term.rename_eval` (in `LeanScript.NTerm.RenameEval`) proves that a successful renaming
preserves the value, in environments that agree along the renaming.
-/

namespace LeanScript.NTerm

variable {ks : List Nat} {Δ : DSig ks}

/-- A partial renaming of unknowns (or of join points). -/
abbrev URen (Γ Γ' : UCtx ks) : Type := ∀ {τ : Ty ks}, UVar Γ τ → Option (UVar Γ' τ)

/-- A partial renaming of known values, preserving openness. -/
abbrev KRen (Φ Φ' : KCtx ks) : Type :=
  ∀ {τ : Ty ks} {o : Bool}, KVar Φ τ o → Option (KVar Φ' τ o)

/-- The identity. -/
def URen.id {Γ : UCtx ks} : URen Γ Γ := fun x => some x

/-- The identity. -/
def KRen.id {Φ : KCtx ks} : KRen Φ Φ := fun x => some x

/-- The renaming under one more binder. -/
def URen.lift {Γ Γ' : UCtx ks} (r : URen Γ Γ') : (b : UBinder ks) → URen (b :: Γ) (b :: Γ')
  | ⟨_, _⟩, _, .head h => some (.head h)
  | ⟨_, _⟩, _, .tail x => (r x).map .tail

/-- The renaming under the binders `bs`. -/
def URen.liftN {Γ Γ' : UCtx ks} (r : URen Γ Γ') : (bs : UCtx ks) → URen (bs ++ Γ) (bs ++ Γ')
  | [] => r
  | b :: bs => URen.lift (URen.liftN r bs) b

/-- The renaming under one more known binder. -/
def KRen.lift {Φ Φ' : KCtx ks} (r : KRen Φ Φ') : (b : KBinder ks) → KRen (b :: Φ) (b :: Φ')
  | ⟨_, _, _⟩, _, _, .head h => some (.head h)
  | ⟨_, _, _⟩, _, _, .tail x => (r x).map .tail

/-- The renaming seen from a closed body. -/
def KRen.closedOnly {Φ Φ' : KCtx ks} (r : KRen Φ Φ') :
    KRen (KCtx.closedOnly Φ) (KCtx.closedOnly Φ') :=
  fun x => (r x.unmask).bind KVar.mask

/-- Drop an unused unknown binder. -/
def URen.drop {Γ : UCtx ks} {σ : Ty ks} {u : Usage} : URen (⟨σ, u⟩ :: Γ) Γ
  | _, .head _ => none
  | _, .tail x => some x

/-- Drop an unused known binder. -/
def KRen.drop {Φ : KCtx ks} {σ : Ty ks} {u : Usage} {o : Bool} : KRen (⟨σ, u, o⟩ :: Φ) Φ
  | _, _, .head _ => none
  | _, _, .tail x => some x

/-- Change the usage of the innermost unknown binder. -/
def URen.reuse {Γ : UCtx ks} {σ : Ty ks} {u : Usage} (u' : Usage) :
    URen (⟨σ, u⟩ :: Γ) (⟨σ, u'⟩ :: Γ)
  | _, .head _ => if h : u' = .zero then none else some (.head h)
  | _, .tail x => some (.tail x)

/-- Change the usage of the innermost known binder. -/
def KRen.reuse {Φ : KCtx ks} {σ : Ty ks} {u : Usage} {o : Bool} (u' : Usage) :
    KRen (⟨σ, u, o⟩ :: Φ) (⟨σ, u', o⟩ :: Φ)
  | _, _, .head _ => if h : u' = .zero then none else some (.head h)
  | _, _, .tail x => some (.tail x)

/-- There is nothing to rename in an empty context. -/
def URen.nil : URen ([] : UCtx ks) [] := fun x => nomatch x

/-- All the options are there, as one function. -/
def Fin.optAll {n : Nat} {β : Fin n → Type} (f : (i : Fin n) → Option (β i)) :
    Option ((i : Fin n) → β i) :=
  if h : ∀ i, (f i).isSome = true then some (fun i => (f i).get (h i)) else none

theorem Fin.optAll_eq_some {n : Nat} {β : Fin n → Type} {f : (i : Fin n) → Option (β i)}
    {g : (i : Fin n) → β i} (h : Fin.optAll f = some g) (i : Fin n) : f i = some (g i) := by
  unfold Fin.optAll at h
  split at h
  · cases h; simp
  · cases h

section Rename

mutual
/-- Rename a neutral expression. -/
def Neu.rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') :
    {τ : Ty ks} → Neu Δ Φ Γ τ → Option (Neu Δ Φ' Γ' τ)
  | _, .var x => (ru x).map .var
  | _, .data_out b j n => (n.rename rk ru).map (.data_out b j)
  | _, .cond c a b => do
      let c ← c.rename rk ru
      let a ← a.rename rk ru
      let b ← b.rename rk ru
      pure (.cond c a b)
  | _, .extern e args => (args.rename rk ru).map (.extern e)
/-- Rename a pure expression. -/
def PExpr.rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') :
    {τ : Ty ks} → {o : Bool} → PExpr Δ Φ Γ τ o → Option (PExpr Δ Φ' Γ' τ o)
  | _, _, .neu n => (n.rename rk ru).map .neu
  | _, _, .kvar k => (rk k).map .kvar
  | _, _, .lit p v => some (.lit p v)
  | _, _, .enum_mk s i => some (.enum_mk s i)
  | _, _, .record_mk args => (args.rename rk ru).map .record_mk
  | _, _, .union_mk ix args => (args.rename rk ru).map (.union_mk ix)
  | _, _, .array_mk es => (es.rename rk ru).map .array_mk
  | _, _, .list_mk es => (es.rename rk ru).map .list_mk
  | _, _, .data_in b j e => (e.rename rk ru).map (.data_in b j)
/-- Rename arguments. -/
def Args.rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') :
    {σs : List (Ty ks)} → {o : Bool} → Args Δ Φ Γ σs o → Option (Args Δ Φ' Γ' σs o)
  | _, _, .nil => some .nil
  | _, _, .cons a as => do
      let a ← a.rename rk ru
      let as ← as.rename rk ru
      pure (.cons a as)
/-- Rename elements. -/
def Elems.rename {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KRen Φ Φ') (ru : URen Γ Γ') :
    {t : Ty ks} → {o : Bool} → Elems Δ Φ Γ t o → Option (Elems Δ Φ' Γ' t o)
  | _, _, .nil => some .nil
  | _, _, .cons e es => do
      let e ← e.rename rk ru
      let es ← es.rename rk ru
      pure (.cons e es)
end

mutual
/-- Rename a value. -/
def Val.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KRen Φ Φ' → URen Γ Γ' →
    {τ : Ty ks} → {o : Bool} → Val Δ Φ Γ τ o → Option (Val Δ Φ' Γ' τ o)
  | _, _, _, _, rk, ru, _, _, .lam b => (b.rename rk ru).map .lam
  | _, _, _, _, rk, ru, _, _, .thunk_mk b => (b.rename rk ru).map .thunk_mk
  | _, _, _, _, rk, ru, _, _, .lazy_mk b => (b.rename rk ru).map .lazy_mk
  | _, _, _, _, rk, ru, _, _, .record_mk args => (args.rename rk ru).map .record_mk
  | _, _, _, _, rk, ru, _, _, .union_mk ix args => (args.rename rk ru).map (.union_mk ix)
  | _, _, _, _, rk, ru, _, _, .array_mk es => (es.rename rk ru).map .array_mk
  | _, _, _, _, rk, ru, _, _, .list_mk es => (es.rename rk ru).map .list_mk
  | _, _, _, _, rk, ru, _, _, .data_in b j e => (e.rename rk ru).map (.data_in b j)
/-- Rename a body. -/
def Body.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KRen Φ Φ' → URen Γ Γ' →
    {bs : UCtx ks} → {τ : Ty ks} → {o : Bool} → Body Δ Φ Γ bs τ o →
    Option (Body Δ Φ' Γ' bs τ o)
  | _, _, _, _, rk, _, _, _, _, .closed t =>
      (t.rename (KRen.closedOnly rk) URen.id URen.nil).map .closed
  | _, _, _, [], _, _, _, _, _, .opened _ => none
  | _, _, _, _ :: _, rk, ru, bs, _, _, .opened t =>
      (t.rename rk (URen.liftN ru bs) URen.nil).map .opened
/-- Rename a computation. -/
def Comp.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KRen Φ Φ' → URen Γ Γ' →
    {τ : Ty ks} → Comp Δ Φ Γ τ → Option (Comp Δ Φ' Γ' τ)
  | _, _, _, _, rk, ru, _, .app f a h => do
      let f ← f.rename rk ru
      let a ← a.rename rk ru
      pure (.app f a h)
  | _, _, _, _, rk, ru, _, .share n => (n.rename rk ru).map .share
  | _, _, _, _, rk, ru, _, .nat_rec n z s h => do
      let n ← n.rename rk ru
      let z ← z.rename rk ru
      let s ← s.rename rk ru
      pure (.nat_rec n z s h)
  | _, _, _, _, rk, ru, _, .array_foldl a z s h => do
      let a ← a.rename rk ru
      let z ← z.rename rk ru
      let s ← s.rename rk ru
      pure (.array_foldl a z s h)
  | _, _, _, _, rk, ru, _, .data_rec b ρ us brs j e h => do
      let brs ← Fin.optAll (fun i => (brs i).rename rk ru)
      let e ← e.rename rk ru
      pure (.data_rec b ρ us brs j e h)
  | _, _, _, _, rk, ru, _, .data_brec b ρ k us brs j e h => do
      let brs ← Fin.optAll (fun i => (brs i).rename rk ru)
      let e ← e.rename rk ru
      pure (.data_brec b ρ k us brs j e h)
  | _, _, _, _, rk, ru, _, .thunk_force e => (e.rename rk ru).map .thunk_force
  | _, _, _, _, rk, ru, _, .lazy_force e => (e.rename rk ru).map .lazy_force
/-- Rename a statement. -/
def Term.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} → KRen Φ Φ' →
    URen Γ Γ' → URen js js' → {τ : Ty ks} → Term Δ Φ Γ τ js → Option (Term Δ Φ' Γ' τ js')
  | _, _, _, _, _, _, rk, ru, _, _, .ret e => (e.rename rk ru).map .ret
  | _, _, _, _, _, _, rk, ru, rj, _, .letV u v b => do
      let v ← v.rename rk ru
      let b ← b.rename (KRen.lift rk _) ru rj
      pure (.letV u v b)
  | _, _, _, _, _, _, rk, ru, rj, _, .letE u c b => do
      let c ← c.rename rk ru
      let b ← b.rename rk (URen.lift ru _) rj
      pure (.letE u c b)
  | _, _, _, _, _, _, rk, ru, rj, _, .record_casesOn us n b => do
      let n ← n.rename rk ru
      let b ← b.rename rk (URen.liftN ru _) rj
      pure (.record_casesOn us n b)
  | _, _, _, _, _, _, rk, ru, rj, _, .branch br => (br.rename rk ru rj).map .branch
  | _, _, _, _, _, _, rk, ru, rj, _, .jump j e => do
      let j ← rj j
      let e ← e.rename rk ru
      pure (.jump j e)
/-- Rename a branch. -/
def Branch.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} → KRen Φ Φ' →
    URen Γ Γ' → URen js js' → {τ : Ty ks} → Branch Δ Φ Γ τ js → Option (Branch Δ Φ' Γ' τ js')
  | _, _, _, _, _, _, rk, ru, rj, _, .ite c t e => do
      let c ← c.rename rk ru
      let t ← t.rename rk ru rj
      let e ← e.rename rk ru rj
      pure (.ite c t e)
  | _, _, _, _, _, _, rk, ru, rj, _, .enum_casesOn e bs => do
      let e ← e.rename rk ru
      let bs ← Fin.optAll (fun i => (bs i).rename rk ru rj)
      pure (.enum_casesOn e bs)
  | _, _, _, _, _, _, rk, ru, rj, _, .union_casesOn e bs => do
      let e ← e.rename rk ru
      let bs ← bs.rename rk ru rj
      pure (.union_casesOn e bs)
  | _, _, _, _, _, _, rk, ru, rj, _, .join σ u uₓ body main => do
      let body ← body.rename rk (URen.lift ru _) rj
      let main ← main.rename rk ru (URen.lift rj _)
      pure (.join σ u uₓ body main)
/-- Rename the branches of a union's case analysis. -/
def Branches.rename : {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : UCtx ks} → KRen Φ Φ' →
    URen Γ Γ' → URen js js' → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    Branches Δ Φ Γ cs τ js → Option (Branches Δ Φ' Γ' cs τ js')
  | _, _, _, _, _, _, rk, ru, rj, _, _, _, .two us₁ us₂ b₁ b₂ => do
      let b₁ ← b₁.rename rk (URen.liftN ru _) rj
      let b₂ ← b₂.rename rk (URen.liftN ru _) rj
      pure (.two us₁ us₂ b₁ b₂)
  | _, _, _, _, _, _, rk, ru, rj, _, _, _, .cons us b bs => do
      let b ← b.rename rk (URen.liftN ru _) rj
      let bs ← bs.rename rk ru rj
      pure (.cons us b bs)
end

end Rename

end LeanScript.NTerm

end
