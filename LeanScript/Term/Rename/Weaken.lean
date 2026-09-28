module

public import LeanScript.Term.Syntax.Term

@[expose] public section

set_option autoImplicit false

/-!
# Thinnings: total weakening of pure expressions

A thinning `Thin xs ys` embeds the list `xs` into `ys` in order (`ys` has extra entries).
Weakening a pure expression along thinnings of its two contexts always succeeds
(`PExpr.thin`), unlike the partial renamings of `LeanScript.Term.Rename.Basic`.

A **closed** pure expression mentions no unknown and only closed known values, so it can be
moved into any context of unknowns and into the closed view of the known context
(`PExpr.toClosed`): this is how a closed value enters a closed body.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- An order-preserving embedding of `xs` into `ys`. -/
inductive Thin {α : Type} : List α → List α → Type where
  | nil : Thin [] []
  | keep {x : α} {xs ys : List α} : Thin xs ys → Thin (x :: xs) (x :: ys)
  | skip {y : α} {xs ys : List α} : Thin xs ys → Thin xs (y :: ys)

namespace Thin
variable {α : Type}

/-- The identity. -/
def id : (xs : List α) → Thin xs xs
  | [] => .nil
  | _ :: xs => .keep (id xs)

/-- One more innermost entry. -/
def wk1 {xs : List α} {y : α} : Thin xs (y :: xs) := .skip (id xs)

/-- Under more binders. -/
def keepN {xs ys : List α} (θ : Thin xs ys) : (zs : List α) → Thin (zs ++ xs) (zs ++ ys)
  | [] => θ
  | _ :: zs => .keep (θ.keepN zs)

/-- Composition. -/
def comp : {xs ys zs : List α} → Thin xs ys → Thin ys zs → Thin xs zs
  | _, _, _, θ, .skip η => .skip (comp θ η)
  | _, _, _, .keep θ, .keep η => .keep (comp θ η)
  | _, _, _, .skip θ, .keep η => .skip (comp θ η)
  | _, _, _, .nil, .nil => .nil

end Thin

/-- A thinning of known contexts, seen from closed bodies. -/
def Thin.closedOnly : {Φ Φ' : KCtx ks} → Thin Φ Φ' → Thin (KCtx.closedOnly Φ) (KCtx.closedOnly Φ')
  | _, _, .nil => .nil
  | ⟨_, _, some _, _⟩ :: _, _, .keep θ => .keep θ.closedOnly
  | ⟨_, _, none, _⟩ :: _, _, .keep θ => .keep θ.closedOnly
  | _, ⟨_, _, some _, _⟩ :: _, .skip θ => .skip θ.closedOnly
  | _, ⟨_, _, none, _⟩ :: _, .skip θ => .skip θ.closedOnly

/-- Weaken an unknown. -/
def UVar.thin : {Γ Γ' : UCtx ks} → Thin Γ Γ' → {τ : Ty ks} → {ℓ : Nat} → UVar Γ τ ℓ → UVar Γ' τ ℓ
  | _, _, .keep _, _, _, .head h => .head h
  | _, _, .keep θ, _, _, .tail x => .tail (x.thin θ)
  | _, _, .skip θ, _, _, x => .tail (x.thin θ)

/-- Weaken a known variable. -/
def KVar.thin : {Φ Φ' : KCtx ks} → Thin Φ Φ' → {τ : Ty ks} → {o : Lvl} → KVar Φ τ o → KVar Φ' τ o
  | _, _, .keep _, _, _, .head => .head
  | _, _, .keep θ, _, _, .tail x => .tail (x.thin θ)
  | _, _, .skip θ, _, _, x => .tail (x.thin θ)

/-- A closed known variable, in the closed view. -/
def KVar.toClosed : {Φ : KCtx ks} → {τ : Ty ks} → KVar Φ τ none → KVar (KCtx.closedOnly Φ) τ none
  | ⟨_, _, none, _⟩ :: _, _, .head => .head
  | ⟨_, _, some _, _⟩ :: _, _, .tail x => .tail x.toClosed
  | ⟨_, _, none, _⟩ :: _, _, .tail x => .tail x.toClosed

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks}

mutual
/-- Weaken a neutral expression. -/
def Neu.thin (θk : Thin Φ Φ') (θu : Thin Γ Γ') : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Neu Δ Φ' Γ' τ ℓ
  | _, _,  .var x => .var (x.thin θu)
  | _, _,  .data_out b j n => .data_out b j (n.thin θk θu)
  | _, _,  .cond c a b => .cond (c.thin θk θu) (a.thin θk θu) (b.thin θk θu)
  | _, _,  .extern e args h => .extern e (args.thin θk θu) h
/-- Weaken a pure expression. -/
def PExpr.thin (θk : Thin Φ Φ') (θu : Thin Γ Γ') :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → PExpr Δ Φ' Γ' τ o
  | _, _, .neu n => .neu (n.thin θk θu)
  | _, _, .kvar k => .kvar (k.thin θk)
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk (args.thin θk θu)
  | _, _, .union_mk ix args => .union_mk ix (args.thin θk θu)
  | _, _, .array_mk es => .array_mk (es.thin θk θu)
  | _, _, .list_mk es => .list_mk (es.thin θk θu)
  | _, _, .data_in b j e => .data_in b j (e.thin θk θu)
/-- Weaken arguments. -/
def Args.thin (θk : Thin Φ Φ') (θu : Thin Γ Γ') :
    {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Args Δ Φ' Γ' σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons (a.thin θk θu) (as.thin θk θu)
/-- Weaken elements. -/
def Elems.thin (θk : Thin Φ Φ') (θu : Thin Γ Γ') :
    {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Elems Δ Φ' Γ' t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons (e.thin θk θu) (es.thin θk θu)
end

mutual
/-- A closed pure expression in any context of unknowns and in the closed view of the known
    values. -/
def PExpr.toClosed : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → o = none →
    PExpr Δ (KCtx.closedOnly Φ) Γ' τ none
  | _, _, .neu _, h => nomatch h
  | _, _, .kvar k, h => .kvar (h ▸ k).toClosed
  | _, _, .lit p v, _ => .lit p v
  | _, _, .enum_mk s i, _ => .enum_mk s i
  | _, _, .record_mk args, h => .record_mk (args.toClosed h)
  | _, _, .union_mk ix args, h => .union_mk ix (args.toClosed h)
  | _, _, .array_mk es, h => .array_mk (es.toClosed h)
  | _, _, .list_mk es, h => .list_mk (es.toClosed h)
  | _, _, .data_in b j e, h => .data_in b j (e.toClosed h)
/-- Closed arguments, moved. -/
def Args.toClosed : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → o = none →
    Args Δ (KCtx.closedOnly Φ) Γ' σs none
  | _, _, .nil, _ => .nil
  | _, _, .cons a as, h =>
      .cons (a.toClosed ((Lvl.meet_eq_none _ _).mp h).1) (as.toClosed ((Lvl.meet_eq_none _ _).mp h).2)
/-- Closed elements, moved. -/
def Elems.toClosed : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → o = none →
    Elems Δ (KCtx.closedOnly Φ) Γ' t none
  | _, _, .nil, _ => .nil
  | _, _, .cons e es, h =>
      .cons (e.toClosed ((Lvl.meet_eq_none _ _).mp h).1) (es.toClosed ((Lvl.meet_eq_none _ _).mp h).2)
end

end Layer1

end LeanScript

end
