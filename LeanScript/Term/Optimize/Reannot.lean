module

public import LeanScript.Term.Rename.Eval
public import LeanScript.Term.Optimize.Occ

@[expose] public section

set_option autoImplicit false

/-!
# Re-annotating the fields a case analysis binds

A case analysis (`Term.record_casesOn`, the branches of `Branch.union_casesOn`) binds the
fields of its scrutinee with usages `us` (`UCtx.annot d ts us`).  `URen.reannot d ts us us'`
is the partial renaming that changes those usages to `us'`: a field keeps its position, and a
field re-annotated `0` has no image (a statement mentioning it cannot be renamed).  The fields
hold the same values whatever their usages (`URen.Agree.reannot`), so renaming along it
preserves the value (`Term.rename_eval`).

`Term.countFields t n` counts the usages of the `n` innermost unknowns of `t`: what the fields
of a case analysis should be annotated with.  `Term.dce` uses both, so that a field that is
never read is annotated `0` (and not taken out of the scrutinee by the JavaScript backend).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- Change the usage of the innermost binder to `u'`, and rename the others along `r`. -/
def URen.reannotHead {Γ Γ' : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat} (u' : Usage01ω)
    (r : URen Γ Γ') : URen (⟨σ, u, ℓ⟩ :: Γ) (⟨σ, u', ℓ⟩ :: Γ')
  | _, _, .head _ => if h : u' = .zero then none else some (.head h)
  | _, _, .tail x => (r x).map .tail

/-- Change the usages of the fields bound by a case analysis from `us` to `us'`. -/
def URen.reannot {Γ : UCtx ks} (d : Nat) : (ts : List (Ty ks)) → (us us' : List Usage01ω) →
    URen (UCtx.annot d ts us ++ Γ) (UCtx.annot d ts us' ++ Γ)
  | [], _, _ => URen.id
  | _ :: ts, [], [] => URen.reannotHead .many (URen.reannot d ts [] [])
  | _ :: ts, [], u' :: us' => URen.reannotHead u' (URen.reannot d ts [] us')
  | _ :: ts, _ :: us, [] => URen.reannotHead .many (URen.reannot d ts us [])
  | _ :: ts, _ :: us, u' :: us' => URen.reannotHead u' (URen.reannot d ts us us')

theorem URen.Agree.reannotHead {Γ Γ' : UCtx ks} {σ : Ty ks} {u : Usage01ω} {ℓ : Nat}
    (u' : Usage01ω) {r : URen Γ Γ'} {ρ : UEnv Δ Γ} {ρ' : UEnv Δ Γ'} (h : URen.Agree r ρ ρ')
    (v : Ty.Den Δ σ) :
    URen.Agree (URen.reannotHead (σ := σ) (u := u) (ℓ := ℓ) u' r) (Tuple.cons v ρ)
      (Tuple.cons v ρ') := by
  intro _ _ x y hxy
  cases x with
  | head _ =>
      simp only [URen.reannotHead] at hxy
      split at hxy
      · cases hxy
      · simp only [Option.some.injEq] at hxy; subst hxy; simp
  | tail x =>
      simp only [URen.reannotHead, Option.map_eq_some_iff] at hxy
      obtain ⟨z, hz, rfl⟩ := hxy
      simp [h x z hz]

theorem UEnv.append_ofDL_nil {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (v : DenList (DSig.refDen Δ) (t :: ts)) :
    (Tuple.append (UEnv.ofDL d (t :: ts) [] v) ρ : UEnv Δ (UCtx.annot d (t :: ts) [] ++ Γ)) =
      Tuple.cons (F := fun b : UBinder ks => Ty.Den Δ b.ty) (a := ⟨t, .many, d⟩) v.head
        (Tuple.append (UEnv.ofDL d ts [] v.tail) ρ) := by
  show Tuple.append (Tuple.cons (F := fun b : UBinder ks => Ty.Den Δ b.ty) (a := ⟨t, .many, d⟩)
    v.head (UEnv.ofDL d ts [] v.tail)) ρ = _
  rw [Tuple.append_cons, Tuple.head_cons, Tuple.tail_cons]

theorem UEnv.append_ofDL_cons {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (u : Usage01ω) (us : List Usage01ω) (v : DenList (DSig.refDen Δ) (t :: ts)) :
    (Tuple.append (UEnv.ofDL d (t :: ts) (u :: us) v) ρ :
        UEnv Δ (UCtx.annot d (t :: ts) (u :: us) ++ Γ)) =
      Tuple.cons (F := fun b : UBinder ks => Ty.Den Δ b.ty) (a := ⟨t, u, d⟩) v.head
        (Tuple.append (UEnv.ofDL d ts us v.tail) ρ) := by
  show Tuple.append (Tuple.cons (F := fun b : UBinder ks => Ty.Den Δ b.ty) (a := ⟨t, u, d⟩)
    v.head (UEnv.ofDL d ts us v.tail)) ρ = _
  rw [Tuple.append_cons, Tuple.head_cons, Tuple.tail_cons]

/-- The fields hold the same values whatever their usages. -/
theorem URen.Agree.reannot {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) :
    (ts : List (Ty ks)) → (us us' : List Usage01ω) → (v : DenList (DSig.refDen Δ) ts) →
    URen.Agree (URen.reannot (Γ := Γ) d ts us us') (Tuple.append (UEnv.ofDL d ts us v) ρ)
      (Tuple.append (UEnv.ofDL d ts us' v) ρ)
  | [], _, _, _ => URen.Agree.id _
  | _ :: ts, [], [], v => by
      rw [UEnv.append_ofDL_nil]
      intro x y h
      exact URen.Agree.reannotHead (u := .many) (ℓ := d) .many (URen.Agree.reannot ρ d ts [] [] v.tail)
        v.head x y h
  | _ :: ts, [], u' :: us', v => by
      rw [UEnv.append_ofDL_nil, UEnv.append_ofDL_cons]
      intro x y h
      exact URen.Agree.reannotHead (u := .many) (ℓ := d) u' (URen.Agree.reannot ρ d ts [] us' v.tail)
        v.head x y h
  | _ :: ts, u :: us, [], v => by
      rw [UEnv.append_ofDL_cons, UEnv.append_ofDL_nil]
      intro x y h
      exact URen.Agree.reannotHead (u := u) (ℓ := d) .many (URen.Agree.reannot ρ d ts us [] v.tail)
        v.head x y h
  | _ :: ts, u :: us, u' :: us', v => by
      rw [UEnv.append_ofDL_cons, UEnv.append_ofDL_cons]
      intro x y h
      exact URen.Agree.reannotHead (u := u) (ℓ := d) u' (URen.Agree.reannot ρ d ts us us' v.tail)
        v.head x y h

/-- The usages of the `n` innermost unknowns of a statement. -/
def Term.countFields {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) (n : Nat) : List Usage01ω :=
  (List.range n).map t.countU

end LeanScript

end
