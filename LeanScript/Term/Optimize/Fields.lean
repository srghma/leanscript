module

public import LeanScript.Term.Optimize.Reannot

@[expose] public section

set_option autoImplicit false

/-!
# Known fields: taking a record apart once

`let ⟨a, b⟩ := x; …; let ⟨c, d⟩ := x; body`: the second case analysis takes apart a record
that is already taken apart, and its fields are `a` and `b`.  This file removes such repeated
case analyses:

* `FieldVars Γ d ts`: for each field of a record (of types `ts`), the unknown of `Γ` that holds
  it, if any (a field bound with usage `0` has none);
* `RecFact Γ d`: an unknown `x` of record type together with the unknowns holding its fields.
  It *holds* in an environment (`RecFact.Holds`) when those unknowns hold the fields of the
  value of `x`;
* `Term.widenFields`: every record case analysis binds all its fields (usage `ω`, so each field
  has an unknown); `Term.dce` counts the usages again afterwards;
* `Term.reuseFields facts`: walks a statement with the facts known to hold; a case analysis of
  an unknown `x` records the fact that its fields hold the fields of `x`, and a case analysis of
  an unknown whose fields are known is dropped, its fields renamed to the known ones
  (`FieldVars.toRen`).  As for the other rewrites, this is done only when it keeps the level of
  the statement.

Both walks keep the value (`Term.widenFields_eval`, `Term.reuseFields_eval`); the facts are
only carried at one depth (a body starts with none).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Variables weakened under binders -/

/-- A variable of `Γ`, seen under the binders `bs`. -/
def UVar.weakenN {Γ : UCtx ks} : (bs : UCtx ks) → {τ : Ty ks} → {ℓ : Nat} → UVar Γ τ ℓ →
    UVar (bs ++ Γ) τ ℓ
  | [], _, _, x => x
  | _ :: bs, _, _, x => .tail (UVar.weakenN bs x)

@[simp] theorem UEnv.get_tail {Γ : UCtx ks} {b : UBinder ks} {τ : Ty ks} {ℓ : Nat}
    (v : Ty.Den Δ b.ty) (ρ : UEnv Δ Γ) (x : UVar Γ τ ℓ) :
    UEnv.get (Tuple.cons (F := fun b : UBinder ks => Ty.Den Δ b.ty) v ρ) (UVar.tail x) =
      ρ.get x := by
  simp

theorem UEnv.get_weakenN {Γ : UCtx ks} (ρ : UEnv Δ Γ) : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    {τ : Ty ks} → {ℓ : Nat} → (x : UVar Γ τ ℓ) →
    UEnv.get (Tuple.append vs ρ) (UVar.weakenN bs x) = ρ.get x
  | [], _, _, _, _ => rfl
  | _ :: bs, vs, _, _, x => by
      rw [Tuple.append_cons]
      simp only [UVar.weakenN, UEnv.get_tail]
      exact UEnv.get_weakenN ρ bs vs.tail x

theorem UVar.ext_index : {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} → (x y : UVar Γ τ ℓ) →
    x.index = y.index → x = y
  | _, _, _, .head _, .head _, _ => rfl
  | _, _, _, .tail x, .tail y, h => by
      rw [UVar.ext_index x y (by simpa [UVar.index] using h)]
  | _, _, _, .head _, .tail _, h => by simp [UVar.index] at h
  | _, _, _, .tail _, .head _, h => by simp [UVar.index] at h

theorem UEnv.get_ofDL_nil_head {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (v : DenList (DSig.refDen Δ) (t :: ts)) (h : Usage01ω.many ≠ .zero) :
    UEnv.get (Γ := UCtx.annot d (t :: ts) [] ++ Γ) (Tuple.append (UEnv.ofDL d (t :: ts) [] v) ρ)
      (UVar.head h) = v.head := by
  show UEnv.get (Γ := ⟨t, .many, d⟩ :: (UCtx.annot d ts [] ++ Γ))
    (Tuple.append (UEnv.ofDL d (t :: ts) [] v) ρ) (UVar.head h) = v.head
  rw [UEnv.append_ofDL_nil]; simp

theorem UEnv.get_ofDL_cons_head {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (u : Usage01ω) (us : List Usage01ω)
    (v : DenList (DSig.refDen Δ) (t :: ts)) (h : u ≠ .zero) :
    UEnv.get (Γ := UCtx.annot d (t :: ts) (u :: us) ++ Γ)
      (Tuple.append (UEnv.ofDL d (t :: ts) (u :: us) v) ρ) (UVar.head h) = v.head := by
  show UEnv.get (Γ := ⟨t, u, d⟩ :: (UCtx.annot d ts us ++ Γ))
    (Tuple.append (UEnv.ofDL d (t :: ts) (u :: us) v) ρ) (UVar.head h) = v.head
  rw [UEnv.append_ofDL_cons]; simp

theorem UEnv.get_ofDL_nil_tail {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (v : DenList (DSig.refDen Δ) (t :: ts)) {τ : Ty ks} {ℓ : Nat}
    (y : UVar (UCtx.annot d ts [] ++ Γ) τ ℓ) :
    UEnv.get (Γ := UCtx.annot d (t :: ts) [] ++ Γ) (Tuple.append (UEnv.ofDL d (t :: ts) [] v) ρ)
      (UVar.tail (b := ⟨t, .many, d⟩) y) =
      UEnv.get (Tuple.append (UEnv.ofDL d ts [] v.tail) ρ) y := by
  show UEnv.get (Γ := ⟨t, .many, d⟩ :: (UCtx.annot d ts [] ++ Γ))
    (Tuple.append (UEnv.ofDL d (t :: ts) [] v) ρ) (UVar.tail y) = _
  rw [UEnv.append_ofDL_nil]; simp

theorem UEnv.get_ofDL_cons_tail {Γ : UCtx ks} (ρ : UEnv Δ Γ) (d : Nat) (t : Ty ks)
    (ts : List (Ty ks)) (u : Usage01ω) (us : List Usage01ω)
    (v : DenList (DSig.refDen Δ) (t :: ts)) {τ : Ty ks} {ℓ : Nat}
    (y : UVar (UCtx.annot d ts us ++ Γ) τ ℓ) :
    UEnv.get (Γ := UCtx.annot d (t :: ts) (u :: us) ++ Γ)
      (Tuple.append (UEnv.ofDL d (t :: ts) (u :: us) v) ρ) (UVar.tail (b := ⟨t, u, d⟩) y) =
      UEnv.get (Tuple.append (UEnv.ofDL d ts us v.tail) ρ) y := by
  show UEnv.get (Γ := ⟨t, u, d⟩ :: (UCtx.annot d ts us ++ Γ))
    (Tuple.append (UEnv.ofDL d (t :: ts) (u :: us) v) ρ) (UVar.tail y) = _
  rw [UEnv.append_ofDL_cons]; simp

/-! ## The unknowns holding the fields of a record -/

/-- For each field (of type in `ts`), the unknown of `Γ`, bound at level `d`, that holds it. -/
inductive FieldVars (Γ : UCtx ks) (d : Nat) : List (Ty ks) → Type where
  | nil : FieldVars Γ d []
  | cons {t : Ty ks} {ts : List (Ty ks)} : Option (UVar Γ t d) → FieldVars Γ d ts →
      FieldVars Γ d (t :: ts)

namespace FieldVars

variable {Γ : UCtx ks} {d : Nat}

/-- Under one more binder. -/
def weaken (b : UBinder ks) : {ts : List (Ty ks)} → FieldVars Γ d ts → FieldVars (b :: Γ) d ts
  | _, .nil => .nil
  | _, .cons o fv => .cons (o.map .tail) (fv.weaken b)

/-- Under the binders `bs`. -/
def weakenN : (bs : UCtx ks) → {ts : List (Ty ks)} → FieldVars Γ d ts →
    FieldVars (bs ++ Γ) d ts
  | [], _, fv => fv
  | b :: bs, _, fv => (fv.weakenN bs).weaken b

/-- The fields bound by a case analysis (with usages `us`): the ones not annotated `0`. -/
def ofAnnot (Γ : UCtx ks) (d : Nat) : (ts : List (Ty ks)) → (us : List Usage01ω) →
    FieldVars (UCtx.annot d ts us ++ Γ) d ts
  | [], _ => .nil
  | _ :: ts, [] => .cons (some (.head (by decide))) ((ofAnnot Γ d ts []).weaken _)
  | _ :: ts, u :: us =>
      .cons (if h : u = .zero then none else some (.head h)) ((ofAnnot Γ d ts us).weaken _)

/-- The renaming that maps the fields bound by a second case analysis (with usages `us`) to the
    known ones, and leaves the rest alone. -/
def toRen : {ts : List (Ty ks)} → FieldVars Γ d ts → (us : List Usage01ω) →
    URen (UCtx.annot d ts us ++ Γ) Γ
  | [], .nil, _, _, _, x => some x
  | _ :: _, .cons o _, [], _, _, .head _ => o
  | _ :: _, .cons _ fv, [], _, _, .tail y => fv.toRen [] y
  | _ :: _, .cons o _, _ :: _, _, _, .head _ => o
  | _ :: _, .cons _ fv, _ :: us, _, _, .tail y => fv.toRen us y

/-- The unknowns hold the values `v` of the fields. -/
def Holds : {ts : List (Ty ks)} → FieldVars Γ d ts → UEnv Δ Γ → DenList (DSig.refDen Δ) ts →
    Prop
  | [], .nil, _, _ => True
  | _ :: _, .cons o fv, ρ, v => (∀ z, o = some z → ρ.get z = v.head) ∧ fv.Holds ρ v.tail

theorem Holds.weaken {b : UBinder ks} (x : Ty.Den Δ b.ty) {ρ : UEnv Δ Γ} :
    {ts : List (Ty ks)} → (fv : FieldVars Γ d ts) → (v : DenList (DSig.refDen Δ) ts) →
    fv.Holds ρ v → (fv.weaken b).Holds (Tuple.cons x ρ) v
  | [], .nil, _, _ => trivial
  | _ :: _, .cons o fv, v, h => by
      obtain ⟨h₁, h₂⟩ := h
      refine ⟨?_, Holds.weaken x fv v.tail h₂⟩
      intro z hz
      cases o with
      | none => cases hz
      | some y =>
          simp only [Option.map_some, Option.some.injEq] at hz
          subst hz
          simp [h₁ y rfl]

theorem Holds.weakenN {ρ : UEnv Δ Γ} : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    {ts : List (Ty ks)} → (fv : FieldVars Γ d ts) → (v : DenList (DSig.refDen Δ) ts) →
    fv.Holds ρ v → (fv.weakenN bs).Holds (Tuple.append vs ρ) v
  | [], _, _, _, _, h => h
  | _ :: bs, vs, _, fv, v, h => by
      rw [Tuple.append_cons]
      exact Holds.weaken _ _ v (Holds.weakenN bs vs.tail fv v h)

/-- The fields a case analysis binds hold the fields of its scrutinee. -/
theorem Holds.ofAnnot (ρ : UEnv Δ Γ) (d : Nat) : (ts : List (Ty ks)) → (us : List Usage01ω) →
    (v : DenList (DSig.refDen Δ) ts) →
    (FieldVars.ofAnnot Γ d ts us).Holds (Tuple.append (UEnv.ofDL d ts us v) ρ) v
  | [], _, _ => trivial
  | t :: ts, [], v => by
      have hw := Holds.weaken (b := ⟨t, .many, d⟩) v.head _ v.tail (Holds.ofAnnot ρ d ts [] v.tail)
      rw [← UEnv.append_ofDL_nil] at hw
      refine ⟨?_, hw⟩
      intro z hz
      cases hz
      exact UEnv.get_ofDL_nil_head ρ d t ts v _
  | t :: ts, u :: us, v => by
      have hw := Holds.weaken (b := ⟨t, u, d⟩) v.head _ v.tail (Holds.ofAnnot ρ d ts us v.tail)
      rw [← UEnv.append_ofDL_cons] at hw
      refine ⟨?_, hw⟩
      intro z hz
      split at hz
      · cases hz
      · cases hz
        exact UEnv.get_ofDL_cons_head ρ d t ts u us v _

/-- Renaming the fields of a second case analysis to the known ones keeps the value. -/
theorem Holds.agree {ρ : UEnv Δ Γ} : {ts : List (Ty ks)} → (fv : FieldVars Γ d ts) →
    (v : DenList (DSig.refDen Δ) ts) → fv.Holds ρ v → (us : List Usage01ω) →
    URen.Agree (fv.toRen us) (Tuple.append (UEnv.ofDL d ts us v) ρ) ρ
  | [], .nil, _, _, _ => by
      intro x y h
      simp only [FieldVars.toRen] at h
      cases h; rfl
  | _ :: _, .cons o fv, v, h, [] => by
      obtain ⟨h₁, h₂⟩ := h
      intro x y h
      cases x with
      | head hu =>
          simp only [FieldVars.toRen] at h
          rw [h₁ y h, UEnv.get_ofDL_nil_head ρ d _ _ v hu]
      | tail x =>
          simp only [FieldVars.toRen] at h
          rw [Holds.agree fv v.tail h₂ [] x y h, UEnv.get_ofDL_nil_tail ρ d _ _ v x]
  | _ :: _, .cons o fv, v, h, u :: us => by
      obtain ⟨h₁, h₂⟩ := h
      intro x y h
      cases x with
      | head hu =>
          simp only [FieldVars.toRen] at h
          rw [h₁ y h, UEnv.get_ofDL_cons_head ρ d _ _ u us v hu]
      | tail x =>
          simp only [FieldVars.toRen] at h
          rw [Holds.agree fv v.tail h₂ us x y h, UEnv.get_ofDL_cons_tail ρ d _ _ u us v x]

end FieldVars

/-! ## Facts: an unknown record and the unknowns holding its fields -/

/-- The values of the fields of a record, as the case analysis binds them. -/
def recordFields {t : Ty ks} {fs : Fields ks} (r : Ty.Den Δ (.record t fs)) :
    DenList (DSig.refDen Δ) (t :: fs.toList) :=
  Tuple.cons r.1 (Fields.toDL fs r.2)

/-- The unknown `x`, a record, has its fields in the unknowns `fv`. -/
structure RecFact (Γ : UCtx ks) (d : Nat) where
  {t : Ty ks}
  {fs : Fields ks}
  {ℓ : Nat}
  x : UVar Γ (.record t fs) ℓ
  fv : FieldVars Γ d (t :: fs.toList)

namespace RecFact

variable {Γ : UCtx ks} {d : Nat}

/-- The fact holds in an environment. -/
def Holds (f : RecFact Γ d) (ρ : UEnv Δ Γ) : Prop :=
  f.fv.Holds ρ (recordFields (ρ.get f.x))

/-- Under one more binder. -/
def weaken (b : UBinder ks) (f : RecFact Γ d) : RecFact (b :: Γ) d :=
  ⟨f.x.tail, f.fv.weaken b⟩

/-- Under the binders `bs`. -/
def weakenN (bs : UCtx ks) (f : RecFact Γ d) : RecFact (bs ++ Γ) d :=
  ⟨f.x.weakenN bs, f.fv.weakenN bs⟩

theorem Holds.weaken {b : UBinder ks} (v : Ty.Den Δ b.ty) {ρ : UEnv Δ Γ} {f : RecFact Γ d}
    (h : f.Holds ρ) : (f.weaken b).Holds (Tuple.cons v ρ) := by
  unfold RecFact.Holds RecFact.weaken
  simp only [UEnv.get_tail]
  exact FieldVars.Holds.weaken v _ _ h

theorem Holds.weakenN (bs : UCtx ks) (vs : UEnv Δ bs) {ρ : UEnv Δ Γ} {f : RecFact Γ d}
    (h : f.Holds ρ) : (f.weakenN bs).Holds (Tuple.append vs ρ) := by
  unfold RecFact.Holds RecFact.weakenN
  simp only [UEnv.get_weakenN]
  exact FieldVars.Holds.weakenN bs vs _ _ h

/-- The known fields of the unknown `y`, if the fact is about `y`. -/
def match? (f : RecFact Γ d) {t : Ty ks} {fs : Fields ks} {ℓ : Nat}
    (y : UVar Γ (.record t fs) ℓ) : Option (FieldVars Γ d (t :: fs.toList)) :=
  match f with
  | @RecFact.mk _ _ _ t' fs' ℓ' x fv =>
    if h : t' = t ∧ fs' = fs ∧ ℓ' = ℓ then
      if x.index = y.index then some (h.1 ▸ h.2.1 ▸ fv) else none
    else none

theorem match?_holds {f : RecFact Γ d} {ρ : UEnv Δ Γ} (hf : f.Holds ρ) {t : Ty ks}
    {fs : Fields ks} {ℓ : Nat} {y : UVar Γ (.record t fs) ℓ}
    {fv : FieldVars Γ d (t :: fs.toList)} (h : f.match? y = some fv) :
    fv.Holds ρ (recordFields (ρ.get y)) := by
  obtain ⟨x, fv'⟩ := f
  simp only [match?] at h
  split at h
  · rename_i hty
    obtain ⟨rfl, rfl, rfl⟩ := hty
    split at h
    · rename_i hi
      simp only [Option.some.injEq] at h
      subst h
      rw [← UVar.ext_index x y hi]
      exact hf
    · cases h
  · cases h

/-- The known fields of `y`, from the first fact about it. -/
def find? : List (RecFact Γ d) → {t : Ty ks} → {fs : Fields ks} → {ℓ : Nat} →
    UVar Γ (.record t fs) ℓ → Option (FieldVars Γ d (t :: fs.toList))
  | [], _, _, _, _ => none
  | f :: facts, _, _, _, y =>
    match f.match? y with
    | some fv => some fv
    | none => find? facts y

theorem find?_holds {ρ : UEnv Δ Γ} : (facts : List (RecFact Γ d)) →
    (∀ f ∈ facts, f.Holds ρ) → {t : Ty ks} → {fs : Fields ks} → {ℓ : Nat} →
    {y : UVar Γ (.record t fs) ℓ} → {fv : FieldVars Γ d (t :: fs.toList)} →
    find? facts y = some fv → fv.Holds ρ (recordFields (ρ.get y))
  | [], _, _, _, _, _, _, h => by cases h
  | f :: facts, hs, _, _, _, y, fv, h => by
      simp only [find?] at h
      split at h
      · rename_i fv' hm
        simp only [Option.some.injEq] at h
        subst h
        exact match?_holds (hs f (List.mem_cons_self)) hm
      · exact find?_holds facts (fun g hg => hs g (List.mem_cons_of_mem _ hg)) h

end RecFact

end LeanScript

end
