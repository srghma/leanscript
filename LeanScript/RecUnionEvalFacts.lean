module

public import LeanScript.Eval
public import LeanScript.RecUnionRecFacts

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# What the evaluator does with a recursive tagged union

The recursive analogue of the facts at the end of `LeanScript.Eval`.

* **ι-rules for a dispatch.**  Taking apart a value built by `Term.recTaggedUnion_mk` is
  taking apart the tagged value of the *unfolded* union with the same constructor and
  fields (`Term.eval_recTaggedUnion_casesOn_mk`,
  `Term.eval_recTaggedUnion_casesOnWithDefault_mk`).  Both rest on the round trip
  `TyWf.DenRec.unfold_mk` (and `Ty.unroll_roll` / `Ty.roll_unroll` below it, in
  `LeanScript.Den.Rec`).
* **The fold, and its ι-rule.**  `TaggedUnionFoldCases.recFold` is the plain fold of the
  branches of `Term.recTaggedUnion_rec` at depth `0`, written with `WType.fold` — no memo
  — and `TaggedUnionFoldCases.recFold_mk` is its equation: the answer at a node is the
  branch of its constructor, evaluated on its fields and, after each field that is
  literally `Ty.self`, the answer of the fold at that field.
* **Depth does not change meaning.**  The evaluator folds by `WType.memo`, remembering
  every answer; `Comp.eval_recTaggedUnion_rec_toFoldK` says that at **every** depth `k`,
  branches that answer where they stand (`TaggedUnionFoldCases.toFoldK`) give exactly
  that plain fold.
-/

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## What the introduction form builds

A dispatch on the introduction form itself is a redex, which the grammar does not have
(`LeanScript.Expr.Usage`); what can be said is what the value it builds holds. -/

/-- The tag of a value built by the introduction form is the constructor it was built
    with. -/
theorem Comp.eval_recTaggedUnion_mk_tag {Γ : Ctx} {u : Usage Γ}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    {ks : List Head}
    (fields : Spine Sg Γ u ((TyWf.recTaggedUnionUnfold l hwf).get t ht) ks)
    (env : Env Γ)
    (h : Comp.NoRecMk (.recTaggedUnion_mk l hwf t ht fields)) :
    (TyWf.DenRec.unfold l hwf (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env h)).1.val
      = t := by
  show (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)).1.val = t
  rw [TyWf.DenRec.unfold_mk]
  rfl

/-- The fields of a value built by the introduction form are the ones it was built with. -/
theorem Comp.eval_recTaggedUnion_field? {Γ : Ctx} {u : Usage Γ}
    (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    {ks : List Head}
    (fields : Spine Sg Γ u ((TyWf.recTaggedUnionUnfold l hwf).get t ht) ks)
    (env : Env Γ)
    (h : Comp.NoRecMk (.recTaggedUnion_mk l hwf t ht fields)) :
    TyWf.DenTU.field? t ht
        (TyWf.DenRec.unfold l hwf (Comp.eval G (.recTaggedUnion_mk l hwf t ht fields) env h)) =
      some (Spine.eval G fields env h) := by
  show TyWf.DenTU.field? t ht (TyWf.DenRec.unfold l hwf (TyWf.DenRec.mk l hwf _)) = _
  rw [TyWf.DenRec.unfold_mk, TyWf.DenTU.field?_mk]

/-! ## The plain fold

The environment of a branch, read off a node whose holes hold each subtree **with** the
answer of the fold at it. -/

/-- The environment a branch of the fold binds, at a constructor with fields `fs`, from
    the fields' shape with a subtree and its answer in each hole. -/
def recBindEnvOf (l : LeanTaggedUnionSchema (TyWfIn 1)) (hwf : Ty.Wf (TyWf.recTaggedUnionTy l))
    (τ : TyWf) :
    (fs : List (TyWfIn 1)) →
      (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj
        (TyWf.Den (TyWf.recTaggedUnion l hwf) × TyWf.Den τ) →
      TyWf.DenList (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ fs)
  | [], _ => PUnit.unit
  | ⟨.self, _⟩ :: fs, e =>
      let p := e.prodFst.2 PUnit.unit
      (p.1, p.2, recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.familyMember i, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.familyMember i) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.shape sh, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.shape sh) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recTaggedUnion l', _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recTaggedUnion l')
          ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recObject r, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recObject r) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.recAlias b, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.recAlias b) ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)
  | ⟨.mutualRecursiveFamily f, _⟩ :: fs, e =>
      (Ty.unroll (TyWf.recTaggedUnionTy l) (Ty.mutualRecursiveFamily f)
          ⟨e.prodFst.1, fun p => (e.prodFst.2 p).1⟩,
        recBindEnvOf l hwf τ fs e.prodSnd)

/-- The environment read off memos is the environment read off each memo's tree and
    answer. -/
theorem recBindEnv_eq_recBindEnvOf (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (τ : TyWf) :
    ∀ (fs : List (TyWfIn 1)) (e : RecFields l τ fs),
      recBindEnv l hwf τ fs e =
        recBindEnvOf l hwf τ fs ⟨e.1, fun p => ((e.2 p).tree, (e.2 p).answer)⟩
  | [], _ => rfl
  | ⟨.self, _⟩ :: fs, e => by
      show (_, _, recBindEnv l hwf τ fs e.prodSnd) = (_, _, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.familyMember _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.shape _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recTaggedUnion _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recObject _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.recAlias _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl
  | ⟨.mutualRecursiveFamily _, _⟩ :: fs, e => by
      show (_, recBindEnv l hwf τ fs e.prodSnd) = (_, recBindEnvOf l hwf τ fs _)
      rw [recBindEnv_eq_recBindEnvOf l hwf τ fs e.prodSnd]; rfl

/-! ### The branches of the plain fold, at a node -/

mutual

/-- The answer of the branches of a plain fold at a node of constructor `t`, whose fields
    are `e` — their shape, with some `Y` in each hole that `mkEnv` turns into the
    environment of the branch.  The hypothesis is the evaluator's, for the same branches
    read at any depth. -/
def TaggedUnionFoldCases.evalAt {Y : Type} {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {k : Nat} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema (TyWfIn 1)} →
    {τ : TyWf} → (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ u l τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAt (recL l) t).Obj Y →
    TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l₀) (k := k) c) →
    TyWf.Den τ
  | _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, 0, e, h =>
      Term.eval G b0 (Env.append (mkEnv _ e) env) h.1
  | _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, 1, e, h =>
      Term.eval G b1 (Env.append (mkEnv _ e) env) h.2.1
  | _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, n + 2, e, h =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e h.2.2
  | _, _, _, _, _, .skip b0 _, env, mkEnv, 0, e, h =>
      Term.eval G b0 (Env.append (mkEnv _ e) env) h.1
  | _, _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldCases.evalAt rest env mkEnv n e h.2

/-- `TaggedUnionFoldCases.evalAt`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadFoldCases.evalAt {Y : Type} {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {k : Nat} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {u : Usage Γ} → {c : CtorsWithPayload (TyWfIn 1)} →
    {τ : TyWf} → (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ u c τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj Y →
    CtorsWithPayloadFoldKCases.NoRecMk
      (CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀) (k := k) cs) →
    TyWf.Den τ
  | _, _, _, _, _, .here b _, env, mkEnv, 0, e, h =>
      Term.eval G b (Env.append (mkEnv _ e) env) h.1
  | _, _, _, _, _, .here _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e h.2
  | _, _, _, _, _, .skip b _, env, mkEnv, 0, e, h =>
      Term.eval G b (Env.append (mkEnv _ e) env) h.1
  | _, _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldCases.evalAt rest env mkEnv n e h.2

/-- `TaggedUnionFoldCases.evalAt`, on a plain list of constructors. -/
def TaggedUnionFoldCasesRest.evalAt {Y : Type} {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}
    {k : Nat} :
    {bind : List (TyWfIn 1) → List TyWf} → {Γ : Ctx} → {u : Usage Γ} → {cs : List (List (TyWfIn 1))} →
    {τ : TyWf} → (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ u cs τ) → Env Γ →
    ((fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs)) →
    (t : Nat) → (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj Y →
    TaggedUnionFoldKCasesRest.NoRecMk
      (TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀) (k := k) r) →
    TyWf.Den τ
  | _, _, _, _, _, .nil, _, _, _, e, _ => PEmpty.elim e.1
  | _, _, _, _, _, .cons b _, env, mkEnv, 0, e, h =>
      Term.eval G b (Env.append (mkEnv _ e) env) h.1
  | _, _, _, _, _, .cons _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldCasesRest.evalAt rest env mkEnv n e h.2

end

/-- **The plain fold** of a value of `recTaggedUnion l`, for branches that answer where
    they stand: the answer at a node is its constructor's branch, evaluated on its fields
    and the answers of the fold at its occurrences.  Written with `WType.fold`, so no
    answer is stored. -/
def TaggedUnionFoldCases.recFold {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {k : Nat}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (env : Env Γ)
    (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l) (k := k) c)) :
    TyWf.Den (TyWf.recTaggedUnion l hwf) → TyWf.Den τ :=
  WType.fold fun node kids ih =>
    TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ) node.1.val
      ⟨node.2, fun p => (kids p, ih p)⟩ h

/-- **The ι-rule of the fold**: the answer at a node is the branch of its constructor,
    evaluated on its fields and, after each field that is literally `Ty.self`, the subtree
    there together with the answer of the fold at it. -/
theorem TaggedUnionFoldCases.recFold_mk {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {k : Nat}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (env : Env Γ)
    (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l) (k := k) c))
    (node : Ty.RecNode (recL l)) (f : Ty.RecHole (recL l) node → TyWf.Den (TyWf.recTaggedUnion l hwf)) :
    TaggedUnionFoldCases.recFold G c env h (WType.mk node f) =
      TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ) node.1.val
        ⟨node.2, fun p => (f p, TaggedUnionFoldCases.recFold G c env h (f p))⟩ h :=
  rfl

/-! ### The evaluator's fold, for branches that answer where they stand -/

section
variable {τ : TyWf} {l₀ : LeanTaggedUnionSchema (TyWfIn 1)}

mutual

/-- The evaluator's answer at a node, for branches that answer where they stand, is the
    answer of those branches read as a plain fold. -/
theorem TaggedUnionFoldKCases.eval_toFoldK {k : Nat} {bind : List (TyWfIn 1) → List TyWf}
    {Γ : Ctx} {u : Usage Γ} {l : LeanTaggedUnionSchema (TyWfIn 1)} :
    ∀ (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ u l τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (t : Nat) (e : (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ))
      (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l₀) (k := k) c)),
      TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK c) env mkEnv t e h =
        TaggedUnionFoldCases.evalAt G c env mkEnv t e h
  | .payloadFirst _ _ _, _, _, 0, _, _ => rfl
  | .payloadFirst _ _ _, _, _, 1, _, _ => rfl
  | .payloadFirst _ _ rest, env, mkEnv, n + 2, e, h =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv n e h.2.2
  | .skip _ _, _, _, 0, _, _ => rfl
  | .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval_toFoldK rest env mkEnv n e h.2

theorem CtorsWithPayloadFoldKCases.eval_toFoldK {k : Nat}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {u : Usage Γ} {c : CtorsWithPayload (TyWfIn 1)} :
    ∀ (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ u c τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (t : Nat) (e : (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ))
      (h : CtorsWithPayloadFoldKCases.NoRecMk
        (CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀) (k := k) cs)),
      CtorsWithPayloadFoldKCases.eval G (CtorsWithPayloadFoldCases.toFoldK cs) env mkEnv t e h =
        CtorsWithPayloadFoldCases.evalAt G cs env mkEnv t e h
  | .here _ _, _, _, 0, _, _ => rfl
  | .here _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv n e h.2
  | .skip _ _, _, _, 0, _, _ => rfl
  | .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval_toFoldK rest env mkEnv n e h.2

theorem TaggedUnionFoldKCasesRest.eval_toFoldK {k : Nat}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {u : Usage Γ} {cs : List (List (TyWfIn 1))} :
    ∀ (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ u cs τ) (env : Env Γ)
      (mkEnv : (fs : List (TyWfIn 1)) → RecFields l₀ τ fs → TyWf.DenList (bind fs))
      (t : Nat) (e : (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ))
      (h : TaggedUnionFoldKCasesRest.NoRecMk
        (TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀) (k := k) r)),
      TaggedUnionFoldKCasesRest.eval G (TaggedUnionFoldCasesRest.toFoldK r) env mkEnv t e h =
        TaggedUnionFoldCasesRest.evalAt G r env mkEnv t e h
  | .nil, _, _, _, e, _ => PEmpty.elim e.1
  | .cons _ _, _, _, 0, _, _ => rfl
  | .cons _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval_toFoldK rest env mkEnv n e h.2

end

end

section
variable {τ : TyWf} {l₀ l₀' : LeanTaggedUnionSchema (TyWfIn 1)} {Y Y' : Type} (g : Y → Y')

mutual

/-- The answer of a plain fold at a node depends on the contents of its holes only
    through the environments they give, and not on the depth its hypothesis is stated
    at. -/
theorem TaggedUnionFoldCases.evalAt_map {k k' : Nat} {bind : List (TyWfIn 1) → List TyWf}
    {Γ : Ctx} {u : Usage Γ} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (c : TaggedUnionFoldCases Sg (TyWfIn 1) bind Γ u l τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAt (recL l) t).Obj Y)
      (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l₀) (k := k) c))
      (h' : TaggedUnionFoldKCases.NoRecMk
        (TaggedUnionFoldCases.toFoldK (l₀ := l₀') (k := k') c)),
      TaggedUnionFoldCases.evalAt G c env mkEnv t e h =
        TaggedUnionFoldCases.evalAt G c env mkEnv' t (PFunctor.map _ g e) h'
  | .payloadFirst b0 _ _, env, 0, e, h, _ => by
      exact congrArg (fun x => Term.eval G b0 (Env.append x env) h.1) (hm _ _)
  | .payloadFirst _ b1 _, env, 1, e, h, _ => by
      exact congrArg (fun x => Term.eval G b1 (Env.append x env) h.2.1) (hm _ _)
  | .payloadFirst _ _ rest, env, n + 2, e, h, h' =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e h.2.2 h'.2.2
  | .skip b0 _, env, 0, e, h, _ => by
      exact congrArg (fun x => Term.eval G b0 (Env.append x env) h.1) (hm _ _)
  | .skip _ rest, env, n + 1, e, h, h' =>
      CtorsWithPayloadFoldCases.evalAt_map mkEnv mkEnv' hm rest env n e h.2 h'.2

theorem CtorsWithPayloadFoldCases.evalAt_map {k k' : Nat}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {u : Usage Γ} {c : CtorsWithPayload (TyWfIn 1)}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (cs : CtorsWithPayloadFoldCases Sg (TyWfIn 1) bind Γ u c τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj Y)
      (h : CtorsWithPayloadFoldKCases.NoRecMk
        (CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀) (k := k) cs))
      (h' : CtorsWithPayloadFoldKCases.NoRecMk
        (CtorsWithPayloadFoldCases.toFoldK (l₀ := l₀') (k := k') cs)),
      CtorsWithPayloadFoldCases.evalAt G cs env mkEnv t e h =
        CtorsWithPayloadFoldCases.evalAt G cs env mkEnv' t (PFunctor.map _ g e) h'
  | .here b _, env, 0, e, h, _ => by
      exact congrArg (fun x => Term.eval G b (Env.append x env) h.1) (hm _ _)
  | .here _ rest, env, n + 1, e, h, h' =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e h.2 h'.2
  | .skip b _, env, 0, e, h, _ => by
      exact congrArg (fun x => Term.eval G b (Env.append x env) h.1) (hm _ _)
  | .skip _ rest, env, n + 1, e, h, h' =>
      CtorsWithPayloadFoldCases.evalAt_map mkEnv mkEnv' hm rest env n e h.2 h'.2

theorem TaggedUnionFoldCasesRest.evalAt_map {k k' : Nat}
    {bind : List (TyWfIn 1) → List TyWf} {Γ : Ctx} {u : Usage Γ} {cs : List (List (TyWfIn 1))}
    (mkEnv : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y →
      TyWf.DenList (bind fs))
    (mkEnv' : (fs : List (TyWfIn 1)) → (Ty.toPFunctorList (fs.map TyWfIn.toTy)).Obj Y' →
      TyWf.DenList (bind fs))
    (hm : ∀ fs e, mkEnv fs e = mkEnv' fs (PFunctor.map _ g e)) :
    ∀ (r : TaggedUnionFoldCasesRest Sg (TyWfIn 1) bind Γ u cs τ) (env : Env Γ)
      (t : Nat) (e : (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj Y)
      (h : TaggedUnionFoldKCasesRest.NoRecMk
        (TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀) (k := k) r))
      (h' : TaggedUnionFoldKCasesRest.NoRecMk
        (TaggedUnionFoldCasesRest.toFoldK (l₀ := l₀') (k := k') r)),
      TaggedUnionFoldCasesRest.evalAt G r env mkEnv t e h =
        TaggedUnionFoldCasesRest.evalAt G r env mkEnv' t (PFunctor.map _ g e) h'
  | .nil, _, _, e, _, _ => PEmpty.elim e.1
  | .cons b _, env, 0, e, h, _ => by
      exact congrArg (fun x => Term.eval G b (Env.append x env) h.1) (hm _ _)
  | .cons _ rest, env, n + 1, e, h, h' =>
      TaggedUnionFoldCasesRest.evalAt_map mkEnv mkEnv' hm rest env n e h.2 h'.2

end

end

/-- The plain fold does not depend on the depth its hypothesis is stated at. -/
theorem TaggedUnionFoldCases.recFold_depth {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {k k' : Nat}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (env : Env Γ)
    (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l) (k := k) c))
    (h' : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l) (k := k') c)) :
    ∀ v, TaggedUnionFoldCases.recFold G c env h v = TaggedUnionFoldCases.recFold G c env h' v
  | .mk node f => by
      have ih : (fun p => (f p, TaggedUnionFoldCases.recFold G c env h (f p))) =
          (fun p => (f p, TaggedUnionFoldCases.recFold G c env h' (f p))) :=
        funext fun p => by rw [TaggedUnionFoldCases.recFold_depth c env h h' (f p)]
      refine (congrArg (fun x => TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ)
        node.1.val ⟨node.2, x⟩ h) ih).trans ?_
      exact TaggedUnionFoldCases.evalAt_map G id _ _ (fun _ _ => rfl) c env _ _ h h'

/-- The step of the evaluator's memoised fold, for branches that answer where they
    stand. -/
abbrev TaggedUnionFoldCases.memoStep {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} {k : Nat}
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (env : Env Γ)
    (h : TaggedUnionFoldKCases.NoRecMk (TaggedUnionFoldCases.toFoldK (l₀ := l) (k := k) c)) :
    (node : Ty.RecNode (recL l)) → (Ty.RecHole (recL l) node → RecMemo l τ) → TyWf.Den τ :=
  fun node kids =>
    TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK c) env (recBindEnv l hwf τ)
      node.1.val ⟨node.2, kids⟩ h

/-- **The evaluator's memoised fold is the plain fold**, at every depth, for branches that
    answer where they stand. -/
theorem Comp.eval_recTaggedUnion_rec_toFoldK {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat)
    {w : Usage Γ} {hd : Head} (v : Atom Sg Γ w (.recTaggedUnion l hwf) hd)
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (hc : Head.closedComp (Usage.arg hd w + Usage.many u) τ .comp = false)
    (env : Env Γ) (h : Comp.NoRecMk (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) hc)) :
    Comp.eval G (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) hc) env h =
      TaggedUnionFoldCases.recFold G c env h.2 (Atom.eval G v env h.1) := by
  show (WType.memo _ (Atom.eval G v env h.1)).answer = _
  generalize Atom.eval G v env h.1 = w
  induction w with
  | mk node f ih =>
      show TaggedUnionFoldKCases.eval G (TaggedUnionFoldCases.toFoldK c) env
          (recBindEnv l hwf τ) node.1.val ⟨node.2, fun p => WType.memo _ (f p)⟩ h.2 = _
      rw [TaggedUnionFoldKCases.eval_toFoldK,
        TaggedUnionFoldCases.evalAt_map G (fun m => (WType.Memo.tree m, WType.Memo.answer m))
          (recBindEnv l hwf τ) (recBindEnvOf l hwf τ)
          (fun fs e => recBindEnv_eq_recBindEnvOf l hwf τ fs e) c env _ _ h.2 h.2]
      refine Eq.trans ?_ (TaggedUnionFoldCases.recFold_mk G c env h.2 node f).symm
      have hk : (fun p => ((WType.memo (TaggedUnionFoldCases.memoStep G c env h.2) (f p)).tree,
            (WType.memo (TaggedUnionFoldCases.memoStep G c env h.2) (f p)).answer)) =
          fun p => (f p, TaggedUnionFoldCases.recFold G c env h.2 (f p)) :=
        funext fun p => by rw [WType.memo_tree, ih p]
      exact congrArg (fun x => TaggedUnionFoldCases.evalAt G c env (recBindEnvOf l hwf τ)
        node.1.val ⟨node.2, x⟩ h.2) hk

/-- **Depth does not change meaning**: branches that answer where they stand give the same
    value at every depth. -/
theorem Comp.eval_recTaggedUnion_rec_depth {Γ : Ctx} {u : Usage Γ} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k k' : Nat)
    {w : Usage Γ} {hd : Head} (v : Atom Sg Γ w (.recTaggedUnion l hwf) hd)
    (c : TaggedUnionFoldCases Sg (TyWfIn 1) (TyWf.recBinders (TyWf.recTaggedUnion l hwf) τ) Γ u l τ)
    (hc : Head.closedComp (Usage.arg hd w + Usage.many u) τ .comp = false)
    (env : Env Γ) (h : Comp.NoRecMk (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) hc))
    (h' : Comp.NoRecMk (.recTaggedUnion_rec k' v (TaggedUnionFoldCases.toFoldK c) hc)) :
    Comp.eval G (.recTaggedUnion_rec k v (TaggedUnionFoldCases.toFoldK c) hc) env h =
      Comp.eval G (.recTaggedUnion_rec k' v (TaggedUnionFoldCases.toFoldK c) hc) env h' := by
  rw [Comp.eval_recTaggedUnion_rec_toFoldK, Comp.eval_recTaggedUnion_rec_toFoldK]
  exact TaggedUnionFoldCases.recFold_depth G c env h.2 h'.2 _

end LeanScript

end
