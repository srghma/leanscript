module

public import LeanScript.BuildEvalFacts.BuildersPrim

@[expose] public section

set_option autoImplicit false

/-!
# Every builder computes what its direct-style constructor means

One theorem per function of `LeanScript.Expr.Build` that takes operands: the value of the
A-normal term it builds is the value the direct-style form it is named after has — the
operands evaluated, and the step, dispatch or fold applied to their values.  They hold for
**all** terms and environments, so a translated term, however its operands are nested,
computes what it says.

The theorems for redexes, applications and the primitive dispatches are in
`LeanScript.BuildEvalFacts.BuildersPrim`, which this file imports; the ones for delays,
arrays, enums, records, tagged unions and the recursive shapes are here.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig} (G : GlobalEnv Sg.decls)

/-! ## Delays and arrays -/

/-- Forcing a delayed value is the value. -/
theorem Term.eval_lazy_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.lazy τ)) (env : Env Γ) :
    (Term.eval G (Term.lazy_force e) env : TyWf.Den τ) = (Term.eval G e env : TyWf.Den (.lazy τ)) :=
  Term.evalJ_bindAtom G e (fun _ a => .ofComp (.lazy_force a)) env (J := []) PUnit.unit
    (fun x => x) fun _ _ _ _ => rfl

/-- Forcing a thunk is the value it delays. -/
theorem Term.eval_thunk_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.thunk τ)) (env : Env Γ) :
    (Term.eval G (Term.thunk_force e) env : TyWf.Den τ) = (Term.eval G e env : TyWf.Den (.thunk τ)) :=
  Term.evalJ_bindAtom G e (fun _ a => .ofComp (.thunk_force a)) env (J := []) PUnit.unit
    (fun x => x) fun _ _ _ _ => rfl

/-- An array is the array of the values of its elements. -/
theorem Term.eval_array_mk {Γ : Ctx} {τ : TyWf} (ts : Terms Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.array_mk ts) env = (Terms.eval G ts env).toArray :=
  Terms.eval_bindAtoms G ts Ren.id env env (EnvRel.id' env) (fun _ as => .ofComp (.array_mk as))
    (fun vs => (vs.toArray : TyWf.Den (.array τ)))
    fun _ _ _ _ => rfl

/-- Taking an array apart: the empty branch, or the successor branch binding the first
    element and the rest. -/
theorem Term.eval_array_casesOn' {Γ : Ctx} {σ τ : TyWf} (a : Term Sg Γ (.array σ))
    (z : Term Sg Γ τ) (s : Term Sg (σ :: TyWf.array σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.array_casesOn' a z s) env =
      List.casesOn (motive := fun _ => TyWf.Den τ)
        (Array.toList (α := TyWf.Den σ) (Term.eval G a env)) (Term.eval G z env)
        fun x xs => Term.eval G s (x, xs.toArray, env) := by
  refine Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit
    (fun v => List.casesOn (motive := fun _ => TyWf.Den τ) (Array.toList (α := TyWf.Den σ) v)
      (Term.eval G z env) fun x xs => Term.eval G s (x, xs.toArray, env)) ?_ ?_
  · intro x
    show (match Array.toList (α := TyWf.Den σ) (Atom.eval x env) with
      | [] => Term.eval G z env | y :: ys => Term.eval G s (y, ys.toArray, env)) = _
    cases Array.toList (α := TyWf.Den σ) (Atom.eval x env) <;> rfl
  · intro Δ ρ env' x h
    show (match Array.toList (α := TyWf.Den σ) (Atom.eval x env') with
      | [] => Term.eval G (z.rename ρ) env'
      | y :: ys => Term.eval G (s.rename (Ren.lift (Ren.lift ρ))) (y, ys.toArray, env')) = _
    dsimp only
    cases Array.toList (α := TyWf.Den σ) (Atom.eval x env') with
    | nil => exact Term.eval_rename G ρ z h
    | cons y ys => exact Term.eval_rename G _ s (EnvRel.lift (EnvRel.lift h _) _)

/-- **The fold of an array** (descending `k + 1` elements) is `listFoldK` of its short-list
    answers and its branch, over the elements of its argument. -/
theorem Term.eval_array_rec' {Γ : Ctx} {σ τ : TyWf} (k : Nat) (a : Term Sg Γ (.array σ))
    (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ) (env : Env Γ) :
    Term.eval G (Term.array_rec' k a bases branch) env =
      listFoldK (fun l => ArrayRecBases.eval G bases env l)
        (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
        (Array.toList (α := TyWf.Den σ) (Term.eval G a env)) := by
  refine Term.evalJ_bindAtomOr G a _ _ env (J := []) PUnit.unit
    (fun v => listFoldK (fun l => ArrayRecBases.eval G bases env l)
      (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
      (Array.toList (α := TyWf.Den σ) v)) (fun _ => rfl) ?_
  intro Δ ρ env' x h
  show listFoldK (fun l => ArrayRecBases.eval G (bases.rename ρ) env' l)
    (fun hd tl w => Term.eval G (branch.rename (Ren.lift (Ren.lift (Ren.liftNat τ (k + 1) ρ))))
      (hd, tl.toArray, Env.ofWin w env')) _ = _
  congr 1
  · funext l
    exact ArrayRecBases.eval_rename G ρ bases env env' l h
  · funext hd tl w
    exact Term.eval_rename G _ branch
      (EnvRel.lift (EnvRel.lift (EnvRel.liftNat h _ _ w) _) _)

/-- **A `while` loop** is `whileIter` of its body, read as a step, from the value of its
    initial state, with the fuel `whileFuel`. -/
theorem Term.eval_while_loop' {Γ : Ctx} {τ : TyWf} (init : Term Sg Γ τ)
    (body : Term Sg (τ :: Γ) (TyWf.sum τ τ)) (env : Env Γ) :
    Term.eval G (Term.while_loop' init body) env =
      whileIter (fun s => TyWf.sumStep (Term.eval G body (s, env))) whileFuel
        (Term.eval G init env) := by
  refine Term.evalJ_bindAtomOr G init _ _ env (J := []) PUnit.unit
    (fun v => whileIter (fun s => TyWf.sumStep (Term.eval G body (s, env))) whileFuel v)
    (fun _ => rfl) ?_
  intro Δ ρ env' x h
  show whileIter (fun s => TyWf.sumStep (Term.eval G (body.rename (Ren.lift ρ)) (s, env')))
    whileFuel _ = _
  congr 2
  funext s
  exact congrArg TyWf.sumStep (Term.eval_rename G _ body (EnvRel.lift h s))

/-! ## Enums, records and tagged unions -/

/-- A dispatch on an enum takes the branch of the constructor the value is. -/
theorem Term.eval_enum_casesOn' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema}
    (e : Term Sg Γ (.enum s)) (cases : EnumCases Sg Γ τ s) (env : Env Γ) :
    Term.eval G (Term.enum_casesOn' e cases) env =
      EnumCases.eval G cases env (J := []) PUnit.unit (Term.eval G e env) :=
  Term.evalJ_bindAtomOr G e _ _ env (J := []) PUnit.unit
    (fun v => EnumCases.eval G cases env (J := []) PUnit.unit v) (fun _ => rfl)
    fun ρ env' _ h => EnumCases.eval_rename G ρ cases env env' _ _ h

/-- A partial dispatch on an enum takes the first branch naming the value's constructor,
    and the default otherwise. -/
theorem Term.eval_enum_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema}
    {k : Nat} (e : Term Sg Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k) (dflt : Term Sg Γ τ)
    (hk : k < s.nOfConstructors) (env : Env Γ) :
    Term.eval G (Term.enum_casesOnWithDefault' e cases dflt hk) env =
      EnumSomeCases.eval G cases env (J := []) PUnit.unit (Term.eval G e env) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G e _ _ env (J := []) PUnit.unit
    (fun v => EnumSomeCases.eval G cases env (J := []) PUnit.unit v (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show EnumSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact EnumSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- A record is the tuple of the values of its fields. -/
theorem Term.eval_record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf)
    (fields : Spine Sg Γ fs.toList) (env : Env Γ) :
    Term.eval G (Term.record_mk fs fields) env =
      cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm (Spine.eval G fields env) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => cast (Ty.denRecord_eq (fs.map TyWf.toTy)).symm vs) fun _ _ _ _ => rfl

/-- Taking a record apart binds its fields. -/
theorem Term.eval_record_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf}
    (r : Term Sg Γ (.record fs)) (body : Term Sg (fs.toList ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.record_casesOn' r body) env =
      Term.eval G body
        (Env.append (cast (Ty.denRecord_eq (fs.map TyWf.toTy)) (Term.eval G r env)) env) :=
  Term.evalJ_bindAtomOr G r _ _ env (J := []) PUnit.unit
    (fun v => Term.eval G body (Env.append (cast (Ty.denRecord_eq (fs.map TyWf.toTy)) v) env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.liftN _ _)

/-- A tagged value is its tag and the values of its fields. -/
theorem Term.eval_taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    Term.eval G (Term.taggedUnion_mk l t ht fields) env =
      TyWf.DenTU.mk t ht (Spine.eval G fields env) := by
  unfold Term.taggedUnion_mk
  exact Spine.eval_bindArgs (τ := .taggedUnion l) G fields Ren.id env env (EnvRel.id' env) _
    (TyWf.DenTU.mk t ht) fun _ _ _ _ => rfl

/-- A dispatch on a tagged union takes the branch of the value's tag, binding its fields. -/
theorem Term.eval_taggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
    (v : Term Sg Γ (.taggedUnion l)) (cases : TaggedUnionFoldCases Sg TyWf id Γ l τ)
    (env : Env Γ) :
    Term.eval G (Term.taggedUnion_casesOn' v cases) env =
      TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit (Term.eval G v env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit x) (fun _ => rfl)
    fun ρ env' _ h => TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' _ _ h

/-- A partial dispatch on a tagged union: the first branch naming the value's tag, and the
    default otherwise. -/
theorem Term.eval_taggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema TyWf} {k : Nat} (v : Term Sg Γ (.taggedUnion l))
    (cases : TaggedUnionSomeCases Sg Γ l τ k) (dflt : Term Sg Γ τ) (hk : k < l.length)
    (env : Env Γ) :
    Term.eval G (Term.taggedUnion_casesOnWithDefault' v cases dflt hk) env =
      TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit (Term.eval G v env)
        (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit x (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show TaggedUnionSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-! ## The recursive shapes -/

/-- A value of a recursive tagged union is the node built from its tag and fields. -/
theorem Term.eval_recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l)) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length)
    (fields : Spine Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_mk l hwf t ht fields) env =
      TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht (Spine.eval G fields env)) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht vs)) fun _ _ _ _ => rfl

/-- A dispatch on a recursive tagged union takes one level off the value. -/
theorem Term.eval_recTaggedUnion_casesOn' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ)
    (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_casesOn' v cases) env =
      TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit
        (TyWf.DenRec.unfold l hwf (Term.eval G v env)) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionCases.eval G cases rfl .rfl .rfl env (J := []) PUnit.unit
      (TyWf.DenRec.unfold l hwf x)) (fun _ => rfl)
    fun ρ env' _ h => TaggedUnionCases.eval_rename G ρ cases rfl .rfl .rfl env env' _ _ h

/-- A partial dispatch on a recursive tagged union takes one level off the value. -/
theorem Term.eval_recTaggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    {k : Nat} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k)
    (dflt : Term Sg Γ τ) (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length) (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_casesOnWithDefault' v cases dflt hk) env =
      TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenRec.unfold l hwf (Term.eval G v env)) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => TaggedUnionSomeCases.eval G cases env (J := []) PUnit.unit (TyWf.DenRec.unfold l hwf x)
      (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show TaggedUnionSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact TaggedUnionSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- **The fold of a recursive tagged union** is `WType.memoFold` of its branches, at the
    value of its argument. -/
theorem Term.eval_recTaggedUnion_rec' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat)
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldKCases Sg l (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ l τ k [])
    (env : Env Γ) :
    Term.eval G (Term.recTaggedUnion_rec' k v cases) env =
      WType.memoFold
        (fun node kids =>
          TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
            node.1.val ⟨node.2, kids⟩)
        (Term.eval G v env) := by
  unfold Term.recTaggedUnion_rec'
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids =>
        TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
          node.1.val ⟨node.2, kids⟩) x) ?_ ?_
  · intro _; rfl
  intro Δ ρ env' a h
  show WType.memoFold _ (Atom.eval a env') = WType.memoFold _ (Atom.eval a env')
  congr 1
  funext node kids
  exact TaggedUnionFoldKCases.eval_rename G ρ cases env env' _ _ _ _ h

/-- A value of a recursive record is the node built from its fields. -/
theorem Term.eval_recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs))
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) (env : Env Γ) :
    Term.eval G (Term.recObject_mk fs hwf fields) env =
      TyWf.DenObj.mk fs hwf (Spine.eval G fields env) :=
  Spine.eval_bindArgs G fields Ren.id env env (EnvRel.id' env) _
    (fun vs => TyWf.DenObj.mk fs hwf vs) fun _ _ _ _ => rfl

/-- Taking a recursive record apart binds its unfolded fields. -/
theorem Term.eval_recObject_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recObject_casesOn' v body) env =
      Term.eval G body (Env.append (TyWf.DenObj.unfold fs hwf (Term.eval G v env)) env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G body (Env.append (TyWf.DenObj.unfold fs hwf x) env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.liftN _ _)

/-- **The fold of a recursive record** is `WType.memoFold` of its body, at the value of its
    argument. -/
theorem Term.eval_recObject_rec' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat) (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recObject_rec' k v body) env =
      WType.memoFold
        (fun node kids => Term.eval G body (Env.append (objRecEnv fs hwf τ k node kids) env))
        (Term.eval G v env) := by
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids => Term.eval G body (Env.append (objRecEnv fs hwf τ k node kids) env)) x)
    (fun _ => rfl) ?_
  intro Δ ρ env' a h
  show WType.memoFold (fun node kids => Term.eval G (body.rename _)
      (Env.append (objRecEnv fs hwf τ k node kids) env')) _ = _
  congr 1
  funext node kids
  exact Term.eval_rename G _ body (h.liftN _ _)

/-- A value of a recursive newtype is the node built from its body. -/
theorem Term.eval_recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b))
    (value : Term Sg Γ (TyWf.recAliasUnfold b hwf)) (env : Env Γ) :
    Term.eval G (Term.recAlias_mk b hwf value) env =
      TyWf.DenAlias.mk b hwf (Term.eval G value env) :=
  Term.evalJ_bindAtom G value _ env (J := []) PUnit.unit (fun x => TyWf.DenAlias.mk b hwf x)
    fun _ _ _ _ => rfl

/-- Taking a recursive newtype apart binds its unfolded body. -/
theorem Term.eval_recAlias_casesOn' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recAlias_casesOn' v body) env =
      Term.eval G body (TyWf.DenAlias.unfold b hwf (Term.eval G v env), env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => Term.eval G body (TyWf.DenAlias.unfold b hwf x, env))
    (fun _ => rfl) fun _ _ _ h => Term.eval_rename G _ body (h.lift _)

/-- **The fold of a recursive newtype** is `WType.memoFold` of its body, at the value of its
    argument. -/
theorem Term.eval_recAlias_rec' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (k : Nat) (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) τ) (env : Env Γ) :
    Term.eval G (Term.recAlias_rec' k v body) env =
      WType.memoFold
        (fun node kids => Term.eval G body (Env.append (aliasRecEnv b hwf τ k node kids) env))
        (Term.eval G v env) := by
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => WType.memoFold
      (fun node kids => Term.eval G body (Env.append (aliasRecEnv b hwf τ k node kids) env)) x)
    (fun _ => rfl) ?_
  intro Δ ρ env' a h
  show WType.memoFold (fun node kids => Term.eval G (body.rename _)
      (Env.append (aliasRecEnv b hwf τ k node kids) env')) _ = _
  congr 1
  funext node kids
  exact Term.eval_rename G _ body (h.liftN _ _)

/-- A value of a member of a mutual family is the node built from its operands. -/
theorem Term.eval_mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2))) (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f))
    (value : FamilyMemberValue Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_mk f hwf value) env =
      TyWf.DenFam.mk f hwf (FamilyMemberValue.eval G value env) :=
  FamilyMemberValue.eval_bindArgs G value _ env (fun x => TyWf.DenFam.mk f hwf x)
    fun _ _ _ _ => rfl

/-- A dispatch on a member of a mutual family takes one level off the value. -/
theorem Term.eval_mutualRecursiveFamily_casesOn' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_casesOn' v cases) env =
      FamilyMemberCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenFam.unfold f hwf (Term.eval G v env)) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => FamilyMemberCases.eval G cases env (J := []) PUnit.unit (TyWf.DenFam.unfold f hwf x))
    (fun _ => rfl) fun ρ env' _ h => FamilyMemberCases.eval_rename G ρ cases env env' _ _ h

/-- A partial dispatch on a member of a mutual family takes one level off the value. -/
theorem Term.eval_mutualRecursiveFamily_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (dflt : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_casesOnWithDefault' v cases dflt) env =
      FamilyMemberSomeCases.eval G cases env (J := []) PUnit.unit
        (TyWf.DenFam.unfold f hwf (Term.eval G v env)) (Term.eval G dflt env) :=
  Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => FamilyMemberSomeCases.eval G cases env (J := []) PUnit.unit (TyWf.DenFam.unfold f hwf x)
      (Term.eval G dflt env))
    (fun _ => rfl) fun ρ env' _ h => by
      show FamilyMemberSomeCases.eval G (cases.rename ρ) env' (J := []) PUnit.unit _
        (Term.eval G (dflt.rename ρ) env') = _
      rw [Term.eval_rename G ρ dflt h]
      exact FamilyMemberSomeCases.eval_rename G ρ cases env env' _ _ _ h

/-- **The fold of a mutual family** is `IWType.memoFold` of the branches of every member, at
    the value of its argument. -/
theorem Term.eval_mutualRecursiveFamily_rec' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))} {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (k : Nat) (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ τ f.members k)
    (env : Env Γ) :
    Term.eval G (Term.mutualRecursiveFamily_rec' k v cases) env =
      IWType.memoFold (β := TyWf.Den τ)
        (fun i a kids => FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
        (cast (den_mutualRecursiveFamily f hwf) (Term.eval G v env)) := by
  unfold Term.mutualRecursiveFamily_rec'
  refine Term.evalJ_bindAtomOr G v _ _ env (J := []) PUnit.unit
    (fun x => IWType.memoFold (β := TyWf.Den τ)
      (fun i a kids => FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
      (cast (den_mutualRecursiveFamily f hwf) x)) ?_ ?_
  · intro _; rfl
  intro Δ ρ env' a h
  show IWType.memoFold (β := TyWf.Den τ) _ (cast (den_mutualRecursiveFamily f hwf) (Atom.eval a env'))
    = IWType.memoFold (β := TyWf.Den τ) _ (cast (den_mutualRecursiveFamily f hwf) (Atom.eval a env'))
  congr 1
  funext i x kids
  exact FamilyFoldKCases.eval_rename G ρ cases env env' _ _ _ h

end LeanScript

end
