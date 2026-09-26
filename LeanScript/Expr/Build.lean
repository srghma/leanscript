module

public import LeanScript.Expr.Build.Prim
public meta import LeanScript.CtorTag
public meta import LeanScript.Ty.WfTactic

@[expose] public section

set_option autoImplicit false

/-!
# The direct-style forms

One function per constructor of the direct-style grammar: each takes arbitrary terms as
operands, names every one of them with a `let` (`LeanScript.Expr.Build.Bind`, which also
explains the scheme) and applies the computation step to the atoms it got.
-/

namespace LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

variable {Sg : Sig}

/-- Delay a value, unmemoised. -/
abbrev Term.lazy_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.lazy τ) :=
  .ofComp (.lazy_mk e)

/-- Run a delayed value. -/
def Term.lazy_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.lazy τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ofComp (.lazy_force a)

/-- Delay a value and remember it: a `Thunk`. -/
abbrev Term.thunk_mk {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ τ) : Term Sg Γ (.thunk τ) :=
  .ofComp (.thunk_mk e)

/-- Force a thunk. -/
def Term.thunk_force {Γ : Ctx} {τ : TyWf} (e : Term Sg Γ (.thunk τ)) : Term Sg Γ τ :=
  e.bindAtom fun _ a => .ofComp (.thunk_force a)

/-- An array, from its elements, in order. -/
def Term.array_mk {Γ : Ctx} {τ : TyWf} (ts : Terms Sg Γ τ) : Term Sg Γ (.array τ) :=
  ts.bindAtoms Ren.id fun _ as => .ofComp (.array_mk as)

/-- Take an array apart. -/
def Term.array_casesOn' {Γ : Ctx} {σ τ : TyWf} (a : Term Sg Γ (.array σ)) (z : Term Sg Γ τ)
    (s : Term Sg (σ :: TyWf.array σ :: Γ) τ) : Term Sg Γ τ :=
  a.bindAtomOr (fun x => (.array_casesOn x z s))
    fun ρ x => (.array_casesOn x (z.rename ρ) (s.rename (Ren.lift (Ren.lift ρ))))

/-- The fold of an array that descends `k + 1` elements at a time. -/
def Term.array_rec' {Γ : Ctx} {σ τ : TyWf} (k : Nat := 0) (a : Term Sg Γ (.array σ))
    (bases : ArrayRecBases Sg Γ σ τ k)
    (branch : Term Sg (σ :: TyWf.array σ :: natRecCtx τ (k + 1) Γ) τ) : Term Sg Γ τ :=
  a.bindAtomOr (fun x =>
    (.array_rec k x bases
      branch .ret))
    fun ρ x =>
    (.array_rec k x (bases.rename ρ)
      (branch.rename (Ren.lift (Ren.lift (Ren.liftNat τ (k + 1) ρ)))) .ret)

/-- A constructor of an enum. -/
abbrev Term.enum_mk {Γ : Ctx} (s : LeanEnumSchema) (i : Fin s.nOfConstructors) :
    Term Sg Γ (.enum s) := .ofComp (.enum_mk s i)

/-- A dispatch on an enum. -/
def Term.enum_casesOn' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} (e : Term Sg Γ (.enum s))
    (cases : EnumCases Sg Γ τ s) : Term Sg Γ τ :=
  e.bindAtomOr (fun a => (.enum_casesOn a cases))
    fun ρ a => (.enum_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of an enum, with a default. -/
def Term.enum_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {s : LeanEnumSchema} {k : Nat}
    (e : Term Sg Γ (.enum s)) (cases : EnumSomeCases Sg Γ τ s k) (dflt : Term Sg Γ τ)
    (hk : k < s.nOfConstructors := by ctor_lt) : Term Sg Γ τ :=
  e.bindAtomOr (fun a => (.enum_casesOnWithDefault a cases dflt hk))
    fun ρ a => (.enum_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A record, from its fields. -/
def Term.record_mk {Γ : Ctx} (fs : LeanRecordSchema TyWf) (fields : Spine Sg Γ fs.toList) :
    Term Sg Γ (.record fs) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.record_mk fs as)

/-- The eliminator of a record. -/
def Term.record_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema TyWf}
    (r : Term Sg Γ (.record fs)) (body : Term Sg (fs.toList ++ Γ) τ) : Term Sg Γ τ :=
  r.bindAtomOr (fun a => (.record_casesOn a body))
    fun ρ a => (.record_casesOn a (body.rename (Ren.liftN fs.toList ρ)))

/-- A tagged value. -/
def Term.taggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema TyWf) (t : Nat)
    (ht : t < l.length := by ctor_tag) (fields : Spine Sg Γ (l.get t ht)) :
    Term Sg Γ (.taggedUnion l) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.taggedUnion_mk l t ht as)

/-- The eliminator of a tagged union. -/
def Term.taggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema TyWf}
    (v : Term Sg Γ (.taggedUnion l)) (cases : TaggedUnionFoldCases Sg TyWf id Γ l τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.taggedUnion_casesOn a cases))
    fun ρ a => (.taggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a tagged union, with a default. -/
def Term.taggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema TyWf} {k : Nat} (v : Term Sg Γ (.taggedUnion l))
    (cases : TaggedUnionSomeCases Sg Γ l τ k) (dflt : Term Sg Γ τ)
    (hk : k < l.length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.taggedUnion_casesOnWithDefault a cases dflt hk))
    fun ρ a =>
    (.taggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- A value of a recursive tagged union. -/
def Term.recTaggedUnion_mk {Γ : Ctx} (l : LeanTaggedUnionSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recTaggedUnionTy l) := by ty_wf) (t : Nat)
    (ht : t < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_tag)
    (fields : Spine Sg Γ ((TyWf.recTaggedUnionUnfold l hwf).get t ht)) :
    Term Sg Γ (.recTaggedUnion l hwf) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.recTaggedUnion_mk l hwf t ht as)

/-- The eliminator of a recursive tagged union. -/
def Term.recTaggedUnion_casesOn' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldCases Sg TyWf id Γ (TyWf.recTaggedUnionUnfold l hwf) τ) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recTaggedUnion_casesOn a cases))
    fun ρ a => (.recTaggedUnion_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a recursive tagged union, with a default. -/
def Term.recTaggedUnion_casesOnWithDefault' {Γ : Ctx} {τ : TyWf}
    {l : LeanTaggedUnionSchema (TyWfIn 1)} {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)}
    {k : Nat} (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionSomeCases Sg Γ (TyWf.recTaggedUnionUnfold l hwf) τ k)
    (dflt : Term Sg Γ τ)
    (hk : k < (TyWf.recTaggedUnionUnfold l hwf).length := by ctor_lt) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recTaggedUnion_casesOnWithDefault a cases dflt hk))
    fun ρ a =>
    (.recTaggedUnion_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ) hk)

/-- The fold of a recursive tagged union. -/
def Term.recTaggedUnion_rec' {Γ : Ctx} {τ : TyWf} {l : LeanTaggedUnionSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recTaggedUnionTy l)} (k : Nat := 0)
    (v : Term Sg Γ (.recTaggedUnion l hwf))
    (cases : TaggedUnionFoldKCases Sg l
      (TyWf.recBinders (.recTaggedUnion l hwf) τ) Γ l τ k []) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recTaggedUnion_rec k a cases .ret))
    fun ρ a => (.recTaggedUnion_rec k a (cases.rename ρ) .ret)

/-- A value of a recursive record. -/
def Term.recObject_mk {Γ : Ctx} (fs : LeanRecordSchema (TyWfIn 1))
    (hwf : Ty.Wf (TyWf.recObjectTy fs) := by ty_wf)
    (fields : Spine Sg Γ (TyWf.recObjectUnfold fs hwf).toList) :
    Term Sg Γ (.recObject fs hwf) :=
  fields.bindArgs Ren.id fun _ as => .ofComp (.recObject_mk fs hwf as)

/-- The eliminator of a recursive record. -/
def Term.recObject_casesOn' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg ((TyWf.recObjectUnfold fs hwf).toList ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recObject_casesOn a body))
    fun ρ a =>
    (.recObject_casesOn a (body.rename (Ren.liftN (TyWf.recObjectUnfold fs hwf).toList ρ)))

/-- The fold of a recursive record. -/
def Term.recObject_rec' {Γ : Ctx} {τ : TyWf} {fs : LeanRecordSchema (TyWfIn 1)}
    {hwf : Ty.Wf (TyWf.recObjectTy fs)} (k : Nat := 0) (v : Term Sg Γ (.recObject fs hwf))
    (body : Term Sg (TyWf.recObjectRecBinders fs hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recObject_rec k a body .ret))
    fun ρ a =>
    (.recObject_rec k a (body.rename (Ren.liftN (TyWf.recObjectRecBinders fs hwf τ k) ρ)) .ret)

/-- A value of a recursive newtype. -/
def Term.recAlias_mk {Γ : Ctx} (b : TyWfIn 1) (hwf : Ty.Wf (TyWf.recAliasTy b) := by ty_wf)
    (value : Term Sg Γ (TyWf.recAliasUnfold b hwf)) : Term Sg Γ (.recAlias b hwf) :=
  value.bindAtom fun _ a => .ofComp (.recAlias_mk b hwf a)

/-- The eliminator of a recursive newtype. -/
def Term.recAlias_casesOn' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1}
    {hwf : Ty.Wf (TyWf.recAliasTy b)} (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasUnfold b hwf :: Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.recAlias_casesOn a body))
    fun ρ a => (.recAlias_casesOn a (body.rename (Ren.lift ρ)))

/-- The fold of a recursive newtype. -/
def Term.recAlias_rec' {Γ : Ctx} {τ : TyWf} {b : TyWfIn 1} {hwf : Ty.Wf (TyWf.recAliasTy b)}
    (k : Nat := 0) (v : Term Sg Γ (.recAlias b hwf))
    (body : Term Sg (TyWf.recAliasRecBinders b hwf τ k ++ Γ) τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.recAlias_rec k a body .ret))
    fun ρ a =>
    (.recAlias_rec k a (body.rename (Ren.liftN (TyWf.recAliasRecBinders b hwf τ k) ρ)) .ret)

/-- A value of one member of a mutual recursive family. -/
def Term.mutualRecursiveFamily_mk {Γ : Ctx} {n : Nat}
    (f : LeanMutualRecFamily (TyWfIn (n + 2)))
    (hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f) := by ty_wf)
    (value : FamilyMemberValue Sg Γ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ (.mutualRecursiveFamily f hwf) :=
  value.bindArgs fun _ as => .ofComp (.mutualRecursiveFamily_mk f hwf as)

/-- The eliminator of a member of a mutual family. -/
def Term.mutualRecursiveFamily_casesOn' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf))) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.mutualRecursiveFamily_casesOn a cases))
    fun ρ a => (.mutualRecursiveFamily_casesOn a (cases.rename ρ))

/-- A dispatch on some of the constructors of a member of a mutual family, with a
    default. -/
def Term.mutualRecursiveFamily_casesOnWithDefault' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)}
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyMemberSomeCases Sg Γ τ (f.current.map (TyWfIn.unfoldFam f hwf)))
    (dflt : Term Sg Γ τ) : Term Sg Γ τ :=
  v.bindAtomOr (fun a =>
    (.mutualRecursiveFamily_casesOnWithDefault a cases dflt))
    fun ρ a =>
    (.mutualRecursiveFamily_casesOnWithDefault a (cases.rename ρ) (dflt.rename ρ))

/-- The fold of a mutual family. -/
def Term.mutualRecursiveFamily_rec' {Γ : Ctx} {τ : TyWf} {n : Nat}
    {f : LeanMutualRecFamily (TyWfIn (n + 2))}
    {hwf : Ty.Wf (TyWf.mutualRecursiveFamilyTy f)} (k : Nat := 0)
    (v : Term Sg Γ (.mutualRecursiveFamily f hwf))
    (cases : FamilyFoldKCases Sg n f.members (TyWf.famRecBinders f hwf τ) Γ τ f.members k) :
    Term Sg Γ τ :=
  v.bindAtomOr (fun a => (.mutualRecursiveFamily_rec k a cases .ret))
    fun ρ a => (.mutualRecursiveFamily_rec k a (cases.rename ρ) .ret)

/-! ## Reading the answers out of a window of answer trees

What `#leanscript_to_term` binds beside the window of a fold of depth above `0`, at a field
that is a function or a delay (`LeanScript.RecFnFieldFacts` proves their values). -/

/-- **The function of the answers at a function field**, as the translation writes it: the
    window `w : σ ⇒ ⟨τ, W⟩` holds, at every argument, the answer tree there, and the term
    is `fun a => (w a).1`. It is a `lam` around a `record_casesOn'` of `w a` that returns
    the first field. -/
def Term.fnTreeAnswer {Γ : Ctx} {σ τ W : TyWf} (w : Γ ∋ (σ ⇒ .record ⟨τ, W, []⟩)) :
    Term Sg Γ (σ ⇒ τ) :=
  Term.lam (Term.record_casesOn' (fs := ⟨τ, W, []⟩)
    (Term.ap (Term.var (Var.tail w)) (Term.var Var.head)) (Term.var Var.head))

/-- **The delayed answer at a delayed field**, as the translation writes it: the window
    `w : thunk ⟨τ, W⟩` holds the delayed answer tree, and the term delays the first field
    of it, `thunk_mk (thunk_force w).1`. -/
def Term.thunkTreeAnswer {Γ : Ctx} {τ W : TyWf} (w : Γ ∋ .thunk (.record ⟨τ, W, []⟩)) :
    Term Sg Γ (.thunk τ) :=
  Term.thunk_mk (Term.record_casesOn' (fs := ⟨τ, W, []⟩)
    (Term.thunk_force (Term.var w)) (Term.var Var.head))

end LeanScript

end
