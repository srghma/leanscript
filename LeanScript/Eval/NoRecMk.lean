module

public import LeanScript.Eval.Env

@[expose] public section

set_option autoImplicit false

/-!
# The fragment the evaluator interprets

`Term.NoRecMk` and the `no_rec_mk` tactic; see the section header below.
-/

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-! ## The fragment the evaluator interprets

`LeanScript.Ty.Den` gives a recursive **tagged union** its values — the W-tree of its
constructors — but gives the other three recursive shapes of `Ty` (`Ty.recObject`,
`Ty.recAlias`, `Ty.mutualRecursiveFamily`) **no values**: each of them denotes `PEmpty`.
So the one thing this evaluator cannot do is *build* a value of one of those three —
`Term.recObject_mk`, `Term.recAlias_mk` and `Term.mutualRecursiveFamily_mk` have no image
in the model.  Everything else does, the eliminators of those shapes included: their
scrutinee has no values, so a dispatch on one is `PEmpty.elim`.

`Term.NoRecMk t` says that `t` builds no such value: it is `False` at exactly those three
constructors and the conjunction of its subterms' everywhere else — the four forms of a
recursive tagged union included, whose branches really are evaluated — so a term that
does not mention them at all satisfies it by `no_rec_mk`, which is the default of the
hypothesis on `Term.run` and `Term.run'`.

Giving the other three shapes their values needs the same construction as for a
recursive tagged union (a container and its W-type; an *indexed* one for a mutual
family); until it is here, the restriction is stated rather than assumed. -/

mutual

/-- The term builds no value of a recursive record, newtype or mutual family, so
    `Term.eval` can interpret it.  See this section's header. -/
def Term.NoRecMk {Sg : Sig} : {Γ : Ctx} → {u : Usage Γ} → {hd : Head} → {τ : TyWf} → Term Sg Γ u τ hd → Prop
  | _, _, _, _, .lam body => Term.NoRecMk body
  | _, _, _, _, .ap f a _ _ => Term.NoRecMk f ∧ Term.NoRecMk a
  | _, _, _, _, .letE e body _ _ _ => Term.NoRecMk e ∧ Term.NoRecMk body
  -- externs applied to terms
  | _, _, _, _, .externCall args _ _ _ => Spine.NoRecMk args
  | _, _, _, _, .externCallChecked args _ fallback _ _ => Spine.NoRecMk args ∧ Term.NoRecMk fallback
  -- case analysis on a leaf
  | _, _, _, _, .bool_casesOn c t e _ _ => Term.NoRecMk c ∧ Term.NoRecMk t ∧ Term.NoRecMk e
  | _, _, _, _, .nat_casesOn n z s _ => Term.NoRecMk n ∧ Term.NoRecMk z ∧ Term.NoRecMk s
  | _, _, _, _, .nat_rec _ n base branch _ _ _ =>
      Term.NoRecMk n ∧ Spine.NoRecMk base ∧ Term.NoRecMk branch
  | _, _, _, _, .int_casesOn i a b _ => Term.NoRecMk i ∧ Term.NoRecMk a ∧ Term.NoRecMk b
  | _, _, _, _, .uint8_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .uint16_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .uint32_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .uint64_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .int8_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .int16_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .int32_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .int64_casesOn v b _ _ => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, _, _, .char_casesOn c b _ _ => Term.NoRecMk c ∧ Term.NoRecMk b
  | _, _, _, _, .stringPosRaw_casesOn p b _ _ => Term.NoRecMk p ∧ Term.NoRecMk b
  | _, _, _, _, .stringPos_casesOn p b _ _ => Term.NoRecMk p ∧ Term.NoRecMk b
  | _, _, _, _, .substringRaw_casesOn s b _ _ => Term.NoRecMk s ∧ Term.NoRecMk b
  | _, _, _, _, .float_casesOn x b _ _ => Term.NoRecMk x ∧ Term.NoRecMk b
  | _, _, _, _, .float32_casesOn x b _ _ => Term.NoRecMk x ∧ Term.NoRecMk b
  | _, _, _, _, .floatModel_casesOn m b _ _ => Term.NoRecMk m ∧ Term.NoRecMk b
  | _, _, _, _, .float32Model_casesOn m b _ _ => Term.NoRecMk m ∧ Term.NoRecMk b
  -- delays
  | _, _, _, _, .lazy_mk e => Term.NoRecMk e
  | _, _, _, _, .lazy_force e _ _ => Term.NoRecMk e
  | _, _, _, _, .thunk_mk e => Term.NoRecMk e
  | _, _, _, _, .thunk_force e _ _ => Term.NoRecMk e
  -- arrays
  | _, _, _, _, .array_mk ts => Terms.NoRecMk ts
  | _, _, _, _, .array_casesOn a z s _ _ => Term.NoRecMk a ∧ Term.NoRecMk z ∧ Term.NoRecMk s
  | _, _, _, _, .array_rec _ a bases branch _ _ _ =>
      Term.NoRecMk a ∧ ArrayRecBases.NoRecMk bases ∧ Term.NoRecMk branch
  -- enums
  | _, _, _, _, .enum_casesOn e cases _ => Term.NoRecMk e ∧ EnumCases.NoRecMk cases
  | _, _, _, _, .enum_casesOnWithDefault e cases dflt _ _ =>
      Term.NoRecMk e ∧ EnumSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  -- records and tagged unions
  | _, _, _, _, .record_mk _ fields => Spine.NoRecMk fields
  | _, _, _, _, .record_casesOn r body _ _ _ => Term.NoRecMk r ∧ Term.NoRecMk body
  | _, _, _, _, .taggedUnion_mk _ _ _ fields => Spine.NoRecMk fields
  | _, _, _, _, .taggedUnion_casesOn v cases _ _ => Term.NoRecMk v ∧ TaggedUnionCases.NoRecMk cases
  | _, _, _, _, .taggedUnion_casesOnWithDefault v cases dflt _ _ _ =>
      Term.NoRecMk v ∧ TaggedUnionSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  -- recursive tagged unions have values: their forms are interpreted like the others
  | _, _, _, _, .recTaggedUnion_mk _ _ _ _ fields => Spine.NoRecMk fields
  | _, _, _, _, .recTaggedUnion_casesOn v cases _ _ =>
      Term.NoRecMk v ∧ TaggedUnionCases.NoRecMk cases
  | _, _, _, _, .recTaggedUnion_casesOnWithDefault v cases dflt _ _ _ =>
      Term.NoRecMk v ∧ TaggedUnionSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  | _, _, _, _, .recTaggedUnion_rec _ v cases _ =>
      Term.NoRecMk v ∧ TaggedUnionFoldKCases.NoRecMk cases
  -- the other three recursive shapes: an introduction form has no value in this model,
  -- and an eliminator needs nothing of its branches, since its scrutinee has none either
  | _, _, _, _, .recObject_mk _ _ _ => False
  | _, _, _, _, .recObject_casesOn v _ _ _ _ => Term.NoRecMk v
  | _, _, _, _, .recObject_rec _ v _ _ => Term.NoRecMk v
  | _, _, _, _, .recAlias_mk _ _ _ => False
  | _, _, _, _, .recAlias_casesOn v _ _ _ _ => Term.NoRecMk v
  | _, _, _, _, .recAlias_rec _ v _ _ => Term.NoRecMk v
  | _, _, _, _, .mutualRecursiveFamily_mk _ _ _ => False
  | _, _, _, _, .mutualRecursiveFamily_casesOn v _ _ _ => Term.NoRecMk v
  | _, _, _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _ _ _ => Term.NoRecMk v
  | _, _, _, _, .mutualRecursiveFamily_rec _ v _ _ => Term.NoRecMk v
  -- a variable, a reference to a declaration and every literal
  | _, _, _, _, _ => True

/-- `Term.NoRecMk`, on the elements of an array. -/
def Terms.NoRecMk {Sg : Sig} : {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {ks : List Head} →
    Terms Sg Γ u τ ks → Prop
  | _, _, _, _, .nil => True
  | _, _, _, _, .cons t ts => Term.NoRecMk t ∧ Terms.NoRecMk ts

/-- `Term.NoRecMk`, on the answers a fold of an array gives to the short lists. -/
def ArrayRecBases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {σ τ : TyWf} → {k : Nat} → ArrayRecBases Sg Γ u σ τ k → Prop
  | _, _, _, _, _, .nil e => Term.NoRecMk e
  | _, _, _, _, _, .cons e more => Term.NoRecMk e ∧ ArrayRecBases.NoRecMk more

/-- `Term.NoRecMk`, on a list of terms. -/
def Spine.NoRecMk {Sg : Sig} : {Γ : Ctx} → {u : Usage Γ} → {ks : List Head} → {σs : List TyWf} → Spine Sg Γ u σs ks → Prop
  | _, _, _, _, .nil => True
  | _, _, _, _, .cons t ts => Term.NoRecMk t ∧ Spine.NoRecMk ts

/-- `Term.NoRecMk`, on the branches of a dispatch on a tagged union. -/
def TaggedUnionCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {kh : Head} →
    TaggedUnionCases Sg Γ u l τ kh → Prop
  | _, _, _, _, _, .payloadFirst b0 b1 rest =>
      Term.NoRecMk b0 ∧ Term.NoRecMk b1 ∧ TaggedUnionCasesRest.NoRecMk rest
  | _, _, _, _, _, .skip b0 rest =>
      Term.NoRecMk b0 ∧ CtorsWithPayloadCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {c : CtorsWithPayload TyWf} → {τ : TyWf} → {kh : Head} →
    CtorsWithPayloadCases Sg Γ u c τ kh → Prop
  | _, _, _, _, _, .here b rest => Term.NoRecMk b ∧ TaggedUnionCasesRest.NoRecMk rest
  | _, _, _, _, _, .skip b rest => Term.NoRecMk b ∧ CtorsWithPayloadCases.NoRecMk rest

/-- `Term.NoRecMk`, on a plain list of branches. -/
def TaggedUnionCasesRest.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {cs : List (List TyWf)} → {τ : TyWf} → {kh : Head} →
    TaggedUnionCasesRest Sg Γ u cs τ kh → Prop
  | _, _, _, _, _, .nil => True
  | _, _, _, _, _, .cons b rest => Term.NoRecMk b ∧ TaggedUnionCasesRest.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a partial dispatch on a tagged union. -/
def TaggedUnionSomeCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {kh : Head} →
    {k lo : Nat} → TaggedUnionSomeCases Sg Γ u l τ kh k lo → Prop
  | _, _, _, _, _, _, _, .last _ _ branch _ => Term.NoRecMk branch
  | _, _, _, _, _, _, _, .cons _ _ branch rest _ =>
      Term.NoRecMk branch ∧ TaggedUnionSomeCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a dispatch on an enum. -/
def EnumCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {s : LeanEnumSchema} → {kh : Head} →
    EnumCases Sg Γ u τ s kh → Prop
  | _, _, _, _, _, .three b0 b1 b2 => Term.NoRecMk b0 ∧ Term.NoRecMk b1 ∧ Term.NoRecMk b2
  | _, _, _, _, _, .cons b rest => Term.NoRecMk b ∧ EnumCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a partial dispatch on an enum. -/
def EnumSomeCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {s : LeanEnumSchema} → {kh : Head} →
    {k lo : Nat} → EnumSomeCases Sg Γ u τ s kh k lo → Prop
  | _, _, _, _, _, _, _, .last _ branch _ => Term.NoRecMk branch
  | _, _, _, _, _, _, _, .cons _ branch rest _ =>
      Term.NoRecMk branch ∧ EnumSomeCases.NoRecMk rest

/-- `Term.NoRecMk`, on one branch of a depth-`k` fold of a recursive tagged union. -/
def FoldKBranch.NoRecMk {Sg : Sig} :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {fs : List (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    FoldKBranch Sg l₀ bind Γ u fs τ k → Prop
  | _, _, _, _, _, _, _, .here body => Term.NoRecMk body
  | _, _, _, _, _, _, _, .deep _ cases => TaggedUnionFoldKCases.NoRecMk cases

/-- `Term.NoRecMk`, on the branches of a depth-`k` fold of a recursive tagged union. -/
def TaggedUnionFoldKCases.NoRecMk {Sg : Sig} :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    TaggedUnionFoldKCases Sg l₀ bind Γ u l τ k → Prop
  | _, _, _, _, _, _, _, .payloadFirst b0 b1 rest =>
      FoldKBranch.NoRecMk b0 ∧ FoldKBranch.NoRecMk b1 ∧ TaggedUnionFoldKCasesRest.NoRecMk rest
  | _, _, _, _, _, _, _, .skip b0 rest =>
      FoldKBranch.NoRecMk b0 ∧ CtorsWithPayloadFoldKCases.NoRecMk rest

/-- `Term.NoRecMk`, on the fold branches of the constructors that follow a field-less
    one. -/
def CtorsWithPayloadFoldKCases.NoRecMk {Sg : Sig} :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {c : CtorsWithPayload (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    CtorsWithPayloadFoldKCases Sg l₀ bind Γ u c τ k → Prop
  | _, _, _, _, _, _, _, .here b rest =>
      FoldKBranch.NoRecMk b ∧ TaggedUnionFoldKCasesRest.NoRecMk rest
  | _, _, _, _, _, _, _, .skip b rest =>
      FoldKBranch.NoRecMk b ∧ CtorsWithPayloadFoldKCases.NoRecMk rest

/-- `Term.NoRecMk`, on a plain list of fold branches. -/
def TaggedUnionFoldKCasesRest.NoRecMk {Sg : Sig} :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {cs : List (List (TyWfIn 1))} → {τ : TyWf} → {k : Nat} →
    TaggedUnionFoldKCasesRest Sg l₀ bind Γ u cs τ k → Prop
  | _, _, _, _, _, _, _, .nil => True
  | _, _, _, _, _, _, _, .cons b rest =>
      FoldKBranch.NoRecMk b ∧ TaggedUnionFoldKCasesRest.NoRecMk rest

end

/-- Prove that a term builds no value of a recursive record, newtype or mutual family.  A
    term written out builds none unless one of those three introduction forms is in it,
    and then the goal is `False` and the tactic fails, which is the honest answer. -/
macro "no_rec_mk" : tactic =>
  `(tactic| repeat' first | exact trivial | refine And.intro ?_ ?_)

end LeanScript

end
