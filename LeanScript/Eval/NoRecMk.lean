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

`LeanScript.Ty.Den` gives the four recursive shapes of `Ty` **no values**: each of them
denotes `PEmpty`.  That is a model of the language without recursive data, and it is the
model this evaluator works in, so the one thing it cannot do is *build* a value of a
recursive type — `Term.recTaggedUnion_mk`, `Term.recObject_mk`, `Term.recAlias_mk` and
`Term.mutualRecursiveFamily_mk` have no image in it.  Everything else does, the four
eliminators of those shapes included: their scrutinee has no values, so a dispatch on one
is `PEmpty.elim`.

`Term.NoRecMk t` says that `t` builds no recursive value: it is `False` at exactly those
four constructors and the conjunction of its subterms' everywhere else, so a term that
does not mention them at all satisfies it by `no_rec_mk`, which is the default of the
hypothesis on `Term.run` and `Term.run'`.

A model in which the recursive shapes *do* have values needs the least fixpoint of the
functor a binder's payload describes, which is a construction (a container, and its
`WType`) this module does not have; until it is here, the restriction is stated rather
than assumed. -/

mutual

/-- The term builds no value of a recursive shape, so `Term.eval` can interpret it.  See
    this section's header. -/
def Term.NoRecMk {Sg : Sig} : {Γ : Ctx} → {τ : TyWf} → Term Sg Γ τ → Prop
  | _, _, .lam body => Term.NoRecMk body
  | _, _, .ap f a => Term.NoRecMk f ∧ Term.NoRecMk a
  | _, _, .letE e body => Term.NoRecMk e ∧ Term.NoRecMk body
  -- case analysis on a leaf
  | _, _, .bool_casesOn c t e => Term.NoRecMk c ∧ Term.NoRecMk t ∧ Term.NoRecMk e
  | _, _, .nat_casesOn n z s => Term.NoRecMk n ∧ Term.NoRecMk z ∧ Term.NoRecMk s
  | _, _, .nat_rec _ n base branch =>
      Term.NoRecMk n ∧ Spine.NoRecMk base ∧ Term.NoRecMk branch
  | _, _, .int_casesOn i a b => Term.NoRecMk i ∧ Term.NoRecMk a ∧ Term.NoRecMk b
  | _, _, .uint8_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .uint16_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .uint32_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .uint64_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .int8_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .int16_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .int32_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .int64_casesOn v b => Term.NoRecMk v ∧ Term.NoRecMk b
  | _, _, .char_casesOn c b => Term.NoRecMk c ∧ Term.NoRecMk b
  | _, _, .stringPosRaw_casesOn p b => Term.NoRecMk p ∧ Term.NoRecMk b
  | _, _, .stringPos_casesOn p b => Term.NoRecMk p ∧ Term.NoRecMk b
  | _, _, .substringRaw_casesOn s b => Term.NoRecMk s ∧ Term.NoRecMk b
  | _, _, .float_casesOn x b => Term.NoRecMk x ∧ Term.NoRecMk b
  | _, _, .float32_casesOn x b => Term.NoRecMk x ∧ Term.NoRecMk b
  | _, _, .floatModel_casesOn m b => Term.NoRecMk m ∧ Term.NoRecMk b
  | _, _, .float32Model_casesOn m b => Term.NoRecMk m ∧ Term.NoRecMk b
  -- delays
  | _, _, .lazy_mk e => Term.NoRecMk e
  | _, _, .lazy_force e => Term.NoRecMk e
  | _, _, .thunk_mk e => Term.NoRecMk e
  | _, _, .thunk_force e => Term.NoRecMk e
  -- arrays
  | _, _, .array_mk ts => Terms.NoRecMk ts
  | _, _, .array_casesOn a z s => Term.NoRecMk a ∧ Term.NoRecMk z ∧ Term.NoRecMk s
  | _, _, .array_rec _ a bases branch =>
      Term.NoRecMk a ∧ ArrayRecBases.NoRecMk bases ∧ Term.NoRecMk branch
  -- enums
  | _, _, .enum_casesOn e cases => Term.NoRecMk e ∧ EnumCases.NoRecMk cases
  | _, _, .enum_casesOnWithDefault e cases dflt _ =>
      Term.NoRecMk e ∧ EnumSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  -- records and tagged unions
  | _, _, .record_mk _ fields => Spine.NoRecMk fields
  | _, _, .record_casesOn r body => Term.NoRecMk r ∧ Term.NoRecMk body
  | _, _, .taggedUnion_mk _ _ _ fields => Spine.NoRecMk fields
  | _, _, .taggedUnion_casesOn v cases => Term.NoRecMk v ∧ TaggedUnionCases.NoRecMk cases
  | _, _, .taggedUnion_casesOnWithDefault v cases dflt _ =>
      Term.NoRecMk v ∧ TaggedUnionSomeCases.NoRecMk cases ∧ Term.NoRecMk dflt
  -- the recursive shapes: an introduction form has no value in this model, and an
  -- eliminator needs nothing of its branches, since its scrutinee has none either
  | _, _, .recTaggedUnion_mk _ _ _ _ _ => False
  | _, _, .recTaggedUnion_casesOn v _ => Term.NoRecMk v
  | _, _, .recTaggedUnion_casesOnWithDefault v _ _ _ => Term.NoRecMk v
  | _, _, .recTaggedUnion_rec _ v _ => Term.NoRecMk v
  | _, _, .recObject_mk _ _ _ => False
  | _, _, .recObject_casesOn v _ => Term.NoRecMk v
  | _, _, .recObject_rec _ v _ => Term.NoRecMk v
  | _, _, .recAlias_mk _ _ _ => False
  | _, _, .recAlias_casesOn v _ => Term.NoRecMk v
  | _, _, .recAlias_rec _ v _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_mk _ _ _ => False
  | _, _, .mutualRecursiveFamily_casesOn v _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_rec _ v _ => Term.NoRecMk v
  -- a variable, a reference to a declaration and every literal
  | _, _, _ => True

/-- `Term.NoRecMk`, on the elements of an array. -/
def Terms.NoRecMk {Sg : Sig} : {Γ : Ctx} → {τ : TyWf} → Terms Sg Γ τ → Prop
  | _, _, .nil => True
  | _, _, .cons t ts => Term.NoRecMk t ∧ Terms.NoRecMk ts

/-- `Term.NoRecMk`, on the answers a fold of an array gives to the short lists. -/
def ArrayRecBases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {σ τ : TyWf} → {k : Nat} → ArrayRecBases Sg Γ σ τ k → Prop
  | _, _, _, _, .nil e => Term.NoRecMk e
  | _, _, _, _, .cons e more => Term.NoRecMk e ∧ ArrayRecBases.NoRecMk more

/-- `Term.NoRecMk`, on a list of terms. -/
def Spine.NoRecMk {Sg : Sig} : {Γ : Ctx} → {σs : List TyWf} → Spine Sg Γ σs → Prop
  | _, _, .nil => True
  | _, _, .cons t ts => Term.NoRecMk t ∧ Spine.NoRecMk ts

/-- `Term.NoRecMk`, on the branches of a dispatch on a tagged union. -/
def TaggedUnionCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} →
    TaggedUnionCases Sg Γ l τ → Prop
  | _, _, _, .payloadFirst b0 b1 rest =>
      Term.NoRecMk b0 ∧ Term.NoRecMk b1 ∧ TaggedUnionCasesRest.NoRecMk rest
  | _, _, _, .skip b0 rest =>
      Term.NoRecMk b0 ∧ CtorsWithPayloadCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {c : CtorsWithPayload TyWf} → {τ : TyWf} →
    CtorsWithPayloadCases Sg Γ c τ → Prop
  | _, _, _, .here b rest => Term.NoRecMk b ∧ TaggedUnionCasesRest.NoRecMk rest
  | _, _, _, .skip b rest => Term.NoRecMk b ∧ CtorsWithPayloadCases.NoRecMk rest

/-- `Term.NoRecMk`, on a plain list of branches. -/
def TaggedUnionCasesRest.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {cs : List (List TyWf)} → {τ : TyWf} →
    TaggedUnionCasesRest Sg Γ cs τ → Prop
  | _, _, _, .nil => True
  | _, _, _, .cons b rest => Term.NoRecMk b ∧ TaggedUnionCasesRest.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a partial dispatch on a tagged union. -/
def TaggedUnionSomeCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {k lo : Nat} →
    TaggedUnionSomeCases Sg Γ l τ k lo → Prop
  | _, _, _, _, _, .last _ _ branch _ => Term.NoRecMk branch
  | _, _, _, _, _, .cons _ _ branch rest _ =>
      Term.NoRecMk branch ∧ TaggedUnionSomeCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a dispatch on an enum. -/
def EnumCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → EnumCases Sg Γ τ s → Prop
  | _, _, _, .three b0 b1 b2 => Term.NoRecMk b0 ∧ Term.NoRecMk b1 ∧ Term.NoRecMk b2
  | _, _, _, .cons b rest => Term.NoRecMk b ∧ EnumCases.NoRecMk rest

/-- `Term.NoRecMk`, on the branches of a partial dispatch on an enum. -/
def EnumSomeCases.NoRecMk {Sg : Sig} :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {k lo : Nat} →
    EnumSomeCases Sg Γ τ s k lo → Prop
  | _, _, _, _, _, .last _ branch _ => Term.NoRecMk branch
  | _, _, _, _, _, .cons _ branch rest _ =>
      Term.NoRecMk branch ∧ EnumSomeCases.NoRecMk rest

end

/-- Prove that a term builds no value of a recursive shape.  A term written out builds
    none unless one of the four introduction forms is in it, and then the goal is
    `False` and the tactic fails, which is the honest answer. -/
macro "no_rec_mk" : tactic =>
  `(tactic| repeat' first | exact trivial | refine And.intro ?_ ?_)

end LeanScript

end
