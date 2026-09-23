module

public import LeanScript.Eval.Env
public import LeanScript.Eval.NoRecMk
public import LeanScript.Eval.Extern

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The evaluator, and why it stops

`Term.eval` takes a term of type `τ` in a context `Γ`, an environment holding a value for
every type of `Γ`, and an environment holding a value for every declaration of the
signature, and gives **the** value of that term: an element of `LeanScript.TyWf.Den τ`.

It is a **total Lean function, defined by structural recursion on the term**, so it
terminates on every input — there is no fuel, no `partial` and no `unsafe`, and the
answer is a value rather than a computation that might not stop.

It has one restriction, and it is a restriction of the *model* rather than of the
language: `LeanScript.Ty.Den` gives the four recursive shapes no values, so a term that
**builds** one has no value here.  That is the hypothesis `LeanScript.Term.NoRecMk`, the
last argument of `Term.eval`; the section below states it and the tactic `no_rec_mk`
discharges it for a term that does not use those four introduction forms.

That this is possible at all is the point of the grammar: `LeanScript.Term` has no
fixpoint constructor.  The two recursive forms it does have, `Term.nat_rec` and
`Term.array_rec`, are folds — the branch is *given* the value of the recursion on the
smaller argument (as a de Bruijn index) rather than being able to call anything — so
evaluating them is `Nat.rec` and `List.rec`, and every other constructor evaluates its
immediate subterms.  In particular:

* a dispatch always has a branch to take: `EnumCases` and `TaggedUnionCases` are indexed
  by the schema, so they are exhaustive by construction, and the two `WithDefault` forms
  carry a default;
* a field is never looked up by index: an eliminator binds the fields of the constructor
  it matched, so there is no out-of-range read to fail on;
* there is no effect and no failure, so the result is a value and not an `Option` or an
  `Except`.

The evaluator is *call-by-value*, and that choice is invisible: every form is total, so
the value of a term does not depend on the order its subterms are evaluated in.  In
particular a delay (`Ty.lazy`, `Ty.thunk`) denotes the value it stands for, and the two
`WithDefault` dispatches evaluate their default eagerly.
-/

/-! ## The evaluator -/

mutual

/-- **The value of a term**: a total function of the term, its environment and the values
    of the module's top-level declarations.  It is defined by structural recursion on the
    term, so it terminates on every input.

    The last argument is the one restriction — the term builds no value of a recursive
    shape, which this model has none of; see the section above. -/
def Term.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (t : Term Sg Γ τ) → Env Γ → Term.NoRecMk t → TyWf.Den τ
  | _, _, .var v, env, _ => Env.get v env
  | _, _, .lam body, env, h => fun x => Term.eval G body (x, env) h
  | _, _, .ap f a, env, h => (Term.eval G f env h.1) (Term.eval G a env h.2)
  | _, _, .global r, _, _ => GlobalEnv.get r G
  | _, _, .letE e body, env, h => Term.eval G body (Term.eval G e env h.1, env) h.2
  -- literals
  | _, _, .bool_mk b, _, _ => b
  | _, _, .nat_mk n, _, _ => n
  | _, _, .int_mk i, _, _ => i
  | _, _, .bitvec_mk _ v, _, _ => v
  | _, _, .uint8_mk v, _, _ => v
  | _, _, .uint16_mk v, _, _ => v
  | _, _, .uint32_mk v, _, _ => v
  | _, _, .uint64_mk v, _, _ => v
  | _, _, .int8_mk v, _, _ => v
  | _, _, .int16_mk v, _, _ => v
  | _, _, .int32_mk v, _, _ => v
  | _, _, .int64_mk v, _, _ => v
  | _, _, .char_mk c, _, _ => c
  | _, _, .string_mk s, _, _ => s
  | _, _, .stringPos_mk _ p, _, _ => p
  | _, _, .stringPosRaw_mk p, _, _ => p
  | _, _, .substringRaw_mk s, _, _ => s
  | _, _, .stringSlice_mk s, _, _ => s
  | _, _, .float_mk x, _, _ => x
  | _, _, .float32_mk x, _, _ => x
  | _, _, .floatModel_mk m, _, _ => m
  | _, _, .float32Model_mk m, _, _ => m
  -- externs: the Lean function the extern implements, applied to its arguments
  | _, _, .extern e, _, _ => Extern.eval e
  -- case analysis on a leaf
  | _, _, .bool_casesOn c t e, env, h =>
      let c' : Bool := Term.eval G c env h.1
      match c' with
      | true => Term.eval G t env h.2.1
      | false => Term.eval G e env h.2.2
  | _, _, .nat_casesOn n z s, env, h =>
      let n' : Nat := Term.eval G n env h.1
      match n' with
      | 0 => Term.eval G z env h.2.1
      | k + 1 => Term.eval G s (k, env) h.2.2
  | _, _, .nat_rec _ n base branch, env, h =>
      natFoldK (Spine.eval G base env h.2.1)
        (fun m w => Term.eval G branch (m, Env.ofWin w env) h.2.2)
        (show Nat from Term.eval G n env h.1)
  | _, _, .int_casesOn i ofNat negSucc, env, h =>
      let i' : Int := Term.eval G i env h.1
      match i' with
      | .ofNat k => Term.eval G ofNat (k, env) h.2.1
      | .negSucc k => Term.eval G negSucc (k, env) h.2.2
  | _, _, .uint8_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, .uint16_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, .uint32_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, .uint64_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, .int8_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt8, env) h.2
  | _, _, .int16_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt16, env) h.2
  | _, _, .int32_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt32, env) h.2
  | _, _, .int64_casesOn v b, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt64, env) h.2
  | _, _, .char_casesOn c b, env, h =>
      Term.eval G b ((Term.eval G c env h.1).val, env) h.2
  | _, _, .stringPosRaw_casesOn p b, env, h =>
      Term.eval G b ((Term.eval G p env h.1).byteIdx, env) h.2
  | _, _, .stringPos_casesOn p b, env, h =>
      Term.eval G b ((Term.eval G p env h.1).offset, env) h.2
  | _, _, .substringRaw_casesOn s b, env, h =>
      let v : Substring.Raw := Term.eval G s env h.1
      Term.eval G b (v.str, v.startPos, v.stopPos, env) h.2
  | _, _, .float_casesOn x b, env, h =>
      Term.eval G b ((Term.eval G x env h.1).toModel, env) h.2
  | _, _, .float32_casesOn x b, env, h =>
      Term.eval G b ((Term.eval G x env h.1).toModel, env) h.2
  | _, _, .floatModel_casesOn m b, env, h =>
      Term.eval G b ((Term.eval G m env h.1).toBits, env) h.2
  | _, _, .float32Model_casesOn m b, env, h =>
      Term.eval G b ((Term.eval G m env h.1).toBits, env) h.2
  -- delays: a delay denotes the value it stands for
  | _, _, .lazy_mk e, env, h => let v := Term.eval G e env h; v
  | _, _, .lazy_force e, env, h => let v := Term.eval G e env h; v
  | _, _, .thunk_mk e, env, h => let v := Term.eval G e env h; v
  | _, _, .thunk_force e, env, h => let v := Term.eval G e env h; v
  -- arrays
  | _, _, .array_mk ts, env, h => Terms.eval G ts env h
  | _, _, .array_casesOn a z s, env, h =>
      let a' : List _ := Term.eval G a env h.1
      match a' with
      | [] => Term.eval G z env h.2.1
      | x :: xs => Term.eval G s (x, xs, env) h.2.2
  | _, _, .array_rec _ a bases branch, env, h =>
      listFoldK (fun l => ArrayRecBases.eval G bases env l h.2.1)
        (fun hd tl w => Term.eval G branch (hd, tl, Env.ofWin w env) h.2.2)
        (show List _ from Term.eval G a env h.1)
  -- enums
  | _, _, .enum_mk _ i, _, _ => i
  | _, _, .enum_casesOn e cases, env, h =>
      EnumCases.eval G cases env (Term.eval G e env h.1) h.2
  | _, _, .enum_casesOnWithDefault e cases dflt _, env, h =>
      EnumSomeCases.eval G cases env (Term.eval G e env h.1)
        (Term.eval G dflt env h.2.2) h.2.1
  -- records
  | _, _, .record_mk fs fields, env, h =>
      cast (Ty.denRecord_eq _).symm (Spine.eval G fields env h)
  | _, _, .record_casesOn r body, env, h =>
      Term.eval G body (Env.append (cast (Ty.denRecord_eq _) (Term.eval G r env h.1)) env)
        h.2
  -- tagged unions
  | _, _, .taggedUnion_mk _ t ht fields, env, h =>
      TyWf.DenTU.mk t ht (Spine.eval G fields env h)
  | _, _, .taggedUnion_casesOn v cases, env, h =>
      TaggedUnionCases.eval G cases env (Term.eval G v env h.1) h.2
  | _, _, .taggedUnion_casesOnWithDefault v cases dflt _, env, h =>
      TaggedUnionSomeCases.eval G cases env (Term.eval G v env h.1)
        (Term.eval G dflt env h.2.2) h.2.1
  -- the recursive shapes: no value of one is built, and one taken apart has none
  | _, _, .recTaggedUnion_mk _ _ _ _ _, _, h => h.elim
  | _, _, .recTaggedUnion_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recTaggedUnion_casesOnWithDefault v _ _ _, env, h =>
      PEmpty.elim (Term.eval G v env h)
  | _, _, .recTaggedUnion_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recObject_mk _ _ _, _, h => h.elim
  | _, _, .recObject_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recObject_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recAlias_mk _ _ _, _, h => h.elim
  | _, _, .recAlias_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recAlias_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_mk _ _ _, _, h => h.elim
  | _, _, .mutualRecursiveFamily_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _, env, h =>
      PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)

/-- The values of the elements of an array, in order. -/
def Terms.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (ts : Terms Sg Γ τ) → Env Γ → Terms.NoRecMk ts →
    List (TyWf.Den τ)
  | _, _, .nil, _, _ => []
  | _, _, .cons t ts, env, h => Term.eval G t env h.1 :: Terms.eval G ts env h.2

/-- The answer a fold of an array gives to a list shorter than its window: the elements
    are peeled off one at a time and bound, and the answer of the list that is left is
    read off the answers of one lower depth.  A list that is **not** short — one the fold
    never consults these answers for — runs out of depth and gets the answer of the empty
    list of the innermost block. -/
def ArrayRecBases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {k : Nat} → (bs : ArrayRecBases Sg Γ σ τ k) → Env Γ →
    List (TyWf.Den σ) → ArrayRecBases.NoRecMk bs → TyWf.Den τ
  | _, _, _, _, .nil e, env, _, h => Term.eval G e env h
  | _, _, _, _, .cons e _, env, [], h => Term.eval G e env h.1
  | _, _, _, _, .cons _ more, env, a :: as, h =>
      ArrayRecBases.eval G more (a, env) as h.2

/-- The values of a list of terms, typed by the list of their types. -/
def Spine.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σs : List TyWf} → (ts : Spine Sg Γ σs) → Env Γ → Spine.NoRecMk ts →
    TyWf.DenList σs
  | _, _, .nil, _, _ => PUnit.unit
  | _, _, .cons t ts, env, h => (Term.eval G t env h.1, Spine.eval G ts env h.2)

/-- The value of the branch a value of a tagged union takes.  The branches are indexed by
    the schema and the value carries a tag that the schema has, so there is always
    exactly one branch to take. -/
def TaggedUnionCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} →
    (cases : TaggedUnionCases Sg Γ l τ) → Env Γ → TyWf.DenTU l →
    TaggedUnionCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, .payloadFirst b0 b1 rest, env, v, h =>
      match v with
      | ⟨⟨0, _⟩, f⟩ => Term.eval G b0 (Env.append (cast (Ty.denNE_eq _) f) env) h.1
      | ⟨⟨1, _⟩, f⟩ => Term.eval G b1 (Env.append f env) h.2.1
      | ⟨⟨n + 2, _⟩, f⟩ => TaggedUnionCasesRest.eval G rest env n f h.2.2
  | _, _, _, .skip b0 rest, env, v, h =>
      match v with
      | ⟨⟨0, _⟩, _⟩ => Term.eval G b0 env h.1
      | ⟨⟨n + 1, _⟩, f⟩ => CtorsWithPayloadCases.eval G rest env n f h.2

/-- `TaggedUnionCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {c : CtorsWithPayload TyWf} → {τ : TyWf} →
    (cases : CtorsWithPayloadCases Sg Γ c τ) → Env Γ → (t : Nat) → TyWf.DenAtCP c t →
    CtorsWithPayloadCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, .here b _, env, 0, f, h =>
      Term.eval G b (Env.append (cast (Ty.denNE_eq _) f) env) h.1
  | _, _, _, .here _ rest, env, n + 1, f, h =>
      TaggedUnionCasesRest.eval G rest env n f h.2
  | _, _, _, .skip b _, env, 0, _, h => Term.eval G b env h.1
  | _, _, _, .skip _ rest, env, n + 1, f, h =>
      CtorsWithPayloadCases.eval G rest env n f h.2

/-- `TaggedUnionCases.eval`, on a plain list of constructors.  A tag past the end of the
    list has no value — `Ty.DenAtList [] n` is `PEmpty` — which is why the empty list of
    branches needs no branch. -/
def TaggedUnionCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {cs : List (List TyWf)} → {τ : TyWf} →
    (cases : TaggedUnionCasesRest Sg Γ cs τ) → Env Γ → (t : Nat) → TyWf.DenAtList cs t →
    TaggedUnionCasesRest.NoRecMk cases → TyWf.Den τ
  | _, _, _, .nil, _, _, f, _ => PEmpty.elim f
  | _, _, _, .cons b _, env, 0, f, h => Term.eval G b (Env.append f env) h.1
  | _, _, _, .cons _ rest, env, n + 1, f, h =>
      TaggedUnionCasesRest.eval G rest env n f h.2

/-- The value of a dispatch on **some** of the constructors of a tagged union: the first
    branch whose constructor the value has, and the default if it has none of them. -/
def TaggedUnionSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {k lo : Nat} →
    (cases : TaggedUnionSomeCases Sg Γ l τ k lo) → Env Γ → TyWf.DenTU l → TyWf.Den τ →
    TaggedUnionSomeCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .last t ht branch _, env, v, dflt, h =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env) h
      | none => dflt
  | _, _, _, _, _, .cons t ht branch rest _, env, v, dflt, h =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env) h.1
      | none => TaggedUnionSomeCases.eval G rest env v dflt h.2

/-- The value of the branch a constructor of an enum takes.  The branches are indexed by
    the schema, so there is always exactly one branch to take. -/
def EnumCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} →
    (cases : EnumCases Sg Γ τ s) → Env Γ → Fin s.nOfConstructors →
    EnumCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, .three b0 b1 b2, env, i, h =>
      match i with
      | ⟨0, _⟩ => Term.eval G b0 env h.1
      | ⟨1, _⟩ => Term.eval G b1 env h.2.1
      | ⟨2, _⟩ => Term.eval G b2 env h.2.2
      | ⟨_ + 3, hi⟩ => absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, .cons b rest, env, i, h =>
      match i with
      | ⟨0, _⟩ => Term.eval G b env h.1
      | ⟨n + 1, hi⟩ =>
          EnumCases.eval G rest env ⟨n, by
            simp only [LeanEnumSchema.nOfConstructors] at hi ⊢; omega⟩ h.2

/-- The value of a dispatch on **some** of the constructors of an enum: the first branch
    whose constructor the value is, and the default if it is none of them. -/
def EnumSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {k lo : Nat} →
    (cases : EnumSomeCases Sg Γ τ s k lo) → Env Γ → Fin s.nOfConstructors → TyWf.Den τ →
    EnumSomeCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .last j branch _, env, i, dflt, h =>
      if i = j then Term.eval G branch env h else dflt
  | _, _, _, _, _, .cons j branch rest _, env, i, dflt, h =>
      if i = j then Term.eval G branch env h.1
      else EnumSomeCases.eval G rest env i dflt h.2

end

/-! ## Running a closed term -/

/-- The value of a term of the empty context: a closed program, run against the values of
    the module's top-level declarations.  The hypothesis is written by `no_rec_mk`, so a
    term that builds no recursive value needs nothing written by hand. -/
def Term.run {Sg : Sig} {τ : TyWf} (G : GlobalEnv Sg.decls) (t : Term Sg [] τ)
    (h : Term.NoRecMk t := by no_rec_mk) : TyWf.Den τ :=
  Term.eval G t Env.nil h

/-- The value of a term of the empty context of a module with no top-level
    declarations. -/
def Term.run' {τ : TyWf} (t : Term ⟨[], rfl⟩ [] τ)
    (h : Term.NoRecMk t := by no_rec_mk) : TyWf.Den τ :=
  Term.eval GlobalEnv.nil t Env.nil h

/-! ## What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that the
language's application is Lean's, that a `let` is a substitution, that a delay carries
nothing, and that reading the fields of the constructor a value was built with gives them
back. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf} (G : GlobalEnv Sg.decls)

/-- Applying an abstraction is substituting the argument's value for the bound
    variable. -/
theorem Term.eval_beta (body : Term Sg (σ :: Γ) τ) (a : Term Sg Γ σ) (env : Env Γ)
    (hb : Term.NoRecMk body) (ha : Term.NoRecMk a) :
    Term.eval G (.ap (.lam body) a) env ⟨hb, ha⟩ =
      Term.eval G body (Term.eval G a env ha, env) hb :=
  rfl

/-- `let x = e; body` binds the value of `e`. -/
theorem Term.eval_letE (e : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ) (env : Env Γ)
    (he : Term.NoRecMk e) (hb : Term.NoRecMk body) :
    Term.eval G (.letE e body) env ⟨he, hb⟩ =
      Term.eval G body (Term.eval G e env he, env) hb :=
  rfl

/-- Forcing a delay gives back what was delayed. -/
theorem Term.eval_lazy_force_mk (e : Term Sg Γ τ) (env : Env Γ) (he : Term.NoRecMk e) :
    Term.eval G (.lazy_force (.lazy_mk e)) env he = Term.eval G e env he :=
  rfl

/-- Forcing a thunk gives back what was delayed. -/
theorem Term.eval_thunk_force_mk (e : Term Sg Γ τ) (env : Env Γ) (he : Term.NoRecMk e) :
    Term.eval G (.thunk_force (.thunk_mk e)) env he = Term.eval G e env he :=
  rfl

/-- An extern is the Lean function it implements, applied to its arguments. -/
theorem Term.eval_extern (e : Extern τ) (env : Env Γ) (h : Term.NoRecMk (Sg := Sg) (.extern e)) :
    Term.eval G (.extern e) env h = Extern.eval e :=
  rfl

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Term.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ)
    (hf : Spine.NoRecMk fields) :
    (Term.eval G (.taggedUnion_mk l t ht fields) env hf).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Term.eval_taggedUnion_field? {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ)
    (hf : Spine.NoRecMk fields) :
    TyWf.DenTU.field? t ht (Term.eval G (.taggedUnion_mk l t ht fields) env hf) =
      some (Spine.eval G fields env hf) :=
  TyWf.DenTU.field?_mk t ht _

end LeanScript

end
