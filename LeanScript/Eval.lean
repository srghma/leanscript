module

public import LeanScript.Expr
public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

namespace LeanScript

/-!
# The evaluator, and why it stops

`Term.eval` takes a term of type `τ` in a context `Γ`, an environment holding a value for
every type of `Γ`, and an environment holding a value for every declaration of the
signature, and gives **the** value of that term: an element of `LeanScript.Ty.Den τ`.

It is a **total Lean function, defined by structural recursion on the term**, so it
terminates on every input — there is no fuel, no `partial` and no `unsafe`, and the
answer is a value rather than a computation that might not stop.

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

/-! ## Environments -/

/-- An environment: a value for every type of the context, innermost first. -/
abbrev Env (Γ : Ctx) : Type := Ty.DenList Γ

/-- The empty environment, of the empty context. -/
abbrev Env.nil : Env [] := PUnit.unit

/-- One more value, in front. -/
abbrev Env.cons {Γ : Ctx} {τ : Ty} (v : Ty.Den τ) (env : Env Γ) : Env (τ :: Γ) := (v, env)

/-- The value a variable stands for. -/
def Env.get : {Γ : Ctx} → {τ : Ty} → (Γ ∋ τ) → Env Γ → Ty.Den τ
  | _ :: _, _, .head, env => env.1
  | _ :: _, _, .tail v, env => Env.get v env.2

/-- Bind a whole block of values at once — the fields an eliminator's branch binds are
    in front of the context that branch is written in. -/
def Env.append : {as : List Ty} → {Γ : Ctx} → Ty.DenList as → Env Γ → Env (as ++ Γ)
  | [], _, _, env => env
  | _ :: _, _, vs, env => (vs.1, Env.append vs.2 env)

/-- An environment for the module's signature: a value for every top-level declaration,
    at the type the signature gives it. -/
def GlobalEnv : List GlobalDecl → Type
  | [] => PUnit
  | d :: ds => Ty.Den d.ty × GlobalEnv ds

/-- No declarations, nothing to supply. -/
abbrev GlobalEnv.nil : GlobalEnv [] := PUnit.unit

/-- The value a reference to a top-level declaration stands for. -/
def GlobalEnv.get : {ds : List GlobalDecl} → {τ : Ty} → GlobalRef ds τ → GlobalEnv ds →
    Ty.Den τ
  | _ :: _, _, .head, g => g.1
  | _ :: _, _, .tail r, g => GlobalEnv.get r g.2

/-! ## Two folds

`Term.nat_rec` and `Term.array_rec` are `Nat.rec` and `List.rec` with a non-dependent
motive.  They are named here so that the evaluator's clause for each is one line, and so
that it is visible that the recursion is over the *value*, which is already in hand, and
not over the term. -/

/-- `Nat.rec` with a non-dependent motive: the fold of a natural number. -/
def natFold {α : Type} (z : α) (s : Nat → α → α) : Nat → α
  | 0 => z
  | n + 1 => s n (natFold z s n)

/-- `List.rec` with a non-dependent motive: the fold of an array.  The step is given the
    head, the tail, and the value of the fold over the tail — the three things
    `Term.array_rec`'s branch binds. -/
def listFold {α β : Type} (z : β) (s : α → List α → β → β) : List α → β
  | [] => z
  | a :: as => s a as (listFold z s as)

/-! ## The evaluator -/

mutual

/-- **The value of a term**: a total function of the term, its environment and the values
    of the module's top-level declarations.  It is defined by structural recursion on the
    term, so it terminates on every input. -/
def Term.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : Ty} → Term Sg Γ τ → Env Γ → Ty.Den τ
  | _, _, .var v, env => Env.get v env
  | _, _, .lam body, env => fun x => Term.eval G body (x, env)
  | _, _, .ap f a, env => (Term.eval G f env) (Term.eval G a env)
  | _, _, .global r, _ => GlobalEnv.get r G
  | _, _, .letE e body, env => Term.eval G body (Term.eval G e env, env)
  -- literals
  | _, _, .bool_mk b, _ => b
  | _, _, .nat_mk n, _ => n
  | _, _, .int_mk i, _ => i
  | _, _, .bitvec_mk _ v, _ => v
  | _, _, .uint8_mk v, _ => v
  | _, _, .uint16_mk v, _ => v
  | _, _, .uint32_mk v, _ => v
  | _, _, .uint64_mk v, _ => v
  | _, _, .int8_mk v, _ => v
  | _, _, .int16_mk v, _ => v
  | _, _, .int32_mk v, _ => v
  | _, _, .int64_mk v, _ => v
  | _, _, .char_mk c, _ => c
  | _, _, .string_mk s, _ => s
  | _, _, .stringPos_mk _ p, _ => p
  | _, _, .stringPosRaw_mk p, _ => p
  | _, _, .substringRaw_mk s, _ => s
  | _, _, .stringSlice_mk s, _ => s
  | _, _, .float_mk x, _ => x
  | _, _, .float32_mk x, _ => x
  | _, _, .floatModel_mk m, _ => m
  | _, _, .float32Model_mk m, _ => m
  -- case analysis on a leaf
  | _, _, .bool_casesOn c t e, env =>
      let c' : Bool := Term.eval G c env
      match c' with
      | true => Term.eval G t env
      | false => Term.eval G e env
  | _, _, .nat_casesOn n z s, env =>
      let n' : Nat := Term.eval G n env
      match n' with
      | 0 => Term.eval G z env
      | k + 1 => Term.eval G s (k, env)
  | _, _, .nat_rec n z s, env =>
      natFold (Term.eval G z env)
        (fun k ih => Term.eval G s (k, ih, env))
        (show Nat from Term.eval G n env)
  | _, _, .int_casesOn i ofNat negSucc, env =>
      let i' : Int := Term.eval G i env
      match i' with
      | .ofNat k => Term.eval G ofNat (k, env)
      | .negSucc k => Term.eval G negSucc (k, env)
  | _, _, .uint8_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toBitVec, env)
  | _, _, .uint16_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toBitVec, env)
  | _, _, .uint32_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toBitVec, env)
  | _, _, .uint64_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toBitVec, env)
  | _, _, .int8_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toUInt8, env)
  | _, _, .int16_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toUInt16, env)
  | _, _, .int32_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toUInt32, env)
  | _, _, .int64_casesOn v b, env =>
      Term.eval G b ((Term.eval G v env).toUInt64, env)
  | _, _, .char_casesOn c b, env =>
      Term.eval G b ((Term.eval G c env).val, env)
  | _, _, .stringPosRaw_casesOn p b, env =>
      Term.eval G b ((Term.eval G p env).byteIdx, env)
  | _, _, .stringPos_casesOn p b, env =>
      Term.eval G b ((Term.eval G p env).offset, env)
  | _, _, .substringRaw_casesOn s b, env =>
      let v : Substring.Raw := Term.eval G s env
      Term.eval G b (v.str, v.startPos, v.stopPos, env)
  | _, _, .float_casesOn x b, env =>
      Term.eval G b ((Term.eval G x env).toModel, env)
  | _, _, .float32_casesOn x b, env =>
      Term.eval G b ((Term.eval G x env).toModel, env)
  | _, _, .floatModel_casesOn m b, env =>
      Term.eval G b ((Term.eval G m env).toBits, env)
  | _, _, .float32Model_casesOn m b, env =>
      Term.eval G b ((Term.eval G m env).toBits, env)
  -- delays: a delay denotes the value it stands for
  | _, _, .lazy_mk e, env => let v := Term.eval G e env; v
  | _, _, .lazy_force e, env => let v := Term.eval G e env; v
  | _, _, .thunk_mk e, env => let v := Term.eval G e env; v
  | _, _, .thunk_force e, env => let v := Term.eval G e env; v
  -- arrays
  | _, _, .array_mk ts, env => Terms.eval G ts env
  | _, _, .array_casesOn a z s, env =>
      let a' : List _ := Term.eval G a env
      match a' with
      | [] => Term.eval G z env
      | x :: xs => Term.eval G s (x, xs, env)
  | _, _, .array_rec a z s, env =>
      listFold (Term.eval G z env)
        (fun hd tl ih => Term.eval G s (hd, tl, ih, env))
        (show List _ from Term.eval G a env)
  -- enums
  | _, _, .enum_mk _ i, _ => i
  | _, _, .enum_casesOn e cases, env => EnumCases.eval G cases env (Term.eval G e env)
  | _, _, .enum_casesOnWithDefault e cases dflt, env =>
      EnumSomeCases.eval G cases env (Term.eval G e env) (Term.eval G dflt env)
  -- records
  | _, _, .record_mk fs fields, env =>
      cast (Ty.denRecord_eq fs).symm (Spine.eval G fields env)
  | _, _, .record_casesOn r body, env =>
      Term.eval G body (Env.append (cast (Ty.denRecord_eq _) (Term.eval G r env)) env)
  -- tagged unions
  | _, _, .taggedUnion_mk _ t ht fields, env =>
      Ty.DenTU.mk t ht (Spine.eval G fields env)
  | _, _, .taggedUnion_casesOn v cases, env =>
      TaggedUnionCases.eval G cases env (Term.eval G v env)
  | _, _, .taggedUnion_casesOnWithDefault v cases dflt, env =>
      TaggedUnionSomeCases.eval G cases env (Term.eval G v env) (Term.eval G dflt env)

/-- The values of the elements of an array, in order. -/
def Terms.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : Ty} → Terms Sg Γ τ → Env Γ → List (Ty.Den τ)
  | _, _, .nil, _ => []
  | _, _, .cons t ts, env => Term.eval G t env :: Terms.eval G ts env

/-- The values of a list of terms, typed by the list of their types. -/
def Spine.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σs : List Ty} → Spine Sg Γ σs → Env Γ → Ty.DenList σs
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons t ts, env => (Term.eval G t env, Spine.eval G ts env)

/-- The value of the branch a value of a tagged union takes.  The branches are indexed by
    the schema and the value carries a tag that the schema has, so there is always
    exactly one branch to take. -/
def TaggedUnionCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema Ty} → {τ : Ty} →
    TaggedUnionCases Sg Γ l τ → Env Γ → Ty.DenTU l → Ty.Den τ
  | _, _, _, .payloadFirst b0 b1 rest, env, v =>
      match v with
      | ⟨⟨0, _⟩, f⟩ => Term.eval G b0 (Env.append (cast (Ty.denNE_eq _) f) env)
      | ⟨⟨1, _⟩, f⟩ => Term.eval G b1 (Env.append f env)
      | ⟨⟨n + 2, _⟩, f⟩ => TaggedUnionCasesRest.eval G rest env n f
  | _, _, _, .skip b0 rest, env, v =>
      match v with
      | ⟨⟨0, _⟩, _⟩ => Term.eval G b0 env
      | ⟨⟨n + 1, _⟩, f⟩ => CtorsWithPayloadCases.eval G rest env n f

/-- `TaggedUnionCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {c : CtorsWithPayload Ty} → {τ : Ty} →
    CtorsWithPayloadCases Sg Γ c τ → Env Γ → (t : Nat) → Ty.DenAtCP c t → Ty.Den τ
  | _, _, _, .here b _, env, 0, f =>
      Term.eval G b (Env.append (cast (Ty.denNE_eq _) f) env)
  | _, _, _, .here _ rest, env, n + 1, f => TaggedUnionCasesRest.eval G rest env n f
  | _, _, _, .skip b _, env, 0, _ => Term.eval G b env
  | _, _, _, .skip _ rest, env, n + 1, f => CtorsWithPayloadCases.eval G rest env n f

/-- `TaggedUnionCases.eval`, on a plain list of constructors.  A tag past the end of the
    list has no value — `Ty.DenAtList [] n` is `PEmpty` — which is why the empty list of
    branches needs no branch. -/
def TaggedUnionCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {cs : List (List Ty)} → {τ : Ty} →
    TaggedUnionCasesRest Sg Γ cs τ → Env Γ → (t : Nat) → Ty.DenAtList cs t → Ty.Den τ
  | _, _, _, .nil, _, _, f => PEmpty.elim f
  | _, _, _, .cons b _, env, 0, f => Term.eval G b (Env.append f env)
  | _, _, _, .cons _ rest, env, n + 1, f => TaggedUnionCasesRest.eval G rest env n f

/-- The value of a dispatch on **some** of the constructors of a tagged union: the first
    branch whose constructor the value has, and the default if it has none of them. -/
def TaggedUnionSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema Ty} → {τ : Ty} → {lo : Nat} →
    TaggedUnionSomeCases Sg Γ l τ lo → Env Γ → Ty.DenTU l → Ty.Den τ → Ty.Den τ
  | _, _, _, _, .last t ht branch _, env, v, dflt =>
      match Ty.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env)
      | none => dflt
  | _, _, _, _, .cons t ht branch rest _, env, v, dflt =>
      match Ty.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env)
      | none => TaggedUnionSomeCases.eval G rest env v dflt

/-- The value of the branch a constructor of an enum takes.  The branches are indexed by
    the schema, so there is always exactly one branch to take. -/
def EnumCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : Ty} → {s : LeanEnumSchema} →
    EnumCases Sg Γ τ s → Env Γ → Fin s.nOfConstructors → Ty.Den τ
  | _, _, _, .three b0 b1 b2, env, i =>
      match i with
      | ⟨0, _⟩ => Term.eval G b0 env
      | ⟨1, _⟩ => Term.eval G b1 env
      | ⟨2, _⟩ => Term.eval G b2 env
      | ⟨_ + 3, h⟩ => absurd h (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, .cons b rest, env, i =>
      match i with
      | ⟨0, _⟩ => Term.eval G b env
      | ⟨n + 1, h⟩ =>
          EnumCases.eval G rest env ⟨n, by
            simp only [LeanEnumSchema.nOfConstructors] at h ⊢; omega⟩

/-- The value of a dispatch on **some** of the constructors of an enum: the first branch
    whose constructor the value is, and the default if it is none of them. -/
def EnumSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : Ty} → {n lo : Nat} →
    EnumSomeCases Sg Γ τ n lo → Env Γ → Fin n → Ty.Den τ → Ty.Den τ
  | _, _, _, _, .last j branch _, env, i, dflt =>
      if i = j then Term.eval G branch env else dflt
  | _, _, _, _, .cons j branch rest _, env, i, dflt =>
      if i = j then Term.eval G branch env else EnumSomeCases.eval G rest env i dflt

end

/-! ## Running a closed term -/

/-- The value of a term of the empty context: a closed program, run against the values of
    the module's top-level declarations. -/
def Term.run {Sg : Sig} {τ : Ty} (G : GlobalEnv Sg.decls) (t : Term Sg [] τ) : Ty.Den τ :=
  Term.eval G t Env.nil

/-- The value of a term of the empty context of a module with no top-level
    declarations. -/
def Term.run' {τ : Ty} (t : Term ⟨[], rfl⟩ [] τ) : Ty.Den τ :=
  Term.eval GlobalEnv.nil t Env.nil

/-! ## What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that the
language's application is Lean's, that a `let` is a substitution, that a delay carries
nothing, and that reading the fields of the constructor a value was built with gives them
back. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : Ty} (G : GlobalEnv Sg.decls)

/-- Applying an abstraction is substituting the argument's value for the bound
    variable. -/
theorem Term.eval_beta (body : Term Sg (σ :: Γ) τ) (a : Term Sg Γ σ) (env : Env Γ) :
    Term.eval G (.ap (.lam body) a) env = Term.eval G body (Term.eval G a env, env) :=
  rfl

/-- `let x = e; body` binds the value of `e`. -/
theorem Term.eval_letE (e : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (.letE e body) env = Term.eval G body (Term.eval G e env, env) :=
  rfl

/-- Forcing a delay gives back what was delayed. -/
theorem Term.eval_lazy_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.lazy_force (.lazy_mk e)) env = Term.eval G e env :=
  rfl

/-- Forcing a thunk gives back what was delayed. -/
theorem Term.eval_thunk_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.thunk_force (.thunk_mk e)) env = Term.eval G e env :=
  rfl

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Term.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema Ty} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    (Term.eval G (.taggedUnion_mk l t ht fields) env).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Term.eval_taggedUnion_field? {l : LeanTaggedUnionSchema Ty} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    Ty.DenTU.field? t ht (Term.eval G (.taggedUnion_mk l t ht fields) env) =
      some (Spine.eval G fields env) :=
  Ty.DenTU.field?_mk t ht _

end LeanScript

end
