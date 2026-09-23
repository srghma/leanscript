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

/-! ## Environments -/

/-- An environment: a value for every type of the context, innermost first. -/
abbrev Env (Γ : Ctx) : Type := TyWf.DenList Γ

/-- The empty environment, of the empty context. -/
abbrev Env.nil : Env [] := PUnit.unit

/-- One more value, in front. -/
abbrev Env.cons {Γ : Ctx} {τ : TyWf} (v : TyWf.Den τ) (env : Env Γ) : Env (τ :: Γ) :=
  (v, env)

/-- The value a variable stands for. -/
def Env.get : {Γ : Ctx} → {τ : TyWf} → (Γ ∋ τ) → Env Γ → TyWf.Den τ
  | _ :: _, _, .head, env => env.1
  | _ :: _, _, .tail v, env => Env.get v env.2

/-- Bind a whole block of values at once — the fields an eliminator's branch binds are
    in front of the context that branch is written in. -/
def Env.append : {as : List TyWf} → {Γ : Ctx} → TyWf.DenList as → Env Γ → Env (as ++ Γ)
  | [], _, _, env => env
  | _ :: _, _, vs, env => (vs.1, Env.append vs.2 env)

/-- An environment for the module's signature: a value for every top-level declaration,
    at the type the signature gives it. -/
def GlobalEnv : List GlobalDecl → Type
  | [] => PUnit
  | d :: ds => TyWf.Den d.ty × GlobalEnv ds

/-- No declarations, nothing to supply. -/
abbrev GlobalEnv.nil : GlobalEnv [] := PUnit.unit

/-- The value a reference to a top-level declaration stands for. -/
def GlobalEnv.get : {ds : List GlobalDecl} → {τ : TyWf} → GlobalRef ds τ → GlobalEnv ds →
    TyWf.Den τ
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

/-! ### The window of a fold that descends more than one step

`Term.nat_rec k` descends `k + 1` steps, so its branch is given the answers at the
`k + 1` previous arguments.  The evaluator carries them as a **window** — `k + 1` values
of `τ`, nearest first — and shifts a new answer in at each step, so the fold is linear
and no answer is ever recomputed.  The window is literally an environment of the block
`natRecCtx τ (k + 1) []` of the branch's context, which is why the base values (an
ordinary `Spine`) and the branch's environment need no conversion and no cast. -/

/-- The window a depth-`k` fold carries: `k` values of `τ`, nearest first. -/
abbrev NatWin (τ : TyWf) (k : Nat) : Type := TyWf.DenList (natRecCtx τ k [])

/-- Shift a new answer in at the front, dropping the oldest: the one step of the fold. -/
def NatWin.push {τ : TyWf} : {k : Nat} → TyWf.Den τ → NatWin τ (k + 1) → NatWin τ (k + 1)
  | 0, a, _ => (a, PUnit.unit)
  | _ + 1, a, w => (a, NatWin.push w.1 w.2)

/-- The oldest answer the window holds: the value of the fold at the argument the window
    was built for. -/
def NatWin.last {τ : TyWf} : {k : Nat} → NatWin τ (k + 1) → TyWf.Den τ
  | 0, w => w.1
  | _ + 1, w => NatWin.last w.2

/-- The environment the branch of a depth-`k` fold runs in: the window in front of the
    environment of the ambient context. -/
def Env.ofWin {τ : TyWf} {Γ : Ctx} :
    {k : Nat} → NatWin τ k → Env Γ → Env (natRecCtx τ k Γ)
  | 0, _, env => env
  | _ + 1, w, env => (w.1, Env.ofWin w.2 env)

/-- The window of the depth-`k + 1` fold at `n`: it holds the answers at
    `n + k, …, n + 1, n`. -/
def natFoldKAux {τ : TyWf} {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) : Nat → NatWin τ (k + 1)
  | 0 => z
  | n + 1 => let w := natFoldKAux z s n; NatWin.push (s n w) w

/-- The depth-`k + 1` fold of a natural number: the meaning of `Term.nat_rec k`.  `z`
    holds the answers at `k, …, 0`, nearest first, and `s n w` is the branch at
    `n + k + 1`, given `n` and the window of the previous `k + 1` answers. -/
def natFoldK {τ : TyWf} {k : Nat} (z : NatWin τ (k + 1))
    (s : Nat → NatWin τ (k + 1) → TyWf.Den τ) (n : Nat) : TyWf.Den τ :=
  NatWin.last (natFoldKAux z s n)

/-- `List.rec` with a non-dependent motive: the fold of an array.  The step is given the
    head, the tail, and the value of the fold over the tail — the three things
    `Term.array_rec`'s branch binds. -/
def listFold {α β : Type} (z : β) (s : α → List α → β → β) : List α → β
  | [] => z
  | a :: as => s a as (listFold z s as)

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
  | _, _, .array_rec a z s => Term.NoRecMk a ∧ Term.NoRecMk z ∧ Term.NoRecMk s
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
  | _, _, .recTaggedUnion_rec v _ => Term.NoRecMk v
  | _, _, .recObject_mk _ _ _ => False
  | _, _, .recObject_casesOn v _ => Term.NoRecMk v
  | _, _, .recObject_rec v _ => Term.NoRecMk v
  | _, _, .recAlias_mk _ _ _ => False
  | _, _, .recAlias_casesOn v _ => Term.NoRecMk v
  | _, _, .recAlias_rec v _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_mk _ _ _ => False
  | _, _, .mutualRecursiveFamily_casesOn v _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _ => Term.NoRecMk v
  | _, _, .mutualRecursiveFamily_rec v _ => Term.NoRecMk v
  -- a variable, a reference to a declaration and every literal
  | _, _, _ => True

/-- `Term.NoRecMk`, on the elements of an array. -/
def Terms.NoRecMk {Sg : Sig} : {Γ : Ctx} → {τ : TyWf} → Terms Sg Γ τ → Prop
  | _, _, .nil => True
  | _, _, .cons t ts => Term.NoRecMk t ∧ Terms.NoRecMk ts

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
  | _, _, .array_rec a z s, env, h =>
      listFold (Term.eval G z env h.2.1)
        (fun hd tl ih => Term.eval G s (hd, tl, ih, env) h.2.2)
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
  | _, _, .recTaggedUnion_rec v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recObject_mk _ _ _, _, h => h.elim
  | _, _, .recObject_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recObject_rec v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recAlias_mk _ _ _, _, h => h.elim
  | _, _, .recAlias_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .recAlias_rec v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_mk _ _ _, _, h => h.elim
  | _, _, .mutualRecursiveFamily_casesOn v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _, env, h =>
      PEmpty.elim (Term.eval G v env h)
  | _, _, .mutualRecursiveFamily_rec v _, env, h => PEmpty.elim (Term.eval G v env h)

/-- The values of the elements of an array, in order. -/
def Terms.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (ts : Terms Sg Γ τ) → Env Γ → Terms.NoRecMk ts →
    List (TyWf.Den τ)
  | _, _, .nil, _, _ => []
  | _, _, .cons t ts, env, h => Term.eval G t env h.1 :: Terms.eval G ts env h.2

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
