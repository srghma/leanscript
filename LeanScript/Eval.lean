module

public import LeanScript.Eval.Env
public import LeanScript.Eval.Extern
public import LeanScript.Den.Rec
public import LeanScript.Den.RecObjectAlias
public import LeanScript.Den.Family

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

It interprets **every** term: every type of the language has values
(`LeanScript.Ty.Den`), so there is no side condition on the term.  The four recursive
shapes have values — the W-tree of the binder's payload, or for a family the *indexed*
W-tree of its members' payloads — and all of their forms are interpreted:

* a recursive **tagged union**: `Term.recTaggedUnion_mk` builds a node
  (`TyWf.DenRec.mk`), a dispatch takes one level off (`TyWf.DenRec.unfold`), and the fold
  of any depth `k` is `WType.memoFold`, which computes the answer at every node once,
  bottom-up, and stores it beside the node, so a branch that looks further down reads
  answers that are already there;
* a recursive **record**: `Term.recObject_mk` builds a node from the unfolded fields
  (`TyWf.DenObj.mk`), `Term.recObject_casesOn` binds them again (`TyWf.DenObj.unfold`),
  and `Term.recObject_rec` is `WType.memoFold` too, its branch binding the fields and the
  window of answer trees read off the memo (`LeanScript.objRecEnv`);
* a recursive **newtype**: the same, with the body for the fields (`TyWf.DenAlias.mk`,
  `TyWf.DenAlias.unfold`, `LeanScript.aliasRecEnv`);
* a **mutual family**: `Term.mutualRecursiveFamily_mk` builds a node of the member the
  family selects from its unfolded constructors, fields or body (`TyWf.DenFam.mk`), a
  dispatch takes one level off (`TyWf.DenFam.unfold`), and the fold of any depth `k` is
  `IWType.memoFold`: the answer at every node, whichever member it is a value of, is
  computed once from *that member's* branches and stored beside the node, and a deeper
  look into an occurrence of another member reads the answers stored under it
  (`LeanScript.famBindEnv`).

All of it is structural, on the term and on the value, so the evaluator is still total
with no fuel.  `LeanScript.RecUnionEvalFacts` and `LeanScript.RecObjectAliasEvalFacts`
state what it does with them; the family forms are run, against Lean references, by
`TermTests/RecTermTest.lean` and `TermTests/FamilyRecDepthTest.lean`.

That this is possible at all is the point of the grammar: `LeanScript.Term` has no
fixpoint constructor.  The two recursive forms it does have, `Term.nat_rec` and
`Term.array_rec`, are folds — the branch is *given* the value of the recursion on the
smaller argument (as a de Bruijn index) rather than being able to call anything — so
evaluating them is `Nat.rec` and `List.rec` (an array of the language denotes a Lean
`Array`, and its fold runs over the list of its elements), and every other constructor evaluates its
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
    term, so it terminates on every input, and it interprets every term. -/
def Term.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (t : Term Sg Γ τ) → Env Γ → TyWf.Den τ
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
  -- externs: the Lean function the extern implements, called on its arguments
  | _, _, .extern e, _ => Extern.eval e
  | _, _, .externCall args call, env => Extern.eval (call (Spine.eval G args env))
  | _, _, .externCallChecked args call fallback, env =>
      match call (Spine.eval G args env) with
      | some e => Extern.eval e
      | none => Term.eval G fallback env
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
  | _, _, .nat_rec _ n base branch, env =>
      natFoldK (Spine.eval G base env)
        (fun m w => Term.eval G branch (m, Env.ofWin w env))
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
  | _, _, .array_mk ts, env => (Terms.eval G ts env).toArray
  | _, _, .array_casesOn a z s, env =>
      let a' : Array _ := Term.eval G a env
      match a'.toList with
      | [] => Term.eval G z env
      | x :: xs => Term.eval G s (x, xs.toArray, env)
  | _, _, .array_rec _ a bases branch, env =>
      listFoldK (fun l => ArrayRecBases.eval G bases env l)
        (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env))
        (show Array _ from Term.eval G a env).toList
  -- enums
  | _, _, .enum_mk _ i, _ => i
  | _, _, .enum_casesOn e cases, env =>
      EnumCases.eval G cases env (Term.eval G e env)
  | _, _, .enum_casesOnWithDefault e cases dflt _, env =>
      EnumSomeCases.eval G cases env (Term.eval G e env)
        (Term.eval G dflt env)
  -- records
  | _, _, .record_mk fs fields, env =>
      cast (Ty.denRecord_eq _).symm (Spine.eval G fields env)
  | _, _, .record_casesOn r body, env =>
      Term.eval G body (Env.append (cast (Ty.denRecord_eq _) (Term.eval G r env)) env)
       
  -- tagged unions
  | _, _, .taggedUnion_mk _ t ht fields, env =>
      TyWf.DenTU.mk t ht (Spine.eval G fields env)
  | _, _, .taggedUnion_casesOn v cases, env =>
      TaggedUnionCases.eval G cases rfl .rfl .rfl env (Term.eval G v env)
  | _, _, .taggedUnion_casesOnWithDefault v cases dflt _, env =>
      TaggedUnionSomeCases.eval G cases env (Term.eval G v env)
        (Term.eval G dflt env)
  -- recursive tagged unions: a value is a W-tree, taken apart one level by
  -- `TyWf.DenRec.unfold` and folded bottom-up with every answer remembered
  | _, _, .recTaggedUnion_mk l hwf t ht fields, env =>
      TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht (Spine.eval G fields env))
  | _, _, .recTaggedUnion_casesOn (l := l) (hwf := hwf) v cases, env =>
      TaggedUnionCases.eval G cases rfl .rfl .rfl env
        (TyWf.DenRec.unfold l hwf (Term.eval G v env))
  | _, _, .recTaggedUnion_casesOnWithDefault (l := l) (hwf := hwf) v cases dflt _, env =>
      TaggedUnionSomeCases.eval G cases env (TyWf.DenRec.unfold l hwf (Term.eval G v env))
        (Term.eval G dflt env)
  | _, τ, .recTaggedUnion_rec (l := l) (hwf := hwf) _ v cases, env =>
      WType.memoFold
        (fun node kids =>
          TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) RecFrames.nil
            node.1.val ⟨node.2, kids⟩)
        (Term.eval G v env)
  -- recursive records: a value is a W-tree of the record's shapes, taken apart one level
  -- by `TyWf.DenObj.unfold` and folded bottom-up with every answer remembered
  | _, _, .recObject_mk fs hwf fields, env =>
      TyWf.DenObj.mk fs hwf (Spine.eval G fields env)
  | _, _, .recObject_casesOn (fs := fs) (hwf := hwf) v body, env =>
      Term.eval G body (Env.append (TyWf.DenObj.unfold fs hwf (Term.eval G v env)) env)
       
  | _, τ, .recObject_rec (fs := fs) (hwf := hwf) k v body, env =>
      WType.memoFold
        (fun node kids => Term.eval G body (Env.append (objRecEnv fs hwf τ k node kids) env)
         )
        (Term.eval G v env)
  -- recursive newtypes: the same, with the body for the fields
  | _, _, .recAlias_mk b hwf value, env =>
      TyWf.DenAlias.mk b hwf (Term.eval G value env)
  | _, _, .recAlias_casesOn (b := b) (hwf := hwf) v body, env =>
      Term.eval G body (TyWf.DenAlias.unfold b hwf (Term.eval G v env), env)
  | _, τ, .recAlias_rec (b := b) (hwf := hwf) k v body, env =>
      WType.memoFold
        (fun node kids =>
          Term.eval G body (Env.append (aliasRecEnv b hwf τ k node kids) env))
        (Term.eval G v env)
  -- mutual families: a value is an indexed W-tree, rooted at the member the family
  -- selects, taken apart one level by `TyWf.DenFam.unfold` and folded bottom-up with every
  -- answer remembered
  | _, _, .mutualRecursiveFamily_mk f hwf value, env =>
      TyWf.DenFam.mk f hwf (FamilyMemberValue.eval G value env)
  | _, _, .mutualRecursiveFamily_casesOn (f := f) (hwf := hwf) v cases, env =>
      FamilyMemberCases.eval G cases env (TyWf.DenFam.unfold f hwf (Term.eval G v env))
  | _, _, .mutualRecursiveFamily_casesOnWithDefault (f := f) (hwf := hwf) v cases dflt, env =>
      FamilyMemberSomeCases.eval G cases env (TyWf.DenFam.unfold f hwf (Term.eval G v env))
        (Term.eval G dflt env)
  | _, τ, .mutualRecursiveFamily_rec (f := f) (hwf := hwf) _ v cases, env =>
      IWType.memoFold (β := TyWf.Den τ)
        (fun i a kids =>
          FamilyFoldKCases.eval G cases env (famBindEnv f hwf τ) i ⟨a, kids⟩)
        (cast (den_mutualRecursiveFamily f hwf) (Term.eval G v env))

/-- The values of the elements of an array, in order, as a list; `Term.array_mk` turns it
    into the Lean `Array` an array of the language denotes. -/
def Terms.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → (ts : Terms Sg Γ τ) → Env Γ →
    List (TyWf.Den τ)
  | _, _, .nil, _ => []
  | _, _, .cons t ts, env => Term.eval G t env :: Terms.eval G ts env

/-- The answer a fold of an array gives to a list shorter than its window: the elements
    are peeled off one at a time and bound, and the answer of the list that is left is
    read off the answers of one lower depth.  A list that is **not** short — one the fold
    never consults these answers for — runs out of depth and gets the answer of the empty
    list of the innermost block. -/
def ArrayRecBases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σ τ : TyWf} → {k : Nat} → (bs : ArrayRecBases Sg Γ σ τ k) → Env Γ →
    List (TyWf.Den σ) → TyWf.Den τ
  | _, _, _, _, .nil e, env, _ => Term.eval G e env
  | _, _, _, _, .cons e _, env, [] => Term.eval G e env
  | _, _, _, _, .cons _ more, env, a :: as =>
      ArrayRecBases.eval G more (a, env) as

/-- The values of a list of terms, typed by the list of their types. -/
def Spine.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {σs : List TyWf} → (ts : Spine Sg Γ σs) → Env Γ →
    TyWf.DenList σs
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons t ts, env => (Term.eval G t env, Spine.eval G ts env)

/-- The value of the branch a value of a tagged union takes.  The branches are indexed by
    the schema and the value carries a tag that the schema has, so there is always
    exactly one branch to take.

    A plain dispatch is the fold-case family at `ι := TyWf` and `bind := id`
    (`LeanScript.TaggedUnionCases`).  Structural recursion needs the indices of the family
    to be variables, so the evaluator is stated for any `ι` and `bind` together with the
    equations that pin them — the caller passes `rfl`, and matching on those `rfl`s makes
    a branch's context `fs ++ Γ` again. -/
def TaggedUnionCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {l : LeanTaggedUnionSchema ι} →
    {τ : TyWf} → (cases : TaggedUnionFoldCases Sg ι bind Γ l τ) →
    {l' : LeanTaggedUnionSchema TyWf} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    l ≍ l' → Env Γ → TyWf.DenTU l' → TyWf.Den τ
  | _, _, _, _, _, .payloadFirst b0 b1 rest, _, rfl, .rfl, .rfl, env, v =>
      match v with
      | ⟨⟨0, _⟩, f⟩ => Term.eval G b0 (Env.append (cast (Ty.denNE_eq _) f) env)
      | ⟨⟨1, _⟩, f⟩ => Term.eval G b1 (Env.append f env)
      | ⟨⟨n + 2, _⟩, f⟩ => TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env n f
  | _, _, _, _, _, .skip b0 rest, _, rfl, .rfl, .rfl, env, v =>
      match v with
      | ⟨⟨0, _⟩, _⟩ => Term.eval G b0 env
      | ⟨⟨n + 1, _⟩, f⟩ => CtorsWithPayloadCases.eval G rest rfl .rfl .rfl env n f

/-- `TaggedUnionCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {c : CtorsWithPayload ι} →
    {τ : TyWf} → (cases : CtorsWithPayloadFoldCases Sg ι bind Γ c τ) →
    {c' : CtorsWithPayload TyWf} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    c ≍ c' → Env Γ → (t : Nat) → TyWf.DenAtCP c' t → TyWf.Den τ
  | _, _, _, _, _, .here b _, _, rfl, .rfl, .rfl, env, 0, f =>
      Term.eval G b (Env.append (cast (Ty.denNE_eq _) f) env)
  | _, _, _, _, _, .here _ rest, _, rfl, .rfl, .rfl, env, n + 1, f =>
      TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env n f
  | _, _, _, _, _, .skip b _, _, rfl, .rfl, .rfl, env, 0, _ => Term.eval G b env
  | _, _, _, _, _, .skip _ rest, _, rfl, .rfl, .rfl, env, n + 1, f =>
      CtorsWithPayloadCases.eval G rest rfl .rfl .rfl env n f

/-- `TaggedUnionCases.eval`, on a plain list of constructors.  A tag past the end of the
    list has no value — `Ty.DenAtList [] n` is `PEmpty` — which is why the empty list of
    branches needs no branch. -/
def TaggedUnionCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {ι : Type} → {bind : List ι → List TyWf} → {Γ : Ctx} → {cs : List (List ι)} →
    {τ : TyWf} → (cases : TaggedUnionFoldCasesRest Sg ι bind Γ cs τ) →
    {cs' : List (List TyWf)} → ι = TyWf → bind ≍ (id : List TyWf → List TyWf) →
    cs ≍ cs' → Env Γ → (t : Nat) → TyWf.DenAtList cs' t → TyWf.Den τ
  | _, _, _, _, _, .nil, _, rfl, .rfl, .rfl, _, _, f => PEmpty.elim f
  | _, _, _, _, _, .cons b _, _, rfl, .rfl, .rfl, env, 0, f => Term.eval G b (Env.append f env)
  | _, _, _, _, _, .cons _ rest, _, rfl, .rfl, .rfl, env, n + 1, f =>
      TaggedUnionCasesRest.eval G rest rfl .rfl .rfl env n f

/-- The value of a dispatch on **some** of the constructors of a tagged union: the first
    branch whose constructor the value has, and the default if it has none of them. -/
def TaggedUnionSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {k lo : Nat} →
    (cases : TaggedUnionSomeCases Sg Γ l τ k lo) → Env Γ → TyWf.DenTU l → TyWf.Den τ → TyWf.Den τ
  | _, _, _, _, _, .last t ht branch _, env, v, dflt =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env)
      | none => dflt
  | _, _, _, _, _, .cons t ht branch rest _, env, v, dflt =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env)
      | none => TaggedUnionSomeCases.eval G rest env v dflt

/-- The value of the branch a constructor of an enum takes.  The branches are indexed by
    the schema, so there is always exactly one branch to take. -/
def EnumCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} →
    (cases : EnumCases Sg Γ τ s) → Env Γ → Fin s.nOfConstructors → TyWf.Den τ
  | _, _, _, .three b0 b1 b2, env, i =>
      match i with
      | ⟨0, _⟩ => Term.eval G b0 env
      | ⟨1, _⟩ => Term.eval G b1 env
      | ⟨2, _⟩ => Term.eval G b2 env
      | ⟨_ + 3, hi⟩ => absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, .cons b rest, env, i =>
      match i with
      | ⟨0, _⟩ => Term.eval G b env
      | ⟨n + 1, hi⟩ =>
          EnumCases.eval G rest env ⟨n, by
            simp only [LeanEnumSchema.nOfConstructors] at hi ⊢; omega⟩

/-- The value of a dispatch on **some** of the constructors of an enum: the first branch
    whose constructor the value is, and the default if it is none of them. -/
def EnumSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {s : LeanEnumSchema} → {k lo : Nat} →
    (cases : EnumSomeCases Sg Γ τ s k lo) → Env Γ → Fin s.nOfConstructors → TyWf.Den τ → TyWf.Den τ
  | _, _, _, _, _, .last j branch _, env, i, dflt =>
      if i = j then Term.eval G branch env else dflt
  | _, _, _, _, _, .cons j branch rest _, env, i, dflt =>
      if i = j then Term.eval G branch env
      else EnumSomeCases.eval G rest env i dflt

/-- The answer of one branch of the fold of a recursive tagged union, at a node whose
    fields are `e` — their shape, with the memo of the subtree in each hole — below the
    nodes `fr` dispatched on above it.  An answer is its term, in the environment `mkEnv`
    reads off the node; a deeper look takes the memo of the occurrence it names, at this
    node or at one above, and dispatches on *its* node, so every answer it reads below is
    already stored there and nothing is recomputed. -/
def FoldKBranch.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {fs : List (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (br : FoldKBranch Sg l₀ bind Γ fs τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer → RecFields l₀ τ fs → TyWf.Den τ
  | _, _, _, _, _, _, _, .here body, env, mkEnv, _, e =>
      Term.eval G body (Env.append (mkEnv _ e) env)
  | _, _, _, _, _, _, _, .deep sf cases, env, mkEnv, fr, e =>
      match selfFieldMemo sf e with
      | .mk (node, _) kids =>
          TaggedUnionFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
            node.1.val ⟨node.2, kids⟩
  | _, _, _, _, _, _, _, .deepOuter o cases, env, mkEnv, fr, e =>
      match outerSelfFieldMemo o fr with
      | .mk (node, _) kids =>
          TaggedUnionFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
            node.1.val ⟨node.2, kids⟩

/-- The answer of the fold of a recursive tagged union at a node of constructor `t`: the
    branch of that constructor, as `TaggedUnionCases.eval` selects it. -/
def TaggedUnionFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {l : LeanTaggedUnionSchema (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : TaggedUnionFoldKCases Sg l₀ bind Γ l τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, fr, 0, e =>
      FoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, fr, 1, e =>
      FoldKBranch.eval G b1 env mkEnv fr e
  | _, _, _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, fr, n + 2, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e
  | _, _, _, _, _, _, _, .skip b0 _, env, mkEnv, fr, 0, e =>
      FoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv fr n e

/-- `TaggedUnionFoldKCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {c : CtorsWithPayload (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : CtorsWithPayloadFoldKCases Sg l₀ bind Γ c τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .here b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .here _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e
  | _, _, _, _, _, _, _, .skip b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, n + 1, e =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv fr n e

/-- `TaggedUnionFoldKCases.eval`, on a plain list of constructors; past the end there is
    no node. -/
def TaggedUnionFoldKCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {cs : List (List (TyWfIn 1))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn 1))} →
    (cases : TaggedUnionFoldKCasesRest Sg l₀ bind Γ cs τ k outer) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFrames l₀ τ outer →
    (t : Nat) → (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ) →
      TyWf.Den τ
  | _, _, _, _, _, _, _, .nil, _, _, _, _, e => PEmpty.elim e.1
  | _, _, _, _, _, _, _, .cons b _, env, mkEnv, fr, 0, e => FoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, fr, n + 1, e =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv fr n e

/-- The value of a member of a mutual family, built from the shape that member has. -/
def FamilyMemberValue.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {m : LeanFamMemberSchema TyWf} → FamilyMemberValue Sg Γ m → Env Γ →
    TyWf.DenMember m
  | _, _, .ctors _ t ht fields, env => TyWf.DenTU.mk t ht (Spine.eval G fields env)
  | _, _, .record _ fields, env => cast (Ty.denRecord_eq _).symm (Spine.eval G fields env)
  | _, _, .alias _ value, env => Term.eval G value env

/-- The value of the branch a value of a member of a mutual family takes: a dispatch on its
    constructor for a member with constructors, and the one branch, binding what the value
    holds, for a record or a newtype member. -/
def FamilyMemberCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} →
    FamilyMemberCases Sg Γ τ m → Env Γ → TyWf.DenMember m → TyWf.Den τ
  | _, _, _, .ctors cases, env, v => TaggedUnionCases.eval G cases rfl .rfl .rfl env v
  | _, _, _, .record body, env, v =>
      Term.eval G body (Env.append (cast (Ty.denRecord_eq _) v) env)
  | _, _, _, .alias body, env, v => Term.eval G body (v, env)

/-- The value of a partial dispatch on a member of a mutual family: the first branch whose
    constructor the value has, and the default if it has none of them. -/
def FamilyMemberSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {τ : TyWf} → {m : LeanFamMemberSchema TyWf} →
    FamilyMemberSomeCases Sg Γ τ m → Env Γ → TyWf.DenMember m → TyWf.Den τ → TyWf.Den τ
  | _, _, _, .ctors cases _, env, v, dflt => TaggedUnionSomeCases.eval G cases env v dflt

/-- The answer of one branch of the fold of a mutual family, at a node whose fields are
    `e` — their shape, with the memo of the subtree in each hole — below the nodes `fr`
    dispatched on above it.  An answer is its term, in the environment `mkEnv` reads off
    the node; a deeper look takes the memo of the occurrence it names, at this node or at
    one above, and dispatches on *its* node — whichever member it is a value of — so every
    answer it reads below is already stored there and nothing is recomputed. -/
def FamilyFoldKBranch.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {fs : List (TyWfIn (n + 2))} →
    {τ : TyWf} → {k : Nat} → {outer : List (List (TyWfIn (n + 2)))} →
    FamilyFoldKBranch Sg n ms₀ bind Γ fs τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer → FamFields ms₀ τ fs → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .here body, env, mkEnv, _, e =>
      Term.eval G body (Env.append (mkEnv _ e) env)
  | _, _, _, _, _, _, _, _, .deep field member cases, env, mkEnv, fr, e =>
      FamilyMemberFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
        (FamW.memoNodeAt _ _ member.at_famFs (famFieldMemo field e)).2
  | _, _, _, _, _, _, _, _, .deepOuter field member cases, env, mkEnv, fr, e =>
      FamilyMemberFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv (e, fr)
        (FamW.memoNodeAt _ _ member.at_famFs (famOuterFieldMemo field fr)).2

/-- The answer of the fold of a mutual family at a node of a given member: the branch of
    that member's constructor, field list or body. -/
def FamilyMemberFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {τ : TyWf} →
    {m : LeanFamMemberSchema (TyWfIn (n + 2))} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyMemberFoldKCases Sg n ms₀ bind Γ τ m k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer → (famIPF m).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .ctors cases, env, mkEnv, fr, x =>
      FamilyTaggedUnionFoldKCases.eval G cases env mkEnv fr x.1.1.val ⟨x.1.2, x.2⟩
  | _, _, _, _, _, _, _, _, .record br, env, mkEnv, fr, x =>
      FamilyFoldKBranch.eval G br env mkEnv fr x
  | _, _, _, _, _, _, _, _, .alias br, env, mkEnv, fr, x =>
      FamilyFoldKBranch.eval G br env mkEnv fr
        (IPFunctor.Obj.pair x ⟨PUnit.unit, fun p => PEmpty.elim p⟩)

/-- The answer of the fold of a member with constructors, at a node of constructor `t`. -/
def FamilyTaggedUnionFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {l : LeanTaggedUnionSchema (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyTaggedUnionFoldKCases Sg n ms₀ bind Γ l τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAt (l.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, fr, 1, e =>
      FamilyFoldKBranch.eval G b1 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, fr, t + 2, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e
  | _, _, _, _, _, _, _, _, .skip b0 _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b0 env mkEnv fr e
  | _, _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyCtorsWithPayloadFoldKCases.eval G rest env mkEnv fr t e

/-- `FamilyTaggedUnionFoldKCases.eval`, on the constructors that follow a field-less one. -/
def FamilyCtorsWithPayloadFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {c : CtorsWithPayload (TyWfIn (n + 2))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyCtorsWithPayloadFoldKCases Sg n ms₀ bind Γ c τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAtCP (c.map TyWfIn.toTy) t).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, _, .here b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .here _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e
  | _, _, _, _, _, _, _, _, .skip b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyCtorsWithPayloadFoldKCases.eval G rest env mkEnv fr t e

/-- `FamilyTaggedUnionFoldKCases.eval`, on a plain list of constructors; past the end
    there is no node. -/
def FamilyTaggedUnionFoldKCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} →
    {cs : List (List (TyWfIn (n + 2)))} → {τ : TyWf} → {k : Nat} →
    {outer : List (List (TyWfIn (n + 2)))} →
    FamilyTaggedUnionFoldKCasesRest Sg n ms₀ bind Γ cs τ k outer → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    FamFrames ms₀ τ outer →
    (t : Nat) → (Ty.toIPFAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (FamMemoAt ms₀ τ) →
    TyWf.Den τ
  | _, _, _, _, _, _, _, _, .nil, _, _, _, _, e => PEmpty.elim e.1
  | _, _, _, _, _, _, _, _, .cons b _, env, mkEnv, fr, 0, e =>
      FamilyFoldKBranch.eval G b env mkEnv fr e
  | _, _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, fr, t + 1, e =>
      FamilyTaggedUnionFoldKCasesRest.eval G rest env mkEnv fr t e

/-- The answer of the fold of a mutual family at a node of member `i`: the branches of
    member `i`, found by walking the members in declaration order.  The node is given as a
    shape of whatever container is *the* container of member `i` of the members still to
    walk, so walking past a member costs no `cast`; past the last member there is no
    node. -/
def FamilyFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {n : Nat} → {ms₀ : List (LeanFamMemberSchema (TyWfIn (n + 2)))} →
    {bind : List (TyWfIn (n + 2)) → List TyWf} → {Γ : Ctx} → {τ : TyWf} →
    {ms : List (LeanFamMemberSchema (TyWfIn (n + 2)))} → {k : Nat} →
    FamilyFoldKCases Sg n ms₀ bind Γ τ ms k → Env Γ →
    ((fs' : List (TyWfIn (n + 2))) → FamFields ms₀ τ fs' → TyWf.DenList (bind fs')) →
    (i : Nat) → (IPFunctor.at (famFs ms) i).Obj (FamMemoAt ms₀ τ) → TyWf.Den τ
  | _, _, _, _, _, _, _, .nil, _, _, _, node => PEmpty.elim node.1
  | _, _, _, _, _, _, _, .cons c _, env, mkEnv, 0, node =>
      FamilyMemberFoldKCases.eval G c env mkEnv FamFrames.nil node
  | _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, i + 1, node =>
      FamilyFoldKCases.eval G rest env mkEnv i node

end

/-! ## Running a closed term -/

/-- The value of a term of the empty context: a closed program, run against the values of
    the module's top-level declarations. -/
def Term.run {Sg : Sig} {τ : TyWf} (G : GlobalEnv Sg.decls) (t : Term Sg [] τ) : TyWf.Den τ :=
  Term.eval G t Env.nil

/-- The value of a term of the empty context of a module with no top-level
    declarations. -/
def Term.run' {τ : TyWf} (t : Term ⟨[], rfl⟩ [] τ) : TyWf.Den τ :=
  Term.eval GlobalEnv.nil t Env.nil

/-! ## What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that the
language's application is Lean's, that a `let` is a substitution, that a delay carries
nothing, and that reading the fields of the constructor a value was built with gives them
back. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf} (G : GlobalEnv Sg.decls)

/-- Applying an abstraction is substituting the argument's value for the bound
    variable. -/
theorem Term.eval_beta (body : Term Sg (σ :: Γ) τ) (a : Term Sg Γ σ) (env : Env Γ) :
    Term.eval G (.ap (.lam body) a) env =
      Term.eval G body (Term.eval G a env, env) :=
  rfl

/-- `let x = e; body` binds the value of `e`. -/
theorem Term.eval_letE (e : Term Sg Γ σ) (body : Term Sg (σ :: Γ) τ) (env : Env Γ) :
    Term.eval G (.letE e body) env =
      Term.eval G body (Term.eval G e env, env) :=
  rfl

/-- Forcing a delay gives back what was delayed. -/
theorem Term.eval_lazy_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.lazy_force (.lazy_mk e)) env = Term.eval G e env :=
  rfl

/-- Forcing a thunk gives back what was delayed. -/
theorem Term.eval_thunk_force_mk (e : Term Sg Γ τ) (env : Env Γ) :
    Term.eval G (.thunk_force (.thunk_mk e)) env = Term.eval G e env :=
  rfl

/-- An extern is the Lean function it implements. -/
theorem Term.eval_extern (e : Extern τ) (env : Env Γ) :
    Term.eval (Sg := Sg) G (.extern e) env = Extern.eval e :=
  rfl

/-- An extern applied to terms is the Lean function called on their values. -/
theorem Term.eval_externCall {σs : List TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Extern τ) (env : Env Γ) :
    Term.eval G (.externCall args call) env = Extern.eval (call (Spine.eval G args env)) :=
  rfl

/-- An extern that takes a proof, applied to terms whose values satisfy the proposition,
    is the Lean function called on those values, with the proof. -/
theorem Term.eval_externCallChecked_of_some {σs : List TyWf} (args : Spine Sg Γ σs)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ τ) (env : Env Γ)
    (e : Extern τ)
    (he : call (Spine.eval G args env) = some e) :
    Term.eval G (.externCallChecked args call fallback) env = Extern.eval e := by
  show (match call (Spine.eval G args env) with
    | some e => Extern.eval e
    | none => Term.eval G fallback env) = _
  rw [he]

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Term.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    (Term.eval G (.taggedUnion_mk l t ht fields) env).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Term.eval_taggedUnion_field? {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) (fields : Spine Sg Γ (l.get t ht)) (env : Env Γ) :
    TyWf.DenTU.field? t ht (Term.eval G (.taggedUnion_mk l t ht fields) env) =
      some (Spine.eval G fields env) :=
  TyWf.DenTU.field?_mk t ht _

end LeanScript

end
