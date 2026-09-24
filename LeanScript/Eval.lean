module

public import LeanScript.Eval.Env
public import LeanScript.Eval.NoRecMk
public import LeanScript.Eval.Extern
public import LeanScript.Den.Rec

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
language: `LeanScript.Ty.Den` gives a recursive **record**, a recursive **newtype** and a
**mutual family** no values, so a term that **builds** one has no value here.  That is the
hypothesis `LeanScript.Term.NoRecMk`, the last argument of `Term.eval`; the tactic
`no_rec_mk` discharges it for a term that does not use those three introduction forms.  A
recursive **tagged union** does have values — the W-tree of its constructors — and all
four of its forms are interpreted: `Term.recTaggedUnion_mk` builds a node
(`TyWf.DenRec.mk`), a dispatch takes one level off (`TyWf.DenRec.unfold`), and the fold
of any depth `k` is `WType.memoFold`, which computes the answer at every node once,
bottom-up, and stores it beside the node, so a branch that looks further down reads
answers that are already there.  All of it is structural, on the term and on the value,
so the evaluator is still total with no fuel.  `LeanScript.RecUnionEvalFacts` states what
it does with them.

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
    term, so it terminates on every input.

    The last argument is the one restriction — the term builds no value of a recursive
    record, newtype or mutual family, which this model has none of; see the section
    above. -/
def Term.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {hd : Head} → {τ : TyWf} → (t : Term Sg Γ u τ hd) → Env Γ → Term.NoRecMk t → TyWf.Den τ
  | _, _, _, _, .var v, env, _ => Env.get v env
  | _, _, _, _, .lam body, env, h => fun x => Term.eval G body (x, env) h
  | _, _, _, _, .ap f a _, env, h => (Term.eval G f env h.1) (Term.eval G a env h.2)
  | _, _, _, _, .global r, _, _ => GlobalEnv.get r G
  | _, _, _, _, .letE e body _ _, env, h => Term.eval G body (Term.eval G e env h.1, env) h.2
  -- literals
  | _, _, _, _, .bool_mk b, _, _ => b
  | _, _, _, _, .nat_mk n, _, _ => n
  | _, _, _, _, .int_mk i, _, _ => i
  | _, _, _, _, .bitvec_mk _ v, _, _ => v
  | _, _, _, _, .uint8_mk v, _, _ => v
  | _, _, _, _, .uint16_mk v, _, _ => v
  | _, _, _, _, .uint32_mk v, _, _ => v
  | _, _, _, _, .uint64_mk v, _, _ => v
  | _, _, _, _, .int8_mk v, _, _ => v
  | _, _, _, _, .int16_mk v, _, _ => v
  | _, _, _, _, .int32_mk v, _, _ => v
  | _, _, _, _, .int64_mk v, _, _ => v
  | _, _, _, _, .char_mk c, _, _ => c
  | _, _, _, _, .string_mk s, _, _ => s
  | _, _, _, _, .stringPos_mk _ p, _, _ => p
  | _, _, _, _, .stringPosRaw_mk p, _, _ => p
  | _, _, _, _, .substringRaw_mk s, _, _ => s
  | _, _, _, _, .stringSlice_mk s, _, _ => s
  | _, _, _, _, .float_mk x, _, _ => x
  | _, _, _, _, .float32_mk x, _, _ => x
  | _, _, _, _, .floatModel_mk m, _, _ => m
  | _, _, _, _, .float32Model_mk m, _, _ => m
  -- externs: the Lean function the extern implements, called on its arguments
  | _, _, _, _, .extern e _, _, _ => Extern.eval e
  | _, _, _, _, .externCall args call _, env, h => Extern.eval (call (Spine.eval G args env h))
  | _, _, _, _, .externCallChecked args call fallback _, env, h =>
      match call (Spine.eval G args env h.1) with
      | some e => Extern.eval e
      | none => Term.eval G fallback env h.2
  -- case analysis on a leaf
  | _, _, _, _, .bool_casesOn c t e _, env, h =>
      let c' : Bool := Term.eval G c env h.1
      match c' with
      | true => Term.eval G t env h.2.1
      | false => Term.eval G e env h.2.2
  | _, _, _, _, .nat_casesOn n z s _, env, h =>
      let n' : Nat := Term.eval G n env h.1
      match n' with
      | 0 => Term.eval G z env h.2.1
      | k + 1 => Term.eval G s (k, env) h.2.2
  | _, _, _, _, .nat_rec _ n base branch _, env, h =>
      natFoldK (Spine.eval G base env h.2.1)
        (fun m w => Term.eval G branch (m, Env.ofWin w env) h.2.2)
        (show Nat from Term.eval G n env h.1)
  | _, _, _, _, .int_casesOn i ofNat negSucc _, env, h =>
      let i' : Int := Term.eval G i env h.1
      match i' with
      | .ofNat k => Term.eval G ofNat (k, env) h.2.1
      | .negSucc k => Term.eval G negSucc (k, env) h.2.2
  | _, _, _, _, .uint8_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, _, _, .uint16_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, _, _, .uint32_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, _, _, .uint64_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toBitVec, env) h.2
  | _, _, _, _, .int8_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt8, env) h.2
  | _, _, _, _, .int16_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt16, env) h.2
  | _, _, _, _, .int32_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt32, env) h.2
  | _, _, _, _, .int64_casesOn v b _, env, h =>
      Term.eval G b ((Term.eval G v env h.1).toUInt64, env) h.2
  | _, _, _, _, .char_casesOn c b _, env, h =>
      Term.eval G b ((Term.eval G c env h.1).val, env) h.2
  | _, _, _, _, .stringPosRaw_casesOn p b _, env, h =>
      Term.eval G b ((Term.eval G p env h.1).byteIdx, env) h.2
  | _, _, _, _, .stringPos_casesOn p b _, env, h =>
      Term.eval G b ((Term.eval G p env h.1).offset, env) h.2
  | _, _, _, _, .substringRaw_casesOn s b _, env, h =>
      let v : Substring.Raw := Term.eval G s env h.1
      Term.eval G b (v.str, v.startPos, v.stopPos, env) h.2
  | _, _, _, _, .float_casesOn x b _, env, h =>
      Term.eval G b ((Term.eval G x env h.1).toModel, env) h.2
  | _, _, _, _, .float32_casesOn x b _, env, h =>
      Term.eval G b ((Term.eval G x env h.1).toModel, env) h.2
  | _, _, _, _, .floatModel_casesOn m b _, env, h =>
      Term.eval G b ((Term.eval G m env h.1).toBits, env) h.2
  | _, _, _, _, .float32Model_casesOn m b _, env, h =>
      Term.eval G b ((Term.eval G m env h.1).toBits, env) h.2
  -- delays: a delay denotes the value it stands for
  | _, _, _, _, .lazy_mk e, env, h => let v := Term.eval G e env h; v
  | _, _, _, _, .lazy_force e _, env, h => let v := Term.eval G e env h; v
  | _, _, _, _, .thunk_mk e, env, h => let v := Term.eval G e env h; v
  | _, _, _, _, .thunk_force e _, env, h => let v := Term.eval G e env h; v
  -- arrays
  | _, _, _, _, .array_mk ts, env, h => (Terms.eval G ts env h).toArray
  | _, _, _, _, .array_casesOn a z s _, env, h =>
      let a' : Array _ := Term.eval G a env h.1
      match a'.toList with
      | [] => Term.eval G z env h.2.1
      | x :: xs => Term.eval G s (x, xs.toArray, env) h.2.2
  | _, _, _, _, .array_rec _ a bases branch _, env, h =>
      listFoldK (fun l => ArrayRecBases.eval G bases env l h.2.1)
        (fun hd tl w => Term.eval G branch (hd, tl.toArray, Env.ofWin w env) h.2.2)
        (show Array _ from Term.eval G a env h.1).toList
  -- enums
  | _, _, _, _, .enum_mk _ i, _, _ => i
  | _, _, _, _, .enum_casesOn e cases _, env, h =>
      EnumCases.eval G cases env (Term.eval G e env h.1) h.2
  | _, _, _, _, .enum_casesOnWithDefault e cases dflt _ _, env, h =>
      EnumSomeCases.eval G cases env (Term.eval G e env h.1)
        (Term.eval G dflt env h.2.2) h.2.1
  -- records
  | _, _, _, _, .record_mk fs fields, env, h =>
      cast (Ty.denRecord_eq _).symm (Spine.eval G fields env h)
  | _, _, _, _, .record_casesOn r body _, env, h =>
      Term.eval G body (Env.append (cast (Ty.denRecord_eq _) (Term.eval G r env h.1)) env)
        h.2
  -- tagged unions
  | _, _, _, _, .taggedUnion_mk _ t ht fields, env, h =>
      TyWf.DenTU.mk t ht (Spine.eval G fields env h)
  | _, _, _, _, .taggedUnion_casesOn v cases _, env, h =>
      TaggedUnionCases.eval G cases env (Term.eval G v env h.1) h.2
  | _, _, _, _, .taggedUnion_casesOnWithDefault v cases dflt _ _, env, h =>
      TaggedUnionSomeCases.eval G cases env (Term.eval G v env h.1)
        (Term.eval G dflt env h.2.2) h.2.1
  -- recursive tagged unions: a value is a W-tree, taken apart one level by
  -- `TyWf.DenRec.unfold` and folded bottom-up with every answer remembered
  | _, _, _, _, .recTaggedUnion_mk l hwf t ht fields, env, h =>
      TyWf.DenRec.mk l hwf (TyWf.DenTU.mk t ht (Spine.eval G fields env h))
  | _, _, _, _, .recTaggedUnion_casesOn (l := l) (hwf := hwf) v cases _, env, h =>
      TaggedUnionCases.eval G cases env (TyWf.DenRec.unfold l hwf (Term.eval G v env h.1)) h.2
  | _, _, _, _, .recTaggedUnion_casesOnWithDefault (l := l) (hwf := hwf) v cases dflt _ _, env, h =>
      TaggedUnionSomeCases.eval G cases env (TyWf.DenRec.unfold l hwf (Term.eval G v env h.1))
        (Term.eval G dflt env h.2.2) h.2.1
  | _, _, _, τ, .recTaggedUnion_rec (l := l) (hwf := hwf) _ v cases, env, h =>
      WType.memoFold
        (fun node kids =>
          TaggedUnionFoldKCases.eval G cases env (recBindEnv l hwf τ) node.1.val
            ⟨node.2, kids⟩ h.2)
        (Term.eval G v env h.1)
  -- the other recursive shapes: no value of one is built, and one taken apart has none
  | _, _, _, _, .recObject_mk _ _ _, _, h => h.elim
  | _, _, _, _, .recObject_casesOn v _ _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .recObject_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .recAlias_mk _ _ _, _, h => h.elim
  | _, _, _, _, .recAlias_casesOn v _ _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .recAlias_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .mutualRecursiveFamily_mk _ _ _, _, h => h.elim
  | _, _, _, _, .mutualRecursiveFamily_casesOn v _ _, env, h => PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .mutualRecursiveFamily_casesOnWithDefault v _ _ _, env, h =>
      PEmpty.elim (Term.eval G v env h)
  | _, _, _, _, .mutualRecursiveFamily_rec _ v _, env, h => PEmpty.elim (Term.eval G v env h)

/-- The values of the elements of an array, in order, as a list; `Term.array_mk` turns it
    into the Lean `Array` an array of the language denotes. -/
def Terms.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {ks : List Head} → (ts : Terms Sg Γ u τ ks) →
    Env Γ → Terms.NoRecMk ts → List (TyWf.Den τ)
  | _, _, _, _, .nil, _, _ => []
  | _, _, _, _, .cons t ts, env, h => Term.eval G t env h.1 :: Terms.eval G ts env h.2

/-- The answer a fold of an array gives to a list shorter than its window: the elements
    are peeled off one at a time and bound, and the answer of the list that is left is
    read off the answers of one lower depth.  A list that is **not** short — one the fold
    never consults these answers for — runs out of depth and gets the answer of the empty
    list of the innermost block. -/
def ArrayRecBases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {σ τ : TyWf} → {k : Nat} → (bs : ArrayRecBases Sg Γ u σ τ k) → Env Γ →
    List (TyWf.Den σ) → ArrayRecBases.NoRecMk bs → TyWf.Den τ
  | _, _, _, _, _, .nil e, env, _, h => Term.eval G e env h
  | _, _, _, _, _, .cons e _, env, [], h => Term.eval G e env h.1
  | _, _, _, _, _, .cons _ more, env, a :: as, h =>
      ArrayRecBases.eval G more (a, env) as h.2

/-- The values of a list of terms, typed by the list of their types. -/
def Spine.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {ks : List Head} → {σs : List TyWf} → (ts : Spine Sg Γ u σs ks) → Env Γ → Spine.NoRecMk ts →
    TyWf.DenList σs
  | _, _, _, _, .nil, _, _ => PUnit.unit
  | _, _, _, _, .cons t ts, env, h => (Term.eval G t env h.1, Spine.eval G ts env h.2)

/-- The value of the branch a value of a tagged union takes.  The branches are indexed by
    the schema and the value carries a tag that the schema has, so there is always
    exactly one branch to take. -/
def TaggedUnionCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {kh : Head} →
    (cases : TaggedUnionCases Sg Γ u l τ kh) → Env Γ → TyWf.DenTU l →
    TaggedUnionCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .payloadFirst b0 b1 rest, env, v, h =>
      match v with
      | ⟨⟨0, _⟩, f⟩ => Term.eval G b0 (Env.append (cast (Ty.denNE_eq _) f) env) h.1
      | ⟨⟨1, _⟩, f⟩ => Term.eval G b1 (Env.append f env) h.2.1
      | ⟨⟨n + 2, _⟩, f⟩ => TaggedUnionCasesRest.eval G rest env n f h.2.2
  | _, _, _, _, _, .skip b0 rest, env, v, h =>
      match v with
      | ⟨⟨0, _⟩, _⟩ => Term.eval G b0 env h.1
      | ⟨⟨n + 1, _⟩, f⟩ => CtorsWithPayloadCases.eval G rest env n f h.2

/-- `TaggedUnionCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {c : CtorsWithPayload TyWf} → {τ : TyWf} → {kh : Head} →
    (cases : CtorsWithPayloadCases Sg Γ u c τ kh) → Env Γ → (t : Nat) → TyWf.DenAtCP c t →
    CtorsWithPayloadCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .here b _, env, 0, f, h =>
      Term.eval G b (Env.append (cast (Ty.denNE_eq _) f) env) h.1
  | _, _, _, _, _, .here _ rest, env, n + 1, f, h =>
      TaggedUnionCasesRest.eval G rest env n f h.2
  | _, _, _, _, _, .skip b _, env, 0, _, h => Term.eval G b env h.1
  | _, _, _, _, _, .skip _ rest, env, n + 1, f, h =>
      CtorsWithPayloadCases.eval G rest env n f h.2

/-- `TaggedUnionCases.eval`, on a plain list of constructors.  A tag past the end of the
    list has no value — `Ty.DenAtList [] n` is `PEmpty` — which is why the empty list of
    branches needs no branch. -/
def TaggedUnionCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {cs : List (List TyWf)} → {τ : TyWf} → {kh : Head} →
    (cases : TaggedUnionCasesRest Sg Γ u cs τ kh) → Env Γ → (t : Nat) → TyWf.DenAtList cs t →
    TaggedUnionCasesRest.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .nil, _, _, f, _ => PEmpty.elim f
  | _, _, _, _, _, .cons b _, env, 0, f, h => Term.eval G b (Env.append f env) h.1
  | _, _, _, _, _, .cons _ rest, env, n + 1, f, h =>
      TaggedUnionCasesRest.eval G rest env n f h.2

/-- The value of a dispatch on **some** of the constructors of a tagged union: the first
    branch whose constructor the value has, and the default if it has none of them. -/
def TaggedUnionSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema TyWf} → {τ : TyWf} → {kh : Head} →
    {k lo : Nat} → (cases : TaggedUnionSomeCases Sg Γ u l τ kh k lo) → Env Γ → TyWf.DenTU l → TyWf.Den τ →
    TaggedUnionSomeCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, _, _, .last t ht branch _, env, v, dflt, h =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env) h
      | none => dflt
  | _, _, _, _, _, _, _, .cons t ht branch rest _, env, v, dflt, h =>
      match TyWf.DenTU.field? t ht v with
      | some f => Term.eval G branch (Env.append f env) h.1
      | none => TaggedUnionSomeCases.eval G rest env v dflt h.2

/-- The value of the branch a constructor of an enum takes.  The branches are indexed by
    the schema, so there is always exactly one branch to take. -/
def EnumCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {s : LeanEnumSchema} → {kh : Head} →
    (cases : EnumCases Sg Γ u τ s kh) → Env Γ → Fin s.nOfConstructors →
    EnumCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, .three b0 b1 b2, env, i, h =>
      match i with
      | ⟨0, _⟩ => Term.eval G b0 env h.1
      | ⟨1, _⟩ => Term.eval G b1 env h.2.1
      | ⟨2, _⟩ => Term.eval G b2 env h.2.2
      | ⟨_ + 3, hi⟩ => absurd hi (by simp [LeanEnumSchema.nOfConstructors])
  | _, _, _, _, _, .cons b rest, env, i, h =>
      match i with
      | ⟨0, _⟩ => Term.eval G b env h.1
      | ⟨n + 1, hi⟩ =>
          EnumCases.eval G rest env ⟨n, by
            simp only [LeanEnumSchema.nOfConstructors] at hi ⊢; omega⟩ h.2

/-- The value of a dispatch on **some** of the constructors of an enum: the first branch
    whose constructor the value is, and the default if it is none of them. -/
def EnumSomeCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {Γ : Ctx} → {u : Usage Γ} → {τ : TyWf} → {s : LeanEnumSchema} → {kh : Head} →
    {k lo : Nat} → (cases : EnumSomeCases Sg Γ u τ s kh k lo) → Env Γ → Fin s.nOfConstructors → TyWf.Den τ →
    EnumSomeCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, _, _, .last j branch _, env, i, dflt, h =>
      if i = j then Term.eval G branch env h else dflt
  | _, _, _, _, _, _, _, .cons j branch rest _, env, i, dflt, h =>
      if i = j then Term.eval G branch env h.1
      else EnumSomeCases.eval G rest env i dflt h.2

/-- The answer of one branch of the fold of a recursive tagged union, at a node whose
    fields are `e` — their shape, with the memo of the subtree in each hole.  An answer is
    its term, in the environment `mkEnv` reads off the node; a deeper look takes the memo
    of the occurrence it names and dispatches on *its* node, so every answer it reads
    below is already stored there and nothing is recomputed. -/
def FoldKBranch.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {fs : List (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    (br : FoldKBranch Sg l₀ bind Γ u fs τ k) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    RecFields l₀ τ fs → FoldKBranch.NoRecMk br → TyWf.Den τ
  | _, _, _, _, _, _, _, .here body, env, mkEnv, e, h =>
      Term.eval G body (Env.append (mkEnv _ e) env) h
  | _, _, _, _, _, _, _, .deep sf cases, env, mkEnv, e, h =>
      match selfFieldMemo sf e with
      | .mk (node, _) kids =>
          TaggedUnionFoldKCases.eval G cases (Env.append (mkEnv _ e) env) mkEnv node.1.val
            ⟨node.2, kids⟩ h

/-- The answer of the fold of a recursive tagged union at a node of constructor `t`: the
    branch of that constructor, as `TaggedUnionCases.eval` selects it. -/
def TaggedUnionFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {l : LeanTaggedUnionSchema (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    (cases : TaggedUnionFoldKCases Sg l₀ bind Γ u l τ k) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (t : Nat) → (Ty.toPFunctorAt (recL l) t).Obj (RecMemo l₀ τ) →
    TaggedUnionFoldKCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, _, _, .payloadFirst b0 _ _, env, mkEnv, 0, e, h =>
      FoldKBranch.eval G b0 env mkEnv e h.1
  | _, _, _, _, _, _, _, .payloadFirst _ b1 _, env, mkEnv, 1, e, h =>
      FoldKBranch.eval G b1 env mkEnv e h.2.1
  | _, _, _, _, _, _, _, .payloadFirst _ _ rest, env, mkEnv, n + 2, e, h =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv n e h.2.2
  | _, _, _, _, _, _, _, .skip b0 _, env, mkEnv, 0, e, h =>
      FoldKBranch.eval G b0 env mkEnv e h.1
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv n e h.2

/-- `TaggedUnionFoldKCases.eval`, on the constructors that follow a field-less one. -/
def CtorsWithPayloadFoldKCases.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {c : CtorsWithPayload (TyWfIn 1)} → {τ : TyWf} → {k : Nat} →
    (cases : CtorsWithPayloadFoldKCases Sg l₀ bind Γ u c τ k) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (t : Nat) → (Ty.toPFunctorAtCP (c.map TyWfIn.toTy) t).Obj (RecMemo l₀ τ) →
    CtorsWithPayloadFoldKCases.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, _, _, .here b _, env, mkEnv, 0, e, h => FoldKBranch.eval G b env mkEnv e h.1
  | _, _, _, _, _, _, _, .here _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv n e h.2
  | _, _, _, _, _, _, _, .skip b _, env, mkEnv, 0, e, h => FoldKBranch.eval G b env mkEnv e h.1
  | _, _, _, _, _, _, _, .skip _ rest, env, mkEnv, n + 1, e, h =>
      CtorsWithPayloadFoldKCases.eval G rest env mkEnv n e h.2

/-- `TaggedUnionFoldKCases.eval`, on a plain list of constructors; past the end there is
    no node. -/
def TaggedUnionFoldKCasesRest.eval {Sg : Sig} (G : GlobalEnv Sg.decls) :
    {l₀ : LeanTaggedUnionSchema (TyWfIn 1)} → {bind : List (TyWfIn 1) → List TyWf} →
    {Γ : Ctx} → {u : Usage Γ} → {cs : List (List (TyWfIn 1))} → {τ : TyWf} → {k : Nat} →
    (cases : TaggedUnionFoldKCasesRest Sg l₀ bind Γ u cs τ k) → Env Γ →
    ((fs' : List (TyWfIn 1)) → RecFields l₀ τ fs' → TyWf.DenList (bind fs')) →
    (t : Nat) → (Ty.toPFunctorAtList (cs.map (List.map TyWfIn.toTy)) t).Obj (RecMemo l₀ τ) →
    TaggedUnionFoldKCasesRest.NoRecMk cases → TyWf.Den τ
  | _, _, _, _, _, _, _, .nil, _, _, _, e, _ => PEmpty.elim e.1
  | _, _, _, _, _, _, _, .cons b _, env, mkEnv, 0, e, h => FoldKBranch.eval G b env mkEnv e h.1
  | _, _, _, _, _, _, _, .cons _ rest, env, mkEnv, n + 1, e, h =>
      TaggedUnionFoldKCasesRest.eval G rest env mkEnv n e h.2

end

/-! ## Running a closed term -/

/-- The value of a term of the empty context: a closed program, run against the values of
    the module's top-level declarations.  The hypothesis is written by `no_rec_mk`, so a
    term that builds no recursive value needs nothing written by hand. -/
def Term.run {Sg : Sig} {u : Usage []} {τ : TyWf} {k : Head} (G : GlobalEnv Sg.decls)
    (t : Term Sg [] u τ k) (h : Term.NoRecMk t := by no_rec_mk) : TyWf.Den τ :=
  Term.eval G t Env.nil h

/-- The value of a term of the empty context of a module with no top-level
    declarations. -/
def Term.run' {u : Usage []} {τ : TyWf} {k : Head} (t : Term ⟨[], rfl⟩ [] u τ k)
    (h : Term.NoRecMk t := by no_rec_mk) : TyWf.Den τ :=
  Term.eval GlobalEnv.nil t Env.nil h

/-! ## What the evaluator does, stated

The clauses below are the ones worth naming: they hold by `rfl`, and they say that a
`let` is a substitution, that an extern is the Lean function it implements, and that
reading the fields of the constructor a value was built with gives them back.

The grammar has no β-redex, no forced delay and no dispatch on a constructor — those are
not terms (`LeanScript.Expr.Usage`) — so there is nothing to say about how they evaluate:
the translation reduces them before it builds the term. -/

variable {Sg : Sig} {Γ : Ctx} {σ τ : TyWf} (G : GlobalEnv Sg.decls)

/-- `let x = e; body` binds the value of `e`. -/
theorem Term.eval_letE {u : Usage Γ} {v : Usage (σ :: Γ)} {ke kb : Head}
    (e : Term Sg Γ u σ ke) (body : Term Sg (σ :: Γ) v τ kb)
    (hValue : ke = .comp ∨ ke = .ctor ∨ ke = .val ∨ ke = .caseIntro) (hUsed : 2 ≤ Usage.head v) (env : Env Γ)
    (he : Term.NoRecMk e) (hb : Term.NoRecMk body) :
    Term.eval G (.letE e body hValue hUsed) env ⟨he, hb⟩ =
      Term.eval G body (Term.eval G e env he, env) hb :=
  rfl

/-- An extern is the Lean function it implements. -/
theorem Term.eval_extern (e : Extern τ) (hq : TyWf.quotable τ = false) (env : Env Γ)
    (h : Term.NoRecMk (Sg := Sg) (.extern e hq)) :
    Term.eval G (.extern e hq) env h = Extern.eval e :=
  rfl

/-- An extern applied to terms is the Lean function called on their values. -/
theorem Term.eval_externCall {σs : List TyWf} {u : Usage Γ} {ks : List Head}
    (args : Spine Sg Γ u σs ks) (call : TyWf.DenList σs → Extern τ)
    (hArgs : Head.allValue ks = false) (env : Env Γ) (h : Spine.NoRecMk args) :
    Term.eval G (.externCall args call hArgs) env h =
      Extern.eval (call (Spine.eval G args env h)) :=
  rfl

/-- An extern that takes a proof, applied to terms whose values satisfy the proposition,
    is the Lean function called on those values, with the proof. -/
theorem Term.eval_externCallChecked_of_some {σs : List TyWf} {u v : Usage Γ}
    {ks : List Head} {kf : Head} (args : Spine Sg Γ u σs ks)
    (call : TyWf.DenList σs → Option (Extern τ)) (fallback : Term Sg Γ v τ kf)
    (hArgs : Head.allValue ks = false) (env : Env Γ)
    (h : Spine.NoRecMk args ∧ Term.NoRecMk fallback) (e : Extern τ)
    (he : call (Spine.eval G args env h.1) = some e) :
    Term.eval G (.externCallChecked args call fallback hArgs) env h = Extern.eval e := by
  show (match call (Spine.eval G args env h.1) with
    | some e => Extern.eval e
    | none => Term.eval G fallback env h.2) = _
  rw [he]

/-- The tag of a tagged value is the constructor it was built with. -/
theorem Term.eval_taggedUnion_mk_fst {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) {u : Usage Γ} {ks : List Head} (fields : Spine Sg Γ u (l.get t ht) ks)
    (env : Env Γ) (hf : Spine.NoRecMk fields) :
    (Term.eval G (.taggedUnion_mk l t ht fields) env hf).1.val = t :=
  rfl

/-- The fields of a tagged value are the ones it was built with. -/
theorem Term.eval_taggedUnion_field? {l : LeanTaggedUnionSchema TyWf} (t : Nat)
    (ht : t < l.length) {u : Usage Γ} {ks : List Head} (fields : Spine Sg Γ u (l.get t ht) ks)
    (env : Env Γ) (hf : Spine.NoRecMk fields) :
    TyWf.DenTU.field? t ht (Term.eval G (.taggedUnion_mk l t ht fields) env hf) =
      some (Spine.eval G fields env hf) :=
  TyWf.DenTU.field?_mk t ht _

end LeanScript

end
