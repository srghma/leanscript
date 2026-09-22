module
public import LeanScript.ExprCtx
public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

/-!
# `Term`: the one grammar, terminating by construction

## The recursion discipline, and why four of the six kinds are unrepresentable

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | `Term.fixAcc` at `<` on `Nat`, with the structural measure as its subject |
| well-founded recursive | `Term.fixAcc` on the transcribed `termination_by` subject |
| partial fixpoint | unrepresentable: there is no constructor for a fixpoint that does not descend |
| coinductive / inductive fixpoint | unrepresentable: `Ty` has no coinductive former and `Term` has no free fixpoint |
| `partial` | unrepresentable: same |
| `unsafe` | unrepresentable: same |

* **No `IO`, and no effect at all.**  `Ty` has no effectful former, so an `IO`-returning
  declaration has no image in this language.

* **No failure.**  Every operation answers with a value, which is what lets the evaluator
  of `LeanScript.Eval` be an ordinary total Lean function into `τ.den`:
  1. an exhausted recursion is not possible — see `Term.fixAcc` below;
  2. an out-of-range index is not possible: a constructor is a *number with a proof* that
     the type has it, and a field is read by an eliminator that *binds* the fields of the
     constructor it matched, never by a lookup;
  3. a schema is never consulted for a default — there is no `Ty.dflt`.

* **A delay is not a memo cell.**  `Term.lazyForce (Term.lazyMk e)` runs `e`, and
  running it twice runs `e` twice: there is no memoisation.  `LeanScript.Den` makes
  `Ty.lazy` the identity on values — at this layer a delay carries nothing beyond the
  value, and the wrapper only decides what JavaScript is printed later.  `Ty.thunk`,
  which *is* memoised in JavaScript, has `Term.thunkMk` and `Term.thunkForce`: they
  denote the same identity, and the difference between the two wrappers is the code
  printed for them, not the value.  `task` and `promise` are commented out of
  `LeanPrimTyCovariant`.

## Primitive operations

`Term.prim` applies a **total Lean function** to the values of its arguments.  That is
what a pure `@[extern]` function of the Lean runtime is: `LeanScript.LeanInitPureExterns`
is the catalogue of exactly which functions a front end is allowed to name here, and
`Term.prim` is how one of them is applied to *subterms* rather than to values already in
hand.  The evaluator stays total because a Lean function is total.
-/

namespace LeanScript.Expr

open LeanScript

/-- A delay denotes the identity: `Ty.lazy τ` and `τ` have the same values, and the
    wrapper only decides the JavaScript that is printed later. -/
theorem den_lazy (τ : Ty) : (Ty.lazy τ).den = τ.den := rfl

/-- A thunk denotes the identity too: `Ty.thunk τ` and `τ` have the same values, and
    what the wrapper decides is that the JavaScript printed for it *memoises*. -/
theorem den_thunk (τ : Ty) : (Ty.thunk τ).den = τ.den := rfl

/-! ## The fields of a constructor of a recursive tagged union

A recursive declaration is a fixed point taken over *descriptions* (`FDesc`), so the
fields of one of its constructors are described rather than typed: a field is
`FDesc.selfD 0` — an occurrence of the declaration itself — rather than a `Ty`, because
the `Ty` it would be is the one being defined.  `RecFlds` is the bridge: it reads a list
of descriptions and says which `Ty` each field has, so that a constructor takes an
ordinary `Spine` and a branch binds ordinary variables.

It covers the two field shapes that are built and taken apart here — a terminal field,
and an occurrence of the declaration — and there is deliberately no case for the
others: a declaration with a field the language has no `Ty` for is refused rather than
approximated. -/

/-- Which `Ty` each field of a constructor of the recursive tagged union `l` has.  The
    list of descriptions is the constructor's, and the list of types is the context a
    branch of the eliminator binds, in field order. -/
inductive RecFlds (l : LeanTaggedUnionSchemaSealed) : List FDesc → List Ty → Type where
  /-- The constructor has no more fields. -/
  | nil : RecFlds l [] []
  /-- One more field, of a terminal type. -/
  | prim : ∀ {p : LeanPrimTy} {ds σs}, RecFlds l ds σs →
      RecFlds l (.primD p :: ds) (.prim p :: σs)
  /-- One more field, an occurrence of the declaration itself. -/
  | self : ∀ {ds σs}, RecFlds l ds σs →
      RecFlds l (.selfD 0 :: ds) (.recTaggedUnion l :: σs)

/-! ## Terms -/

mutual

/-- A well-scoped, simply-typed term of the module whose signature is `Sg`, in the
    variable context `Γ` and the recursion context `Ρ`.  A term has **no** label context:
    a jump is a `Tail`, never a `Term`, so no value position of the language can hold
    one. -/
inductive Term (Sg : Sig) : Ctx → RCtx → Ty → Type 1
  /-- A variable of `Γ`. -/
  | var : ∀ {Γ Ρ τ}, Γ ∋ τ → Term Sg Γ Ρ τ
  /-- `fun x => body`: **one** parameter, since every function is curried. -/
  | lam : ∀ {Γ Ρ σ τ}, Term Sg (σ :: Γ) Ρ τ → Term Sg Γ Ρ (σ ⇒ τ)
  /-- `f a`: **one** argument. -/
  | ap : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ (σ ⇒ τ) → Term Sg Γ Ρ σ → Term Sg Γ Ρ τ
  /-- A constant of a terminal type. -/
  | lit : ∀ {Γ Ρ} (p : LeanPrimTy), p.denote → Term Sg Γ Ρ (.prim p)
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ Ρ τ}, GlobalRef Sg.decls τ → Term Sg Γ Ρ τ
  /-- `let x = e; body` — `x` is de Bruijn index `0` of `body`. -/
  | letE : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ σ → Term Sg (σ :: Γ) Ρ τ → Term Sg Γ Ρ τ
  /-- `if c then t else e`. -/
  | bool_elim : ∀ {Γ Ρ τ},
      Term Sg Γ Ρ (.prim .bool) → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes once the one
      value of the unit type is erased.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazyMk : ∀ {Γ Ρ τ}, Term Sg Γ Ρ τ → Term Sg Γ Ρ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazyForce : ∀ {Γ Ρ τ}, Term Sg Γ Ρ (.lazy τ) → Term Sg Γ Ρ τ
  /-- Delay a value and remember it: a `Thunk`.

      **Memoised**: the JavaScript printed for it runs the body at the first force and
      answers with the stored value afterwards.  Forcing it is `Term.thunkForce`.  At
      this layer the distinction from `Term.lazyMk` is not visible — a `Term` is a total
      Lean function of its environment, so running the body twice gives the same answer
      as running it once — and what it decides is the code that is printed. -/
  | thunkMk : ∀ {Γ Ρ τ}, Term Sg Γ Ρ τ → Term Sg Γ Ρ (.thunk τ)
  /-- Force a thunk: the value it stands for, computed at most once. -/
  | thunkForce : ∀ {Γ Ρ τ}, Term Sg Γ Ρ (.thunk τ) → Term Sg Γ Ρ τ
  /-- **A primitive operation**: a total Lean function of the values of its arguments.
      This is how a pure `@[extern]` function of the runtime is applied to subterms; the
      catalogue of the ones a front end may name is `LeanScript.LeanInitPureExterns`. -/
  | prim : ∀ {Γ Ρ τ} (args : List Ty), (Tup (Ty.denList args) → τ.den) →
      Spine Sg Γ Ρ args → Term Sg Γ Ρ τ
  /-- A constructor of an enum: its **number**, which is what the runtime holds. -/
  | enum_mk : ∀ {Γ Ρ} (s : LeanEnumSchema), Fin s.nOfConstructors → Term Sg Γ Ρ (.enum s)
  /-- A dispatch on an enum: one branch per constructor, and no default, so it cannot
      fall off the end. -/
  | enum_elim : ∀ {Γ Ρ τ} {s : LeanEnumSchema},
      Term Sg Γ Ρ (.enum s) → EnumCases Sg Γ Ρ τ s.nOfConstructors → Term Sg Γ Ρ τ
  /-- A record, from its fields, in declaration order. -/
  | record_mk : ∀ {Γ Ρ} (fs : LeanRecordSchema Ty),
      Spine Sg Γ Ρ fs.toList → Term Sg Γ Ρ (.record fs)
  /-- The eliminator of a record: it **binds** every field, in declaration order, so de
      Bruijn index `0` of the body is the record's first field.  A projection is this
      node followed by a variable. -/
  | record_elim : ∀ {Γ Ρ τ} {fs : LeanRecordSchema Ty},
      Term Sg Γ Ρ (.record fs) → Term Sg (fs.toList ++ Γ) Ρ τ → Term Sg Γ Ρ τ
  /-- A tagged value: constructor `t` of the union — a number **with the proof that the
      union has it** — and exactly that constructor's fields. -/
  | taggedUnion_mk : ∀ {Γ Ρ} (l : LeanTaggedUnionSchema Ty) (t : Nat)
      (ht : t < l.toList.length),
      Spine Sg Γ Ρ (l.toList[t]'ht) → Term Sg Γ Ρ (.taggedUnion l)
  /-- The eliminator of a tagged union: one branch per constructor, each binding that
      constructor's fields, and no default. -/
  | taggedUnion_elim : ∀ {Γ Ρ τ} {l : LeanTaggedUnionSchema Ty},
      Term Sg Γ Ρ (.taggedUnion l) → Cases Sg Γ Ρ l.toList τ → Term Sg Γ Ρ τ
  /-- **A block**: the one way a term uses labels.  Its tail is written in the *empty*
      label context, so a block is closed for jumps. -/
  | block : ∀ {Γ Ρ τ}, Tail Sg Γ [] Ρ τ → Term Sg Γ Ρ τ
  /-- **The recursion**, and the only one.

      It carries no measure the front end had to invent: an arbitrary order `r` on an
      arbitrary carrier, the **subject** that descends in it, and `hacc`, the termination
      evidence — a proof that the subject of *every* argument tuple is accessible for
      `r`.  The evaluator recurses on that proof (`Acc.rec`), so there is no fuel and
      nothing to consume: the field is a proposition, erased at run time.

      A self call (`Term.selfCall`) re-enters the recursion only at an argument tuple
      whose subject is `r`-below the current one, and `rdec` is what *computes that
      proof* at the call: it is the descent evidence, not a test with two outcomes to
      program for.  **There is no field for a call that does not descend**: the node
      carries no default value of `τ`, no fuel and no measure a front end had to invent.
      What a recursion means is `LeanScript.EvalProof`, where running it needs a proof
      that its self calls descend and nothing else.

      `hne` is the one thing a *junk-completed* run of a term whose calls have **not**
      been proved to descend needs — that `τ` has some value at all, which is a
      proposition, not a chosen value.  `LeanScript.Eval` is that run; nothing in the
      language, and nothing a backend prints, reads it.

      `inv` is the invariant the descent is relative to, which is where an erased
      `Prop`-typed precondition of the source declaration goes; a recursion that descends
      unconditionally takes `fun _ => True`. -/
  | fixAcc : ∀ {Γ Ρ τ} {α : Type} (ps : List Ty) (r : α → α → Prop),
      DecidableRel r → (subject : Env ps → α) →
      (hacc : ∀ as : Env ps, Acc r (subject as)) →
      (inv : Env ps → Prop) →
      (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      (hne : Nonempty τ.den) →
      Term Sg Γ Ρ (Ty.arrows ps τ)
  /-- **The one way to recurse**: call a recursion of `Ρ` with a full argument list.
      There is no measure argument, and no syntax for one — a `Ρ` entry is only ever
      bound by `Term.fixAcc`, so a self call outside a recursion cannot be written. -/
  | selfCall : ∀ {Γ Ρ ps τ}, (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Term Sg Γ Ρ τ
  /-- A value of a **recursive** tagged union: constructor `t` — a number with the proof
      that the declaration has it — and exactly that constructor's fields, whose types
      `RecFlds` reads off the constructor's descriptions.  Only *one* level is built
      here; the recursion is in the fields, which are terms of the declaration's own
      type. -/
  | recTU_mk : ∀ {Γ Ρ} (l : LeanTaggedUnionSchemaSealed) (t : Nat),
      t < (RTy.fdescTU l.schema).length → ∀ {σs : List Ty},
      RecFlds l ((RTy.fdescTU l.schema).getD t []) σs →
      Spine Sg Γ Ρ σs → Term Sg Γ Ρ (.recTaggedUnion l)
  /-- The eliminator of a recursive tagged union: one branch per constructor, each
      binding that constructor's fields, and no default.  It takes the value **one level**
      apart; a recursion over the whole of one is `Term.fixAcc` descending at
      `Mu.size`. -/
  | recTU_elim : ∀ {Γ Ρ τ} {l : LeanTaggedUnionSchemaSealed},
      Term Sg Γ Ρ (.recTaggedUnion l) → RecCases Sg Γ Ρ l (RTy.fdescTU l.schema) τ →
      Term Sg Γ Ρ τ

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    arguments of a jump, the arguments of a self call, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → RCtx → List Ty → Type 1
  /-- No more arguments. -/
  | nil : ∀ {Γ Ρ}, Spine Sg Γ Ρ []
  /-- One more argument. -/
  | cons : ∀ {Γ Ρ σ σs}, Term Sg Γ Ρ σ → Spine Sg Γ Ρ σs → Spine Sg Γ Ρ (σ :: σs)

/-- The branches of a dispatch, one per constructor, in constructor order.  A branch
    **binds the fields** of its constructor, in declaration order, so de Bruijn index `0`
    of its body is that constructor's first field.  There is no default branch and no
    end-of-list before the constructors run out, so a dispatch is exhaustive by
    construction. -/
inductive Cases (Sg : Sig) : Ctx → RCtx → List (List Ty) → Ty → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ Ρ τ}, Cases Sg Γ Ρ [] τ
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ Ρ fs rest τ},
      Term Sg (fs ++ Γ) Ρ τ → Cases Sg Γ Ρ rest τ → Cases Sg Γ Ρ (fs :: rest) τ

/-- The branches of a dispatch on a recursive tagged union, one per constructor, in
    constructor order.  A branch binds the fields of its constructor, at the types
    `RecFlds` reads off their descriptions. -/
inductive RecCases (Sg : Sig) : Ctx → RCtx → (l : LeanTaggedUnionSchemaSealed) →
    List (List FDesc) → Ty → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ Ρ l τ}, RecCases Sg Γ Ρ l [] τ
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ Ρ l ds σs rest τ}, RecFlds l ds σs → Term Sg (σs ++ Γ) Ρ τ →
      RecCases Sg Γ Ρ l rest τ → RecCases Sg Γ Ρ l (ds :: rest) τ

/-- The branches of a dispatch on an enum: `n` of them, binding nothing. -/
inductive EnumCases (Sg : Sig) : Ctx → RCtx → Ty → Nat → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ Ρ τ}, EnumCases Sg Γ Ρ τ 0
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ Ρ τ n},
      Term Sg Γ Ρ τ → EnumCases Sg Γ Ρ τ n → EnumCases Sg Γ Ρ τ (n + 1)

/-- A **tail**: a basic block of the block grammar, answering with `τ`.  Every position of
    a `Tail` is a tail position of the enclosing `Term.block`, which is why a jump is
    allowed here and nowhere else. -/
inductive Tail (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Type 1
  /-- Answer with this value: the block is done. -/
  | ret : ∀ {Γ Ω Ρ τ}, Term Sg Γ Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- Jump to a join point in scope, with one argument per parameter. -/
  | jmp : ∀ {Γ Ω Ρ ps τ}, Ω ∋ₗ ps → Spine Sg Γ Ρ ps → Tail Sg Γ Ω Ρ τ
  /-- `let x = e;` in front of the rest of the block. -/
  | letT : ∀ {Γ Ω Ρ σ τ}, Term Sg Γ Ρ σ → Tail Sg (σ :: Γ) Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A two-way branch, both arms being blocks. -/
  | iteT : ∀ {Γ Ω Ρ τ},
      Term Sg Γ Ρ (.prim .bool) → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A dispatch on a tagged union, every arm being a block. -/
  | caseT : ∀ {Γ Ω Ρ τ} {l : LeanTaggedUnionSchema Ty},
      Term Sg Γ Ρ (.taggedUnion l) → CasesT Sg Γ Ω Ρ l.toList τ → Tail Sg Γ Ω Ρ τ
  /-- A dispatch on an enum, every arm being a block. -/
  | enumCaseT : ∀ {Γ Ω Ρ τ} {s : LeanEnumSchema},
      Term Sg Γ Ρ (.enum s) → EnumCasesT Sg Γ Ω Ρ τ s.nOfConstructors → Tail Sg Γ Ω Ρ τ
  /-- **A join point**, taking the arguments `ps`, in scope in `rest` as label index `0`.

      Its `body` is typed in the *outer* label context `Ω`, so it cannot jump back to
      itself — control passes through it once per jump.  There is no loop here, and none
      can be written: repeating work is `Term.fixAcc` and nothing else. -/
  | join : ∀ {Γ Ω Ρ τ} (ps : List Ty),
      (body : Tail Sg (ps ++ Γ) Ω Ρ τ) →
      (rest : Tail Sg Γ (ps :: Ω) Ρ τ) → Tail Sg Γ Ω Ρ τ

/-- The branches of a `Tail.caseT`: `Cases`, with a block in place of each term, so that
    a branch may answer *or* jump. -/
inductive CasesT (Sg : Sig) : Ctx → LCtx → RCtx → List (List Ty) → Ty → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ Ω Ρ τ}, CasesT Sg Γ Ω Ρ [] τ
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ Ω Ρ fs rest τ}, Tail Sg (fs ++ Γ) Ω Ρ τ → CasesT Sg Γ Ω Ρ rest τ →
      CasesT Sg Γ Ω Ρ (fs :: rest) τ

/-- The branches of a `Tail.enumCaseT`. -/
inductive EnumCasesT (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Nat → Type 1
  /-- Every constructor has a branch. -/
  | nil : ∀ {Γ Ω Ρ τ}, EnumCasesT Sg Γ Ω Ρ τ 0
  /-- The branch of the next constructor. -/
  | cons : ∀ {Γ Ω Ρ τ n}, Tail Sg Γ Ω Ρ τ → EnumCasesT Sg Γ Ω Ρ τ n →
      EnumCasesT Sg Γ Ω Ρ τ (n + 1)

end

end LeanScript.Expr

end
