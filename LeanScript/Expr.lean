module
public import LeanScript.ExprCtx
public import LeanScript.Ty
public import LeanScript.LeanInitPureExterns

@[expose] public section

/-!
# `Term`: the one grammar, terminating by construction

## The recursion discipline, and why four of the six kinds are unrepresentable

This grammar admits the first two and **cannot express** the other four:

| kind | in `Term` |
| :-- | :-- |
| structurally recursive | Nat.brecOn? |
| well-founded recursive | `Term.fixAcc` on the transcribed `termination_by` subject |
| partial fixpoint | unrepresentable: there is no constructor for a fixpoint that does not descend |
| coinductive / inductive fixpoint | unrepresentable: `Ty` has no coinductive former and `Term` has no free fixpoint |
| `partial` | unrepresentable: same |
| `unsafe` | unrepresentable: same |

* **No `IO`, and no effect at all.**  `Ty` has no effectful former, and `Externs` is the
  catalogue of the *pure* `@[extern]` functions, so an `IO`-returning declaration has no
  image in this language.
* **No failure.**  Every operation answers with a value:
  1. an exhausted recursion is not possible
  2. an out-of-range index - this is why constructors like .lean_panic_fn_borrowed, .lean_array_get_borrowed etc take `Inhabited X` too
  3. a lookup a schema - no `Ty.dflt`!! schema should be correct-by-construction.
  That is what lets the evaluator be an ordinary total Lean function.
* **`Ty.lazy` is a delay, not a `Thunk`.**  `Term.lazyForce (Term.lazyMk e)` runs `e`, and
  running it twice runs `e` twice: there is no memoisation (for evaluator, this is just for special printing when we will print js).
  Same for `Thunk` `Term.thunkForce (Term.thunkMk e)` runs `e` as ordinary function. This is only for special printing of js in future.
-/

namespace LeanScript.Expr

open LeanScript
open LeanScript.Ty

/-- A terminal type is a type. -/
instance : Coe LeanPrimTy Ty := ⟨Ty.prim⟩

/-- An array/list/task/promise/thunk/lazy of a terminal type is a type. -/
instance : Coe (LeanPrimTyCovariant LeanPrimTy) Ty :=
  ⟨fun c => Ty.primCovariant (c.map Ty.prim)⟩

/-- An array/list/task/promise/thunk/lazy of a type is a type. -/
instance : Coe (LeanPrimTyCovariant Ty) Ty := ⟨Ty.primCovariant⟩

/-- A one-argument function between terminal types, as a `Ty`. -/
abbrev primFn1 (a b : LeanPrimTy) : Ty := .fn (.prim a) (.prim b)

/-- A two-argument (curried) function between terminal types, as a `Ty`. -/
abbrev primFn2 (a b c : LeanPrimTy) : Ty := .fn (.prim a) (.fn (.prim b) (.prim c))

/-- A product of two terminal types, as a `Ty`. -/
abbrev primProd (a b : LeanPrimTy) : Ty := Ty.prod (.prim a) (.prim b)

/-- The one-argument polymorphic externs, at `Ty`. -/
abbrev Extern1At := @LeanInitPureExtern_X_X Ty _ _ _ Ty.option Ty.list primProd

/-- The two-argument polymorphic externs, at `Ty`. -/
abbrev Extern2At := @LeanInitPureExtern_X_X_X Ty _ _ _ Ty.option Ty.list primFn1

/-- The three-argument polymorphic externs, at `Ty`. -/
abbrev Extern3At :=
  @LeanInitPureExtern_X_X_X_X Ty _ _ primFn1 primFn2 Ty.byteArray Ty.floatArray

/-- The four-argument polymorphic externs, at `Ty`. -/
abbrev Extern4At := @LeanInitPureExtern_X_X_X_X_X Ty _ _ Ty.fn

/-- The six-argument polymorphic externs, at `Ty`. -/
abbrev Extern6At := @LeanInitPureExtern_X_X_X_X_X_X Ty Ty.byteArray

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
  | ap  : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ (σ ⇒ τ) → Term Sg Γ Ρ σ → Term Sg Γ Ρ τ
  /-- A constant of a terminal type. -/
  | lit : ∀ {Γ Ρ} {p : LeanPrimTy}, LeanPrimLit p → Term Sg Γ Ρ (.prim p)
  /-- A reference to a top-level declaration of the module's signature. -/
  | global : ∀ {Γ Ρ τ}, GlobalRef Sg.decls τ → Term Sg Γ Ρ τ
  /-- A pure constant of the runtime (`lean_version_get_major`, …).  It carries no
      argument, and the type language has no function type of no arguments, so it is a
      *delayed* value: `Ty.lazy`, which `Term.lazyForce` runs. -/
  | extern_const : ∀ {p : LeanPrimTy}, LeanInitPureExtern_U_T p → Term Sg Γ Ρ (Ty.arrows  [] (Ty.lazy (.prim p))
  /-- A one-argument function between terminal types. -/
  | extern_prim1 : ∀ {a b : LeanPrimTy},
      LeanInitPureExtern_T_T a b → Term Sg Γ Ρ (Ty.arrows  [.prim a] (.prim b)
  /-- A two-argument function between terminal types. -/
  | extern_prim2 : ∀ {a b c : LeanPrimTy},
      LeanInitPureExtern_T_T_T a b c → Term Sg Γ Ρ (Ty.arrows  [.prim a, .prim b] (.prim c)
  /-- A three-argument function between terminal types. -/
  | extern_prim3 : ∀ {a b c d : LeanPrimTy},
      LeanInitPureExtern_T_T_T_T a b c d → Term Sg Γ Ρ (Ty.arrows  [.prim a, .prim b, .prim c] (.prim d)
  /-- A five-argument function between terminal types. -/
  | extern_prim5 : ∀ {a b c d e f : LeanPrimTy}, LeanInitPureExtern_T_T_T_T_T a b c d e f →
      Term Sg Γ Ρ (Ty.arrows  [.prim a, .prim b, .prim c, .prim d, .prim e] (.prim f)
  /-- A one-argument function of the polymorphic catalogue. -/
  | extern_poly1 : ∀ {α β : Ty}, Extern1At α β → Term Sg Γ Ρ (Ty.arrows  [α] β
  /-- A two-argument function of the polymorphic catalogue. -/
  | extern_poly2 : ∀ {α β γ : Ty}, Extern2At α β γ → Term Sg Γ Ρ (Ty.arrows  [α, β] γ
  /-- A three-argument function of the polymorphic catalogue. -/
  | extern_poly3 : ∀ {α β γ δ : Ty}, Extern3At α β γ δ → Term Sg Γ Ρ (Ty.arrows  [α, β, γ] δ
  /-- A four-argument function of the polymorphic catalogue. -/
  | extern_poly4 : ∀ {α β γ δ ε : Ty}, Extern4At α β γ δ ε → Term Sg Γ Ρ (Ty.arrows  [α, β, γ, δ] ε
  /-- A six-argument function of the polymorphic catalogue. -/
  | extern_poly6 : ∀ {α : Ty} {b : LeanPrimTy} {γ : Ty} {d e f : LeanPrimTy} {ζ : Ty},
      Extern6At α b γ d e f ζ →
      Term Sg Γ Ρ (Ty.arrows [α, .prim b, γ, .prim d, .prim e, .prim f] ζ)
  /-- Delay a value.  This is what a Lean `fun (_ : Unit) => e` becomes: the parameter is
      the one value of a unit type, which carries nothing at run time and is erased, so
      what is left is a delayed value — and `Ty.lazy` is exactly that.

      **Unmemoised**: forcing it twice runs it twice. -/
  | lazyMk : ∀ {Γ Ρ τ}, Term Sg Γ Ρ τ → Term Sg Γ Ρ (.lazy τ)
  /-- Run a delayed value: what an application `f ()` becomes once the unit argument is
      erased. -/
  | lazyForce : ∀ {Γ Ρ τ}, Term Sg Γ Ρ (.lazy τ) → Term Sg Γ Ρ τ

  -- TODO: add thunkMk, thunkForce
  /-- `let x = e; body` — `x` is de Bruijn index 0 of `body`. -/
  | letE : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ σ → Term Sg (σ :: Γ) Ρ τ → Term Sg Γ Ρ τ
  /-- `if c then t else e`. -/
  | bool_elim : ∀ {Γ Ρ τ}, -- Other name is if then else
      Term Sg Γ Ρ (.prim .bool) → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ → Term Sg Γ Ρ τ
  /-- A tagged value, built **at a type whose layout says so**.  `h` is the evidence that
      `τ` has a constructor number `i`, and which fields it has; the arguments are then a
      spine of exactly those types.  So a constructor cannot be built at a type that has
      no such constructor, with a field missing, a field too many, the fields in the
      wrong order, or a field of the wrong type. -/
  -- | ctor : ∀ {Γ Ρ τ}, (i : Nat) → (fields : FieldLayout) → -- TODO: need to split on: enum_ctor, record_ctor, taggedUnion_ctor, recTaggedUnion_ctor, recObject_ctor, recAlias_ctor, mutualRecursiveFamily_ctor
  --     (h : τ.ctorFields? i = some fields) → Spine Sg Γ Ρ fields → Term Sg Γ Ρ τ
  /-- A field of a tagged value.  `h` is the evidence that constructor `i` of `σ` has a
      field `j`, *of type `τ`*, so a field the type does not have cannot be read.

      `hOne` is what makes the read **sound**: `σ` has exactly one constructor, so the
      constructor the value was built with is the one this projection speaks about.  A
      field of a type with several constructors is reached by a `Term.caseTag`, whose
      alternative *binds* the fields of the constructor it matches. -/
  -- TODO: proj, tagOf, caseTag - these all are eliminators. But with bad names. Replace with: enum_elim, record_elim, taggedUnion_elim, recTaggedUnion_elim, recObject_elim, recAlias_elim, mutualRecursiveFamily_elim. And those which are recursive should have also recursive eliminator: recTaggedUnion_rec, recObject_rec, recAlias_rec, mutualRecursiveFamily_rec
  -- | proj : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ σ → (i j : Nat) →
  --     (hOne : σ.numCtors? = some 1) →
  --     (h : σ.fieldTy? i j = some τ) → Term Sg Γ Ρ τ
  -- /-- The runtime tag of a value whose type has a layout: how a dispatch tests which
  --     constructor it has. -/
  -- | tagOf : ∀ {Γ Ρ σ}, Term Sg Γ Ρ σ → (h : σ.isTagged = true) → Term Sg Γ Ρ (.prim .nat)
  -- /-- A dispatch on the tag of a value.  An alternative **binds the fields** of the
  --     constructor it matches, in declaration order, so de Bruijn index `0` of its body is
  --     the constructor's first field.  `h` says that every tag branched on is a
  --     constructor of `σ` and that none is repeated, so a case cannot test an impossible
  --     tag; and a case cannot fall off the end of its branches either, because `Alts` ends
  --     *either* in a default branch (`full = false`) *or* in nothing at all with a branch
  --     for every constructor (`full = true`, `Ty.caseOkFull`). -/
  -- | caseTag : ∀ {Γ Ρ σ τ tags full}, Term Sg Γ Ρ σ → Alts Sg Γ Ρ σ τ tags full →
  --     (h : σ.caseOkAlts full tags = true) → Term Sg Γ Ρ τ
  /-- **A block**: the one way a term uses labels.  Its tail is written in the *empty*
      label context, so a block is closed for jumps — a `break` of the target never
      crosses the boundary of the block it is in. -/
  | block : ∀ {Γ Ρ τ}, Tail Sg Γ [] Ρ τ → Term Sg Γ Ρ τ
  /-- **The recursion**, and the only one.

      It carries no measure the front end had to invent: an arbitrary order `r` on an
      arbitrary carrier `α`, the **subject** that descends in it, and `hacc`, the
      termination evidence — a **proof** that the subject is accessible for `r`.  The
      evaluator recurses on that proof (`Acc.rec`), so there is no fuel and nothing to
      consume: the field is a proposition, erased at run time and proof-irrelevant, and a
      translated program still computes in the kernel because `Acc.rec` is a
      large-eliminating recursor and `accNatLt` is transparent.  A structural
      recursion is this node at `<` on `Nat` with `Env.subjectMeasure` as its subject, a
      well-founded one at the subject Lean's own `termination_by` names; neither is a
      separate constructor, and which of the two a recursion is is read off the node
      rather than declared by it.

      `rdec` decides the order, which is what lets the loop of `LeanScript.Eval` re-enter
      exactly at the calls that descend.  `inv` is the invariant the descent is relative
      to, which is where an erased `Prop`-typed precondition of the source function goes;
      a recursion that descends unconditionally takes `fun _ => True`.  `body` is the
      function's body, with the recursion itself in scope as the innermost entry of
      `Ρ`. -/
  | fixAcc : ∀ {Γ Ρ τ} {α : Type}, (ps : List Ty) → (r : α → α → Prop) → -- TODO: I hope this is correct. We should not use fuel, meausures, AccT (like Acc, but in Type), default values. Recursion should not get stuck. Instead - only proof that WF recursion terminates.
      (rdec : DecidableRel r) → (subject : Env ps → α) →
      (hacc : ∀ as : Env ps, Acc r (subject as)) →
      (inv : Env ps → Prop) →
      (body : Term Sg (ps ++ Γ) (⟨ps, τ⟩ :: Ρ) τ) →
      Term Sg Γ Ρ (Ty.arrows ps τ)
  /-- **The one way to recurse**: call a recursion of `Ρ` with a full argument list.
      There is no measure argument, and no syntax for one. -/
  | selfCall : ∀ {Γ Ρ ps τ}, (Ρ ∋ᵣ ⟨ps, τ⟩) → Spine Sg Γ Ρ ps → Term Sg Γ Ρ τ -- TODO: how can we make sure that selfCall is possible only inside of fixApp?

/-- A list of terms, typed by the list of their types: the arguments of an operation, the
    arguments of a jump, the arguments of a self call, the fields of a constructor. -/
inductive Spine (Sg : Sig) : Ctx → RCtx → List Ty → Type 1
  | nil  : ∀ {Γ Ρ}, Spine Sg Γ Ρ []
  | cons : ∀ {Γ Ρ σ σs}, Term Sg Γ Ρ σ → Spine Sg Γ Ρ σs → Spine Sg Γ Ρ (σ :: σs)

/-- The branches of a `Term.caseTag` on a value of type `σ`, keyed by constructor tag and
    indexed by the list of tags they test, in order, and by whether that list is
    **exhaustive**.  An alternative binds the fields of its constructor: its body is
    written in `fields ++ Γ`, and `h` is the evidence that those are exactly the fields
    the layout gives that constructor.

    A list ends either in `Alts.deflt`, a default branch, or — when `full = true` — in
    `Alts.nilFull`, which is only usable at a `Ty.caseOkFull`, i.e. when every constructor
    has a branch of its own.  Either way no dispatch can fall off the end. -/
-- TODO: this is very beautiful and seems like type-safe, but maybe should be split on: AltsEnum, AltsRecord, AltsTaggedUnion, AltsRecTaggedUnion, AltsRecObject, AltsRecAlias, AltsMutualRecursiveFamily. IF!!! it makes sense.
inductive Alts (Sg : Sig) : Ctx → RCtx → Ty → Ty → List Nat → Bool → Type 1
  -- /-- The default branch a dispatch ends with. -/
  -- | deflt : ∀ {Γ Ρ σ τ}, Term Sg Γ Ρ τ → Alts Sg Γ Ρ σ τ [] false -- NOTE: NO DEFAULTS!!!!
  /-- The end of an **exhaustive** dispatch: no default branch, because every constructor
      has a branch of its own (`Ty.caseOkFull`). -/
  | nilFull : ∀ {Γ Ρ σ τ}, Alts Sg Γ Ρ σ τ [] true
  /-- One more branch, binding the fields of the constructor it matches. -/
  | cons  : ∀ {Γ Ρ σ τ tags full}, (tag : Nat) → (fields : FieldLayout) →
      (h : σ.ctorFields? tag = some fields) →
      Term Sg (fields ++ Γ) Ρ τ → Alts Sg Γ Ρ σ τ tags full →
      Alts Sg Γ Ρ σ τ (tag :: tags) full

/-- A **tail**: a basic block of the block grammar, in the variable context `Γ`, the label
    context `Ω` and the recursion context `Ρ`, answering with `τ`.  Every position of a
    `Tail` is a tail position of the enclosing `Term.block`, which is why a jump is
    allowed here and nowhere else. -/
inductive Tail (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Type 1
  /-- Answer with this value: the block is done. -/
  | ret : ∀ {Γ Ω Ρ τ}, Term Sg Γ Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- Jump to a join point in scope, with one argument per parameter.  A jump never comes
      back, so it stands at **any** answer type: it is the whole of the rest of this
      block. -/
  | jmp : ∀ {Γ Ω Ρ ps τ}, Ω ∋ₗ ps → Spine Sg Γ Ρ ps → Tail Sg Γ Ω Ρ τ
  /-- `let x = e;` in front of the rest of the block. -/
  | letT : ∀ {Γ Ω Ρ σ τ}, Term Sg Γ Ρ σ → Tail Sg (σ :: Γ) Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A two-way branch, both arms being blocks. -/
  | iteT : ∀ {Γ Ω Ρ τ},
      Term Sg Γ Ρ (.prim .bool) → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ → Tail Sg Γ Ω Ρ τ
  /-- A dispatch on the tag of a value, every arm being a block. -/
  | caseT : ∀ {Γ Ω Ρ σ τ tags full}, Term Sg Γ Ρ σ → AltsT Sg Γ Ω Ρ σ τ tags full →
      (h : σ.caseOkAlts full tags = true) → Tail Sg Γ Ω Ρ τ
  /-- **A join point**, taking the arguments `ps`, in scope in `rest` as label index `0`.

      Its `body` is typed in the *outer* label context `Ω`, so it cannot jump back to
      itself — control passes through it once per jump (`l: { … }` with `break l` in the
      target).  There is no loop here, and none can be written: repeating work is
      `Term.fixAcc` and nothing else.

      Inside `body`, de Bruijn index `0` is the **first** argument of the join point,
      i.e. the variable context is `ps ++ Γ`. -/
  | join : ∀ {Γ Ω Ρ τ}, (ps : List Ty) →
      (body : Tail Sg (ps ++ Γ) Ω Ρ τ) →
      (rest : Tail Sg Γ (ps :: Ω) Ρ τ) → Tail Sg Γ Ω Ρ τ

/-- The branches of a `Tail.caseT`: `Alts`, with a block in place of each term, so that a
    branch may answer *or* jump. -/
-- TODO: same as Alts
inductive AltsT (Sg : Sig) : Ctx → LCtx → RCtx → Ty → Ty → List Nat → Bool → Type 1
  /-- The default branch a dispatch ends with. -/
  | deflt : ∀ {Γ Ω Ρ σ τ}, Tail Sg Γ Ω Ρ τ → AltsT Sg Γ Ω Ρ σ τ [] false
  /-- The end of an **exhaustive** dispatch: no default branch. -/
  | nilFull : ∀ {Γ Ω Ρ σ τ}, AltsT Sg Γ Ω Ρ σ τ [] true
  /-- One more branch, binding the fields of the constructor it matches. -/
  | cons : ∀ {Γ Ω Ρ σ τ tags full}, (tag : Nat) → (fields : FieldLayout) →
      (h : σ.ctorFields? tag = some fields) →
      Tail Sg (fields ++ Γ) Ω Ρ τ → AltsT Sg Γ Ω Ρ σ τ tags full →
      AltsT Sg Γ Ω Ρ σ τ (tag :: tags) full

end

end LeanScript.Expr

end
