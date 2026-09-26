# Proposal: `class LeanScriptTyCtor` and `deriving LeanScriptTyCtor`

> **Status: proposal only.** None of this is implemented yet. The Lean in this note is a
> sketch of the design and has not been compiled. The one fact that *was* checked against
> Lean is in §1.2. §9 lists the decisions I need from you before implementing.

The goal is to make this work (from `TermTests/InductiveTypesTest/Existentials.lean`):

```lean
mutual
  inductive Process (α : Type) : Type 1 where
    | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat) : Process α
    | step (State : Type) (seed : State) (trans : State → ProcessOption α State) : Process α
  inductive ProcessOption (α : Type) : Type → Type 1 where
    | none {State : Type} : ProcessOption α State
    | some {State : Type} (nextState : State) (value : α) (proc : Process α) : ProcessOption α State
end

-- stays an error: there is still no *structural* tree for `Process`
deriving instance LeanScriptTyWf for Process, ProcessOption

deriving instance LeanScriptTyCtor for Process, ProcessOption

def mixedProcess_term   := #leanscript_to_term mixedProcess
def varyingProcess_term := #leanscript_to_term varyingProcess
```

---

## 1. What the problem is

### 1.1 A `Term` must have a type, and `Process Nat` has none

`Term Sg Γ τ` is indexed by `τ : TyWf`. For `mixedProcess_term` to type-check, **`Process Nat`
needs a `TyWf`**. Today `LeanScriptTyWf` refuses it, and it has to: a structural `Ty` for
`Process` would need an existential binder (`∃ State. State × (State ⇒ …)`). It would also
need *type-level application* of a family member, because `ProcessOption α` is a type
*operator* (`Type → Type 1`), and `Process` uses it at the bound variable `State`. That is
non-regular recursion, which `Ty.mutualRecursiveFamily` cannot express.

> **Correction.** An earlier version of this section suggested that `mixedProcess` itself
> could not be described. That was wrong. `mixedProcess` and `varyingProcess` are closed values,
> so every witness they use is known, and both can be written today as ordinary records,
> tagged unions and functions. At each constructor application the existential is replaced by
> that application's witness. Where values built with different witnesses meet (the `if` in
> `varyingProcess`), each one is injected into a tagged union with one constructor per layout.
> This is done by hand as `ProcessModel.mixedProcess_term` and
> `ProcessModel.varyingProcess_term` in `TermTests/InductiveTypesTest/Existentials.lean`, and
> checked by `rfl` against what the definitions compute. What these terms do *not* give is
> one type shared by **every** value of `Process Nat`: their types depend on the value. For
> example, a function `Nat → Process Nat` whose result has a different witness for each
> `n` has no finite union of layouts. The rest of this note is about that shared type.
>
> **Update.** The per-constructor half of this proposal now exists as `#leanscript_ctor I c`
> (`LeanScript/CtorFn.lean`): a term elaborator that generates, once, and caches the
> constructor function of any datatype — the type arguments as `TyWf`s (parameters, type
> indices and existentials), a `TyWf` for each field type the language has no tree for (the
> recursive occurrences), then the fields as `Term`s — together with its layout
> (`#leanscript_layout I c`). `ProcessModel` in `TermTests/InductiveTypesTest/Existentials.lean`
> now builds both terms with it. The shared type of §2 is still not implemented.

So a class with *only* "constructor functions" is not enough. We also need a type for the
values those functions return. Most of this proposal is about picking that type (§2).
Once it exists, the class you described follows directly.

### 1.2 Should `ctorTy` be `Fin nOfCtors → Ty` or `Fin nOfCtors → Type`? Neither, as stated

* **`Fin n → Type`** does not typecheck. `Process.step : (State : Type) → State → … → Process α`
  lives in `Type 1`, because it quantifies over `Type`. Even at `Type 1` it would not help:
  `Term` is indexed by `TyWf`, not by Lean types, so a Lean type cannot be the type of a
  `Term`. Also, the Lean type of a constructor is already available (`inferType Process.step`),
  so storing it adds nothing.
* **`Fin n → Ty`** cannot express `Process.step`. Its type depends on the type argument
  `State`, and `Ty` has no `∀`.

What the constructor really has is a type **with holes**: a telescope of type binders
followed by field types that may mention them. I propose
`ctorSig : Fin nOfCtors → CtorSig` (§3.2), where

```lean
structure CtorSig where
  nExists : Nat      -- the type binders the result does not mention (`State`, `HaltedState`)
  fields  : List Ty  -- written over the type variables `params ++ exists` (`Ty.tyVar k`)
```

This is `Fin n → Ty` generalised by "`n` holes". A constructor without existentials
(`nExists = 0`, no `tyVar`) is exactly `Fin n → List Ty`.

Checked in Lean: `ProcessOption` has `numParams = 1` (`α`) and `numIndices = 1`. `State` is
an **index** and a constructor *field* of `ProcessOption.some` (`numFields = 4`), while in
`Process.step` it is an *existential* field (`numFields = 3`). The deriver must tell these
two apart (§5.1).

### 1.3 "`Fin nOfCtors → Term`, but dependent"

The dependency is on the choice of the existential types. The function I propose is

```lean
ctorMk : (i : Fin nOfCtors) → (xs : Vector TyWf (ctorSig i).nExists) →
         Spine Sg Γ ((ctorSig i).fieldTys params xs) → Term Sg Γ selfTy
```

The existential types are **meta-level** arguments: `TyWf` values that the translator picks
at each call site (`State := Nat`, then `String`, then `Bool`). They are not type
abstraction *inside* `Term`, so `Term` does not become System F.

---

## 2. The type of an existentially typed value: three options

| | idea | cost | eliminator later |
| :-- | :-- | :-- | :-- |
| **A. nominal leaf** (recommended) | `Ty.named (name : String) (args : List Ty)`: `Process Nat` is `.named "Process" [.prim .nat]`. The constructors live in a *declaration* (`TyDecl`), not in the tree. | small: one leaf, one `tyVar` leaf used only inside declarations, and one `Term` constructor | needs `Sg` to register the declaration (§7) |
| B. structural `∃` | add `Ty.exists`, `Ty.tyVar` and type application of family members to `Ty`; `Process` gets a real tree | large: substitution under two kinds of binders, a new `Wf`, `TyWfIn` with two scopes, non-regular families, `Den` on `∃` (it breaks structural recursion) | falls out of the tree |
| C. HOAS | `CtorSig.fields : (Fin k → TyWf) → List TyWf`, a Lean function | smallest | `Ty`/`Sig` lose `BEq`/`DecidableEq` (functions inside), which goes against the last task |

**Recommendation: A.**
* It is nominal, so recursion goes *by name*. `Process` mentions `.named "ProcessOption" [α, State]`
  and `ProcessOption` mentions `.named "Process" [α]`. There is no μ-binder, no hoisting, and
  no non-regular family.
* It leaves the existing structural machinery alone.
* The `LeanScriptTyWf` refusal stays true. "`Process` has no (structural) `Ty`" remains
  correct: `Process` gets a *nominal* type only through `LeanScriptTyCtor`.
* It keeps first-order data with `DecidableEq` everywhere.

Rest of this note assumes A.

---

## 3. New definitions

Layout follows your "one child file per import" rule. Nothing imports an aggregator.
**The class has to sit after `Term`**, because it mentions `Term`. Putting it next to
`Ty/Class.lean` would recreate the circular import you hit before.

| file | contents |
| :-- | :-- |
| `LeanScript/Ty/Ty.lean` | two new leaves: `Ty.named`, `Ty.tyVar` (+ the `beq` cases) |
| `LeanScript/Ty/Wf.lean` | `Wf` for `.named` (all args `Wf`); `.tyVar` is **never** `Wf` in a closed scope |
| `LeanScript/Ty/TyVars.lean` (new) | `Ty.WfTv k` (well-formed with type variables `< k`), `Ty.instTyVars`, and the lemma `WfTv k t → (∀ a ∈ as, Wf a) → as.length = k → Wf (t.instTyVars as)`. It is the analogue of `Ty.wf_substOcc` in `WfSubst.lean`. |
| `LeanScript/Ty/TyDecl.lean` (new) | `CtorSig`, `TyDecl`, `TyDecl.selfTy`, `CtorSig.fieldTys` |
| `LeanScript/Expr/Term.lean` | one constructor `Term.named_mk` |
| `LeanScript/Expr/CtorClass.lean` (new) | `class LeanScriptTyCtor` |
| `LeanScript/Ty/Deriving/Ctor.lean` (new) | the deriver |
| `LeanScript/ToTerm/Trans.lean`, `TyView.lean` | use the instance (§6) |

### 3.1 Two new leaves in `Ty`

```lean
inductive Ty where
  …
  /-- A type declared by name (`LeanScript.TyDecl`), applied to type arguments. It is the
      type of values of a type that has existentially typed fields. -/
  | named : String → List Ty → Ty
  /-- Type variable `k` of the declaration it is written in: a parameter, a uniform index,
      or an existential of the constructor. It only appears inside a `TyDecl`. -/
  | tyVar : Nat → Ty
```

`Ty.named` args are ordinary children. `Ty.children`, `Ty.beq`, `TyBEq` (`LawfulBEq`,
`DecidableEq`) and `ty_wf` each get one case per leaf. `Ty.Den (.named _ _) := PEmpty`,
the same as every recursive shape today (see `LeanScript/Den.lean`). So a `named_mk` term
is outside the fragment `Term.eval` runs (`Term.NoRecMk`), and its type is checked but it
is not evaluated, as with lists now.

### 3.2 Declarations

```lean
structure CtorSig where
  name    : String
  nExists : Nat
  fields  : List Ty                 -- over `nParams + nExists` type variables
  deriving BEq, DecidableEq, ReflBEq, LawfulBEq

structure TyDecl where
  name     : String
  nParams  : Nat                    -- Lean params + uniform indices
  ctors    : List CtorSig
  h_ctors_ne  : ctors ≠ [] := by decide
  h_fields_wf : ∀ c ∈ ctors, ∀ f ∈ c.fields, Ty.WfTv (nParams + c.nExists) f := by ty_wf
  deriving BEq, DecidableEq   -- proofs are props, so this works as for `TyWf`

/-- `Process α` at `α := a`. -/
def TyDecl.selfTy (d : TyDecl) (args : List TyWf) (h : args.length = d.nParams := by decide) :
    TyWf := ⟨.named d.name (args.map (·.toTy)), …⟩

/-- The fields of constructor `c` at parameters `ps` and existentials `xs`: the
    declaration's field types with the type variables instantiated, each one a `TyWf`
    by the lemma in `TyVars.lean`. -/
def CtorSig.fieldTys (c : CtorSig) (ps : List TyWf) (xs : Vector TyWf c.nExists) … : List TyWf
```

For the example (params `α` = `tyVar 0`; for `ProcessOption`, `State` = `tyVar 1`):

```
Process        nParams = 1
  halt   nExists = 1  fields = [tyVar 1 ⇒ nat]
  step   nExists = 1  fields = [tyVar 1, tyVar 1 ⇒ named "ProcessOption" [tyVar 0, tyVar 1]]
ProcessOption  nParams = 2          -- α, and the uniform index State
  none   nExists = 0  fields = []
  some   nExists = 0  fields = [tyVar 1, tyVar 0, named "Process" [tyVar 0]]
```

### 3.3 One new `Term` constructor

```lean
  /-- Constructor `i` of the declared type `d`, at parameters `ps` and at the existential
      types `xs` chosen for this value. The witnesses are erased at run time: the value is
      `{ tag: i, _1: …, _2: … }`, like any other constructor. -/
  | named_mk {Γ : Ctx} (d : TyDecl) (ps : List TyWf) (hps : ps.length = d.nParams)
      (i : Fin d.ctors.length) (xs : Vector TyWf (d.ctors.get i).nExists)
      (fields : Spine Sg Γ ((d.ctors.get i).fieldTys ps xs)) :
      Term Sg Γ (d.selfTy ps hps)
```

### 3.4 The class

```lean
/-- The Lean types whose constructors the language can build. For an existentially typed
    type the model is nominal (`Ty.named`); for any other type it is the type's own tree. -/
class LeanScriptTyCtor (α : Type u) where
  /-- The type of the values: `.named "Process" [nat]`, or the structural tree. -/
  selfTy            : TyWf
  nOfCtors          : Nat
  h_nOfCtors_neZero : nOfCtors ≠ 0
  /-- The constructor's type, with holes for its existential types (§1.2). -/
  ctorSig           : Fin nOfCtors → CtorSig
  /-- Its fields at a choice of existential types (params are already fixed by `α`). -/
  ctorFieldTys      : (i : Fin nOfCtors) → Vector TyWf (ctorSig i).nExists → List TyWf
  /-- The constructor, as a builder: this is "`Fin nOfCtors → Term`, dependent". -/
  ctorMk            : (i : Fin nOfCtors) → (xs : Vector TyWf (ctorSig i).nExists) →
                      {Sg : Sig} → {Γ : Ctx} →
                      Spine Sg Γ (ctorFieldTys i xs) → Term Sg Γ selfTy

/-- The curried function form (`Process.step` as a value, e.g. under `List.map`), derived
    once from `ctorMk` by `lam`s. -/
def LeanScriptTyCtor.ctorFn [LeanScriptTyCtor α] (i) (xs) : Term Sg Γ (fields ⇒ … ⇒ selfTy)
```

* `h_nOfCtors_neZero` could be `[NeZero nOfCtors]`. Either works; the field matches what you
  asked for.
* `nOfCtors ≠ 0` does **not** mean the type has values (`inductive Bad | mk : Bad → Bad`).
  The deriver should also refuse a declaration none of whose constructors can be built
  without first having a value of it. This is the usual least-fixed-point check; an
  existential type variable counts as inhabited, because a witness can always be chosen.
* An existential witness must itself have a tree: `tyWfOf Nat`, or the `selfTy` of another
  `LeanScriptTyCtor` type, so `Process (Process Nat)` works too. `TyView.treeOfType` falls
  back to `LeanScriptTyCtor.selfTy` when there is no `LeanScriptTyWf` instance.

---

## 4. What the deriver emits

`deriving instance LeanScriptTyCtor for Process, ProcessOption` adds:

| name | what |
| :-- | :-- |
| `Process.leanScriptTyDecl : TyDecl` | the declaration of §3.2, with `h_fields_wf` proved **once** as a `theorem` |
| `Process.leanScriptCtor_halt`, `Process.leanScriptCtor_step` | one closed `def` per constructor: `fun ps xs spine => Term.named_mk Process.leanScriptTyDecl ps _ i xs spine` |
| `Process.instLeanScriptTyCtor` | `instance [LeanScriptTyWf α] : LeanScriptTyCtor (Process α)`, made of the above |

The same is emitted for `ProcessOption`, with instance
`[LeanScriptTyWf α] [LeanScriptTyWf S] : LeanScriptTyCtor (ProcessOption α S)`. The group
is mutual, but the declarations refer to each other only by *name*, so the instances do not
depend on each other and instance resolution has no cycle.

**For a type with no existentials** (anything `deriving LeanScriptTyWf` accepts), the
deriver emits a **structural** instance. `selfTy` is the existing tree, and each
`leanScriptCtor_*` is the `taggedUnion_mk` / `record_mk` / `enum_mk` /
`recTaggedUnion_mk` / `mutualRecursiveFamily_mk` node that `transCtorApp` builds today,
generated once per constructor instead of once per call site. I propose that
`deriving LeanScriptTyWf` emits this instance automatically, so existing code needs no
change.

This is the caching you mentioned. The field types, the tag bound and the `decide` proof
of `t < length` are computed and checked **once, in the deriver**. `#leanscript_to_term`
only fills in the spine.

---

## 5. The deriver's algorithm

### 5.1 Classify every binder of every constructor

After instantiating the Lean parameters, each binder is one of:

1. **uniform index**: a `Type`-typed binder that is exactly the corresponding index of the
   result, e.g. `State` in `ProcessOption.some … : ProcessOption α State`. Every
   constructor must return `I params x₁ … xₖ` with the `xⱼ` being **distinct bound
   variables**. Then the family is really parametric, and the index becomes a parameter of
   the declaration (`nParams += 1`). Otherwise (a real GADT index such as `Vec α n`,
   `ProcessOption α Nat`) refuse: *"indexed families are not supported"*.
2. **existential**: `isTypeField` (it already exists in `Deriving/Read.lean`) and does not
   occur in the result. It becomes `tyVar (nParams + j)`, `nExists += 1`.
   A *family* of types (`Elem : State → Type`, as in `Keyed` in the existing tests) is
   refused: *"existentially quantified type families are not supported"*.
3. **erased**: a proof or a one-value type (`isErasedType`). It is dropped, as it is now.
4. **value field**: translated to a `Ty` over the type variables (5.2). A field whose type
   depends on a *value* binder is refused (no dependent types).

### 5.2 Translate a field type with type variables

This is `treeOfType` with a variable map:
* a bound type variable becomes `.tyVar k`;
* a type of the mutual group, applied to arguments, becomes `.named n (args translated)`;
* `→` becomes `.fn`;
* any other type former is taken from its instance, with its arguments put in place.

The last case is the same "read the former's own model and substitute" step the
structural deriver already does for a field such as `Option T`. It is now done for a
`tyVar` instead of an occurrence, so `Option State` becomes
`taggedUnion [[], [tyVar 1]]`. A closed field type (`Nat`, `α` once α is a param variable)
is its instance tree.

### 5.3 Pick the mode

If any constructor of the group has an existential, the **nominal** instance is emitted
for every member (they must agree, because they name each other). Otherwise the
**structural** instance is emitted.

### 5.4 The `LeanScriptTyWf` error stays

`deriving instance LeanScriptTyWf for Process, ProcessOption` is unchanged and still gives
the exact message in your test. `LeanScriptTyWf` still means "has a structural tree".

---

## 6. `#leanscript_to_term`

### 6.1 A constructor application

For `Process.step Nat 0 (fun n => …)`, `transCtorApp` becomes:

1. Synthesize `LeanScriptTyCtor (Process Nat)`. If there is no instance, **throw**, naming
   the type (this is your "from now on" TODO):
   > `#leanscript_to_term`: `Process.step` builds a value of `Process Nat`, which has no
   > `LeanScriptTyCtor` instance; add `deriving LeanScriptTyCtor`
2. `i := ci.cidx`. The tag is the Lean constructor index, as it already is in `transCtorApp`.
3. The existential arguments (`State := Nat`) become `xs := #v[tyWfOf Nat]`. Each witness
   goes through `tyOfType`, so `String`, `Bool` and `Process Nat` work.
4. The value arguments (`0`, `fun n => …`) are translated against
   `reduceTy (inst.ctorFieldTys i xs)`, with `mkSpine` exactly as now.
5. Emit `@LeanScriptTyCtor.ctorMk (Process Nat) inst i xs Sg Γ spine`. The kernel unfolds
   `ctorMk` only as far as it needs to check the spine's type.

Partial applications (`Process.halt Bool` with no function yet) are eta-expanded, as now.

**Exempt from the "must have an instance" rule** (they have no constructor in the tree):
`Array` literals (`array_mk`), `Thunk.mk`, `Bool` (`bool_mk`), and literal constructors of
terminal types. Every other constructor must go through an instance. So
`LeanScript/Ty/Instances.lean` needs `LeanScriptTyCtor` instances for `Option`, `Prod`,
`Sum`, `List` and `Ordering`: structural, and written by the same generator.

### 6.2 What happens with the two examples

`mixedProcess` gives nested `ctorMk` calls with `xs` = `[nat]`, `[string]`, `[bool]` at
the three levels. The types line up: the inner lambda `fun s => …` is
`Term … (string ⇒ .named "ProcessOption" [nat, string])`, and that is exactly
`ctorFieldTys` of `step` at `xs = [string]`.

`varyingProcess`: `if n = 0 then … else …` already translates to `bool_casesOn`, through
`boolOfDecidable`. Both branches have type `ProcessOption Nat Nat`. The *inner* `Process`
values differ in their witness (`Unit` vs `Bool`), and that is fine: the witness is not
part of the type `.named "Process" [nat]`. This is exactly what the `…Twin` encoding
could not express.

**`Unit` as a witness is a problem.** The language erases `Unit` and has no tree for it,
so `Process.step Unit () …` has no `xs`. Options (see §9, Q3):
* (a) *erasing instantiation*: allow `Option TyWf` witnesses. `instTyVars` with `none`
  drops a field of type `tyVar k`, turns `tyVar k ⇒ τ` into `τ`, and puts a fixed
  placeholder in `named` args. This is principled but adds a second `fieldTys`.
* (b) add a one-value terminal `LeanPrimTy.unit`, used only where a type is required
  (witnesses, `named` args). It is cheap, but it weakens "unit types are erased".
* (c) refuse `Unit` witnesses for now, and write `varyingProcess` with `Bool`/`Nat` in the
  test.

### 6.3 Types of binders

`fun n => …` of type `Nat → ProcessOption Nat Nat` needs `treeOfType (ProcessOption Nat Nat)`.
That comes from `LeanScriptTyCtor.selfTy` (§3.4). The existentials error in
`TyView.treeOfType` stays for types that have *neither* instance.

---

## 7. Out of scope here: taking such a value apart

`match p with | .step S seed trans => …` needs the branch to be well typed **for every**
witness `S`. Two ways:

* the branch is a Lean function `(xs : Vector TyWf k) → Term Sg (fieldTys ps xs ++ Γ) τ`.
  This is easy to generate, but the branch could *inspect* `xs` (`if xs[0] = nat then …`).
  That is not parametric, and a type-erasing backend cannot run it. **Not recommended.**
* the branch binds **skolem** type variables, i.e. `Ty.tyVar` in the `Term`'s context.
  This is parametric by construction, but it needs `Ctx` to carry the number of skolems,
  and `Wf` of a `Term`'s type to allow them.

Either way, `Term.named_casesOn` must know that `d` is *the* declaration of `"Process"`.
Otherwise two different `TyDecl`s with the same name would give the same type different
constructors. So the eliminator will need `Sig` to list declarations
(`Sig.tyDecls : List TyDecl`, names unique like `h_names_unique`), with `named_mk` taking
a reference into it. For **construction only**, `named_mk` taking `d` directly is sound
(it only builds values), and it keeps `#leanscript_to_term` usable without listing
declarations in the signature. I suggest starting there and moving `d` into `Sig` together
with the eliminator.

---

## 8. Test plan (`TermTests/InductiveTypesTest/Existentials.lean`)

* The existing `#guard_msgs` refusals of `LeanScriptTyWf` stay as they are.
* `deriving instance LeanScriptTyCtor for Process, ProcessOption` succeeds.
  `#check` of the instances, and `example : (inst : LeanScriptTyCtor (Process Nat)).nOfCtors = 2 := rfl`.
* `mixedProcess_term` and `varyingProcess_term` build. `example` pins their type:
  `Term Sg [] (.named "Process" [.prim .nat])`.
* Also `ProcessHaltIsOut`, `Client`/`Server`, `StreamPipeline` (two existentials),
  `CompilerEngine` (three), and `Layered` (existential + `List` of itself; the `List` is
  `List`'s structural model with `named` in place).
* Refusals: `Keyed` (type family), a real GADT index, and a constructor application of a
  type without `LeanScriptTyCtor` inside `#leanscript_to_term`.
* Regression: all of `ToTermTest` etc. still pass once `deriving LeanScriptTyWf` also
  emits the structural `LeanScriptTyCtor` (§4).
* New structures (`CtorSig`, `TyDecl`) get `BEq, ReflBEq, LawfulBEq, DecidableEq`, in line
  with the previous task.

---

## 9. Decisions I need from you

1. **Nominal (A) vs structural `∃` (B)**, §2. I recommend A.
2. **Name**: you wrote both `LeanScriptCtor` and `LeanScriptTyCtor`. I used
   `LeanScriptTyCtor`, as in your `deriving instance` line.
3. **`Unit` witness** in `varyingProcess`, §6.2: (a) erasing instantiation, (b)
   `LeanPrimTy.unit`, or (c) refuse for now.
4. **Should `deriving LeanScriptTyWf` also emit `LeanScriptTyCtor`** (§4)? Without this,
   the "must have an instance" rule breaks every existing test that builds a
   user-defined value.
5. **`h_nOfCtors_neZero : nOfCtors ≠ 0`, or `[NeZero nOfCtors]`?**

## 10. Suggested order of work

1. `Ty.named` / `Ty.tyVar`, `Wf`, `beq`/`TyBEq`, `ty_wf`, `Den` (all mechanical); then
   `TyVars.lean` and its instantiation lemma, the only real proof.
2. `TyDecl`, `Term.named_mk`, the class. Hand-write the `Process` instance in a test file
   and build `mixedProcess_term` by hand, to validate the types before writing any meta
   code.
3. The deriver: nominal mode first, then structural mode, then instances for the built-in
   types.
4. `#leanscript_to_term`: use the instance, then turn on the "must have an instance" error.
5. Later: the eliminator (§7).
