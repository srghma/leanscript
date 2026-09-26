# Proposal: `LitExpr` and `Unfold` through `Ty.mutualRecursiveFamily`

> **Status: proposal only.** Nothing in `LeanScript/` has changed. The trees this note says
> the deriver and the translator should produce are written out by hand in
> `proposals/IndexedExistentialFamilyToy.lean`. That file checks with the existing `ty_wf`
> tactic whether the current `Ty.Wf` accepts each tree (§6). It is not part of the Lake build:
>
> ```
> lake build LeanScript.Ty.TyWf && lake env lean proposals/IndexedExistentialFamilyToy.lean
> ```
>
> It compiles with no errors and no `sorry`. The Lean sketches in this note, outside that
> file, have not been compiled.

The two targets:

```lean
inductive LitExpr : Type → Type 1 where
  | lit  {α : Type} (x : α) : LitExpr α
  | pair {α β : Type} (a : LitExpr α) (b : LitExpr β) : LitExpr (α × β)

structure Unfold (α : Type) where
  State      : Type
  seed       : State
  step       : State → Option (State × α)
  measure    : State → Nat
  decreasing : ∀ x x' a, step x = some (x', a) → measure x' < measure x
```

---

## 0. Summary

Neither type has one tree of the language, because each carries a type-level variable the
language cannot represent:

* **`LitExpr`**: the index `α` decides the payload of `lit`. So `LitExpr α` is a *function
  of a Lean type*, not one tree.
* **`Unfold`**: `State` is chosen separately by every value.

The proposal handles both the same way. **Replace the type-level variable by a finite set of
closed Lean types, computed at elaboration time, with one family member per element.**
Every member is an ordinary schema (`.ctors`, `.record` or `.alias`), and the members point
at each other with `Ty.familyMember i`. That is exactly what `Ty.mutualRecursiveFamily` and
its fold `mutualRecursiveFamily_rec` (with its tuple of answers for members that answer
different types) already provide.

| | variable | finite set | one member per | family needed when |
| :-- | :-- | :-- | :-- | :-- |
| `LitExpr` | the index `α` | indices reachable from the closed index at the use site | reachable index | the index graph has a cycle |
| `Unfold` | the field `State` | states built at the `Unfold.mk` sites of the program | element type `α` of `Unfold α` (the state family `H α`) | the state graph has a cycle (`append`, `map` back and forth, …) |

One caveat applies to `LitExpr` exactly as written. Its index only shrinks (`pair` goes from
`α × β` to `α` and `β`), so its index graph **never has a cycle**. The canonical form below
(§1.4) then has no family at all: it is a finite nesting of plain `taggedUnion`s. The family
becomes necessary as soon as an index can come back: for instance with a `swap` constructor
(§1.6), or with the state family of `Unfold` (§2). I recommend one algorithm for both cases.
It emits `mutualRecursiveFamily` on every cycle of the graph, and plain shapes everywhere
else. §1.5 describes the alternative that always uses a family, and its cost: a change to
`Ty.Wf` and the loss of one tree per Lean type.

---

## 1. `LitExpr`: one member per reachable index

### 1.1 Why it is refused today

`Ty/Deriving/Read.lean` (`existentialField?`) calls a type field existential when a later
field's type mentions it outside the block's indices. `lit {α} (x : α)` does exactly that
(`x : α`), so `deriving LeanScriptTyWf` refuses `LitExpr` with *existential typing is not yet
supported*.

That verdict is right for `LitExpr α` with `α` a variable. But `α` is **not** hidden. It is
fixed by the constructor's result index `LitExpr α`. Once the index at a use site is a closed
Lean type, the type of `x` is known. (`TExpr.fst {α β} (p : TExpr (α × β)) : TExpr α` is
different: there `β` really is hidden, because the result index does not determine it.)

`fun (α : TyWf) => …`, the per-hidden-type mechanism `ToTerm/ExistentialArgs` uses for
`Unfold` today, cannot handle this. The tree of `LitExpr σ` depends on whether `σ` *is a
Lean product*, and a `TyWf` cannot tell: `tyOf (Nat × Bool)` and the tree of a user structure
with two fields are both `.record`. So the index has to be a **Lean type**, known at
elaboration time. In other words, `LitExpr` is monomorphised at each closed index.

### 1.2 The index closure (elaboration time, on `Lean.Expr`)

```
closure(σ₀):
  todo := [σ₀]; seen := []
  while todo ≠ []:
    σ := pop todo;  if σ ∈ seen (up to defeq at instances transparency) continue
    seen += σ
    for every constructor c of the inductive:
      instantiate c's type variables with fresh mvars;
      unless (result index of c) =?= σ succeeds: c is absent at σ;  continue
      every type variable of c must now be assigned      -- else: a real existential (TExpr.fst's β)
      for every recursive field `LitExpr σ'` of c: todo += σ'
    if |seen| > maxIndexClosure (e.g. 64): refuse "the indices reachable from σ₀ do not end"
```

* The matching is Lean's own unifier with metavariables (`isDefEq` at instances
  transparency). So `?α × ?β =?= Nat × (Bool × Nat)` succeeds, `?α × ?β =?= Nat` fails, and a
  reducible alias of `Prod` still matches.
* **A real existential** is a type variable that the match leaves unassigned but a value
  depends on. It stays refused, with the current message. A type variable that the match
  leaves unassigned and no value depends on (`TExpr.pair` when the index is a variable) is
  still erased as it is today.
* **Growing indices** (`wrap (e : E (List α)) : E α`, polymorphic recursion) never close. The
  bound turns that into a clear refusal instead of a loop.

For `LitExpr ((Nat × Bool) × Nat)` the closure is

| # | index | constructors that match | fields |
| :-- | :-- | :-- | :-- |
| 0 | `(Nat × Bool) × Nat` | `lit`, `pair` | `lit (x : (Nat × Bool) × Nat)`, `pair (#1) (#3)` |
| 1 | `Nat × Bool` | `lit`, `pair` | `lit (x : Nat × Bool)`, `pair (#2) (#4)` |
| 2 | `Nat` | `lit` | `lit (x : Nat)` |
| 3 | `Nat` | = #2 (deduplicated) | |
| 4 | `Bool` | `lit` | `lit (x : Bool)` |

### 1.3 One schema per index

Each index gets the schema the deriver already builds for a member of a `mutual` block
(`Ty/Deriving/Build.lean`). The only difference is that the constructors are the ones that
matched:

* a value field gets the tree `tyWfOf` of its instantiated type, by an instance lookup as
  today;
* a recursive field `LitExpr σ'` gets `Ty.familyMember j(σ')` (or `Ty.self`, or the closed tree
  of `σ'`; see §1.4);
* type fields determined by the index, and proofs, are erased;
* the member's shape follows the usual rules. It is `.ctors` for two or more constructors,
  `.record` for one constructor with two or more fields, and `.alias` for one constructor
  with one field (`LitExpr Nat` is a newtype of `Nat`). The newtype wrapper is erased outside
  a family.
* **An index with no matching constructor** has no values (for example a
  `V : Nat → Type` where nothing ends in `V 7`). It is dropped, and so is every constructor
  with a field at that index, repeating until nothing changes. If the root itself becomes
  empty, the tree is refused. This mirrors `Ty.FamHab`, so the family that comes out always
  has values.

### 1.4 The canonical form: families on cycles only (recommended)

`Ty.WfIn.mutualRecursiveFamily` requires `MembersOccur`: *every* member, including the
selected one, is mentioned by the family. It also requires at least two members. In
`LitExpr`'s family nothing ever mentions member 0, because indices only shrink. The toy
checks this: `ty_wf` answers *nothing here mentions member 0* for `LitExpr (Nat × Bool)`
written as one family (toy §1).

These two rules make sense, and they suggest the canonical form. Take the **strongly
connected components** of the index graph (Tarjan), in bottom-up order:

| component | tree |
| :-- | :-- |
| one index, not recursive on itself | the plain shape (`taggedUnion`, `record`, the field itself for a newtype). A field at a lower index gets that index's **closed** tree |
| one index that recurses on itself (`neg : E Nat → E Nat`) | `recTaggedUnion` / `recObject` / `recAlias` with `Ty.self` |
| ≥ 2 indices | `mutualRecursiveFamily`: one member per index of the component. Occurrences inside the component are `familyMember i`. Lower components get their closed trees |

Within a component of two or more indices, each member is mentioned by another member, so
`MembersOccur` holds. Lower components are closed trees, which `Ty.WfIn.closed` accepts in any
scope. **The current `Ty.Wf` accepts every tree of this form unchanged.** The toy checks the
unrolled `LitExpr (Nat × Bool)` and `LitExpr ((Nat × Bool) × Nat)` (toy §2) and the family of
§1.6 (toy §3).

**One tree per Lean type.** A field at index `σ'` must have the same tree as `LitExpr σ'` on
its own. Otherwise a value read out of a field could not be passed to a function of
`LitExpr σ'`. The component form keeps this property as long as the **members of a component
are ordered canonically**, by a structural order on the index `Expr`s (for example
`Expr.lt` after `instantiateMVars`), and not by discovery order. Then `SwExpr (Nat × Bool)` and
`SwExpr (Bool × Nat)` are the same family with different members selected. That is also the
tree `TyWfIn.unfold` produces for a `familyMember` field.

For `LitExpr` every component is a single index that is not recursive on itself. So:

```
tree(LitExpr (Nat × Bool)) = taggedUnion [ [record ⟨nat, bool⟩], [nat, bool] ]
```

### 1.5 The alternative: always one family (not recommended)

Put *every* reachable index into one family rooted at `σ₀`, and relax `MembersOccur` to
"every member except member 0 is mentioned". This makes the translator uniform: one
`mutualRecursiveFamily_rec` for every recursion on an indexed family. It costs two things.

* `Ty.Wf`, `WfTactic`, `WfFacts`, `WfSubst` and every proof that inverts
  `WfIn.mutualRecursiveFamily` change.
* **The tree depends on the root.** The `LitExpr Nat` field of a `LitExpr (Nat × Bool)` would
  be member 1 of the `Nat × Bool` family, while `LitExpr Nat` on its own is `nat`. Every
  crossing between the two would need a conversion term. This breaks what `tyOf` promises
  today: one tree per Lean type.

### 1.6 Where the family really appears: a cycle in the index

```lean
inductive SwExpr : Type → Type 1 where
  | lit  {α : Type} (x : α) : SwExpr α
  | pair {α β : Type} (a : SwExpr α) (b : SwExpr β) : SwExpr (α × β)
  | swap {α β : Type} (p : SwExpr (β × α)) : SwExpr (α × β)
```

From `Nat × Bool`, the reachable indices are `Nat × Bool`, `Bool × Nat`, `Nat` and `Bool`.
`Nat × Bool` and `Bool × Nat` form one component (through `swap`), so they become a family of
two members. `Nat` and `Bool` are closed leaves below it. (Toy §3 writes them as members of
the family. That is also well formed, since both are mentioned. The canonical form inlines
them instead.) Mutual indexed families of this kind are refused today, and would get
`mutualRecursiveFamily` directly.

### 1.7 Recursion on an indexed family

Lean compiles a structural recursion on `LitExpr` into `LitExpr.brecOn`, whose motive takes
the index: `motive : (α : Type) → LitExpr α → Sort u`. The translation of a recursion used at
the closed index `σ₀`:

1. Compute the components of `closure(σ₀)` as in §1.4.
2. Going bottom-up, bind **one local function per index** with `let`:
   `f_σ : tree(LitExpr σ) ⇒ tree(motive σ …)`.
   * **Answer types per index.** The motive is instantiated at `σ`, so `eval : LitExpr α → α`
     answers `nat` at `Nat` and `record ⟨nat, bool⟩` at `Nat × Bool`. This is the "dependent
     motive" that `IndexedGADT.lean` refuses today. It is allowed here because each index has
     its own function.
   * **A component with one index that is not recursive on itself**: the body is
     `taggedUnion_casesOn` (or a record projection) of the Lean branches, instantiated at `σ`.
     The answer at a field of index `σ'` is `f_σ' field`. A deeper `match` is just more
     nested `casesOn`, with no depth limit, because there is no fold.
   * **A self-recursive index**: `recTaggedUnion_rec k` / `recObject_rec` / `recAlias_rec`,
     exactly as `TransRecUnion` does now.
   * **A component of two or more indices**: `mutualRecursiveFamily_rec k`, built by the
     existing `TransRecFamily` with two changes. First, member `j` is index `σ_j`: its
     constructors are the matched ones, and the Lean branch is instantiated at `σ_j` by the
     same match. Second, the answer is the existing **tuple of answers** (`slots`, `PProd`)
     whenever the `motive σ_j` differ. A field in a lower component is answered by calling
     that component's `f`, as in the existing `CrossBlock` tests.
3. The result is `f_σ₀`.

A function that is generic in the index (`size {α} : LitExpr α → Nat`) is translated at each
closed `α` at which it is used. This is the same specialisation the translator already does
for calls on known values.

### 1.8 Where the tree is produced

A `deriving LeanScriptTyWf` instance cannot exist for `LitExpr α` with a variable `α`. So the
tree is produced **per closed index, on demand**, like `#leanscript_ctor`:

* When `tyOf (LitExpr σ)` is needed for a closed `σ` (by the translator, or by the user
  through `tyOf`), a generated `instance : LeanScriptTyWf (LitExpr σ)` is added. Its tree goes
  into the existing table of trees (the environment extension in `Ty/Deriving.lean`), so each
  index is built once for the whole project.
* `deriving LeanScriptTyWf` on `LitExpr` itself registers the inductive as *indexed by
  types*. It checks once that every type field is either determined by the result index or
  erased, and prints the new message otherwise. It does not emit an instance.
* The proof is `ty_wf`, as for every derived tree. Toy §2 and §3 show that the default proof
  of `TyWf` closes the trees of the canonical form.

---

## 2. `Unfold`: a closed-world state family

### 2.1 What exists and what is missing

`TermTests/StructRecTest/Existential.lean` shows the current support:

* a value is built by its `#leanscript_ctor` function, at the layout of the `State` it chose;
* a call on a value that is written out is specialised to that value;
* a function of an `Unfold` becomes a Lean function of the hidden type:
  `fun (State : TyWf) => (… : Term … (Unfold.mk.leanScriptLayout α State ⇒ …))`.

What cannot be written is anything where **two values with different states must have one
type**. Examples:

* `if b then countdown 5 else countFrom 3` (two states in the two branches);
* `List (Unfold Nat)`, or an `Unfold` as a field of another structure;
* a recursion that returns an `Unfold` (`f (n+1) = (f n).append (countdown n)`), whose state
  type grows with `n`;
* recursive datatypes that hide a type at every node (`Proc`/`Process`, which
  `LeanScriptTyCtorProposal.md` §1.1 discusses).

### 2.2 The idea: a finite number of sites, even when there are infinitely many values

A state type is written at a **site**: an application of `Unfold.mk`, or a `{ u with … }`,
somewhere in the translated program. There are finitely many sites. The program above
creates infinitely many *state types* (`Nat`, `Nat ⊕ Nat`, `(Nat ⊕ Nat) ⊕ Nat`, …) only because
a site refers to the state of *another* value: `append` has state `u.State ⊕ v.State`. So:

1. **Collect the sites** reachable from the roots being translated, after the inlining and
   specialisation the translator already does. Each site has a result `Unfold α` (with `α`
   closed after monomorphisation) and a state `S`.
2. **Normalise each state**: replace every `Unfold.State u` with `u : Unfold α'` by a
   placeholder `H α'`. The state of `append` becomes `H α ⊕ H α`, and that of `u.map f` (with
   `u : Unfold α'`) becomes `H α'`.
3. **The state family** `H` is a virtual type indexed by the element type:

   ```
   H : Type → Type
   site_t : S̃_t → H α_t        -- one constructor per distinct normalised state S̃_t at α_t
   ```

   This is `LitExpr`'s situation again. Run §1.2–§1.4 on `H`: the closure of indices, one
   schema per index, and components. `H α` is a `mutualRecursiveFamily` whenever the
   placeholders form a cycle between two element types, a recursive binder when the cycle is
   `H α` on itself (`append`), and a plain union otherwise.
4. **The tree of `Unfold α`** is then an ordinary closed record:

   ```
   Unfold α  ↦  record ⟨ seed    : H α,
                         step    : H α ⇒ Option (H α × α),
                         measure : H α ⇒ Nat ⟩          -- `decreasing` is a proof: erased
   ```

   `H α` is to the left of an arrow, but as a **closed** type (`.mutualRecursiveFamily f`).
   `Ty.Wf` allows that: only an occurrence `familyMember i` there is refused. This is why
   `Unfold α` must stay *outside* the state family. The toy checks both sides: the record is
   accepted, and a family whose member holds `familyMember 0 ⇒ …` is refused with the
   positivity message (toy §4).

Toy §4 is the example of a program with sites `countdown` (`Nat`), `append` (`u.State ⊕
v.State`) and `map` (from `Nat` to `Bool` and back):

* `H Nat = countdown (n : Nat) | append (s : H Nat ⊕ H Nat) | map (s : H Bool)`
* `H Bool = map (s : H Nat)` (a newtype)

This is a family of two members that mention each other, and `Ty.Wf` accepts it as it
stands.

### 2.3 The terms

| Lean | term |
| :-- | :-- |
| `Unfold.State u` (as a type), `u : Unfold α` | `H α` |
| `u.seed`, `u.step`, `u.measure` | projections of the record |
| `u.decreasing` | erased |
| site `t`: `{ State := S, seed, step, measure, .. }` | the record below |

```
{ seed    := inj_t ⟦seed⟧,
  step    := λ h. match h with
                  | inj_t x => (⟦step⟧ x).map (λ (x', a). (inj_t x', a))
                  | _       => none,
  measure := λ h. match h with
                  | inj_t x => ⟦measure⟧ x
                  | _       => 0 }
```

* `inj_t` is the constructor of `H α_t` for the site: `mutualRecursiveFamily_mk`,
  `recTaggedUnion_mk` or a tagged-union constructor, depending on the component. The match is
  `mutualRecursiveFamily_casesOnWithDefault` (or its counterpart), which already exists.
* Inside `⟦seed⟧` and `⟦step⟧`, a value of type `u.State` is already an `H α'` (by the first
  row of the table), so nothing more is wrapped. `append`'s step pattern-matches on
  `Sum.inl s` / `Sum.inr s` and calls `u.step s` / `v.step s` directly.
* **The `_` branches are never taken.** Lean does not allow mixing states: `u.step v.seed` is
  ill-typed (`v.State` is not `u.State`). So in the translated program the `step` of a value is
  only ever applied to states that its own site made. The same argument justifies the default
  branches of `IndexedGADT.lean` for impossible indices. A theorem to prove later, per site:
  `step' (inj_t x) = (step x).map (inj_t × id)`.
* **No cost when there is one site per element type.** Then `H α` has one constructor with
  one field, so it is a newtype and is erased: the record is exactly today's layout at that
  state, and the matches disappear.

### 2.4 What it gives

* `Unfold Nat` has **a tree** in a given program, so `List (Unfold Nat)`, `if … then u₁ else
  u₂`, `Unfold` fields, and recursions returning an `Unfold` all translate.
* `Proc`/`Process`-style recursive datatypes with a hidden type at each node are handled by
  the same placeholder rule. Every hidden `State` of a `Process α` becomes `H_Process α`, and
  the datatype itself becomes an ordinary recursive type over it. This is the "shared type"
  that `LeanScriptTyCtorProposal.md` §2 is looking for, restricted to a closed program.
  Today `ProcessModel.varyingProcess_term` in `TermTests/InductiveTypesTest/Existentials.lean`
  translates one closed value, and its type is the layout of the witnesses *that value*
  uses. The state family gives every `Process Nat` of the program one type.

### 2.5 Costs and limits

* **Closed world.** The tree of `Unfold α` depends on *all* sites of the program, so it is not
  modular. It cannot be an instance emitted with the `structure`. It has to be computed when a
  *program* is translated (a set of roots), and adding a site changes it. I propose a command
  that fixes the set of roots, such as `#leanscript_program p := [f, g, h]`, with an option
  `leanscript.existential := closedWorld | perHiddenType`. The current per-hidden-type
  translation stays the default and the fallback. It is still the only choice for an API that
  receives an `Unfold` from outside, such as a JavaScript caller, since no site is known
  there.
* **Refused states.** A state that is not closed after normalisation, or whose tree depends
  on a value (`State := Vector Nat n` when the tree of `Vector` depends on `n`, or
  `iterate n Option Nat`), is refused. So is a state closure that does not end (polymorphic
  recursion on `α`), using the bound of §1.2.
* **Run time.** When `H α` has two or more constructors, every step does one tag dispatch
  and allocates one wrapper. Newtype `H α`s cost nothing (§2.3).
* **`measure`** is kept because it is data, not a proof. A later pass may drop fields that are
  never read.

### 2.6 Alternatives considered

* **Final coalgebra.** `∃ S. S × (S → Option (S × α))` is equivalent, as far as anything can
  observe, to a lazy list `μX. Option (α × Thunk X)`. With `decreasing` this is inductive. It
  is modular and needs no family. But building it needs general recursion on `measure` (the
  `fix` of `proposals/WellFoundedRecursionAssessment.md`, not implemented), and it changes when
  work happens. It could be a later, complementary open-world encoding.
* **A dynamic type.** The language has no `any` type, and adding one would give up the typed
  `Term`. Rejected.

---

## 3. Implementation plan

| step | where | what |
| :-- | :-- | :-- |
| 1 | `LeanScript/Ty/Deriving/IndexClosure.lean` (new, `meta`) | §1.2 closure, pruning of empty indices (§1.3), Tarjan components, canonical order of members |
| 2 | `Ty/Deriving/Read.lean` | a type field determined by the result index is not existential when the index is closed; new refusal messages (unassigned type variable, closure does not end, empty root) |
| 3 | `Ty/Deriving/Build.lean`, `Ty/Deriving.lean` | a schema per index; the component form; on-demand per-index instances cached in the tree table; proofs by `ty_wf` |
| 4 | `ToTerm/TransIndexed.lean` (new) | §1.7: per-index `let` functions bottom-up. Single indices by `casesOn`, self-recursive ones by `TransRecUnion`, components by `TransRecFamily` with instantiated branches and per-member answer slots |
| 5 | `ToTerm/ClosedExistential.lean` (new) | §2: site collection, normalisation to placeholders, state family (steps 1–3 reused), rewriting of sites and projections, `#leanscript_program` |
| 6 | tests | `TermTests/StructRecTest/IndexedLit.lean` (`LitExpr`, `SwExpr`, `size`, `eval`, a deep `match`) and `TermTests/StructRecTest/ClosedExistential.lean` (`if`, `List (Unfold Nat)`, a recursion returning `append`, `map` back and forth), checked with `kernel_rfl` against the Lean definitions, as the existing tests are |

`Ty`, `Ty.Wf`, `Term` and the evaluator do not change. Everything is new front-end code over
the existing shapes and folds.

## 4. Decisions I need from you

1. **Families only on cycles (§1.4, recommended) or always one family (§1.5)?** The first
   keeps `Ty.Wf` and one tree per Lean type. As a consequence, `LitExpr` itself gets no family.
2. **Canonical order of family members:** is a structural order on the index `Expr` good
   enough, or do you want a name-based order that is stable when the index is written in a
   different but defeq way?
3. **Closed world for `Unfold` (§2.5):** is it acceptable that the tree of `Unfold α` depends
   on the program being translated, with a command that fixes the roots?
4. **Scope of the first step:** `LitExpr`/`SwExpr` (steps 1–4) before `Unfold` (step 5), since
   step 5 reuses steps 1–3?

## 5. Relation to other notes

* `LeanScriptTyCtorProposal.md`: its `#leanscript_ctor` half exists and is reused for the
  sites. Its open question, "one type shared by every value of `Process Nat`", is answered here
  for closed programs (§2.4).
* `NOT_IMPLEMENTED.md`: covers the items "existentially typed fields", "inductive families
  whose index changes the tree" and "dependent motives like `eval : TExpr α → α`" (for indices
  determined by the result).

## 6. What the toy file checks (`proposals/IndexedExistentialFamilyToy.lean`)

| § | tree | current `Ty.Wf` |
| :-- | :-- | :-- |
| 1 | `LitExpr (Nat × Bool)` as one family `[Nat × Bool, Nat, Bool]` | refused: *nothing here mentions member 0* (pinned with `#guard_msgs`) |
| 2 | `LitExpr (Nat × Bool)` and `LitExpr ((Nat × Bool) × Nat)`, unrolled (canonical form) | accepted (default proof `ty_wf` of `TyWf`) |
| 3 | `SwExpr (Nat × Bool)` and `SwExpr (Bool × Nat)`: one family, members 0 and 1 selected | accepted |
| 4 | state family `H Nat`/`H Bool`, and `Unfold Nat`/`Unfold Bool` as records over it | accepted |
| 4 | a family member with `familyMember 0 ⇒ …` (`step` inside the family) | refused: positivity (pinned with `#guard_msgs`) |

These check only that the proposed **trees** are, or are not, types of the language. The
closure algorithm, the translation of recursions and the site rewriting are not implemented
or checked.
