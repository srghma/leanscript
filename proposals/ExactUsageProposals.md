# Exact usages by construction: assessment and proposals

> **Status: proposal only.** Nothing in `LeanScript/` has changed. Every proposal has a toy
> `Term` in `proposals/ExactUsageToy.lean` (namespaces `EUToy.P1` … `EUToy.P4`). Each toy
> comes with an erasure to a common untyped syntax, an evaluator, a proof that its usages are
> exact, and the `AssocArrayAppend` example. The file is not part of the Lake build; check it with
>
> ```
> lake env lean proposals/ExactUsageToy.lean
> ```
>
> It compiles with no errors, no warnings and no `sorry`. The main theorems use only `propext`,
> `Classical.choice` and `Quot.sound`. The Lean sketches in this note that are *not* copied from
> the toy file have not been compiled.

---

## 0. Summary

| | where the counter lives | who computes it | can it be wrong? | elaborator | optimiser passes | fits today's code |
| :-- | :-- | :-- | :-- | :-- | :-- | :-- |
| **P1** QTT contexts | in the context entries (`(τ, u) :: Γ`), **checked** | whoever builds the term must supply the split (`Add`/`Max`/`Scale` witnesses) | no (`P1.Term.exact`) | must compute every split | must return a new context together with a witness (`Σ C', Term C' τ × …`), and env transport along every split | far: every constructor changes, env projections everywhere |
| **P2** input/output counters (Hodas–Miller) | an input and an output counter vector next to each context, **threaded** left to right | Lean computes the output from the input | no (`P2.Term.exact`) | only the input (`0`) is written; the output is computed | must return the new output counters | medium: values/envs are unchanged, binders read the head of the output |
| **P3** synthesised usage index (like `Lvl`) | a usage vector per context, as an **index computed by the constructors** | Lean computes it bottom-up | no (`P3.Term.exact`) | nothing to write (only `h : head ≠ 0` for a definition binder) | the index is in the Σ that passes already return for `Lvl` | closest: the same discipline as `Lvl` |
| **P4** checked cache | as today, a field at each binder, plus an invariant `Exact` in a subtype | smart constructors (`ETerm.letV` …) | no (`P4.ETerm.unique`) | uses the smart constructors | must rebuild with smart constructors, or recount | no change to the `Term` type |

All four use **`UsageN` (`0, 1, 2, …, ω`)** for pattern binders and **`UsageNPos` (`1, 2, …, ω`)**
for definition binders, as requested (§2). In all four, a term carrying the annotations of the
unoptimised snapshot (`k1 [ω]`, `x2 [ω]`, where the counts are `1` and `4`) cannot be built: §3
gives the four rejections.

**Recommendation.** Do **step 0** (§1.3) first: whatever proposal follows, the elaborator has
to produce exact counts. Then, in order of preference:

* **P3** if the main goal is "impossible to put an incorrect usage" at the lowest migration
  cost. It is the `Lvl` discipline applied to usages: one more index computed by the
  constructors. Optimiser passes already return `Σ o', …` for the level, so they would return
  `Σ o' U', …`.
* **P2** if you want the counter to be a property of the *context* (your remark that "the
  usage counter should be part of context"). It is P3 read as a judgement `{c} t {c'}`. With
  the input counters at `0`, the output **is** P3's index (`P2.Term.exact_closed`), but the
  counters stay attached to the contexts, and the binder rule is literally "enter at 0, leave
  at u".
* **P1** is the textbook quantitative type theory (the setting of Idris 2's QTT, linear logic
  and Granule) and the most elegant on paper. In Lean, with three contexts, every elimination
  carries three split witnesses. Renaming and substitution must then preserve splits, and the
  elaborator has to compute them. That is the most work for the roughly 57 files that mention usages
  today.
* **P4** if the `Term` type must not change at all. It is the cheapest option, but the
  invariant is a `Prop` beside the term instead of an index, so pattern matching on a term
  does not hand you the fact that an annotation is exact.

---

## 1. Assessment

### 1.1 What the snapshots show

`Tests/SnapshotsPBOPure/AssocArrayAppend-Term-unoptimized.txt`:

```
val k1 [ω] : ((Array String) → (Array String)) := fun x2 [ω] : (Array String) => (closed)
  ret lean_array_append(… x2 … x2 … x2 … x2 …)
ret k1
```

`…-Term-optimized.txt`:

```
val k1 [1] : … := fun x2 [ω] : (Array String) => (closed)
```

* `k1` is used once. The elaborator wrote `ω`, and `Term.dce` (run by `Term.optimizeN`)
  recounts it to `1`.
* `x2` is used **4** times. With today's three-valued `Usage01ω`, `ω` is the *right* answer
  ("anything other than 0 or 1"). The unoptimised `x2 [ω]` is therefore not wrong under today's
  meaning, only imprecise, and it becomes wrong once the counter is exact (`x2 [4]`).

### 1.2 Root cause

The `Lean code → Term` phase never counts. It writes `.many` at every binder, on purpose:

* `LeanScript/TermElab/Anf.lean`, module doc: *"Every binder is annotated `many`
  (`Usage1ω.many`, `Usage01ω.many`): the annotations are sound and a later pass (`Term.dce`)
  can make them exact."*
* `LeanScript/TermElab/Anf/Emit.lean`: `emitComp` emits `Term.letE … .many`, `emitVal` emits
  `Term.letV .many`, `placeJoins` emits `Branch.join … .many .many`. `branchesStx` emits
  `Branches.two [] []` (and `UCtx.annot` turns `[]` into `many` for every field).
* `LeanScript/TermElab/Anf.lean`: `Val.lam (u := .many)`, `Comp.nat_rec (u₁ := .many) (u₂ := .many)`,
  `Comp.array_foldl (u₁ := .many) (u₂ := .many)`, `dataRecS … (fun _ => .many)`.

The types allow this because they only constrain **one** fact about the annotation
(`LeanScript/Term/Syntax/Usage.lean`): a pattern binder annotated `zero` cannot be referenced
(`UVar.head` needs `u ≠ .zero`). Nothing ties `one`/`many` to the body: *"The type does not
check that the annotation is the actual count; `Term.dce` recounts it."* So:

1. **any over-approximation type-checks.** `many` is accepted everywhere it is not `zero`,
   so the elaborator's choice is sound but not exact;
2. **an under-approximation type-checks too.** Nothing stops `one` on a variable used twice.
   Today's passes do not produce one (`Term.dce` recounts with `Term.countU` …), but nothing
   in the types rules it out, and `dce` re-annotates through a *partial* renaming that keeps
   the old annotation when it fails (`Term.reannotFields`, `Body.reuse1`);
3. **definition binders cannot say `0`.** That is right for live code, but `Term.dce` keeps
   some dead bindings (*"a dead binding that is the only mention of an outer unknown is kept:
   dropping it could make an open body closed"*). Such a binding is annotated `1|ω` although it
   is used `0` times. Exact counting has to settle this case (§2.3).

### 1.3 Step 0 (independent of the proposals): count in the elaborator

The normaliser already computes one bottom-up property of everything it emits, the level:
`Out := { stx : Lean.Term, lv : Lvl }`, combined with `lmeet`. Add the usages the same way:

```lean
structure Out where
  stx  : Lean.Term
  lv   : Lvl
  uses : Uses            -- one UsageN per output position of Φ, Γ, js (by position, like `lv`)
```

Then `emitComp`, `emitVal` and `placeJoins` read the head of `r.uses` instead of writing `.many`:
they already have `r` (the rendered continuation) in hand when they build the binder. A use
is recorded where a variable is rendered (`renderNeu`, `jvarStx`). Arms of branches take the
`max`, and bodies (`Body.closed/opened`, the folds) are scaled to `ω`. With this change the
unoptimised snapshot prints `k1 [1]`, and `Term.dce`'s re-annotation becomes the identity on
elaborated terms. This step is needed for P1–P3 anyway: with P2/P3 the elaborator could even
write `_` and let Lean compute the counter, but writing the literal the normaliser already knows
keeps elaboration cheap: Lean only checks it.

---

## 2. The usage domain: `UsageN` and `UsageNPos`

```lean
inductive UsageN where      -- 0, 1, 2, …, ω
  | fin (n : Nat)
  | omega

inductive UsageNPos where   -- 1, 2, …, ω  (a definition binder is never dead)
  | succ (n : Nat)          -- n + 1
  | omega
```

(`EUToy.UsageN`, `EUToy.UsageNPos` in the toy.) Three operations, as today:

| | where | law |
| :-- | :-- | :-- |
| `a + b` | two parts of straight-line code (and the body + main part of a join point) | `fin a + fin b = fin (a+b)`, `ω` absorbs |
| `max a b` | two arms of a branch (only one runs) | `fin a ⊔ fin b = fin (max a b)` |
| `scale a` | inside a closure / delay / loop body (may run any number of times) | `scale 0 = 0`, otherwise `ω` |

and the law that lets the I/O counters of P2 work: `max (c + a) (c + b) = c + max a b`
(`UsageN.add_max`).

### 2.1 What "exact" means

The counter of a variable is the **maximum, over the execution paths that do not enter a
closure/delay/loop body, of the number of times the path uses it**, and `ω` if a body inside
mentions it. This is `RTerm.cnt` in the toy (the reference count), and what `Term.countU/K/J`
(`LeanScript/Term/Optimize/Occ.lean`) compute today, at a finer grain. `ω` is still needed: a
loop body runs an unknown number of times, so no natural number is exact there.

### 2.2 Variants worth considering

* **Static occurrences next to path counts.** `max` is what inlining needs (a value used once
  in each arm can be inlined into each arm without duplicating *work*), but it duplicates
  *code*. If the backend also wants code size, carry a pair `{ path : UsageN, occ : Nat }`
  (`occ` sums over arms and does not scale). This changes nothing structural in P1–P4.
* **`ℕ∞` from Mathlib.** `UsageN` is `ℕ∞`. The project does not depend on Mathlib
  (`LeanScript/Term/Syntax/UsageAlgebra.lean` imports it and fails to build), so the toy
  proves the few laws it needs by `cases`.

### 2.3 Dead definition binders

With `UsageNPos` on `letV/letE/join`, a dead binding is **ill-typed** in all four proposals
(the head counter must be `≠ 0`). That is the requested property, but it conflicts with
`Term.dce` keeping dead bindings to protect levels (§1.2, point 3). Two ways out:

1. make that case unnecessary: when dropping a dead binding would change the level, re-level
   the statement (`Term.relvl`, `LeanScript/Term/Rename/Relevel.lean`, which already moves
   statements between depths and recomputes levels) instead of keeping the binding;
2. or give `letE` a `UsageN` (allow `0`) and keep `UsageNPos` for `letV` and `join`.

---

## 3. The toy language

All four toys share an untyped erasure target and its reference count
(`EUToy.RExpr`, `EUToy.RTerm`, `EUToy.RTerm.cnt`). Its grammar keeps the three contexts:

```
e ::= uvar i | kvar i | lit n | e + e
t ::= ret e
    | letV (fun x => t) t     -- val k := fun x => body; t   (k : Φ, x : Γ of the body, body sees no J)
    | letE e e t              -- let x := f a; t             (x : Γ)
    | ifz e t t               -- the branch: max of the arms
    | join t t                -- join j x := body; main      (x : Γ of body, j : J of main)
    | jump j e
```

`RTerm.cnt s i t` is the exact usage of variable `i` of context `s ∈ {k, u, j}`. For the
`letV` case the body is scaled, for `ifz` the arms take the `max`, and for `join` body and main
add up.

The running example is `AssocArrayAppend.test1` cut down to its binders:

```
val k1 := fun x2 => ret (x2 + x2 + x2 + x2);  ret k1        -- k1 ↦ 1, x2 ↦ 4
```

| | the exact annotations | the snapshot's `k1 [ω]`, `x2 [ω]` |
| :-- | :-- | :-- |
| P1 | `assocExample` type-checks with `u := .succ 0`, `ux := 4` | a body with counter `ω` for `x2` cannot erase to the same program (`Term.unique`) |
| P2 | `assocExample := .letV (.succ 0) (.fin 4) body4.2 retK.2`; Lean computes `body4.1 = ⟨[], [4], []⟩`, `retK.1 = ⟨[1], [], []⟩` | `.letV (.succ 0) .omega …` and `.letV .omega (.fin 4) …` fail to elaborate (`fail_if_success`) |
| P3 | `assocExample` (no annotation written), the read-off annotations are `(4, 1)` | there is nothing to write |
| P4 | `ETerm.letV …` builds `.letV 1 4 …` | `¬ (ATerm.letV .omega .omega …).Exact` by `decide` |

---

## 4. Proposal 1: quantitative contexts (QTT-style splitting)

**Idea.** As in quantitative type theory, every context entry carries the exact number of
times the term typed in that context uses it. A variable is typed in a context where its entry
says `1` and all others say `0`. Two parts that both run split the context pointwise
(`Γ = Γ₁ + Γ₂`), two arms take the pointwise `max`, and a body is seen from outside scaled
(`ω·Γ`). A binder's annotation is not a free choice: it **is** the head entry of its scope's
context, so the type checker reads it there.

With three contexts the counters live in all three: `Ctxs := {k u j : List (Ty × UsageN)}`.
The relations are inductive families, so no function appears in an index (`Type`-valued,
because `eval` takes them apart to split environments):

```lean
inductive Var : Ctx → Ty → Type
  | head {Γ τ} : Ctx.Zero Γ → Var ((τ, 1) :: Γ) τ      -- this one 1, all others 0
  | tail {Γ σ τ} : Var Γ τ → Var ((σ, 0) :: Γ) τ

inductive Term : Ctxs → Ty → Type
  | ret  : PExpr C τ → Term C τ
  | letV (u : UsageNPos) (ux : UsageN) :
      Term ⟨Φb, (σ₁, ux) :: Γb, Jb⟩ σ₂ → Ctx.Zero Jb → Ctxs.Scale ⟨Φb, Γb, Jb⟩ C₁ →
      Term ⟨(.fn σ₁ σ₂, u.toN) :: C₂.k, C₂.u, C₂.j⟩ τ → Ctxs.Add C₁ C₂ C → Term C τ
  | letE (u : UsageNPos) :
      PExpr C₁ (.fn σ ρ) → PExpr C₂ σ → Ctxs.Add C₁ C₂ C₁₂ →
      Term ⟨C₃.k, (ρ, u.toN) :: C₃.u, C₃.j⟩ τ → Ctxs.Add C₁₂ C₃ C → Term C τ
  | ifz  : PExpr C₁ .nat → Term C₂ τ → Term C₃ τ → Ctxs.Max C₂ C₃ C₄ → Ctxs.Add C₁ C₄ C → Term C τ
  | join (u : UsageNPos) (ux : UsageN) :
      Term ⟨C₁.k, (σ, ux) :: C₁.u, C₁.j⟩ τ → Term ⟨C₂.k, C₂.u, (σ, u.toN) :: C₂.j⟩ τ →
      Ctxs.Add C₁ C₂ C → Term C τ
  | jump : Ctx.Zero Φ₁ → Ctx.Zero Γ₁ → Var J₁ σ → PExpr C₂ σ → Ctxs.Add ⟨Φ₁, Γ₁, J₁⟩ C₂ C → Term C τ
```

**Proved in the toy.**

* `P1.Term.exact : t.erase.cnt s i = C.useAt s i`: every counter of every context is the
  reference count of the erasure;
* `P1.Term.binder_exact`: the head counter of a scope (the `u`/`ux` of `letV`, `letE`,
  `join`) is the recount of the scope;
* `P1.Term.unique`: two terms with the same erasure have the same counters. There is no
  second annotation of the same program.

**Pros.** The counter is part of the context, exactly as asked. The typing rules are the
standard ones of QTT, and each rule states its usage law locally. A rewrite that preserves the
multiset of uses (inlining a use-once value, moving a binding) preserves the type unchanged.
`UVar.head`'s `u ≠ 0` side condition disappears: a variable can only be mentioned where its
entry says `1`.

**Cons.**

* **The split is an input.** The toy's example must write the contexts of the sub-terms
  (`twoX`, `fourX`). For exact usages the split is determined bottom-up, but Lean's elaborator
  does not invert `Add`, so the Anf elaborator must compute and emit every split (or use smart
  constructors that synthesise contexts, which turns P1 into P3).
* **Environments are split as well.** `eval` projects environments along every `Add`/`Max`/`Scale`
  witness (`Ctx.Add.left/right`, …). The values are shared and only the counters split, but
  every semantic proof (`rename_eval`, `subst_eval`, all `*Eval.lean`) has to commute with
  these projections.
* **Renaming and substitution must preserve the splits.** Strengthening (dropping a `0`
  entry), weakening (adding one), and contraction (CSE merges two variables, so their counters
  add) each need a lemma per relation.
* **Every pass that changes uses changes the context**, e.g. `dce` dropping a value removes its
  uses from the outer counters. Such a pass returns `Σ C', Term C' τ × C' ≤ C` and transports
  environments along `≤`.
* **Three contexts triple the witnesses.** Every elimination carries an `Add` over `k`, `u` and
  `j`.

---

## 5. Proposal 2: input/output counters (Hodas–Miller style)

**Idea.** The judgement `{Γ} t : α {Δ}` of Hodas–Miller, used to make proof search in linear
logic deterministic, threads the resources: `Γ` is what is available before `t`, `Δ` what is
left after it, and a used linear hypothesis is replaced by `⊥` in `Δ`. Read the entries as
counters and the `⊥` marks become counts. Here the counters count **up**, because that keeps
exactness with `ω` and needs no budget to be known in advance:

* `{c} x {c[x ↦ c(x)+1]}`: a variable bumps its counter;
* `{c₀} a {c₁}`, `{c₁} b {c₂}` ⟹ `{c₀} a + b {c₂}`: straight-line code threads the counters;
* `{c₁} t₁ {c₂}`, `{c₁} t₂ {c₃}` ⟹ `{c₀} ifz e t₁ t₂ {max c₂ c₃}` (with `{c₀} e {c₁}`): the arms
  start from the same counters, and the branch leaves the larger result (an additive `&` that
  allows different uses per arm);
* a binder enters its scope with counter **`0`** and leaves it with counter **`u`**, so **the
  annotation is the output counter of the bound variable**;
* a closure body is counted locally from `0` and added to the outside scaled:
  `c₀ + ω·d`.

The toy keeps the types of the contexts (`TCtx`) apart from the counters (`Cnts`, one
`List UsageN` per context, missing entries meaning `0`). Values depend only on types, so
`eval` needs **no** casts or projections, unlike P1. Outputs are *computed* (functions in the
indices), so Lean infers them:

```lean
inductive PExpr (Γ : TCtx) : Cnts → Ty → Cnts → Type
  | uvar {c τ} (x : Var Γ.u τ) : PExpr Γ c τ (c.hit .u x.index)
  | kvar {c τ} (x : Var Γ.k τ) : PExpr Γ c τ (c.hit .k x.index)
  | lit  {c} (n : Nat) : PExpr Γ c .nat c
  | add  : PExpr Γ c₀ .nat c₁ → PExpr Γ c₁ .nat c₂ → PExpr Γ c₀ .nat c₂

inductive Term : TCtx → Cnts → Ty → Cnts → Type
  | ret  : PExpr Γ c₀ τ c₁ → Term Γ c₀ τ c₁
  | letV (u : UsageNPos) (ux : UsageN) :
      Term ⟨Γ.k, σ₁ :: Γ.u, []⟩ ⟨[], [0], []⟩ σ₂ ⟨dk, ux :: du, dj⟩ →
      Term ⟨.fn σ₁ σ₂ :: Γ.k, Γ.u, Γ.j⟩ ⟨0 :: (c₀.addScale dk du).k, (c₀.addScale dk du).u, c₀.j⟩ τ
        ⟨u.toN :: k₃, u₃, j₃⟩ →
      Term Γ c₀ τ ⟨k₃, u₃, j₃⟩
  | letE (u : UsageNPos) :
      PExpr Γ c₀ (.fn σ ρ) c₁ → PExpr Γ c₁ σ c₂ →
      Term ⟨Γ.k, ρ :: Γ.u, Γ.j⟩ ⟨c₂.k, 0 :: c₂.u, c₂.j⟩ τ ⟨k₃, u.toN :: u₃, j₃⟩ →
      Term Γ c₀ τ ⟨k₃, u₃, j₃⟩
  | ifz  : PExpr Γ c₀ .nat c₁ → Term Γ c₁ τ c₂ → Term Γ c₁ τ c₃ → Term Γ c₀ τ (c₂.max c₃)
  | join (u : UsageNPos) (ux : UsageN) :
      Term ⟨Γ.k, σ :: Γ.u, Γ.j⟩ ⟨c₀.k, 0 :: c₀.u, c₀.j⟩ τ ⟨k₁, ux :: u₁, j₁⟩ →
      Term ⟨Γ.k, Γ.u, σ :: Γ.j⟩ ⟨k₁, u₁, 0 :: j₁⟩ τ ⟨k₂, u₂, u.toN :: j₂⟩ →
      Term Γ c₀ τ ⟨k₂, u₂, j₂⟩
  | jump (x : Var Γ.j σ) : PExpr Γ (c₀.hit .j x.index) σ c₁ → Term Γ c₀ τ c₁
```

**Proved in the toy.**

* `P2.Term.exact : c'.at s i = c.at s i + t.erase.cnt s i`: output = input + reference count;
* `P2.Term.exact_closed`: starting from no uses, the output counters **are** the reference
  counts (this is P3's index, §6);
* the example: `body4.1 = ⟨[], [4], []⟩` and `retK.1 = ⟨[1], [], []⟩` hold by `rfl`. Lean
  computed them. `.letV (.succ 0) .omega body4.2 retK.2` and `.letV .omega (.fin 4) …` are
  rejected (`fail_if_success`).

**Lessons from writing the toy** (they apply to the real `Term` too).

* Output indices must be built from **separate variables** (`⟨u.toN :: k₃, u₃, j₃⟩`), not from
  projections of one (`⟨u.toN :: c₃.k, c₃.u, c₃.j⟩`). Lean does not solve `?c.k =?= […]` by
  eta-expanding `?c`, so the projection version does not elaborate.
* The counter functions must reduce by `whnf`. A `Cnt.zip` defined by well-founded recursion
  blocks unification. The toy's version is structural, recursing on the first list and mapping
  over the rest.

**Pros.** The counter is a property of the contexts, as asked. The judgement is deterministic,
with no splitting to guess. Values and environments are untouched. The binder rule
("enter at 0, leave at u") is easy to read. A definition binder's `u : UsageNPos` makes dead
code ill-typed.

**Cons.** Every judgement carries two counter vectors, so the signatures are long. Passes that
change uses return new output counters, as in P3. Composition is sequential, so moving code
past other code (hoisting, CSE) needs a lemma that commutes the counter updates. Input counters
other than `0` add nothing to the information (only the difference matters,
`P2.Term.exact`), which is the argument for P3.

---

## 6. Proposal 3: the usages as a synthesised index (the `Lvl` discipline)

**Idea.** This is your proposal 1 taken literally: *"terms are indexed by the usages they
consume … u is not a parameter you choose, it is read directly from the head of b's usage
vector."* The index has three vectors, one per context, and is computed by the constructors
exactly as `Lvl` is today. In the words of the `Term` module doc, *"the level is computed by
the constructors …, so it cannot lie"*. A binder stores **no** annotation, and a definition
binder only carries a proof that the head is not `0`:

```lean
inductive PExpr : TCtx → Ty → Cnts → Type
  | uvar (x : Var Γ.u τ) : PExpr Γ τ (Cnts.one .u x.index)
  | kvar (x : Var Γ.k τ) : PExpr Γ τ (Cnts.one .k x.index)
  | lit  (n : Nat) : PExpr Γ .nat ⟨[], [], []⟩
  | add  : PExpr Γ .nat U₁ → PExpr Γ .nat U₂ → PExpr Γ .nat (Cnts.add U₁ U₂)

inductive Term : TCtx → Ty → Cnts → Type
  | ret  : PExpr Γ τ U → Term Γ τ U
  | letV : Term ⟨Γ.k, σ₁ :: Γ.u, []⟩ σ₂ Ub → Term ⟨.fn σ₁ σ₂ :: Γ.k, Γ.u, Γ.j⟩ τ Ut →
      Cnt.hd Ut.k ≠ 0 → Term Γ τ (Cnts.letV Ub Ut)        -- ω·tail(Ub) + tail(Ut)
  | letE : PExpr Γ (.fn σ ρ) Uf → PExpr Γ σ Ua → Term ⟨Γ.k, ρ :: Γ.u, Γ.j⟩ τ Ut →
      Cnt.hd Ut.u ≠ 0 → Term Γ τ (Cnts.add (Cnts.add Uf Ua) ⟨Ut.k, Cnt.tl Ut.u, Ut.j⟩)
  | ifz  : PExpr Γ .nat Ue → Term Γ τ U₁ → Term Γ τ U₂ → Term Γ τ (Cnts.add Ue (Cnts.max U₁ U₂))
  | join : Term ⟨Γ.k, σ :: Γ.u, Γ.j⟩ τ Ub → Term ⟨Γ.k, Γ.u, σ :: Γ.j⟩ τ Um →
      Cnt.hd Um.j ≠ 0 → Term Γ τ (Cnts.add ⟨Ub.k, Cnt.tl Ub.u, Ub.j⟩ ⟨Um.k, Um.u, Cnt.tl Um.j⟩)
  | jump (x : Var Γ.j σ) : PExpr Γ σ Ue → Term Γ τ (Cnts.add (Cnts.one .j x.index) Ue)
```

The annotation of `letV` is `Cnt.hd Ut.k` (`Term.letV.use`) and that of the closure parameter
is `Cnt.hd Ub.u`. The pretty printer and the backend read them from the index.

**Proved in the toy.**

* `P3.Term.exact : U.at s i = t.erase.cnt s i`: the index is the reference count;
* `P3.Term.letV_use_exact`: the read-off annotation is the recount of the scope;
* the example elaborates with no annotation written (`by decide` discharges the `≠ 0`
  side conditions), and the read-off annotations are `(4, 1)` by `rfl`.

**About "part of the context, not a function from ctx to Usage".** In P3 the vectors are
*parallel* to the contexts (entry `i` of `U.u` belongs to entry `i` of `Γ.u`). Zipping them
into the context entries turns the synthesised index into P2's output context with input `0`.
P2 and P3 are the same information, presented as a judgement or as an index, so the choice
between them is presentation and ergonomics, not expressiveness.

**Pros.** It is the smallest change to the architecture. It is one more index, computed like
`Lvl`, and the passes that already return `(o' : Lvl) × …` (`Val.relvl`, `Term.dce` through
`castLvl`, …) return `(o' : Lvl) × (U' : Uses) × …`. Nothing has to be written by the
elaborator, and Lean computes it. `Term.dce`'s re-annotation disappears (there is nothing to
re-annotate), `Occ.lean` becomes the specification `index = count`, and `Reannot.lean` and the
`reuse` renamings go away.

**Cons.**

* It shares the `Lvl` cost: functions in indices, so dependent pattern matching on a term
  with a *concrete* index needs casts (`Term.castLvl` exists for this reason).
* Vectors have several representations (`[]` and `[0]` both mean "unused"), so equalities
  are stated through `Cnt.at`. Normalising (trimming trailing zeros) or indexing by
  length-checked vectors fixes this at the cost of more arithmetic.
* Large terms make Lean compute large vectors while elaborating. Step 0 can emit the literal
  so that Lean only checks it.

---

## 7. Proposal 4: annotations as a checked cache

**Idea.** Keep the binders' fields, as today, and make wrong values unrepresentable by a
subtype. A term is `Exact` when it is the annotation pass applied to its own erasure. Smart
constructors are the only way to build an `ETerm`, and each computes the annotation of the
binder it creates:

```lean
inductive ATerm where           -- annotations stored, as today
  | ret (e : RExpr) | letV (u ux : UsageN) (body t : ATerm) | letE (u : UsageN) (f a : RExpr) (t : ATerm)
  | ifz (e : RExpr) (t₁ t₂ : ATerm) | join (u ux : UsageN) (body main : ATerm) | jump (j : Nat) (e : RExpr)

def ATerm.Exact (a : ATerm) : Prop := a = annotate a.erase
abbrev ETerm := { a : ATerm // a.Exact }

def ETerm.letV (b t : ETerm) : ETerm :=
  ⟨.letV (t.1.erase.cnt .k 0) (b.1.erase.cnt .u 0) b.1 t.1, by …⟩
```

**Proved in the toy.** `P4.erase_annotate` (annotating loses nothing), `P4.ETerm.letV_exact`
(an exact `letV` stores its recounts), `P4.ETerm.unique` (an exact term is determined by its
erasure). The snapshot's annotation is refuted by `decide`.

**Pros.** The `Term` type and the roughly 57 files that mention usages keep their shape. The guarantee is a single
invariant, and the existing `Term.dce` becomes the `annotate` of the proof.

**Cons.** The guarantee lives *next to* the term. Matching on an `ETerm` gives an `ATerm` plus
a proof that has to be unfolded to learn anything about a sub-term. Smart constructors recount
the scope (quadratic) unless the counts are cached at the nodes, and caching them is P3 without
the index. In the real `Term`, which is already intrinsically typed, the subtype sits on top of
the indices instead of replacing them. Every pass must rebuild through smart constructors or
re-establish `Exact`.

---

## 8. Migration sketch (for the chosen proposal)

1. **`Syntax/Usage.lean`**: add `UsageN`, `UsageNPos` with `+`, `max`, `scale` and their laws
   (no Mathlib). Delete `Usage01ω`/`Usage1ω` once nothing uses them. `UsageAlgebra.lean` (the
   Mathlib instances) can go.
2. **Step 0** (§1.3) in `TermElab/Anf*`: `Out.uses`, binder annotations from `r.uses`.
3. **`Syntax/Ctx.lean`, `Syntax/Term.lean`**:
   * P1: binders keep `use : UsageN`, relations `Add/Max/Scale/Zero` over the three contexts,
     `UVar.head` requires the rest of the context to be zero;
   * P2: `Term` gains input/output `Uses`, and binders read the head of the output;
   * P3: `Term` gains a `Uses` index, binders lose their `use` field, and definition binders
     get `hd ≠ 0`;
   * P4: no change, plus `ETerm` and smart constructors.
4. **`Semantics/*`**: unchanged for P2–P4. For P1, environments are projected along the
   splits.
5. **`Rename/*`**: P3/P2 renamings map the vectors (a permutation or a strengthening of a
   `0` entry), and `reuse`/`reannot` disappear. In P1 renamings preserve splits.
6. **`Optimize/*`**: `Occ.lean` becomes the exactness theorem (`index = count`). `Dce.lean`
   only drops dead code (re-annotation is gone), with §2.3 deciding the level-preserving
   case. Passes return the new usages in their Σ (P2/P3) or a new context with a witness (P1).
7. **`Term/Pretty.lean`, `JsTerm/Lower/*`**: print `[n]`/`[ω]` and read usages from the index
   (P3), the output counters (P2) or the context (P1). `usedFields` becomes `u ≠ 0`, and "used
   once" becomes `u = 1` (now meaning exactly one use on every path).
