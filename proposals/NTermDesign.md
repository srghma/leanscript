# `LeanScript.NTerm`: proposal B as implemented, and what to improve

This note describes the normal-form terms of `LeanScript/NTerm/` (proposal B of
`NormalFormProposals.md`: two contexts, *known* and *unknown*), as they are in the code now,
and answers four questions about the design:

1. Does the usage `0 | 1 | ω` make sense for every binder? Should some binders only allow
   `1 | ω`, so that a dead variable cannot be written at all?
2. What is the *open* flag, exactly?
3. Join points for loops: which loops, and does it make sense? Or only for well-founded
   recursion (not implemented)?
4. Does the proposal keep the strict A-normal-form design?

The current `LeanScript.Term` is not changed; `NTerm` is a new module next to it, and every
constructor of `Term` has a counterpart (table in §2).

---

## 1. The rule

> Terms are in A-normal form. **A redex whose variables are all known (a closed redex) is
> evaluated, and the type makes sure of it.** A redex that is stuck on an unknown is kept,
> and then it is better to **share too much than too little**: a computation is never
> duplicated. The same goes for join points: too many join points is fine (a dead one is
> removed by the optimiser), too few is not.
> Every binder has a usage `0 | 1 | ω`, so dead variables can be found and removed.

### 1.1 Three contexts

A statement `Term Δ Φ Γ τ js` has

| context | what it holds | bound by |
|---|---|---|
| `Φ : KCtx` — **known** | values whose *shape* is known: closures, delays, record/union/array/list/`data_in` literals | `letV` only |
| `Γ : UCtx` — **unknown** | anything whose value is not known when the term is built | `letE` (the result of a computation), `record_casesOn` and union case fields, the parameters of closures, loop bodies and join points |
| `js : UCtx` — **join points** | the type of the parameter of each join point | `Branch.join` |

Every entry has a `Usage`. A known entry also has an `isOpen : Bool` (§3).

A variable is a typed de Bruijn index (`UVar Γ τ`, `KVar Φ τ o`) whose `head` constructor
needs a proof `use ≠ .zero`. **You cannot refer to a binder whose usage is `zero`.**

### 1.2 The grammar (`LeanScript/NTerm/Syntax.lean`)

```
Neu     Φ Γ   ::= var x                          -- x : UVar Γ τ, an unknown
                | data_out b j Neu | cond Neu PExpr PExpr
                | extern e (Args true)           -- at least one open argument
PExpr   Φ Γ o ::= neu Neu                        -- o = true
                | kvar k                         -- a known value, by name; o is its flag
                | lit | enum_mk                  -- o = false
                | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
                | data_in b j PExpr              -- o = openness of the arguments
Val     Φ Γ o ::= lam Body | thunk_mk Body | lazy_mk Body
                | record_mk | union_mk | array_mk | list_mk | data_in
Body    Φ Γ bs o ::= closed (Term Φ.closedOnly bs)   -- o = false
                   | opened (Term Φ (bs ++ Γ))        -- o = true, needs Γ ≠ []
Comp    Φ Γ   ::= app PExpr PExpr                -- function or argument open
                | share Neu
                | nat_rec | array_foldl | data_rec | data_brec
                                                 -- an operand or the body open
                | thunk_force (PExpr true) | lazy_force (PExpr true)
Term    Φ Γ js ::= ret PExpr
                 | letV u Val Term               -- extends Φ
                 | letE u Comp Term              -- extends Γ
                 | record_casesOn us Neu Term    -- extends Γ with the fields
                 | branch Branch
                 | jump j PExpr
Branch  Φ Γ js ::= ite Neu Term Term | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
                 | join σ u uₓ Term Branch        -- only in front of a branch
```

### 1.3 How the types enforce "closed redexes are evaluated"

Every elimination needs something *open* (something that mentions an unknown):

* **Neutral eliminations** (`record_casesOn`, `ite`, `enum_casesOn`, `union_casesOn`,
  `data_out`, `cond`) take a `Neu`, and a `Neu` is ultimately an unknown variable. A known
  value is **never** taken apart: `Neu` has no constructor for a `KVar`. So
  `match ⟨1, 2⟩ with | ⟨a, b⟩ => …` and `if true then …` cannot be written.
* **`extern e args`** needs `args : Args σs true`. `1 + 2` cannot be written, but `n + 2` can.
* **`app f a`** needs a proof `(of || oa) = true`. A closed known closure applied to a
  closed argument cannot be written, so the normaliser has to β-reduce it.
* **Folds** (`nat_rec`, `array_foldl`, `data_rec`, `data_brec`) need an open operand or an
  open body. A loop over a literal whose body is closed has to be run by the normaliser.
* **Forces** take a `PExpr (.thunk τ) true`: an unknown delay, or an open known delay. The
  body of a closed delay is already a value (below), so there is nothing left to force.
* **Join points** only come in front of a `Branch`. `join j x := b; jump j v` (a redex)
  cannot be written; the normaliser substitutes `v` into `b` instead.

What this buys is proved in `LeanScript/NTerm/Closed.lean`:

* `Neu.not_closed`, `Comp.not_closed`, `Branch.not_closed`: when there is no unknown in
  scope (`Γ = []`) and the known values are closed, no neutral term, no computation and no
  branch can be written at all;
* `Term.closed_isValue`: such a term is a chain of `letV`s ending in `ret v`;
* `Term.run_isValue`: in particular every top-level term (`Term Δ [] [] τ []`) is a value;
* `Term.closedBody_isValue`: the same for the body of a closed closure/delay/loop.

This is the "most important" part of the request: **there is no unevaluated chunk when all
variables are known**, and it is a theorem about the type, not a property of one normaliser.

### 1.4 How sharing works when a redex is stuck

* A closure, a delay or a data literal is bound once by `letV` and then **passed by name**
  (`PExpr.kvar`). Using it twice does not copy it.
* A known closure applied to an *open* argument is kept as `app (kvar f) a` — the call
  stays, the closure is shared, and the body is **not** inlined. (Inlining it when it is used
  once is an optimisation, allowed by usage `1`, never required.)
* A known **delay** forced twice: if the delay is closed, its body is already a value (§1.3),
  so forcing it is free. If it is open, `lazy_force (kvar d)` stays a computation; each force
  is a `letE`, and the body is **not** inlined at the force. This is the correction you asked
  for: in the earlier table "known `lazy_mk`, forced → body inlined at every force" is gone.
  Note the semantics of `lazy` is still "recompute at every force"; the normal form does not
  merge two forces of a `lazy` into one (that would change `lazy` into `thunk`). If a delay is
  meant to be computed once, it should be a `thunk`.
* A neutral expression that is needed twice is named once with `letE u (share n)`. `share`
  takes a `Neu` only: sharing a literal or a known value is pointless (it already has a name,
  or is free to rebuild), so `share` of a closed expression cannot be written.
* Branches that continue with the same code get a join point, never a copy of the code.

### 1.5 Semantics and optimisations that are proved

* `Eval.lean`: a denotational semantics for all layers, and `Term.run`.
* `Rename.lean`, `RenameEval.lean`: partial renamings of the three contexts, and
  `Term.rename_eval`: renaming does not change the meaning.
* `Occ.lean`: occurrence counting (`countU`, `countK`, `countJ`) as `Usage`s; an occurrence
  inside a closure, delay or loop body is `scale`d to `ω`, because the body can run many times.
* `Dce.lean`: `Term.dce` recomputes every usage bottom-up, drops every `letV`/`letE`/join point
  whose usage is `0`, and re-annotates all binders. `Term.dce_eval` / `Term.dce_run`: it does
  not change the meaning.
* `Weaken.lean`: thinnings, and `PExpr.toClosed` (a closed pure expression can be moved into
  a closed body).
* `TermTests/NTermTest.lean`: hand-written normal forms (`mulTwice`, `shareTwice`,
  `callOpen`, `deadLets` cleaned by `dce` checked by `rfl`) and examples that the type
  rejects.

---

## 2. Correspondence with `LeanScript.Term`

| `Term` | `NTerm` | when |
|---|---|---|
| `PExpr` (any) | `PExpr … o` | `o` computed by the constructors |
| `Neu` | `Neu` | an unknown, or an elimination of one; no known variables inside |
| `Comp.app` | `Comp.app` with `(of‖oa)=true` | otherwise β-reduced |
| `Comp.lam` | `Val.lam` + `letV` | a closure is a known value |
| `Comp.share` (of any `PExpr`) | `Comp.share` (of a `Neu` only) | sharing a known value is by name |
| `nat_rec`, `array_foldl`, `data_rec`, `data_brec` | same, with an open operand or body | otherwise run |
| `thunk_mk`, `lazy_mk` | `Val.thunk_mk`, `Val.lazy_mk` + `letV` | a delay is a known value |
| `thunk_force`, `lazy_force` | same, of an open delay | otherwise already a value |
| `ret`, `letE`, `record_casesOn`, `jump` | same (+ `letV`) | `record_casesOn` of a `Neu` |
| `ite`, `enum_casesOn`, `union_casesOn` | `Branch.*` of a `Neu` | known scrutinee → pick the branch |
| `join` | `Branch.join` | only in front of a branch |

---

## 3. Question 2: the open flag

**Definition.** Something is *open* when it mentions an unknown — directly (a `Neu`), or
through a known value that is itself open. `PExpr`, `Args`, `Elems`, `Val` and `Body` are
indexed by `o : Bool`, and the flag is **computed by the constructors**, so it cannot lie:

* `neu n : PExpr … true`; `lit`, `enum_mk` : `… false`;
* `Args.cons e es : Args … (o₁ || o₂)`, same for `Elems`; a record/union/array/list/`data_in`
  literal is as open as its arguments;
* `kvar k : PExpr … o` where `k : KVar Φ τ o`: a known variable is as open as the entry
  `⟨τ, u, o⟩` it points to, and `letV u (v : Val … o) body` pushes exactly that `o`;
* a body is `closed` (sees only `Φ.closedOnly` and its own parameters, `o = false`) or
  `opened` (sees `Φ` and `Γ`, `o = true`).

**Why a known value can be open.** "Known" means *known shape*, not *known value*. In
`fun n => ⟨n, 3⟩` the record is known (it can be projected without a case analysis — the
normaliser just reads field `1`) but it mentions `n`. In
`fun n => "abc".any (fun c => c == n)` the inner closure is a known closure (it can be
inlined or called), but its body mentions `n`. These are open known values.

**Why the flag is needed.** Without it the rule of §1.3 cannot be stated: "`app f a` needs
an unknown operand" would allow `app (kvar f) lit` for a closed `f`, which is a closed redex.
With the flag, `app` needs `of || oa`: calling an **open** known closure on a literal is fine
(its body is stuck on the outer unknown), calling a closed one is not. The same argument
applies to the forces and the folds.

**Closed bodies see only closed known values.** `Body.closed` is typed in
`KCtx.closedOnly Φ`, where every open entry is hidden (its usage becomes `zero`, so no
`KVar` can point to it). This is what makes `Term.closedBody_isValue` true: inside a closed
body nothing unknown is reachable, so the body is itself a value chain.

**Honesty of the flag and known imprecisions.**

* `Body.opened` only requires `Γ ≠ []`; it does not require that the body *actually*
  mentions an unknown. So a closed body can be marked open when there is an unknown in scope.
  This is on the "over-share / under-evaluate" side (a loop that could have been run is kept),
  never on the unsound side, but it weakens "closed redexes are evaluated" to "closed redexes
  **outside of open-marked bodies** are evaluated". A normaliser should always pick `closed`
  when it can (it can decide it by checking `countU` of the outer context, and strengthening
  the body with `Weaken.lean`). *Improvement:* make it exact by construction, e.g. index
  `Term` by the set of unknowns it mentions, or add a checked predicate `Body.Tight`
  (`opened` ⇒ some outer unknown has non-zero count) and prove the normaliser produces it.
* `closedOnly` hides an open entry by setting its usage to `zero`. That conflates *hidden* and
  *dead*: `countK` of the outer entry ignores the body anyway, but a reader may take the
  `zero` for "dead". *Improvement:* a separate `visible : Bool` in `KBinder`, or a
  `KCtx.filter` view with an explicit injection (the current `mask`/`unmask`).

---

## 4. Question 1: `0 | 1 | ω` everywhere, or `1 | ω` for some binders?

**Binders fall into two groups.**

| binder | can it legitimately be unused? | why |
|---|---|---|
| `letV` (a known value) | **no** | if it is unused, drop it |
| `letE` (a computation) | **no** | computations are pure and total; if unused, drop it |
| `join j` (the join point itself) | **no**, *after* optimisation | the normaliser may create too many (as you asked); `dce` removes them |
| `record_casesOn` / union case fields | **yes** | a pattern names every field, used or not |
| closure parameter (`lam`) | **yes** | `fun _ => 3` |
| loop binders (`nat_rec` acc/pred, `array_foldl` elem/acc, `data_rec` arg) | **yes** | `Nat.rec z (fun _ acc => …)` |
| join-point parameter `uₓ` | **yes** | a join point called for its control flow only (`Unit`) |

So a single `1 | ω` type for *all* binders would be wrong: pattern binders need `0`.
For **definition binders** (`letV`, `letE`, `join`), `{1, ω}` is the right domain for the
*output of the optimiser*.

**But a `1 | ω` annotation alone does not make dead binders impossible.** The annotation is
a claim, and nothing in the current type checks it against the body: the `head` constructor
of `UVar`/`KVar` only forbids *using* a `zero` binder; it does not force a `one`/`many` binder
to be used. So restricting `letV` to `u ∈ {1, ω}` would only remove the honest way of writing
a dead binding, not the dead binding. Dead-by-construction needs the usage to be *checked*,
in one of two ways:

1. **Graded (usage-indexed) syntax.** Index every syntactic class by a usage vector for its
   contexts (`Term Δ Φ Γ τ js (ks : UsageVec Φ) (us : UsageVec Γ)`), with `var` producing the
   unit vector, `Args.cons` adding vectors, bodies scaling them to `ω`, and branches taking
   the join (see below). Then `letV u v body` requires `body`'s vector to have `u` at the new
   position, and `u ≠ 0` can be demanded. This is the fully typed answer; it is the
   "relevant/graded type system" of quantitative type theory. The price is large: every
   renaming and every normaliser step has to rebuild the vectors (all of `Rename*.lean`
   becomes about vector arithmetic), and the indices make pattern matching and `decide`
   noticeably heavier. I do not recommend it now.
2. **A checked predicate** `Term.WellCounted : Term … → Prop` — every binder's annotation is
   the (abstracted) count `countU`/`countK`/`countJ` of its scope, and definition binders are
   non-zero. `Term.dce` is the natural producer; the theorem to add is
   `(t.dce).WellCounted` (and "`dce` is idempotent"). This keeps the syntax simple, is cheap,
   and gives the same guarantee to the code generator. **Recommended.**

With (2), the definition binders can be given type `DUsage := one | many` (a subtype of
`Usage`) when `dce` has run; before that the normaliser is free to produce `zero`.

**Why the soundness of `1` matters.** `0` only licenses dropping (safe even if wrong in the
direction "said ω, was 0"). `1` licenses **inlining**, and inlining an expression that is in
fact used twice duplicates work, which is exactly what the sharing rule forbids. Today the
annotations are only trusted after `dce` (which recomputes them), and `dce_eval` proves the
meaning is preserved — but no theorem yet says the annotations are *exact*. That is the gap
(2) closes.

**Two refinements of counting, both cheap:**

* **Branches.** `countU` adds the counts of the arms of `ite`/`case`
  (`1 + 1 = ω`). Dynamically only one arm runs, so the right combination is the *max*
  (`1 ⊔ 1 = 1`). With `add`, a variable used once in each arm is never inlined. Switching the
  arms to `max` is sound for inlining into a *straight-line* position and is what GHC does
  ("occurs once in each branch").
* **Under a body.** Counts inside a closure/delay/loop are scaled to `ω`, which is right for
  inlining *work*; but inlining a *known value* (a `kvar` of a closure) used once under a
  lambda is still fine because a known value is free to rebuild. The normaliser can
  distinguish these; the `Usage` domain does not need to.

---

## 5. Question 3: join points and loops

**Which loops exist.** The language has no general recursion. Loops are the folds:
`nat_rec`, `array_foldl`, `data_rec`, `data_brec`. The surface `for` loop over a range and a
structurally terminating `while` loop are translated by
`LeanScript/TermElab/ToTerm/While.lean` into a `nat_rec` of a fixed number of steps over a
`ForInStep β` state (`LeanScript/Term/BoundedLoop.lean` proves the bound is enough, so it is
not fuel: `boundedLoop_done`, `boundedLoop_stable`). `break`/`return` become `.done v`, which
the next steps keep.

**What join points do in NTerm.** A join point is a *non-recursive* local continuation for
the tail of a branch: `join j x := k; case n of … → jump j a | … → jump j b`. It replaces
code duplication, and is compiled to a labelled block / local function called in tail
position. This is the sharing rule applied to control flow.

**Join points and loop bodies.** A loop body is a `Body … bs τ o` whose term has `js = []`:
you cannot jump out of a body into an enclosing join point. This is correct, because a body is
a function called by the fold, not a block of the enclosing statement. Inside a body, join
points are allowed as usual (the body's own branches share their tails).

**"Jumping out of a loop" is already handled.** The only thing a jump out of a loop body
would mean is an early exit — `break`/`return`. With bounded folds this is the `ForInStep`
encoding: the step returns `.done v`, and later steps are identity. A back-end can compile
`nat_rec` over `ForInStep` into a real `for`/`while` loop with `break`, and the `.done` test at
the head of each step into the loop condition; that is a code-generation pattern, not a new
term former.

**Recursive join points (`joinrec`).** A join point that can jump to itself is a *loop*
(GHC's `joinrec`, a `while` loop in SSA). It only makes sense with **general or well-founded
recursion**: with bounded folds, every loop is a fold with a known number of iterations, and
its body is a closure-like `Body`. So:

* for the current language (structural recursion, bounded loops): **no join points for
  loops are needed**; non-recursive join points for branches are all we need;
* if well-founded recursion is added (`WellFoundedRecursionAssessment.md`), a tail-recursive
  function should normalise to a **`joinrec`** whose parameter is the loop state, with the
  termination measure erased — this is the natural target for `while` loops that are not
  structurally bounded. Adding it later is a new `Branch.joinrec σ u uₓ body main` where
  `body` is typed with `⟨σ, u⟩ :: js` (it can jump to itself). The "better too many than too
  few" rule carries over unchanged; `countJ` would count self-jumps as `ω`.

---

## 6. Question 4: strict A-normal form?

**Yes, and stricter than `Term`.**

* **Same as `Term`:** every computation is named by a `let` (`letE`); arguments of
  computations, externs, constructors and jumps are pure expressions (`PExpr`); branches and
  jumps are only in tail position; join points only in tail-branch position.
* **Stricter:**
  * closures and delays are *values* (`Val`), named by `letV`, not computations; they are
    only ever passed by name;
  * a known value is never eliminated (no `record_casesOn`/`case`/`force`/`app` of a closed
    known value): those redexes are gone, by type (§1.3);
  * `share` takes a `Neu`, not an arbitrary `PExpr`;
  * `join; jump` redexes cannot be written.
* **One non-ANF-looking construct stays**, as in `Term`: `cond c a b` (the pure conditional
  `c ? a : b`) is a `Neu` whose arms are pure expressions. It is cheap and total, so it does not
  need to be a branch with join points; it is only allowed on a neutral condition.
* Extern calls on open arguments are `Neu` (inside pure expressions), as in `Term`: an extern
  is pure, so nesting `n + (m * 2)` without naming `m * 2` is accepted. If you want *every*
  extern call named (a stricter ANF), `Neu.extern` would move to `Comp`; the cost is more
  `letE`s, which `share`/inlining then has to undo. I recommend keeping it as is.

---

## 7. What is not done yet, and the recommended order

1. **The normaliser `Term → NTerm`** (normalisation by evaluation): a semantic domain where
   known values are Lean values/closures and unknowns are `Neu`s, a `quote` back to
   `NTerm`, and the theorem `normalise_eval : (normalise t).run = t.run`. Rules it must follow:
   pick `Body.closed` whenever possible (§3); share every `Neu` used twice with `letE share`;
   create a join point for every branch continuation (§5); run closed folds and forces.
2. **`Term.WellCounted` and `(dce t).WellCounted`** (§4, option 2), then `DUsage` for
   definition binders.
3. **Branch counts with `max`** instead of `add` (§4).
4. **An exact open flag for bodies** (§3), or at least a proof that the normaliser picks
   `closed` whenever it can.
5. **Pretty printer and code generation** from `NTerm`.
6. **`joinrec`**, only together with well-founded recursion (§5).

One practical caveat of the rule itself: "every closed redex is evaluated" means the
normaliser runs closed loops *at compile time*. `nat_rec 1000000000 …` with a closed body is
a closed redex, and the type forces the normaliser to compute it. If that is a problem, the
escape hatch is to treat the bound as an unknown (e.g. a top-level parameter), not to weaken
the rule.
