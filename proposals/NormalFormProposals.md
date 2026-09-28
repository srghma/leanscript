# Making "a closed `Term` is its own value" true: normal forms by construction

`TermTests/Semantics/ClosedEvalTest.lean` proves that, with the grammar as it is today, evaluating a
closed `Term` is **not** the identity: `ret (3 + 4)` and `ret 7` are different closed terms
with the same value. This document proposes ways to change the grammar so that the statement
becomes true, with the normalisation done when Lean is elaborated to `Term`
(`LeanScript/TermElab/Anf.lean`, `#leanscript_to_term`, `[Term| …]`).

The proposals are in your order of preference: **structural** solutions first (the types rule
out non-normal terms), then **`Prop`-based** ones (a proof that the term is normal travels with
it, like `TyWf`'s `:= by ty_wf`), then **`Bool`-based** ones (a checker plus `= true`). I read
"Prob" in your request as `Prop`.

**What is checked.** The central claim of proposal A is checked in a small stand-alone toy,
`proposals/NormalFormToy.lean`. It is outside the Lake build; check it with
`lake env lean proposals/NormalFormToy.lean`, which currently reports no errors, warnings or
`sorry`. `#print axioms` on its theorems lists only `propext` and `Quot.sound`. The toy is a
cut-down language with `nat`, `bool`, `fn`, two externs, `let`, `if`, application and
`Nat.rec`. It proves:

* `Neu.not_closed`, `Comp.not_closed`: there is no closed neutral expression and no closed
  computation;
* `Term.closed_ret`: every closed statement is `ret v`;
* `Term.closed_eq_quote`: at a first-order type, a closed statement is `ret (quote t.run)`;
* `Term.closed_run_injective`: so `run` is injective on closed statements;
* `addT_rejected`: the old counterexample `ret (3 + 4)` no longer typechecks.

Proposal B is checked the same way in `proposals/NormalFormBToy.lean` (see §B), and the
examples of §B.5 are translated with today's `#leanscript_to_term` in
`proposals/NormalFormBExamples.lean`, whose printed output is quoted there.

Everything else here, including all statements about the real `LeanScript.Term`, comes from
reading the sources. It is design discussion, not a formal result.

---

## 0. The target: what "true" should mean

`Term.eval` returns a Lean value (`Ty.Den Δ τ`), not a `Term`, so "eval is the identity" has
to be stated through a read-back function (`quote`). There are two levels:

```lean
/-- T1 (every type): a closed statement is the answer of a value. -/
theorem Term.closed_ret (t : Term Δ [] τ []) : ∃ v : PExpr Δ [] τ, t = .ret v ∧ v.IsIntro

/-- First-order types: their values are finite trees of literals and constructors
    (`prim`, `enum`, `record`, `union`, `array`, `list`, `data` over a first-order `Δ`;
    no `fn`, and no `thunk`/`lazy` unless they are quoted as delays of values, see §2). -/
inductive Ty.FO (Δ : DSig ks) : Ty ks → Prop

def PExpr.quote : (τ : Ty ks) → Ty.FO Δ τ → Ty.Den Δ τ → PExpr Δ Γ τ

/-- T2 (first-order types): a closed statement is the quotation of its own value. -/
theorem Term.closed_eq_quote (h : Ty.FO Δ τ) (t : Term Δ [] τ []) :
    t = .ret (PExpr.quote τ h t.run)

/-- Corollary: closed statements of a first-order type *are* their values. -/
def Term.closedEquivDen (h : Ty.FO Δ τ) : Term Δ [] τ [] ≃ Ty.Den Δ τ
```

T2 cannot hold at function types, even in principle: `fun x => x + 0` and `fun x => x` are
different normal terms with equal values (function extensionality), and equality of
functions is not decidable. So T2 is limited to first-order types, and T1 is the statement at
every type. A closure is a value, just as `fun` is a normal form in the λ-calculus.

## 1. What breaks it today (the holes to close)

Each item is a closed well-typed term that still computes. Every proposal has to rule out
all of them, either in the types or with a proof.

1. **Extern on values.** `Neu.extern e args` is neutral whatever its arguments are, so
   `PExpr.lean_nat_add 3 4` is a closed "neutral" term. This is the root cause: in
   `LeanScript/Term/PExpr.lean`, "neutral" means "not an introduction form", not "stuck on a
   variable".
2. **Things that are neutral only through that.** `ite`, `cond`, `enum_casesOn`, … are all
   allowed on such a call (`ite (lean_nat_dec_lt 1 2) …`, the `iteT` of `ClosedEvalTest`).
3. **`let` hides values.** "A value bound by a `let` is a variable, hence neutral." For
   example, `letE (share (lean_nat_add 3 4)) (ite (lean_nat_dec_lt (var 0) 5) …)`. The
   normaliser also turns a Lean term of unknown shape into a neutral variable by `let`-binding
   it (`Anf.neutral`).
4. **β-redex through `let`.** `letE (lam b) (letE (app (var 0) (lit 3)) …)` is well typed:
   `app` takes any pure expression as its function, including a variable bound to a `lam`.
5. **Folds over literals.** `nat_rec (lit 3) z s`, `array_foldl (array_mk …) z s` and
   `data_rec … (data_in …)` take any `PExpr` (on purpose, see the module doc of
   `Term.lean`).
6. **Delays.** `letE (thunk_mk t) (letE (thunk_force (var 0)) …)`, and the same with `lazy`.
7. **Join points used once.** `join σ body (jump .head v)` is a redex: it is `body[v/x]`.
8. **Constants.** A zero-argument extern (`lean_version_get_major : [] → lazy nat`) is a
   closed call.
9. **Unquotable values.** `Ty.list` has no introduction form in `PExpr` (only `array_mk`
   exists), so a closed list value such as `lean_array_to_list #[1, 2]` has no normal form to
   reduce to. A `list_mk` constructor has to be added whatever else is chosen.

## 2. Infrastructure every proposal needs

* **`PExpr.list_mk : Elems Δ Γ t → PExpr Δ Γ (.list t)`** (hole 9), with its evaluator case.
* **`Ty.FO` and `PExpr.quote`** (§0). `quote` at `.prim p` is `.lit p v` (every `p.denote`
  already has a literal); at `.enum`/`.record`/`.union`/`.array`/`.list` it quotes the parts;
  at `.data` it goes through `data_in`, by structural recursion on the value. For T2 we also
  need `quote` to be a left inverse of evaluation on closed introduction forms. That follows
  because each introduction form is injective and the forms are disjoint: `CtorIx` picks
  distinct injections of a union, `Fin` distinct enum constructors, and so on.
* **An elaboration-time evaluator for externs.** When every argument of an extern call is a
  value, the normaliser computes the call. It builds the Lean expression
  `Extern.eval e ⟨v₁, …⟩`, evaluates it with `Lean.Meta.evalExpr` (the catalogue is
  ordinary compiled Lean code), and turns the result back into `Term` syntax with a
  meta-level `quoteStx` (`ToExpr`-style, one case per `LeanPrimTy.denote`; `Float` through
  `Float.ofBits`). If the result type is not first-order:
  * `thunk`/`lazy` of a value: quote it as the delay of `ret v`. This needs `thunk_mk` and
    `lazy_mk` to become values (proposal A moves them into `PExpr`).
  * `fn`: this cannot be quoted. No current entry returns a function; if one ever does, it
    must stay an opaque *value* (`PExpr.const e args`, all arguments values), and T2 does
    not apply at that type.
* **Smart constructors, in Lean rather than in `MetaM`** (for code that builds terms, for
  substitution, and for `rfl` tests). `LeanScript/Term/Elim.lean` already has
  `PExpr.mkDataOut`, `PExpr.mkCond`, `Term.mkIte` and `Term.mkEnumCases`, which reduce when
  the argument is an introduction form. We add `PExpr.mkExtern e args`, which is
  `quote (e.eval …)` when all the arguments are values and a call otherwise, plus `mkApp`,
  `mkNatRec`, `mkFoldl` and so on. `ExternShorthands` would then generate the shorthands
  through `mkExtern`, so that `PExpr.lean_nat_add 3 4 = 7` holds by `rfl`.

---

## Proposal A (structural, recommended core): *stuck* neutral forms

Change what "neutral" means, from "not an introduction form" to **"stuck on an unknown
variable"**. Then a neutral term needs a variable, a closed context has none, and T1 and T2
follow by a short induction. This is proved on the toy.

### Grammar changes (relative to `LeanScript/Term/{PExpr,Term}.lean`)

```lean
inductive Neu (Δ) : Ctx ks → Ty ks → Type where
  | var      : Var Γ τ → Neu Δ Γ τ
  | data_out : … → Neu Δ Γ (.data …) → Neu Δ Γ (unfold …)          -- unchanged
  | cond     : Neu Δ Γ .bool → PExpr Δ Γ τ → PExpr Δ Γ τ → Neu Δ Γ τ  -- unchanged
  | extern   : Extern ks σs τ → StuckArgs Δ Γ σs → Neu Δ Γ τ          -- CHANGED (hole 1)

/-- Arguments of which at least one is neutral; `here` marks the first neutral one, so the
    witness is canonical. -/
inductive StuckArgs (Δ) : Ctx ks → List (Ty ks) → Type where
  | here  : Neu Δ Γ σ → Args Δ Γ σs → StuckArgs Δ Γ (σ :: σs)
  | there : PExpr Δ Γ σ → StuckArgs Δ Γ σs → StuckArgs Δ Γ (σ :: σs)

inductive PExpr (Δ) : Ctx ks → Ty ks → Type where
  | neu | lit | enum_mk | record_mk | union_mk | array_mk | data_in    -- unchanged
  | list_mk  : Elems Δ Γ t → PExpr Δ Γ (.list t)                        -- NEW (hole 9)
  | lam      : Term Δ (σ :: Γ) τ [] → PExpr Δ Γ (.fn σ τ)               -- MOVED from Comp (hole 4)
  | thunk_mk : Term Δ Γ τ.relax [] → PExpr Δ Γ (.thunk τ)               -- MOVED (hole 6)
  | lazy_mk  : Term Δ Γ τ.relax [] → PExpr Δ Γ (.lazy τ)                -- MOVED (hole 6)

inductive Comp (Δ) : Ctx ks → Ty ks → Type where        -- every computation eliminates a Neu
  | app         : Neu Δ Γ (.fn σ τ) → PExpr Δ Γ σ → Comp Δ Γ τ         -- was PExpr (hole 4)
  | share       : Neu Δ Γ τ → Comp Δ Γ τ                                -- was PExpr (hole 3)
  | nat_rec     : Neu Δ Γ .nat → PExpr Δ Γ τ → Term … → Comp Δ Γ τ      -- was PExpr (hole 5)
  | array_foldl : Neu Δ Γ (.array t) → …                                -- was PExpr (hole 5)
  | data_rec    : … → Neu Δ Γ (.data …) → Comp …                        -- was PExpr (hole 5)
  | data_brec   : … → Neu Δ Γ (.data …) → Comp …                        -- was PExpr (hole 5)
  | thunk_force : Neu Δ Γ (.thunk τ) → Comp Δ Γ τ.relax                 -- was PExpr (hole 6)
  | lazy_force  : Neu Δ Γ (.lazy τ) → Comp Δ Γ τ.relax                  -- was PExpr (hole 6)

inductive Term (Δ) : Ctx ks → Ty ks → JCtx ks → Type where
  | ret | letE | record_casesOn | ite | enum_casesOn | union_casesOn | jump   -- unchanged
  /-- A join point is only introduced together with the branch that needs it (hole 7):
      `join j x := body; <lets>; if c then … else …`.  Lets before the branch are hoisted
      above the `join` by the normaliser, since they cannot mention `j`. -/
  | joinIte   (σ) : Term Δ (σ :: Γ) τ js → Neu Δ Γ .bool →
                    Term Δ Γ τ (σ :: js) → Term Δ Γ τ (σ :: js) → Term Δ Γ τ js
  | joinEnum  (σ) : … → Neu Δ Γ (.enum s) → (Fin _ → Term Δ Γ τ (σ :: js)) → Term Δ Γ τ js
  | joinUnion (σ) : … → Neu Δ Γ (.union cs) → Branches Δ Γ cs τ (σ :: js) → Term Δ Γ τ js
```

### The invariant: every variable is an unknown

With `lam`, `thunk_mk` and `lazy_mk` moved to `PExpr`, every `letE` binds the result of a
computation that eliminates a neutral term, so the new variable is itself stuck. Every other
binder also binds an unknown: a closure parameter, the fields of a case analysis of a neutral
scrutinee, a fold's binders, the parameter of a join point (reached from two branches of a
neutral test). So **`Neu.var` needs no side condition**, and "neutral" really means "its value
depends on something unknown".

### The proofs (as in the toy)

```lean
theorem Neu.not_closed  : Neu Δ [] τ → False         -- var: no variable; others: recurse
theorem StuckArgs.not_closed : StuckArgs Δ [] σs → False
theorem Comp.not_closed : Comp Δ [] τ → False         -- each constructor has a Neu argument
theorem Term.closed_ret (t : Term Δ [] τ []) : ∃ v, t = .ret v
  -- letE: Comp.not_closed; ite/cases/record_casesOn/join*: Neu.not_closed; jump: JVar [] σ is empty
theorem PExpr.closed_eq_quote (h : Ty.FO Δ τ) (v : PExpr Δ [] τ) : v = PExpr.quote τ h (v.eval ())
  -- neu: impossible; lam/thunk_mk/lazy_mk: excluded by FO (or quoted as delays); rest: by parts
```

Each proof is a structural induction of a few lines, with no reasoning about evaluation
except in the last one.

### What it costs

* **Sharing of closures is lost.** Calling a `let`-bound closure is a β-redex, so the
  normaliser must inline every call of a *known* function. There is no fixpoint (every loop is
  a fold), so this always terminates, but code size can grow, exponentially in the worst
  case. Proposal B restores sharing.
* **Loops over literals are unrolled.** `nat_rec (lit 1000) z s` is a redex:
  * if `z` and `s` are closed, the normaliser computes the whole fold at elaboration time
    (§2, the result is one literal);
  * if the body is open, it has to unroll the loop.

  The normaliser needs a bound (an option such as `leanscript.normalize.maxUnroll`) and
  reports an error beyond it ("loop over a literal of size 1000 with an open body; make the
  bound a parameter"). Proposal C2 avoids this.
* **`PExpr` becomes mutual with `Term`** (through `lam`). Today `PExpr` is deliberately an
  ordinary inductive that is not mutual with the other layers. The evaluator stays structural,
  as the toy shows.
* **Substitution becomes hereditary.** `Neu.subst` already returns a `PExpr` and reduces
  ι-redexes through `mkDataOut`/`mkCond`. The extern case must now also go through
  `mkExtern` (evaluate and quote), and `app`/folds through their smart forms, which
  substitute again. The `*_eval_subst` lemmas in `TermSubst.lean` keep their statements, but
  each new smart form needs an `eval_mk*` lemma. `mkExtern` needs `quote` at the extern's
  result type, which is another reason every catalogue result type has to be quotable (§2).
* **Existing tests change.** `ClosedEvalTest.lean`: `addT` and `iteT` become ill-typed, so
  turn them into "does not elaborate" tests, and prove T1 and T2 instead. The shorthand tests
  in `ExternCallTest.lean` would have to go through `mkExtern`.

### Elaborator changes (`LeanScript/TermElab/Anf.lean`)

The normaliser becomes a small partial evaluator. Its CPS structure stays; only the rules for
what may be emitted change.

* `Atom` gets a three-way classification: *value* (an introduction form, closures included),
  *stuck* (a neutral term over an output variable), and *unknown shape*.
* extern: all arguments are values → evaluate and quote (§2); otherwise emit the call with
  the first stuck argument as the `here` of `StuckArgs`.
* `app f a`: `f` a closure value → substitute `a` in its body through the `Scope`
  environment (the normaliser already substitutes atoms for source variables this way);
  `f` stuck → emit `app`.
* folds: scrutinee a value → compute (closed) or unroll (open, bounded); stuck → emit.
* `ite`/`cond`/cases on a value → take the branch (already done for literals by
  `boolSel`/`unionSel`).
* a source `let` of a value → use it in place (today only trivial values are); of a stuck
  term → `share`.
* `join`: emitted only in front of a branch on a stuck scrutinee; a join point jumped to
  from one place only is inlined.
* **Lean terms of unknown shape** (antiquotations in `[Term| …]`, generic `sumT`) can no longer
  be made neutral by `let`-binding them (hole 3). Either reduce them at elaboration time to a
  constructor form (`whnfR`, then read back), or accept them only in positions that take any
  `PExpr`, and report an error in eliminated positions.

---

## Proposal B (structural, keeps sharing): two contexts, *known* and *unknown*

Proposal B is proposal A plus one thing: values may be **named and shared**. Every statement
gets a second context. So a statement has two contexts:

* `Γ`, the **unknowns**: variables whose value is not known when the term is elaborated.
  These are the parameters of closures, the binders of loops and case analyses, the parameters
  of join points, and the results of computations (`letE`).
* `Φ`, the **known values**: variables bound by the new `letV` to an *introduction form*,
  meaning a closure, a delay, or a record/union/array/list/`data_in` literal.

"Known" means *of known shape*, not *known at elaboration time*. A known value may mention
unknowns. In `fun n => val %p := ⟨n, n + 1⟩; …`, `%p` is known to be a pair, but its fields
depend on `n`. What matters is that nothing can be learned by taking `%p` apart or calling it,
because the normaliser can always do that itself.

The rule that makes it work: **a known value is never neutral**. `Neu.var` takes only a
variable of `Γ`. So a `kvar` can be passed around (to an extern, to an unknown function, into
a constructor, as the answer), but it can never be taken apart, called or forced. Every
closed-term argument of proposal A goes through unchanged, because it never looks at `Φ`.

What is checked: `proposals/NormalFormBToy.lean` is proposal B on the toy language of
`NormalFormToy.lean`, with closures as the only known values. Check it with
`lake env lean proposals/NormalFormBToy.lean`; it gives no errors, warnings or `sorry`, and
`#print axioms` lists only `propext` and `Quot.sound`. It proves:

* `Neu.not_closed` and `Comp.not_closed` for `Neu Φ [] τ` and `Comp Φ [] τ`, for **any** `Φ`;
* `Term.closed_chain`: a closed statement is a chain of `letV`s ending in `ret v`;
* `Term.closed_endsWith_quote`: at a first-order type, the `v` at the end of the chain is the
  quotation of the value of the whole statement;
* `Term.closed_endsWith_of_run_eq`: so two closed statements with the same value end in the
  same literal;
* `knownCall_rejected`: calling a known closure is ill-typed.

It also builds `shareTwice`, a closure shared by name and passed twice, and runs it.

`proposals/NormalFormBExamples.lean` translates the examples of §B.5 with today's
`#leanscript_to_term` and prints them. Check it with
`lake env lean proposals/NormalFormBExamples.lean` (the project's `LeanScript.TermElab.ToTerm`
and `LeanScript.TermElab.Notation` must be built). Every "before" output below is copied from
that file's output. The "after" outputs are **derived by hand**, since proposal B is not
implemented.

### B.1 Grammar before (today, `LeanScript/Term/{PExpr,Term}.lean`)

```
Neu   Γ ::= var x                      -- x : Var Γ τ
          | data_out b j Neu | cond Neu PExpr PExpr
          | extern e Args               -- any arguments, even all literals (hole 1)
PExpr Γ ::= neu Neu | lit | enum_mk | record_mk Args | union_mk ix Args | array_mk Elems
          | data_in b j PExpr
Comp  Γ ::= app PExpr PExpr             -- the function may be a let-bound closure (hole 4)
          | lam Term | share PExpr      -- share of any non-trivial pure expression
          | nat_rec PExpr PExpr Term | array_foldl PExpr PExpr Term
          | data_rec b ρ Termᵢ j PExpr | data_brec b ρ k Termᵢ j PExpr
          | thunk_mk Term | thunk_force PExpr | lazy_mk Term | lazy_force PExpr
Term  Γ ::= ret PExpr | letE Comp Term  -- letE extends Γ
          | record_casesOn Neu Term | ite Neu Term Term
          | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
          | join σ Term Term | jump j PExpr
```

One context `Γ`. Every `let` (of a closure, a shared value or a call) puts its variable in
`Γ`, and every variable of `Γ` is neutral. So a `let` hides what it binds (hole 3), and a
`let`-bound closure can be called (hole 4).

### B.2 Grammar after (proposal B)

```
Neu   Φ Γ ::= var x                    -- x : Var Γ τ   (an unknown; never a Var Φ)
            | data_out b j Neu | cond Neu PExpr PExpr
            | extern e StuckArgs        -- at least one neutral argument (as in A)
StuckArgs ::= here Neu Args | there PExpr StuckArgs
PExpr Φ Γ ::= neu Neu
            | kvar k                    -- NEW  k : Var Φ τ, a known value by name
            | lit | enum_mk | record_mk Args | union_mk ix Args
            | array_mk Elems | list_mk Elems | data_in b j PExpr
Val   Φ Γ ::= lam Term                  -- NEW family: the values worth sharing
            | thunk_mk Term | lazy_mk Term
            | record_mk Args | union_mk ix Args | array_mk Elems | list_mk Elems
            | data_in b j PExpr
Comp  Φ Γ ::= app Neu PExpr | share Neu -- Neu, as in A
            | nat_rec Neu PExpr Term | array_foldl Neu PExpr Term
            | data_rec b ρ Termᵢ j Neu | data_brec b ρ k Termᵢ j Neu
            | thunk_force Neu | lazy_force Neu
Term  Φ Γ ::= ret PExpr
            | letV Val Term             -- NEW  extends Φ
            | letE Comp Term            --      extends Γ
            | record_casesOn Neu Term | ite Neu Term Term
            | enum_casesOn Neu Termᵢ | union_casesOn Neu Branches
            | joinIte σ Term Neu Term Term | joinEnum … | joinUnion …   -- as in A
            | jump j PExpr
```

In Lean:

```lean
inductive Neu (Δ) : (Φ Γ : Ctx ks) → Ty ks → Type where
  | var    : Var Γ τ → Neu Δ Φ Γ τ
  | extern : Extern ks σs τ → StuckArgs Δ Φ Γ σs → Neu Δ Φ Γ τ
  | …
inductive PExpr (Δ) : (Φ Γ : Ctx ks) → Ty ks → Type where
  | neu  : Neu Δ Φ Γ τ → PExpr Δ Φ Γ τ
  | kvar : Var Φ τ → PExpr Δ Φ Γ τ
  | …
inductive Val (Δ) : (Φ Γ : Ctx ks) → Ty ks → Type where
  | lam       : Term Δ Φ (σ :: Γ) τ [] → Val Δ Φ Γ (.fn σ τ)     -- the parameter is an unknown
  | thunk_mk  : Term Δ Φ Γ τ.relax [] → Val Δ Φ Γ (.thunk τ)
  | lazy_mk   : Term Δ Φ Γ τ.relax [] → Val Δ Φ Γ (.lazy τ)
  | record_mk : Args Δ Φ Γ (t :: fs.toList) → Val Δ Φ Γ (.record t fs)
  | …
inductive Term (Δ) : (Φ Γ : Ctx ks) → Ty ks → JCtx ks → Type where
  | letV : Val Δ Φ Γ σ → Term Δ (σ :: Φ) Γ τ js → Term Δ Φ Γ τ js
  | letE : Comp Δ Φ Γ σ → Term Δ Φ (σ :: Γ) τ js → Term Δ Φ Γ τ js
  | …
def Term.eval (κ : Env Δ Φ) (ρ : Env Δ Γ) : Term Δ Φ Γ τ js → JEnv … → Ty.Den Δ τ
```

Differences from proposal A:

* `lam`, `thunk_mk` and `lazy_mk` **stay out of `PExpr`**. They are `Val`s and are always
  bound by `letV`. So `PExpr` stays non-mutual with `Term`, as it is today, which is one of the
  costs of A that B avoids.
* `share` takes a `Neu`, as in A, so a literal can no longer be `share`d into `Γ` (today
  `pairTwice` below does that). A literal that is used more than once becomes a `letV`.
* `app`, the folds and the forces take a `Neu`, as in A. Since a `kvar` is not a `Neu`, **every
  call of a known closure and every force of a known delay is still reduced by the
  normaliser**, exactly as in A. What B adds is that a known value that is only *passed on*
  (not called) no longer has to be copied.

Written terms in the examples below use this notation (the printer does not support it yet):
`val %f := V; t` for `letV`, `%f` for `kvar`, `let x := c; t` for `letE`, and `let (a, b) := s; t`
for `record_casesOn`. In a statement, `fun x => t` in answer position abbreviates
`val %f := fun x => t; %f`, the only way B can return a closure. Variables have names for
readability; the real terms are de Bruijn, with separate indices for `Φ` and `Γ`.

### B.3 What the closed-term theorems become

* **T1**: a closed statement (`Γ = []`, any `Φ`) is a chain `val … ; val … ; ret v`. The proof
  is A's proof, because `Neu Δ Φ [] τ` and `Comp Δ Φ [] τ` are still empty. This is checked on
  the toy (`Term.closed_chain`).
* **T2** needs one more decision, because `v` may mention the `val`s. There are two ways:
  1. **Only non-first-order values in `Φ`** (closures and delays; data literals are then
     always inlined). At a first-order type, `v` has no function-typed part, so it contains no
     `kvar`, and it is the quotation of the value. This is checked on the toy
     (`Term.closed_endsWith_quote`). The cost: a data literal used twice is duplicated.
  2. **Data literals in `Φ` too** (the grammar of §B.2). Then `val %p := ⟨1, 2⟩; ⟨%p, %p⟩` is
     a closed first-order statement with `kvar`s in its answer. T2 is stated after inlining:
     `t.inlineKnown = .ret (quote t.run)`, where `inlineKnown` substitutes the `val`s.
* **Dead `val`s** are allowed by the types. `val %f := fun x => x; 3` and `3` are two closed
  statements with the same value. The toy's T2 holds anyway (both end in `3`), but they are
  different terms. To have exactly one closed term per value, the normaliser must never emit
  a dead `val` (§B.4). Enforcing it in the types would need relevant typing of `Φ`, which is
  heavy. A `Prop` side condition (proposal C) is the lighter alternative.

### B.4 Lets with 0, 1 and 2+ uses

**Today** (read from `LeanScript/TermElab/Anf.lean`, and seen in the outputs of §B.5):
the normaliser counts no uses at all. What happens depends only on *what* is bound:

| what a source `let` binds | used 0 times | used 1 time | used 2+ times |
|---|---|---|---|
| a trivial atom: variable, literal, enum constructor, **a closed Lean term of a leaf type** (`10 * 10`, `ack 2 3`) | disappears | inlined | inlined (the Lean expression is copied: `lit ‹2 + 3›` twice in `letsClosed`) |
| a non-trivial pure expression: extern call, record/union/array literal | **kept**: `let _ := share …` (`letsT`) | kept, shared | shared |
| a computation: call, closure, fold, delay, force | **kept**: `let _ := f n` (`letsAppT`) | kept | kept |

So today: **no**, unused lets are not eliminated, unless they bind a trivial atom. **No**,
lets used once are not inlined, unless they bind a trivial atom; a closure that is called
once is still bound and called (`callTwice`, `fibT`). **Yes**, lets used 2+ times are shared,
except trivial atoms, which are copied.

Two related facts:
* Lean's own elaborator removes nothing: the `dead` lets of §B.5 reach the translator.
* A projection `s.f` becomes its own `record_casesOn s`, binding *every* field. In `fibLoop`
  below, the state is taken apart 4 times per iteration: 12 binders, 4 of them used.

**Proposal B.** Some of the answers are forced by the types. The others are a policy of the
normaliser, needed so that closed terms are canonical (§B.3). Uses are counted **on the output
of the normaliser, after reduction**. Inlining a call can add or remove uses, so the count is a
post-pass that runs to a fixpoint (see §B.6).

| what is bound | 0 uses | 1 use | 2+ uses | forced by the types? |
|---|---|---|---|---|
| trivial atom (variable, literal, enum constructor) | gone | inlined | inlined | no (as today) |
| known closure (`val %f := fun …`), **calls** | — | β-inlined | β-inlined at every call | **yes**: `app` needs a `Neu` |
| known closure, uses other than calls (passed on, stored, returned) | `val` dropped | kept as `val` (a closure has no other form in B) | **shared** by `val` | 0: policy; ≥1: yes |
| known delay (`thunk_mk`), **forces** | — | body inlined at the force | body computed once, `let v := body`, before the first force | reducing: **yes**; computing once: policy |
| known delay (`lazy_mk`), **forces** | — | body inlined | body inlined at every force (`lazy` means recomputed) | **yes** |
| known data literal (`val %p := ⟨…⟩`) | dropped | inlined (in a closure, loop or delay body only if closed) | **shared** by `val` | no: policy |
| unknown, `share n` (a neutral pure expression) | dropped | inlined, except into a closure, loop or delay body | shared by `let` | no: policy |
| unknown, other computation (a call of an unknown function, a fold over an unknown, a force of an unknown delay) | dropped | **kept** | shared by `let` | 1: **yes**, an operand must be a pure expression |

So, for proposal B:

* **Used 0 times: eliminated, yes, for every kind of `let`.** This is safe because the
  language is pure and total: there is no fixpoint, every extern is a total function, and a
  computation has no effect other than its value. Dropping one changes only the running time.
  For `val`s it is also *needed* for canonical closed terms (§B.3).
* **Used 1 time: inlined for pure things, no for computations.** This covers `share` of a
  neutral expression, a data literal, and a delay or closure at its only force or call. A
  computation (`app`, a fold, a force of an unknown) cannot be inlined, because operands are
  pure expressions. A closure that is used once but *not called* stays a `val`, since B has no
  inline closure. There is one exception to inlining: never inline into the body of a
  closure, a loop or a delay, because that body runs many times and the work would be repeated.
  (Moving into a branch is fine: it only makes the work lazier.)
* **Used 2+ times: shared, yes.** `share`, computations, data literals, and closures that are
  passed on are all shared. The exceptions: trivial atoms are copied as today, and **calls of
  a known closure are inlined at every call** (the types demand it). That duplicates the
  closure's body; there is no fixpoint, so it terminates, but it can grow code.
  A `thunk` forced twice is computed once, which keeps its memoisation. Doing it eagerly is
  sound (every computation terminates) but costs time if every force sits in a branch that
  is not taken.

### B.5 Examples

For each example: the Lean input, today's output (printed by the project, in its `[Term| …]`
notation: `#i` is the de Bruijn variable `i`, `‹…›` an embedded Lean term), the same read with
names, and the output under proposal B (by hand). All inputs are in
`proposals/NormalFormBExamples.lean`.

#### 1. Lets used 0, 1 and 2 times (extern calls)

```lean
def lets (n : Nat) : Nat :=
  let dead := n * 7      -- used 0 times
  let once := n * 2      -- used 1 time
  let twice := n + 1     -- used 2 times
  once + twice * twice
```

Before (printed):
```
fun _ =>
  let _ := extern ‹.lean_nat_mul› #0 7;
    let _ := extern ‹.lean_nat_mul› #1 2;
      let _ := extern ‹.lean_nat_add› #2 1; extern ‹.lean_nat_add› #1 (extern ‹.lean_nat_mul› #0 #0)
```
Read: `fun n => let dead := share (n * 7); let once := share (n * 2); let twice := share (n + 1); once + twice * twice`.
All three are kept, `dead` included.

After (B):
```
fun n => let twice := share (n + 1); n * 2 + twice * twice
```
`dead` is dropped (0 uses), `once` is inlined (1 use, a `share` of a `Neu`), and `twice` is
shared (2 uses).

#### 2. Lets used 0, 1 and 2 times (computations)

```lean
def letsApp (f : Nat → Nat) (n : Nat) : Nat :=
  let dead := f n
  let once := f (n + 1)
  let twice := f (n + 2)
  once + twice * twice
```

Before:
```
fun _ _ =>
  let _ := #1 #0;
    let _ := #2 (extern ‹.lean_nat_add› #1 1);
      let _ := #3 (extern ‹.lean_nat_add› #2 2); extern ‹.lean_nat_add› #1 (extern ‹.lean_nat_mul› #0 #0)
```
Read: `fun f n => let dead := f n; let once := f (n + 1); let twice := f (n + 2); once + twice * twice`.

After (B):
```
fun f n => let once := f (n + 1); let twice := f (n + 2); once + twice * twice
```
`dead` is dropped: `f` is total and pure, so not calling it changes nothing but time. `once`
stays a `let`, because a call is not a pure expression and cannot be put in an operand.

#### 3. Lets of closed values, and closed arithmetic

```lean
def letsClosed (n : Nat) : Nat :=
  let dead := 3 + 4
  let once := 10 * 10
  let twice := 2 + 3
  n + once + twice * twice

def seven : Nat := 3 + 4
```

Before:
```
fun _ =>
  extern ‹.lean_nat_add› (extern ‹.lean_nat_add› #0 (lit ‹LeanPrimTy.nat› ‹10 * 10›))
    (extern ‹.lean_nat_mul› (lit ‹LeanPrimTy.nat› ‹2 + 3›) (lit ‹LeanPrimTy.nat› ‹2 + 3›))
```
```
lit ‹LeanPrimTy.nat› ‹3 + 4›                        -- seven
```
The translator already turns a closed Lean term of a leaf type into a *literal that holds
the Lean expression* (`LeanScript/TermElab/ToTerm/Expr.lean`, "a closed value of a leaf type
is a literal"). So these lets bind trivial atoms, and `dead` vanishes. But the literal is not
evaluated (`‹2 + 3›` is copied), and `5 * 5` is still an extern call on two literals, which is
hole 1.

After (B, with the evaluator of §2 run on these literals and on extern calls whose arguments
are all values):
```
fun n => n + 100 + 25
```
```
7                                                   -- seven
```

(`PExpr.lit .nat (3 + 4)` and `PExpr.lit .nat 7` are *equal* Lean values, since `3 + 4 = 7`
by `rfl`. So for `seven` the change is only in how the term is printed. The counterexample of
`ClosedEvalTest` is `ret (lean_nat_add 3 4)`, an extern call, which is a different term.)

#### 4. Ackermann

```lean
def ackInner (f : Nat → Nat) : Nat → Nat
  | 0     => f 1
  | n + 1 => f (ackInner f n)

def ack : Nat → Nat → Nat
  | 0     => fun n => n + 1
  | m + 1 => ackInner (ack m)

def ack23 : Nat := ack 2 3
```
(`ack` is written in this higher-order form so that it is structurally recursive, as in
`TermTests/ToTerm/TcoTest.lean`.)

Before:
```
fun _ =>
  let _ := fun _ => extern ‹.lean_nat_add› #0 1;
    nat_rec #1 #0 (let _ := fun _ _ => let _ := #1 1; nat_rec #1 #0 (#4 #0); #0 #1)
```
```
lit ‹LeanPrimTy.nat› ‹ack 2 3›                      -- ack23
```
Read:
```
fun m =>
  let s := fun n => n + 1;
  nat_rec m s (k ih =>                         -- ih : Nat → Nat, the answer for k
    let inner := fun f n =>                    -- the translation of `ackInner`
      let a := f 1;
      nat_rec n a (j acc => f acc);
    inner ih)
```
The helper's closure `inner` is bound in every step and called once.

After (B):
```
fun m =>
  val %s := fun n => n + 1;
  nat_rec m %s (k ih =>
    fun n =>                                   -- = val %r := fun n => …; %r
      let a := ih 1;
      nat_rec n a (j acc => ih acc))
```
```
9                                                   -- ack23
```
* `inner ih` calls a known closure, so it is β-reduced (forced by the types). `inner` then has
  no uses left and is dropped. The result is a closure, so the step answers it through a `val`.
* `%s` is passed to `nat_rec` as its start value, a use that is not a call. A closure has no
  inline form in B, so it stays a `val`. (Proposal A would write the `lam` in place.)
* `let a := ih 1` is a call of an *unknown* function (`ih` is a binder of the loop), so it
  stays.
* `ack23`: the translator already produces a literal, which the evaluator of §2 computes.

#### 5. A recursive function that changes a record every iteration

```lean
structure St where
  a : Nat
  b : Nat
  steps : Nat

def fibLoop : Nat → St → St
  | 0,     s => s
  | n + 1, s => fibLoop n { a := s.b, b := s.a + s.b, steps := s.steps + 1 }

def fib (n : Nat) : Nat := (fibLoop n { a := 0, b := 1, steps := 0 }).a
def fib10 : Nat := fib 10
```

Before (`fibLoop`):
```
fun _ _ =>
  let _ := fun _ => #0;
    let _ :=
      nat_rec #2 #0
        (fun _ =>
            let (_, _, _) := #0;
              let (_, _, _) := #3;
                let (_, _, _) := #6;
                  let (_, _, _) := #9;
                    #13 ‹St.mk.leanScriptCtor›(#10, extern ‹.lean_nat_add› #6 #4, extern ‹.lean_nat_add› #2 1));
      #0 #2
```
Read:
```
fun n s =>
  let id := fun x => x;
  let r := nat_rec n id (k ih =>               -- the fold answers a function St → St
    fun s' =>
      let (a₁, b₁, steps₁) := s';              -- for s'.b
      let (a₂, b₂, steps₂) := s';              -- for s'.a
      let (a₃, b₃, steps₃) := s';              -- for s'.b
      let (a₄, b₄, steps₄) := s';              -- for s'.steps
      ih ⟨b₁, a₂ + b₃, steps₄ + 1⟩);
  r s
```
Each projection takes `s'` apart again. There are 12 binders and 4 of them are used.

Before (`fib`):
```
fun _ =>
  let _ := fun _ _ => …the whole of fibLoop above…;
    let _ := #0 #1; let _ := #0 ‹St.mk.leanScriptCtor›(0, 1, 0); let (_, _, _) := #0; #0
```
Read: `fun n => let F := fun n s => …; let p := F n; let q := p ⟨0, 1, 0⟩; let (a, b, steps) := q; a`.

Before (`fib10`): `lit ‹LeanPrimTy.nat› ‹fib 10›`.

After (B), `fibLoop`:
```
fun n s =>
  val %id := fun x => x;
  let r := nat_rec n %id (k ih =>
    fun s' =>
      let (a, b, steps) := s';
      ih ⟨b, a + b, steps + 1⟩);
  r s
```
After (B), `fib`:
```
fun n =>
  val %id := fun x => x;
  let r := nat_rec n %id (k ih => fun s' => let (a, b, steps) := s'; ih ⟨b, a + b, steps + 1⟩);
  let q := r ⟨0, 1, 0⟩;
  let (a, b, steps) := q;
  a
```
After (B), `fib10`: `55`.

* In `fib`, `F n` calls a known closure, so it is β-reduced. Its result, `fun s => …`, is again
  a known closure, and `p ⟨0, 1, 0⟩` calls it, so that is β-reduced too. `F` and `p` are then
  dead and dropped. The record literal `⟨0, 1, 0⟩` is used once, so it is inlined.
* The single `let (a, b, steps) := s'` is **not** a consequence of B. It is an extra rule of the
  same post-pass: *a neutral record that is already taken apart in scope is not taken apart
  again*. Today's translator gives the same shape when the source uses a pattern: the
  `fibLoopM` variant in the examples file prints `let (_, _, _) := #0; #4 ‹St.mk…›(#1, … #0 #1, … #2 1)`.
  Of the three binders, `a`, `b` and `steps` are all used.
* The fold still answers a function (`St → St`) and builds one closure per step: `nat_rec`
  has one accumulator, and the record changes while `n` counts down. B does not change this.
  Turning such folds into loops that pass the record along is a separate optimisation.

#### 6. A record used twice, and a closed condition

```lean
structure P2 where
  a : Nat
  b : Nat

def pairTwice (n : Nat) : P2 × P2 :=
  let p := { a := n, b := n + 1 }
  (p, p)

def closedCond (n : Nat) : Nat := if 1 < 2 then n else 0
```

Before:
```
fun _ =>
  let _ := ‹P2.mk.leanScriptCtor›(#0, extern ‹.lean_nat_add› #0 1);
    ‹proposals.NormalFormBExamples.Prod.mk.leanScriptCtor›(#0, #0)
```
```
fun _ => let _ := lit ‹LeanPrimTy.bool› ‹decide (1 < 2)›; if #0 then #1 else 0
```
Read: `fun n => let p := share ⟨n, n + 1⟩; ⟨p, p⟩` and
`fun n => let c := share (decide (1 < 2)); if c then n else 0`. The second is hole 3: to be
tested, the literal is bound by a `let` so that it becomes a (neutral) variable.

After (B):
```
fun n => val %p := ⟨n, n + 1⟩; ⟨%p, %p⟩
```
```
fun n => n
```
* `p` is a data literal used twice, so it is shared by a `val` (2+ uses). It cannot be a
  `share` any more, because `share` takes a `Neu`. With only one use, `(p, 0)` would become
  `⟨⟨n, n + 1⟩, 0⟩`. Proposal A (or B with only closures and delays in `Φ`) would copy it:
  `⟨⟨n, n + 1⟩, ⟨n, n + 1⟩⟩`, computing `n + 1` twice.
* `decide (1 < 2)` is evaluated to `true` and the branch is taken.

#### 7. A closure used twice: called, and passed on

```lean
def callTwice (n : Nat) : Nat :=
  let f := fun x => x * n + 1
  f (f n)

def passTwice (g : (Nat → Nat) → Nat) (n : Nat) : Nat :=
  let f := fun x => x + n
  g f + g f
```

Before:
```
fun _ => let _ := fun _ => extern ‹.lean_nat_add› (extern ‹.lean_nat_mul› #0 #1) 1; let _ := #0 #1; #1 #0
```
```
fun _ _ =>
  let _ := fun _ => extern ‹.lean_nat_add› #0 #1; let _ := #2 #0; let _ := #3 #1; extern ‹.lean_nat_add› #1 #0
```
Read: `fun n => let f := fun x => x * n + 1; let a := f n; f a` and
`fun g n => let f := fun x => x + n; let a := g f; let b := g f; a + b`.

After (B):
```
fun n => (n * n + 1) * n + 1
```
```
fun g n => val %f := fun x => x + n; let a := g %f; let b := g %f; a + b
```
* `callTwice`: both uses of `f` are calls, so both are β-reduced (forced). The inner result
  `n * n + 1` is a pure expression used once, so it is inlined. `f` is then dead and dropped.
* `passTwice`: `f` is only passed on, twice, so it is shared by a `val`. **This is the case B
  exists for**: proposal A has to write `g (fun x => x + n)` twice. (`g %f` is computed twice.
  Merging the two identical calls is common-subexpression elimination, a separate
  optimisation.)

#### 8. A memoised delay forced twice

```lean
def thunkTwice (n : Nat) : Nat :=
  let t := Thunk.mk (fun _ => n * n)
  t.get + t.get
```

Before:
```
fun _ =>
  let _ := thunk_mk (let _ := lazy_mk (extern ‹.lean_nat_mul› #0 #0); lazy_force #0);
    let _ := thunk_force #0; let _ := thunk_force #1; extern ‹.lean_nat_add› #1 #0
```
Read: `fun n => let t := thunk_mk (let l := lazy_mk (n * n); lazy_force l); let a := thunk_force t; let b := thunk_force t; a + b`.

After (B):
```
fun n => let v := share (n * n); v + v
```
* `lazy_force l` forces a known delay, so it is reduced (forced by the types): the thunk
  becomes `thunk_mk (n * n)`.
* `t` is forced twice. Inlining its body at both forces would compute `n * n` twice and lose
  the memoisation, so the body is computed once (`let v`), and `v` is shared.

### B.6 Elaborator changes (on top of A's, §A)

* **`Scope`** gets a second list: source variables bound to known values. `Atom` gets a
  `kvar` case (a level in `Φ`), and `bindAtom` binds a non-trivial *introduction form* with
  `letV` rather than `share`.
* **β and forces**: `app f a` with `f` a known closure substitutes `a` into its body (the
  normaliser already substitutes atoms for source variables through `Scope`). A force of a
  known delay continues with its body.
* **Occurrence post-pass.** The normaliser builds an output tree first (today it renders syntax
  directly). A pass then counts the uses of every `letV`/`letE` variable, drops the dead ones,
  inlines the single-use pure ones (not into closure, loop or delay bodies), merges repeated
  `record_casesOn`s of the same neutral record, and repeats until nothing changes. Only then
  is it rendered to `Term` syntax. It terminates because each step removes a binder.
* **Printing and notation**: `val` and `%x` are new, and so is a second index space.

### B.7 Costs

* Every function in `TermSubst.lean`, `Eval.lean` and the notation gets a second context.
  Renaming and substitution are needed on `Φ` (for inlining), and on `Γ` *under* `Φ`: a
  `val` is typed at its binding point, and to inline it deeper, past more `letE`s, it has to be
  weakened over them.
* `Term.eval` takes two environments.
* Calls of known closures are still inlined, as in A. B shares only closures that are passed
  on. If closures that are *called* from several places should also be shared, the rule
  "`app` needs a `Neu`" has to be dropped, and with it the guarantee that closed terms have no
  β-redex. That is proposal C2's territory.
* Canonical closed terms need the "no dead `val`" policy (§B.3), which the types do not enforce.

## Proposal A′ (structural, other encoding): one family, indexed by its shape

Proposal A uses two families, `Neu` and `PExpr`. The same guarantee can be had with one
family, indexed by a `Form`:

```lean
inductive Form | intro | stuck
inductive PExpr (Δ) : Ctx ks → Ty ks → Form → Type where
  | var    : Var Γ τ → PExpr Δ Γ τ .stuck
  | lit    : … → PExpr Δ Γ (.prim p) .intro
  | extern : Extern ks σs τ → Args Δ Γ σs fs → (h : fs.any (· = .stuck)) → PExpr Δ Γ τ .stuck
  | cond   : PExpr Δ Γ .bool .stuck → PExpr Δ Γ τ f → PExpr Δ Γ τ g → PExpr Δ Γ τ .stuck
  …
```

This is fewer types, but the extern needs a side condition on an index list (the `h`
above, which is really a small proof). `StuckArgs` in A gets the same guarantee with no
proof field at all. I list this only for completeness; A's two families are the cleaner
structural encoding, and they are the families the project already has.

---

## Proposal C (`Prop`-based): keep the grammar, carry a proof of normality

Keep today's `Term`, and add an inductive predicate saying the term is normal. It can be
carried in either of two ways:

* **Bundled:** `NTerm Δ Γ τ js := { t : Term Δ Γ τ js // t.NF }`. `#leanscript_to_term`
  produces an `NTerm`.
* **In the constructors**, in the style of `TyWf`'s `:= by ty_wf`:
  `Neu.extern e args (h : args.SomeStuck := by term_nf)`,
  `Comp.nat_rec (n : PExpr …) (h : n.Stuck := by term_nf) …`. Proof irrelevance keeps
  equality of terms unchanged: two terms that differ only in their proofs are equal.

Two strengths are possible.

**C1, full normal form.** `Neu.Stuck`, `Args.SomeStuck` and `Term.NF` state exactly A's
rules as predicates over today's syntax, plus "every `let`-bound variable is bound to a
stuck computation" (which is what makes `var` stuck: an environment `Ctx → Prop` of which
variables are unknown). T1 and T2 then hold for `NTerm` by the same induction as in A,
done on the proof instead of on the syntax. The costs are the same as A's, except that no
constructor moves.

**C2, weak normal form: "every closed subterm is a value".** Require only that no
elimination or extern call is **closed**: each must mention a free variable of `Γ` that
stands for an unknown. This is exactly what T1 and T2 need, because in a closed context
every subterm is closed. It is weaker than full normality in open terms, and that is useful:

* `nat_rec (lit 1000) z s` is allowed when `s` or `z` mentions an unknown, so there is no
  forced unrolling;
* a `let`-bound closure may be *called* on an argument that mentions an unknown, so sharing
  is kept.

`x + (3 + 4)` is still rejected: the inner call is closed and must be folded to `7`. This
is hard to state structurally, because "mentions an outer variable" is a set of free
variables, not a flag. As a predicate over free variables (`Term.fv`) it is easy.

**Producing the proof.** Do not use `decide`: `Term` has function-valued branches, so
`NF` is not decidable by kernel reduction in general. Instead:

* the normaliser knows *why* each node it emits is normal, so it emits the proof term
  alongside the syntax (`NF.extern (SomeStuck.here …)`); or
* use a tactic `term_nf` that applies the `NF` constructors (`repeat constructor` with
  `Var` lemmas), like `ty_wf`.

**Pros:** no grammar change, `TermSubst.lean`/`Eval.lean` untouched, and the proof is only
needed where closed-term reasoning is wanted. **Cons:** a raw `Term` can still be
non-normal; substitution does not preserve `NF` (a `NF`-preserving substitution needs the
same hereditary smart forms as A); and proofs in `NF` can make elaboration slow on big terms.

---

## Proposal D (`Bool`-based): a checker

```lean
def Term.isNF : Term Δ Γ τ js → Bool        -- A's rules (or C2's), as a function
structure NTerm … where
  t : Term Δ Γ τ js
  h : t.isNF = true := by decide            -- or `by rfl`, or `native_decide`
theorem Term.isNF_iff : t.isNF = true ↔ t.NF   -- bridge to C, needed for T1/T2
```

This is the cheapest to write, and the checker is also a useful debugging aid for A to C.
But it is the weakest:

* `decide`/`rfl` must reduce `isNF` on the whole term in the kernel, which is slow for big
  terms. `native_decide` adds the `Lean.ofReduceBool` trust.
* `isNF` has to look through the function-valued branches of `enum_casesOn` and `data_rec`,
  so it must enumerate them with `Fin` (fine, but awkward).
* T1 and T2 still need `isNF_iff`, i.e. C's predicate anyway.

---

## Comparison

| | A: stuck forms | B: known/unknown contexts | A′: `Form` index | C1: `NF` proof | C2: closed subterms are values | D: `Bool` checker |
|---|---|---|---|---|---|---|
| kind | structural | structural | structural (small proof in extern) | `Prop` | `Prop` | `Bool` |
| T1 / T2 | by construction | T1 by construction; T2 by construction if `Φ` holds only closures and delays, else after inlining `Φ` | by construction | from the proof | from the proof | via `isNF_iff` |
| non-normal raw terms | impossible | impossible | impossible | possible | possible | possible |
| sharing of closures | lost (inlined) | kept when passed on; calls still inlined | lost | lost | kept | depends on the rules |
| loops over literals | unrolled / computed | unrolled / computed | unrolled / computed | unrolled / computed | kept if open | depends on the rules |
| grammar change | medium | large (2nd context everywhere) | large | none | none | none |
| `TermSubst` impact | hereditary (`mkExtern`, …) | hereditary + `Φ` | hereditary | new preservation lemmas | new preservation lemmas | none |

## Recommendation

1. Do **§2 first** in any case: `list_mk`, `Ty.FO`, `PExpr.quote`, the elaboration-time
   evaluator and the smart constructor `PExpr.mkExtern`. It is needed by every proposal, and
   on its own it already makes the normaliser fold closed extern calls, so `[Term| 3 + 4]`
   elaborates to `ret 7`.
2. Then take **proposal A**. It is the structural solution with the smallest change to the
   existing families (`StuckArgs`; `Neu` arguments for `app`, `share` and the folds;
   `lam`/`thunk_mk`/`lazy_mk` moved into `PExpr`; `join` fused with its branch). It is the
   one checked on the toy, and it makes T1 and T2 short inductions.
3. If inlining known closures or unrolling open loops over literals turns out to be too
   costly in practice, move to **B** (structural, restores sharing of values) or, if a
   grammar change that large is not wanted, to **C2** (a `Prop`, keeps both sharing and
   loops). Keep **D** only as a debugging checker.
