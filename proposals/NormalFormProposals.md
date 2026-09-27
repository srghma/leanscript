# Making "a closed `Term` is its own value" true: normal forms by construction

`TermTests/ClosedEvalTest.lean` proves that, with the grammar as it is today, evaluating a
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

This is proposal A, except that values may be named and shared. A statement gets a second
context, `Φ`, of `let`-bound **known values**, next to the context `Γ` of unknowns:

```lean
inductive Term (Δ) : (Φ Γ : Ctx ks) → Ty ks → JCtx ks → Type where
  | letV : Val Δ Φ Γ σ → Term Δ (σ :: Φ) Γ τ js → Term Δ Φ Γ τ js   -- share a value
  | letE : Comp Δ Φ Γ σ → Term Δ Φ (σ :: Γ) τ js → Term Δ Φ Γ τ js  -- bind an unknown
  | …

inductive PExpr (Δ) : (Φ Γ : Ctx ks) → Ty ks → Type where
  | kvar : Var Φ τ → PExpr Δ Φ Γ τ      -- a known value: an operand, never taken apart
  | neu  : Neu Δ Φ Γ τ → PExpr Δ Φ Γ τ  -- Neu.var takes a Var Γ only
  | …
```

* `Neu.var` takes only a variable of `Γ`, so a known value is never neutral. It can be passed
  to an extern, stored in a constructor or returned, but it cannot be taken apart or called:
  `app` still needs a `Neu`, so a call of a known closure is still inlined (β-normal).
* `lam`, `thunk_mk` and `lazy_mk` can stay in `Comp`, bound with `letV` into `Φ`, so `PExpr`
  does not have to become mutual with `Term`. Big literal arrays and records can be shared by
  name too.
* T1 becomes: a closed statement (`Γ = []`, any `Φ`) is a chain of `letV`s ending in
  `ret v`. `Neu.not_closed` holds for `Neu Δ Φ [] τ` by the same proof, since it never looks
  at `Φ`.
* T2 needs a canonical form for the `letV`s. Either
  * state it after inlining: `(t.inlineKnown) = .ret (quote t.run)`, where `inlineKnown`
    substitutes `Φ`; or
  * restrict `letV` to values of non-first-order types (closures, delays, the only things
    worth sharing that cannot be duplicated freely). At a first-order result type no `kvar`
    can then occur in `v` (a first-order type has no function-typed part). A dead `letV` can
    still occur, so add a "used" condition: that is proposal C's territory, or linear/relevant
    typing of `Φ`, which is heavy.
* Cost: every function in `TermSubst.lean`, `Eval.lean` and the notation gets a second
  context. `Ren`/`Subst` on `Φ` are needed when inlining.

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
| T1 / T2 | by construction | T1 by construction; T2 after inlining `Φ` | by construction | from the proof | from the proof | via `isNF_iff` |
| non-normal raw terms | impossible | impossible | impossible | possible | possible | possible |
| sharing of closures | lost (inlined) | kept (can't be called) | lost | lost | kept | depends on the rules |
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
