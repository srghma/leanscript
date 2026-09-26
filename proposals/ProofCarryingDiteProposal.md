# Proposal: reuse the proof from `if h : …` instead of checking again

## The problem today

```lean
fun (a : Array Nat) => if h : 1 < a.size then a[1] else 0
```

`#leanscript_to_term` currently produces roughly this:

```
bool_casesOn (lean_nat_dec_lt 1 (lean_array_get_size a))      -- test no. 1
  (externCallChecked [var a, nat_mk 1]
     (fun vs => if h : vs.2.1 < vs.1.size                        -- test no. 2
                then some (.lean_array_fget αt vs.1 vs.2.1 h) else none)
     (nat_mk 0))                                                 -- fallback you can never reach
  (nat_mk 0)
```

* `transDite` (`LeanScript/ToTerm/Trans.lean`) translates the test and then **drops** `h`:
  each branch is translated in a context that has no record of the fact.
* When `a[1]'h` reaches `transExternApp?` (`LeanScript/ToTerm/Extern.lean`), `h` is a local
  hypothesis, so the call is not closed. It becomes `Term.externCallChecked`, which decides
  `1 < a.size` again and needs a fallback term that can never be reached.

The root cause is in the grammar, not the translator. `Term Sg Γ τ` has nowhere to keep a
fact. `Γ : Ctx = List TyWf` holds only values, and `Env Γ = TyWf.DenList Γ` holds only their
denotations. So even a translator that kept `h` would have nothing to translate it to. To fix
this, the grammar needs somewhere to hold a proof, and the translator has to fill it in.

## Goals

1. `if h : P then … else …` gives a node that decides `P` **once**. The branch then
   **holds the proof** (`P` in the then-branch, `¬ P` in the else-branch).
2. An extern that takes a proof built from `h` gets that proof, with no second check and no
   fallback. That covers `h` itself, or any term built from `h` and the tested values, such as
   `Nat.lt_of_not_le h` or the output of `by omega`.
3. No regression. When the translator can't do this (see *Limits*), it produces exactly what
   it produces today (`bool_casesOn` + `externCallChecked`).
4. The evaluator stays total and structural. Soundness comes from type-checking: if `call`
   typechecks, the proof is correct. Nothing new needs proving about the translator.
5. `TyWf` keeps its `DecidableEq`/`BEq` instances. No `Prop`-valued field goes into a type
   of the language.

## Recommended design: a second context of *closed* hypotheses

### Key idea

A hypothesis stores **the values it talks about, captured when the test ran, together with
the proof**, not a proposition about the environment:

```lean
/-- A fact the program established: a proposition about values captured when it was tested. -/
structure Hyp where
  σs   : List TyWf
  prop : TyWf.DenList σs → Prop

abbrev Hyps := List Hyp

/-- The captured values and the proofs, one per hypothesis. -/
def HEnv : Hyps → Type
  | []     => PUnit
  | H :: Δ => {vs : TyWf.DenList H.σs // H.prop vs} × HEnv Δ
```

Because a `Hyp` is closed (it doesn't mention `Γ`), the hypothesis context `Δ` is
**independent of `Γ`**:

* entering a value binder (`lam`, `letE`, a branch of a case split, a fold) changes `Γ` and
  leaves `Δ` alone, so a hypothesis never needs weakening or re-indexing;
* no induction-recursion is involved, since `Hyp` doesn't mention `Env`;
* `Ctx`, `Env`, `Γ ∋ τ` and `TyWf` are unchanged.

A proposition about the environment (`Env Γ → Prop`) would work too, but it has to be
weakened at every binder. A proposition inside `Ctx` entries would need `Ctx` and `Env` to be
defined together, which Lean doesn't support. Closed hypotheses avoid both problems.

### Grammar changes (`LeanScript/Expr/Term.lean`)

Every family of the `mutual` block gets one more index, `Δ : Hyps`. Only `guard` extends it;
every other constructor passes it through unchanged:

```lean
inductive Term (Sg : Sig) : Ctx → Hyps → TyWf → Type 1
  | var  : ∀ {Γ Δ τ}, Γ ∋ τ → Term Sg Γ Δ τ
  | lam  : ∀ {Γ Δ σ τ}, Term Sg (σ :: Γ) Δ τ → Term Sg Γ Δ (σ ⇒ τ)
  …                                   -- every existing constructor: `Δ` passed through

  /-- `if h : p vs then t else e`, with `vs` the values of `args`. `p` is decided once. Each
      branch holds the captured values together with the proof (`p vs` or `¬ p vs`). -/
  | guard : ∀ {Γ Δ σs τ}, Spine Sg Γ Δ σs →
      (p : TyWf.DenList σs → Prop) → (dec : ∀ vs, Decidable (p vs)) →
      Term Sg Γ (⟨σs, p⟩ :: Δ) τ →
      Term Sg Γ (⟨σs, fun vs => ¬ p vs⟩ :: Δ) τ →
      Term Sg Γ Δ τ

  /-- An extern that takes a proof. The proof, and any value it is about, come from the
      hypotheses. The other arguments are the terms `args`, computed when the term runs. -/
  | externHyp : ∀ {Γ Δ ρs τ}, Spine Sg Γ Δ ρs →
      (call : HEnv Δ → TyWf.DenList ρs → Extern τ) → Term Sg Γ Δ τ
```

`call` receives the **whole** `HEnv Δ`, so a proof built from several nested guards, such as
`if h₁ : i < a.size then if h₂ : j < a.size then a.swap i j h₁ h₂`, needs no index type
of its own.

`guard` and `externHyp` don't replace anything. `bool_casesOn`, `externCall`,
`externCallChecked` and `extern` all stay.

To keep existing code and tests compiling, add
`abbrev Term₀ Sg Γ τ := Term Sg Γ [] τ` and `Term.eval₀ … := Term.eval … ()`. Clients that
don't care about hypotheses see the old signatures.

### Evaluator changes (`LeanScript/Eval.lean`)

`Term.eval` gets one more argument, `henv : HEnv Δ`, which every case passes along. The new
cases are:

```lean
  | _, _, .guard args p dec t e, env, henv, h =>
      let vs := Spine.eval G args env henv h.1
      if hp : p vs then Term.eval G t env (⟨vs, hp⟩, henv) h.2.1
      else            Term.eval G e env (⟨vs, hp⟩, henv) h.2.2
  | _, _, .externHyp args call, env, henv, h =>
      Extern.eval (call henv (Spine.eval G args env henv h))
```

The recursion is still structural on the term. No fuel, no `Option`, no fallback.
`NoRecMk` gets the two obvious cases. New `rfl` lemmas: `Term.eval_guard_pos`,
`Term.eval_guard_neg`, `Term.eval_externHyp`.

### What the translator does

**Where it stands (`LeanScript/ToTerm/Ctx.lean`).** `TCtx` gets
`hyps : Array HypInfo`, innermost first, with

```lean
structure HypInfo where
  proof    : FVarId        -- the `h` of `if h : …`
  captured : Array Expr    -- the Lean expressions whose values were captured
  pred     : Expr          -- `p`, as a Lean lambda over `TyWf.DenList σs`
  σs       : Array Expr    -- their types in the language
```

and `TCtx.delta : Expr`, the `Hyps` list as an expression, which is passed as the new `Δ`
argument wherever `c.gamma` is passed today.

**`transDite`.**

1. If neither branch mentions `h` (`(mkApp b h).headBeta` doesn't contain the fvar), emit
   `bool_casesOn` exactly as today. This is cheap and keeps current output for most programs.
2. Otherwise, choose the **captured values**. These are the value fvars occurring in `cnd`
   (the `a` and `i` of `i < a.size`), plus any closed subterm the translator already
   translates as a literal. Build
   `p := fun vs => cnd[captured ↦ projections of vs]` and
   `dec := fun vs => inst[captured ↦ projections of vs]`, where `inst` is the program's own
   `Decidable` instance (`args[2]` of `dite`). Check `p` and `dec` with `Meta.check`. If they
   mention anything outside the allowed set (see *Limits*), go back to step 1's output,
   dropping `h` as today.
3. Translate each branch with `c.pushHyp {proof := h, captured, pred := p (or ¬ p), σs}`.
   Emit `Term.guard (spine of captured) p dec thenT elseT`.

**`transExternApp?`.** Before building `externCallChecked`, when the entry takes a proof
(`checked`) and the proof arguments mention some `h` in `c.hyps`, try `externHyp`:

1. In the entry's arguments (value arguments and proofs), replace every captured
   expression of every hypothesis in scope by `(henv.get k).1.j` and every `h_k` by
   `(henv.get k).2`. This is `kabstract` (or `replaceFVars` when the captured values are
   fvars, the usual case). Remaining value arguments that still mention local variables
   become the spine `ρs`, as `externCall` does today.
2. Wrap the result in `fun henv rest => entry …` and check it with `Meta.check` / `isDefEq`
   against `HEnv Δ → DenList ρs → Extern τ`. **This is the whole soundness argument.** If
   Lean accepts `call`, the proof really does prove the entry's proposition about the values
   the entry is given. If Lean rejects it, fall back to `externCallChecked`.
3. Emit `Term.externHyp spine call`.

For the example at the top, the translator would produce

```
guard [nat_mk 1, var a] (fun vs => vs.1 < vs.2.1.size) (fun _ => inferInstance)
  (externHyp [] (fun henv _ => .lean_array_fget αt henv.1.1.2.1 henv.1.1.1 henv.1.2))
  (nat_mk 0)
```

This has one test, no fallback, and uses the program's own proof. `proposals/ProofCarryingDiteToy.lean`
is a stand-alone model of this. It checks with plain `lean`, since the project build
currently fails because `mathlib` is required in `lakefile.toml` but missing from
`lake-manifest.json`. The toy evaluates this term and a variant whose else-branch hands
`Nat.lt_of_not_le h` to the extern.

### Why values are captured, not re-read

In the branch, `a` is still an ordinary variable, and reading it gives the same value that
was captured, since the language is pure. `call` must nevertheless take `a` **from the
hypothesis**. That is the only way the type of the proof it hands over (`vs.1 < vs.2.1.size`)
can be about the same array the entry receives. Re-reading `var a` would give a value that
is equal but not known to be equal to the captured one, and the entry's type would not check.

### Consequences for a code generator

A code generator should treat `HEnv` as erased: a `guard` becomes `if (dec(vs))`, and each
`(henv.get k).1.j` in an `externHyp` is read back as the captured expression. To make that
trivial, the translator should keep captured values **variables** (A-normal form). When
`cnd` tests a compound expression (`if h : f x < a.size`), it `letE`-binds it first. Then
captured values are just aliases of variables in scope. They hold no extra reference, so
in-place updates such as `Array.set` on a uniquely-owned array are not blocked.

## Limits (what still goes through `externCallChecked`)

* **`p` has to be computable in the language.** `p` and `dec` are Lean closures, like the
  `call` of `externCall`/`externCallChecked` today. They may mention only the captured values,
  literals, and functions the catalogue models (`Array.size`, `<`, `∣`, `String.utf8ByteSize`,
  …). A test through a user function declared in the signature (`if h : myPred x`) is left
  as it is today: `bool_casesOn` on the translated test, with `h` dropped.
* **The proof may mention only hypotheses and captured values.** A proof that also depends on
  a local value that wasn't captured (e.g. `by omega` using a `let` that isn't in `cnd`) fails
  the check in step 2 and falls back. Captured values could later be widened to all value
  fvars of the proof, but that needs a guard that captures more than its test reads.
* **Proofs that don't come from a `dite`** are unchanged: `match h : e with`,
  `Array.get?`-then-`get`, and hypotheses that are arguments of the translated definition
  (`def getAt (a) (i) (h : i < a.size) := a[i]`). `match h : …` could reuse the same machinery
  later, since it is the same "decide once, keep the proof" pattern.
* `USize` entries stay excluded, as today.

## Alternatives considered

| Design | What changes | Why not (for now) |
|---|---|---|
| **A. Closed hypothesis context `Δ`** (above) | new index on every family of `Term`, two new constructors | Mechanical but wide refactor. Recommended because it is general (any decidable `P`, any derived proof, nested guards) and leaves `Ctx`/`TyWf` alone |
| **B. Facts in `Ctx`**: `Ctx := List CtxEntry`, `CtxEntry := val τ \| hyp σs p` | `Γ ∋ τ`, `Env`, every `σ :: Γ` | Touches as much as A, plus every variable lookup. `Ctx` loses `DecidableEq` |
| **C. Precondition index `Φ : Env Γ → Prop`** | index on every family | Needs weakening at every binder (`fun e => Φ e.2`), and a test is a proposition about the environment, not about values, which makes `call` harder to build |
| **D. A refinement *type*** `TyWf.refine (c : PreCode)` with a first-order code for the finitely many preconditions of the catalogue (`i < a.size`, `n < UInt8.size`, `y ∣ x`, …), `Den = {vs // c.holds vs}` | `Ty`/`TyWf` (+ `Den`, `Wf`, the deriving handlers, `tyView`); `Term` only gets `guard`/`externHyp` | Keeps `Term`'s indices, but only handles tests that match a catalogue precondition exactly: no `¬ P`, no derived proofs. It also puts a proof-carrying type in the user-visible types |
| **E. Keep the second check, remove it after translation**: a verified pass or code-generator rule that drops `externCallChecked` under a matching `bool_casesOn` | an optimisation pass + its correctness proof | Doesn't carry the proof. Matching the `Bool` test term against the Lean decision closure is heuristic, and the proof of the pass has to reason about opaque `call` functions |

## Staged plan

1. **`LeanScript/Expr/Hyp.lean`** (new): `Hyp`, `Hyps`, `HEnv`, `HEnv.get`, plus notation.
2. **Thread `Δ`**, a mechanical change with no new behaviour. Add `{Δ}` to every family in
   the `mutual` block of `Term.lean` (`Term`, `Terms`, `Spine`, the `…Cases` / `…FoldCases`
   families), to `Term.eval`/`Spine.eval`/…, to `NoRecMk` and to the `…Facts` files. Add
   `Term₀`/`eval₀` so tests keep their statements. Then build, and check that nothing but
   signatures changed.
3. **Add `guard` and `externHyp`**, their eval and `NoRecMk` cases, and the `rfl` lemmas.
4. **Translator.** Add `TCtx.hyps`/`TCtx.delta`, pass `Δ` wherever `c.gamma` is passed, the
   new `transDite` path, and `externHyp?` ahead of `externCallChecked` in
   `transExternApp?`. Update the headers of `ToTerm/Overview.lean`, `ToTerm/Extern.lean` and
   `Eval/Extern.lean`.
5. **Tests** (`TermTests/ExternToTermTest.lean`):
   * the example above gives `guard` + `externHyp`, and `Term.eval` agrees with the Lean
     function on in-bounds and out-of-bounds arrays;
   * else-branch with a derived proof (`if h : a.size ≤ i then 0 else a[i]`);
   * nested guards (`Array.swap` with `h₁ h₂`);
   * `Array.set` under a guard;
   * the fallback cases (a test through a signature function; a proof that uses an
     uncaptured local) still give `externCallChecked`;
   * a `dite` whose branches don't use `h` still gives `bool_casesOn`.
6. **Optional:** a lemma relating the two translations. Under `guard args p dec t e`, if an
   `externCallChecked` node's decision agrees with `p`, its value equals that of the
   `externHyp` node. This would justify rewriting old terms, but the design doesn't need it.

## Risks and costs

* **Size of step 2.** Every family of the `mutual` block and every theorem about `Term.eval`
  changes signature. It is mechanical, but it touches the most files. `Term₀` keeps test
  files mostly unchanged.
* **Kernel checking of `call`.** `call` contains the program's proof term, which can be large
  (`omega` proofs), so the kernel check of a translated term can get slower. This is the same
  cost `Term.extern` already pays for closed calls.
* **The existing "tag too big" limit** on compiled definitions that build high-numbered
  catalogue entries is unaffected, and applies to `externHyp` in the same way.
