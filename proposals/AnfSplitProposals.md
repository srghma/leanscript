# A-normal form for `LeanScript.Term`: do we split, and how could we?

This answers two questions: does our term grammar split terms into pure expressions,
computations and statements, the way the `PCL` grammar you quoted does? And would it make
sense to split further? After that come several proposals.

The Lean-level claims about proposal 1 are checked in a small stand-alone toy,
`proposals/AnfSplitToy.lean`. It is outside the Lake build; check it with
`lake env lean proposals/AnfSplitToy.lean`, which currently gives no errors, warnings or
`sorry`. Everything else here comes from reading the sources. It is design discussion, not a
formal result.

**Implementation status.** Proposal 1 is now implemented in `LeanScript.Term` itself
(not as a second IR, proposal 3): `LeanScript/Term.lean` has the three layers `PExpr`
(with `Args`/`Elems`), `Comp` and `Term` (with `Branches`, `PCL`'s `Expr`), with join points
in their own context `js : JCtx`. The existing constructor names are kept, each in its
layer; the new ones are `Comp.share`, `Term.ret`, `Term.join` and `Term.jump`. Of
proposal 4, 4a (`lam` in `Comp`) and 4c (`record_casesOn` as the non-branching destructuring)
are taken, and so are 4d (`PExpr.cond`) and 4h (the cheap externs `PExpr.extern`, chosen by
`LeanScript.Extern.isCheap` on the name of the extern and by the translator's check that its
arguments and result are scalars; every other extern is a named `Comp.extern`). The notation `[Term| …]` and `#leanscript_to_term` are still written in direct
style and A-normalised by `LeanScript/TermElab/Anf.lean`. Sections 0–3 below describe the grammar as it
was *before* this change.

---

## 0. Where we were: we did not split

`LeanScript/Term.lean` is **one syntactic category in direct style**, and its module doc says
so ("The grammar is in direct style"). `LeanScript/TermElab/ToTerm.lean` says the same about the
translator ("The translation is in direct style"). A `Term Δ Γ τ` can appear as an operand of
any other term:

```
app (ite c (nat_rec n z s) (lam b)) (extern "Nat.add" f [data_out b j e, array_foldl …])
```

is a well-typed `Term`. The only other families are the argument lists `Args`, `Branches` and
`Elems`, which exist to encode lists of subterms. They are not layers.

What we have and `PCL` does not:

* first-class functions (`lam`/`app`, `Ty.fn`);
* four folds that carry bodies (`nat_rec`, `array_foldl`, `data_rec`, `data_brec`). They are
  the only loops, and there is no fixpoint;
* case analysis of enums, records and unions;
* delays (`thunk_mk`/`thunk_force`/`lazy_mk`/`lazy_force`).

What `PCL` has and we do not:

* the three layers;
* join points;
* global functions with `self` calls, preconditions, postconditions and path conditions `G`;
* the normal-form proofs `isNF`, `isCond` and `isShareable`.

Two historical notes, from the project's history notes only (the git history here has a
single commit, so I could not re-check them):

* The project once had a strict A-normal `Term`/`Comp` pair with join points in their own
  context, in which atoms could only be variables. The nominal redesign replaced it with the
  current direct-style `Term`.
* The `PCL` docstring you quoted cites "the reference grammar `LeanScript.Term`, whose blocks
  are `letE`s of `Comp`s". That describes the old grammar. For the current tree, that sentence
  is out of date.

## 1. Does splitting make sense for us?

Yes. There are four concrete reasons, and none of them depends on `PCL`'s proof-carrying
features:

1. **Evaluation order and sharing become explicit.** Our language is pure and total, so
   direct style has the same meaning. But a target runtime (JavaScript, or any
   statement-based back end) has to decide what to evaluate once and in which order. In A-NF,
   each non-trivial value is named exactly once.
2. **Code generation is almost syntax-directed.** `PExpr` becomes a target *expression*,
   `Expr` becomes target *statements* (`const x = …; if … { … } else { … }; return …`),
   and a join point becomes a local function or a labelled block. Direct style needs this
   work done in the back end, and every back end would redo it.
3. **Substitution stays inside the grammar.** Substituting a `PExpr` for a variable gives a
   term of the same grammar, because `PExpr` is closed under its own operations. This is a
   reason to prefer a `PExpr` layer over strict "atoms are variables" A-NF (§3, proposal 2):
   there, substituting anything other than a variable breaks the normal form.
4. **Fold bodies are small, closed statements.** A fold body is a statement with no join
   point in scope (`js = []`), so a loop never jumps out to the enclosing continuation. This
   gives each loop a clean compilation unit.

Splitting costs something:

* Terms get larger (every intermediate value gets a `let`). The history notes record that
  the earlier A-NF `Term` needed higher `maxRecDepth` in some tests.
* The translator either has to produce A-NF itself or go through a normaliser.
* Every function on terms (evaluator, renaming, notation, delaborator) gets one function per
  layer.

Proposal 3 keeps most of these costs away from existing code.

## 2. How each current constructor would be classified

| `Term` constructor | layer | remark |
| :-- | :-- | :-- |
| `var`, `lit`, `enum_mk` | `PExpr` | atoms and constants |
| `record_mk`, `union_mk`, `array_mk`, `data_in` | `PExpr` | constructors applied to `PExpr`s (`Args`/`Elems` become `PExprs`) |
| `data_out` | `PExpr` | one layer out, cheap |
| `extern` | `PExpr` **or** `Comp` | see proposal 4h: a cheap primitive (`Nat.add`) is a `PExpr`; an expensive or unknown-cost one is a named call |
| `thunk_mk`, `lazy_mk` | `Comp` (`delay`, body an `Expr`) | a delay suspends a *computation*, like `lam`. It is a `PExpr` wrapper only if its argument is call-free |
| `thunk_force`, `lazy_force` | `Comp` | forcing may run arbitrary code at run time. (`Term.eval` treats all four as the identity, so either choice has the same meaning; the choice matters for code generation) |
| `app` | `Comp` | a call |
| `lam` | `Comp` (`let f := fun x => body`) | a let-bound lambda, like `Code.fun` in Lean's own compiler IR (`Lean.Compiler.LCNF.Code`). Keeping `lam` out of `PExpr` keeps `PExpr` non-mutual (proposal 4a) |
| `nat_rec`, `array_foldl`, `data_rec`, `data_brec` | `Comp` with statement bodies (`js = []`) | exactly like `PCL`'s `map`/`foldl`/`muRec`/`muBRec` |
| `letE` | `Expr.letE c k` | the single binding construct; a `let` of a call-free value is `Comp.share` |
| `ite` | `Expr.ite` (tail) | a non-tail `if` becomes `join j v := rest in if c then …; jump j a else …; jump j b` |
| `enum_casesOn`, `union_casesOn` | `Expr` (tail); `Branches` over `Expr` | as `ite`: non-tail uses need a join point |
| `record_casesOn` | `Expr.unpack` (not tail) or `PExpr` projections | a record has one constructor, so taking it apart does not branch and needs no join point (proposal 4c) |

## 3. Proposals

### Proposal 1 — the three `PCL` layers, adapted to our language (checked in the toy)

```
PExpr  ::= #i | lit | enum_mk | record_mk PExprs | union_mk ix PExprs | array_mk PExprs
         | data_in b j PExpr | data_out b j PExpr | extern_cheap f PExprs
Comp   ::= app PExpr PExpr | lam Expr | share PExpr | delay Expr | force PExpr
         | extern f PExprs
         | nat_rec PExpr PExpr Expr | array_foldl PExpr PExpr Expr
         | data_rec b ρ Exprᵢ j PExpr | data_brec b ρ k Exprᵢ j PExpr
Expr   ::= ret PExpr | letE Comp Expr | unpack PExpr Expr
         | ite PExpr Expr Expr | enum_casesOn PExpr Exprᵢ | union_casesOn PExpr Branches
         | join s Expr Expr | jump j PExpr
```

* `PExpr` (with `PExprs`) is an ordinary inductive, **not mutual** with the other two. Only
  `Comp` and `Expr` (with `Branches`) are mutual. **[checked in the toy]**
* **Join points need no predicates.** We have no path conditions or postconditions, so the
  join-point scope is just the list of the join points' parameter types,
  `Expr Γ t (js : List Ty)`. A join point's value is a closure over its definition
  environment (`JEnv t js`), so it needs neither `PCL`'s `JScope.wk` constructor nor
  weakening of the scope under `letE`. **[checked in the toy]**
* All three evaluators stay **total and structural**, with no fuel: `lam`, the folds and
  `join`/`jump` included. **[checked in the toy]**
* Programs still compute by `rfl`, including a non-tail `if` written with a join point
  (`nonTailIf` in the toy). **[checked in the toy]**
* A pitfall found while writing the toy: Lean promotes the context `Γ` of `PExpr` to an
  inductive *parameter*, because it is the same in every constructor. `PExpr.eval` is then
  structural only if `Γ` is bound before the colon. Otherwise Lean silently falls back to
  well-founded recursion, and every `rfl` test breaks. Write `termination_by structural`
  everywhere, as `Term.eval` already does.
* `joinrec` is **not needed today**, because every loop is a fold. It becomes relevant only
  if well-founded / tail-recursive loops are added (see
  `proposals/WellFoundedRecursionAssessment.md`).

### Proposal 2 — strict A-NF: atoms are variables only

This is the variant the project had before, per the history notes. `PExpr` shrinks to `var`,
and every literal, constructor, `data_out` and extern becomes a `Comp` bound by `let`.

* Pros: each program has exactly one form. There is no normal-form side condition, because
  "no copy `let`" and "ret returns a variable" are enforced by the types.
* Cons: much larger terms, since every constant gets its own `let`. Substituting anything
  other than a variable leaves the grammar (§1, point 3). Simplifications such as
  `data_out (data_in e) ↦ e` need a `let` lookup instead of a local rewrite.
* Recommendation: prefer proposal 1. Use proposal 2 only if the target back end really wants
  one instruction per value (a register machine or bytecode).

### Proposal 3 — keep the direct-style `Term` as the source; add A-NF as a second IR

Keep `Term` exactly as it is: the translator, the notation and every `rfl` test stay
unchanged. Add:

* `LeanScript/Anf/Syntax.lean`, with the grammar of proposal 1;
* `LeanScript/Anf/Eval.lean`, with its evaluator;
* `LeanScript/Anf/Normalize.lean`, with `Term.toAnf : Term Δ Γ τ → Anf.Expr Δ Γ τ []`, in
  the usual continuation style. A continuation is Kripke-style: for every extension of the
  context, it maps a `PExpr` in that context to an `Expr`. A non-tail `ite`/`casesOn`
  reifies the continuation as a `join`;
* `LeanScript/Anf/NormalizeCorrect.lean`, with `Anf.Expr.eval (Term.toAnf e) ρ () = e.eval ρ`,
  proved by a logical relation over renamings.

This is the lowest-risk path. The correctness theorem is the real work, and the history notes
say similar builder-correctness theorems were proved for the old A-NF builders. Code
generation then consumes only `Anf`, and the source grammar stays convenient to write and to
reason about.

### Proposal 4 — splitting *more* than `PCL`: what is worth it

* **4a. `lam` in `Comp`, not in `PExpr`.** A lambda is a *value* in the textbook sense. But
  putting it in `PExpr` makes `PExpr` mutual with `Expr` (its body is a statement), which
  loses the non-mutual, closed-under-substitution `PExpr`. Let-bound lambdas are what Lean's
  own LCNF does (`Code.fun`). Recommended.
* **4b. Split `Comp` into call / loop / closure types?** Not recommended as separate
  inductives. They are all "one step whose value a `let` binds", and `Expr.letE` treats them
  alike. Group them only in the documentation (and possibly in the order of the
  constructors).
* **4c. Non-branching multi-binders as `let`s.** `record_casesOn` does not branch. Make it
  `Expr.unpack (p : PExpr Γ (.record t fs)) (k : Expr (t :: fs.toList ++ Γ) τ js)` so it
  can sit anywhere in a `let` chain without a join point. Alternatively, add a projection
  `PExpr.proj i` and let destructuring be a derived form (a `share` per field). `unpack` is
  closer to the current `record_casesOn` and to the evaluator's `Fields.toDL`. Recommended.
* **4d. A value-level conditional `PExpr.cond c a b`** (as in `PCL`'s
  `if PExpr then PExpr else PExpr`). With it, `if c then x + 1 else 0` in operand position
  needs no join point. The same could be done for an enum/union case whose branches are all
  call-free. Recommended for `ite`; optional for cases.
* **4e. A separate "canonical value" layer** (`Val`: literals and constructors only) below
  `PExpr`. It helps case-of-known-constructor. But it duplicates the constructor list, and a
  Boolean predicate `PExpr.isValue` gives the same benefit. Not recommended as a type.
* **4f. Separate `Block` (a chain of `let`s) and `Tail` types.** Because the context grows
  with each `let`, a chain cannot be a plain `List Comp`. It would have to be a
  telescope-indexed type, which is more complex than `Expr.letE`. Not recommended; keep one
  `Expr`, as `PCL` does.
* **4g. Normal-form invariants as `Bool` proofs**, checked by `decide`, as in `PCL`:
  * `share` never binds an atom (no copy `let`);
  * `ite`'s condition is not a literal;
  * no `data_out (data_in e)`;
  * no `casesOn` of a known constructor.

  These are optional and only worth adding once a simplifier exists that produces them.
  Otherwise they only make programs harder to write by hand.
* **4h. Which externs are pure expressions.** All our externs are pure and total, so
  semantically every extern could be a `PExpr`, and duplicating one only costs time. Two
  options:
  * a flag on the extern, `cheap : Bool` (`PExpr.extern` requires `cheap = true`, and the
    others go through `Comp.call`);
  * all externs in `PExpr`, relying on `share` to avoid recomputation.

  The first makes the cost model visible in the grammar. It would be set from the extern
  catalogue (`LeanScript/LeanInitPureExterns*`).

### Proposal 5 — what each proposal touches

| file | proposal 1 or 2 (replace `Term`) | proposal 3 (second IR) |
| :-- | :-- | :-- |
| `Term.lean`, `Eval.lean` | rewritten into three layers | unchanged; new `Anf/Syntax.lean`, `Anf/Eval.lean` |
| `TermSubst.lean` | renaming per layer; substitution only of `PExpr`s | unchanged; `Anf` needs only renaming (for the normaliser) |
| `TermNotation.lean`, delaborators | new forms (`join`, `jump`, `let … := c`) | unchanged (optionally an `[Anf| …]` notation) |
| `ToTerm/*` | must emit A-NF (naming every call, join points for non-tail `if`/`match`) | unchanged |
| tests (`TermTests/*`) | every term written by hand changes; `rfl` runs still work (toy) | unchanged; new tests `(Term.toAnf e).eval = e.eval` |

## 4. Recommendation

1. Go with **proposal 3**: keep direct style as the source language, and add the three-layer
   A-NF of **proposal 1** as an IR produced by a verified normaliser.
2. Within the A-NF, take:
   * 4a (`lam` in `Comp`);
   * 4c (`unpack` for records);
   * 4d (`PExpr.cond`);
   * 4h (a `cheap` flag on externs).

   Do not add separate types for 4b, 4e or 4f.
3. Leave the normal-form proofs (4g), `joinrec`, and the `PCL`-style path conditions and
   postconditions for later. They are independent of the split. (Path conditions were
   already assessed and rejected in `proposals/WellFoundedRecursionAssessment.md`.)
