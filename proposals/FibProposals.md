# A recursion that descends more than one step: the design, and which node to add

> **Status: implemented.**  The recommendation of this note — one depth-indexed fold,
> with the cut-off in the translation rather than in the grammar — is now the grammar's
> `LeanScript.Term.nat_rec k`, whose depth defaults to `0`.  Its meaning is
> `LeanScript.natFoldK` and its two equations are proved in `LeanScript/NatRecFacts.lean`;
> `#leanscript_to_term` reads the depth off the compiled recursion, and also translates
> `do` in `Id` and a `for` loop over a range.  `TermTests/NatRecDepthTest/` translates
> `fib`, `fibLoopTR`, `fibPair`, `fibLoop` and the tribonacci … hexanacci numbers as they
> are written; `fibFast` is still refused, for the reason §5 of this note gives.  The text
> below is the design as it was argued, and is kept for the record.

```lean
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```

This was the definition `TermTests/ToTermTest/` pinned as **refused**, with

> `#leanscript_to_term`: this recursion reads the value of the function at an argument
> that is not the immediate predecessor, and the grammar's folds descend one step at a
> time

**The decision this note is written around.**  Of the five ways out set out in §6, the
one chosen is *a new constructor for a fold that descends more than one step*, because:

* **no fuel** — a `Nat` counter threaded through the evaluator is out; `Term.eval` is a
  total Lean function and should stay one;
* **no well-foundedness yet** — no measure, no accessibility proof inside a term;
* **no rewriting of the user's algorithm** — the printed JavaScript should look like the
  Lean that was written, so a `fib` written with an `n + 2` pattern should not be
  silently re-expressed as a fold over a record of two numbers.

That last point is the one that decides between the proposals, and it is worth stating
plainly: the sliding-window encoding of §6.1 *works today* and is proved to
(`TermTests/FibWindowTest.lean`), but it changes the shape of the code, and the grammar is
meant to be a faithful description of the code the backend will print.

**The question this revision answers.**  Given that a new node is going in: should it be
`nat_rec2` only, or one node that covers every depth — and if it is a fixed family
(`nat_rec`, `nat_rec2`, `nat_rec3`), is making deeper recursions *unrepresentable* a
feature or an accident?

**The answer, in one line.**  Add **one** depth-indexed node, `nat_recK`, and put the
cut-off in the *translation*, not in the grammar.  It is the same work as the
`nat_rec2`-only proposal today and less work the first time a depth of three is wanted,
the worry that its computed types would need casts is measured and false (§4), and
`nat_rec2` remains available as notation for its `k = 1` instance so nothing is lost in readability or in
printing.  §5 makes the case for the other reading of the question — the fixed family —
and says exactly when it is the better answer.

Everything claimed below about semantics or about types is checked in Lean:

| claim | where |
| :-- | :-- |
| the depth-`k` fold's two equations, at every depth and every argument | `TermTests/NatRecKTest.lean` (`natFoldK_base`, `natFoldK_step`) |
| its window really holds the previous `k` answers (so the fold is linear, not exponential) | `natFoldKAux_eq_winOf` |
| `nat_rec`'s meaning **is** its `k = 0` instance | `natFoldK_eq_natFold` |
| `nat_rec2`'s meaning **is** its `k = 1` instance | `natFoldK_eq_natFold2`, `natFoldK_fib` |
| a depth-three recursion (tribonacci) runs on it | `tribFold_eq` |
| the computed contexts reduce to the readable ones, and the evaluator clause elaborates with no cast | `natRecCtx_two`, `natRecCtx_three`, `win_eq_denList`, `Env.ofWin`, `evalNatRecK` |
| `fib` as a term of the grammar **as it stands** | `TermTests/FibWindowTest.lean` (`fib_term_eval`) |
| which of the five `fib` algorithms are writable today | `TermTests/FibAlgorithmsTest.lean` |

---

## 1. Why `fib` is refused today

Two places decide this, and they agree:

* **The grammar** (`LeanScript/Expr.lean`).  Its only fold over a number is

  ```lean
  | nat_rec : ∀ {Γ τ}, Term Sg Γ (.prim .nat) →
      Term Sg Γ τ → Term Sg (TyWf.prim .nat :: τ :: Γ) τ → Term Sg Γ τ
  ```

  The successor branch binds the predecessor (index `0`) and **the value of the fold at
  that predecessor** (index `1`).  There is no index that holds the value two steps
  down, and that is on purpose: a branch is *given* values, it never makes a call, which
  is exactly why a term is terminating by construction and why `Term.eval`
  (`LeanScript/Eval.lean`) is a total Lean function with no fuel.

* **The translation** (`LeanScript.ToTerm.transBrecOn`).  Lean compiles a structural
  recursion to `Nat.brecOn`, whose branch receives the whole *history* — the value of
  the function at every smaller argument, as a nest of `PProd`s.  `transBrecOn`
  instantiates the branch at a history whose head is a variable standing for the value
  at the predecessor (`substHistoryHead`) and then demands that **nothing else of the
  history is read**.  `fib` reads the second entry as well, so the check fires.

So the restriction is one restriction, in one place: *depth one*.  Nothing about
well-foundedness, positivity or `Ty.Wf` is involved, and nothing here is unsound to
lift — a depth-`k` course-of-values recursion on `Nat` is as terminating as a depth-one
one, and the fold that evaluates it is linear.

---

## 2. The five algorithms, one at a time

The five definitions in the request are five different programs, not five spellings of
one, and the backend should be able to print each of them as written.  Each was checked
against the grammar; `TermTests/FibAlgorithmsTest.lean` contains the terms and the proofs.

| definition | shape | needs | status |
| :-- | :-- | :-- | :-- |
| `fibTR` / `fibLoopTR` | tail recursion with two accumulators | `nat_rec` **at a function type** `nat ⇒ nat ⇒ nat` | **writable today** — `fibTR_term_eval` |
| `fib2` / `fibPair` | one-step recursion returning a pair | `nat_rec` at a record type | **writable today** — `fibPair_term_eval`, `fib2_term_eval` |
| `fibLoop` | `for _ in [:n]` with two mutable variables | the *same* fold as `fibPair`; a `ForIn`/`Std.Range` case in `#leanscript_to_term` | grammar: nothing; translation: one case |
| `fib` | `| n + 2 => fib n + fib (n + 1)` | a depth-two fold | **this note** |
| `fibFast` | recursive call at `n / 2` | a descent that is not by a fixed number of steps | out of reach of every proposal here; see §6.5 |

Two of these deserve a sentence, because they are easy to assume are missing:

* **the tail-recursive loop is already expressible.**  "The branch is given the value at
  the predecessor" sounds like it rules out accumulators, but the value of the fold may
  itself be a *function*: `fibLoopTR` is `nat_rec` at `nat ⇒ nat ⇒ nat`, whose branch
  answers `fun a b => loop b (a + b)`.  Proved at every argument and both accumulators
  (`loop_term_eval`, `fibTR_term_eval`).
* **`fibFast` is not a depth-`k` recursion at all.**  Its call is at `n / 2`, so no
  window of a fixed size holds the value it reads.  It is genuinely well-founded, and no
  proposal short of §6.5 reaches it.  (The one way to write fast doubling without
  well-foundedness is as a fold over the binary digits of `n`, most significant first —
  but *producing* those digits is itself the recursion at `n / 2`, so they would have to
  come from a signature declaration.)

---

## 3. The chosen node, in the smallest form: `nat_rec2`

For reference, and because it is the form to keep as notation, here is the depth-two
node exactly as it would be written.

```lean
/-- `Nat.rec` that descends **two** steps: a branch for `0`, a branch for `1`, and a
    branch for `n + 2` that binds `n` (index `0`), the value at `n + 1` (index `1`) and
    the value at `n` (index `2`). -/
| nat_rec2 : ∀ {Γ τ}, Term Sg Γ (.prim .nat) →
    Term Sg Γ τ → Term Sg Γ τ →
    Term Sg (TyWf.prim .nat :: τ :: τ :: Γ) τ → Term Sg Γ τ
```

It is terminating by construction for the same reason `nat_rec` is: the branch is given
two values and calls nothing.  Its evaluator clause is

```lean
def natFold2Aux {α : Type} (z0 z1 : α) (s : Nat → α → α → α) : Nat → α × α
  | 0 => (z0, z1)
  | n + 1 => let w := natFold2Aux z0 z1 s n; (w.2, s n w.1 w.2)

def natFold2 {α : Type} (z0 z1 : α) (s : Nat → α → α → α) (n : Nat) : α :=
  (natFold2Aux z0 z1 s n).1
```

```lean
| _, _, .nat_rec2 n z0 z1 s, env, h =>
    natFold2 (Term.eval G z0 env h.2.1) (Term.eval G z1 env h.2.2.1)
      (fun k a b => Term.eval G s (k, b, a, env) h.2.2.2)
      (show Nat from Term.eval G n env h.1)
```

`natFold2` carries a window on purpose: it is **linear**, whereas the naive double
recursion is exponential.  The equation the constructor promises,

```lean
natFold2 z0 z1 s (n + 2) = s n (natFold2 z0 z1 s n) (natFold2 z0 z1 s (n + 1))
```

is proved (`TermTests/FibWindowTest.lean`, `natFold2_succ_succ`), as is `natFold2_fib`.

**Its one defect** is the obvious one: it answers `k = 2`, and `| n + 3 => …` is refused
again.  That is an odd line to draw, and drawing it costs a clause in `Term.NoRecMk`, in
`Term.eval`, in `#leanscript_to_term` and in the printer — the same clauses a general
node costs, paid again for every depth someone later wants.  Hence §4.

---

## 4. One node for every depth: `nat_recK` (recommended)

### 4.1 The constructor

```lean
/-- `k` copies of `τ` in front of `Γ`: the block of the context a depth-`k` branch binds.
    (`natRecCtx τ k Γ = List.replicate k τ ++ Γ`; written as a recursion because that is
    the form that reduces when `k` is not a literal.) -/
def natRecCtx (τ : TyWf) : Nat → Ctx → Ctx
  | 0, Γ => Γ
  | k + 1, Γ => τ :: natRecCtx τ k Γ
```

```lean
/-- `Nat.rec` that descends `k + 1` steps.  `base` holds the answers at `k, …, 1, 0` —
    **nearest first**, so it reads `(f k, …, f 0)` — and the branch for `n + k + 1` binds
    `n` (index `0`) and then the answers at `n + k, …, n + 1, n` (indices `1 … k + 1`). -/
| nat_recK : ∀ {Γ τ} (k : Nat), Term Sg Γ (.prim .nat) →
    Spine Sg Γ (natRecCtx τ (k + 1) []) →
    Term Sg (TyWf.prim .nat :: natRecCtx τ (k + 1) Γ) τ →
    Term Sg Γ τ
```

`k = 0` is `nat_rec`, `k = 1` is `nat_rec2`, `k = 2` is a `nat_rec3`, and so on.  The
nearest-first order is what makes those agree: at `k = 0` the single bound value is the
one `nat_rec` binds, and at `k = 1` index `1` is the value at `n + 1` and index `2` the
value at `n`, which is exactly what §3 writes.

### 4.2 Its meaning

The evaluator's clause is the fold below, `natFoldK`, whose state is the window of the
last `k + 1` answers, shifted one place per step:

```lean
def natFoldKAux (z : Win α (k + 1)) (s : Nat → Win α (k + 1) → α) : Nat → Win α (k + 1)
  | 0 => z
  | n + 1 => let w := natFoldKAux z s n; wpush (s n w) w

def natFoldK (z : Win α (k + 1)) (s : Nat → Win α (k + 1) → α) (n : Nat) : α :=
  wget (natFoldKAux z s n) k (by omega)
```

It is `O(n · k)` — one branch call and one window shift per number, never a recomputed
answer.  The two equations a user of the node would reason with are proved in
`TermTests/NatRecKTest.lean`, in full generality (every `k`, every argument):

```lean
theorem natFoldK_base (j : Nat) (hj : j ≤ k) : natFoldK z s j = wget z (k - j) _
theorem natFoldK_step (n : Nat) :
    natFoldK z s (n + k + 1) = s n (winOf (natFoldK z s) (k + 1) n)
```

and the invariant that makes the second one say what it should — that the window the
fold carries **is** the tuple of the previous `k + 1` answers — is
`natFoldKAux_eq_winOf`.  That is the whole correctness argument for the node, and it is
machine-checked rather than asserted.

Both existing meanings are *instances*, not analogues:

```lean
theorem natFoldK_eq_natFold  : natFoldK (k := 0) (z, ⟨⟩) (fun n w => s n w.1) n = natFold z s n
theorem natFoldK_eq_natFold2 : natFoldK (k := 1) (z1, z0, ⟨⟩) (fun n w => s n w.2.1 w.1) n
                                 = natFold2 z0 z1 s n
```

### 4.3 The objection that this revision withdraws

The earlier version of this note (§6.3 below) argued against a depth-indexed node on the
grounds that its *computed* types — a context written `List.replicate k τ ++ Γ`, base
values written as a `Spine` at a computed list — would force casts into the evaluator,
length proofs into the translation, and unreadable de Bruijn indices into every written
term.  That was not measured, and it is wrong.  What was actually checked:

* **the branch's context reduces to the readable one at every literal depth** —
  `natRecCtx τ 2 Γ = τ :: τ :: Γ` and `natRecCtx τ 3 Γ = τ :: τ :: τ :: Γ` hold by `rfl`,
  so a term written at depth two or three has exactly the indices `nat_rec2` would give
  it;
* **depth one is `nat_rec` definitionally** — `Term Sg (nat :: natRecCtx τ 1 Γ) τ` and
  `Term Sg (nat :: τ :: Γ) τ` are the same type by `rfl`, so the general node subsumes
  the existing one with no term rewritten;
* **the base values are an ordinary `Spine`** — `.cons a (.cons b .nil)`, with nothing
  to prove at its type (`baseSpine_two`);
* **the window is the environment of that block of the context** —
  `Win (TyWf.Den τ) 3 = TyWf.DenList (natRecCtx τ 3 [])` by `rfl`, and at a symbolic
  depth the two conversions the evaluator needs, `winOfDenList` and `Env.ofWin`, are
  four-line structural recursions **with no cast and no length proof**;
* **the evaluator clause elaborates as written** — `evalNatRecK` in
  `TermTests/NatRecKTest.lean` *is* that clause, typechecked:

  ```lean
  natFoldK (winOfDenList (Spine.eval G base env hb))
    (fun m w => Term.eval G branch (m, Env.ofWin w env) hs) n
  ```

The honest cost of the generality is therefore: `natRecCtx`, `Win`, `wget`, `wpush`,
`winOfDenList`, `Env.ofWin`, `natFoldKAux`, `natFoldK` — eight small definitions, all
above, none of which any *user* of the language ever sees.

### 4.4 What changes in the code

| file | change |
| :-- | :-- |
| `LeanScript/Expr.lean` | `natRecCtx`; the `nat_recK` constructor; a line in the grammar's prose beside `nat_rec`; optionally the `nat_rec2` abbreviation of §4.5 |
| `LeanScript/Eval.lean` | `Win`, `wget`, `wpush`, `winOfDenList`, `Env.ofWin`, `natFoldKAux`, `natFoldK`; one `Term.NoRecMk` clause (`.nat_recK _ n base branch => Term.NoRecMk n ∧ Spine.NoRecMk base ∧ Term.NoRecMk branch`); one `Term.eval` clause (`evalNatRecK`) |
| `LeanScript/ToTerm.lean` | `transBrecOn` reads the **depth** off the history instead of demanding depth one (§4.6); `transRecCore` gains the case; the refusal message is narrowed (§7) |
| the JavaScript backend | one node: a loop carrying `k + 1` rolling accumulators (§4.7) |
| `TermTests/ToTermTest/`, `TermTests/EvalTest.lean`, `TermTests/TermTest.lean` | `fib` moves from the refusals to the value checks; a depth-three test (tribonacci) alongside it |
| `docs/TermTypeSafety.md`, `LeanScript/Expr.lean`'s header | "the two folds" becomes "the three folds" |

Nothing else.  `Term.NoRecMk` is a plain structural predicate, and the two theorems
`type_of_term_is_wf` / `ctx_of_term_is_wf` hold for any constructor, since they read the
index rather than the term.

Note that this is the *same* table as the `nat_rec2`-only proposal, line for line.  The
difference in cost between the two is the eight definitions of §4.3 against a second
copy of every clause the day a depth-three example arrives.

### 4.5 Keeping `nat_rec` and `nat_rec2` as names

Two variants, and the second is recommended:

* **(a) Replace `nat_rec` by `nat_recK 0`.**  The types are definitionally equal, but
  every existing term, test, evaluator clause and translation site mentions `nat_rec` by
  name, and each would have to be rewritten to pass a `Spine` of one element.  Real
  churn for no gain.
* **(b) Keep `nat_rec` as it is, add `nat_recK` for `k ≥ 1`.**  Nothing existing moves;
  the one-step fold — by far the common case, and the one the printer emits as a plain
  loop — keeps its direct, readable form; the general node is the door that never has to
  be reopened.  `nat_rec2` becomes an abbreviation rather than a constructor:

  ```lean
  @[inline] def Term.nat_rec2 {Sg Γ τ} (n : Term Sg Γ (.prim .nat))
      (z0 z1 : Term Sg Γ τ) (s : Term Sg (TyWf.prim .nat :: τ :: τ :: Γ) τ) :
      Term Sg Γ τ :=
    .nat_recK 1 n (.cons z1 (.cons z0 .nil)) s
  ```

  which typechecks precisely because of the reductions checked in §4.3.  A printer that
  wants a two-accumulator loop matches `nat_recK 1`; one that does not, treats `k + 1`
  accumulators uniformly.

### 4.6 What the translation does

In `transBrecOn`, today's check "the history is read only at its head" becomes "the
history is read only at a **prefix** of length `k + 1`":

1. collect the history projections the compiled branch performs; if any is not
   `hist.1`, `hist.2.1`, …, `hist.2^j.1` for `j ≤ k`, refuse as before (that is a
   genuinely non-uniform descent, `f (n / 2)` and friends);
2. take `k + 1` to be one more than the largest depth read;
3. instantiate the branch at variables for those `k + 1` entries
   (`substHistoryHead` generalised to `substHistoryPrefix`);
4. the base values at `0, …, k` come from instantiating the compiled branch at the
   literals `0, …, k`; refuse if one of them still reads the history;
5. emit `nat_recK k` (or `nat_rec` when `k = 0`).

**Where to put a cut-off, if one is wanted.**  Step 2 is the place: `if k + 1 > maxDepth
then throwError …`.  A cap there is a policy — one line, one option, changeable without
touching the grammar, the evaluator or a single proof — whereas a cap in the grammar is
a design commitment that has to be undone by adding another constructor.  This is the
concrete form of the answer to "is it better to make deeper functions unrepresentable?":
**make them untranslatable, not unrepresentable**, so that the decision can be revisited
cheaply and so that the *language* stays uniform.

### 4.7 How each depth prints

The reason to prefer a node over the window encoding is the printed output, so it is
worth writing down what the printer emits.  For `k + 1` accumulators:

```js
// nat_recK k  ~  fib at k = 1
let a0 = 1, a1 = 0;                 // base, nearest first: f 1, f 0
for (let i = 0; i + 2 <= n; i++) {  // the branch, once per step
  const v = a0 + a1;                // the branch body, reading the window
  a1 = a0; a0 = v;                  // the shift
}
return n === 0 ? a1 : a0;           // below the depth: a base value
```

which is the loop a person would write, and which generalises to `k + 1` variables
without the printer needing a case per depth.  The window encoding of §6.1 would print
the same loop only after a peephole that unpacks the record; the node makes it direct.

---

## 5. The other reading: a fixed family, and deeper recursions unrepresentable

The question was also asked the other way round — perhaps it is *better* to have
`nat_rec`, `nat_rec2`, `nat_rec3` and to make a function that needs more of them
unrepresentable.  That is a real position, and here is the case for and against.

**For.**

* Every constructor of `Term` is then a first-order description of a concrete printed
  form, with no computed index anywhere in the grammar — `Term` stays readable as a
  specification of the backend's node set.
* A pattern like `| n + 7 => …` is almost certainly a mistake or a table lookup in
  disguise; refusing it at the door is a useful editorial policy.
* Nothing in the evaluator has to talk about vectors, windows or replicated contexts:
  each clause is as concrete as `natFold2`.

**Against.**

* The line is arbitrary: nothing distinguishes depth 3 from depth 4 mathematically, so
  the refusal message has to say "not supported" rather than "not sound" or "not
  terminating" — and "not supported" is the message the user is already trying to get
  rid of.
* The cost is paid per depth and it is paid *forever*: a constructor, a `NoRecMk`
  clause, an `eval` clause, a `ToTerm` case, a printer case and a test file, three times
  over, and a fourth time the day depth four appears.
* It does not actually make the *functions* unrepresentable, only their direct spelling:
  the window encoding (§6.1) expresses any depth with the constructors that exist today,
  proved in `TermTests/FibWindowTest.lean`.  So the guarantee "no deep recursions in the
  language" is not one the fixed family provides — it is a guarantee about syntax only.
  If unrepresentability is the goal, the enforcement has to be in the translation
  anyway, which is §4.6.

**When the fixed family wins.**  If the backend's node set is the specification — that
is, if every `Term` constructor must correspond to a hand-written printer case and the
set of printer cases must be closed and small — then a fixed family is the honest model,
and `nat_rec` + `nat_rec2` is enough for every algorithm in the request.  If instead the
printer can emit a loop with `k + 1` rolling variables (it can: §4.7), the depth-indexed
node dominates.

---

## 6. The five original proposals, for the record

These are the five options the first version of this note set out.  §6.2 and §6.3 are
what §3 and §4 above develop; the verdicts stated here are the *original* ones, with the
corrections marked.

### 6.1 Proposal 1 — no new constructor: the sliding window

A recursion that reads its own value at `n` and at `n + 1` is a one-step fold whose value
is the **pair of the last two answers**:

```
w 0       = (fib 0, fib 1) = (0, 1)
w (k + 1) = (b, a + b)   where (a, b) = w k
fib n     = (w n).1
```

`w` descends one step, so it is `Term.nat_rec` at the type `record ⟨nat, nat⟩`, and the
projection is `Term.record_casesOn`.  Nothing new is needed in `Term`, in `Ty`, in
`Term.eval` or in the printer, and `TermTests/FibWindowTest.lean` contains the term and
the proof that it computes `fib` at every argument (`fib_term_eval`).  In general, for a
definition whose branches read `f` at the `k` immediate predecessors, the state is a
record of `k` values, the seed is the `k` base branches, and the step is
`record_casesOn` followed by `record_mk` of the shifted window.

*Original verdict: recommended.*  **Superseded**: it changes the shape of the user's
algorithm, which is the one thing the chosen design is trying to avoid.  It remains the
fallback that needs no code at all, and the proof that the encoding is correct is also
the proof that the new node cannot express anything unsound.

### 6.2 Proposal 2 — one new constructor, `nat_rec2`

Developed in §3.  *Original verdict: add only if the printed output matters.*  The
printed output does matter, so this is the family the chosen design belongs to; §4
argues for its depth-indexed generalisation rather than for the depth-two node alone.

### 6.3 Proposal 3 — one constructor for every depth, `nat_recK`

Developed in §4.  *Original verdict: only worth it if depth-`k` recursions are common,
because the computed types would cost casts and length proofs.*  **Corrected in §4.3**:
they cost neither, and the correction is checked in Lean.

### 6.4 Proposal 4 — course of values: the whole history as an array

```lean
| nat_courseOfValues : ∀ {Γ τ}, Term Sg Γ (.prim .nat) →
    Term Sg (TyWf.prim .nat :: TyWf.array τ :: Γ) τ → Term Sg Γ τ
```

Every structural recursion on `Nat` in one node, at every depth, including ones whose
depth is not fixed.  Against it: `hist[1]` at `n = 1` does not exist, so the read needs a
default — the first node in the language whose meaning depends on one, and the point at
which the translation can no longer check that the recursion is well defined; the history
is `O(n)` memory where a fold is `O(1)`; and the value of a fold becomes observable as
data.  *Verdict unchanged: the most expressive and the least in keeping with the rest of
the design.*

### 6.5 Proposal 5 — a general fixpoint with a measure

```lean
| fixAcc : ∀ {Γ σ τ}, (measure : Term Sg Γ (σ ⇒ .prim .nat)) → … → Term Sg Γ (σ ⇒ τ)
```

A body that may call itself at any argument whose measure is smaller, with the decrease
carried as a proof.  This is what covers `fibFast`, and it is what `LeanScript/Expr.lean`'s
header calls "well-founded recursive — not supported yet".  The proof obligation has to
live in the term, the evaluator needs the accessibility argument to stay total, and the
printer needs a recursion it currently never emits.  *Verdict unchanged, and explicitly
out of scope:* §3 and §4 need none of it, because a depth-`k` descent is still primitive
recursion.

---

## 7. One thing to change either way: the refusal message

Today the message says the grammar's folds descend one step at a time, full stop.  Once
a depth-`k` fold exists it should name what is actually unsupported — a read at an
argument that is **not one of the last `k`**, i.e. a non-uniform descent such as
`f (n / 2)` — and, if §4.6's cap is in force, say what the cap is and that it is a
setting rather than a limitation of the language:

> `#leanscript_to_term`: this recursion reads the value of the function at `n / 2`, which
> is not one of the last `k` arguments; the grammar's folds descend by a fixed number of
> steps, so only a recursion whose reads are at `n - 1, …, n - k` can be translated.
> (Well-founded recursion is not supported yet.)
