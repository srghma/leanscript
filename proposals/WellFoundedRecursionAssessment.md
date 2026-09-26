# Assessment: the `PCL` grammar (proof-carrying calls), and well-founded recursion for `Term`

This note looks at the `PCL` grammar ("well-founded recursion as a construct of the grammar")
against what `LeanScript.Term` is today (`LeanScript/Expr/Term.lean`, `LeanScript/Eval.lean`,
`LeanScript/ToTerm/`). It answers three questions:

1. Which ideas of `PCL` are worth taking, and which are not.
2. Does well-founded recursion subsume the iteration forms `Term` already has?
3. What well-founded recursion should look like *this iteration*, given the constraint that
   **Lean → `Term` elaboration keeps erasing proofs**. The one exception is
   `Term.externCallChecked`. Propositions may still steer *optimisations* during
   elaboration, but no Lean proof is copied into a term.

Claims marked **[checked]** come with a Lean file that compiles:
`proposals/WellFoundedRecursionToy.lean`. It uses only the core library and is not part of the
Lake build, the same as `ProofCarryingDiteToy.lean`. Check it with
`lean proposals/WellFoundedRecursionToy.lean`. Claims marked **[observed]** come from `#print`
or timing runs in Lean 4.34 and are not stored as artifacts.

---

## 0. Short answer

* **Don't port `PCL` as it stands.** Its main mechanism is to put the decreasing proof, the
  path condition `G`, the pre/postconditions and the `isNF` proofs *into the syntax*. That is
  exactly the proof-porting that elaboration must not do. With proofs erased, `G`, `pre`,
  `post` and `Q` would always be `True`, so they would be dead indices on every family of the
  `mutual` block of `Term.lean` (about 1100 lines). `dec` can't be `True` at all.
* **Take the core idea without the proofs.** A recursive function carries its
  **measure as data**: a term of type `nat`, or a pair of them for a lexicographic order.
  Totality comes from a **fuel derived from the measure**, which the evaluator counts down
  *structurally*. Optionally, each call is **checked when it runs**. Lean itself compiles
  `termination_by <Nat>` this way: `WellFounded.Nat.fix` counts down a fuel of `h x + 1`
  **[observed]**.
* **Represent the recursive function as an ordinary bound variable of function type**
  (`fix f x. body`), not as a special `selfCall` statement. Then a recursive call is just
  `Comp.ap`. That covers calls under a `lam`, calls passed to `List.map`, and nested calls
  like Ackermann's. `PCL`'s first-order `fixSelfCall` can't express these, and Lean's
  well-founded preprocessing produces them all the time (`kids.attach.map (fun ⟨k, _⟩ => k.sum)`).
* **Well-founded recursion does *not* replace the existing folds** (§2). It can express them,
  but at a cost: it needs a measure and a fallback, `k`-deep folds lose their linear
  complexity, and folds are total with no run-time guard. Lean also compiles structural
  recursion to `brecOn`, not to `WellFounded.fix`, so the translator never has to choose
  between the two. **Keep all folds; add `fix`.**

---

## 1. Idea-by-idea assessment of `PCL`

| # | `PCL` idea | Verdict | Why |
|---|---|---|---|
| 1 | `fixSelfCall` carries `dec : ∀ e, G e → R (args e) (cur e)` | **Reject** as is; **replace** by a measure + fuel/check | `dec` can only come from Lean's `decreasing_by` proof, which elaboration may not copy. A measure is *data* (Lean keeps it in the term: `WellFounded.Nat.fix (fun x => x.length) F` **[observed]**), so the elaborator can translate it like any other expression. |
| 2 | Path condition index `G : Env Γ → Prop`, strengthened by each `ite` branch | **Reject** | It exists only to prove `dec`, `hpre` and `post`. Without proofs it would always be `True`. It would still be an extra index on every family (`Term`, `Comp`, all case families, `Dest`, the evaluator, `Build`, `Rename`, the translator). |
| 3 | Pre/postconditions (`Fn.pre`, `Fn.post`, the `Q` index, subtype results `FnVal`) | **Reject** for elaborated terms | Same reason. A verified layer on top could add them later as a *separate* predicate on `Term`, not as indices of the grammar. |
| 4 | Program = ordered **global definitions**, each calling the earlier ones (`Globals`, `gCall`) | **Adopt later** (not this iteration) | Today `Sig` globals are opaque values supplied by `GlobalEnv`, and a callee is inlined into each caller ("split across two top-level definitions: the fold of the callee, inlined"). A module layer of definitions *with bodies* would let a translated recursive function be shared. It is independent of well-founded recursion: `let f := fix …` inside the term is enough for now. |
| 5 | The recursive call as `let v := self args in k` | **Adapt**: the recursive function is a **bound variable of type `σ ⇒ ρ`** | `Term` has closures (`Comp.lam`, `Comp.ap`), which `PCL` doesn't. As a variable, the recursive function works under a `lam`, can be passed to a higher-order function, and allows nested calls. The toy's `sumToT` calls it under a `lam` **[checked]**. |
| 6 | Join points `join` / `jump` with a scope `JScope` (with a `wk` constructor) | **Already have it**, in simpler form | `Term.letJ`, `Term.jump` and `Dest` exist. `PCL` needs `JScope` indexed by `Γ` (hence `wk`) only because its join points carry predicates over the environment. Our `JCtx` is independent of `Γ`, which is simpler. Keep ours. |
| 7 | **Recursive join points** `joinrec` (loops), back edges going down along `R` | **Adopt in iteration 2**, in proof-free form | Worth having: a `letJRec` whose back jumps are counted down by a fuel from a measure on the parameter. It prints as a JavaScript `while (true)` loop with no stack growth (JavaScript has no guaranteed tail calls). It isn't needed for *semantics* in iteration 1, since a tail-recursive `fix` means the same thing and the printer can detect "all recursive calls are in tail position". |
| 8 | Derived `whileLoop` (`join` for the exit + `joinrec` for the loop) | **Defer** | Lean's `while` / `repeat` in `Id` goes through `Loop.forIn`, which is `partial` and so has no image in `Term`. Only hand-written terms would use it. It becomes a two-line derived form once #7 exists. |
| 9 | `PExpr`: call-free compound expressions as operands | **Reject** | `Term` is *strict* A-normal form by type: atoms are variables only, and an operation is a `Comp` bound by `let`. Mixing in a second expression layer would undo that design decision. |
| 10 | `isNF` / `isCond` optimisation proofs in the syntax (`by decide`) | **Reject in the grammar** | They are propositions about syntax, not Lean proofs, so they would be allowed, but they add a proof to every node for little gain. If wanted, write a Boolean checker `Term.isOptimised` and test it with `decide`, keeping the grammar proof-free. |
| 11 | Evaluator runs recursion with `WellFounded.fix` on an arbitrary relation `R` with a proof `wf` | **Reject**; use structural fuel | (a) An arbitrary `R`/`wf` is itself a proof to port. (b) Kernel evaluation: `decide +kernel`, used by 129 test lines, runs Lean's **lexicographic** well-founded recursion **not at all** (`lexLoop`, **[checked]** with `fail_if_success`). The same loop with the two-fuel combinator runs fine (`lexLoopT`, `ackT`: Ackermann `(3, 3) = 61`, **[checked]**). A `Nat` measure through `WellFounded.Nat.fix` does reduce (`countDown 2000`, **[checked]**). |
| 12 | Soundness theorems `fixFn_eq` (unfolding) and `fixFn_unique` (unique solution) | **Adopt**, as theorems about `Term.eval`, not as proofs inside terms | Toy: `checkedFix_eq` (unfolding with **no** hypothesis) and `checkedFix_agree` / `fuelFix_agree` (the fixpoint computes every solution of the recursive equation whose body only calls on smaller arguments), **[checked]**. `log2T_correct` uses them to prove a translated, proof-free term equal to the Lean function **after the fact** **[checked]**. |
| 13 | `PTerm.ofFix`, `callTop`, `Term.ofFix_eval` (a test harness: "the program computes `f`") | **Adopt the shape** for tests | An `eval_fix_agree` lemma of the same shape lets a test state `(#leanscript_to_term f).eval = f` for a well-founded `f`, the counterpart of the current `decide +kernel` value tests. |
| 14 | `tupleTy` / `toEnv`: several parameters packed as one | **Adopt**, as a record | Lean packs parameters into a `PSigma` (`gcdWF._unary : (_ : Nat) ×' Nat → Nat`, **[observed]**). The translator maps that to `Ty.record` and `PSigma.casesOn` to `record_casesOn`. (`PCL`'s `tupleTy [] = .bool` is a stand-in for a missing unit type; `Term` erases unit instead.) |

Further observations on `PCL`'s design:

* It is **first-order**: no `lam`, no closures. Porting its self-call discipline to a language
  with closures needs point 5 anyway.
* Global functions can't be **mutually recursive** (each calls only the ones before it).
  Lean's mutual well-founded definitions are packed into one function on a `PSum` of the
  argument types with a *dependent* motive. That needs a tagged union of arguments, and a
  tuple of answer types as in the existing family folds.
* The `Expr` type has six indices, three of them predicates. A term produced by elaboration
  would carry a predicate lambda at every node. That is costly for the kernel, for
  `#leanscript_to_term` elaboration time, and for the build-time work recorded in
  `proposals/BuildSpeed*.md`.

---

## 2. Does well-founded recursion subsume the existing iteration forms?

Existing iteration in `Term`: `nat_rec k`, `array_rec k`, `recTaggedUnion_rec k`,
`recObject_rec k`, `recAlias_rec k`, `mutualRecursiveFamily_rec k`, and `for i in [:n]` (→
`nat_rec`). Mutual blocks of functions over one type become a fold answering a tuple.

| Aspect | Subsumed? |
|---|---|
| **What can be expressed** | **Almost.** Each fold is a `fix` whose measure is the value itself (`nat`), the array size (the `lean_array_get_size` extern) or the size of a tree. **But** the size of a recursive tagged union, record, newtype or family is a `nat` that must itself be computed, and in `Term` the only way to compute it is a fold (or a new primitive `sizeOf`). So a language with only `fix` would still need either `_rec` at depth 0 or a size primitive per recursive type. |
| **Complexity** | **No.** `nat_rec k` and the other `k`-deep folds keep a **window** of the last `k + 1` answers and are linear (`fib` in O(n)). The direct well-founded `fib n = fib (n-1) + fib (n-2)` is exponential. |
| **Guarantees** | **No.** A fold is total with no guard: the recursive answers are *given* to the branch, and there is no fallback term and no measure. A `fix` without proofs needs a fuel, a fallback, and optionally a run-time check (§3). |
| **Proof ergonomics** | **No.** A fold's evaluation lemmas are definitional unfoldings, and the existing `decide +kernel` tests rely on that. A `fix` has an unfolding lemma (`checkedFix_eq`), but agreement with a Lean function needs the "calls only on smaller arguments" argument (`checkedFix_agree`). |
| **Translator overlap** | **None.** Lean compiles structural recursion through `brecOn` (→ folds, already handled). It uses `WellFounded.fix` / `WellFounded.Nat.fix` only for `termination_by` / `decreasing_by` definitions, which today are *refused* (`LeanScript/ToTerm/Cache.lean`, "well-founded recursion … is not supported"). The two forms serve disjoint inputs. |

**Conclusion:** keep every fold as it is, and add `fix` for the definitions Lean compiles with
well-founded recursion. The JavaScript printer can still print folds as recursive functions if
that makes code generation simpler. That is a printing decision, not a grammar one.

---

## 3. Proposed design for this iteration

### 3.1 Grammar

A recursive function is a **computation step** that yields a function, like `Comp.lam`:

```lean
/-- `fix f x. body`: a function of `x : σ` that may call itself, recursive on the `nat`
    measure `μ` of its parameter.  In `body`, `x` is de Bruijn index 1 and the recursive
    function `f` is index 0 — an ordinary variable of type `σ ⇒ ρ`, so a recursive call is
    `Comp.ap`, also under a `lam`.  No proof: `fallback` is the value of a call that does not go
    down (never reached from a term translated from Lean). -/
| fix : ∀ {Γ σ ρ},
    (μ : Term Sg (σ :: Γ) (.prim .nat)) →
    (fallback : Term Sg (σ :: Γ) ρ) →
    (body : Term Sg ((σ ⇒ ρ) :: σ :: Γ) ρ) →
    Comp Sg Γ (σ ⇒ ρ)
```

* Several parameters: `σ` is a `Ty.record` of them, mirroring Lean's `PSigma` packing.
* Bodies start with `J = []`, like `lam`, `lazy_mk` and fold branches.
* Lexicographic measures (iteration 1b): `fixLex` with `μ₁ μ₂ : Term Sg (σ :: Γ) nat`, using
  the two-fuel scheme of the toy's `lexFix`. More components nest the same way.
* `Ty` and `TyWf` don't change, and no proposition enters the grammar.

### 3.2 Evaluator

`Comp.eval` of `fix` is the toy's `checkedFix` (or `fuelFix`) with `μ`, `fallback` and `body`
evaluated in the extended environment:

```lean
| _, _, .fix μ fb body, env =>
    checkedFix (fun x => Term.evalJ G μ (x, env) PUnit.unit)
      (fun x => Term.evalJ G fb (x, env) PUnit.unit)
      (fun x rec => Term.evalJ G body (rec, x, env) PUnit.unit)
```

The recursion of `Term.evalJ` stays structural: `body`, `μ` and `fb` are subterms, and
`checkedFix.go` recurses structurally on its fuel. There is no `WellFounded.fix`, so kernel
reduction keeps working (**[checked]** on the toy language: `log2T`, `sumToT`, `ackT`, `lexLoopT`
by `decide +kernel`).

The two variants, both **[checked]** in the toy:

| | `checkedFix` (each call compares measures) | `fuelFix` (fuel only, as in Lean's `WellFounded.Nat.fix`) |
|---|---|---|
| unfolding lemma | unconditional (`checkedFix_eq`) | only for bodies that respect the measure |
| agreement with a Lean function | `checkedFix_agree` | `fuelFix_agree` |
| cost per call, in the model | computing `μ` of the argument; for a tree-size measure that is O(size), so O(n²) overall | O(1); `μ` computed once, at the entry |
| a term whose calls don't go down | answers `fallback` at that call | answers `fallback` when the fuel runs out |

**Recommendation:** use `checkedFix` for `Term.eval`, because its unconditional unfolding
lemma becomes a plain `@[simp] Term.eval_fix`. Switch to `fuelFix` only if tree-size measures
make kernel tests too slow. Either way the JavaScript printer can **omit** the check. The
elaborator knows that Lean proved every call decreasing, so a flag or printing option records
"calls proven decreasing at elaboration". That is the "proposition used for an optimisation"
the constraint allows. The denotation stays the checked one.

### 3.3 Elaboration (Lean → `Term`), proofs erased

Patterns Lean 4.34 produces **[observed]** with `#print`:

```
gcdWF._unary := WellFounded.Nat.fix (fun x => PSigma.casesOn x fun a b => b)
                  fun _x a => PSigma.casesOn _x (fun a b a_1 => if h : b = 0 then a else a_1 ⟨b, a % b⟩ ⋯) a
half          := WellFounded.Nat.fix (fun x => x.length) fun xs a => match xs with … | _ :: _ :: t => fun x => x (t.drop 0) ⋯ + 1
bs._unary     := fun hi => WellFounded.Nat.fix (fun x => hi - x) fun lo a => if h : lo < hi then a (lo + 1) ⋯ + 1 else 0
ack._unary    := ack._unary._proof_1.fix fun _x a => …   -- relation: invImage (…) Prod.instWellFoundedRelation
Rose.sum      := Rose.sum._proof_1.fix fun a a_1 => … List.map (fun ⟨k, property⟩ => x k ⋯) kids.attach …
                                                   -- relation: invImage (fun x => x) sizeOfWFRel
qs            := WellFounded.Nat.fix (fun x => x.length) … (List.filter … t.attach).unattach …
```

Steps:

1. **Recognise** `WellFounded.Nat.fix μ F` (a `Nat` measure). Also recognise `WellFounded.fix`
   whose relation, read off the type of `F`'s recursive argument, is `invImage f sizeOfWFRel`
   (measure `sizeOf ∘ f`) or `invImage f Prod.instWellFoundedRelation` on `Nat × Nat`
   (lexicographic, iteration 1b). Refuse anything else with a message, as `Cache.lean` does
   today.
2. **Translate the measure** `μ` as an ordinary expression. It is data, not a proof. `sizeOf`
   goes through its generated `SizeOf` instance, which is a structural recursion and so a
   fold that already translates.
3. **Translate `F`'s body** with the recursive-call binder mapped to variable 0. A call
   `rec y proof` becomes `Comp.ap (var 0) y`, and **the proof is dropped**, as every other
   proof is today.
4. **Unpack parameters**: `PSigma.mk` becomes `record_mk` and `PSigma.casesOn` becomes
   `record_casesOn`. Fixed leading parameters (`fun hi => WellFounded.Nat.fix …`) are
   ordinary variables of the enclosing context.
5. **Erase the well-founded preprocessing wrappers.** `List.attach`, `unattach`,
   `Subtype.mk` / `.val` and patterns `⟨k, h⟩` exist only to carry membership proofs. The
   project doesn't translate `Subtype` yet, so this is new work: treat `{x // p x}` as the
   type of `x`, and `attach` / `unattach` as the identity.
6. **Fallback**: the translation of the `Inhabited` default of the result type, exactly as
   `externCallChecked` gets its fallback (`LeanScript/ToTerm/Extern.lean`). Refuse if there is
   no instance. (`Ty.Wf` guarantees every type has values, `Ty.HabIn`, but there is
   deliberately no `Ty.dflt`, so a term is used.)
7. **Out of scope for iteration 1**: mutual well-founded definitions (`PSum` packing with a
   dependent motive), relations other than `Nat` / `sizeOf` / `Nat × Nat` lexicographic, and
   `partial` / `Loop.forIn` (still unrepresentable).

### 3.4 Theorems to add (about `Term.eval`, never inside terms)

* `Term.eval_fix` / `Comp.eval_fix`: the unfolding (`checkedFix_eq`).
* `Comp.eval_fix_agree`: if a Lean `f` satisfies the recursive equation of the body, and the
  body only calls on smaller measures, the value of `fix` is `f` (`checkedFix_agree`). Tests
  use it to prove translated well-founded functions correct, as `log2T_correct` does in the
  toy.
* For `fixLex`: the same pair of theorems. The toy only *evaluates* `lexFix`; its agreement
  theorem is not yet proved.

### 3.5 Documentation to update when implementing

* `LeanScript/Expr/Design.lean`, recursion table: "well-founded recursive — not supported yet"
  becomes "`Comp.fix`, `nat` (or lexicographic) measure, fuel + run-time check, proof-free".
* `LeanScript/ToTerm/Overview.lean`: a row for `termination_by` definitions, and removal of
  well-founded recursion from the list of refused forms.

---

## 4. Roadmap

| Iteration | Content |
|---|---|
| **1 (now)** | `Comp.fix` with a `nat` measure (§3.1–3.2); translator for `WellFounded.Nat.fix` and `sizeOfWFRel` (§3.3, steps 1–6); `eval_fix` and `eval_fix_agree`; tests `gcd`, `log2`, `qs` (after `attach` erasure), `Rose.sum`. |
| 1b | `fixLex` (two or more fuels) and `Prod.instWellFoundedRelation`; Ackermann test; agreement theorem for the lexicographic combinator. |
| 2 | `letJRec` (recursive join point) for loops that print without stack growth, and `whileLoop` as a derived form for hand-written terms. |
| 3 | A module layer of global definitions with bodies (`PCL`'s `Globals`), so recursive functions are shared rather than inlined; mutual well-founded recursion through a tagged union of arguments. |

Not planned: path conditions, pre/postconditions, decreasing proofs, or `isNF` proofs in the
grammar. They all require carrying proofs into terms, which the constraint rules out.
