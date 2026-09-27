# Assessment: `Thunk` / `Unit → _` in `Ty`, via `LeanPrimTyCovariant`

Question: why does `Ty` have no thunk, what else used to be expressible and no longer is, and
what would break if

```lean
  /-- A Lean `Array`. -/
  | array {ks : List Nat} : Ty ks → Ty ks
```

were replaced by `LeanPrimTyCovariant` (`array` / `thunk` / `lazy`), with a Lean `Unit → τ`
read as `.lazy τ`?

Nothing in the build was changed. The kernel and elaborator claims below are checked in
`proposals/CovTyToy.lean`, a cut-down copy of `Ty` (`prim`, `fn`, `cov`, `record`). It is
outside the Lake build and compiles with no errors, warnings or `sorry`
(`lake env lean proposals/CovTyToy.lean`).

---

## 1. Why `Ty` has no thunk today

It was a deliberate decision in the nominal redesign (`proposals/NominalTyProposal.md`,
"Status of the implementation", steps 1–3):

> there is no `thunk`/`lazy` wrapper (it would denote the value it wraps, so `thunk bool`
> would be a second type of two values).

The same reason is in the reader's error (`LeanScript/Gen/Read.lean`, the ``Thunk`` case of
`classify`), in the module doc of `LeanScript/Signature.lean`, and in a test that checks the
error message (`TermTests/ToTermTest.lean`, `forceB`).

In practice, the decision protects one proved theorem and one design rule.

* **Theorem `Ty.eq_bool_of_two_points`** (`LeanScript/Three.lean`): every closed type whose
  meaning has at most two points *is* `Ty.bool`. With a delay, `Ty.den (thunk bool)` is
  `Thunk Bool` (or `Unit → Bool` for `lazy`), which has exactly two values. So the theorem
  becomes **false**. The toy proves this (`thunk_bool_two_points`, `thunk_bool_ne_bool`).
* **Rule "each finite set of points has exactly one type"** (module doc of
  `LeanScript/Ty.lean`, `UnionShape`, `LeanPrimTy.Nondeg`). With delays, `t`, `thunk t`,
  `lazy t`, `thunk (lazy t)`, … all have isomorphic meanings.

The reason given ("a delay denotes the value it stands for") assumes a delay would *mean* its
contents, i.e. `den (thunk t) = den t`. That meaning cannot be used here anyway. The
translator's correctness checks compare a translated term with the Lean function up to
definitional equality, so `den` has to return the Lean type itself: `Thunk (den t)`, and
`Unit → den t` for `lazy`. With that faithful meaning, `Thunk Bool` and `Bool` really are two
different Lean types that both have two points. The cost is only the theorem and the rule
above. Soundness is not affected, and neither is the "at least two values" guarantee
(`Ty.den_exists_ne` / `Two`): a delay of a type with two values still has two values.

## 2. What was expressible before and is not now

This list is taken from the project's history notes and the older proposals. The old type
stack (`Ty/*`, `TyShape`, `TyWf`, …) was deleted in the nominal redesign, and the repository
history does not contain it, so these items were not re-checked against old code.

| was supported | how | now |
| :-- | :-- | :-- |
| `Thunk τ` as a type | `TyShape` held a `LeanPrimTyCovariant` (`array` / `thunk` / `lazy`) | refused (`Gen/Read.lean`) |
| `lazy τ` (a JS `() => …`) | same former, used by many catalogue entries (`Lean.version.getMajor : lazy nat`, `System.Platform.getTarget : lazy string`, `Thunk.mk : lazy α → thunk α`, …) | no `Ty` for it, so the catalogue in `LeanInitPureExterns/` is not instantiated at `Ty` (it still takes an abstract `MyTy` with `Coe (LeanPrimTyCovariant MyTy) MyTy`) |
| term formers for delays | "lazy/thunk forcing" in the old evaluator (`thunk_mk`, `thunk_force`, …) | none |
| `Thunk T` fields in recursive / `mutual` families | the `TA`/`TB` tests of the old `NestedFamily.lean`; the fold passed `thunk_mk (thunk_force w).1` at such a field | refused: `Fld` (`LeanScript/Decl.lean`) has only `hole` / `old` / `array` / `fn` |
| a `Unit` **argument** | dropped: "Functions become `⇒` (a `Unit`, proof or instance argument is dropped)", so `Unit → τ` was read as `τ` | refused: `Unit` has one value, so it has no type, and `withUnit (_u : Unit) (n : Nat)` is pinned as refused in `TermTests/ToTermTest.lean` |
| a `Unit` **field** | erased | refused ("a `Unit` field is refused, not erased"); `Option Unit` is refused rather than read as `Bool` |
| existentially typed datatypes (`Process`, `Client`/`Server`, `Unfold`) | `Twin`/`Seal`, with one layout per constructor | removed at your request, earlier |

These were never in `Ty`, only commented out or proposed: `task`, `promise` and
`shareCommonState` (commented out in `LeanPrimTyCovariant.lean`), `IO` / impure externs
(`LeanInitImpureExterns.lean_` is disabled), and `list` / `finFn` (only in
`WTypeTyProposal.md`, part A, which was not implemented). `ByteArray` and `FloatArray` are
meant to be `Array UInt8` / `Array Float`.

Adding `thunk`/`lazy` with the `Unit → τ ↦ lazy τ` rule restores the first four rows and the
`Unit`-argument row, and does so faithfully: `Unit → τ` now means `Unit → den τ` instead of
dropping the argument. `Unit` fields stay refused. That is consistent: only `Unit` as the
**domain of an arrow** gets a meaning.

## 3. Three ways to write it

### A. Nested, as you suggest

```lean
  | cov {ks : List Nat} : LeanPrimTyCovariant (Ty ks) → Ty ks
@[match_pattern] abbrev Ty.array (t : Ty ks) : Ty ks := .cov (.array t)
@[match_pattern] abbrev Ty.thunk (t : Ty ks) : Ty ks := .cov (.thunk t)
@[match_pattern] abbrev Ty.lazy  (t : Ty ks) : Ty ks := .cov (.lazy t)
```

Checked in the toy:

* The kernel accepts the nested occurrence inside the `mutual` block.
* `Repr` still derives.
* **`DecidableEq` does not derive.** The handler refuses nested occurrences through
  `LeanPrimTyCovariant`, both in a `mutual` block and alone (checked separately). It has to
  be written by hand as one more function of the `mutual` block (`Ty.covDecEq` in the toy).
  For the real `Ty` / `Fields` / `Ctor` / `Ctors`, whose indices are `Bool` and
  `List Bool`, this is roughly 150 lines. `BEq` / `LawfulBEq` then come from it as they do
  today.
* Structural recursion through the nested occurrence works: `Ty.map`, `Ty.map_id` and
  `Ty.den` all go through. Written with the `.array t` / `.thunk t` / `.lazy t` patterns,
  existing definitions keep their shape and only gain two cases.
* The meaning still computes by `rfl`
  (`Ty.den (.array (.thunk .bool)) = Array (Thunk Bool)`), and `decide` works on `Ty`
  equality.
* Because of the `@[match_pattern]` abbreviations, every existing `.array t`, both as a term
  and as a pattern, compiles unchanged. There are about 110 occurrences in 29 files. The
  existing proofs about `Ty` are term-mode recursion, not `cases`/`induction` with named
  cases, so none of them depends on the constructor name `array`.
* `Coe (LeanPrimTyCovariant (Ty ks)) (Ty ks) := ⟨.cov⟩` is exactly the interface the
  extern catalogue expects.

### B. Tag plus child (not nested)

```lean
  | cov {ks : List Nat} : LeanPrimTyCovariant Unit → Ty ks → Ty ks
```

Checked separately: `DecidableEq` **derives**, and nothing is nested. It keeps
`LeanPrimTyCovariant` as the single list of formers. The catalogue coercion becomes
`fun c => .cov (c.map fun _ => ()) c.val`. The `@[match_pattern]` abbreviations work the same
way. The drawback is cosmetic: `LeanPrimTyCovariant Unit` is only used as a tag.

### C. Three plain constructors

`array`, `thunk`, `lazy` as ordinary constructors of `Ty`. This is the least machinery and
derives everything, but it does not reuse `LeanPrimTyCovariant`, which remains only the
catalogue's interface (`Coe` by `match`).

**Recommendation.** Use B if deriving `DecidableEq` matters more than the literal nested
shape. Otherwise use A, and accept the hand-written equality. Everything else below is the
same for all three.

## 4. What adding it breaks, file by file

Legend: **mech.** means one or two cases are added to an existing `match` or `mutual`
definition; **design** means a decision is needed; **proof** means a theorem changes.

### Core types and meaning

| file | change | kind |
| :-- | :-- | :-- |
| `Ty.lean` | constructor change; `DecidableEq` hand-written (A only); `Ty.map`, `map_id` and `map_map` get `thunk`/`lazy` cases; the module doc's "what cannot be written" list and the "one type per set of points" claim must be restated | mech. + doc |
| `Decl.lean` | `Fld` needs delays too, otherwise `Thunk T` and `Unit → T` fields of recursive types stay refused. **Grounding differs:** `Fld.array` is *guarded* (element `Fld ks n n`, because `#[]` always exists), but a delay has a value only if its contents do, so its child stays at `g`, like `fn`'s codomain. So `Fld` cannot simply take a `LeanPrimTyCovariant (Fld ks n ?)`: either add separate `Fld.thunk`/`Fld.lazy : Fld ks n g → Fld ks n g`, or index the child's grounding by the former (`Fld.cov (c : LeanPrimTyCovariant Unit) : Fld ks n (c.childGround n g) → Fld ks n g`). `Fld.inst` / `Ty.unfold` get the cases | design + mech. |
| `Container.lean` | none: `lazy` is exactly `IPF.fn Unit c`, and `thunk` can reuse it through `Thunk.mk` / `Thunk.get` | – |
| `Den.lean` | `Ty.den`: `thunk t ↦ Thunk (den t)`, `lazy t ↦ Unit → den t`. `Ty.lift` / `Ty.lower`: map through the delay. `Fld.toIPF`, `Fld.roll`, `Fld.unroll`: new cases (`lazy` as `fn Unit`, `thunk` via `Thunk.mk` / `.get`) | mech. |
| `DenFacts.lean` | roundtrip lemmas (`lift_lower`, `lower_lift`, `roll_unroll`, …) get the new cases. The `thunk` cases need the structure eta `⟨fun _ => t.get⟩ = t` plus `funext` on `Unit`, so they are no longer plain `rfl`, but they remain short | proof (easy) |
| `Two.lean` | `Two (Thunk α)` and `Two (Unit → α)` from `Two α`; `Fld.inh`/`Fld.two` cases | mech. |
| `Three.lean` | **The theorem breaks.** `Ty.threeDen` has to take "the type with its outer delays stripped is not `bool`" instead of `t ≠ .bool`, and `Ty.eq_bool_of_two_points` becomes `t.stripDelays = .bool`, where `stripDelays` removes the outer `thunk`/`lazy` wrappers. The `thunk`/`lazy` cases then just reuse the three values of the child. `TyTests/ThreeTest.lean` is updated to match | proof (moderate) |
| `DenBrec.lean` | none found: it does not match on `Ty` / `Fld` shapes directly | – |

### Terms and evaluation

| file | change | kind |
| :-- | :-- | :-- |
| `Term.lean` | new formers, at least `lazy_mk : Term Δ Γ τ → Term Δ Γ (.lazy τ)` (a delay without a binder: `Unit` has no variable) and `lazy_force : Term Δ Γ (.lazy τ) → Term Δ Γ τ`. For `thunk`: either `thunk_mk : … (.lazy τ) → … (.thunk τ)` and `thunk_get`, or externs (`Thunk.mk` / `Thunk.get` / `Thunk.pure` are already catalogue entries). The translator today refuses an extern whose argument or result is not a leaf type, so dedicated formers are simpler | design + mech. |
| `Eval.lean` | `lazy_mk e ↦ fun _ => eval e`, `lazy_force e ↦ eval e ()`, `thunk_mk ↦ Thunk.mk`, `thunk_get ↦ Thunk.get`. Still total and structural | mech. |
| `TermSubst.lean` | renaming and substitution, and the theorems that they commute with `eval`, each get one case per new former | proof (mechanical) |
| `DeBruijn.lean` | none (`Ctx ks := List (Ty ks)`) | – |

### Generator, translator, notation

| file | change | kind |
| :-- | :-- | :-- |
| `Gen/Read.lean` | `Head` gets `thunk`/`lazy`. The ``Thunk`` case returns `.thunk` instead of failing. An arrow whose domain is `Unit` / `PUnit` (up to `whnfR`) becomes `.lazy b`. It must be matched **before** reading the domain, which today refuses `Unit`. The ``Thunk`` rule must stay explicit: `Thunk` is a one-field structure `{ fn : Unit → α }`, so the generic path would erase it to `lazy α` and give the wrong Lean type. `occurrences` gets the cases | design + mech. |
| `Gen/Translate.lean` | `CIR`/`FIR` get `thunk`/`lazy` (`toCIR`, `toFIR`, `hasData`, …), with the grounding rule of `Fld` above | mech. |
| `Gen/Print.lean` | prints `Ty.thunk` / `Ty.lazy` / `Fld.thunk` / `Fld.lazy` | mech. |
| `Signature.lean`, `GetCtor.lean` | doc text ("refuses … a `Thunk`"); generated constructor functions can now have `Thunk`/`Unit →` arguments | doc + mech. |
| `ToTerm.lean`, `ToTerm/*` | translate `fun (_ : Unit) => e` to `lazy_mk`, `f ()` to `lazy_force`, `Thunk.mk` / `Thunk.pure` / `Thunk.get` / `t.get` / the `⟨f⟩` pattern, and a top-level `Unit` parameter to `lazy_mk` around the rest of the body. Any other `Unit`-typed subterm can only be `()` and must be read as such, since there is no `Unit` term. `ToTerm/Basic.lean` (`isLeaf`, `nestShape`) and the fold at a delayed field of a recursive type, which binds the pair of subvalue and answer as it does at a function field, also change | design + mech. (largest part) |
| `TyNotation.lean` | `Thunk τ` and `Unit → τ` in `[Ty| …]`. Delaborators must match both `Ty.array t` (as written) and `Ty.cov (.array t)` (after reduction), and likewise for the delays | mech. |
| `TermNotation.lean` | syntax and printing for the new formers | mech. |
| `LeanInitPureExterns/*` | nothing breaks. Instantiating the catalogue at `Ty` becomes possible (with `Coe (LeanPrimTyCovariant (Ty ks)) (Ty ks)`), but it also needs `list` and `ordering`, which are declared datatypes and not formers | optional |

### Tests whose expectations change

* `TermTests/ToTermTest.lean`: `forceB (t : Thunk Bool) : Bool := t.get` goes from refused
  to translated. `withUnit (_u : Unit) (n : Nat)` goes from refused to translated, as
  `lazy (Nat → Nat)`. The module doc lists both as refusals.
* `TyTests/ThreeTest.lean`: the statement of `eq_bool_of_two_points`.
* Printing tests that go through `Ty.cov`, if values are reduced before being printed.
* New tests to add: a `Thunk`/`lazy` round trip, a `Thunk T` field in a recursive type and
  in a `mutual` block, and `Unit → Unit` (still refused, because the codomain is unit-like).

## 5. Decisions needed

1. **Encoding:** A (nested, `DecidableEq` written by hand), B (tag and child, everything
   derives) or C (three constructors).
2. **Meaning:** `thunk t ↦ Thunk (den t)`, `lazy t ↦ Unit → den t`. This is required for the
   translator's definitional-equality checks. The alternative, `den t`, is what the old
   decision assumed, and it would make `Thunk`/`Unit →` impossible to translate.
3. **Accept the weaker theorem** "at most two points ⇒ `bool` under zero or more delays", and
   the extra spellings `thunk (thunk t)`, `lazy (thunk t)`, …. Refusing nested delays would
   refuse Lean types such as `Thunk (Thunk α)`, which Lean accepts.
4. **Scope of `Unit → τ ↦ lazy τ`:** only a non-dependent arrow whose domain is exactly
   `Unit`/`PUnit`? Or also a dependent `(u : Unit) → β u`, with `()` substituted for `u`?
   `Unit` fields and `Option Unit` stay refused.
5. **Recursive fields:** add `Fld.thunk`/`Fld.lazy`, grounded like `fn`'s codomain, so that
   `node : Thunk T → T` and `node : (Unit → T) → T` are declarable.
6. **Thunk operations:** dedicated term formers, or externs (which requires lifting the
   translator's "externs on leaves only" rule).
