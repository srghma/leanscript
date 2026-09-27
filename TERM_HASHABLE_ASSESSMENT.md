# What still stops `Term` from being `Hashable`?

This note lists what, apart from floats, stands between the term language
(`Neu`/`PExpr`/`Args`/`Elems` in `LeanScript/Term/PExpr.lean` and `Comp`/`Term`/`Branches` in
`LeanScript/Term/Term.lean`) and `Hashable` instances. It also covers what a *useful* hash
needs as well: a lawful `BEq` and `LawfulHashable`, so that terms can be keys of a
`Std.HashMap`.

The claims below come from trying the deriving handlers in a scratch file (not part of the
project) against the current sources.

## 0. Done in this step: floats

* `LeanPrimTy.float` now denotes `HashableFloat` and `LeanPrimTy.float32` denotes
  `HashableFloat32` (`LeanScript/HashableFloat/`). Each is a float that is neither `NaN` nor
  `-0.0`, with a lawful `BEq`, `Hashable`, `LawfulHashable`, `DecidableEq` and a lawful
  linear `Ord`.
* `LeanPrimTy` itself (the leaf *type codes*) derives `Hashable` and has `LawfulHashable`.

## 1. The type side is easy (nothing blocks it)

These derive `Hashable` without trouble (checked with `deriving instance Hashable for …`):

* `LeanEnumSchema`, `Ref`, `BRef`
* the mutual block `Ty`, `Fields`, `Ctor`, `Ctors`
* `DeBruijn` (so `Var` and `JVar`), `CtorIx`

`DSig` and the `Decl` family only occur as parameters, but deriving for them should be just
as easy. `UnionShape` is a `class inductive` used as an instance argument; it needs a
`Hashable` as well, or it has to be skipped when hashing (it is a subsingleton for each
`bs`).

**Done:** all of these now have `Hashable` (derived; `DeBruijn` by hand, hashing the position,
so that it does not need a `Hashable` of the entries), and `LawfulHashable` follows from their
`LawfulBEq` (core's `instLawfulHashableOfLawfulBEq`).  `TyTests/InstancesTest.lean` checks it.

## 2. Blocker A: extern nodes hold a Lean function

```lean
| Neu.extern  (name : String) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) : Args Δ Γ σs → …
| Comp.extern (name : String) (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) : Args Δ Γ σs → …
```

`deriving Hashable` fails with
`failed to synthesize Hashable (DenList Δ.refDen σs → Ty.Den Δ τ)`.

* A function can be *hashed* by skipping it (hash only `name` and the arguments). That gives
  a `Hashable`, but no `BEq` can be lawful: equality of functions is undecidable, so no
  `DecidableEq`, `LawfulBEq` or `LawfulHashable` is possible for any `BEq` that tells
  different `f`s apart.
* A `BEq` that compares only `name` is not lawful either: two terms with the same name and
  different `f` would be `==` but not `=`.

**Fix options:**
1. Replace `f` by *first-order data* that identifies the operation. The natural candidate
   is an entry of the existing catalogue `LeanInitPureExtern` (or an index into it), with
   the denotation given by an interpreter `LeanInitPureExtern.eval`. Equality of terms is
   then equality of catalogue codes.
2. Keep `f` out of the term: make `Term` generic in an extern alphabet
   `(E : List (Ty ks) → Ty ks → Type)` and supply the semantics
   `E σs τ → DenList … → Ty.Den Δ τ` separately. `Hashable`/`DecidableEq` then follow from
   those of `E`.

The catalogue has problems of its own if used for option 1 (see §5).

## 3. Blocker B: literals of the remaining leaves

```lean
| PExpr.lit (p : LeanPrimTy) (v : p.denote) : PExpr Δ Γ (.prim p)
```

A derived instance needs `Hashable p.denote` for a *variable* `p`, so it needs one instance
`(p : LeanPrimTy) → Hashable p.denote`, which means every leaf needs one. Checked leaf by
leaf:

| leaf | `Hashable` | `DecidableEq` | lawful `BEq` (as found by instance search) |
|---|---|---|---|
| `bool`, `nat`, `int`, `bitvec n`, `uint*`, `int*`, `char`, `string` | ✔ | ✔ | ✔ |
| `stringPos s`, `stringPosRaw` | ✔ | ✔ | ✔ |
| `float`, `float32` (`HashableFloat`, `HashableFloat32`) | ✔ | ✔ | ✔ |
| `stringSlice` (`String.Slice`) | ✔ | ✘ | ✘ (`==` compares contents) |
| `substringRaw` (`Substring.Raw`) | ✘ | ✘ | ✘ (`==` compares contents) |
| `floatModel`, `float32Model` (`Float.Model`, `Float32.Model`) | ✘ | ✔ (structural) | ✘ (`==` is IEEE: `NaN != NaN`, `0 == -0`) |

**Fix options:**
* `floatModel`/`float32Model`: denote hashable variants too (a model that is neither `NaN`
  nor `-0`, as for `HashableFloat`), or drop the two leaves. Another option is to hash
  `toBits` and pick the *structural* `BEq` for the `denote` family (see the note below).
* `substringRaw` and `stringSlice`: equality of the *representation* (string plus two
  positions) is decidable and hashable, but their `BEq` compares contents, so a
  representation hash is not lawful for it. Options:
  * denote the representation as a plain structure (`String × String.Pos.Raw ×
    String.Pos.Raw`), with derived `DecidableEq`/`Hashable`; or
  * hash the contents (`s.toString`) and prove `LawfulHashable` against the contents
    equality; or
  * turn such literals into a `string` literal plus an extern (`String.toSubstring`,
    `String.toSlice`), so that only `string` literals remain.

**Note on instance selection.** `LeanPrimTy.denote` is `@[reducible]`. For a concrete leaf,
instance search sees the underlying type (for example `Float.Model`) and finds *its* `BEq`.
In `PExpr.lit` the leaf `p` is a variable, so a derived `BEq`/`Hashable` for `PExpr` uses the
generic family instance `(p : LeanPrimTy) → BEq p.denote`. That family instance can use
`DecidableEq` (structural equality) for every leaf, and then it is lawful even where the
leaf's own `BEq` is IEEE or contents-based. The price is that `==` on a concrete leaf and
`==` inside a term can disagree. Choosing hashable denotations, as done for the floats,
avoids this.

## 4. Blocker C: function-typed fields with a finite domain

```lean
| Term.enum_casesOn : Neu Δ Γ (.enum s) → (Fin s.nOfConstructors → Term Δ Γ τ js) → Term Δ Γ τ js
| Comp.data_rec  (b) (ρ : Fin (k+1) → Ty ks) (branches : (i : Fin (k+1)) → Term …) (j) : …
| Comp.data_brec (b) (ρ : Fin (k+1) → Ty ks) (k) (branches : (i : Fin (k+1)) → Term …) (j) : …
```

Functions out of `Fin n` are finite tables, so they can be hashed (fold `hash (f i)` over
`i < n`) and compared (`∀ i`, decidable). The deriving handlers cannot do this, and the
recursion through `branches i` is nested, so a hand-written instance needs well-founded or
structural recursion through the function. Two ways out:

* **Hand-written instances**, with `Fin.foldl` for the hash and `Nat.all`/`Fin` for
  equality, defined by mutual structural recursion. This is doable, but the termination
  proof through `branches i` needs care.
* **Change the representation** to first-order lists, e.g. a `Branches`-style inductive
  indexed by `n` (`EnumBranches Δ Γ τ js n` with `nil`/`cons`), and a `Tys (k+1)` vector for
  `ρ`. Deriving then works, as it already does for `Branches` over unions.

## 5. Blocker D (only if the catalogue replaces `f`): `LeanInitPureExtern`

Its own doc comment says it has no `DecidableEq`/`BEq`, because:

* some entries hold **functions** (`lean_string_foldl : (String → Char → String) → …`,
  `lean_string_any`, `lean_string_nextwhile`, `lean_substring_all`,
  `lean_substring_takewhile` hold `Char → Bool`);
* other entries hold values `denote αt` of an arbitrary type of the language, which can be a
  function type;
* entry indices are computed through abstract coercions, so the deriving handlers cannot
  unify them.

The float entries take raw `Float` arguments (`lean_float_add : Float → Float → …`) and
return `float`, which now denotes `HashableFloat`. As a catalogue of **codes**, the entries
should take *no* values, only the code of the operation. The arguments would be `PExpr`s
(already in `Args`) and results would go through `normalize`. The catalogue is not used by
the term language today, so this change breaks nothing.

## 6. Other points to keep in mind

* **Indices and `DecidableEq`.** Many constructors have implicit arguments that the result
  index does not determine: `σ` in `Term.letE`, `σs` in the externs, `t fs` in
  `record_casesOn`, `σ` in `join`/`jump`. `Hashable` is unaffected (it just hashes them).
  A derived `DecidableEq` has to compare these first, using `DecidableEq (Ty ks)`, and
  `cast`, which the handler does for simple cases. Expect to write some of it by hand.
* **`Hashable` ≠ useful as a key.** A hash map needs `BEq` + `LawfulHashable`. So blockers
  A–C also have to be solved for `BEq`/`DecidableEq`, not only for `Hashable`. Hashing while
  skipping `f` and the `Fin` tables compiles, but it is not a sound key.
* **Hash quality.** Derived hashes of the de Bruijn `DeBruijn` indices are cheap. Hashing
  implicit type indices (`Ty ks`) on every node costs time. Consider hashing only the
  explicit structure, which is enough for lawfulness because equal terms have equal indices.

## Suggested order

1. Derive `Hashable` (and `LawfulHashable`) for the type side (§1). This is mechanical.
2. Fix the literal leaves (§3): hashable denotations for the float models and for
   `substringRaw`/`stringSlice`.
3. Replace the `Fin`-indexed functions by first-order lists (§4).
4. Replace the extern function by a code or an extern alphabet (§2, §5).
5. Derive `Hashable`/`DecidableEq` for `Neu`/`PExpr`/`Args`/`Elems`, then
   `Comp`/`Term`/`Branches`, and get `LawfulHashable` from `LawfulBEq`.
