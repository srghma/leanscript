# `JsTerm` review: assessment and plan

This file answers the seven review points on `JsTerm/Ty.lean`, `JsTerm/Syntax.lean`,
`JsTerm/OpsImported.lean` and `JsTerm/OpsInlined.lean`. For each point it gives:

- **Assessment:** is the concern right, and what does the code do today?
- **Proposal:** a Lean sketch.
- **Impact:** which files change, how big the change is, and the risks.

A phased plan comes at the end.

## Status (implemented)

The plan below was reviewed and implemented as follows:

| § | Decision | State |
| --- | --- | --- |
| 1 | `typedArray (elem : JsTypedElem)`, the kind computed from the element | done (`JsTerm/Ty.lean`) |
| 2 | the **fully structural** alternative: `record (f₁ f₂ : JsTy) (fs : List JsTy)`, `union (c₀ c₁ : List JsTy) (cs : List (List JsTy))`; the `{}` case is gone | done |
| 3 | put aside; replaced by a proposal for fast recursive datatypes | `proposals/RecursiveDatatypesProposal.md` |
| 4 | uncurried functions: `fn (doms : List JsTy) cod`, n-ary `lam`/`app`, `lazy t` is `fn [] t`, maximal uncurrying by type, partial application as a closure, exported functions take every parameter of their type | done (`JsTerm/FromTerm.lean`) |
| 5 | `JsTerm/NumberLit.lean`, from `Float.Model.UnpackedFloat` | done |
| 6 | every extern implemented (`runtime.js`), `lean_extern_unimplemented` deleted; a missing operation is a conversion error and the generator refuses to run | done |
| 7 | one `JsTerm/Ops.lean`: `JsOpImported` and `JsOpInlinable`, indexed by `Effectfulness` (`pure`/`effectful`) and `MayThrow` (`doesntThrow`/`mayThrow`); the runtime name is the constructor name (`ctor_names%`, `JsOpImported.runtimeName`); every array update (`push`, `pop`, `set`, `swap`, `fset`, `fswap`) is a pair `…_immutable` / `…_mutable` of functions of `runtime.js` at the same signature, paired by the generated `JsOpImported.toMutable?` (typed-array `push` / `pop` are `_immutable` only); aliases at the same signature are merged (`lean_array_get_borrowed` is `lean_array_get`) | done (now split into `JsTerm/Ops/`) |
| 7.3 | effect-directed optimisations in `JsTerm` | not done, by decision: every optimisation belongs to `Term.optimize` |

`JsOpImported` has 398 constructors (`JsTerm/Ops/Imported.lean`, generated); the operations
of each group of externs are in the generated `JsTerm/Ops/Cands/*.lean`.

The rest of this file is the plan as it was written, before the implementation. The facts about
the code it gives are those of that time.

---

## 1. `typedArray (kind : JsTypedArray) (elem : JsTerminalTy)` lets through nonsense

**Assessment: correct.** The two indices are independent, so `JsTy` accepts types like these:

- `typedArray .uint8Array .string`
- `typedArray .float64Array .bigint_nat`
- `typedArray .bigInt64Array .uint8`

None of them is a JavaScript value.

`lowerArrayPrim` only ever produces valid pairs, but nothing enforces that. This leaks into
every polymorphic operation, because each one quantifies over `(k : JsTypedArray) (e :
JsTerminalTy)`, e.g. `typedArray__lean_array_to_list`, `typedArray__uint53__lean_mk_array` and
`JsArrayLayout.typed k e`.

The pairs `lowerArrayPrim` actually produces:

| kind | element leaf |
| --- | --- |
| `Uint8Array` | `uint8`, `bitvec_small n` with `n ≤ 8` |
| `Uint16Array` | `uint16`, `bitvec_small n` with `8 < n ≤ 16` |
| `Uint32Array` | `uint32`, `bitvec_small n` with `16 < n ≤ 32` |
| `Int8Array` / `Int16Array` / `Int32Array` | `int8` / `int16` / `int32` |
| `Float32Array` / `Float64Array` | `float32` / `float` |
| `BigUint64Array` | `bigint_nat` (a `UInt64` at the bigint repr), `bigint_bitvec_big 64` |
| `BigInt64Array` | `bigint_int` (an `Int64` at the bigint repr) |

In every case the kind is a **function of the element**. For a `BitVec n` it is the smallest
typed array that holds `n` bits. `exactTypedArrayOnly` and `roundUpToSmallestTypedArray` only
decide *whether* a typed array is used, never *which* one. So the kind index is redundant.

**Proposal.** Replace the pair by one enumeration of the valid element types. Compute the
kind from it.

```lean
/-- The element types a JavaScript typed array can hold. -/
inductive JsTypedElem where
  | uint8 | uint16 | uint32 | int8 | int16 | int32
  | float32 | float64
  /-- A `UInt64` at the `BigInt` representation, in a `BigUint64Array`. -/
  | uint64
  /-- An `Int64` at the `BigInt` representation, in a `BigInt64Array`. -/
  | int64
  /-- A `BitVec n` of at most 32 bits, in the smallest unsigned array that holds it. -/
  | bitvec (n : Nat) (h₂ : 2 ≤ n) (h : n ≤ 32)
  /-- A `BitVec 64` at the `BigInt` representation, in a `BigUint64Array`. -/
  | bitvec64
  deriving DecidableEq, Repr

def JsTypedElem.kind : JsTypedElem → JsTypedArray        -- `bitvec n` ↦ Uint8/16/32Array by `n`
def JsTypedElem.leaf : JsTypedElem → JsTerminalTy        -- `uint64` ↦ `.bigint_nat`, …

inductive JsTy where
  …
  | typedArray (elem : JsTypedElem)
```

- `JsArrayLayout.typed (t : JsTypedElem) : JsArrayLayout (.typedArray t) (.terminal t.leaf)`.
- Polymorphic operations quantify over one `t : JsTypedElem` instead of `k e`.
- `typedArray__lean_array_to_list : (t : JsTypedElem) → JsOp … [.typedArray t] (.list t.leaf)`.

An alternative is to keep both indices and add a proof `(h : kind.holds elem)`. That is
strictly worse: every consumer then has to carry and transport the proof, and the kind is
still redundant.

**Impact (small):**

- `Ty.lean`: `lowerArrayPrim` becomes simpler.
- `gen_js_ops.py` and the generated ops files: `(k : JsTypedArray) → (e : JsTerminalTy)` becomes `(t : JsTypedElem)`.
- `PrintMini.lean` (`k.ctorName` becomes `t.kind.ctorName`).
- `Tests/Main.lean` (one `typedArray .uint8Array .uint8`).

Printed JavaScript does not change.

---

## 2. Records and unions cannot be empty

**Assessment: correct. In fact the bounds are stronger than "non-empty".** The source types
(`LeanScript/Ty/Syntax/Ty.lean`) already guarantee:

- **`Ty.record t fs`** has a first field plus `Fields` (one or more), so **at least 2
  fields**. `lowerTy` gives `.record (lowerTy t :: lowerFields fs)`, which is never shorter
  than 2. A one-field structure is unboxed before this stage.
- **`Ty.union cs [UnionShape bs]`** is built from `Ctors`, so it has **at least 2
  constructors**. `UnionShape` also requires **at least one constructor with fields**. A
  union of only nullary constructors is a `bool` or an `enum`, never a union.

`JsTy.record (fields : List JsTy)` and `JsTy.union (ctors : List (List JsTy))` drop all of
this. So `.record []`, `.record [t]`, `.union []`, `.union [[]]` and `.union [[], []]` are
all types. The printer even has a special case for `{}` (`JsExpr.pretty`, `record_mk`) that
no real program reaches.

**Proposal.** Keep the `List` indices, because `JsArgs`, `JsSel`, `JsUnionArms`, `pushAll`
and `JsMem cs fs` all work on lists. Add the invariant as a proof field with an `autoParam`,
so literal types still read naturally:

```lean
/-- A union shape: at least two constructors, and at least one of them has fields. -/
def JsUnionShape (cs : List (List JsTy)) : Prop := 2 ≤ cs.length ∧ cs.any (!·.isEmpty)

inductive JsTy where
  …
  | record (fields : List JsTy) (h : 2 ≤ fields.length := by decide)
  | union (ctors : List (List JsTy)) (h : JsUnionShape ctors := by decide)
```

- Proof irrelevance keeps `DecidableEq` and pattern matching (`.record fs _`) unchanged.
- `lowerTy` needs two lemmas: `(lowerFields cfg fs).length ≥ 1` and a transport of
  `UnionShape bs` through `lowerCtors`. Both are short inductions.
- `Tests/Main.lean` (`.union [[], [tN]]`, `.record [tN, .terminal .bool]`) compiles
  unchanged, because `by decide` fills in the proof.

The fully structural alternative is `record (f₁ f₂ : JsTy) (fs : List JsTy)`. It needs no
proofs, but every consumer has to write `f₁ :: f₂ :: fs`. That is more churn for the same
guarantee.

**Impact (small):**

- `Ty.lean`: the constructors, the hand-written `decEqTy` and `lowerTy`.
- `FromTerm.lean`: record and union types at construction sites.
- `Hoist.lean`: it builds `.union` types for `$tag0`.
- `PrintMini.lean` and `Syntax.lean`: drop the `{}` case.

---

## 3. `data (name : String)`: what it is, and how to improve it

**What it is.** `Ty.data r` is a reference to a member of a block of **mutually recursive
user datatypes** (`inductive Tree | leaf | node (l r : Tree)`). A recursive type cannot be
written out structurally, because it would be infinite. So the source language names it by a
`Ref ks`: the de Bruijn index of the block and the member index inside it. `lowerTy` turns
that reference into the string `D<depth>_<member>` (`refName`).

**Assessment: it is the weakest part of `JsTy`.**

1. **It is untyped.** It is a bare string: two different datatypes with the same printed name
   are the same `JsTy`, and nothing ties the name to a declaration.
2. **Its layout is unknown to the backend.** A value of type `.data n` cannot be matched,
   projected or constructed, because `JsTy` does not say it is, say, `union [[], [.data n,
   .data n]]`.
3. **It blocks every program that uses a recursive datatype.** Every construct that touches a
   datatype is `notYet` in `JsTerm/FromTerm.lean`: `Neu.data_out`, `PExpr.data_in`,
   `data_rec` and `data_brec`. Such a program is currently a conversion error.

**Proposal: index `JsTy` by the block sizes and reuse `Ref`. The module then carries the
unfoldings.**

```lean
inductive JsTy : List Nat → Type where
  …
  | data {ks : List Nat} (r : Ref ks) : JsTy ks          -- was `data (name : String)`

/-- The layout of every member of every declared block: what `data r` unfolds to. -/
def JsSig (ks : List Nat) : Type := (r : Ref ks) → JsTy ks  -- in practice a record/union

-- two expression formers, both the identity at run time (a datatype value *is* its layout):
| data_in  (r : Ref ks) (e : JsExpr … (Σ.unfold r)) : JsExpr … (.data r)
| data_out (r : Ref ks) (e : JsExpr … (.data r))    : JsExpr … (Σ.unfold r)
```

- This follows `Ty ks` / `DSig ks` in `LeanScript` one to one, so `lowerTy` stays a plain
  structural map.
- The printer can still print `D0_1` in the dump, because the name is computed from `r` as
  it is today.
- `JsModule` gets a `sig : JsSig ks` and a `ks`.
- `data_rec` / `data_brec` become ordinary recursive local functions (a `const f = (x) => …`
  that calls itself). That needs a `letRec` block former, or a top-level function per
  recursor.

**Cost.** Every `List JsTy` context becomes `List (JsTy ks)`. That is a mechanical `{ks}`
parameter in every file of `JsTerm/`. An intermediate step is possible: keep `JsTy`
unindexed, but replace the string by `data (block member : Nat)` and give `JsModule` a table
of unfoldings. It is cheaper but still not type-safe (a dangling index is representable), so
I would only use it as a stepping stone.

**Naming.** `data` is fine as a mirror of `Ty.data`. If a clearer name is wanted, `named r`
or `recTy r` would do.

**Impact (large):** it touches every `JsTerm/*.lean` file. It is also the only way to
convert programs that use user datatypes, so it is valuable.

---

## 4. Uncurried functions

**Assessment: correct.** Today `JsTy.fn (dom cod : JsTy)` has one argument, and
`JsExpr.app` / `JsExpr.lam` are unary. So a Lean `Nat → Nat → Nat` stored in a structure or
passed as an argument becomes `(a) => (b) => …`, and it is called as `f(a)(b)`. That
allocates an intermediate closure per call, and V8 cannot inline through it.

Top-level functions (`JsFun.params : List (String × JsTy)`) are already uncurried. Only
local and first-class functions are curried.

**Proposal:**

```lean
inductive JsTy where
  …
  | fn (doms : List JsTy) (cod : JsTy)     -- `(x₁, …, xₙ) => cod`, `n ≥ 0`

| app {σs} (f : JsExpr C M (.fn σs τ)) (args : JsArgs C M σs) : JsExpr C M τ
| lam {σs} (hints : List String) (body : JsBlock (pushAll σs C) M [] (.ret τ)) :
    JsExpr C M (.fn σs τ)
```

- `lazy t` is then just `fn [] t`. I would keep `lazy` as an abbreviation, or drop the
  constructor and `lazy_mk` / `lazy_force`, which become `lam []` / `app f .nil`.
- **The arity follows the type.** `lowerTy` uncurries *maximally*: `Ty.fn a (Ty.fn b c) ↦
  fn [a, b] c`. The representation of a Lean function type is then canonical, which is what
  lets values of that type be stored and passed around consistently.
- **Conversion from `Term`** (which is curried):
  - `λx. λy. body` becomes `(x, y) => body`.
  - A saturated `f a b` becomes `f(a, b)`.
  - A partial application `f a` of type `fn [b] c` becomes the closure `(y) => f(a, y)`.
  - Over-application becomes nested calls.
- **The one semantic caveat.** `λx. let z := work x; λy. g z y` has type `fn [a, b] c`, so it
  becomes `(x, y) => { const z = work(x); return g(z, y); }`. Now `work x` runs on *every*
  call instead of once per partial application. The results are the same, since the code is
  pure, but the cost can grow. Lean's own compiler makes the same trade-off. A later pass can
  keep the curried shape where `work` is expensive and the partial application is shared,
  but only if that is also reflected in the type. For a first version I would accept the
  trade-off.

**Optimisations this enables:**

- Calls of known functions with all their arguments go straight to the function.
- An arity-aware inliner (`app (lam hs b) args` becomes `b` with the arguments substituted).
- No closure allocation for multi-argument callbacks (`Array.foldl` bodies, comparators).

**Impact (medium):**

- `Syntax.lean` and `Vars.lean`: renaming and substitution under an n-ary binder, which
  `pushAll` already handles for patterns.
- `FromTerm.lean`: arity analysis and eta-expansion.
- `PrintMini.lean`, `Simplify.lean`, `InPlace.lean` and `Hoist.lean`: mechanical changes.

---

## 5. `FloatParts` belongs in its own module, and the core library already has it

**Assessment: correct on both counts.**

- `FloatParts`, `floatParts`, `floatSmallInt?`, `decDigits`, `shortestDecimal` and
  `numberSource` are about printing a JavaScript `number`. They have nothing to do with the
  grammar in `Syntax.lean`.
- **The Lean core library already has the type (no Batteries or Mathlib needed).** Lean
  4.34's `Init.Data.Float.Model` defines `Float.Model.UnpackedFloat`:

  ```lean
  inductive UnpackedFloat where
    | infinity (sign : Sign) | notANumber | zero (sign : Sign)
    | finite (sign : Sign) (mantissa : Nat) (exponent : Int) (mantissa_pos : 0 < mantissa)
  ```

  It comes with `Float.toModel : Float → Float.Model` and `Float.Model.unpack`, plus the same
  for `Float32`.
  - It is more precise than `FloatParts`: zero is its own constructor, so a finite value has
    a proof that `m > 0`.
  - `Sign` replaces `neg : Bool`.
  - It is maintained with the formal float model, so a hand-rolled bit decoder is one less
    thing to trust.
  - A quick `#eval` (not a test in the project) shows it runs on compiled code:
    `(3.5 : Float).toModel.unpack = finite positive 7881299347898368 (-51)`,
    `(-0.0).toModel.unpack = zero negative` and `(5e-324).toModel.unpack = finite positive 1 (-1074)`.
- **Batteries** (not a dependency of this project) has `Float.toRatParts : Float → Option
  (Int × Int)`. It loses the sign of zero and does not tell `NaN` from `±∞`, so it is not a
  better fit. Adding the dependency for it would not pay off.
- Shortest round-trip printing (what `shortestDecimal` does) is not in core. It stays ours.

**Proposal:**

- New module `JsTerm/NumberLit.lean` with `numberSource`, `shortestDecimal`, `decDigits` and
  `floatSmallInt?`.
- Delete `FloatParts` and `floatParts`. Match on `f.toModel.unpack` instead.
- Add `float32Source` for `JsLit.float32`, which today goes through `f.toFloat`. That is
  correct, but the shortest float32 decimal is often shorter.
- Tests in `Tests/Main.lean`:
  - round-trip `numberSource f` for special values, subnormals, `2^53 ± 1` and `0.1`;
  - compare against `node -e 'console.log(String(x))'` in the snapshot job.

**Impact (small):** `Syntax.lean` loses about 90 lines. `PrintMini.lean` and `Syntax.lean`
import `NumberLit`.

---

## 6. `unimplemented`: implement what is missing

**Assessment.** `gen_js_ops.py --report` lists **149** operations with no runtime function.
Each is emitted as `lean_extern_unimplemented("name")`, which throws. Grouped:

| group | count | examples | how | risk |
| --- | --- | --- | --- | --- |
| float / float32 math | 50 | `sin`, `atan2`, `exp2`, `pow`, `round`, `fabs`, `sinf` … | `Math.*`, plus `Math.fround` for float32 | see note A |
| float conversions | 36 | `to_uint8..64`, `to_int8..64`, `to_bits`/`of_bits`, `frexp`, `scaleb`, `to_string` | `DataView` for bits; saturating casts as Lean defines them; `frexp`/`scaleb` via bits | `to_string` must match Lean's formatting exactly |
| string / substring / slice | 48 | `string_drop`, `trim`, `posof`, `utf8_prev`, `substring_takewhile`, `slice_hash` … | the existing `$utf8*` helpers (positions are UTF-8 byte offsets); `slice_hash` reuses `lean_string_hash` | higher-order ones (`foldl`, `any`, `all`, `takewhile`) take a closure, so they depend on §4 |
| version / platform | 12 | `lean_version_get_major`, `lean_system_platform_target`, `lean_internal_is_stage0` … | inline literals generated from the Lean that runs `leanscript` (`Lean.version.major`, …) | see question Q3 |
| hashes | 3 | `lean_uint64_mix_hash` (×2), `lean_get_githash` | port `lean_uint64_mix_hash` bit for bit from the Lean runtime C source; `githash` is a literal | must match Lean exactly (snapshots compare hashes) |

**Note A (exactness).** `Math.sin` etc. are "implementation-approximated" in JavaScript, and
libm's `sin` is not correctly rounded either, so results can differ by one ulp. Expect a few
snapshot differences, and compare float math up to 1 ulp.

Two functions are **not** approximations but have different semantics, and must be written
by hand:

- **`round`:** C rounds half away from zero, while `Math.round` rounds half toward +∞. So
  `round(-2.5)` is `-3` in C but `Math.round(-2.5)` is `-2`. Use
  `Math.sign(x) * Math.round(Math.abs(x))`, plus a `-0` fix.
- **Float to integer casts:** Lean saturates, and `NaN` becomes 0.

**Proposal:**

1. Implement the groups in `runtime.js`, or as inline templates in `js_ops_inline.json` where
   one operator suffices. Order: platform → float math → conversions → string → hashes.
2. Once the report is empty:
   - Split the remaining uses of `JsExpr.unimplemented` into a new `JsExpr.unreachable τ`
     for the defaults of traversals (the `Inhabited` instances) and the "unused field" case
     in `FromTerm`.
   - Make an extern with no operation a **conversion error**, like the literal-too-big
     error. It is then no longer a runtime throw.
   - Delete `lean_extern_unimplemented`.
3. Add a test to `Tests/Main.lean` that fails if the report is non-empty.

**Impact:**

- Mostly `runtime.js` and `gen_js_ops.py` (about 150 small functions).
- `Syntax.lean`, `Extern.lean`, `FromTerm.lean` and `Hoist.lean` for step 2.

The groups are independent of each other and of §1–§5, so they can be done in parallel.

---

## 7. One `Ops.lean` with `JsOp : Purity → Inlinability → …`, mutable variants, and purity in the grammar

### 7.1 Merge the files and index by purity and inlinability

**Assessment: sound.**

- The split into two inductives is only about *how an operation is printed*. `OpsLookup.lean`
  already re-merges them into a sum `JsOp σs τ := imported | inlined`.
- One inductive indexed by the printing strategy is simpler, and the indices let functions
  be total on their half:
  - `template : JsOp p .inlined σs τ → JsInline`
  - `runtimeName : JsOp p .imported σs τ → String`
- **Syntax corrections to the sketch:**
  - Constructors are written without the leading dot: `inductive Purity where | pure | impure`.
  - **`import` is a Lean keyword**, so `.import` cannot be a constructor name. Use
    `imported` / `inlined`.
  - Spell the type `Inlinability`.

```lean
inductive Purity where
  /-- No observable effect: may be hoisted, shared (CSE), dropped when unused, speculated. -/
  | pure
  /-- May mutate an argument or throw: stays where it is, runs exactly as often as written. -/
  | impure
  deriving DecidableEq, Repr

inductive Inlinability where
  /-- Written inline (`a & b`, `BigInt(a)`): `JsOp.template`. -/
  | inlined
  /-- A call of the function of `runtime.js` of the same name: `JsOp.runtimeName`. -/
  | imported
  deriving DecidableEq, Repr

/-- Generated by `scripts/gen_js_ops.py`. -/
inductive JsOp : Purity → Inlinability → List JsTy → JsTy → Type where
  | bigint_nat__lean_nat_land : JsOp .pure .inlined [bigint_nat, bigint_nat] bigint_nat
  | uint53__lean_nat_land     : JsOp .pure .imported [uint53, uint53] uint53
  | uint53__lean_nat_add      : JsOp .impure .imported [uint53, uint53] uint53  -- throws past 2^53
  | uint53__lean_array_fset_immutable : {A E} → JsArrayLayout A E →
      JsOp .pure   .imported [A, uint53, E] A
  | uint53__lean_array_fset_mutable   : {A E} → JsArrayLayout A E →
      JsOp .impure .imported [A, uint53, E] A
  …
```

**Where the purity comes from.** The generator needs a purity column:

- **Mutating** operations are `.impure`.
- **Operations that can throw** are `.impure`. These are the `uint53`/`int53` operations
  that check overflow with `$chk53`, and the `number` representations of `UInt64`, `Int64`
  and `BitVec`. The inline catalogue (`js_ops_inline.json`) gets a `"purity"` field, and
  imported operations default to `pure` unless listed.

**Recommendation: consider a three-way `Purity` (`pure | throws | mutates`).** With only
two levels, *every* `uint53` arithmetic operation is `.impure`, just because it can overflow.
At the `pbo` preset that disables hoisting and CSE for most arithmetic. The three levels
permit different rewrites:

- **`throws`:** safe to CSE (the same inputs give the same throw) and to drop when unused,
  if a disappearing `RangeError` is acceptable. The overflow is a limitation of the
  representation, not Lean behaviour. Not safe to speculate out of a branch.
- **`mutates`:** allows none of these.

The type then has an order `pure ≤ throws ≤ mutates`, and everything below uses `≤` where it
says "pure". This is a design question (Q1).

**Risk: elaboration time.** One inductive of about 500 constructors with four indices is
bigger than today's 320 + 171. A function total on `.inlined` still has to dismiss about 330
impossible `.imported` cases during pattern-match compilation. That can be slow, so I would
measure it first. A known fallback keeps one user-facing `JsOp` but generates it as two
nested levels:

```lean
inductive JsOp : Purity → Inlinability → List JsTy → JsTy → Type where
  | inl (op : InlineOp p σs τ) : JsOp p .inlined σs τ
  | imp (op : ImportOp p σs τ) : JsOp p .imported σs τ
```

That is still one file and one type, and the matches stay small.

**Name clash.** `OpsLookup.lean` already defines a `JsOp σs τ` (the sum). The new type
replaces it. `ofSig` / `firstOf` return `Σ p i, JsOp p i σs τ`.

### 7.2 Immutable and mutable variants

Operations that return an updated copy of an array argument:

| extern | variants today | to add |
| --- | --- | --- |
| `lean_array_push` | `array__…` and `…_inplace` | rename to `_immutable` / `_mutable` |
| `lean_array_pop` | `array__…` and `…_inplace` | rename |
| `lean_array_set` | `bigint_nat__`, `uint53__`, and `_inplace` | rename |
| `lean_array_swap` | `bigint_nat__`, `uint53__`, and `_inplace` | rename |
| `lean_array_fset` | immutable only (an alias of `set` in `runtime.js`) | **`_mutable`** (×2 reprs) |
| `lean_array_fswap` | immutable only (an alias of `swap`) | **`_mutable`** (×2 reprs) |

Some operations are **not** candidates:

- **String operations** (`lean_string_push`, `append`, `utf8_set`, …): JavaScript strings are
  immutable primitives.
- **Reads** (`get`, `get_borrowed`, `get_size`) and **constructors** (`mk_array`,
  `mk_empty_array_with_capacity`): they do not update anything.

**Two remarks:**

- **Typed arrays.** A typed array cannot grow or shrink. `push_mutable` / `pop_mutable` on a
  typed array still copies at O(n) (the runtime checks `Array.isArray` at run time).
  - With the layout index known, the generator can drop the run-time check: specialise
    `_mutable` push/pop to `JsArrayLayout.generic`, and keep the typed-array cases on
    `_immutable`.
  - The alternative is a growable buffer: a typed array plus a length, doubling capacity.
    That is a separate, larger change.
- **`InPlace.lean`.** `toInPlace?` maps `_immutable` to `_mutable`. Today it is a hand-written
  table of 6 entries. The generator should emit this pairing, so a new mutable operation is
  picked up automatically. `runtime.js` names change accordingly, and the test that
  `runtime.js` exports every operation keeps them in sync.

### 7.3 Purity in the grammar, and what to use it for

**Proposal.** Index expressions by an *upper bound* on the effects they may have. Leave
blocks unindexed: a block is a sequence of statements whose order is fixed anyway.

```lean
inductive JsExpr : Purity → List JsTy → List JsTy → JsTy → Type where
  | op {p q i σs τ} (o : JsOp q i σs τ) (h : q ≤ p) (args : JsArgs p C M σs) : JsExpr p C M τ
  | lam …  : JsExpr p C M (.fn σs τ)      -- building a closure is pure, whatever its body
  | app {p} (f : JsExpr p C M (.fn σs τ)) (args : JsArgs p C M σs) (h : .impure ≤ p) : JsExpr p C M τ
  | cond {p} (c : JsExpr p …) (a b : JsExpr p … τ) : JsExpr p C M τ
  | cvar / mvar / lit / global / record_mk / … : JsExpr p …   -- pure at any bound
  …
def JsExpr.relax (h : p ≤ q) : JsExpr p C M τ → JsExpr q C M τ   -- structural, no proof search
```

- `imported` / `inlined` merge into the single `op` former. The printer dispatches on the
  `Inlinability` index.
- Reading a mutable variable (`mvar`) is pure as an expression. What matters is only that an
  expression is not moved across an `assign` to that variable. That check is about
  occurrences, and `Vars.lean` already tracks them.
- A call of an unknown function (`app`) is treated as `.impure`: it may run mutating or
  throwing code. Adding a purity to function types (`fn (p : Purity) σs τ`, an effect on
  the arrow) would make pure closures callable in pure code. It is a natural later extension,
  not needed at first.

**The alternative** is no index, only a computed `JsExpr.purity : JsExpr C M τ → Purity`,
plus a subtype `{e // e.purity = .pure}` where it matters. It is cheaper to introduce, but
the guarantees are only checked where someone remembers to ask.

**How it would be used, pass by pass:**

1. **Hoisting (`Hoist.lean`).**
   - `JsConst.e : JsExpr .pure [] [] ty`. The type checker then guarantees that a shared
     top-level constant cannot mutate or throw.
   - Today this is a boolean filter ("arrays and runtime calls are never moved"). With the
     index, pure runtime calls (`bigint_nat__lean_nat_div(12n, 5n)`) can be hoisted too.
2. **Dead code (`Simplify.lean`, new rewrite).** `const x = e; rest` with `x` unused
   becomes `rest` only when `e : JsExpr .pure`. With the three-way variant, `throws` also
   qualifies. `Simplify` has no dead-code rewrite today.
3. **Inlining a single-use `const` into its use.** Always allowed for a pure `e`. For an
   impure `e`, only when no other impure expression is evaluated in between.
   - `Simplify.inlineArrays` already does this for array literals.
   - It relies on an ad-hoc syntactic check ("the elements are variables, literals and
     spreads: no effect, cannot fail").
   - With the index, that check becomes `e : JsExpr .pure`, and the rewrite extends to any
     pure expression.
4. **CSE.** Two occurrences of the same pure expression in scope become one `const`.
5. **Speculation.** `if (c) { return a } else { return b }` becomes `return c ? a : b`.
   `cond` with impure branches is still fine, because only one branch runs. The rewrite
   that needs purity is the reverse direction, and hoisting an expression out of a branch
   *above* the `if`. That needs `a : JsExpr .pure`.
6. **Loop-invariant code motion** (`forRange`, `forOf`). A pure expression that reads no
   variable bound in the body moves before the loop.
7. **In-place updates (`InPlace.lean`).** The `_mutable` operations are the only `.impure`
   array operations, so the ownership analysis can state what it checks: no pure expression
   that reads the array is evaluated after the impure update. Every `_mutable` operation
   lands in the `impure` world, so a later pass cannot reorder it by accident.
8. **Correctness statements of the optimiser.** Rewrites like "drop an unused pure `const`"
   or "hoist a pure constant" are only sound for pure expressions. With purity in the type,
   these lemmas can be stated for a JavaScript evaluator (`eval (drop e rest) = eval rest`
   for `e : JsExpr .pure`) without side conditions.

**Impact (medium):**

- `gen_js_ops.py`: purity column, one output file.
- `Ops.lean` replaces `OpsImported.lean` + `OpsInlined.lean`; `OpsLookup.lean` keeps only the
  lookup.
- `Syntax.lean` and `Vars.lean`: the new index.
- `Simplify.lean`, `Hoist.lean` and `InPlace.lean`: they use it.
- `PrintMini.lean`: one `op` case instead of two.
- `runtime.js`: renames.
- `Tests/Main.lean`: operation names.

---

## Phased plan

Each phase ends with these checks green, and is one commit series:

- `lake build JsTerm leanscript tests`
- `lake test`
- `scripts/leanscript-snapshots.sh` (node comparison)

| phase | content | size | depends on |
| --- | --- | --- | --- |
| **0** | §5: `NumberLit.lean`, use `Float.Model.UnpackedFloat`, add float32 printing and tests | S | — |
| **1** | §1 `JsTypedElem`, §2 record/union invariants | S | — |
| **2** | §7.1 + §7.2: generator emits one `Ops.lean` with `Purity`/`Inlinability` (measure elaboration time; fall back to the two-level shape if slow), `_immutable`/`_mutable` naming, `fset`/`fswap` mutable variants, generated `toInPlace?` table, `runtime.js` renames | M | 1 (the ops signatures mention `JsTypedElem`) |
| **3** | §7.3: purity index on `JsExpr`; `JsConst` pure by type; Simplify/Hoist/InPlace use it (dead code, CSE, loop-invariant motion) | M | 2 |
| **4** | §4: n-ary `fn`/`lam`/`app`, maximal uncurrying in `lowerTy`, eta-expansion of partial applications, `lazy` = `fn []` | M | 3 (so the new binders come with purity) |
| **5** | §3: `JsTy ks`, `data (r : Ref ks)`, `JsSig`, `data_in`/`data_out`, recursors → recursive local functions; removes the `notYet`s in `FromTerm` | L | 4 (recursors are n-ary functions) |
| **6** | §6: implement the 149 missing operations by group; then `unreachable` + "no operation" as a conversion error + empty-report test | M | 4 for the string operations that take closures; the rest can run in parallel from phase 0 |

## Open questions for you

- **Q1.** Two-level `Purity` as in your sketch, or three levels (`pure | throws | mutates`)?
  With two levels, all overflow-checked `uint53` arithmetic is `impure`.
- **Q2.** For uncurrying: is the loss of sharing between curried binders acceptable (§4, the
  caveat), with a possible later refinement?
- **Q3.** `lean_system_platform_target`, `lean_version_*`, `lean_get_githash`: should
  generated code report the Lean toolchain that ran `leanscript` (matching the snapshots
  against Lean)? Or should it report a JavaScript-specific platform?
- **Q4.** Float math may differ from Lean's native results by one ulp (§6, note A). Should
  the snapshot comparison allow 1 ulp for these operations, or must they be bit-exact? Being
  bit-exact means shipping a correctly rounded implementation in `runtime.js`.
