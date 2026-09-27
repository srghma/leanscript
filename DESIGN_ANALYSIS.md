# Design analysis: shortcomings of `Ty` and `Term`

This reviews the code as it is now: `LeanScript/Ty.lean`, `LeanScript/Decl.lean`,
`LeanScript/Den.lean` (types and what they mean), and `LeanScript/Term.lean`,
`LeanScript/Eval.lean`, `LeanScript/TermSubst.lean` (terms and their evaluator). Where it
helps, it says how the translator (`LeanScript/TermElab/ToTerm*`) and the generators
(`LeanScript/GenElab/`) are affected.

Only the claims in §1.2 have Lean checks. They are in `TyTests/DenNonInjectiveTest.lean`,
which is part of `lake build`. Everything else here is a reading of the source and of
`NOT_IMPLEMENTED.md`, not a formal result.

Note: this tree has no `LeanScript/Ty/` directory, no `TyWf`, no `ty_wf` tactic and no
`CoeOut Ty TyWf`. `Ty` is one file, and its well-formedness is built into the constructors
(the `2 ≤ n` / `2 ≤ s.length` proofs of `LeanPrimTy.bitvec` / `LeanPrimTy.stringPos`, `UnionShape`, `Ctors` having at least two constructors).
This analysis covers that design.

---

## 1. Shortcomings of the current `Ty` design

### 1.1 The "every type has ≥ 2 values, and two values is only `bool`" rule is expensive

The grammar makes a type with no value, one value, or two values other than `bool`
impossible to write. That makes `Ty.den_exists_ne` and `Ty.eq_bool_of_two_points` true,
but it costs a lot:

- **`Unit` and unit-like types have no type.** `Unit`, `PUnit`, an empty structure,
  `Option Unit`, `Except ε Unit`, `StateM σ Unit`, `Std.HashSet α` (= `HashMap α Unit`), and
  every function returning `Unit` are refused. Ordinary Lean code uses these all the time,
  so the translator has to refuse them instead of erasing them.
- **Rules that never end.** Because of the invariant, the grammar needs the proofs in `LeanPrimTy.bitvec` / `LeanPrimTy.stringPos`,
  `UnionShape`, a separate `Ty.enum` for field-less sums of ≥ 3 constructors,
  `LeanEnumSchema.extraConstructors` (counting from 3), `Ctor.nullary` vs `Ctor.fields`,
  records of ≥ 2 fields, `Decl.wrap`'s `isOld = false`, and the grounding index `g` and the
  base constructor of `Alts`. Every new type former has to be checked against the invariant.
- **Proofs inside data.** `LeanPrimTy.bitvec n h` and `LeanPrimTy.stringPos s h` carry a size proof, and
  `Ty.union` carries a `UnionShape` instance. You have to write `(h := h)` in every match on
  `.union`, and a non-literal `p` (such as `.stringPos s` for a variable `s`) needs a proof
  by hand.
- **Encoding depends on context.** A one-field structure is its field, a one-constructor
  multi-field type is a record, and a two-point type is `bool`. So the `Ty` of a Lean type
  depends on counting its values, not on its shape. A small change to a Lean declaration
  (adding a field or a constructor) can change the encoding completely.
- **The count is not checked everywhere.** Proof fields are erased, subtypes become their
  carrier, and indices are erased. So `{x : Nat // x < 1}` (one value in Lean) becomes
  `nat`, and `Vec Bool 1` (two values in Lean) becomes a list. The invariant is guaranteed
  for `Ty`, but not for the Lean type that `Ty` stands for.

### 1.2 `Ty.den` is not injective, so "canonical forms" are only syntactic

The file header says each finite set of points has exactly one type. That holds for
field-less types, but distinct `Ty`s can still mean the same Lean type (checked by `rfl` in
`TyTests/DenNonInjectiveTest.lean`):

| two different `Ty`s | same meaning |
| :-- | :-- |
| `record a (.one (record b (.one c)))` vs `record a (.cons b (.one c))` | `A × B × C` |
| `union (.two .nullary (.fields (.one a)))` vs `union (.two (.fields (.one a)) .nullary)` | `Option A` |
| `union (.cons a' (.two b' c'))` vs `union (.two a' (.fields (.one (sum b c))))` | `A ⊕ B ⊕ C` |
| `enum ⟨0, 0⟩` vs `enum ⟨0, -1⟩` | `Fin 3` |

Consequences:

- The constructor order of an `Option`-like union, and the `shift` of an enum, exist in the
  syntax but not in the meaning. The meaning cannot say "the `none` constructor came first".
- Lean instances on `Ty.Den Δ t` (`Repr`, `BEq`, …) cannot tell these types apart.
- Because right-nested products and sums are used for meanings, a record cannot be told
  apart from a record nested in its last field.

### 1.3 Types have no names

`Ty`, `Decl`, `Fields` and `Ctors` hold no constructor names, field names, datatype names
or enum constructor names. `SignatureTest` shows `Point` becoming `.record .nat (.one .int)`
and `Color` becoming `.enum ⟨0, 0⟩`. For a JavaScript backend this is a real loss:

- generated code cannot use `{x, y}` objects or named tags, and debugging output shows
  positions;
- two Lean structures with the same field types (`Point := Nat × Int` and
  `Pair := Nat × Int`) are the *same* `Ty`, so a type-directed backend choice (such as
  printing, or a custom JS class) cannot depend on the Lean type;
- names would have to be kept in a side table beside the signature.

### 1.4 The meaning of a type is not the Lean type

`Ty.Den Δ t` is built from `Prod`, `Sum`, `Option`, `Bool`, `Fin n` and indexed W-types
(`IW`). It is not the user's inductive:

- a `Point` value is a `Nat × Int`, a `Color` is a `Fin 3`, and a `List Nat` is an `IW` tree
  whose children are functions out of position types (`ListPos`, `PUnit`, …);
- there is **no general encoding or decoding** between a Lean inductive and `Ty.Den` of its
  `Ty`. Every correctness statement about a translated function
  (`TermTests/*Proofs.lean`) builds its own encoding by hand;
- a value of a declared datatype has no decidable equality or `Repr` (it is a W-type with
  function-valued children), so a test cannot `#eval` it or compare it with `==`. It can
  only compare results of leaf type, or fold the value first;
- kernel reduction (`rfl` runs) of `IW` values goes through `DSig.block`'s `toIW`/`ofIW`
  transports, `Mems.rollMember`, `listRoll`, etc. That is heavy, and it is one reason
  `rfl`-based tests are slow.

### 1.5 Recursive types are nominal, per program, and not unique

- A recursive type is a name `Ty.data r` into one program's `DSig`. So `List Nat` in two
  programs gives two unrelated `Ty`s, and no function or term can be shared between
  programs. There is no `Term` or `Ty` weakening along an extension of the signature: `Ty.map`
  renames `Ref`s, but nothing does the same for `Term`, whose type contains the whole `Δ`.
- The same block can be declared in several syntactically different ways: members in a
  different grounding order, and a different choice of the grounded base constructor
  (`Alts.two₁` / `two₂` / `here` / `there`). `DecidableEq (DSig ks)` therefore does not decide
  "same datatypes".
- **No type parameters**: `List Nat` and `List String` are separate blocks. Generic
  containers are copied once per instance, and there is no polymorphic `Ty`.
- `List` is a declared datatype but `Array` is primitive. Lists get `data_rec`, arrays get
  only `array_foldl`.
- `ks : List Nat` stores block sizes minus one (`k` means `k + 1` members). This is easy to
  get off by one, and `Fin ((Δ.block b).k + 1)` appears in every datatype term former.

### 1.6 Some Lean type features are erased instead of typed

These are documented in `NOT_IMPLEMENTED.md` §1. In each case the language type has more
values than the Lean type, and nothing relates the two:

- indices of inductive families (`Vec α n` becomes a list);
- dependent fields (`Fin n → Nat` becomes `Nat → Nat`);
- `Fin m → X` on a recursive cycle becomes `Nat → Option X`;
- proofs and subtypes (`Fin k`, `Subtype`) become their carrier;
- quotients become their carrier;
- type-indexed families (`Nest`) go through a generated `Elem` type;
- existentially typed fields (`Unfold.State : Type`) are refused.

### 1.7 Coverage gaps

- No `unit`, no effects (`IO`, `Task`, `Thunk`), no `ByteArray`/`FloatArray` (commented out
  of `LeanPrimTy`).
- No recursive occurrence in a function's domain (a strict-positivity restriction that
  Lean also has, but here it is enforced by `Fld.fn` taking an *older* `Ty`).
- Everything is in `Type` (universe 0).
- `LeanPrimTy` mixes Lean types with JavaScript representation notes. Several leaves
  (`stringSlice`, `substringRaw`, `floatModel`, `float32Model`) have open questions in
  their doc comments.

---

## 2. Shortcomings of the current `Term` design

### 2.1 `Comp.extern` holds a Lean function

`extern name f args` holds `f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ` next to a
`name : String`.

- **Nothing links `name` and `f`.** A term can be named `"Nat.add"` and compute `Nat.mul`.
  The evaluator uses `f` and a JavaScript backend would use `name`, so the two meanings can
  differ without anything noticing.
- `Term` has **no `DecidableEq`, `BEq` or `Repr`** (stated in `Term.lean` and
  `NOT_IMPLEMENTED.md`), so terms cannot be compared, hashed, deduplicated or printed, and a
  term cannot be serialized.
- The type of `f` depends on `Δ`, so an extern over a declared datatype belongs to that one
  signature.
- Because `Ty.Den` is not the Lean type (§1.4), a Lean library function on a non-leaf type
  (`Array.push` on an array of structures, `List.length`) cannot be used as `f` directly.
  This is why the translator only allows externs on leaf types, and refuses `qs.size`,
  `qs.map`, `qs[i]` on member arrays.

### 2.2 Terms are not first-order data

Apart from `extern`, several term formers hold Lean functions:
`enum_casesOn : (Fin n → Term …)`, `data_rec`/`data_brec` branches
`(i : Fin _) → Term …`, and the answer types `ρ : Fin _ → Ty ks`. So even without `extern`,
a structural derived `DecidableEq` does not work, and a program over terms (an optimizer or
a code generator) has to handle functions, not syntax.

### 2.3 Intrinsic typing over a concrete `Δ` makes terms heavy

- `Term Δ Γ τ` is indexed by the signature *value* `Δ`, not only by `ks`. Checking the
  types of `data_in b j e` needs `(Δ.block b).unfold j` to reduce by whnf through
  `DSig.block`, `Mems.inst` and `Mems.instMember`. That makes elaboration slow for large
  signatures (see `proposals/BuildSpeed*.md`).
- There is no untyped or less-typed intermediate form. Every stage (translator, future
  optimizer, JS printer) has to produce well-typed-by-construction terms or work on Lean
  `Expr`s that stand for them.
- There is no type checker from raw syntax to `Term` (no `Term.check? : RawTerm → Option
  (Term Δ Γ τ)`), so terms can only be built through Lean's elaborator.

### 2.4 Only folds: no general recursion, and no early exit

Every loop is `nat_rec`, `array_foldl`, `data_rec` or `data_brec`. That makes `eval` total,
but:

- well-founded recursion, fuel-free loops (`while`), partial functions and coinductive data
  cannot be written;
- `nat_rec` is unary and non-dependent. It iterates `n` times with no early exit, and `for`
  loops pay for `break` by carrying a `ForInStep` to the end. Evaluating it by `rfl` in the
  kernel is only practical for small `n`;
- `array_foldl` always goes from `0` to `size`: there is no range, reverse fold, or `break`;
- `data_rec` folds the **whole block** with one answer type per member. So two functions of
  a `mutual` group on the same member are refused, and members that nobody recurses on still
  need made-up branches;
- `data_brec` looks down a fixed depth `k`, chosen when the term is written;
- `data_rec` branches receive paramorphism-style `(subvalue, answer)` pairs. This is general,
  but writing it by hand is very verbose (see `TermTests/TermTest.lean`, `sumT`, `roseSumT`).

### 2.5 No polymorphism and no effects

- There are no type variables or type abstraction, so every generic function is translated
  once per instance (`#leanscript_to_term f (α := T)`), and the translator refuses
  definitions with a type or instance parameter.
- There is no monad or effect former: only `Id` `do` blocks are translated.

### 2.6 Hard to use by hand

- **De Bruijn only, with no names.** `Ctx` is `List (Ty ks)`, so generated JavaScript needs
  made-up variable names, and hand-written terms need comments explaining binder order
  (`record_casesOn` binds *all* fields, the first innermost. `nat_rec`'s step binds the
  answer at `0` and the predecessor at `1`. `array_foldl` binds the element at `0` and the
  accumulator at `1`).
- **No projection former**: reading one field means `record_casesOn` and binding every
  field.
- **Only unary `lam`/`app`**: multi-argument functions are curried, and there is no
  multi-argument call to map to JS functions efficiently.
- `ite` needs a `bool` term. Matching on a literal (`match s with | "a" => …`) goes through
  `ite` of an extern `decide`, and there is no dependent `dite` (the proof is dropped, see
  `proposals/ProofCarryingDiteProposal.md`).
- `CtorIx`, `Args`, `Branches` and `Elems` are four more mutual inductives that exist only
  to keep `eval` structural. They add many cases to every traversal (`rename`, `subst`,
  `eval`).

### 2.7 Metatheory and correctness gaps

- `TermSubst.lean` proves that renaming and substitution commute with `eval`, but not the
  syntactic laws (composition of substitutions, `rename` as a special `subst`).
- There is no general theorem that `#leanscript_to_term f` evaluates to `f`. Correctness is
  proved per example (`TermTests/*Proofs.lean`) or checked on samples, and each proof needs
  its own encoding because of §1.4.
- There is no notion of the cost of evaluation, and no guarantee that `letE` shares work in
  a backend. `eval` fixes only the meaning.

---

## 3. Summary

| area | main problem | main effect |
| :-- | :-- | :-- |
| `Ty` invariant (≥ 2 values, two is `bool`) | `Unit` and friends cannot be written; proofs inside data | common Lean code is refused; more rules to keep |
| `Ty.den` | not injective, not the Lean type, no names | no generic encoding or decoding, no printing, per-example proofs |
| declared datatypes | nominal per `DSig`, no type parameters, several encodings of one block | no sharing between programs, copies per instance |
| `Comp.extern` | holds a function whose link to its name is unchecked | no `DecidableEq`/`Repr`, name and meaning can differ |
| `Term` indexing | over a concrete `Δ`, higher-order children | slow elaboration, no first-order IR for later stages |
| control flow | folds only, one answer per member, fixed `brec` depth | many Lean definitions refused or rewritten into heavy terms |
| usability | de Bruijn, no projections, unary functions | hand-written terms are hard to read and write |
