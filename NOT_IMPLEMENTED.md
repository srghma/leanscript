# What is not implemented yet

This list describes the project as it stands now: one grammar of types (`LeanScript/Ty.lean`,
`LeanScript/Decl.lean`), one grammar of terms (`LeanScript/Term.lean`), the generators
(`LeanScript/Signature.lean`, `LeanScript/GetCtor.lean`, `LeanScript/Gen/`) and the translator
`#leanscript_to_term` (`LeanScript/ToTerm.lean`). Each item names where to read more.

## 1. Types

- **Existentially typed fields.** A constructor with a field whose value is a type
  (`State : Type` in `Unfold`) is refused (`LeanScript/Gen/Read.lean`, `readCtors`). This
  was deferred on purpose.
- **Inductive families have their indices erased, not typed.** `Vec α n` is the datatype
  `Vec α` of every length (`Gen/Read.lean`, `normType`), and a constructor field that only
  names an index (`n` in `Vec.cons {n} a v`) is dropped (`erasedFields`): `Vec α` is a linked
  list, and `Matrix` (`rows`, `cols`, `cells : Vec (Vec Nat cols) rows`) a record of two
  numbers and a list of lists. `TermTests/IndexedFamilyProofs.lean` proves, for every input,
  that the translations of `Vec.sum`, `Vec.double`, `Vec.sumRows` and `Matrix.size` compute
  what the Lean functions compute, that the encoding of vectors is injective (the length is
  recovered), and the value counts behind the refusals and caveats below; other translated
  functions over families are only checked on samples. Caveats
  (`TermTests/IndexedFamilyTest.lean`):
  - the erased type has more values than the Lean one (a `Vec Nat 3` is any list);
  - at *closed* indices only the constructors that can build a value are checked, one level
    deep: `Vec Nat 0` (one value), a family with no or two field-less constructors at the
    index are refused, but `Vec Bool 1` (two values in Lean) is a list of `Bool`;
  - at an index that is a variable nothing is checked: a family with one value at every
    index (`Idx : Nat → Type`, `z : Idx 0`, `s : Idx n → Idx (n + 1)`) becomes a unary
    number;
  - in `#leanscript_to_term`, a parameter that only names an index (`{n}` in
    `Vec.sum {n} (v : Vec Nat n)`) is dropped and cannot be used as a value (`Vec.len v := n`
    is refused), and a branch Lean proves unreachable (`Vec.head : Vec α (n + 1) → α`, whose
    `nil` branch is reachable after erasure) is refused.
- **Families indexed by a type are erased through a generated element type, not typed.**
  `Nest : Type → Type 1` with `cons : α → Nest (α × α) → Nest α` has infinitely many
  instances, so none of them is a block member. `Gen/Read.lean` (`typeFamilySteps`,
  `ensureElem`, `canonIndex`) generates, once, the Lean inductive
  `Nest.Elem α := leaf α | node (Nest.Elem α) (Nest.Elem α)` (one `node` per recursive index;
  a structure index such as `α × α` is flattened into its fields), and reads `Nest τ` as the
  datatype `Nest (Nest.Elem B)`, `B` being `τ` with the recursive indices peeled off
  (`Nest (Nat × Nat)` and `Nest Nat` are the same datatype). A value at depth `k` is put in
  `Nest.Elem B` (`injectElem`: `(2, 3)` is `node (leaf 2) (leaf 3)`). A function generic in
  the index (`Nest.length`) is translated at the index the program declares the family at,
  or at `#leanscript_to_term f (α := T)`. `TermTests/NestProofs.lean` proves that the encoding
  is injective at every index and that the translated `Nest.length` is correct on every
  value. Caveats (`TermTests/NestTest.lean`):
  - the erased type has more values than the Lean one (an element may be a tree of any shape,
    not a perfect tree of the depth of its level);
  - an element read at its Lean type (`headNat : Nest Nat → Option Nat`, `| .cons a _ => some
    a`) is refused: in the language it is an element of `Nest.Elem Nat`;
  - only families with one index, of type `Type`, no universe parameters, and constructors
    generic in the index (no `G.nat : Nat → G Nat`) are supported; a recursive index in which
    the index is not positive (`Neg (α → Nat)`) is refused by the kernel check of the element
    type; a value at an unflattened recursive index (`Two (List α)`) cannot be put in the
    element type (its type is supported);
  - `Nest Unit` and `Nest Empty` are refused (the element type holds a `Unit`/`Empty` field),
    although `Nest Unit` has infinitely many values in Lean;
  - the element type is declared in the module that first needs it: two modules that both
    generate it and are then imported together clash.
- **Dependent fields are erased, not typed.** A field whose type depends on an earlier field
  is read through its erasure (`Gen/Read.lean`, `eraseDeps`): the dependency may only go
  through arrows, type arguments, and wrappers of one value besides proofs. `Fin n → Nat` is
  `Nat → Nat`, `Tele.cons (n : Nat) (v : Fin (n + 2)) rest` has two `Nat` fields, `Vector α n`
  is `Array α`, a dependent arrow `(i : Fin n) → Fin (i + 1)` inside a field is `Nat → Nat`.
  A type computed from a value (`cond b Nat String`) is refused. The erased type has more
  values than the Lean one (every `Nat`, not only those below `n`); nothing relates the two.
  (`TermTests/DependentFieldTest.lean`.)
- **`Fin m → X` on a recursive cycle is `Nat → Option X`, not typed.** When the bound `m` is
  an earlier field and `X` is on a recursive cycle through the constructor's type
  (`RoseF.node : (m : Nat) → (Fin m → RoseF) → RoseF`, `WT Nat Fin`, the `Σ` form
  `(m : Nat) × (Fin m → RoseS)`), the field is read as `Nat → Option X`
  (`Gen/Read.lean`, `finOptArrow`): the plain erasure `Nat → X` would have no base value.
  Caveats:
  - the translated type has more values than the Lean one: a function that is `none` below
    `m` or `some` from `m` on has no Lean counterpart;
  - the rule is syntactic: a bound other than a field (`Fin (m + 1)`, `Fin (2 * m)`) keeps the
    plain erasure (so `Loop.node : (m : Nat) → (Fin (m + 1) → Loop) → Loop`, empty in Lean, is
    refused), and "on a recursive cycle" is decided on the constants of constructor types, so
    a codomain that merely mentions a type whose constructors mention the constructor's own
    type also gets the `Option`;
  - a proof field that forbids `m = 0` (`h : m > 0`) is erased, so such a type (empty in Lean)
    gets values in the language, as with every subtype;
  - in `#leanscript_to_term`, a child `f i` read on its own (not only through the answer of a
    recursive call) is taken apart with a branch for the unreachable `none`, which needs an
    `Inhabited` instance of `X` (refused otherwise); a recursive call on `f i` needs one of
    its answer type; only `Fin.foldl` iterates over the children (`Fin.foldr`, `List.finRange`,
    … are not translated);
  - `RoseF.size` and `RoseF.fan` are proved correct for every input
    (`TermTests/RoseVariantsProofs.lean`); other functions are only checked on examples.
- **Generic W-types** (`WT α β` with `β` not given) are refused (`β` is not a type);
  `WT Nat (fun _ => Nat)` has no value and is refused.
- **Proofs are erased, so a subtype is its carrier**: `Fin k` for a numeral `k ≥ 3` and
  `Fin n` for a non-numeral `n` are `nat`; `Fin 0`, `Fin 1`, `Fin 2` are refused, but a
  structure or subtype whose proof leaves it with 0, 1 or 2 values (`{x : Nat // x < 1}`) is
  not detected and becomes its carrier.
- **Quotients are read as their carrier, not typed.** `Quot r` (and `Quotient s`) is the type
  of its representatives (`Gen/Read.lean`, `quotCarrier?`): `QT.node : Quot (· % 2 = · % 2) →
  QT → QT` has a `nat` field. In `#leanscript_to_term`, `Quot.mk r a` is `a`, `Quot.lift f h q`
  (and `Quot.liftOn`, `Quot.rec`, `Quot.recOn`, `Quot.hrecOn`, `Quot.recOnSubsingleton`, the
  `Quotient` versions, `Quotient.lift₂`) is `f` on the representative, and an extern taking a
  quotient (or an `Array` of them) is given `Quot.mk r a`. `TermTests/QuotientProofs.lean`
  proves that every `QT` has a value in the language and that the translated `QT.odds` is
  correct on every representative. Caveats (`TermTests/QuotientTest.lean`):
  - the erased type has more values than the quotient (parity classes of `Nat` are `Nat`), and
    a quotient that leaves 0, 1 or 2 classes is not detected (`Quot (fun _ _ : Bool => True)`,
    one class, is `bool`); a carrier of no, one or two values is refused / `bool` as usual;
  - a call *returning* a quotient that does not compute to `Quot.mk` (`pick n` for an opaque
    `pick`) is refused: the language would need a representative (`Quot.out` is not
    computable);
  - an extern given an `Array` of quotients receives `Array.map (Quot.mk r) xs`, which the
    kernel does not reduce by `rfl`.
- **Types of no or one value** (`Empty`, `Unit`, `PUnit`, a structure with no field, …) and
  **types of two values other than `Bool`** (`Option Unit`, `BitVec 1`, `String.Pos` of a
  one-character string, `Thunk Bool`, …) have no type in the language, by design: they are
  refused, never erased. A type of two values is always `Ty.bool`: this is proved,
  `Ty.eq_bool_of_two_points` (`LeanScript/Three.lean`).
- **A recursive occurrence in the domain of a function** is refused (`Gen/Translate.lean`,
  `toFIR`).
- **Effects.** There is no type former for `IO`, tasks or promises.

## 2. Terms

- **Partial fixpoints, well-founded recursion, coinductive types** cannot be written: every
  loop is a fold (`nat_rec`, `array_foldl`, `data_rec`, `data_brec`).
- **Substitution theory is only semantic**: `LeanScript/TermSubst.lean` has renaming,
  weakening and substitution and proves they commute with evaluation, but not the syntactic
  laws (substitution composition, `rename` as a special `subst`).
- **No `DecidableEq`/`Repr` for `Term`**: `Term.extern` holds a Lean function.

## 3. The translator `#leanscript_to_term`

The supported fragment and the refusals are listed in the header of
`LeanScript/ToTerm.lean`; the refusals are pinned by `#guard_msgs` in
`TermTests/ToTermTest.lean`. Not supported yet:

- **Polymorphic definitions** (a parameter that is a type or an instance).
- **Recursion on a parameter that is not matched at the top of the body**, recursion that
  changes the other parameters (an accumulator), and recursion through a helper.  (A
  `mutual` group of functions, one per member of a block, is translated, also when members
  are held inside an `Array` or a function: `TermTests/MutualToTermTest.lean`.)
- **Two functions of a `mutual` group on the same member** of a block (one fold has one
  answer per member).
- **A field that holds members inside an `Array` or a function** can only be folded with
  `Array.foldl` (from `0` to its size), applied, or passed to a recursive call: `qs.size`,
  `qs.map`, `qs[i]` or rebuilding a value from it are refused.  A course-of-values recursion
  (`data_brec`) through such a field is refused.
- **`Thunk`** is not a type of the language at all (inside a block or not): a constructor
  with a `Thunk` field is refused by `leanscript_signature`.
- **Course-of-values recursion on `Nat`** (`fib (n + 2) = fib n + fib (n + 1)`): `Nat` is a
  leaf, so there is no `data_brec` for it; on a declared datatype, calls up to four levels
  down are translated to `data_brec`.
- **Patterns on numerals** other than `0` / `n + 1` (Lean compiles them to `dite` on
  equalities), and `if h : c` whose proof `h` is used.
- **Externs on non-leaf values**: a call of a Lean function is an extern only when its value
  arguments and its result are leaf types (or arrays of them); `List.length l` on a declared
  `List Nat` is refused (write the recursion instead).
- **Loops** (`for`, `while`, `do` notation in `Id`).
- **No proof that the translation is correct** in general: each test checks it on examples
  by `rfl`, and `ToTermTest.sumToT_run` proves it at every argument for one function.

## 4. Backend

- **There is no JavaScript backend or printer.**

## 5. Housekeeping

- `Scratch.lean` at the root of the project is not part of any library and imports modules
  that no longer exist.
- The extern catalogue (`LeanScript/LeanInitPureExterns*.lean`) is not used by the language.
