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
- **W-types (`WT α β`, `sup (a : α) (f : β a → WT α β)`)** are read, but no instance has a
  type: a Lean W-type gets its finite values from an *empty* `β a` (`Fin 0`), and after
  erasure every function domain has values, so the erased type (`μX. Nat × (Nat → X)` for
  `WT Nat Fin`) has no grounding order and is refused. A generic `WT α β` is refused too
  (`β` is not a type). Reading `Fin n → X` as `Array X` would make `WT Nat Fin` a rose tree;
  this was not done, because `Chunk.data : Fin n → Nat` is to be a function.
- **Proofs are erased, so a subtype is its carrier**: `Fin k` for a numeral `k ≥ 3` and
  `Fin n` for a non-numeral `n` are `nat`; `Fin 0`, `Fin 1`, `Fin 2` are refused, but a
  structure or subtype whose proof leaves it with 0, 1 or 2 values (`{x : Nat // x < 1}`) is
  not detected and becomes its carrier.
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
