# What is not implemented yet

This list describes the project as it stands now: one grammar of types (`LeanScript/Ty/Syntax/Ty.lean`,
`LeanScript/Ty/Syntax/Decl.lean`), one grammar of terms (`LeanScript/Term/Syntax/Term.lean`), the generators
(`LeanScript/GenElab/Signature.lean`, `LeanScript/GenElab/GetCtor.lean`, `LeanScript/GenElab/`) and the translator
`#leanscript_to_term` (`LeanScript/TermElab/ToTerm.lean`). Each item names where to read more.

## 1. Types

- **Existentially typed fields.** A constructor with a field whose value is a type
  (`State : Type` in `Unfold`) is refused (`LeanScript/GenElab/Read.lean`, `readCtors`). This
  was deferred on purpose.
- **Inductive families have their indices erased, not typed.** `Vec α n` is the datatype
  `Vec α` of every length (`Gen/Read.lean`, `normType`), and a constructor field that only
  names an index (`n` in `Vec.cons {n} a v`) is dropped (`erasedFields`): `Vec α` is a linked
  list, and `Matrix` (`rows`, `cols`, `cells : Vec (Vec Nat cols) rows`) a record of two
  numbers and a list of lists. `TermTests/Datatypes/IndexedFamilyProofs.lean` proves, for every input,
  that the translations of `Vec.sum`, `Vec.double`, `Vec.sumRows` and `Matrix.size` compute
  what the Lean functions compute, that the encoding of vectors is injective (the length is
  recovered), and the value counts behind the refusals and caveats below; other translated
  functions over families are only checked on samples. Caveats
  (`TermTests/Datatypes/IndexedFamilyTest.lean`):
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
  instances, so none of them is a block member. `GenElab/Read/Nest.lean` (`typeFamilySteps`,
  `ensureElem`, `canonIndex`) generates, once, the Lean inductive
  `Nest.Elem α := leaf α | node (Nest.Elem α) (Nest.Elem α)` (one `node` per recursive index;
  a structure index such as `α × α` is flattened into its fields), and reads `Nest τ` as the
  datatype `Nest (Nest.Elem B)`, `B` being `τ` with the recursive indices peeled off
  (`Nest (Nat × Nat)` and `Nest Nat` are the same datatype). A value at depth `k` is put in
  `Nest.Elem B` (`injectElem`: `(2, 3)` is `node (leaf 2) (leaf 3)`). A function generic in
  the index (`Nest.length`) is translated at the index the program declares the family at,
  or at `#leanscript_to_term f (α := T)`. `TermTests/Datatypes/NestProofs.lean` proves that the encoding
  is injective at every index and that the translated `Nest.length` is correct on every
  value. Caveats (`TermTests/Datatypes/NestTest.lean`):
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
  (`TermTests/ToTerm/DependentFieldTest.lean`.)
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
    (`TermTests/Datatypes/RoseVariantsProofs.lean`); other functions are only checked on examples.
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
  quotient (or an `Array` of them) is given `Quot.mk r a`. `TermTests/Datatypes/QuotientProofs.lean`
  proves that every `QT` has a value in the language and that the translated `QT.odds` is
  correct on every representative. Caveats (`TermTests/Datatypes/QuotientTest.lean`):
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
  `Ty.eq_bool_of_two_points` (`LeanScript/Ty/Den/Three.lean`).
- **A recursive occurrence in the domain of a function** is refused (`Gen/Translate.lean`,
  `toFIR`).
- **Effects.** There is no type former for `IO`, tasks or promises.

## 2. Terms

- **Partial fixpoints, well-founded recursion, coinductive types** cannot be written: every
  loop is a fold (`nat_rec`, `array_foldl`, `data_rec`, `data_brec`).
- **No substitution**: the grammar of normal forms has renaming and weakening
  (`LeanScript/Term/Rename/Basic.lean`, `LeanScript/Term/Rename/Weaken.lean`, with `Term.rename_eval`), but
  no substitution: substituting a value can create a redex, which only the normaliser computes.
- **The normaliser is not verified**: `LeanScript/TermElab/Anf.lean` normalises at elaboration
  time; there is no proof that it preserves meaning (the translated programs are checked by
  their own `rfl` runs and proofs in `TermTests/`).
- **Usage annotations are sound, not checked against the uses**: the elaborators write `ω`
  (`many`) everywhere; `Term.dce` recomputes exact annotations and removes dead bindings, but
  nothing requires a term to carry exact ones (a binder annotated `0` cannot be referenced,
  which the types do enforce).
- **The optimiser is small**: `Term.optimize` (`LeanScript/Term/Optimize/Basic.lean`, proved to
  preserve the value) only does copy propagation of an unknown of the same level, returns a
  shared neutral answer directly, drops a `record_casesOn` whose fields are unused, and runs
  `Term.dce`.  Every rewrite is skipped when it would change the level index of the statement.
  There is no common-subexpression elimination (for example of repeated `record_casesOn` on the
  same neutral record), no inlining of a `share` used once into a neutral expression (that is a
  substitution, see above), and it does not look inside pure expressions.
- **No pretty printer for terms**: terms print as constructor applications.
- **No `DecidableEq`/`Repr` for `Term`**: an extern is now an entry of the catalogue
  `LeanInitPureExtern σs τ` (data, no Lean function), but the catalogue itself has no derived
  `DecidableEq`: its signature indices are written over an abstract grammar of types (`MyTy`
  with `Coe`/`CoeOut` instances), which the deriving handler does not support.

## 3. The translator `#leanscript_to_term`

The supported fragment and the refusals are listed in the header of
`LeanScript/TermElab/ToTerm.lean`; the refusals are pinned by `#guard_msgs` in
`TermTests/ToTerm/ToTermTest.lean`. Not supported yet:

- **Polymorphic definitions** (a parameter that is a type or an instance).
- **Recursion on a parameter that is not matched at the top of the body**, and mutual
  recursion through a helper (a helper that calls back the function being translated).
  (Recursion that changes the other parameters, an accumulator, and calls of non-recursive
  or recursive helpers are translated: `TermTests/ToTerm/TcoTest.lean`.)
- **`for` loops** only over a `Std.Legacy.Range` (`[a:b]`, `[a:b:s]`) in `Id`; other
  collections and other monads are refused.  (A
  `mutual` group of functions, one per member of a block, is translated, also when members
  are held inside an `Array` or a function: `TermTests/ToTerm/MutualToTermTest.lean`.)
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
  equalities), and `if h : c` whose proof `h` is used by anything but an extern (an extern
  that takes a proof decides its proposition again when the term runs,
  `TermTests/Extern/CondExternTest.lean`).  A proof whose proposition speaks about a value that is
  not an argument of the extern, or is not decidable, is refused.
- **Externs on non-leaf values**: a call of a Lean function is an extern only when its value
  arguments and its result are leaf types (or arrays of them); `List.length l` on a declared
  `List Nat` is refused (write the recursion instead).
- **Loops**: a `for` over a range and a `while` in `Id` are translated; a `while` only when
  its termination is read off its syntax (a `Nat` variable moved towards a bound by a
  literal step, `TermTests/ToTerm/WhileTest.lean`); any other `while`, `repeat`, and loops in other
  monads are refused.
- **No proof that the translation is correct** in general: each test checks it on examples
  by `rfl`, and `ToTermTest.sumToT_run` proves it at every argument for one function.

## 4. Backend (`JsTerm/`, `leanscript`)

- **Declared datatypes are not converted to JavaScript**: a term using `data_in`,
  `data_out`, `data_rec` or `data_brec` is refused by `MoreJs.termToJs`
  (`JsTerm/FromTerm.lean`), so every function over `List`, a user inductive, … is listed
  under "not translated" in the outputs.  (The layouts exist in `JsTerm.lowerTy`: tagged
  arrays, enums; only the recursors are missing.)
- **Some externs have no JavaScript implementation**: they are emitted as a runtime helper
  that throws (`MoreJs.stubHelper`, `JsTerm/Extern.lean`).  `leanscript --check` finds
  them (a check answers "threw: … has no JavaScript implementation yet").
- `String` ordering (`lean_string_dec_lt`) is JavaScript's `<`, which compares UTF-16 code
  units, not code points as Lean does: the two differ on strings mixing characters above
  `U+FFFF` with characters in `U+E000`–`U+FFFF`.
- A top-level function whose body is not a chain of lambdas (e.g. `fun m => nat_rec …`
  returning a function) is exported curried: `ack2(m)(n)`.
- `leanscript` only reads the definitions `LeanScript.Term` supports: non-recursive and
  structurally recursive ones.  Well-founded recursion and `mutual` blocks are refused for now
  (the open-definition machinery in `LeanScriptCli/Frontend.lean` is kept but unused, and
  `LeanScriptCli/RecCalls.lean_` is set aside), as are `partial` definitions, `IO`/`ST`
  actions, definitions with errors and constants whose value is not computable; each is
  listed with the reason in every output file.
- `Array Bool` and `Array Char` are always generic JavaScript arrays (the `Uint8Array` /
  `Uint32Array` representations are commented out in `JsTerm/Config.lean`).
- The optimiser does not inline a join point jumped to only once when its body is not
  trivial, and does not share computations across closure / loop-body boundaries.
- The translator reports "invalid scope" for `ScalarRepl.test6` (a private structure
  passed through a structural recursion); not investigated.

## 5. Housekeeping

- `Scratch.lean` at the root of the project is not part of any library and imports modules
  that no longer exist.
- The extern catalogue (`LeanScript/LeanInitPureExterns*.lean`) is not used by the language.
