# What is not implemented yet

This list describes the project as it stands now: one grammar of types (`LeanScript/Ty.lean`,
`LeanScript/Decl.lean`), one grammar of terms (`LeanScript/Term.lean`), the generators
(`LeanScript/Signature.lean`, `LeanScript/GetCtor.lean`, `LeanScript/Gen/`) and the translator
`#leanscript_to_term` (`LeanScript/ToTerm.lean`). Each item names where to read more.

## 1. Types

- **Existentially typed fields.** A constructor with a field whose value is a type
  (`State : Type` in `Unfold`) is refused (`LeanScript/Gen/Read.lean`, `readCtors`). This
  was deferred on purpose.
- **Inductive families with indices** are refused (`readCtors`).
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
- **No substitution theory** (renaming, weakening, substitution lemmas) for `Term`.
- **No `DecidableEq`/`Repr` for `Term`**: `Term.extern` holds a Lean function.

## 3. The translator `#leanscript_to_term`

The supported fragment and the refusals are listed in the header of
`LeanScript/ToTerm.lean`; the refusals are pinned by `#guard_msgs` in
`TermTests/ToTermTest.lean`. Not supported yet:

- **Polymorphic definitions** (a parameter that is a type or an instance).
- **Recursion on a parameter that is not matched at the top of the body**, recursion that
  changes the other parameters (an accumulator), mutual recursion, recursion over a block of
  several members (`Rose`/`List Rose`), and recursion through a helper.
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
