module

/-!
# `#leanscript_to_term`: a Lean definition, as a `Term`

```lean
def addOne (n : Nat) : Nat := n + 1   -- with `add` declared in the signature

def addOne_term : Term sg [] (TyWf.prim .nat ⇒ TyWf.prim .nat) :=
  #leanscript_to_term addOne
```

`#leanscript_to_term e` reads the Lean definition `e` and builds the `LeanScript.Term`
that means the same thing.  It is a **term** elaborator, so the type it is checked
against says which signature and which context the term is written in: the expected type
is a `LeanScript.Term Sg Γ τ`, and `Sg` is the signature the translation resolves
top-level names against.

The signature can be named instead of read off the expected type, and then the type of
the translation does not have to be written at all:

```lean
def addOne_term' := #leanscript_to_term (sig := sg) addOne
```

With neither an expected type nor a `(sig := …)`, the empty signature and the empty
context are used.

## What may appear in a translated definition

| Lean | `Term` |
| :-- | :-- |
| `fun x => b`, `f a`, `let x := v; b` | `lam`, `ap`, `letE` |
| a literal of a terminal type | `bool_mk`, `nat_mk`, `int_mk`, `string_mk`, … |
| `if b then t else e` (`b : Bool`), `cond` | `bool_casesOn` |
| a constructor of a record-shaped type | `record_mk` |
| a constructor of a tagged union | `taggedUnion_mk` |
| a constructor of an enum | `enum_mk` |
| an array literal | `array_mk` |
| a constructor of `List` | `recTaggedUnion_mk` |
| `Thunk.mk (fun _ => e)`, `t.get` | `thunk_mk`, `thunk_force` |
| `match`, `X.casesOn`, a projection | `record_casesOn`, `taggedUnion_casesOn`, `enum_casesOn`, `bool_casesOn`, `recTaggedUnion_casesOn`, `nat_casesOn` |
| a `match` that leaves constructors out | `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault`, `recTaggedUnion_casesOnWithDefault` |
| `Nat.rec`, `List.rec` (non-dependent motive), a structural recursion Lean compiled through `Nat.brecOn` / `List.brecOn` | `nat_rec`, `recTaggedUnion_rec 0` — or `nat_casesOn` / `recTaggedUnion_casesOn`, when the branch does not use the value of the fold |
| a recursion on a `Nat` that descends `k + 1` steps (`fib`, the tribonacci numbers, …) | `nat_rec k` |
| a recursion on a **list** that descends `k + 1` constructors | *not read yet*: the node for it is `recTaggedUnion_rec k`, which `TyTests/RecUnionRecDepthTest.lean` writes out |
| `do` in `Id` — `Id.run`, `pure`, `>>=`, `<$>`, and `let mut` | the `let`s and applications it stands for |
| `for i in [:n] do …` in `Id`, over `Std.Legacy.Range` | `nat_rec`, folding the state of the loop |
| a name of the signature | `global` |

**A list and an array are different types here.**  `Array α` is `Ty.array`, the one
sequence the grammar has an introduction form for: it takes every element at once, so an
array literal translates and a non-literal array does not.  `List α` is the tree its
`LeanScriptTyWf` instance gives it — the recursive tagged union `nil | cons α self` — so
`[]` and `hd :: tl` are `recTaggedUnion_mk`, a `match` on a list is
`recTaggedUnion_casesOn` and `List.rec` is `recTaggedUnion_rec`.  A list therefore does
not have to be written out.

The two are not interchangeable, and neither `Array.toList` nor a `match` on an array has
a term.  Note also that `LeanScript.Ty.Den` gives a recursive tree no values, so a
translated list is outside the fragment `LeanScript.Term.eval` interprets
(`LeanScript.Term.NoRecMk`): it is checked by its type, not run.

## Which calls are allowed

A **constructor is inlinable**: an application of one is built in place, as the
`record_mk`, `taggedUnion_mk`, `enum_mk` or `array_mk` node it denotes.  So are
projections and anything marked `@[inline]`, `@[macro_inline]`, `@[always_inline]` or
`@[reducible]` (an `abbrev`): their definition is translated and cached, and the
translation is used at the call site.

Every **other** top-level function must be declared in the signature: it is translated
to `Term.global`, the reference the signature gives it.  A call of a function that is
neither inlinable nor declared is refused, naming the function — there is no third way
for a term to mention a top-level name.

The definition `#leanscript_to_term` is *applied to* is always unfolded: it is the thing
being translated.

## What is refused

* `partial` and `unsafe` definitions, and `opaque` constants and axioms: they have no
  total value to translate.
* well-founded recursion (`WellFounded.fix`, `Acc.rec`) and partial fixpoints
  (`Lean.Order.fix`).
* a recursion on a `Nat` that does **not** descend by a fixed number of steps: a call at
  `n / 2`, say.  A recursion that descends `k + 1` steps for some fixed `k` — `fib` reads
  its value at `n` and at `n + 1`, the hexanacci numbers at the six previous arguments —
  is translated as `nat_rec k`, and the depth is read off the compiled recursion: it is
  the smallest number of steps at which the *history* the `brecOn` hands the branch is
  fully read.  A recursion on a `List` still descends one step, and a structural
  recursion on any other type is still refused, since those are the only folds.
* a `for` loop that leaves early (`break`, `return`), or over a range that does not start
  at `0` or steps by more than `1`; and `do` in any monad other than `Id`, which is the
  only one that is not an effect.

## Which dispatch a `match` becomes

A `match` is translated by the shape of the type it takes apart and by **which
constructors it names**:

* it names them all, and no branch uses the value of a fold: the exhaustive dispatch,
  `enum_casesOn`, `taggedUnion_casesOn`, `record_casesOn`, `recTaggedUnion_casesOn`,
  `nat_casesOn`, `bool_casesOn`;
* it leaves constructors out (a wildcard, or fewer patterns than constructors): the
  partial dispatch, `enum_casesOnWithDefault`, `taggedUnion_casesOnWithDefault` or
  `recTaggedUnion_casesOnWithDefault`, whose default branch is the one the wildcard
  wrote — the dispatch is *not* expanded into one branch per constructor;
* it is the branch of a recursion whose body uses the value at the smaller argument: the
  fold, `nat_rec` or `recTaggedUnion_rec`.
* a dependent motive, a dependent function type, and any type with no
  `LeanScript.LeanScriptTyWf` instance (an existentially typed structure, for one, has
  no instance: see `LeanScript.Ty.Deriving`).

## The cache

Every closed definition that is inlined is translated **once**: the translation is
stored as a function of the context, `fun Γ => …`, which is what makes one translation
usable at every depth it is called from.

Two definitions that translate to the *same shape* share one entry: the produced tree is
hashed (`Lean.Expr.hash`) and compared against the entries of that hash, and an equal
one is returned as the **same object**, so the duplicate is not built twice and the two
call sites point at one tree in memory.  `#leanscript_to_term_cache_stats` reports how
many entries, cache hits and shape merges there have been, and
`#leanscript_to_term_cache_clear` empties the cache.

`TyTests/ToTermTest.lean` runs all of this: it translates about twenty definitions and
checks, by the kernel, that `LeanScript.Term.eval` gives each translation the value the
Lean definition has — except for the lists, which have no values and are checked by their
types — and it pins what the translation refuses.

The translation itself is split across the modules of this directory:
`LeanScript.ToTerm.ObjectExpr` (the expressions of the object language),
`LeanScript.ToTerm.TyView` (a tree as a view, and the tree of a Lean type),
`LeanScript.ToTerm.Ctx` (where a translation stands, and the signature),
`LeanScript.ToTerm.Cache` (the cache, and what may be translated at all),
`LeanScript.ToTerm.Pieces` (literals, and small pieces of the object language),
`LeanScript.ToTerm.Match` (a dispatch Lean compiled with a default),
`LeanScript.ToTerm.Brec` (the compiled form of a structural recursion),
`LeanScript.ToTerm.Trans` (the translation proper) and
`LeanScript.ToTerm.Elab` (the elaborator, which is what a user imports).
-/
