This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# LeanScript

A typed object language embedded in Lean, with one grammar of types and one grammar of
terms:

* **types** (`Ty ks`): closed types whose recursive datatypes are *declared once*, in a
  datatype signature (`DSig ks`), and named (`Ty.data r`).  Every type has at least two
  values (`Ty.den_exists_ne`); a type of no or one value (`Unit`, `Empty`, …) cannot be
  written, and a type of two values is always `Ty.bool` (a union needs a constructor with
  fields, `BitVec 1` is refused, …): every type other than `Ty.bool` has three different
  values (`Ty.den_exists_three`, `Ty.eq_bool_of_two_points`);
* **terms** (`Term Δ Γ τ`): a direct-style grammar that terminates by construction (every
  loop is a fold: `nat_rec`, `array_foldl`, `data_rec`, `data_brec`), with a total,
  structural evaluator `Term.eval` into Lean values;
* **generators**: `leanscript_signature` declares the datatypes of a program,
  `#leanscript_get_ty` / `#leanscript_get_ctor` / `#leanscript_get_cases` give the type,
  the constructors and the case analysis of a Lean type, and `#leanscript_to_term`
  translates a Lean definition into a `Term`.

Build everything, tests included, with `lake build`; run the compiled tests (the checks that
are too slow for the kernel) with `lake test`.  The project depends on Mathlib (`v4.34.0`,
with Batteries and Aesop); `LeanScript/Term/Syntax/UsageAlgebra.lean` takes the algebra of usages
(commutative monoid, linear order) from it.

## From Lean to JavaScript: `leanscript`

```
lake build leanscript
.lake/build/bin/leanscript Tests/SnapshotsMy/TcoAck.lean     # or a module name: SnapshotsMy.TcoAck
.lake/build/bin/leanscript --check FILE.lean                 # also differential checks
scripts/leanscript-snapshots.sh               # Tests/SnapshotsMy + Tests/SnapshotsPBOPure (files with a public non-recursive or structurally recursive function), checks run with node
```

For each public definition of the file that `LeanScript.Term` supports — non-recursive or
structurally recursive (well-founded and `mutual` definitions are refused for now, with the
reason) — `leanscript` reads its `Expr` (not LCNF or IR, which have lost the types),
translates it to a `Term` (`#leanscript_to_term`), optimises it (`Term.optimizeN`, which
preserves `Term.eval`: `Term.optimizeN_eval`), converts it to the simply typed JavaScript
grammar `JsTerm` twice, once per preset (`MoreJs.termToJs`: `pbo` uses `number` for the integer
types and JavaScript arrays for `List`, `faithful` uses `BigInt` and tagged cons cells for
`List`), and prints it with `LanguageJavascriptMini`.  Next to
`FILE.lean` it writes `FILE-Term-unoptimized.txt`, `FILE-Term-optimized.txt`,
`FILE-pbo.js` and `FILE-faithful.js` (one
`import { … } from "<relative path>/runtime.js"` of the runtime functions the code calls, then the constants of the module, then one `export const f = (x, y) => …` per function: a
chain of lambdas becomes one arrow with several parameters, and the components of the Lean
name are joined by `$`, `ArrayTest.test1` is `ArrayTest$test1`); with `--check` also
`FILE-pbo.check.mjs` and `FILE-faithful.check.mjs`, which call every exported function on
sample arguments and compare the answers with the ones Lean computes.  Every output lists
the definitions that were not translated, with the reason; the JavaScript outputs also start
with their configuration.

`JsTerm` is simply typed (`JsTy`: the leaves `JsTerminalTy` — `bool`, `bigint_nat`, `uint53`,
`bigint_int`, `int53`, bit vectors, the fixed-width integers, `float`, `float32`, `string`, … —
generic and typed arrays, lists, functions, records, unions, enums, thunks) and intrinsically
typed (`JsExpr C M τ`, `JsBlock C M J k`); its variables are de Bruijn indices into three
separate contexts: the constants `C`, the mutable variables `M` and the join points `J`.  It
has no generic arithmetic operators: every extern at every representation of its types is an
operation of its own, named `type__extern` (`lean_nat_div` is `bigint_nat__lean_nat_div` on
`BigInt`s and `uint53__lean_nat_div` on `number`s), either **imported** from `runtime.js`
(`JsOpImported`: the function of `runtime.js` named as the constructor) or **inlined** as one
JavaScript operator or conversion (`JsOpInlinable`: `bigint_nat__lean_nat_land` is `a & b`),
both in `JsTerm/Ops/` and indexed by their effects (`Effectfulness`: `pure`, or
`effectful` for the `_mutable` array updates; `MayThrow`: an operation on a `number`
representation of an unbounded type throws a `RangeError` when its result does not fit).
The operations (`JsTerm/Ops/Imported.lean`, `JsTerm/Ops/Inlinable.lean`, `JsTerm/Ops/Template.lean`) and the lookup
(`JsTerm/Ops/Cands/*.lean`, `JsTerm/Ops/Lookup.lean`) are generated by
`scripts/gen_js_ops.py` from the catalogue of externs and `runtime.js`; the script fails when
an extern has neither form at some representation (`--report` lists them: none today).  The
types say which conversions are needed, so no `Number(i)`/`BigInt(i)` is written where the
representations already agree.  A literal that does not fit in its representation (a `Nat`
above `2^53 - 1` as a `uint53`) is an error: `leanscript` reports it and exits with a failure.

The generated code contains no runtime definitions: it imports the functions it calls from
`runtime.js` (`--runtime FILE` says where it is, default `runtime.js` of the project; the
import path is relative to the output file; `leanscript` fails if the runtime does not export
one of them).  Every extern has an operation at every representation, so an extern without
one at the types of a call is an error of the conversion.  Functions are uncurried: a Lean
`A → B → C` is a JavaScript function of two parameters, a lambda takes all the parameters of
its type and a call passes them all (a partial application is a closure).  The `JsTerm` of a function is written out as
the conversion builds it: nothing rewrites it (`JsTerm` is only the typed shape of the printed
JavaScript and its link to `runtime.js`; every optimisation is done on `Term`, by
`Term.optimize`, before the conversion — see `proposals/NoJsTermOptimizations.md`).  Array
updates are in place when a static ownership analysis of the optimised `Term`
(`LeanScript/Term/Ownership/`, below) says nothing else can still see the array; otherwise they
are the copying `…_immutable` operations.  A constant value is written where it is used.

**Functional but in place, statically.**  There are no reference counts at run time.  Instead
`LeanScript/Term/Ownership/Basic.lean` counts the occurrences of every variable (with the ones
that escape, the ones in a loop body and the ones in a closure or delay), and
`LeanScript/Term/Ownership/Walk.lean` walks a function in the order it runs and tracks which
arrays are *owned* (built by the function itself, or a parameter its caller gave up) and not
used later: an update (`push`, `pop`, `set`, `swap`, `fset`, `fswap`) of such an array is done
in place, a `set!`/`swapIfInBounds` of an array that is still used copies first, and the
accumulator of a loop (`nat_rec`, `foldl`) is borrowed, owned, or copied once before the loop
when that saves a copy per iteration.  Every translated function gets **versions**
(`OwnedTerm`, `Own.Version`, `ClosedTerm.withOwnership`): the first borrows every parameter
(the plain export, safe for any caller); when owning an array-holding parameter saves copies,
an extra export owns those parameters (`f$$mut_0_2` owns parameters 0 and 2), and for two or
three such parameters one version owns each alone.  The conversion (`termToJs … owned`)
generates each version from the same `Term`; the doc comment of each version says what it
owns and its static cost, and `FILE-Term-optimized.txt` lists them (`-- version …`).  The node
checks run every version and, for functions with array parameters, call the plain export twice
on the same array to check it is not mutated.  Inside a function the same analysis covers:
**local functions** that are not inlined (`Own.lamPlan`): each gets one JavaScript constant per
way its calls give up their array arguments (`k` borrows, `k_mut` owns), each call calls the
version owning the most arguments its caller gives up, and the answer of a call is owned when
every path of that version answers a new array; **owning closures** (`Own.AccMode.ownFn`): a
loop whose accumulator is a function (a structural recursion with an array accumulator, such as
`fill : Nat → Array Nat → Array Nat`) makes every closure it builds own its array argument,
and every call of one gives up its argument or copies it once (`[...a]`); **folds over
declared datatypes** (`Own.dataRecOwns`): when every branch answers a new array, the answers at
the holes of a layer are owned, so `(toArray t).push h` pushes in place; and conditionals
(`c ? push(a, x) : a` consumes `a` in either arm).  `Tests/SnapshotsMy/LocalFnInPlace.lean` shows
these, and `Tests/SnapshotsMy/OwnershipAliasing.lean` programs where an update in place would be
visible (their checks compare every answer with Lean's).  This analysis is not proved (it only decides
which array operations are in place); `Term.eval` and the proofs about `Term.optimize` are
unaffected.  Join points are de Bruijn indexed in `JsTerm` (`JsBlock.join`,
`JsBlock.jump`) and printed as labelled blocks (`let x$1; j$2: { …; x$1 = e; break j$2; }`).  In the `Term`
files a lazy value `Unit → τ` is printed `(Lazy τ)`.

In the tool a `List α` is the built-in list `Ty.list α` (an immutable JavaScript array), not a
datatype (the tool has no signature to declare it in): a literal `[a, b]` is a list literal,
and `xs ++ ys` is the extern `lean_list_append` (`List.append`).

**Array functions written in Lean.**  `Array.append`, `Array.map`, `Array.filter`,
`Array.flatMap`, `Array.flatten`, `Array.reverse`, `Array.extract` (and so `take`/`drop`),
`Array.any`/`all`/`contains`/`find?`/`findIdx?`/`idxOf?`, `Array.eraseIdx!`/`insertIdx!` (and
their `IfInBounds` versions), `Array.qsort`, `Array.foldr`, `Array.zipWith`/`zip`, `Array.back?`,
`Array.countP` and `List.append` are not `@[extern]` in Lean, but they are entries of the
catalogue of externs (`ArrayStdExtern`,
`LeanScript/LeanInitPureExterns/ArrayStdFunctionsNonExternButBigEnoughToLoseInformation.lean`),
whose meaning is the Lean function itself (`LeanScript/Term/Extern/Eval/ArrayStd.lean`): without
an entry the elaborator would unfold them into folds (`xs ++ ys` into
`array_foldl ys xs (fun e acc => lean_array_push acc e)`), and the backend could no longer tell
which function was called.  With the entry, the JavaScript is the function of `runtime.js`
(`array__lean_array_map`, …) and appends are optimised in the conversion to `JsTerm`:

* an append of arrays (or of lists at `list=array`) is one array literal in which the literal
  operands and the appends already written as literals are spliced: `#["a"] ++ (xs ++ #["b"])`
  is `["a", ...xs, "b"]`, whatever the nesting (an append onto an array nothing else refers to
  is otherwise done in place, `array__lean_array_append_mutable`);
* an append of cons-cell lists (`list=tagged`) is built from its end, as `a ++ (b ++ (c ++ d))`
  (the last operand is shared, not copied; `List.append` is associative), a literal operand is
  its cells put in front of the rest, and any other operand is copied in front of the rest by
  `consList__lean_list_append` (a loop, so a long list does not overflow the stack).  Since the
  cons-cell layout is chosen by the code generator, this function is **written into the
  generated module** (not exported, only when the module calls it; `JsTerm/Lower/LocalHelpers.lean`)
  instead of imported from `runtime.js`; `runtime.js` keeps a copy of the same name for the
  operation tables, and `lake exe tests` checks that the two agree.  There is no destructive
  (in-place) version of it: the ownership analysis tracks arrays only, not the spines of lists,
  and in the snapshots every non-literal operand is a parameter, which the caller may still
  hold;
* an array literal bound by a `let` and used once (not under a `fun`) is substituted, so that it
  can be spliced; an argument of an extern that another argument also computes (the array of
  `(xs.map f).filter p`, whose default bound is `(xs.map f).size`) is bound once.

`Tests/SnapshotsPBOPure/AssocArrayAppend.lean` (compare with
`Tests/SnapshotsPBOPure/legacy-backend/AssocArrayAppend.js`) and
`Tests/SnapshotsMy/ArrayStdFunctions.lean` show them.

How a `List` is laid out in JavaScript is the knob `JsConfig.listRepr` (`MoreJs.ListRepr`,
`JsTerm/Ty/Config.lean`; spelled `list=tagged` or `list=array` in the configuration line of
every output):

* `taggedUnion` (the default, preset `faithful`): cons cells, `[]` is `{ tag: 0 }` and
  `x :: xs` is `{ tag: 1, _1: x, _2: xs }`: the prelude object type `JsTy.consList α`
  (`obj consList [α]`, one declaration for every element type).  A list literal is its cells.
  The externs over lists (`Array.toList`, `List.toArray`, …) are written for arrays: their list
  arguments and results are converted (`consList__to_array`, `consList__of_array`, in
  `runtime.js`);
* `stdListToJsArray` (preset `pbo`): an immutable JavaScript array (`JsTy.list`), as above.

Only the standard library's `List` follows the knob: a user's list-like inductive
(`inductive MyList | nil | cons (h : α) (t : MyList α)`) is a datatype, a tagged union, in both
(`MoreJs.lowerTy_data_listRepr`).  `Tests/SnapshotsMy/ListRepr.lean` shows both layouts.  A `Float.Model` (`Float32.Model`) is the
`number` of the float it models.

The optimiser (`LeanScript/Term/Optimize/Basic.lean`, `Cse.lean`, `Atom.lean`) does constant
folding, copy propagation, dead-code elimination, common subexpression elimination of pure
computations (`let x := f a; … let y := f a; …` computes `f a` once), an `if` whose branches
are the same atom, inlining of a join point whose body is trivial (`ret a`, an atom), reuse of
the fields of a record already taken apart (a second `record_casesOn` of the same variable, or
of a record rebuilt from known fields, reads the fields bound the first time:
`LeanScript/Term/Optimize/Fields.lean`, `FieldsWalk.lean`, `Term.widenFields`,
`Term.reuseFields`), and dead-code elimination re-annotates the fields of every case analysis
with their counted usages, so an unused field is not taken apart
(`LeanScript/Term/Optimize/Reannot.lean`, `Term.reannotFields`);
`Term.optimize_eval` proves it does not change `Term.eval`, and `Term.numCalls_optimize` that it never increases the number of calls.
When dropping a repeated `record_casesOn` would change the level of its body, the optimiser keeps
the case analysis but renames its fields to the ones already known (`Term.reuseRecord`,
`FieldVars.toRenKeep`), so a record is not taken apart twice under different names.

The printer (`JsTerm/Print/Mini/`) only chooses how to spell what the `JsTerm` says: it writes
`if` statements as short as it can (no empty `else`, `if (x.tag !== 0)` for an empty `then`, no
`else` after a `return`, `c ? a : b` for returns of names and literals), arms of a union's case
analysis that are all the same once, without a test, a join point assigned once as a `const`, a
field read once, outside loops and closures, in place (`p._1`), and an arrow whose body is one
`return` as `(x) => e`.  `leanscript --help` lists the options.

**Object types are nominal** (`proposals/TypedDataProposals3.md`, proposals P, Q, R and S).  Every
tagged object is `JsTy.obj id args`, a name and arguments, looked up in the signature `JsSig` of
the function (a parameter of the grammar: `JsExpr S C M τ`, `JsBlock S C M J k`): a record is
the anonymous declaration `record n` of its number of fields, a structural union the anonymous
declaration `union arities` of the numbers of fields of its constructors (so `Option Nat` and
`Option String` share `union [0, 1]`, at different arguments), the built-in list at the tagged
layout the prelude declaration `consList` (`obj consList [α]`), and a declared datatype its
stable number (`decl i`, `refIndex`: the same whatever scope names it), whose row in `JsSig` is
its unfolded body.  The four forms that build and take objects apart (`record_mk`, `union_mk`,
`destructure`, `unionCases`) are indexed by `S.fieldsOf id args` / `S.ctorsOf id args`; the casts
`fold i` / `unfold i` go one layer into and out of a declared datatype (nothing at run time).
Type equality is syntactic.  So functions over the user's recursive datatypes
(`leanscript_signature`) are converted: `data_in`/`data_out` are the casts, and a fold
(`data_rec`, `data_brec` of depth `0`) is one local function per member of the block, mutually
recursive (`JsBlock.funs`), each rebuilding one layer with the answers at its holes and running
the member's branch on it (`JsTerm/Lower/DataRec.lean`; `Tests/SnapshotsMy/RecData.lean`).

*Canonical layout ids* (proposal R, `JsTerm/Ty/Canon.lean`): before a function is converted, the
table of its datatypes is minimised by partition refinement (`MoreJs.canonDecls`), so datatypes
whose layouts are equal as infinite trees (`MyList Nat` and a `Stack` of the same constructors,
two mutually recursive trees of one shape) get one object id.  The classes are checked to be a
bisimulation (`MoreJs.isBisim`), and `MoreJs.canonDecls_sound` proves that a datatype and its
canonical datatype unfold to the same layout at every depth (`MoreJs.JsTy.unfoldDecls`).

*The representation is part of the identity* (proposal S): a union is `obj (union arities r)
args`, `r` a `MoreJs.JsRepr` — `cells` (every constructor an object, the default) or
`smallIntNullary` (a constructor without fields is the number of its position, `0` instead of
`{ tag: 0 }`, and is tested by `s === 0`; a constructor with fields is still `{ tag: i, … }`,
tested by `s.tag === i`).  The knob `JsConfig.nullaryRepr` (`leanscript --nullary=int`) chooses
`smallIntNullary` for every union that has constructors with and without fields
(`JsConfig.unionRepr`: `Option`, list-like and tree-like datatypes); the standard library's cons
cells keep their cells (`runtime.js` reads them).  Two representations are two types: where an
extern of the catalogue answers (or takes) a union, the value is converted explicitly
(`JsListOp.nullaryToInt` / `nullaryToCells`, `obj__nullary_to_int` / `obj__nullary_to_cells` in
`runtime.js`).  The default is `cells`, so the snapshots of the presets are unchanged; `lake test`
runs `leanscript --nullary=int --check` on `RecData` and `ListRepr` and the checks against Lean
with node.

Not done: recovering type parameters of declared datatypes by anti-unification (a declared
datatype is `obj (decl i) []`; the JavaScript is the same either way), the other representations
and gains listed in the proposal, and course-of-values folds of depth `1` or more.

| path | what it holds |
| :-- | :-- |
| `JsTerm/Ty/` | the types of `JsTerm` (`JsTerm/Ty.lean` imports them all): `Config.lean` (`MoreJs.JsConfig`: how each leaf type is represented, a `number` or a `BigInt`, typed or generic arrays; presets `faithful` (default) and `pbo`, command-line knobs), `Defs.lean` (the leaves `JsTerminalTy` — `uint53`: a `number` standing for a `Nat`; `bigint_nat`: a `BigInt`; … — and `JsTy`: arrays, typed arrays, lists, functions, enums, thunks, and the nominal object types `obj id args` — records `{ _1: …, _2: … }`, unions `{ tag: i, _1: … }`, the prelude `consList`, declared datatypes — with the signature `JsSig` that gives their layouts), `DecEq.lean` (decidable equality of `JsTy`), `Basic.lean` (names and renderings of the types, the layouts `JsNatTy` and `JsArrayLayout`), `Lower.lean` (`lowerScalarPrim`/`lowerArrayPrim`/`lowerTy`, the representation of a union `JsConfig.unionRepr`), `Canon.lean` (canonical layout ids of datatypes, `canonDecls`, and their soundness `canonDecls_sound`) |
| `JsTerm/Ops/` | the typed operations (`type__extern`; `JsTerm/Ops.lean` imports them all): `Basic.lean` (their indices `Effectfulness`, `MayThrow`, the `JsInline` templates), and, generated by `scripts/gen_js_ops.py`, `Imported.lean` (the ones implemented by `runtime.js`, `JsOpImported`) `Inlinable.lean` (the ones written inline, `JsOpInlinable`) and `Template.lean` (their JavaScript, `JsOpInlinable.template`); `Op.lean` (`JsOp`, either of them), and the operation of an extern at given types (`JsOp.lookup`, generated): its candidates by group of externs in `Cands/` (`Nat`, `UInt`, `SInt`, `Float`, `String`, `Misc`) and `Lookup.lean` |
| `JsTerm/Syntax/` | the JavaScript grammar (`JsTerm/Syntax.lean` imports it all): `NumberLit.lean` (`number` literals), `Basic.lean` (the grammar, intrinsically typed with de Bruijn indices — constants, mutable variables, join points: `JsExpr`, `JsBlock`, `JsFun`, `JsModule`, over a signature `JsSig`), `Vars.lean` with `Vars/` (`Rename.lean`: renaming and weakening of the variables; `Occs.lean`: their occurrences), `Pretty.lean` (a readable dump of the grammar, used by the tests; the tool no longer writes it to a file) |
| `JsTerm/Lower/` | from `Term` to `JsTerm` (`JsTerm/Lower.lean` imports it all): `Extern.lean` (an extern call as its typed operation, `lowerExtern`; an error when there is none), `Basic.lean` (the support of the conversion: literals, `ConvM`, casts, builders, the signature `jsSigOf`), `Tail.lean` (returns as loop assignments or jumps), `DataRec.lean` (the folds of declared datatypes as mutually recursive local functions), `FromTerm.lean` (`MoreJs.termToJs`: a closed `Term` to a `JsFun` — loops for `nat_rec`/`array_foldl`, `if`/`switch` for branches, closures for lambdas), `Module.lean` (the imports of a module, `mkModule`) |
| `JsTerm/Print/` | printing (`JsTerm/Print.lean` imports it all): `Mini.lean` (`JsModule.toJs`: through the `LanguageJavascriptMini` AST to source text) with `Mini/` (`Basic.lean`: helpers, the printer's state, early ends of iterations; `Block.lean`: expressions and blocks) |
| `runtime.js` | the runtime the generated code imports: one function per imported operation, of the same name, each with JSDoc `@param`/`@returns` tags giving the JavaScript type and the `JsTy` of its arguments and result (written by `scripts/annotate_runtime.py`) |
| `LeanScriptCli/` | the executable: `Frontend.lean` (elaborating the file, choosing the definitions, translating, open definitions of recursive functions), `RecCalls.lean` (binding the recursive functions of an open definition in its JavaScript, direct calls), `Check.lean` (`--check`), `Main.lean` |

## Layout

| path | what it holds |
| :-- | :-- |
| `LeanScript/Ty/Syntax/LeanPrimTy.lean`, `LeanScript/Ty/Syntax/LeanPrimTyCovariant.lean`, `LeanScript/Ty/Syntax/EnumSchema.lean` | the leaf types, the covariant leaf type formers (arrays, thunks, lazy values; used by the extern catalogue) and the payload of an enum |
| `LeanScript/Ty/Syntax/Ty.lean` | `Ref`, `BRef`, the mutual `Ty`/`Fields`/`Ctor`/`Ctors`, `UnionShape`, with `DecidableEq`, `BEq`, `LawfulBEq`, `Repr`; renaming `Ty.map` and its laws `Ty.map_id`, `Ty.map_map` |
| `LeanScript/Ty/Syntax/Decl.lean` | declarations of blocks of datatypes (`Fld`, `Decl`, `Mems`, `DSig`) and `unfold` |
| `LeanScript/Ty/Den/Container.lean`, `LeanScript/Ty/Den/Basic.lean` | what a type denotes: indexed W-types for the declared blocks, `Ty.den`, `Ty.Den`, `DSig.dataIn`/`dataOut`/`dataRec` |
| `LeanScript/Ty/Den/Facts.lean`, `LeanScript/Ty/Den/Brec.lean` | `dataIn`/`dataOut` are inverse; course-of-values recursion `DSig.dataBrec` and its computation rule |
| `LeanScript/Ty/Den/Two.lean` | every type has two values that a Boolean test tells apart |
| `LeanScript/Ty/Den/Three.lean` | every type other than `bool` has three values that a test tells apart: two points are only ever `bool` |
| `LeanScript/Term/Syntax/Ctx.lean`, `LeanScript/Term/Syntax/Usage.lean`, `LeanScript/Term/Syntax/Term.lean`, `LeanScript/Term/Semantics/Eval.lean` | the grammar of normal-form terms: two contexts (known values `Φ`, unknowns `Γ`), levels (`Lvl`) that make the open/closed flag of every expression and body exact, usages `Usage1ω` on definition binders (`letV`, `letE`, join points) and `Usage01ω` on pattern binders (a binder annotated `0` cannot be referenced); every elimination needs an open operand, so no redex that could be computed can be written (`TermTests/Syntax/NoIotaTest.lean`, `TermTests/Syntax/NormalFormTest.lean`); and its evaluator |
| `LeanScript/Term/Semantics/Closed.lean` | a term with no unknown and no open known value is a value (`Term.closed_isValue`, `Term.run_isValue`) |
| `LeanScript/Term/Semantics/NormalValue.lean` | `Term.eval` of a statement in which every variable is known (no unknown, no open known value, no join point, completely normalised known values) is the reading of a completely normalised value `NVal`: constructors all the way down, delays forced, functions as closures of closed bodies over completely normalised values (`Term.eval_normal`, `Term.run_normal`) |
| `LeanScript/Term/Rename/Basic.lean`, `LeanScript/Term/Rename/Eval.lean`, `LeanScript/Term/Rename/Weaken.lean` | renaming (partial: it fails on a dropped variable that is used) and weakening, and the fact that renaming commutes with evaluation (`Term.rename_eval`, `TermTests/Semantics/RenameTest.lean`) |
| `LeanScript/Term/Ownership/Basic.lean`, `LeanScript/Term/Ownership/Walk.lean` | the static ownership analysis (not proved): occurrences of variables, owned/borrowed arrays, in-place updates, loop accumulator modes, the versions of a function (`Own.Version.select`, `OwnedTerm`) generated as extra exports, the versions of local functions (`Own.lamPlan`), owning closures (`Own.AccMode.ownFn`), owned answers of folds (`Own.dataRecOwns`) |
| `LeanScript/Term/Optimize/Occ.lean`, `LeanScript/Term/Optimize/Dce.lean` | occurrence counts (added along straight-line code, the maximum across the arms of a branch, `ω` inside a body that may run many times) and dead-code elimination with exact usages, which preserves the meaning (`Term.dce_eval`) |
| `LeanScript/Term/Optimize/Fields.lean`, `LeanScript/Term/Optimize/FieldsWalk.lean`, `LeanScript/Term/Optimize/Reannot.lean` | the known fields of records: facts `x = (f₁, …, fₙ)` gathered along a term (`RecFact`, `RecFact.Holds`), `Term.widenFields` (a `record_casesOn` binds every field), `Term.reuseFields` (a later `record_casesOn` of a known record reuses its fields), with `Term.widenFields_eval`, `Term.reuseFields_eval` and their call counts; `Term.reannotFields` (the fields of a case analysis annotated with their counted usages, `Term.reannotFields_eval`) |
| `LeanScript/Term/Optimize/Basic.lean` | the optimiser `Term.optimize` (`Term.inlineKnown` in `Inline.lean`, `InlineEval.lean`: a known closure whose closed body only computes a pure expression of its parameter is inlined at its calls, `let y := k a` becoming `let y := share e[a]`, proved by `Term.inlineKnown_eval`; `Term.simp`, `Term.widenFields`, `Term.reuseFields`, `Term.cseWalk`, `Term.condWalk` in `Cond.lean`, `Term.appendWalk` in `Append.lean`: chains of `Array.append` regrouped to the left and of `List.append` to the right, empty literals dropped and neighbouring literals merged, proved by `Term.appendWalk_eval`; `Term.inlineRet` in `InlineRet.lean`/`InlineBlock.lean`: calls of known closures in tail position, and known closures used once with a closed body, are inlined (on any pure argument, the parameter substituted by `Term.subst` in `Subst.lean`; a body making calls at its only call, `Term.inlineAt` in `InlineOnce.lean`), their bodies re-levelled by `Term.relvl` (`Rename/Relevel.lean`), proved by `Term.inlineRet_eval`/`Term.relvl_eval`/`Term.subst_eval`/`Term.inlineAt_eval`; `Term.arithWalk` in `Arith.lean`: chains of `+` and of `*` of `Int`, `Nat` and the fixed-width integers normalised, their literals folded, the copies of an unknown in a sum counted (`x + x` is `x * 2`), three copies or more of an unknown in a product of `Int`s or `Nat`s written as a power (`x * x * x` is `x ^ 3`, the extern `lean_int_pow`/`lean_nat_pow`, `x ** 3n` in JavaScript; `ArithBasic.lean`, `ArithPow.lean`) and the operands combined from the left, proved by `Term.arithWalk_eval`; the same walk drops a unit operand of a `Float`/`Float32` operation (`x * 1.0`, `1.0 * x`, `x / 1.0`, `x - 0.0` are `x`, bit for bit, for every float: `Neu.floatUnit` in `FloatUnit.lean`, the IEEE identities in `HashableFloat/Identities.lean`), but never regroups a float chain (IEEE arithmetic is not associative; the legacy-style regrouping is the opt-in `Term.floatReassoc` in `FloatReassoc.lean`, `leanscript --float-reassoc`, which changes results: `Tests/TermTests/Optimize/AssocNumberOpsTest.lean`); `Term.dce`): copy propagation (`let x := share y`), a shared answer returned directly (`let x := share n; ret x` is `ret n`), dead `record_casesOn` dropped, known fields reused, boolean conditions simplified (`c ? true : false` is `c`, a test of a negation swaps the arms), append chains regrouped (`#["a"] ++ (#["b"] ++ (xs ++ #["c"]))` is `(#["a", "b"] ++ xs) ++ #["c"]`, `Tests/TermTests/Optimize/AppendTest.lean`), integer chains normalised (`1 + (((((2 + x) + x) + x) + x) + 3) + 4` is `x * 4 + 10`, `1 * (2 * (x * (x * (x * (x * 3))))) * 4` is `x ^ 4 * 24`, `Tests/TermTests/Optimize/ArithTest.lean`), then dead-code elimination; it preserves the value (`Term.optimize_eval`, `Term.optimize_run`, `TermTests/Optimize/OptimizeTest.lean`) |
| `LeanScript/Term/Optimize/Count.lean`, `CountRename.lean`, `CountDce.lean`, `CountOptimize.lean`, `Tests/TermTests/Optimize/CseTest.lean` | `Term.numCalls`, the number of calls (`f a`, `t.get`, `t ()`) written in a statement; renaming preserves it (`Term.numCalls_rename`), and every pass of the optimiser never increases it (`Term.numCalls_inlineKnown` in `CountInline.lean`, `Term.numCalls_inlineRet`, `Term.numCalls_simp`, `Term.numCalls_cseWalk`, `Term.numCalls_condWalk`, `Term.numCalls_appendWalk`, `Term.numCalls_arithWalk`, `Term.numCalls_dce`, so `Term.numCalls_optimize`, `Term.numCalls_optimizeN`); on `EsPrecedence01.test1` the translation has 5 calls and the optimised statement 1, with the same value |
| `LeanScript/Term/Rewrite/Step.lean`, `LeanScript/Term/Rename/Comp.lean`, `LeanScript/Term/Rewrite/StepRename.lean`, `LeanScript/Term/Rewrite/StepInv.lean`, `LeanScript/Term/Rewrite/Abstract.lean`, `LeanScript/Term/Rewrite/ChurchRosser.lean`, `LeanScript/Term/Rewrite/SimpStep.lean` | Church–Rosser for rewriting under `Term.eval`: the one-step relation `Term.Step` (drop a dead `val`/`let`/`record_casesOn`/`join`, copy propagation, a shared answer returned or jumped directly, anywhere in a term), which preserves the value (`Term.Step.eval`); it is strongly confluent, hence confluent and Church–Rosser (`Term.Step.confluent`, `Term.Step.churchRosser`, `Term.eval_churchRosser`, `Term.run_churchRosser`), normal forms are unique (`Term.Step.normal_unique`), and the optimiser's rewriting pass is a sequence of such steps (`Term.simp_star`, `Term.simp_joinable`; `TermTests/Optimize/ChurchRosserTest.lean`) |
| `LeanScript/Term/Optimize/OpenRec.lean`, `Tests/TermTests/Optimize/OpenRecTest.lean` | why `leanscript`'s open definitions are faithful: a functional whose recursive calls go down a well-founded relation has exactly one fixed point (`OpenRec.fix_unique`, `OpenRec.fix_isFix`, `OpenRec.eq_fix_of_isFix`); the optimiser keeps the fixed points of a translated open definition (`Term.optimizeN_isFix_iff`, `Term.optimizeN_fix_eq`); a `nat_rec` whose step ignores the accumulator is the `if` the JavaScript prints (`natIter_of_ignoresAcc'`); for `mc91Loop` and `ack` (open definitions written as the tool builds them), every solution of the unfolding equation is the function, and every fixed point of the `#leanscript_to_term` translation of `mc91Loop`'s open definition, optimised any number of times, is `mc91Loop` (`mc91LoopOpenT_optimizeN_fix`) |
| `LeanScript/WFTerm/Syntax.lean`, `LeanScript/WFTerm/Eval.lean`, `LeanScript/WFTerm/Optimize.lean` | `WFTerm`: well-founded recursion around `Term` (whose normal-form terms are the call-free atoms): global functions with pre/postconditions and a well-founded relation, recursive calls (`WFComp.self`) carrying their decrease proof under the path condition, calls of earlier global functions, shared values, `map`/`foldl` whose body knows `x ∈ l`, join points and recursive join points (`joinrec`, loops whose back edges carry their decrease proof); the evaluator `WFTerm.eval`/`WFProgram.run` is total and structural, runs recursion by `WellFounded.fix` (proofs only: no fuel, no measure, no default value) and returns the answer with its postcondition; the optimiser `WFTerm.optimize` (atoms by `Term.optimize`, constant tests, a join point entered at once inlined, folds of `[]`) preserves the value (`WFTerm.optimize_eval`, `WFProgram.optimize_run`; `TermTests/Optimize/WFTermTest.lean`, run in `Tests/Main.lean`) |
| `LeanScript/Term/Build.lean` | abbreviations the elaborators write (`PExpr.externLit`, `Branch.enumList`, `Comp.dataRecS`, …) |
| `LeanScript/Term/Syntax/Tuple.lean` | `Tuple F [a, b] = F a × F b`: right-nested products with no trailing `PUnit`, for environments, extern arguments and join-point closures |
| `LeanScript/Term/Semantics/BoundedLoop.lean` | a loop of a fixed number of steps whose iterations shrink a measure has stopped after `μ init + 1` steps, and more steps change nothing (`boundedLoop_done`, `boundedLoop_stable`): why a translated `while` loop needs no fuel |
| `LeanScript/GenElab/` (`Signature.lean`, `GetCtor.lean`, `Read.lean`, `Read/`, `Translate.lean`, `Print.lean`, `Cache.lean`) | `leanscript_signature`, `#leanscript_get_ty`/`_ctor`/`_cases`, and the generator they share (reading Lean types, erasing fields that depend on earlier fields — `Fin n → Nat` is `Nat → Nat`, `TermTests/ToTerm/DependentFieldTest.lean`; on a recursive cycle `Fin m → X` is `Nat → Option X`, so the rose tree `node : (m : Nat) → (Fin m → Rose) → Rose` is a record of a `nat` and a function to `Option Rose`, different from the `List` and `Array` rose trees, `TermTests/Datatypes/RoseVariantsTest.lean` — and the indices of inductive families — `Vec α n` is the linked list `Vec α`, `TermTests/Datatypes/IndexedFamilyTest.lean`; a type index recursed at other indices goes through a generated element type — `Nest α` is a list of `Nest.Elem α` trees, `TermTests/Datatypes/NestTest.lean` —; a quotient is read as its carrier and a proof field is dropped — `Quot (· % 2 = · % 2)` is `Nat`, `Pos` is `Nat`, `TermTests/Datatypes/QuotientTest.lean` —, SCCs and grounding order, printing, cache) |
| `LeanScript/TyElab/Notation.lean` | the `[Ty| …]` notation |
| `LeanScript/TermElab/Anf.lean`, `LeanScript/TermElab/Anf/` (`Src`, `Sem`, `Render`, `Emit`), `LeanScript/TermElab/Notation.lean` | the normaliser (by evaluation, at elaboration time) of direct-style source trees into normal-form terms, and the `[Term| …]` notation built on it |
| `LeanScript/TermElab/ToTerm.lean`, `LeanScript/TermElab/ToTerm/` | `#leanscript_to_term` (`ToTerm/Basic.lean`: translation state and helpers; `ToTerm/Expr.lean`: the expression translator `tr`, with its cases in `ToTerm/Expr/` (`Loops`, `Calls`, `Ctor`, `Cases`) taking `tr` as an argument, with calls of library functions as calls of catalogue externs (`Neu.extern`, table `ToTerm/ExternTable.lean`), pure `if`s as `Neu.cond` and externs that take a proof, `TermTests/Extern/CondExternTest.lean`; `ToTerm/While.lean`: which `while` loops are structurally terminating, `TermTests/ToTerm/WhileTest.lean`; `ToTerm.lean`: the definition translator and the syntax), including `mutual` groups of recursive functions and members of a block held inside an `Array` or a function (`TermTests/ToTerm/MutualToTermTest.lean`) |
| `LeanScript/LeanInitPureExterns.lean`, `LeanScript/LeanInitPureExterns/`, `LeanScript/LeanInitPureExterns/Shorthands.lean`, `LeanScript/ExternElab/CatalogueShorthands.lean` | the catalogue of the pure externs of `Init`, indexed by signature (`LeanInitPureExtern σs τ`): the language's only kind of extern |
| `LeanScript/Term/Extern/Catalogue.lean`, `LeanScript/Term/Extern/Eval.lean`, `LeanScript/Term/Extern/Eval/`, `LeanScript/Term/Extern/Shorthands.lean`, `LeanScript/ExternElab/TermShorthands.lean` | the catalogue instantiated at the types of the language (`Extern ks σs τ`), the meaning of every entry (`Extern.eval`), and one term former per entry (`PExpr.lean_string_any s f`, `Neu.lean_nat_add a b`) |
| `LeanScript/TacticElab/KernelRfl.lean` | `kernel_rfl`, an equation checked by the kernel only |
| `HashableFloat/` | `HashableFloat`/`HashableFloat32`: floats with lawful `BEq`, `Hashable` and a linear `Ord` (away from `NaN`), the leaf types of the floats |
| `NonEmpty/` | correct-by-construction non-empty lists, arrays and strings (their literal notations and `ToExpr` instances are in `NonEmpty/*Elab/`) |
| `TyTests/`, `TermTests/` | the tests, checked by `lake build` (`#guard_msgs` snapshots, `rfl` runs) |
| `Tests/Main.lean`, `Spec/` | `lake test`: the checks on values that are too slow for the kernel (`kernel_rfl` runs of `Term.eval` taking from half a second to many seconds), run compiled with the `Spec` test library, and the optimiser on the same programs; unit tests of the JavaScript conversion (typed operations, nominal object types, folds of declared datatypes, literals too big for a `number`; `runtime.js` exports every imported operation) |
| `RuntimeSpec/` (`Model.lean`, `Runtime.lean`, `Correct.lean`) | the integer functions of `runtime.js` whose code was simplified, transcribed into a model of the JavaScript they use (`BigInt`s and safe-integer `number`s as `Int`, the 32-bit operators exactly, an overflow `RangeError` as `none`), with the old versions beside them; proofs that each computes Lean's operation on its representation (a function that may throw returns Lean's result checked to be a safe integer), that the `BigInt`/`number` split agrees with the old `typeof` tests, and that every removed throw could never fire (`lake build RuntimeSpec`) |
| `proposals/` | proposals, reviews and stand-alone sketches; nothing here is part of the build (`NominalTyProposal.md` is the design that is implemented) |
| `scripts/` | benchmarking scripts; `annotate_runtime.py` writes the type comments of the functions of `runtime.js` from the signatures of `JsTerm/Ops/Imported.lean` (`--check`: fail if they are not up to date) |

Elaborators, notations, tactics and the meta-level code they use live in `XxxElab/`
directories (`TyElab/`, `TermElab/`, `GenElab/`, `ExternElab/`, `TacticElab/`), next to the
modules they elaborate into.

There is no module that gathers the others: a file imports the modules it uses, one by
one.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
