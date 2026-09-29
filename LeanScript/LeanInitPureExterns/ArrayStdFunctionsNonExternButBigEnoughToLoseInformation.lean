module
prelude
public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: array functions of `Init` that are *not* `@[extern]`

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised).

The Lean functions below are written in Lean (loops, recursion, `foldl` and `push`), not as
`@[extern]` C primitives, so without an entry `#leanscript_to_term` unfolds them: `xs ++ ys`
becomes `array_foldl ys xs (fun e acc => lean_array_push acc e)`.  That is correct, but the
information *which* function was called is lost, and the JavaScript backend can then only
write the loop; with an entry it can write what JavaScript already has for it (`[...a, ...b]`,
`a.map(f)`, `a.filter(p)`, `a.slice(i, j)`, `a.some(p)`, `a.includes(x)`, …) and optimise
chains of them (an append of appends is one array literal with spreads).

**Which functions.**  A function gets an entry when its unfolding loses information the
backend can use, i.e. it is at least one loop (or a recursion) in Lean *and* JavaScript or a
short function of `runtime.js` can do it directly.  The functions that are already externs
(`Array.size`, `Array.push`, `Array.pop`, `Array.set!`, `Array.replicate`, `Array.mkEmpty`, …)
are in `LeanScript.LeanInitPureExterns.Core`.  The functions that unfold to one of the entries
below need no entry of their own (`Array.take xs i` is `xs.extract 0 i`, `Array.drop xs i` is
`xs.extract i`); nor do the ones whose unfolding is already an access (`Array.back!`,
`xs[i]?`: a bounds check and `lean_array_get`).

| JavaScript                  | Lean                           | entry                        |
| :-------------------------- | :----------------------------- | :--------------------------- |
| `[...a, ...b]`, `a.concat(b)` | `a ++ b`, `Array.append`     | `lean_array_append`          |
| `a.map(f)`                  | `Array.map`, `f <$> a`         | `lean_array_map`             |
| `a.slice(i, j).filter(p)`   | `Array.filter`                 | `lean_array_filter`          |
| `a.flatMap(f)`              | `Array.flatMap`                | `lean_array_flat_map`        |
| `a.flat()`                  | `Array.flatten`                | `lean_array_flatten`         |
| `a.toReversed()`            | `Array.reverse`                | `lean_array_reverse`         |
| `a.slice(i, j)`             | `Array.extract`, `take`, `drop`| `lean_array_extract`         |
| `a.slice(i, j).some(p)`     | `Array.any`                    | `lean_array_any`             |
| `a.slice(i, j).every(p)`    | `Array.all`                    | `lean_array_all`             |
| `a.includes(x)`             | `Array.contains`, `x ∈ a`      | `lean_array_contains`        |
| `a.find(p)`                 | `Array.find?`                  | `lean_array_find_opt`        |
| `a.findIndex(p)`            | `Array.findIdx?`               | `lean_array_find_idx_opt`    |
| `a.indexOf(x)`              | `Array.idxOf?`                 | `lean_array_idx_of_opt`      |
| `a.toSpliced(i, 1)`         | `Array.eraseIdx!`              | `lean_array_erase_idx`       |
| `a.toSpliced(i, 0, x)`      | `Array.insertIdx!`             | `lean_array_insert_idx`      |
| `a.toSpliced(i, 1)`         | `Array.eraseIdxIfInBounds`     | `lean_array_erase_idx_if_in_bounds` |
| `a.toSpliced(i, 0, x)`      | `Array.insertIdxIfInBounds`    | `lean_array_insert_idx_if_in_bounds` |
| `a.toSorted(cmp)` (Lean's quicksort, not stable) | `Array.qsort` | `lean_array_qsort`       |
| `a.reduceRight(f, z)`       | `Array.foldr`                  | `lean_array_foldr`           |
| `a.map((x, i) => f(x, b[i]))` | `Array.zipWith`              | `lean_array_zip_with`        |
| `a.map((x, i) => [x, b[i]])`  | `Array.zip`                  | `lean_array_zip`             |
| `a.at(-1)`                  | `Array.back?`                  | `lean_array_back_opt`        |
| `a.filter(p).length`        | `Array.countP`                 | `lean_array_count_p`         |
| `[...a, ...b]` / cons cells | `List.append` (`l ++ l'`)      | `lean_list_append`           |

`Array.replicate` (`arr.fill`) is already the C extern `lean_mk_array`, and
`Array.size`/`Array.push`/`Array.pop`/`Array.set!`/`a[i]!` are C externs as well.

**Instances.**  A `[BEq α]` argument (`Array.contains`, `Array.idxOf?`) is passed to the extern
as its function `BEq.beq` (the first argument, of type `α → α → Bool`), so the entry does not
depend on an instance: `#leanscript_to_term` passes `fun a b => a == b`
(`LeanScript.Gen.externCall`).

**Default arguments.**  The `optParam`s of the Lean functions (the bounds `start`/`stop` of
`Array.filter`, `Array.any`, `Array.all`, `Array.extract`, `Array.foldr`, the bounds `lo`/`hi`
and the order of `Array.qsort`) are ordinary arguments of the entries: the elaborator has
filled them in when the program was written.

**Panics.**  `Array.eraseIdx!` and `Array.insertIdx!` panic out of bounds; the value of a panic
is the default of the type (the empty array), which is what the entry answers, as the Lean
function does.  `Array.eraseIdxIfInBounds` and `Array.insertIdxIfInBounds` answer the array
unchanged out of bounds (the operations then answer a copy of it, so that their answer is always
a new array).

The meaning of each entry is the Lean function in its comment (`LeanScript.Extern.eval`,
`LeanScript.Term.Extern.Eval.ArrayStd`), so an entry cannot change the value of a program.
-/

open LeanPrimTy
open LeanPrimTyCovariant

variable {MyTy : Type}
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  (ordering : MyTy)
  (leanName : MyTy)

------------------------------------------------------------------------------
-- Init/Data/Array/Basic.lean, Init/Data/Array/QSort/Basic.lean, Init/Data/List/Basic.lean:
-- the functions written in Lean that the backend knows
------------------------------------------------------------------------------
/-- The array (and list) functions of `Init` written in Lean whose unfolding would lose
    information (see the module doc). -/
inductive ArrayStdExtern : List MyTy → MyTy → Type where
  | lean_array_append : (αt : MyTy) → ArrayStdExtern [(array αt), (array αt)] (array αt) -- Array.append
  | lean_array_map : (αt βt : MyTy) → ArrayStdExtern [(fn1 αt βt), (array αt)] (array βt) -- Array.map
  | lean_array_filter : (αt : MyTy) → ArrayStdExtern [(fn1 αt LeanPrimTy.bool), (array αt), nat, nat] (array αt) -- Array.filter
  | lean_array_flat_map : (αt βt : MyTy) → ArrayStdExtern [(fn1 αt (array βt)), (array αt)] (array βt) -- Array.flatMap
  | lean_array_flatten : (αt : MyTy) → ArrayStdExtern [(array (Coe.coe (array αt : LeanPrimTyCovariant MyTy) : MyTy))] (array αt) -- Array.flatten
  | lean_array_reverse : (αt : MyTy) → ArrayStdExtern [(array αt)] (array αt) -- Array.reverse
  | lean_array_extract : (αt : MyTy) → ArrayStdExtern [(array αt), nat, nat] (array αt) -- Array.extract
  | lean_array_any : (αt : MyTy) → ArrayStdExtern [(array αt), (fn1 αt LeanPrimTy.bool), nat, nat] LeanPrimTy.bool -- Array.any
  | lean_array_all : (αt : MyTy) → ArrayStdExtern [(array αt), (fn1 αt LeanPrimTy.bool), nat, nat] LeanPrimTy.bool -- Array.all
  | lean_array_contains : (αt : MyTy) → ArrayStdExtern [(fn2 αt αt LeanPrimTy.bool), (array αt), αt] LeanPrimTy.bool -- Array.contains
  | lean_array_find_opt : (αt : MyTy) → ArrayStdExtern [(fn1 αt LeanPrimTy.bool), (array αt)] (option αt) -- Array.find?
  | lean_array_find_idx_opt : (αt : MyTy) → ArrayStdExtern [(fn1 αt LeanPrimTy.bool), (array αt)] (option nat) -- Array.findIdx?
  | lean_array_idx_of_opt : (αt : MyTy) → ArrayStdExtern [(fn2 αt αt LeanPrimTy.bool), (array αt), αt] (option nat) -- Array.idxOf?
  | lean_array_erase_idx : (αt : MyTy) → ArrayStdExtern [(array αt), nat] (array αt) -- Array.eraseIdx!
  | lean_array_insert_idx : (αt : MyTy) → ArrayStdExtern [(array αt), nat, αt] (array αt) -- Array.insertIdx!
  | lean_array_erase_idx_if_in_bounds : (αt : MyTy) → ArrayStdExtern [(array αt), nat] (array αt) -- Array.eraseIdxIfInBounds
  | lean_array_insert_idx_if_in_bounds : (αt : MyTy) → ArrayStdExtern [(array αt), nat, αt] (array αt) -- Array.insertIdxIfInBounds
  | lean_array_qsort : (αt : MyTy) → ArrayStdExtern [(array αt), (fn2 αt αt LeanPrimTy.bool), nat, nat] (array αt) -- Array.qsort
  | lean_array_foldr : (αt βt : MyTy) → ArrayStdExtern [(fn2 αt βt βt), βt, (array αt), nat, nat] βt -- Array.foldr
  | lean_array_zip_with : (αt βt γt : MyTy) → ArrayStdExtern [(fn2 αt βt γt), (array αt), (array βt)] (array γt) -- Array.zipWith
  | lean_array_zip : (αt βt : MyTy) → ArrayStdExtern [(array αt), (array βt)] (array (prod αt βt)) -- Array.zip
  | lean_array_back_opt : (αt : MyTy) → ArrayStdExtern [(array αt)] (option αt) -- Array.back?
  | lean_array_count_p : (αt : MyTy) → ArrayStdExtern [(fn1 αt LeanPrimTy.bool), (array αt)] nat -- Array.countP
  | lean_list_append : (αt : MyTy) → ArrayStdExtern [(list αt), (list αt)] (list αt) -- List.append

end LeanScript

end
