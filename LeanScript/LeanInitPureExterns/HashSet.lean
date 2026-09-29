module
prelude
public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: the functions of `Std.HashSet`

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised); the hash maps are in
`LeanScript.LeanInitPureExterns.HashMap`, whose module doc explains the choices (why entries,
the instances as arguments, the order, the panics), which are the same here.

No function of `Std.HashSet` (`Std/Data/HashSet/Basic.lean`) is `@[extern]`: a hash set is a
`Std.HashMap κ Unit`, and every operation is the hash map's.  With the former
`LeanPrimTyCovariant.hashSet` and an entry per function the backend writes what JavaScript has:

| JavaScript (object keys, `LeanPrimTy.isObjectKey` or an enum) | Lean | entry |
| :--- | :--- | :--- |
| `{}` / `new Set()` | `Std.HashSet.emptyWithCapacity`, `∅`, `{}` | `lean_hash_set_empty_with_capacity` |
| `({...s, [k]: true})` / `new Set(s).add(k)` | `Std.HashSet.insert` | `lean_hash_set_insert` |
| `[k in s, {...s, [k]: true}]` | `Std.HashSet.containsThenInsert` | `lean_hash_set_contains_then_insert` |
| `k in s` / `s.has(k)` | `Std.HashSet.contains`, `k ∈ s` | `lean_hash_set_contains` |
| `const {[k]: _, ...r} = s; r` / `s.delete(k)` on a copy | `Std.HashSet.erase` | `lean_hash_set_erase` |
| `Object.keys(s).length` / `s.size` | `Std.HashSet.size` | `lean_hash_set_size` |
| `… === 0` | `Std.HashSet.isEmpty` | `lean_hash_set_is_empty` |
| `k in s ? k : undefined` | `Std.HashSet.get?` | `lean_hash_set_get_opt` |
| `k in s ? k : d` | `Std.HashSet.getD` | `lean_hash_set_get_d` |
| `k in s ? k : panic(d)` | `Std.HashSet.get!` | `lean_hash_set_get_bang` |
| `Object.keys(s)` / `[...s]` | `Std.HashSet.toList`, `Std.HashSet.toArray` | `lean_hash_set_to_list`, `lean_hash_set_to_array` |
| `Object.fromEntries(l.map(k => [k, true]))` / `new Set(l)` | `Std.HashSet.ofList`, `Std.HashSet.ofArray` | `lean_hash_set_of_list`, `lean_hash_set_of_array` |
| `Object.keys(s).reduce(…)` | `Std.HashSet.fold` (and `for k in s` in `Id`) | `lean_hash_set_fold` |
| `… .filter(…)` | `Std.HashSet.filter` | `lean_hash_set_filter` |
| `new Set([...s, ...l])` | `Std.HashSet.insertMany` (a `List`, an `Array`) | `lean_hash_set_insert_many_list`, `lean_hash_set_insert_many_array` |
| `… .every(…)` / `.some(…)` | `Std.HashSet.all`, `Std.HashSet.any` | `lean_hash_set_all`, `lean_hash_set_any` |
| `s₁.union(s₂)` | `Std.HashSet.union`, `s₁ ∪ s₂` | `lean_hash_set_union` |
| `s₁.intersection(s₂)` | `Std.HashSet.inter`, `s₁ ∩ s₂` | `lean_hash_set_inter` |
| `s₁.difference(s₂)` | `Std.HashSet.diff`, `s₁ \ s₂` | `lean_hash_set_diff` |
| `s₁.size === s₂.size && s₁.isSubsetOf(s₂)` | `Std.HashSet.beq`, `s₁ == s₂` | `lean_hash_set_beq` |
| two filters | `Std.HashSet.partition` | `lean_hash_set_partition` |

**Instances.**  As for the hash maps, the entries that hash or compare keys take
`BEq.beq : κ → κ → Bool` and `Hashable.hash : κ → UInt64` as their first two arguments; the
backend drops them when the key is an object key.

**Order.**  `toList`, `toArray` and `fold` (marked *order*) list the keys in the order of Lean's
buckets, not in the order of a JavaScript object or `Set` (see the hash maps).

**Not entries.**  `Std.HashSet.get` (takes a proof of `k ∈ s`: `lean_hash_set_get_bang` with the
`Inhabited` default), `Std.HashSet.foldM`, `Std.HashSet.forM`, `Std.HashSet.forIn` (monadic: in
`Id` they are `fold`), the `Repr` instance and `Std.HashSet.Internal.numBuckets`.

The meaning of each entry is the Lean function in its comment.

**Status.**  `Ty` has no former for hash sets yet (`LeanScript.Ty.ofCovariant`), so this family
is not a constructor of `LeanInitPureExtern`: it records the functions and their signatures,
over any grammar of types with the former `LeanPrimTyCovariant.hashSet`.
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

------------------------------
-- Std/Data/HashSet/Basic.lean
------------------------------
/-- The functions of `Std.HashSet` (all written in Lean, none `@[extern]`), with the `BEq`
    and `Hashable` instances of the key as the first two arguments of the ones that hash or
    compare keys (see the module doc of `LeanScript.LeanInitPureExterns.HashMap`).  `κt` is the
    type of the keys. -/
inductive HashSetExtern : List MyTy → MyTy → Type where
  | lean_hash_set_empty_with_capacity : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), nat] (hashSet κt) -- Std.HashSet.emptyWithCapacity
  | lean_hash_set_insert : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] (hashSet κt) -- Std.HashSet.insert
  | lean_hash_set_contains_then_insert : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] (prod LeanPrimTy.bool (hashSet κt)) -- Std.HashSet.containsThenInsert
  | lean_hash_set_contains : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] LeanPrimTy.bool -- Std.HashSet.contains
  | lean_hash_set_erase : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] (hashSet κt) -- Std.HashSet.erase
  | lean_hash_set_size : (κt : MyTy) → HashSetExtern [(hashSet κt)] nat -- Std.HashSet.size
  | lean_hash_set_is_empty : (κt : MyTy) → HashSetExtern [(hashSet κt)] LeanPrimTy.bool -- Std.HashSet.isEmpty
  | lean_hash_set_get_opt : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] (option κt) -- Std.HashSet.get?
  | lean_hash_set_get_d : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt, κt] κt -- Std.HashSet.getD
  | lean_hash_set_get_bang : (κt : MyTy) → HashSetExtern [κt, (fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), κt] κt -- Std.HashSet.get! (the default first)
  | lean_hash_set_to_list : (κt : MyTy) → HashSetExtern [(hashSet κt)] (list κt) -- Std.HashSet.toList (order)
  | lean_hash_set_to_array : (κt : MyTy) → HashSetExtern [(hashSet κt)] (array κt) -- Std.HashSet.toArray (order)
  | lean_hash_set_of_list : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (list κt)] (hashSet κt) -- Std.HashSet.ofList
  | lean_hash_set_of_array : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (array κt)] (hashSet κt) -- Std.HashSet.ofArray
  | lean_hash_set_fold : (κt βt : MyTy) → HashSetExtern [(fn2 βt κt βt), βt, (hashSet κt)] βt -- Std.HashSet.fold (order)
  | lean_hash_set_filter : (κt : MyTy) → HashSetExtern [(fn1 κt LeanPrimTy.bool), (hashSet κt)] (hashSet κt) -- Std.HashSet.filter
  | lean_hash_set_insert_many_list : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (list κt)] (hashSet κt) -- Std.HashSet.insertMany (of a `List`)
  | lean_hash_set_insert_many_array : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (array κt)] (hashSet κt) -- Std.HashSet.insertMany (of an `Array`)
  | lean_hash_set_all : (κt : MyTy) → HashSetExtern [(hashSet κt), (fn1 κt LeanPrimTy.bool)] LeanPrimTy.bool -- Std.HashSet.all
  | lean_hash_set_any : (κt : MyTy) → HashSetExtern [(hashSet κt), (fn1 κt LeanPrimTy.bool)] LeanPrimTy.bool -- Std.HashSet.any
  | lean_hash_set_union : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (hashSet κt)] (hashSet κt) -- Std.HashSet.union
  | lean_hash_set_inter : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (hashSet κt)] (hashSet κt) -- Std.HashSet.inter
  | lean_hash_set_diff : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (hashSet κt)] (hashSet κt) -- Std.HashSet.diff
  | lean_hash_set_beq : (κt : MyTy) → HashSetExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashSet κt), (hashSet κt)] LeanPrimTy.bool -- Std.HashSet.beq
  | lean_hash_set_partition : (κt : MyTy) → HashSetExtern [(fn1 κt LeanPrimTy.bool), (hashSet κt)] (prod (hashSet κt) (hashSet κt)) -- Std.HashSet.partition
  -- | lean_hash_set_get : (κt : MyTy) → (s : …) → (k : …) → k ∈ s → HashSetExtern κt -- Std.HashSet.get (takes a proof: `lean_hash_set_get_bang` with the `Inhabited` default)
  -- | lean_hash_set_fold_m -- Std.HashSet.foldM (monadic: in `Id` it is `fold`)
  -- | lean_hash_set_for_m -- Std.HashSet.forM (monadic)
  -- | lean_hash_set_for_in -- Std.HashSet.forIn (monadic: `for k in s` in `Id` is `fold`)
  -- | lean_hash_set_num_buckets -- Std.HashSet.Internal.numBuckets (a detail of the layout)

end LeanScript

end
