module
prelude
public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: the functions of `Std.HashMap`

One part of the catalogue `LeanScript.LeanInitPureExtern` (see
`LeanScript.LeanInitPureExterns` for how it is organised); the hash sets are in
`LeanScript.LeanInitPureExterns.HashSet`.

**Why entries.**  No function of `Std.HashMap` (`Std/Data/HashMap/Basic.lean`,
`Std/Data/HashMap/AdditionalOperations.lean`) is `@[extern]`: a hash map is a structure around an
array of buckets (`Std.DHashMap.Internal.Raw`), and every operation is Lean code that hashes the
key, indexes the array and walks an association list.  Unfolded, `m.insert k v` becomes that
code, the information that the value *is a hash map* is lost, and the JavaScript backend can
only write the buckets by hand.  With the former `LeanPrimTyCovariant.hashMap` and an entry per
function, it writes what JavaScript has (`LeanPrimTyCovariant.hashMap`):

| JavaScript (object keys, `LeanPrimTy.isObjectKey` or an enum) | Lean | entry |
| :--- | :--- | :--- |
| `{}` (`Object.create(null)`) / `new Map()` | `Std.HashMap.emptyWithCapacity`, `∅`, `{}` | `lean_hash_map_empty_with_capacity` |
| `({...m, [k]: v})` / `new Map(m).set(k, v)` | `Std.HashMap.insert` | `lean_hash_map_insert` |
| `k in m ? m : {...m, [k]: v}` | `Std.HashMap.insertIfNew` | `lean_hash_map_insert_if_new` |
| `[k in m, {...m, [k]: v}]` | `Std.HashMap.containsThenInsert` | `lean_hash_map_contains_then_insert` |
| `[k in m, k in m ? m : {...m, [k]: v}]` | `Std.HashMap.containsThenInsertIfNew` | `lean_hash_map_contains_then_insert_if_new` |
| `[m[k], k in m ? m : {...m, [k]: v}]` | `Std.HashMap.getThenInsertIfNew?` | `lean_hash_map_get_then_insert_if_new_opt` |
| `m[k]` (`undefined` is `none`) | `Std.HashMap.get?`, `m[k]?` | `lean_hash_map_get_opt` |
| `k in m` / `m.has(k)` | `Std.HashMap.contains`, `k ∈ m` | `lean_hash_map_contains` |
| `k in m ? m[k] : d` | `Std.HashMap.getD` | `lean_hash_map_get_d` |
| `k in m ? m[k] : panic(d)` | `Std.HashMap.get!`, `m[k]!` | `lean_hash_map_get_bang` |
| `k in m ? k : undefined` | `Std.HashMap.getKey?` | `lean_hash_map_get_key_opt` |
| `k in m ? k : d` | `Std.HashMap.getKeyD` | `lean_hash_map_get_key_d` |
| `k in m ? k : panic(d)` | `Std.HashMap.getKey!` | `lean_hash_map_get_key_bang` |
| `const {[k]: _, ...r} = m; r` / `m.delete(k)` on a copy | `Std.HashMap.erase` | `lean_hash_map_erase` |
| `Object.keys(m).length` / `m.size` | `Std.HashMap.size` | `lean_hash_map_size` |
| `… === 0` | `Std.HashMap.isEmpty` | `lean_hash_map_is_empty` |
| `Object.keys(m)` / `[...m.keys()]` | `Std.HashMap.keys`, `Std.HashMap.keysArray` | `lean_hash_map_keys`, `lean_hash_map_keys_array` |
| `Object.values(m)` / `[...m.values()]` | `Std.HashMap.values`, `Std.HashMap.valuesArray` | `lean_hash_map_values`, `lean_hash_map_values_array` |
| `Object.entries(m)` / `[...m]` | `Std.HashMap.toList`, `Std.HashMap.toArray` | `lean_hash_map_to_list`, `lean_hash_map_to_array` |
| `Object.fromEntries(l)` / `new Map(l)` | `Std.HashMap.ofList`, `Std.HashMap.ofArray` | `lean_hash_map_of_list`, `lean_hash_map_of_array` |
| `Object.entries(m).reduce(…)` | `Std.HashMap.fold` (and `for (k, v) in m` in `Id`) | `lean_hash_map_fold` |
| `Object.fromEntries(Object.entries(m).filter(…))` | `Std.HashMap.filter` | `lean_hash_map_filter` |
| … `.flatMap(…)` | `Std.HashMap.filterMap` | `lean_hash_map_filter_map` |
| … `.map(…)` | `Std.HashMap.map` | `lean_hash_map_map` |
| `k in m ? {...m, [k]: f(m[k])} : m` | `Std.HashMap.modify` | `lean_hash_map_modify` |
| get, then set or delete | `Std.HashMap.alter` | `lean_hash_map_alter` |
| `Object.assign({...m}, Object.fromEntries(l))` | `Std.HashMap.insertMany` (a `List`, an `Array`) | `lean_hash_map_insert_many_list`, `lean_hash_map_insert_many_array` |
| `Object.entries(m).every(…)` / `.some(…)` | `Std.HashMap.all`, `Std.HashMap.any` | `lean_hash_map_all`, `lean_hash_map_any` |
| `({...m₁, ...m₂})` | `Std.HashMap.union`, `m₁ ∪ m₂` | `lean_hash_map_union` |
| keep the keys of `m₁` in `m₂` | `Std.HashMap.inter`, `m₁ ∩ m₂` | `lean_hash_map_inter` |
| drop the keys of `m₁` in `m₂` | `Std.HashMap.diff`, `m₁ \ m₂` | `lean_hash_map_diff` |
| same size, every entry of `m₁` in `m₂` | `Std.HashMap.beq`, `m₁ == m₂` | `lean_hash_map_beq` |
| two filters | `Std.HashMap.partition` | `lean_hash_map_partition` |
| `Object.groupBy(xs, key)` / `Map.groupBy` | `Array.groupByKey`, `List.groupByKey` | `lean_array_group_by_key`, `lean_list_group_by_key` |

**Instances.**  A hash map depends on the `BEq` and `Hashable` instances of its key (they are
parameters of the type `Std.HashMap κ ν`).  As for `Array.contains`
(`LeanScript.LeanInitPureExterns.ArrayStdFunctionsNonExternButBigEnoughToLoseInformation`), an
entry takes them as functions: its first two arguments are `BEq.beq : κ → κ → Bool` and
`Hashable.hash : κ → UInt64`.  Only the entries whose Lean function hashes or compares keys
take them (building a map, and looking up, adding or removing a key); the ones that only walk
the buckets (`size`, `toList`, `fold`, `filter`, `map`, `all`, …) do not.  The backend drops the
two arguments when the key is an object key (`LeanPrimTy.isObjectKey`, or an enum): it then
converts the key with `String` instead.

**Order.**  The order of `toList`, `toArray`, `keys`, `keysArray`, `values`, `valuesArray` and
`fold` is the order of Lean's buckets: it depends on the hashes (`String.hash` is
`lean_string_hash`, `Nat` hashes to itself, …) and on the history of the map (the capacity,
the resizes, and a bucket lists its most recent key first).  A JavaScript object lists its
integer-like property names first, in increasing order, then the others in insertion order,
and a `Map` lists its keys in insertion order.  So these entries (marked *order* below) can
only be written with the JavaScript containers directly when the answer does not depend on the
order (it is sorted, summed, put in another hash map, …); otherwise the runtime must reproduce
Lean's buckets.  Every other entry answers the same whatever the order.

**Default arguments, panics.**  The capacity of `emptyWithCapacity` is an ordinary argument
(the elaborator has filled it in; JavaScript ignores it).  `get!` and `getKey!` panic when the
key is missing; the value of a panic is the default of the type, given as the first argument,
as for `lean_array_get`.

**Not entries.**
* `Std.HashMap.get` and `Std.HashMap.getKey` take a proof of `k ∈ m` and answer a value of an
  arbitrary type: `m[k]` is written with `get!`'s entry and the `Inhabited` default (as
  `Array.getInternal` is, `LeanScript.LeanInitPureExterns.Core`).
* `Std.HashMap.foldM`, `Std.HashMap.forM`, `Std.HashMap.forIn` are monadic: in `Id` they are
  `fold`, and in any other monad they are not pure.
* `Std.HashMap.unitOfList`, `Std.HashMap.unitOfArray`, `Std.HashMap.insertManyIfNewUnit` answer
  a `Std.HashMap κ Unit`, and `Unit` is erased: they are the hash sets'
  (`Std.HashSet.ofList`, …), see `LeanScript.LeanInitPureExterns.HashSet`.
* The `Repr` instance and `Std.HashMap.Internal.numBuckets` are not pure computations of the
  program (a rendering, and a detail of the layout).

The meaning of each entry is the Lean function in its comment.

**Status.**  `Ty` has no former for hash maps yet (`LeanScript.Ty.ofCovariant`), so this family
is not a constructor of `LeanInitPureExtern`: it records the functions and their signatures,
over any grammar of types with the former `LeanPrimTyCovariant.hashMap`.
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
-- Std/Data/HashMap/Basic.lean, Std/Data/HashMap/AdditionalOperations.lean
------------------------------------------------------------------------------
/-- The functions of `Std.HashMap` (all written in Lean, none `@[extern]`), with the `BEq`
    and `Hashable` instances of the key as the first two arguments of the ones that hash or
    compare keys (see the module doc).  `κt` is the type of the keys, `νt` of the values. -/
inductive HashMapExtern : List MyTy → MyTy → Type where
  | lean_hash_map_empty_with_capacity : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), nat] (hashMap κt νt) -- Std.HashMap.emptyWithCapacity
  | lean_hash_map_insert : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] (hashMap κt νt) -- Std.HashMap.insert
  | lean_hash_map_insert_if_new : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] (hashMap κt νt) -- Std.HashMap.insertIfNew
  | lean_hash_map_contains_then_insert : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] (prod LeanPrimTy.bool (hashMap κt νt)) -- Std.HashMap.containsThenInsert
  | lean_hash_map_contains_then_insert_if_new : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] (prod LeanPrimTy.bool (hashMap κt νt)) -- Std.HashMap.containsThenInsertIfNew
  | lean_hash_map_get_then_insert_if_new_opt : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] (prod (option νt) (hashMap κt νt)) -- Std.HashMap.getThenInsertIfNew?
  | lean_hash_map_get_opt : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] (option νt) -- Std.HashMap.get?
  | lean_hash_map_contains : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] LeanPrimTy.bool -- Std.HashMap.contains
  | lean_hash_map_get_d : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, νt] νt -- Std.HashMap.getD
  | lean_hash_map_get_bang : (κt νt : MyTy) → HashMapExtern [νt, (fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] νt -- Std.HashMap.get! (the default first)
  | lean_hash_map_get_key_opt : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] (option κt) -- Std.HashMap.getKey?
  | lean_hash_map_get_key_d : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, κt] κt -- Std.HashMap.getKeyD
  | lean_hash_map_get_key_bang : (κt νt : MyTy) → HashMapExtern [κt, (fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] κt -- Std.HashMap.getKey! (the default first)
  | lean_hash_map_erase : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt] (hashMap κt νt) -- Std.HashMap.erase
  | lean_hash_map_size : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] nat -- Std.HashMap.size
  | lean_hash_map_is_empty : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] LeanPrimTy.bool -- Std.HashMap.isEmpty
  | lean_hash_map_keys : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (list κt) -- Std.HashMap.keys (order)
  | lean_hash_map_keys_array : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (array κt) -- Std.HashMap.keysArray (order)
  | lean_hash_map_values : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (list νt) -- Std.HashMap.values (order)
  | lean_hash_map_values_array : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (array νt) -- Std.HashMap.valuesArray (order)
  | lean_hash_map_to_list : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (list (prod κt νt)) -- Std.HashMap.toList (order)
  | lean_hash_map_to_array : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt)] (array (prod κt νt)) -- Std.HashMap.toArray (order)
  | lean_hash_map_of_list : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (list (prod κt νt))] (hashMap κt νt) -- Std.HashMap.ofList
  | lean_hash_map_of_array : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (array (prod κt νt))] (hashMap κt νt) -- Std.HashMap.ofArray
  | lean_hash_map_fold : (κt νt γt : MyTy) → HashMapExtern [(fn2 γt κt (fn1 νt γt)), γt, (hashMap κt νt)] γt -- Std.HashMap.fold (order)
  | lean_hash_map_filter : (κt νt : MyTy) → HashMapExtern [(fn2 κt νt LeanPrimTy.bool), (hashMap κt νt)] (hashMap κt νt) -- Std.HashMap.filter
  | lean_hash_map_filter_map : (κt νt γt : MyTy) → HashMapExtern [(fn2 κt νt (option γt)), (hashMap κt νt)] (hashMap κt γt) -- Std.HashMap.filterMap
  | lean_hash_map_map : (κt νt γt : MyTy) → HashMapExtern [(fn2 κt νt γt), (hashMap κt νt)] (hashMap κt γt) -- Std.HashMap.map
  | lean_hash_map_modify : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, (fn1 νt νt)] (hashMap κt νt) -- Std.HashMap.modify
  | lean_hash_map_alter : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), κt, (fn1 (option νt) (option νt))] (hashMap κt νt) -- Std.HashMap.alter
  | lean_hash_map_insert_many_list : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), (list (prod κt νt))] (hashMap κt νt) -- Std.HashMap.insertMany (of a `List`)
  | lean_hash_map_insert_many_array : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), (array (prod κt νt))] (hashMap κt νt) -- Std.HashMap.insertMany (of an `Array`)
  | lean_hash_map_all : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt), (fn2 κt νt LeanPrimTy.bool)] LeanPrimTy.bool -- Std.HashMap.all
  | lean_hash_map_any : (κt νt : MyTy) → HashMapExtern [(hashMap κt νt), (fn2 κt νt LeanPrimTy.bool)] LeanPrimTy.bool -- Std.HashMap.any
  | lean_hash_map_union : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), (hashMap κt νt)] (hashMap κt νt) -- Std.HashMap.union
  | lean_hash_map_inter : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), (hashMap κt νt)] (hashMap κt νt) -- Std.HashMap.inter
  | lean_hash_map_diff : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (hashMap κt νt), (hashMap κt νt)] (hashMap κt νt) -- Std.HashMap.diff
  | lean_hash_map_beq : (κt νt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (fn2 νt νt LeanPrimTy.bool), (hashMap κt νt), (hashMap κt νt)] LeanPrimTy.bool -- Std.HashMap.beq (the `BEq` of the values third)
  | lean_hash_map_partition : (κt νt : MyTy) → HashMapExtern [(fn2 κt νt LeanPrimTy.bool), (hashMap κt νt)] (prod (hashMap κt νt) (hashMap κt νt)) -- Std.HashMap.partition
  | lean_array_group_by_key : (κt βt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (fn1 βt κt), (array βt)] (hashMap κt (Coe.coe (array βt : LeanPrimTyCovariant MyTy) : MyTy)) -- Array.groupByKey
  | lean_list_group_by_key : (κt βt : MyTy) → HashMapExtern [(fn2 κt κt LeanPrimTy.bool), (fn1 κt uint64), (fn1 βt κt), (list βt)] (hashMap κt (Coe.coe (list βt : LeanPrimTyCovariant MyTy) : MyTy)) -- List.groupByKey
  -- | lean_hash_map_get : (κt νt : MyTy) → (m : …) → (k : …) → k ∈ m → HashMapExtern νt -- Std.HashMap.get (takes a proof: `m[k]` is `lean_hash_map_get_bang` with the `Inhabited` default)
  -- | lean_hash_map_get_key : (κt νt : MyTy) → (m : …) → (k : …) → k ∈ m → HashMapExtern κt -- Std.HashMap.getKey (takes a proof, as `Std.HashMap.get`)
  -- | lean_hash_map_fold_m -- Std.HashMap.foldM (monadic: in `Id` it is `fold`)
  -- | lean_hash_map_for_m -- Std.HashMap.forM (monadic)
  -- | lean_hash_map_for_in -- Std.HashMap.forIn (monadic: `for (k, v) in m` in `Id` is `fold`)
  -- | lean_hash_map_unit_of_list -- Std.HashMap.unitOfList (a `HashMap κ Unit` is a hash set: `Std.HashSet.ofList`)
  -- | lean_hash_map_unit_of_array -- Std.HashMap.unitOfArray (a hash set: `Std.HashSet.ofArray`)
  -- | lean_hash_map_insert_many_if_new_unit -- Std.HashMap.insertManyIfNewUnit (a hash set: `Std.HashSet.insertMany`)
  -- | lean_hash_map_num_buckets -- Std.HashMap.Internal.numBuckets (a detail of the layout)

end LeanScript

end
