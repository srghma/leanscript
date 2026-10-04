module
prelude
public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.LeanPrimTyCovariant
set_option autoImplicit false
@[expose] public section
namespace LeanScript

/-!
# The catalogue of pure externs: the functions of `Std.HashMap String ν`

One part of the catalogue `LeanScript.LeanInitPureExtern` (see `LeanScript.LeanInitPureExterns`
for how it is organised).

A hash map whose keys are strings, compared and hashed by `String`'s own instances, is a type
of the language (`Ty.strMap`, read from `Std.HashMap String ν`): the backend writes it as a
JavaScript object whose own properties are the keys.  No function of `Std.HashMap` is
`@[extern]` (each is Lean code that hashes the key, indexes the array of buckets and walks an
association list), so each one the backend knows has an entry here, which keeps the
information *which* function was called:

| JavaScript | Lean | entry |
| :--- | :--- | :--- |
| `{}` | `Std.HashMap.emptyWithCapacity`, `∅`, `{}` | `lean_str_map_empty_with_capacity` |
| `({ ...m, [k]: v })` | `Std.HashMap.insert` | `lean_str_map_insert` |
| a copy without `k` | `Std.HashMap.erase` | `lean_str_map_erase` |
| `Object.hasOwn(m, k) ? some(m[k]) : none` | `Std.HashMap.get?`, `m[k]?` | `lean_str_map_get_opt` |
| `Object.hasOwn(m, k)` | `Std.HashMap.contains`, `k ∈ m` | `lean_str_map_contains` |
| `m[k] ?? d` | `Std.HashMap.getD` | `lean_str_map_get_d` |
| `m[k] ?? d` | `Std.HashMap.get!`, `m[k]!` | `lean_str_map_get_bang` |
| `Object.keys(m).length` | `Std.HashMap.size` | `lean_str_map_size` |
| `Object.keys(m).length === 0` | `Std.HashMap.isEmpty` | `lean_str_map_is_empty` |
| `Object.keys(m)` | `Std.HashMap.keys`, `Std.HashMap.keysArray` | `lean_str_map_keys`, `lean_str_map_keys_array` |
| `Object.values(m)` | `Std.HashMap.values`, `Std.HashMap.valuesArray` | `lean_str_map_values`, `lean_str_map_values_array` |
| the entries, as pairs | `Std.HashMap.toList`, `Std.HashMap.toArray` | `lean_str_map_to_list`, `lean_str_map_to_array` |
| an object of the pairs | `Std.HashMap.ofList` | `lean_str_map_of_list` |

**Instances.**  The `BEq` and `Hashable` instances of the key are `String`'s own (the type
`Ty.strMap` is only read from such a hash map), so the entries do not take them.

**Order.**  The order of `keys`, `keysArray`, `values`, `valuesArray`, `toList` and `toArray` is,
in Lean, the order of the buckets (it depends on the hashes and on the history of the map); in
JavaScript it is the order of the properties of the object (the integer-like keys first, in
increasing order, then the others in insertion order).  The meaning of an entry
(`LeanScript.Extern.eval`) is Lean's; the JavaScript of these six lists the same entries, in the
object's order.

**Panics.**  `get!` panics when the key is missing; the value of a panic is the default of the
type, given as the first argument (as for `lean_array_get`).

The meaning of each entry is the Lean function in its comment
(`LeanScript.Term.Extern.Eval.StrMap`), so an entry cannot change the value of a program.
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

/-- `Std.HashMap String νt`, as a type of the grammar (the former `LeanPrimTyCovariant.hashMap`
    at the key `string`; `Ty.ofCovariant` sends it to `Ty.strMap νt`). -/
local notation "strMapT " νt => (Coe.coe (hashMap (Coe.coe LeanPrimTy.string : MyTy) νt : LeanPrimTyCovariant MyTy) : MyTy)

------------------------------------------------------------------------------
-- Std/Data/HashMap/Basic.lean: the hash maps with string keys
------------------------------------------------------------------------------
/-- The functions of `Std.HashMap String ν` that the backend knows (none is `@[extern]`, see
    the module doc).  `νt` is the type of the values. -/
inductive StrMapExtern : List MyTy → MyTy → Type where
  | lean_str_map_empty_with_capacity : (νt : MyTy) → StrMapExtern [nat] (strMapT νt) -- Std.HashMap.emptyWithCapacity
  | lean_str_map_insert : (νt : MyTy) → StrMapExtern [(strMapT νt), string, νt] (strMapT νt) -- Std.HashMap.insert
  | lean_str_map_erase : (νt : MyTy) → StrMapExtern [(strMapT νt), string] (strMapT νt) -- Std.HashMap.erase
  | lean_str_map_get_opt : (νt : MyTy) → StrMapExtern [(strMapT νt), string] (option νt) -- Std.HashMap.get?
  | lean_str_map_contains : (νt : MyTy) → StrMapExtern [(strMapT νt), string] LeanPrimTy.bool -- Std.HashMap.contains
  | lean_str_map_get_d : (νt : MyTy) → StrMapExtern [(strMapT νt), string, νt] νt -- Std.HashMap.getD
  | lean_str_map_get_bang : (νt : MyTy) → StrMapExtern [νt, (strMapT νt), string] νt -- Std.HashMap.get!
  | lean_str_map_size : (νt : MyTy) → StrMapExtern [(strMapT νt)] nat -- Std.HashMap.size
  | lean_str_map_is_empty : (νt : MyTy) → StrMapExtern [(strMapT νt)] LeanPrimTy.bool -- Std.HashMap.isEmpty
  | lean_str_map_keys : (νt : MyTy) → StrMapExtern [(strMapT νt)] (list (Coe.coe LeanPrimTy.string : MyTy)) -- Std.HashMap.keys
  | lean_str_map_keys_array : (νt : MyTy) → StrMapExtern [(strMapT νt)] (array (Coe.coe LeanPrimTy.string : MyTy)) -- Std.HashMap.keysArray
  | lean_str_map_values : (νt : MyTy) → StrMapExtern [(strMapT νt)] (list νt) -- Std.HashMap.values
  | lean_str_map_values_array : (νt : MyTy) → StrMapExtern [(strMapT νt)] (array νt) -- Std.HashMap.valuesArray
  | lean_str_map_to_list : (νt : MyTy) → StrMapExtern [(strMapT νt)] (list (prod string νt)) -- Std.HashMap.toList
  | lean_str_map_to_array : (νt : MyTy) → StrMapExtern [(strMapT νt)] (array (prod string νt)) -- Std.HashMap.toArray
  | lean_str_map_of_list : (νt : MyTy) → StrMapExtern [(list (prod string νt))] (strMapT νt) -- Std.HashMap.ofList

end LeanScript

end
