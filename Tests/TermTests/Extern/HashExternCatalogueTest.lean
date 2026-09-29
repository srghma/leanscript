module

public import LeanScript.LeanInitPureExterns.HashMap
public import LeanScript.LeanInitPureExterns.HashSet
public import LeanScript.Term.Extern.Catalogue
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

set_option autoImplicit false

/-!
# The catalogue families of `Std.HashMap` and `Std.HashSet`

* Every entry of `HashMapExtern` / `HashSetExtern` names a Lean function; the examples below
  check that each of these functions exists and takes its arguments in the order of the
  entry's signature (at keys `String` and values `Nat`), with the key's `BEq.beq` and
  `Hashable.hash` in front for the entries that take them.
* The families can be instantiated at the types of the language (`Ty []`), through the
  coercion `Ty.ofCovariant`.
-/

namespace HashExternCatalogueTest

open LeanScript

abbrev M := Std.HashMap String Nat
abbrev S := Std.HashSet String
abbrev Beq := String → String → Bool
abbrev Hash := String → UInt64

/-! ## `Std.HashMap`: the entries' argument order is the Lean function's -/

example : Beq → Hash → Nat → M := fun _ _ c => Std.HashMap.emptyWithCapacity c
example : Beq → Hash → M → String → Nat → M := fun _ _ => Std.HashMap.insert
example : Beq → Hash → M → String → Nat → M := fun _ _ => Std.HashMap.insertIfNew
example : Beq → Hash → M → String → Nat → Bool × M := fun _ _ => Std.HashMap.containsThenInsert
example : Beq → Hash → M → String → Nat → Bool × M := fun _ _ => Std.HashMap.containsThenInsertIfNew
example : Beq → Hash → M → String → Nat → Option Nat × M := fun _ _ => Std.HashMap.getThenInsertIfNew?
example : Beq → Hash → M → String → Option Nat := fun _ _ => Std.HashMap.get?
example : Beq → Hash → M → String → Bool := fun _ _ => Std.HashMap.contains
example : Beq → Hash → M → String → Nat → Nat := fun _ _ => Std.HashMap.getD
example : Nat → Beq → Hash → M → String → Nat := fun d _ _ m k => (m.get? k).getD d
example : M → String → Nat := Std.HashMap.get!
example : Beq → Hash → M → String → Option String := fun _ _ => Std.HashMap.getKey?
example : Beq → Hash → M → String → String → String := fun _ _ => Std.HashMap.getKeyD
example : M → String → String := Std.HashMap.getKey!
example : Beq → Hash → M → String → M := fun _ _ => Std.HashMap.erase
example : M → Nat := Std.HashMap.size
example : M → Bool := Std.HashMap.isEmpty
example : M → List String := Std.HashMap.keys
example : M → Array String := Std.HashMap.keysArray
example : M → List Nat := Std.HashMap.values
example : M → Array Nat := Std.HashMap.valuesArray
example : M → List (String × Nat) := Std.HashMap.toList
example : M → Array (String × Nat) := Std.HashMap.toArray
example : Beq → Hash → List (String × Nat) → M := fun _ _ => Std.HashMap.ofList
example : Beq → Hash → Array (String × Nat) → M := fun _ _ => Std.HashMap.ofArray
example : (Int → String → Nat → Int) → Int → M → Int := Std.HashMap.fold
example : (String → Nat → Bool) → M → M := Std.HashMap.filter
example : (String → Nat → Option Int) → M → Std.HashMap String Int := Std.HashMap.filterMap
example : (String → Nat → Int) → M → Std.HashMap String Int := Std.HashMap.map
example : Beq → Hash → M → String → (Nat → Nat) → M := fun _ _ => Std.HashMap.modify
example : Beq → Hash → M → String → (Option Nat → Option Nat) → M := fun _ _ => Std.HashMap.alter
example : Beq → Hash → M → List (String × Nat) → M := fun _ _ => Std.HashMap.insertMany
example : Beq → Hash → M → Array (String × Nat) → M := fun _ _ => Std.HashMap.insertMany
example : M → (String → Nat → Bool) → Bool := Std.HashMap.all
example : M → (String → Nat → Bool) → Bool := Std.HashMap.any
example : Beq → Hash → M → M → M := fun _ _ => Std.HashMap.union
example : Beq → Hash → M → M → M := fun _ _ => Std.HashMap.inter
example : Beq → Hash → M → M → M := fun _ _ => Std.HashMap.diff
example : Beq → Hash → (Nat → Nat → Bool) → M → M → Bool := fun _ _ _ => Std.HashMap.beq
example : (String → Nat → Bool) → M → M × M := Std.HashMap.partition
example : Beq → Hash → (Nat → String) → Array Nat → Std.HashMap String (Array Nat) :=
  fun _ _ => Array.groupByKey
example : Beq → Hash → (Nat → String) → List Nat → Std.HashMap String (List Nat) :=
  fun _ _ => List.groupByKey

/-! ## `Std.HashSet`: the entries' argument order is the Lean function's -/

example : Beq → Hash → Nat → S := fun _ _ c => Std.HashSet.emptyWithCapacity c
example : Beq → Hash → S → String → S := fun _ _ => Std.HashSet.insert
example : Beq → Hash → S → String → Bool × S := fun _ _ => Std.HashSet.containsThenInsert
example : Beq → Hash → S → String → Bool := fun _ _ => Std.HashSet.contains
example : Beq → Hash → S → String → S := fun _ _ => Std.HashSet.erase
example : S → Nat := Std.HashSet.size
example : S → Bool := Std.HashSet.isEmpty
example : Beq → Hash → S → String → Option String := fun _ _ => Std.HashSet.get?
example : Beq → Hash → S → String → String → String := fun _ _ => Std.HashSet.getD
example : S → String → String := Std.HashSet.get!
example : S → List String := Std.HashSet.toList
example : S → Array String := Std.HashSet.toArray
example : Beq → Hash → List String → S := fun _ _ => Std.HashSet.ofList
example : Beq → Hash → Array String → S := fun _ _ => Std.HashSet.ofArray
example : (Nat → String → Nat) → Nat → S → Nat := Std.HashSet.fold
example : (String → Bool) → S → S := Std.HashSet.filter
example : Beq → Hash → S → List String → S := fun _ _ => Std.HashSet.insertMany
example : Beq → Hash → S → Array String → S := fun _ _ => Std.HashSet.insertMany
example : S → (String → Bool) → Bool := Std.HashSet.all
example : S → (String → Bool) → Bool := Std.HashSet.any
example : Beq → Hash → S → S → S := fun _ _ => Std.HashSet.union
example : Beq → Hash → S → S → S := fun _ _ => Std.HashSet.inter
example : Beq → Hash → S → S → S := fun _ _ => Std.HashSet.diff
example : Beq → Hash → S → S → Bool := fun _ _ => Std.HashSet.beq
example : (String → Bool) → S → S × S := Std.HashSet.partition

/-! ## The families at the types of the language -/

/-- `HashMapExtern`, at `Ty []`. -/
abbrev TyHashMapExtern : List (Ty []) → Ty [] → Type :=
  HashMapExtern (MyTy := Ty []) (fun t => Ty.option t) (fun a b => Ty.fn a b) Ty.fn2 Ty.pair

/-- `HashSetExtern`, at `Ty []`. -/
abbrev TyHashSetExtern : List (Ty []) → Ty [] → Type :=
  HashSetExtern (MyTy := Ty []) (fun t => Ty.option t) (fun a b => Ty.fn a b) Ty.fn2 Ty.pair

example : TyHashMapExtern
    [Ty.fn2 (.prim .string) (.prim .string) (.prim .bool), .fn (.prim .string) (.prim .uint64),
     Ty.ofCovariant (.hashMap (.prim .string) (.prim .nat)), .prim .string]
    (Ty.option (.prim .nat)) :=
  .lean_hash_map_get_opt (Ty.prim .string) (Ty.prim .nat)

example : TyHashSetExtern [Ty.ofCovariant (.hashSet (.prim .string))] (.prim .nat) :=
  .lean_hash_set_size (Ty.prim .string)

/-! ## Object keys -/

example : LeanPrimTy.isObjectKey .string = true := rfl
example : LeanPrimTy.isObjectKey .nat = true := rfl
example : LeanPrimTy.isObjectKey .substringRaw = false := rfl
example : (LeanPrimTyCovariant.hashMap 1 2).map (· + 1) = .hashMap 2 3 := rfl
example : (LeanPrimTyCovariant.hashMap 1 2).children = [1, 2] := rfl

end HashExternCatalogueTest

end
