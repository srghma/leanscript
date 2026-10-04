module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the hash maps with string keys

The value of every entry of `StrMapExtern` (`LeanScript.LeanInitPureExterns.StrMap`), at the
instantiation of the catalogue to the types of the language (`LeanScript.Extern`), on the
values of its arguments: the function of `Std.HashMap` the entry stands for, at the keys
`String` (with `String`'s own `BEq` and `Hashable` instances, the ones of `Ty.den` of
`Ty.strMap`), so an entry means exactly what the Lean function means.  The default value of
`get!` is its first argument (`⟨d⟩` is the `Inhabited` instance).
-/

namespace LeanScript

/-- The value of an entry of `StrMapExtern` on the values of its arguments. -/
def StrMapExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    StrMapExtern (MyTy := Ty ks) (fun t => Ty.option t) Ty.pair σs τ →
    DenList E σs → Ty.den E τ
  | _, _, (.lean_str_map_empty_with_capacity νt), c =>
    let c : Nat := c
    (Std.HashMap.emptyWithCapacity c : Std.HashMap String (Ty.den E νt))
  | _, _, (.lean_str_map_insert νt), (m, k, v) =>
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    let v : Ty.den E νt := v
    (m.insert k v : Std.HashMap String (Ty.den E νt))
  | _, _, (.lean_str_map_erase νt), (m, k) =>
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    (m.erase k : Std.HashMap String (Ty.den E νt))
  | _, _, (.lean_str_map_get_opt νt), (m, k) =>
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    (m.get? k : Option (Ty.den E νt))
  | _, _, (.lean_str_map_contains νt), (m, k) =>
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    (m.contains k : Bool)
  | _, _, (.lean_str_map_get_d νt), (m, k, d) =>
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    let d : Ty.den E νt := d
    (m.getD k d : Ty.den E νt)
  | _, _, (.lean_str_map_get_bang νt), (d, m, k) =>
    let d : Ty.den E νt := d
    let m : Std.HashMap String (Ty.den E νt) := m
    let k : String := k
    (@Std.HashMap.get! String (Ty.den E νt) _ _ ⟨d⟩ m k : Ty.den E νt)
  | _, _, (.lean_str_map_size νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.size : Nat)
  | _, _, (.lean_str_map_is_empty νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.isEmpty : Bool)
  | _, _, (.lean_str_map_keys νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.keys : List String)
  | _, _, (.lean_str_map_keys_array νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.keysArray : Array String)
  | _, _, (.lean_str_map_values νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.values : List (Ty.den E νt))
  | _, _, (.lean_str_map_values_array νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.valuesArray : Array (Ty.den E νt))
  | _, _, (.lean_str_map_to_list νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.toList : List (String × Ty.den E νt))
  | _, _, (.lean_str_map_to_array νt), m =>
    let m : Std.HashMap String (Ty.den E νt) := m
    (m.toArray : Array (String × Ty.den E νt))
  | _, _, (.lean_str_map_of_list νt), l =>
    let l : List (String × Ty.den E νt) := l
    (Std.HashMap.ofList l : Std.HashMap String (Ty.den E νt))

end LeanScript

end
