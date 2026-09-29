module

public import LeanScript.Term.Extern.Catalogue

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs: the array functions written in Lean

The value of every entry of `ArrayStdExtern`
(`LeanScript.LeanInitPureExterns.ArrayStdFunctionsNonExternButBigEnoughToLoseInformation`), at
the instantiation of the catalogue to the types of the language (`LeanScript.Extern`), on the
values of its arguments: the Lean function the entry stands for, so an entry means exactly
what the Lean function means.  A `[BEq α]` argument is given as its function `beq`
(`⟨beq⟩` is the instance).
-/

namespace LeanScript

/-- The value of an entry of `ArrayStdExtern` on the values of its arguments. -/
def ArrayStdExtern.eval {ks : List Nat} (E : Ref ks → Type) : {σs : List (Ty ks)} → {τ : Ty ks} →
    ArrayStdExtern (MyTy := Ty ks) (fun t => Ty.option t) (fun a b => Ty.fn a b) Ty.fn2 Ty.pair σs τ →
    DenList E σs → Ty.den E τ
  | _, _, (.lean_array_append αt), (x1, x2) =>
    let x1 : Array (Ty.den E αt) := x1
    let x2 : Array (Ty.den E αt) := x2
    (Array.append x1 x2 : Array (Ty.den E αt))
  | _, _, (.lean_array_map αt βt), (f, xs) =>
    let f : Ty.den E αt → Ty.den E βt := f
    let xs : Array (Ty.den E αt) := xs
    (Array.map f xs : Array (Ty.den E βt))
  | _, _, (.lean_array_filter αt), (p, xs, start, stop) =>
    let p : Ty.den E αt → Bool := p
    let xs : Array (Ty.den E αt) := xs
    let start : Nat := start
    let stop : Nat := stop
    (Array.filter p xs start stop : Array (Ty.den E αt))
  | _, _, (.lean_array_flat_map αt βt), (f, xs) =>
    let f : Ty.den E αt → Array (Ty.den E βt) := f
    let xs : Array (Ty.den E αt) := xs
    (Array.flatMap f xs : Array (Ty.den E βt))
  | _, _, (.lean_array_flatten αt), xss =>
    let xss : Array (Array (Ty.den E αt)) := xss
    (Array.flatten xss : Array (Ty.den E αt))
  | _, _, (.lean_array_reverse αt), xs =>
    let xs : Array (Ty.den E αt) := xs
    (Array.reverse xs : Array (Ty.den E αt))
  | _, _, (.lean_array_extract αt), (xs, start, stop) =>
    let xs : Array (Ty.den E αt) := xs
    let start : Nat := start
    let stop : Nat := stop
    (Array.extract xs start stop : Array (Ty.den E αt))
  | _, _, (.lean_array_any αt), (xs, p, start, stop) =>
    let xs : Array (Ty.den E αt) := xs
    let p : Ty.den E αt → Bool := p
    let start : Nat := start
    let stop : Nat := stop
    (Array.any xs p start stop : Bool)
  | _, _, (.lean_array_all αt), (xs, p, start, stop) =>
    let xs : Array (Ty.den E αt) := xs
    let p : Ty.den E αt → Bool := p
    let start : Nat := start
    let stop : Nat := stop
    (Array.all xs p start stop : Bool)
  | _, _, (.lean_array_contains αt), (beq, xs, a) =>
    let beq : Ty.den E αt → Ty.den E αt → Bool := beq
    let xs : Array (Ty.den E αt) := xs
    let a : Ty.den E αt := a
    (@Array.contains _ ⟨beq⟩ xs a : Bool)
  | _, _, (.lean_array_find_opt αt), (p, xs) =>
    let p : Ty.den E αt → Bool := p
    let xs : Array (Ty.den E αt) := xs
    (Array.find? p xs : Option (Ty.den E αt))
  | _, _, (.lean_array_find_idx_opt αt), (p, xs) =>
    let p : Ty.den E αt → Bool := p
    let xs : Array (Ty.den E αt) := xs
    (Array.findIdx? p xs : Option Nat)
  | _, _, (.lean_array_idx_of_opt αt), (beq, xs, a) =>
    let beq : Ty.den E αt → Ty.den E αt → Bool := beq
    let xs : Array (Ty.den E αt) := xs
    let a : Ty.den E αt := a
    (@Array.idxOf? _ ⟨beq⟩ xs a : Option Nat)
  | _, _, (.lean_array_erase_idx αt), (xs, i) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    (Array.eraseIdx! xs i : Array (Ty.den E αt))
  | _, _, (.lean_array_insert_idx αt), (xs, i, a) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    let a : Ty.den E αt := a
    (Array.insertIdx! xs i a : Array (Ty.den E αt))
  | _, _, (.lean_array_erase_idx_if_in_bounds αt), (xs, i) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    (Array.eraseIdxIfInBounds xs i : Array (Ty.den E αt))
  | _, _, (.lean_array_insert_idx_if_in_bounds αt), (xs, i, a) =>
    let xs : Array (Ty.den E αt) := xs
    let i : Nat := i
    let a : Ty.den E αt := a
    (Array.insertIdxIfInBounds xs i a : Array (Ty.den E αt))
  | _, _, (.lean_array_qsort αt), (xs, lt, lo, hi) =>
    let xs : Array (Ty.den E αt) := xs
    let lt : Ty.den E αt → Ty.den E αt → Bool := lt
    let lo : Nat := lo
    let hi : Nat := hi
    (Array.qsort xs lt lo hi : Array (Ty.den E αt))
  | _, _, (.lean_array_foldr αt βt), (f, z, xs, start, stop) =>
    let f : Ty.den E αt → Ty.den E βt → Ty.den E βt := f
    let z : Ty.den E βt := z
    let xs : Array (Ty.den E αt) := xs
    let start : Nat := start
    let stop : Nat := stop
    (Array.foldr f z xs start stop : Ty.den E βt)
  | _, _, (.lean_array_zip_with αt βt γt), (f, xs, ys) =>
    let f : Ty.den E αt → Ty.den E βt → Ty.den E γt := f
    let xs : Array (Ty.den E αt) := xs
    let ys : Array (Ty.den E βt) := ys
    (Array.zipWith f xs ys : Array (Ty.den E γt))
  | _, _, (.lean_array_zip αt βt), (xs, ys) =>
    let xs : Array (Ty.den E αt) := xs
    let ys : Array (Ty.den E βt) := ys
    (Array.zip xs ys : Array (Ty.den E αt × Ty.den E βt))
  | _, _, (.lean_array_back_opt αt), xs =>
    let xs : Array (Ty.den E αt) := xs
    (Array.back? xs : Option (Ty.den E αt))
  | _, _, (.lean_array_count_p αt), (p, xs) =>
    let p : Ty.den E αt → Bool := p
    let xs : Array (Ty.den E αt) := xs
    (Array.countP p xs : Nat)
  | _, _, (.lean_list_append αt), (x1, x2) =>
    let x1 : List (Ty.den E αt) := x1
    let x2 : List (Ty.den E αt) := x2
    (List.append x1 x2 : List (Ty.den E αt))

end LeanScript

end
