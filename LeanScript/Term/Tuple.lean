module

public import LeanScript.Term.DeBruijn

@[expose] public section

set_option autoImplicit false

/-!
# Tuples without a trailing `PUnit`

`Tuple F [a₁, …, aₙ]` is `F a₁ × … × F aₙ`, nested to the right, with no `PUnit` at the end:

* `Tuple F [] = PUnit`,
* `Tuple F [a] = F a`,
* `Tuple F [a, b] = F a × F b`, `Tuple F [a, b, c] = F a × F b × F c`, …

It is what environments (`LeanScript.Env`), the arguments of an extern
(`LeanScript.Comp.extern`) and the closures of the join points in scope (`LeanScript.JEnv`)
are made of.  Because the shape of a tuple depends on whether the tail of the list is empty,
a tuple is taken apart with `Tuple.head`/`Tuple.tail` and built with `Tuple.cons` rather than
with `Prod.fst`/`Prod.snd`/`Prod.mk` whenever the list is not known.
-/

namespace LeanScript

/-- **A tuple**: one value of `F a` for every `a` in the list, as a right-nested product with no
    trailing `PUnit` (`Tuple F [a, b] = F a × F b`). -/
def Tuple {α : Type} (F : α → Type) : List α → Type
  | [] => PUnit
  | [a] => F a
  | a :: b :: as => F a × Tuple F (b :: as)

namespace Tuple
variable {α : Type} {F : α → Type}

/-- The empty tuple. -/
abbrev nil : Tuple F [] := PUnit.unit

/-- Put a value in front of a tuple. -/
def cons : {a : α} → {as : List α} → F a → Tuple F as → Tuple F (a :: as)
  | _, [], x, _ => x
  | _, _ :: _, x, xs => (x, xs)

/-- The first value of a tuple. -/
def head : {a : α} → {as : List α} → Tuple F (a :: as) → F a
  | _, [], x => x
  | _, _ :: _, x => x.1

/-- A tuple without its first value. -/
def tail : {a : α} → {as : List α} → Tuple F (a :: as) → Tuple F as
  | _, [], _ => PUnit.unit
  | _, _ :: _, x => x.2

@[simp] theorem head_cons {a : α} {as : List α} (x : F a) (xs : Tuple F as) :
    (cons x xs).head = x := by
  cases as <;> rfl

@[simp] theorem tail_cons {a : α} {as : List α} (x : F a) (xs : Tuple F as) :
    (cons x xs).tail = xs := by
  cases as
  · rfl
  · rfl

@[simp] theorem cons_head_tail {a : α} {as : List α} (x : Tuple F (a :: as)) :
    cons x.head x.tail = x := by
  cases as <;> rfl

/-- Two tuples with the same head and tail are equal. -/
theorem ext {a : α} {as : List α} {x y : Tuple F (a :: as)} (h₁ : x.head = y.head)
    (h₂ : x.tail = y.tail) : x = y := by
  rw [← cons_head_tail x, ← cons_head_tail y, h₁, h₂]

/-- The value at a position. -/
def get : {as : List α} → {a : α} → Tuple F as → DeBruijn as a → F a
  | _ :: _, _, x, .head => x.head
  | _ :: _, _, x, .tail i => get x.tail i

@[simp] theorem get_head {a : α} {as : List α} (x : Tuple F (a :: as)) :
    x.get .head = x.head := rfl

@[simp] theorem get_tail {a b : α} {as : List α} (x : Tuple F (b :: as)) (i : DeBruijn as a) :
    x.get (.tail i) = x.tail.get i := rfl

@[simp] theorem get_cons_head {a : α} {as : List α} (x : F a) (xs : Tuple F as) :
    (cons x xs).get .head = x := head_cons x xs

@[simp] theorem get_cons_tail {a b : α} {as : List α} (x : F b) (xs : Tuple F as)
    (i : DeBruijn as a) : (cons x xs).get (.tail i) = xs.get i := by
  rw [get_tail, tail_cons]

/-- Put a tuple in front of another. -/
def append : {as : List α} → {bs : List α} → Tuple F as → Tuple F bs → Tuple F (as ++ bs)
  | [], _, _, y => y
  | _ :: _, _, x, y => cons x.head (append x.tail y)

@[simp] theorem append_nil {bs : List α} (x : Tuple F []) (y : Tuple F bs) :
    append x y = y := rfl

theorem append_cons {a : α} {as bs : List α} (x : Tuple F (a :: as)) (y : Tuple F bs) :
    append x y = cons x.head (append x.tail y) := rfl

end Tuple

end LeanScript

end
