module

@[expose] public section

set_option autoImplicit false

/-!
# Typed de Bruijn indices

`DeBruijn xs x` is constructive evidence that `x` occurs in the list `xs`, together with
*where*: `head` is the entry just bound, `tail v` an entry bound further out.  The variables
of a term (`LeanScript.Var`) are the instance `xs := Γ`, a context of types.

Renamings (`DeBruijn.Ren`) are the maps between the positions of two lists that preserve
the entry; they are what `LeanScript.Term.rename` acts by.
-/

namespace LeanScript

/-- **A typed de Bruijn index**: constructive evidence that `x` occurs in `xs`, and where. -/
inductive DeBruijn {α : Type} : List α → α → Type where
  /-- The entry just bound. -/
  | head {x : α} {xs : List α} : DeBruijn (x :: xs) x
  /-- An entry bound further out. -/
  | tail {x y : α} {xs : List α} : DeBruijn xs x → DeBruijn (y :: xs) x
  deriving Repr

namespace DeBruijn
variable {α : Type}

/-- How many binders out an index is. -/
def index : {xs : List α} → {x : α} → DeBruijn xs x → Nat
  | _, _, .head => 0
  | _, _, .tail v => v.index + 1

/-- The entry an index points at is one of the entries. -/
theorem mem : {xs : List α} → {x : α} → DeBruijn xs x → x ∈ xs
  | _, _, .head => List.mem_cons_self
  | _, _, .tail v => List.mem_cons_of_mem _ v.mem

/-- The index is a position of the list. -/
theorem index_lt : {xs : List α} → {x : α} → (v : DeBruijn xs x) → v.index < xs.length
  | _, _, .head => by simp [index]
  | _, _, .tail v => by simp [index, v.index_lt]

/-- The entry at the position of an index is the entry it was built for. -/
theorem getElem_index : {xs : List α} → {x : α} → (v : DeBruijn xs x) →
    xs[v.index]'v.index_lt = x
  | _, _, .head => rfl
  | _, _, .tail v => by simpa [index] using v.getElem_index

/-- Two indices into the same list at the same position are equal. -/
theorem eq_of_index_eq : {xs : List α} → {x : α} → (v w : DeBruijn xs x) →
    v.index = w.index → v = w
  | _, _, .head, .head, _ => rfl
  | _, _, .tail v, .tail w, h => by
      rw [eq_of_index_eq v w (by simpa [index] using h)]
  | _, _, .head, .tail _, h => by simp [index] at h
  | _, _, .tail _, .head, h => by simp [index] at h

/-- The index at position `i`, given that the entry there is `x`.  With a concrete position
    the side condition is closed by `rfl`: `DeBruijn.ofIndex [a, b, c] 2 rfl : DeBruijn _ c`. -/
def ofIndex : (xs : List α) → (i : Nat) → {x : α} → xs[i]? = some x → DeBruijn xs x
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by cases h; exact .head
  | _ :: xs, i + 1, _, h => .tail (ofIndex xs i h)

/-- `ofIndex` points at the position it was given. -/
theorem index_ofIndex : (xs : List α) → (i : Nat) → {x : α} → (h : xs[i]? = some x) →
    (ofIndex xs i h).index = i
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by cases h; rfl
  | _ :: xs, i + 1, _, h => by simp [ofIndex, index, index_ofIndex xs i h]

/-- Two indices into the same list are equal exactly when they are at the same position. -/
instance {xs : List α} {x : α} : DecidableEq (DeBruijn xs x) := fun v w =>
  if h : v.index = w.index then isTrue (eq_of_index_eq v w h)
  else isFalse (fun e => h (e ▸ rfl))

instance {xs : List α} {x : α} : BEq (DeBruijn xs x) := instBEqOfDecidableEq

example {xs : List α} {x : α} : LawfulBEq (DeBruijn xs x) := inferInstance

/-- A renaming from the positions of `xs` to those of `ys` that preserves the entries. -/
abbrev Ren (xs ys : List α) : Type := ∀ {x : α}, DeBruijn xs x → DeBruijn ys x

namespace Ren

/-- The renaming into a list with one more (innermost) entry. -/
abbrev weaken {xs : List α} {y : α} : Ren xs (y :: xs) := fun v => .tail v

/-- A renaming under one more binder. -/
def lift {xs ys : List α} {y : α} (r : Ren xs ys) : Ren (y :: xs) (y :: ys)
  | _, .head => .head
  | _, .tail v => .tail (r v)

/-- A renaming under the binders `zs`. -/
def liftN {xs ys : List α} (r : Ren xs ys) : (zs : List α) → Ren (zs ++ xs) (zs ++ ys)
  | [], _, v => r v
  | _ :: zs, _, .head => .head
  | _ :: zs, _, .tail v => .tail (liftN r zs v)

/-- The renaming that skips the prefix `zs`. -/
def skip {xs : List α} : (zs : List α) → Ren xs (zs ++ xs)
  | [], _, v => v
  | _ :: zs, _, v => .tail (skip zs v)

end Ren

end DeBruijn

end LeanScript

end
