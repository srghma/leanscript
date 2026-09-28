module

public import LeanScript.Ty.Syntax.LeanPrimTy
public import LeanScript.Ty.Syntax.LeanPrimTyCovariant
public import LeanScript.Ty.Syntax.EnumSchema

/-!
# Toy: `Ty.array` replaced by `Ty.cov (LeanPrimTyCovariant (Ty ks))`

Companion of `proposals/CovariantTyAssessment.md`.  Not part of the Lake build; check with

```
lake env lean proposals/CovTyToy.lean
```

(after `lake build LeanScript.LeanPrimTy LeanScript.LeanPrimTyCovariant LeanScript.EnumSchema`).

It checks the kernel/elaborator-level claims of the assessment on a trimmed copy of
`LeanScript/Ty/Syntax/Ty.lean` (`prim`, `fn`, `cov`, `record`/`Fields`; no `union`, `enum`, `data`):

1. the nested occurrence `LeanPrimTyCovariant (Ty ks)` inside the `mutual` block is accepted;
2. `DecidableEq` and `Repr` still derive;
3. a `@[match_pattern]` abbreviation `Ty.array` keeps every existing `.array t` pattern and
   constructor application working unchanged;
4. `Ty.map` / `Ty.map_id` stay structural;
5. `Ty.den` with `thunk ↦ Thunk`, `lazy ↦ Unit → _`;
6. the precise thing that breaks: `Ty.den (.cov (.thunk .bool))` has exactly two values,
   so `Ty.eq_bool_of_two_points` (in `LeanScript/Ty/Den/Three.lean`) would become false.
-/

@[expose] public section

set_option autoImplicit false

namespace CovTyToy
open LeanScript

mutual
inductive Ty : List Nat → Type where
  | prim {ks : List Nat} (p : LeanPrimTy) : Ty ks
  | fn {ks : List Nat} : Ty ks → Ty ks → Ty ks
  /-- `Array`, `Thunk` and `Unit → _`, through the shared former. -/
  | cov {ks : List Nat} : LeanPrimTyCovariant (Ty ks) → Ty ks
  | record {ks : List Nat} : Ty ks → Fields ks → Ty ks
inductive Fields : List Nat → Type where
  | one {ks : List Nat} : Ty ks → Fields ks
  | cons {ks : List Nat} : Ty ks → Fields ks → Fields ks
end

deriving instance Repr for Ty, Fields

/-! `deriving DecidableEq` is refused for this nested `mutual` block ("None of the deriving
handlers for class `DecidableEq` applied"), so it is written by hand, with the nested
occurrence handled by a third function of the `mutual` block. -/

mutual
def Ty.decEq {ks : List Nat} : (a b : Ty ks) → Decidable (a = b)
  | .prim p, .prim q =>
    if h : p = q then .isTrue (h ▸ rfl) else .isFalse (fun e => by cases e; exact h rfl)
  | .fn a b, .fn c d =>
    match Ty.decEq a c, Ty.decEq b d with
    | .isTrue h₁, .isTrue h₂ => .isTrue (h₁ ▸ h₂ ▸ rfl)
    | .isFalse h, _ => .isFalse (fun e => by cases e; exact h rfl)
    | _, .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .cov c, .cov d =>
    match Ty.covDecEq c d with
    | .isTrue h => .isTrue (h ▸ rfl)
    | .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .record a fs, .record b gs =>
    match Ty.decEq a b, Fields.decEq fs gs with
    | .isTrue h₁, .isTrue h₂ => .isTrue (h₁ ▸ h₂ ▸ rfl)
    | .isFalse h, _ => .isFalse (fun e => by cases e; exact h rfl)
    | _, .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .prim _, .fn _ _ | .prim _, .cov _ | .prim _, .record _ _
  | .fn _ _, .prim _ | .fn _ _, .cov _ | .fn _ _, .record _ _
  | .cov _, .prim _ | .cov _, .fn _ _ | .cov _, .record _ _
  | .record _ _, .prim _ | .record _ _, .fn _ _ | .record _ _, .cov _ =>
    .isFalse (fun e => by cases e)
def Ty.covDecEq {ks : List Nat} :
    (a b : LeanPrimTyCovariant (Ty ks)) → Decidable (a = b)
  | .array a, .array b | .thunk a, .thunk b | .lazy a, .lazy b =>
    match Ty.decEq a b with
    | .isTrue h => .isTrue (h ▸ rfl)
    | .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .array _, .thunk _ | .array _, .lazy _ | .thunk _, .array _
  | .thunk _, .lazy _ | .lazy _, .array _ | .lazy _, .thunk _ =>
    .isFalse (fun e => by cases e)
def Fields.decEq {ks : List Nat} : (a b : Fields ks) → Decidable (a = b)
  | .one a, .one b =>
    match Ty.decEq a b with
    | .isTrue h => .isTrue (h ▸ rfl)
    | .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .cons a fs, .cons b gs =>
    match Ty.decEq a b, Fields.decEq fs gs with
    | .isTrue h₁, .isTrue h₂ => .isTrue (h₁ ▸ h₂ ▸ rfl)
    | .isFalse h, _ => .isFalse (fun e => by cases e; exact h rfl)
    | _, .isFalse h => .isFalse (fun e => by cases e; exact h rfl)
  | .one _, .cons _ _ | .cons _ _, .one _ => .isFalse (fun e => by cases e)
end

instance {ks : List Nat} : DecidableEq (Ty ks) := Ty.decEq
instance {ks : List Nat} : DecidableEq (Fields ks) := Fields.decEq

/-- Every existing `.array t` keeps working, as a term and as a pattern. -/
@[match_pattern] abbrev Ty.array {ks : List Nat} (t : Ty ks) : Ty ks := .cov (.array t)
@[match_pattern] abbrev Ty.thunk {ks : List Nat} (t : Ty ks) : Ty ks := .cov (.thunk t)
@[match_pattern] abbrev Ty.lazy {ks : List Nat} (t : Ty ks) : Ty ks := .cov (.lazy t)
abbrev Ty.bool {ks : List Nat} : Ty ks := .prim .bool

example : (Ty.array (Ty.bool : Ty []) == .cov (.array .bool)) = true := by decide

mutual
def Ty.map {ks ks' : List Nat} : Ty ks → Ty ks'
  | .prim p => .prim p
  | .fn a b => .fn (Ty.map a) (Ty.map b)
  | .array t => .array (Ty.map t)
  | .thunk t => .thunk (Ty.map t)
  | .lazy t => .lazy (Ty.map t)
  | .record t fs => .record (Ty.map t) (Fields.map fs)
def Fields.map {ks ks' : List Nat} : Fields ks → Fields ks'
  | .one t => .one (Ty.map t)
  | .cons t fs => .cons (Ty.map t) (Fields.map fs)
end

mutual
theorem Ty.map_id {ks : List Nat} : (t : Ty ks) → Ty.map (ks' := ks) t = t
  | .prim _ => rfl
  | .fn a b => by simp only [Ty.map, Ty.map_id a, Ty.map_id b]
  | .array t => by simp only [Ty.map, Ty.map_id t]
  | .thunk t => by simp only [Ty.map, Ty.map_id t]
  | .lazy t => by simp only [Ty.map, Ty.map_id t]
  | .record t fs => by simp only [Ty.map, Ty.map_id t, Fields.map_id fs]
theorem Fields.map_id {ks : List Nat} : (fs : Fields ks) → Fields.map (ks' := ks) fs = fs
  | .one t => by simp only [Fields.map, Ty.map_id t]
  | .cons t fs => by simp only [Fields.map, Ty.map_id t, Fields.map_id fs]
end

mutual
def Ty.den {ks : List Nat} : Ty ks → Type
  | .prim p => p.denote
  | .fn a b => Ty.den a → Ty.den b
  | .array t => Array (Ty.den t)
  | .thunk t => Thunk (Ty.den t)
  | .lazy t => Unit → Ty.den t
  | .record t fs => Ty.den t × Fields.den fs
def Fields.den {ks : List Nat} : Fields ks → Type
  | .one t => Ty.den t
  | .cons t fs => Ty.den t × Fields.den fs
end

/-- What breaks: a delayed `Bool` is a second type of exactly two values. -/
theorem thunk_bool_two_points :
    ∀ x : Ty.den (Ty.thunk (Ty.bool : Ty [])),
      x = Thunk.pure true ∨ x = Thunk.pure false := by
  intro x
  obtain ⟨f⟩ := x
  show (⟨f⟩ : Thunk Bool) = ⟨fun _ => true⟩ ∨ (⟨f⟩ : Thunk Bool) = ⟨fun _ => false⟩
  cases h : f () with
  | true => left; congr; funext u; cases u; exact h
  | false => right; congr; funext u; cases u; exact h

theorem thunk_bool_ne_bool : Ty.thunk (Ty.bool : Ty []) ≠ Ty.bool := by decide

/-- The meaning still computes by `rfl` through the nested occurrence. -/
example : Ty.den (Ty.array (Ty.thunk Ty.bool) : Ty []) = Array (Thunk Bool) := rfl
example : Ty.den (Ty.lazy (Ty.array Ty.bool) : Ty []) = (Unit → Array Bool) := rfl
example : Ty.map (ks' := [0]) (Ty.array (Ty.lazy Ty.bool) : Ty []) = Ty.array (Ty.lazy Ty.bool) :=
  rfl

end CovTyToy
