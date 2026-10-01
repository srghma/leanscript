module

public import LeanScript.Ty.Den.Two
public import LeanScript.Term.Build
public import LeanScript.TacticElab.KernelRfl
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Constructor fields of a type of one value are erased

The language has no type of one value, but a constructor field of such a type carries no
information, so it is erased (`Gen.isOnePointField`).  Besides `Unit`/`PUnit` and structures
of such fields, a function type (dependent or not) whose result has one value is one too:
`Fin m → Unit`, `Unit → Fin 3 → Unit`, `(n : Nat) → Fin n → Unit × PUnit`.

So `node : (m : Nat) → (Fin m → Unit) → UF` keeps only `m`, and `UF` is read as `Ty.nat`.  A
type all of whose fields are erased this way still has one value and is refused.
-/

open LeanScript

namespace OnePointFieldTest

/-- The children `Fin m → Unit` are one value: erased, `UF` is `m`, a `Nat`. -/
inductive UF where
  | node : (m : Nat) → (Fin m → Unit) → UF

leanscript_signature Ok₁ where
  t := UF

example : Ok₁.t = Ty.nat := rfl

/-- A dependent function type into a structure of one value is erased too. -/
inductive UF₄ where
  | node : (m : Nat) → ((n : Nat) → Fin n → Unit × PUnit) → Bool → UF₄

leanscript_signature Ok₂ where
  t := UF₄

example : Ok₂.t = Ty.record .nat (.one .bool) := rfl

/-- Every field has one value: the type has one value, refused. -/
inductive UF₂ where
  | node : (m : Unit) → (Fin 3 → Unit) → UF₂

/--
error: LeanScript: the type
  UF₂
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₁ where
  t := UF₂

/-- `Unit → Fin 3 → Unit` has one value too: refused. -/
inductive UF₃ where
  | node : (m : Unit) → (Unit → Fin 3 → Unit) → UF₃

/--
error: LeanScript: the type
  UF₃
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₂ where
  t := UF₃

/-! ## Translating functions on `UF` -/

def UF.m : UF → Nat
  | .node m _ => m

/-- Reading the erased field: `f ⟨0, h⟩ : Unit` is matched on, its one branch is taken. -/
def UF.use : UF → Nat
  | .node m f => if h : 0 < m then (match f ⟨0, h⟩ with | () => m + 1) else 0

def ufv : UF := .node 3 (fun _ => ())

def ufMT := #leanscript_to_term UF.m
def ufUseT := #leanscript_to_term UF.use
def ufvT := #leanscript_to_term ufv

example : (ufMT (Δ := Ok₁.Δ)).run (ufvT (Δ := Ok₁.Δ)).run = (3 : Nat) := by kernel_rfl
example : (ufUseT (Δ := Ok₁.Δ)).run (ufvT (Δ := Ok₁.Δ)).run = (4 : Nat) := by kernel_rfl

/-! ## Why the erasure is sound

A field of a type of one value carries no information.  The facts below are the ones the
translation relies on, stated and proved about the Lean types themselves. -/

/-- A function type, dependent or not, whose results each have at most one value has at most
    one value: two such functions are equal (`Fin m → Unit`, `Unit → Fin 3 → Unit`). -/
theorem pi_subsingleton {α : Sort _} {β : α → Sort _} (h : ∀ a, ∀ x y : β a, x = y)
    (f g : (a : α) → β a) : f = g :=
  funext fun a => h a (f a) (g a)

/-- `Fin m → Unit` has exactly one value, `fun _ => ()`. -/
theorem finUnit_eq (m : Nat) (f : Fin m → Unit) : f = fun _ => () :=
  pi_subsingleton (fun _ _ _ => rfl) f _

/-- `Unit → Fin m → Unit` has exactly one value too. -/
theorem unitFinUnit_eq (m : Nat) (f : Unit → Fin m → Unit) : f = fun _ _ => () :=
  pi_subsingleton (fun _ x y => pi_subsingleton (fun _ _ _ => rfl) x y) f _

/-- A structure of fields of at most one value has at most one value (`Unit × PUnit`). -/
theorem prod_subsingleton {α β : Type _} (ha : ∀ x y : α, x = y) (hb : ∀ x y : β, x = y)
    (p q : α × β) : p = q := by
  cases p with
  | mk a b => cases q with
    | mk c d => rw [ha a c, hb b d]

/-- `(n : Nat) → Fin n → Unit × PUnit`, the erased field of `UF₄`, has exactly one value. -/
theorem uf4Field_eq (f : (n : Nat) → Fin n → Unit × PUnit) : f = fun _ _ => ((), PUnit.unit) :=
  pi_subsingleton (fun _ x y => pi_subsingleton
    (fun _ => prod_subsingleton (fun _ _ => rfl) (fun _ _ => rfl)) x y) f _

/-- `UF₄` is read as `Nat × Bool` (the record `.nat` and `.bool`), losing nothing. -/
def UF₄.toPair : UF₄ → Nat × Bool
  | .node m _ b => (m, b)

def UF₄.ofPair (p : Nat × Bool) : UF₄ := .node p.1 (fun _ _ => ((), PUnit.unit)) p.2

theorem UF₄.ofPair_toPair (u : UF₄) : UF₄.ofPair u.toPair = u := by
  cases u with
  | node m f b => simp only [UF₄.toPair, UF₄.ofPair, uf4Field_eq f]

theorem UF₄.toPair_ofPair (p : Nat × Bool) : (UF₄.ofPair p).toPair = p := rfl

/-- The `Nat` that `UF` is read as. -/
def UF.ofNat (m : Nat) : UF := .node m (fun _ => ())

/-- Reading `UF` as `Nat` loses nothing: `UF.m` and `UF.ofNat` are inverse bijections. -/
theorem UF.ofNat_m (u : UF) : UF.ofNat u.m = u := by
  cases u with
  | node m f => simp only [UF.m, UF.ofNat, finUnit_eq m f]

theorem UF.m_ofNat (m : Nat) : (UF.ofNat m).m = m := rfl

/-- The declared layout of `UF` denotes `Nat`. -/
example : Ty.Den Ok₁.Δ Ok₁.t = Nat := rfl

/-- `UF₂` has exactly one value: refusing it loses nothing. -/
theorem UF₂.eq (u v : UF₂) : u = v := by
  cases u with
  | node a f => cases v with
    | node b g => cases a; cases b; rw [finUnit_eq 3 f, finUnit_eq 3 g]

/-- `UF₃` has exactly one value: refusing it loses nothing. -/
theorem UF₃.eq (u v : UF₃) : u = v := by
  cases u with
  | node a f => cases v with
    | node b g => cases a; cases b; rw [unitFinUnit_eq 3 f, unitFinUnit_eq 3 g]

/-- The translation of `UF.m` computes `UF.m` on every value, read as its `Nat`. -/
theorem ufMT_run (u : UF) : (ufMT (Δ := Ok₁.Δ)).run u.m = u.m := by
  cases u; rfl

/-- The translation of `UF.use`, which reads the erased field, computes `UF.use` on every
    value. -/
theorem ufUseT_run (u : UF) : (ufUseT (Δ := Ok₁.Δ)).run u.m = UF.use u := by
  cases u with
  | node m f =>
    cases m with
    | zero => rfl
    | succ n => rfl

/-- The translation of `ufv` is its `Nat`. -/
theorem ufvT_run : (ufvT (Δ := Ok₁.Δ)).run = ufv.m := rfl

end OnePointFieldTest

end
