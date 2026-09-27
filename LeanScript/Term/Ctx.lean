module

public import LeanScript.Term.Usage
public import LeanScript.Term.Common

@[expose] public section

set_option autoImplicit false

/-!
# Contexts of normal-form terms: known values, unknowns, join points

A normal-form statement (`LeanScript.Term.Term`) has three contexts:

* `Φ : KCtx ks`, the **known** values: variables bound by `Term.letV` to a value of known shape
  (a closure, a delay, a record/union/array/list/`data_in` literal).  Each entry records its
  type, its usage (`Usage1ω`: a definition binder), its **level** `lv : Lvl` and whether it is
  visible.  The level says whether (and how) the value is **open**: `none` when it mentions no
  unknown, `some ℓ` when the outermost unknown it mentions has level `ℓ`.  A closed known
  value is fully known when the term is elaborated; an open one only has a known *shape*.
* `Γ : UCtx ks`, the **unknowns**: parameters of closures, binders of loops and case
  analyses, parameters of join points, results of computations.  Each entry records its type,
  its usage (`Usage01ω`) and its level `lv : Nat`: how many closure, delay or loop bodies it is
  nested in.
* `js : JCtx ks`, the **join points** in scope: the type of the parameter and the usage of the
  join point (`Usage1ω`: a definition binder).

**Levels.**  The level of an unknown is the *depth* at which it is bound: the unknowns of a
statement at depth `d` (`Term Δ d …`) are bound at level `d`, the parameters of a body inside
it at level `d + 1`.  Every syntactic class records the *smallest* level it mentions
(`Lvl`, with `none` for "no unknown at all"), so a body at depth `d + 1` is **open** exactly
when it mentions a level `≤ d`: something bound outside of it.

A variable is a typed de Bruijn index (`UVar`, `KVar`, `JVar`) that also records the level of
its entry.  An unknown whose binder is annotated `zero` cannot be referenced, nor can a hidden
known value.
-/

namespace LeanScript

/-! ## Levels -/

/-- The smallest level of unknown something mentions: `none` when it mentions no unknown
    (it is **closed**), `some ℓ` otherwise (it is **open**). -/
abbrev Lvl : Type := Option Nat

/-- The level of two things together: the smaller one (`none` is the unit). -/
def Lvl.meet : Lvl → Lvl → Lvl
  | none, o => o
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

/-- The level of something open (of level `ℓ`) together with something of level `o`. -/
def Lvl.meetL (ℓ : Nat) : Lvl → Nat
  | none => ℓ
  | some b => Nat.min ℓ b

/-- The level of finitely many things together. -/
def Lvl.meetFin : (n : Nat) → (Fin n → Lvl) → Lvl
  | 0, _ => none
  | n + 1, f => Lvl.meet (f 0) (Lvl.meetFin n (fun i => f i.succ))

@[simp] theorem Lvl.none_meet (o : Lvl) : Lvl.meet none o = o := rfl
@[simp] theorem Lvl.meet_none (o : Lvl) : Lvl.meet o none = o := by cases o <;> rfl

@[simp] theorem Lvl.meet_eq_none (o₁ o₂ : Lvl) : Lvl.meet o₁ o₂ = none ↔ o₁ = none ∧ o₂ = none := by
  cases o₁ <;> cases o₂ <;> simp [Lvl.meet]

@[simp] theorem Lvl.some_meet (a : Nat) (o : Lvl) : Lvl.meet (some a) o = some (Lvl.meetL a o) := by
  cases o <;> rfl

theorem Lvl.meetFin_eq_none {n : Nat} {f : Fin n → Lvl} (h : Lvl.meetFin n f = none)
    (i : Fin n) : f i = none := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      simp only [Lvl.meetFin, Lvl.meet_eq_none] at h
      cases i using Fin.cases with
      | zero => exact h.1
      | succ i => exact ih h.2 i

theorem Lvl.meetFin_none (n : Nat) : Lvl.meetFin n (fun _ => none) = none := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Lvl.meetFin, ih]

/-! ## Binders and contexts -/

/-- An entry of the context of unknowns: a type, a usage and a level. -/
structure UBinder (ks : List Nat) where
  ty : Ty ks
  use : Usage01ω
  lv : Nat
  deriving DecidableEq

/-- An entry of the context of known values: a type, a usage, a level (`none` when the value
    is closed), and whether it can be referenced (`vis = false` for the open entries hidden
    from a closed body, `KCtx.closedOnly`). -/
structure KBinder (ks : List Nat) where
  ty : Ty ks
  use : Usage1ω
  lv : Lvl
  vis : Bool
  deriving DecidableEq

/-- An entry of the context of join points: the type of the parameter and a usage. -/
structure JBinder (ks : List Nat) where
  ty : Ty ks
  use : Usage1ω
  deriving DecidableEq

instance {ks : List Nat} : BEq (UBinder ks) := instBEqOfDecidableEq
instance {ks : List Nat} : BEq (KBinder ks) := instBEqOfDecidableEq
instance {ks : List Nat} : BEq (JBinder ks) := instBEqOfDecidableEq

/-- The unknowns in scope, innermost first. -/
abbrev UCtx (ks : List Nat) : Type := List (UBinder ks)

/-- The known values in scope, innermost first. -/
abbrev KCtx (ks : List Nat) : Type := List (KBinder ks)

/-- The join points in scope, innermost first. -/
abbrev JCtx (ks : List Nat) : Type := List (JBinder ks)

/-- A variable of the context of unknowns, of type `τ` and level `ℓ`, whose binder is used. -/
inductive UVar {ks : List Nat} : UCtx ks → Ty ks → Nat → Type where
  | head {τ : Ty ks} {u : Usage01ω} {ℓ : Nat} {Γ : UCtx ks} : u ≠ .zero → UVar (⟨τ, u, ℓ⟩ :: Γ) τ ℓ
  | tail {τ : Ty ks} {ℓ : Nat} {b : UBinder ks} {Γ : UCtx ks} : UVar Γ τ ℓ → UVar (b :: Γ) τ ℓ

/-- A variable of the context of known values, of type `τ` and level `o`, whose binder is
    visible. -/
inductive KVar {ks : List Nat} : KCtx ks → Ty ks → Lvl → Type where
  | head {τ : Ty ks} {u : Usage1ω} {o : Lvl} {Φ : KCtx ks} : KVar (⟨τ, u, o, true⟩ :: Φ) τ o
  | tail {τ : Ty ks} {o : Lvl} {b : KBinder ks} {Φ : KCtx ks} : KVar Φ τ o → KVar (b :: Φ) τ o

/-- A join point whose parameter has type `σ`. -/
inductive JVar {ks : List Nat} : JCtx ks → Ty ks → Type where
  | head {σ : Ty ks} {u : Usage1ω} {js : JCtx ks} : JVar (⟨σ, u⟩ :: js) σ
  | tail {σ : Ty ks} {b : JBinder ks} {js : JCtx ks} : JVar js σ → JVar (b :: js) σ

/-- How many binders out a variable is. -/
def UVar.index {ks : List Nat} : {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} → UVar Γ τ ℓ → Nat
  | _, _, _, .head _ => 0
  | _, _, _, .tail x => x.index + 1

/-- How many binders out a known variable is. -/
def KVar.index {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} → KVar Φ τ o → Nat
  | _, _, _, .head => 0
  | _, _, _, .tail x => x.index + 1

/-- How many binders out a join point is. -/
def JVar.index {ks : List Nat} : {js : JCtx ks} → {σ : Ty ks} → JVar js σ → Nat
  | _, _, .head => 0
  | _, _, .tail x => x.index + 1

/-- The context of known values as seen from a **closed** body (a closed closure, delay or
    loop body): the open entries are hidden. -/
def KCtx.closedOnly {ks : List Nat} : KCtx ks → KCtx ks
  | [] => []
  | ⟨t, u, some ℓ, _⟩ :: Φ => ⟨t, u, some ℓ, false⟩ :: closedOnly Φ
  | ⟨t, u, none, v⟩ :: Φ => ⟨t, u, none, v⟩ :: closedOnly Φ

/-- Every known value is closed: the known context of a statement with no unknown. -/
def KCtx.AllClosed {ks : List Nat} : KCtx ks → Prop
  | [] => True
  | b :: Φ => b.lv = none ∧ AllClosed Φ

/-- Binders at level `ℓ` for a list of types, with the given usages (`many` when the list of
    usages is too short).  The fields a case analysis binds. -/
def UCtx.annot {ks : List Nat} (ℓ : Nat) : List (Ty ks) → List Usage01ω → UCtx ks
  | [], _ => []
  | t :: ts, [] => ⟨t, .many, ℓ⟩ :: annot ℓ ts []
  | t :: ts, u :: us => ⟨t, u, ℓ⟩ :: annot ℓ ts us

/-- The types of the entries. -/
theorem UCtx.annot_map_ty {ks : List Nat} (ℓ : Nat) : (ts : List (Ty ks)) → (us : List Usage01ω) →
    (UCtx.annot ℓ ts us).map UBinder.ty = ts
  | [], _ => rfl
  | _ :: ts, [] => by simp [annot, annot_map_ty ℓ ts []]
  | _ :: ts, _ :: us => by simp [annot, annot_map_ty ℓ ts us]

/-- No known value is open once the open ones are hidden. -/
theorem KVar.closedOnly_closed {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KVar (KCtx.closedOnly Φ) τ o → o = none
  | ⟨_, _, some _, _⟩ :: _, _, _, .tail x => x.closedOnly_closed
  | ⟨_, _, none, _⟩ :: _, _, _, .head => rfl
  | ⟨_, _, none, _⟩ :: _, _, _, .tail x => x.closedOnly_closed

/-- A variable of the closed view is a variable of the context. -/
def KVar.unmask {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KVar (KCtx.closedOnly Φ) τ o → KVar Φ τ o
  | ⟨_, _, some _, _⟩ :: _, _, _, .tail x => .tail x.unmask
  | ⟨_, _, none, _⟩ :: _, _, _, .head => .head
  | ⟨_, _, none, _⟩ :: _, _, _, .tail x => .tail x.unmask

/-- A variable of the context as a variable of the closed view, when it is closed. -/
def KVar.mask {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KVar Φ τ o → Option (KVar (KCtx.closedOnly Φ) τ o)
  | ⟨_, _, some _, _⟩ :: _, _, _, .head => none
  | ⟨_, _, some _, _⟩ :: _, _, _, .tail x => x.mask.map .tail
  | ⟨_, _, none, _⟩ :: _, _, _, .head => some .head
  | ⟨_, _, none, _⟩ :: _, _, _, .tail x => x.mask.map .tail

/-- There is no variable in an empty context. -/
theorem UVar.not_nil {ks : List Nat} {τ : Ty ks} {ℓ : Nat} : UVar ([] : UCtx ks) τ ℓ → False :=
  nofun

/-- A known variable of a context of closed values is closed. -/
theorem KVar.allClosed {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KCtx.AllClosed Φ → KVar Φ τ o → o = none
  | _, _, _, h, .head => h.1
  | _ :: _, _, _, h, .tail x => x.allClosed h.2

end LeanScript

end
