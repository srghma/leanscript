module

public import LeanScript.NTerm.Usage
public import LeanScript.Term.Common

@[expose] public section

set_option autoImplicit false

/-!
# Contexts of normal-form terms: known values, unknowns, join points

A normal-form statement (`LeanScript.NTerm.Term`) has three contexts:

* `Φ : KCtx ks`, the **known** values: variables bound by `Term.letV` to a value of known shape
  (a closure, a delay, a record/union/array/list/`data_in` literal).  Each entry records its
  type, its `Usage` and whether the value is **open** (`isOpen`): whether it mentions an
  unknown (a variable of `Γ`, or an open known value).  A closed known value is fully known
  when the term is elaborated; an open one only has a known *shape*.
* `Γ : UCtx ks`, the **unknowns**: parameters of closures, binders of loops and case
  analyses, parameters of join points, results of computations.  Each entry records its type
  and its `Usage`.
* `js : UCtx ks`, the **join points** in scope: the type of the parameter and the usage of
  the join point.

A variable is a typed de Bruijn index (`UVar`, `KVar`) into an entry whose usage is **not**
`zero`: a binder annotated `zero` cannot be referenced.
-/

namespace LeanScript.NTerm

/-- An entry of the context of unknowns (or of join points): a type and a usage. -/
structure UBinder (ks : List Nat) where
  ty : Ty ks
  use : Usage

/-- An entry of the context of known values: a type, a usage, and whether the value mentions
    an unknown. -/
structure KBinder (ks : List Nat) where
  ty : Ty ks
  use : Usage
  isOpen : Bool

/-- The unknowns in scope, innermost first. -/
abbrev UCtx (ks : List Nat) : Type := List (UBinder ks)

/-- The known values in scope, innermost first. -/
abbrev KCtx (ks : List Nat) : Type := List (KBinder ks)

/-- A variable of the context of unknowns (or of join points) of type `τ`, whose binder is
    used. -/
inductive UVar {ks : List Nat} : UCtx ks → Ty ks → Type where
  | head {τ : Ty ks} {u : Usage} {Γ : UCtx ks} : u ≠ .zero → UVar (⟨τ, u⟩ :: Γ) τ
  | tail {τ : Ty ks} {b : UBinder ks} {Γ : UCtx ks} : UVar Γ τ → UVar (b :: Γ) τ

/-- A variable of the context of known values of type `τ` and openness `o`, whose binder is
    used. -/
inductive KVar {ks : List Nat} : KCtx ks → Ty ks → Bool → Type where
  | head {τ : Ty ks} {u : Usage} {o : Bool} {Φ : KCtx ks} : u ≠ .zero → KVar (⟨τ, u, o⟩ :: Φ) τ o
  | tail {τ : Ty ks} {o : Bool} {b : KBinder ks} {Φ : KCtx ks} : KVar Φ τ o → KVar (b :: Φ) τ o

/-- How many binders out a variable is. -/
def UVar.index {ks : List Nat} : {Γ : UCtx ks} → {τ : Ty ks} → UVar Γ τ → Nat
  | _, _, .head _ => 0
  | _, _, .tail x => x.index + 1

/-- How many binders out a known variable is. -/
def KVar.index {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} → KVar Φ τ o → Nat
  | _, _, _, .head _ => 0
  | _, _, _, .tail x => x.index + 1

/-- The context of known values as seen from a **closed** body (a closed closure, delay or
    loop body): the open entries are hidden, by making them unusable (usage `zero`). -/
def KCtx.closedOnly {ks : List Nat} : KCtx ks → KCtx ks
  | [] => []
  | ⟨t, _, true⟩ :: Φ => ⟨t, .zero, true⟩ :: closedOnly Φ
  | ⟨t, u, false⟩ :: Φ => ⟨t, u, false⟩ :: closedOnly Φ

/-- Every known value is closed: the known context of a statement with no unknown. -/
def KCtx.AllClosed {ks : List Nat} : KCtx ks → Prop
  | [] => True
  | b :: Φ => b.isOpen = false ∧ AllClosed Φ

/-- Binders for a list of types, with the given usages (`many` when the list of usages is
    too short).  The fields a case analysis binds. -/
def UCtx.annot {ks : List Nat} : List (Ty ks) → List Usage → UCtx ks
  | [], _ => []
  | t :: ts, [] => ⟨t, .many⟩ :: annot ts []
  | t :: ts, u :: us => ⟨t, u⟩ :: annot ts us

/-- The types of the entries. -/
theorem UCtx.annot_map_ty {ks : List Nat} : (ts : List (Ty ks)) → (us : List Usage) →
    (UCtx.annot ts us).map UBinder.ty = ts
  | [], _ => rfl
  | _ :: ts, [] => by simp [annot, annot_map_ty ts []]
  | _ :: ts, _ :: us => by simp [annot, annot_map_ty ts us]

/-- No known value is open once the open ones are hidden (for the entries that are
    usable). -/
theorem KVar.closedOnly_closed {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} →
    KVar (KCtx.closedOnly Φ) τ o → o = false
  | ⟨_, _, true⟩ :: _, _, _, .head h => absurd rfl h
  | ⟨_, _, true⟩ :: _, _, _, .tail x => x.closedOnly_closed
  | ⟨_, _, false⟩ :: _, _, _, .head _ => rfl
  | ⟨_, _, false⟩ :: _, _, _, .tail x => x.closedOnly_closed

/-- A variable of the closed view is a variable of the context. -/
def KVar.unmask {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} →
    KVar (KCtx.closedOnly Φ) τ o → KVar Φ τ o
  | ⟨_, _, true⟩ :: _, _, _, .head h => absurd rfl h
  | ⟨_, _, true⟩ :: _, _, _, .tail x => .tail x.unmask
  | ⟨_, _, false⟩ :: _, _, _, .head h => .head h
  | ⟨_, _, false⟩ :: _, _, _, .tail x => .tail x.unmask

/-- A variable of the context as a variable of the closed view, when it is closed. -/
def KVar.mask {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} →
    KVar Φ τ o → Option (KVar (KCtx.closedOnly Φ) τ o)
  | ⟨_, _, true⟩ :: _, _, _, .head _ => none
  | ⟨_, _, true⟩ :: _, _, _, .tail x => x.mask.map .tail
  | ⟨_, _, false⟩ :: _, _, _, .head h => some (.head h)
  | ⟨_, _, false⟩ :: _, _, _, .tail x => x.mask.map .tail

/-- There is no variable in an empty context. -/
theorem UVar.not_nil {ks : List Nat} {τ : Ty ks} : UVar ([] : UCtx ks) τ → False := nofun

/-- A known variable of a context of closed values is closed. -/
theorem KVar.allClosed {ks : List Nat} : {Φ : KCtx ks} → {τ : Ty ks} → {o : Bool} →
    KCtx.AllClosed Φ → KVar Φ τ o → o = false
  | _, _, _, h, .head _ => h.1
  | _ :: _, _, _, h, .tail x => x.allClosed h.2

end LeanScript.NTerm

end
