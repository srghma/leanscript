module

public import LeanScript.Term.Syntax.Common
public import LeanScript.LeanInitPureExterns.Shorthands

@[expose] public section

set_option autoImplicit false

/-!
# The catalogue of externs, over the types of the language

The catalogue `LeanScript.LeanInitPureExtern` is written over any grammar of types `MyTy`;
this module instantiates it to `Ty ks`: `Extern ks σs τ` is an entry of the catalogue whose
arguments have the types `σs` and whose result has the type `τ`.  An extern call of a term
(`LeanScript.Neu.extern`) holds such an entry and the pure expressions of its arguments.

The type formers the catalogue asks for are the ones of `Ty`:

* a leaf type `p : LeanPrimTy` is `Ty.prim p` (the coercion `Ty.instCoeLeanPrimTy`);
* an array, a list, a thunk or a lazy value of `t` is `Ty.array t`, `Ty.list t`, `Ty.thunk t`,
  `Ty.lazy t`
  (`Ty.ofCovariant`); a delay around a delay is one delay, as in `Ty.mkThunk`;
* an option is `Ty.option`, a pair `Ty.pair`, a function `Ty.fn` (`Ty.fn2` for two
  arguments), `Ordering` is the enum `Ty.ordering` (three constructors printed as
  `-1 | 0 | 1`), and `Lean.Name` is `Ty.leanName`, the list of its components
  (`nameToComponents`, `nameOfComponents`).

The evaluator of the entries is `LeanScript.Extern.eval` (`LeanScript.Term.Extern.Eval`).
-/

namespace LeanScript

namespace Ty
variable {ks : List Nat}

/-- A type as a type that is not a delay: a delay is replaced by the type it delays (a delay
    denotes its value, so this does not change the denotation, `Ty.den_strictOf`). -/
def strictOf : Ty ks → Ty ks false
  | .prim p => .prim p
  | .fn a b => .fn a b
  | .array t => .array t
  | .list t => .list t
  | .enum s => .enum s
  | .record t fs => .record t fs
  | .union cs (h := h) => .union cs (h := h)
  | .data r => .data r
  | .thunk t => t
  | .lazy t => t

/-- A value of a type, as a value of the type without its delay. -/
def toStrictOf (E : Ref ks → Type) : (t : Ty ks) → Ty.den E t → Ty.den E (Ty.relax t.strictOf)
  | .prim _, x => x
  | .fn _ _, x => x
  | .array _, x => x
  | .list _, x => x
  | .enum _, x => x
  | .record _ _, x => x
  | .union _ (h := _), x => x
  | .data _, x => x
  | .thunk t, x => Ty.toRelax E t x
  | .lazy t, x => Ty.toRelax E t x

/-- A value of the type without its delay, as a value of the type. -/
def ofStrictOf (E : Ref ks → Type) : (t : Ty ks) → Ty.den E (Ty.relax t.strictOf) → Ty.den E t
  | .prim _, x => x
  | .fn _ _, x => x
  | .array _, x => x
  | .list _, x => x
  | .enum _, x => x
  | .record _ _, x => x
  | .union _ (h := _), x => x
  | .data _, x => x
  | .thunk t, x => Ty.ofRelax E t x
  | .lazy t, x => Ty.ofRelax E t x

/-- The covariant type formers of the catalogue (`array`, `list`, `thunk`, `lazy`), as types. -/
def ofCovariant : LeanPrimTyCovariant (Ty ks) → Ty ks
  | .array t => .array t
  | .list t => .list t
  | .thunk t => .thunk t.strictOf
  | .lazy t => .lazy t.strictOf

/-- A function of two arguments. -/
abbrev fn2 (a b c : Ty ks) : Ty ks := .fn a (.fn b c)

/-- `Ordering`: the enum of three constructors printed as `-1 | 0 | 1`. -/
abbrev ordering : Ty ks := .enum { extraConstructors := 0, shift := -1 }

instance instCoeLeanPrimTy : Coe LeanPrimTy (Ty ks) := ⟨fun p => .prim p⟩
instance instCoeCovariantLeanPrimTy : Coe (LeanPrimTyCovariant LeanPrimTy) (Ty ks) :=
  ⟨fun c => ofCovariant (c.map fun p => .prim p)⟩
instance instCoeCovariant : Coe (LeanPrimTyCovariant (Ty ks)) (Ty ks) := ⟨ofCovariant⟩

end Ty

/-- **An extern**: an entry of the catalogue `LeanInitPureExtern`, over the types of the
    language, whose arguments have the types `σs` and whose result has the type `τ`. -/
abbrev Extern (ks : List Nat) (σs : List (Ty ks)) (τ : Ty ks) : Type :=
  LeanInitPureExtern (MyTy := Ty ks) (fun t => Ty.option t) (fun a b => Ty.fn a b) Ty.fn2
    Ty.pair Ty.ordering Ty.leanName σs τ

/-- The Boolean answer of an extern: a `Bool`, or the decision of a proposition (an extern
    whose Lean function returns `Decidable p` answers `decide p`). -/
class ExternBool (α : Type) where
  /-- The answer, as a `Bool`. -/
  toBool : α → Bool

instance : ExternBool Bool := ⟨id⟩
instance {p : Prop} : ExternBool (Decidable p) := ⟨fun d => @decide p d⟩

/-- An `Ordering`, as a constructor of the enum `Ty.ordering`. -/
def orderingToFin : Ordering → Fin 3
  | .lt => 0
  | .eq => 1
  | .gt => 2

/-- A component of a `Lean.Name`, as a value of `Ty.nameComponent`. -/
abbrev NameComponent : Type := String ⊕ Nat

/-- The values of `Ty.leanName` are the lists of components. -/
theorem Ty.den_leanName {ks : List Nat} (E : Ref ks → Type) : Ty.den E Ty.leanName = List NameComponent := rfl

/-- The components of a name, root first, in front of `acc`. -/
def nameToComponentsAux : Lean.Name → List NameComponent → List NameComponent
  | .anonymous, acc => acc
  | .str p s, acc => nameToComponentsAux p (.inl s :: acc)
  | .num p n, acc => nameToComponentsAux p (.inr n :: acc)

/-- A `Lean.Name`, as a value of `Ty.leanName`: its components, root first
    (`` `a.b `` is `[.inl "a", .inl "b"]`). -/
def nameToComponents (n : Lean.Name) : List NameComponent := nameToComponentsAux n []

/-- One more component at the end of a name. -/
def nameAppendComponent : Lean.Name → NameComponent → Lean.Name
  | p, .inl s => .str p s
  | p, .inr n => .num p n

/-- A value of `Ty.leanName`, as a `Lean.Name`. -/
def nameOfComponents (cs : List NameComponent) : Lean.Name :=
  cs.foldl nameAppendComponent .anonymous

theorem nameOfComponents_aux (n : Lean.Name) (acc : List NameComponent) :
    (nameToComponentsAux n acc).foldl nameAppendComponent .anonymous =
      acc.foldl nameAppendComponent n := by
  induction n generalizing acc with
  | anonymous => rfl
  | str p s ih => rw [nameToComponentsAux, ih]; rfl
  | num p k ih => rw [nameToComponentsAux, ih]; rfl

theorem nameToComponents_aux (cs : List NameComponent) (m : Lean.Name)
    (acc : List NameComponent) :
    nameToComponentsAux (cs.foldl nameAppendComponent m) acc =
      nameToComponentsAux m (cs ++ acc) := by
  induction cs generalizing m with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    cases c <;> rfl

/-- Reading a name back from its components gives the name. -/
@[simp] theorem nameOfComponents_nameToComponents (n : Lean.Name) :
    nameOfComponents (nameToComponents n) = n :=
  nameOfComponents_aux n []

/-- The components of the name read from components are the components. -/
@[simp] theorem nameToComponents_nameOfComponents (cs : List NameComponent) :
    nameToComponents (nameOfComponents cs) = cs := by
  simp [nameToComponents, nameOfComponents, nameToComponents_aux, nameToComponentsAux]

end LeanScript

end
