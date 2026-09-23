module

public import LeanScript.Ty.Wf
public import LeanScript.Ty.TyBEq
public meta import LeanScript.Ty.WfTactic

@[expose] public section

namespace LeanScript

/-- A tree of the language together with the proof that it is one: what a
    `LeanScript.LeanScriptTyWf` instance holds, with the Lean type it models forgotten.

    `Ty` is in `Type` and `Ty.Wf` is a proposition, so `TyWf` is in `Type` as well — not
    in `Type 1`.

    The proof is written by `ty_wf` unless one is given, so a bundled tree is usually
    written as its tree alone: `(⟨.prim .nat⟩ : TyWf)`. -/
structure TyWf where
  /-- The tree. -/
  toTy : Ty
  /-- That the tree is a type of the language. -/
  isWf : Ty.Wf toTy := by ty_wf

namespace TyWf

/-- Two bundled trees are equal when their trees are: the other field is a proof. -/
@[ext] theorem ext : ∀ {s t : TyWf}, s.toTy = t.toTy → s = t
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- A bundled tree *is* its tree wherever a tree is wanted: the proof is dropped.  This is
    the only direction that can be a coercion — the other one needs a proof, which no
    instance can supply; `LeanScript.Ty.toTyWf` is that direction, written out. -/
instance : CoeOut TyWf Ty := ⟨toTy⟩

/-- Equality of bundled trees is equality of their trees: the other field is a proof, and
    two proofs of one proposition are equal. -/
instance : BEq TyWf := ⟨fun s t => s.toTy == t.toTy⟩

instance : LawfulBEq TyWf where
  eq_of_beq h := TyWf.ext (eq_of_beq h)
  rfl := Ty.beq_refl _

instance : DecidableEq TyWf := fun s t =>
  if h : s.toTy = t.toTy then .isTrue (TyWf.ext h) else .isFalse fun he => h (he ▸ rfl)

instance : Inhabited TyWf := ⟨⟨.prim .bool, .shape .prim⟩⟩

end TyWf

/-- The other direction: a tree becomes a bundle once it is known to be a type, and
    `ty_wf` writes that proof, so `(Ty.prim .nat).toTyWf` needs nothing written by hand.
    It cannot be a `CoeOut` instance, because an instance has no room for the proof. -/
def Ty.toTyWf (t : Ty) (h : Ty.Wf t := by ty_wf) : TyWf := ⟨t, h⟩

@[simp] theorem Ty.toTy_toTyWf (t : Ty) (h : Ty.Wf t) : (t.toTyWf h).toTy = t := rfl

end LeanScript

end
