module

public import LeanScript.Den
public import LeanScript.Ty.Instances

@[expose] public section

/-!
# The values of a record or a constructor are a tuple, with no trailing `PUnit`

`Ty.Den (.record ⟨α, β, []⟩)` is `Ty.Den α × Ty.Den β`, and a constructor with one field
holds that field itself.  Every equation below holds by `rfl`.
-/

namespace TermTests.DenTuple

open LeanScript

/-- A pair denotes the pair of the denotations — for **any** two types, not only concrete
    ones. -/
theorem den_prod (α β : Type) [LeanScriptTyWf α] [LeanScriptTyWf β] :
    TyWf.Den (tyWfOf (α × β)) = (TyWf.Den (tyWfOf α) × TyWf.Den (tyWfOf β)) := rfl

example : TyWf.Den (tyWfOf (Nat × Bool)) = (Nat × Bool) := rfl

example : (((3 : Nat), true) : TyWf.Den (tyWfOf (Nat × Bool))).2 = true := rfl

/-- A record of three fields is nested to the right, still with no `PUnit`. -/
example (a b c : Ty) :
    Ty.Den (.record ⟨a, b, [c]⟩) = (Ty.Den a × Ty.Den b × Ty.Den c) := rfl

/-- The fields of a constructor with one field are that field; with none, `PUnit`. -/
example (a : Ty) : Ty.DenFields [a] = Ty.Den a := rfl
example : Ty.DenFields [] = PUnit := rfl

/-- `some` of `Option α` holds a value of `α`, not a value of `α × PUnit`. -/
example : TyWf.DenTU.field? (l := .skip (.here ⟨tyWfOf Nat, []⟩ [])) 1 (by decide)
    ⟨⟨1, by decide⟩, (5 : Nat)⟩ = some (5 : Nat) := rfl

/-- An environment is still closed by `PUnit`; `Ty.DenFields.toList` converts. -/
example (a b : Ty) (x : Ty.Den a) (y : Ty.Den b) :
    Ty.DenFields.toList [a, b] (x, y) = (x, y, PUnit.unit) := rfl

end TermTests.DenTuple

end
