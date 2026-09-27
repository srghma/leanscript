module

public import LeanScript.Den

@[expose] public section

set_option autoImplicit false

/-!
# Tests: different types with the same meaning

`Ty.Den` is not injective. Each pair below is two *different* `Ty`s (the derived
`DecidableEq` tells them apart) whose meanings are the *same* Lean type, by `rfl`. These are
the checks behind `DESIGN_ANALYSIS.md`, section 1.2.
-/

namespace DenNonInjectiveTest

open LeanScript

variable {ks : List Nat} (Δ : DSig ks) (a b c : Ty ks)

/-- A record of three fields and a record of a field and a record of two fields. -/
example : (Ty.record a (.one (.record b (.one c))) : Ty ks) ≠ Ty.record a (.cons b (.one c)) := by simp
example : Ty.Den Δ (Ty.record a (.one (.record b (.one c)))) =
    Ty.Den Δ (Ty.record a (.cons b (.one c))) := rfl

/-- `Option a` with the field-less constructor first or second. -/
example : (Ty.union (.two .nullary (.fields (.one a))) : Ty ks) ≠
    Ty.union (.two (.fields (.one a)) .nullary) := by simp
example : Ty.Den Δ (Ty.union (.two .nullary (.fields (.one a)))) =
    Ty.Den Δ (Ty.union (.two (.fields (.one a)) .nullary)) := rfl

/-- A union of three constructors and a union of two whose second holds a sum. -/
example : Ty.Den Δ (Ty.union (.cons (.fields (.one a)) (.two (.fields (.one b)) (.fields (.one c))))) =
    Ty.Den Δ (Ty.union (.two (.fields (.one a)) (.fields (.one (Ty.sum b c))))) := rfl

/-- Two enums that differ only in how they are numbered. -/
example : (Ty.enum ⟨0, 0⟩ : Ty ks) ≠ Ty.enum ⟨0, -1⟩ := by simp
example : Ty.Den Δ (Ty.enum ⟨0, 0⟩) = Ty.Den Δ (Ty.enum ⟨0, -1⟩) := rfl

end DenNonInjectiveTest

end
