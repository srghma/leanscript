module

public import JsTerm.Ty.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Decidable equality of the types of `JsTerm`

`JsTy` is a nested inductive (its constructors hold lists of types), so its `DecidableEq`
instance (`JsTy.decEqTy`) is written by hand, by mutual recursion over types, lists of types
and lists of lists of types.
-/

namespace MoreJs

namespace JsTy

mutual
/-- Decidable equality of types. -/
def decEqTy : (a b : JsTy) → Decidable (a = b)
  | .terminal x0, .terminal y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .terminal _, .array _ => isFalse (fun h => by cases h)
  | .terminal _, .typedArray _ => isFalse (fun h => by cases h)
  | .terminal _, .list _ => isFalse (fun h => by cases h)
  | .terminal _, .fn _ _ => isFalse (fun h => by cases h)
  | .terminal _, .record _ _ _ => isFalse (fun h => by cases h)
  | .terminal _, .union _ _ _ => isFalse (fun h => by cases h)
  | .terminal _, .enum _ _ => isFalse (fun h => by cases h)
  | .terminal _, .data _ => isFalse (fun h => by cases h)
  | .terminal _, .thunk _ => isFalse (fun h => by cases h)
  | .array _, .terminal _ => isFalse (fun h => by cases h)
  | .array x0, .array y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .array _, .typedArray _ => isFalse (fun h => by cases h)
  | .array _, .list _ => isFalse (fun h => by cases h)
  | .array _, .fn _ _ => isFalse (fun h => by cases h)
  | .array _, .record _ _ _ => isFalse (fun h => by cases h)
  | .array _, .union _ _ _ => isFalse (fun h => by cases h)
  | .array _, .enum _ _ => isFalse (fun h => by cases h)
  | .array _, .data _ => isFalse (fun h => by cases h)
  | .array _, .thunk _ => isFalse (fun h => by cases h)
  | .typedArray _, .terminal _ => isFalse (fun h => by cases h)
  | .typedArray _, .array _ => isFalse (fun h => by cases h)
  | .typedArray x0, .typedArray y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .typedArray _, .list _ => isFalse (fun h => by cases h)
  | .typedArray _, .fn _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .record _ _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .union _ _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .enum _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .data _ => isFalse (fun h => by cases h)
  | .typedArray _, .thunk _ => isFalse (fun h => by cases h)
  | .list _, .terminal _ => isFalse (fun h => by cases h)
  | .list _, .array _ => isFalse (fun h => by cases h)
  | .list _, .typedArray _ => isFalse (fun h => by cases h)
  | .list x0, .list y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .list _, .fn _ _ => isFalse (fun h => by cases h)
  | .list _, .record _ _ _ => isFalse (fun h => by cases h)
  | .list _, .union _ _ _ => isFalse (fun h => by cases h)
  | .list _, .enum _ _ => isFalse (fun h => by cases h)
  | .list _, .data _ => isFalse (fun h => by cases h)
  | .list _, .thunk _ => isFalse (fun h => by cases h)
  | .fn _ _, .terminal _ => isFalse (fun h => by cases h)
  | .fn _ _, .array _ => isFalse (fun h => by cases h)
  | .fn _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .fn _ _, .list _ => isFalse (fun h => by cases h)
  | .fn x0 x1, .fn y0 y1 =>
    match decEqTys x0 y0, decEqTy x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .fn _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .data _ => isFalse (fun h => by cases h)
  | .fn _ _, .thunk _ => isFalse (fun h => by cases h)
  | .record _ _ _, .terminal _ => isFalse (fun h => by cases h)
  | .record _ _ _, .array _ => isFalse (fun h => by cases h)
  | .record _ _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .record _ _ _, .list _ => isFalse (fun h => by cases h)
  | .record _ _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .record x0 x1 x2, .record y0 y1 y2 =>
    match decEqTy x0 y0, decEqTy x1 y1, decEqTys x2 y2 with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (h0 ▸ h1 ▸ h2 ▸ rfl)
    | isFalse h, _, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .record _ _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .record _ _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .record _ _ _, .data _ => isFalse (fun h => by cases h)
  | .record _ _ _, .thunk _ => isFalse (fun h => by cases h)
  | .union _ _ _, .terminal _ => isFalse (fun h => by cases h)
  | .union _ _ _, .array _ => isFalse (fun h => by cases h)
  | .union _ _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .union _ _ _, .list _ => isFalse (fun h => by cases h)
  | .union _ _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .union _ _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .union x0 x1 x2, .union y0 y1 y2 =>
    match decEqTys x0 y0, decEqTys x1 y1, decEqTyss x2 y2 with
    | isTrue h0, isTrue h1, isTrue h2 => isTrue (h0 ▸ h1 ▸ h2 ▸ rfl)
    | isFalse h, _, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .union _ _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .union _ _ _, .data _ => isFalse (fun h => by cases h)
  | .union _ _ _, .thunk _ => isFalse (fun h => by cases h)
  | .enum _ _, .terminal _ => isFalse (fun h => by cases h)
  | .enum _ _, .array _ => isFalse (fun h => by cases h)
  | .enum _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .enum _ _, .list _ => isFalse (fun h => by cases h)
  | .enum _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .record _ _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .union _ _ _ => isFalse (fun h => by cases h)
  | .enum x0 x1, .enum y0 y1 =>
    match decEq x0 y0, decEq x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .enum _ _, .data _ => isFalse (fun h => by cases h)
  | .enum _ _, .thunk _ => isFalse (fun h => by cases h)
  | .data _, .terminal _ => isFalse (fun h => by cases h)
  | .data _, .array _ => isFalse (fun h => by cases h)
  | .data _, .typedArray _ => isFalse (fun h => by cases h)
  | .data _, .list _ => isFalse (fun h => by cases h)
  | .data _, .fn _ _ => isFalse (fun h => by cases h)
  | .data _, .record _ _ _ => isFalse (fun h => by cases h)
  | .data _, .union _ _ _ => isFalse (fun h => by cases h)
  | .data _, .enum _ _ => isFalse (fun h => by cases h)
  | .data x0, .data y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .data _, .thunk _ => isFalse (fun h => by cases h)
  | .thunk _, .terminal _ => isFalse (fun h => by cases h)
  | .thunk _, .array _ => isFalse (fun h => by cases h)
  | .thunk _, .typedArray _ => isFalse (fun h => by cases h)
  | .thunk _, .list _ => isFalse (fun h => by cases h)
  | .thunk _, .fn _ _ => isFalse (fun h => by cases h)
  | .thunk _, .record _ _ _ => isFalse (fun h => by cases h)
  | .thunk _, .union _ _ _ => isFalse (fun h => by cases h)
  | .thunk _, .enum _ _ => isFalse (fun h => by cases h)
  | .thunk _, .data _ => isFalse (fun h => by cases h)
  | .thunk x0, .thunk y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)

/-- Decidable equality of lists of types. -/
def decEqTys : (a b : List JsTy) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match decEqTy a b, decEqTys as bs with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
/-- Decidable equality of lists of lists of types. -/
def decEqTyss : (a b : List (List JsTy)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match decEqTys a b, decEqTyss as bs with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
end

instance : DecidableEq JsTy := decEqTy

end JsTy

end MoreJs

end
