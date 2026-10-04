module

public import JsTerm.Ty.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Decidable equality of the types of `JsTerm`

`JsTy` is a nested inductive (its constructors hold lists of types), so its `DecidableEq`
instance (`JsTy.decEqTy`) is written by hand, by mutual recursion over types and lists of
types.  An object type is an identity and arguments (`JsTy.obj`), so the one case of objects
compares an identity (derived `DecidableEq JsObjId`) and a list of types.
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
  | .terminal _, .strMap _ => isFalse (fun h => by cases h)
  | .terminal _, .fn _ _ => isFalse (fun h => by cases h)
  | .terminal _, .enum _ _ => isFalse (fun h => by cases h)
  | .terminal _, .thunk _ => isFalse (fun h => by cases h)
  | .terminal _, .obj _ _ => isFalse (fun h => by cases h)
  | .array _, .terminal _ => isFalse (fun h => by cases h)
  | .array x0, .array y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .array _, .typedArray _ => isFalse (fun h => by cases h)
  | .array _, .list _ => isFalse (fun h => by cases h)
  | .array _, .strMap _ => isFalse (fun h => by cases h)
  | .array _, .fn _ _ => isFalse (fun h => by cases h)
  | .array _, .enum _ _ => isFalse (fun h => by cases h)
  | .array _, .thunk _ => isFalse (fun h => by cases h)
  | .array _, .obj _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .terminal _ => isFalse (fun h => by cases h)
  | .typedArray _, .array _ => isFalse (fun h => by cases h)
  | .typedArray x0, .typedArray y0 =>
    match decEq x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .typedArray _, .list _ => isFalse (fun h => by cases h)
  | .typedArray _, .strMap _ => isFalse (fun h => by cases h)
  | .typedArray _, .fn _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .enum _ _ => isFalse (fun h => by cases h)
  | .typedArray _, .thunk _ => isFalse (fun h => by cases h)
  | .typedArray _, .obj _ _ => isFalse (fun h => by cases h)
  | .list _, .terminal _ => isFalse (fun h => by cases h)
  | .list _, .array _ => isFalse (fun h => by cases h)
  | .list _, .typedArray _ => isFalse (fun h => by cases h)
  | .list x0, .list y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .list _, .strMap _ => isFalse (fun h => by cases h)
  | .list _, .fn _ _ => isFalse (fun h => by cases h)
  | .list _, .enum _ _ => isFalse (fun h => by cases h)
  | .list _, .thunk _ => isFalse (fun h => by cases h)
  | .list _, .obj _ _ => isFalse (fun h => by cases h)
  | .strMap _, .terminal _ => isFalse (fun h => by cases h)
  | .strMap _, .array _ => isFalse (fun h => by cases h)
  | .strMap _, .typedArray _ => isFalse (fun h => by cases h)
  | .strMap _, .list _ => isFalse (fun h => by cases h)
  | .strMap x0, .strMap y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .strMap _, .fn _ _ => isFalse (fun h => by cases h)
  | .strMap _, .enum _ _ => isFalse (fun h => by cases h)
  | .strMap _, .thunk _ => isFalse (fun h => by cases h)
  | .strMap _, .obj _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .terminal _ => isFalse (fun h => by cases h)
  | .fn _ _, .array _ => isFalse (fun h => by cases h)
  | .fn _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .fn _ _, .list _ => isFalse (fun h => by cases h)
  | .fn _ _, .strMap _ => isFalse (fun h => by cases h)
  | .fn x0 x1, .fn y0 y1 =>
    match decEqTys x0 y0, decEqTy x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .fn _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .fn _ _, .thunk _ => isFalse (fun h => by cases h)
  | .fn _ _, .obj _ _ => isFalse (fun h => by cases h)
  | .enum _ _, .terminal _ => isFalse (fun h => by cases h)
  | .enum _ _, .array _ => isFalse (fun h => by cases h)
  | .enum _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .enum _ _, .list _ => isFalse (fun h => by cases h)
  | .enum _ _, .strMap _ => isFalse (fun h => by cases h)
  | .enum _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .enum x0 x1, .enum y0 y1 =>
    match decEq x0 y0, decEq x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .enum _ _, .thunk _ => isFalse (fun h => by cases h)
  | .enum _ _, .obj _ _ => isFalse (fun h => by cases h)
  | .thunk _, .terminal _ => isFalse (fun h => by cases h)
  | .thunk _, .array _ => isFalse (fun h => by cases h)
  | .thunk _, .typedArray _ => isFalse (fun h => by cases h)
  | .thunk _, .list _ => isFalse (fun h => by cases h)
  | .thunk _, .strMap _ => isFalse (fun h => by cases h)
  | .thunk _, .fn _ _ => isFalse (fun h => by cases h)
  | .thunk _, .enum _ _ => isFalse (fun h => by cases h)
  | .thunk x0, .thunk y0 =>
    match decEqTy x0 y0 with
    | isTrue h0 => isTrue (h0 ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .thunk _, .obj _ _ => isFalse (fun h => by cases h)
  | .obj _ _, .terminal _ => isFalse (fun h => by cases h)
  | .obj _ _, .array _ => isFalse (fun h => by cases h)
  | .obj _ _, .typedArray _ => isFalse (fun h => by cases h)
  | .obj _ _, .list _ => isFalse (fun h => by cases h)
  | .obj _ _, .strMap _ => isFalse (fun h => by cases h)
  | .obj _ _, .fn _ _ => isFalse (fun h => by cases h)
  | .obj _ _, .enum _ _ => isFalse (fun h => by cases h)
  | .obj _ _, .thunk _ => isFalse (fun h => by cases h)
  | .obj x0 x1, .obj y0 y1 =>
    match decEq x0 y0, decEqTys x1 y1 with
    | isTrue h0, isTrue h1 => isTrue (h0 ▸ h1 ▸ rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h => isFalse (fun e => by cases e; exact h rfl)

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
end

instance : DecidableEq JsTy := decEqTy

end JsTy

end MoreJs

end
