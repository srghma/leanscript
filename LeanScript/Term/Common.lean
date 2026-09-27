module

public import LeanScript.Ty.Den
public import LeanScript.Term.Tuple

@[expose] public section

set_option autoImplicit false

/-!
# Common definitions of the three layers of `LeanScript.Term`

The contexts, variables and value lists shared by pure expressions (`LeanScript.Term.PExpr`),
computations and statements (`LeanScript.Term.Term`): `Ctx`, `Var`, `DenList`, the types a
constructor binds (`Fields.toList`, `Ctor.binds`), the index of a constructor in a union
(`CtorIx`), and the join-point contexts (`JCtx`, `JVar`).
-/

namespace LeanScript

/-- A context: the types of the variables in scope, innermost first. -/
abbrev Ctx (ks : List Nat) : Type := List (Ty ks)

/-- A typed de Bruijn variable. -/
abbrev Var {ks : List Nat} (Γ : Ctx ks) (τ : Ty ks) : Type := DeBruijn Γ τ

/-- The values of a list of types: a right-nested product with no trailing `PUnit`
    (`DenList E [a, b] = Ty.den E a × Ty.den E b`, `DenList E [a] = Ty.den E a`,
    `DenList E [] = PUnit`; see `Tuple`).  An environment is the `DenList` of a context. -/
abbrev DenList {ks : List Nat} (E : Ref ks → Type) : List (Ty ks) → Type := Tuple (Ty.den E)

/-- The types of the fields, in order. -/
def Fields.toList {ks : List Nat} : Fields ks → List (Ty ks)
  | .one t => [t]
  | .cons t fs => t :: fs.toList

/-- The types a constructor binds: its fields, or nothing. -/
def Ctor.binds {ks : List Nat} {b : Bool} : Ctor ks b → List (Ty ks)
  | .nullary => []
  | .fields fs => fs.toList

/-- A constructor of a union: constructive evidence that `c` is one of `cs`, and where. -/
inductive CtorIx {ks : List Nat} : {bs : List Bool} → {b : Bool} → Ctors ks bs → Ctor ks b → Type where
  | two₁ {a b : Bool} {c : Ctor ks a} {d : Ctor ks b} : CtorIx (.two c d) c
  | two₂ {a b : Bool} {c : Ctor ks a} {d : Ctor ks b} : CtorIx (.two c d) d
  | head {a : Bool} {bs : List Bool} {c : Ctor ks a} {cs : Ctors ks bs} : CtorIx (.cons c cs) c
  | tail {a b : Bool} {bs : List Bool} {c : Ctor ks a} {c' : Ctor ks b} {cs : Ctors ks bs} :
      CtorIx cs c' → CtorIx (.cons c cs) c'
  deriving DecidableEq, Repr, Hashable

instance {ks : List Nat} {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {c : Ctor ks b} :
    BEq (CtorIx cs c) := instBEqOfDecidableEq

instance {ks : List Nat} {a b : Bool} {c : Ctor ks a} {d : Ctor ks b} :
    Inhabited (CtorIx (.two c d) c) := ⟨.two₁⟩
instance {ks : List Nat} {a : Bool} {bs : List Bool} {c : Ctor ks a} {cs : Ctors ks bs} :
    Inhabited (CtorIx (.cons c cs) c) := ⟨.head⟩

/-- The join points in scope: the types of their parameters, innermost first.  A statement
    `Term Δ Γ τ js` may jump to any of them; each one then finishes the statement with an
    answer of type `τ`. -/
abbrev JCtx (ks : List Nat) : Type := List (Ty ks)

/-- A typed de Bruijn index of a join point. -/
abbrev JVar {ks : List Nat} (js : JCtx ks) (σ : Ty ks) : Type := DeBruijn js σ

end LeanScript

end
