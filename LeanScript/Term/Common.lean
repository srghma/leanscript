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
(`CtorIx`), the join-point contexts (`JCtx`, `JVar`), and which externs are cheap
(`Extern.isCheap`).
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
  deriving DecidableEq, Repr

instance {ks : List Nat} {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {c : Ctor ks b} :
    BEq (CtorIx cs c) := instBEqOfDecidableEq

/-- The join points in scope: the types of their parameters, innermost first.  A statement
    `Term Δ Γ τ js` may jump to any of them; each one then finishes the statement with an
    answer of type `τ`. -/
abbrev JCtx (ks : List Nat) : Type := List (Ty ks)

/-- A typed de Bruijn index of a join point. -/
abbrev JVar {ks : List Nat} (js : JCtx ks) (σ : Ty ks) : Type := DeBruijn js σ

/-! ## Cheap externs -/

/-- The operators and functions whose externs are cheap, by the name of the Lean function
    (`Comp.extern`'s `name`). -/
def Extern.cheapNames : List String :=
  ["HAdd.hAdd", "HSub.hSub", "HMul.hMul", "HDiv.hDiv", "HMod.hMod", "Neg.neg",
   "HAnd.hAnd", "HOr.hOr", "HXor.hXor", "HShiftLeft.hShiftLeft", "HShiftRight.hShiftRight",
   "Complement.complement", "Min.min", "Max.max", "BEq.beq", "bne", "not", "and", "or",
   "xor", "Bool.not", "Bool.and", "Bool.or", "Bool.xor", "Nat.succ", "Nat.pred", "Nat.add",
   "Nat.sub", "Nat.mul", "Nat.div", "Nat.mod", "Nat.min", "Nat.max", "Nat.land", "Nat.lor",
   "Nat.xor", "Nat.beq", "Nat.ble", "Nat.blt", "Nat.cast", "NatCast.natCast",
   "IntCast.intCast", "Int.neg", "Int.toNat", "Int.ofNat", "Int.natAbs", "Char.ofNat",
   "Char.toNat", "Char.val"]

/-- The relations whose decision (`decide (a < b)`, extern `"decide LT.lt"`) is cheap. -/
def Extern.cheapRelations : List String :=
  ["LT.lt", "LE.le", "GT.gt", "GE.ge", "Eq", "Ne", "Nat.lt", "Nat.le"]

/-- The namespaces of the fixed-width scalar types, all of whose functions on scalars are
    machine operations. -/
def Extern.cheapNamespaces : List String :=
  ["UInt8", "UInt16", "UInt32", "UInt64", "USize", "Int8", "Int16", "Int32", "Int64",
   "ISize", "Float", "Float32", "Char"]

/-- Is the extern of this name **cheap** (proposal 4h), so that the translator writes it as the
    pure expression `PExpr.extern` rather than the named computation `Comp.extern`: an
    arithmetic, bitwise, Boolean or comparison operator (`Extern.cheapNames`,
    `Extern.cheapRelations`), a conversion to a fixed-width type (`Nat.toUInt8`) or a
    function of a fixed-width type (`UInt16.ofNatLT`, `Float.sqrt`).  The translator also
    requires that every argument and the result are scalars (not a `String`, an `Array`, …),
    so `HAdd.hAdd` on strings or `Eq` on arrays stay `Comp.extern`. -/
def Extern.isCheap (name : String) : Bool :=
  Extern.cheapNames.contains name ||
    (name.startsWith "decide " && Extern.cheapRelations.contains (name.drop 7).toString) ||
    name.startsWith "Nat.toUInt" || name.startsWith "Nat.toInt" || name.startsWith "Nat.toFloat" ||
    Extern.cheapNamespaces.any fun ns => name.startsWith (ns ++ ".")

end LeanScript

end
