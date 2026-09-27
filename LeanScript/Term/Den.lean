module

public import LeanScript.Term.Common
public import LeanScript.Term.ExternEval
public import LeanScript.Ty.DenFacts

@[expose] public section

set_option autoImplicit false

/-!
# Values of records, unions and loops

The value-level helpers the evaluator of `LeanScript.Term` (`LeanScript.Term.Eval`) is written
with: the fields of a record as a list of values and back (`Fields.toDL`, `Fields.ofDL`), the
value of a union from a constructor and its fields (`CtorIx.inject`) and its case analysis
(`Ctor.twoCase`, `Ctor.consCase`), and `Nat.rec` with a non-dependent motive (`natIter`).
-/

namespace LeanScript

section Values
variable {ks : List Nat} {E : Ref ks → Type}

/-- The value of a variable. -/
abbrev DenList.get {Γ : List (Ty ks)} {τ : Ty ks} (v : DenList E Γ) (x : Var Γ τ) : Ty.den E τ :=
  Tuple.get v x

/-- Bind a list of values in front of an environment. -/
abbrev DenList.append {xs : List (Ty ks)} {Γ : List (Ty ks)} (v : DenList E xs)
    (e : DenList E Γ) : DenList E (xs ++ Γ) :=
  Tuple.append v e

/-- The fields of a record, as a list of values. -/
def Fields.toDL : (fs : Fields ks) → Fields.den E fs → DenList E fs.toList
  | .one _, x => x
  | .cons _ fs, x => Tuple.cons x.1 (Fields.toDL fs x.2)

/-- A record's fields from a list of values. -/
def Fields.ofDL : (fs : Fields ks) → DenList E fs.toList → Fields.den E fs
  | .one _, v => v
  | .cons _ fs, v => (v.head, Fields.ofDL fs v.tail)

/-- The first of two constructors. -/
def Ctor.inTwo₁ {a b : Bool} : (c : Ctor ks a) → (d : Ctor ks b) → DenList E c.binds → twoT (Ctor.den E c) (Ctor.den E d)
  | .nullary, .nullary, _ => false
  | .nullary, .fields _, _ => none
  | .fields fs, .nullary, v => some (Fields.ofDL fs v)
  | .fields fs, .fields _, v => .inl (Fields.ofDL fs v)

/-- The second of two constructors. -/
def Ctor.inTwo₂ {a b : Bool} : (c : Ctor ks a) → (d : Ctor ks b) → DenList E d.binds → twoT (Ctor.den E c) (Ctor.den E d)
  | .nullary, .nullary, _ => true
  | .nullary, .fields fs, v => some (Fields.ofDL fs v)
  | .fields _, .nullary, _ => none
  | .fields _, .fields fs, v => .inr (Fields.ofDL fs v)

/-- The constructor in front of the others. -/
def Ctor.inHead {a : Bool} {R : Type} : (c : Ctor ks a) → DenList E c.binds → consT (Ctor.den E c) R
  | .nullary, _ => none
  | .fields fs, v => .inl (Fields.ofDL fs v)

/-- One of the constructors behind the first. -/
def Ctor.inTail {a : Bool} {R : Type} : (c : Ctor ks a) → R → consT (Ctor.den E c) R
  | .nullary, r => some r
  | .fields _, r => .inr r

/-- A value of a union from one of its constructors and that constructor's fields. -/
def CtorIx.inject : {bs : List Bool} → {b : Bool} → {cs : Ctors ks bs} → {c : Ctor ks b} → CtorIx cs c → DenList E c.binds →
    Ctors.den E cs
  | _, _, .two c d, _, .two₁, v => Ctor.inTwo₁ c d v
  | _, _, .two c d, _, .two₂, v => Ctor.inTwo₂ c d v
  | _, _, .cons c _, _, .head, v => Ctor.inHead c v
  | _, _, .cons c _, _, .tail ix, v => Ctor.inTail c (CtorIx.inject ix v)

/-- Case analysis of a value of two constructors. -/
def Ctor.twoCase {a b : Bool} {R : Type} : (c : Ctor ks a) → (d : Ctor ks b) → twoT (Ctor.den E c) (Ctor.den E d) →
    (DenList E c.binds → R) → (DenList E d.binds → R) → R
  | .nullary, .nullary, b, k₁, k₂ => match b with | false => k₁ PUnit.unit | true => k₂ PUnit.unit
  | .nullary, .fields fs, o, k₁, k₂ =>
      match o with | none => k₁ PUnit.unit | some x => k₂ (Fields.toDL fs x)
  | .fields fs, .nullary, o, k₁, k₂ =>
      match o with | some x => k₁ (Fields.toDL fs x) | none => k₂ PUnit.unit
  | .fields fc, .fields fd, x, k₁, k₂ =>
      match x with | .inl a => k₁ (Fields.toDL fc a) | .inr b => k₂ (Fields.toDL fd b)

/-- Case analysis of a value of a constructor in front of the others. -/
def Ctor.consCase {a : Bool} {R RT : Type} : (c : Ctor ks a) → consT (Ctor.den E c) RT →
    (DenList E c.binds → R) → (RT → R) → R
  | .nullary, o, k₁, k₂ => match o with | none => k₁ PUnit.unit | some r => k₂ r
  | .fields fs, x, k₁, k₂ => match x with | .inl a => k₁ (Fields.toDL fs a) | .inr r => k₂ r

end Values

/-- `Nat.rec` with a non-dependent motive, by structural recursion. -/
def natIter {α : Type} (z : α) (s : Nat → α → α) : Nat → α
  | 0 => z
  | n + 1 => s n (natIter z s n)

end LeanScript

end
