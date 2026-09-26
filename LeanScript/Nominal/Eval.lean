module

public import LeanScript.Nominal.Term
public import LeanScript.Nominal.DenFacts

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of `Nominal.Term`

`Term.eval e env : Ty.Den Δ τ` — total, structural, no fuel.  The three datatype formers
evaluate to `DSig.dataIn`, `DSig.dataOut` and `DSig.dataRec`, so a translated program
computes by `rfl`.
-/

namespace LeanScript

namespace Nominal

/-- An environment: a value of every variable in scope. -/
abbrev Env {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : Type := DenList (DSig.refDen Δ) Γ

section Values
variable {ks : List Nat} {E : Ref ks → Type}

/-- The value of a variable. -/
def DenList.get : {Γ : List (Ty ks)} → {τ : Ty ks} → DenList E Γ → Var Γ τ → Ty.den E τ
  | _ :: _, _, v, .head => v.1
  | _ :: _, _, v, .tail x => DenList.get v.2 x

/-- Bind a list of values in front of an environment. -/
def DenList.append : {xs : List (Ty ks)} → {Γ : List (Ty ks)} → DenList E xs → DenList E Γ →
    DenList E (xs ++ Γ)
  | [], _, _, e => e
  | _ :: _, _, v, e => (v.1, DenList.append v.2 e)

/-- The fields of a record, as a list of values. -/
def Fields.toDL : (fs : Fields ks) → Fields.den E fs → DenList E fs.toList
  | .one _, x => (x, PUnit.unit)
  | .cons _ fs, x => (x.1, Fields.toDL fs x.2)

/-- A record's fields from a list of values. -/
def Fields.ofDL : (fs : Fields ks) → DenList E fs.toList → Fields.den E fs
  | .one _, v => v.1
  | .cons _ fs, v => (v.1, Fields.ofDL fs v.2)

/-- The first of two constructors. -/
def Ctor.inTwo₁ : (c d : Ctor ks) → DenList E c.binds → twoT (Ctor.den E c) (Ctor.den E d)
  | .nullary, .nullary, _ => false
  | .nullary, .fields _, _ => none
  | .fields fs, .nullary, v => some (Fields.ofDL fs v)
  | .fields fs, .fields _, v => .inl (Fields.ofDL fs v)

/-- The second of two constructors. -/
def Ctor.inTwo₂ : (c d : Ctor ks) → DenList E d.binds → twoT (Ctor.den E c) (Ctor.den E d)
  | .nullary, .nullary, _ => true
  | .nullary, .fields fs, v => some (Fields.ofDL fs v)
  | .fields _, .nullary, _ => none
  | .fields _, .fields fs, v => .inr (Fields.ofDL fs v)

/-- The constructor in front of the others. -/
def Ctor.inHead {R : Type} : (c : Ctor ks) → DenList E c.binds → consT (Ctor.den E c) R
  | .nullary, _ => none
  | .fields fs, v => .inl (Fields.ofDL fs v)

/-- One of the constructors behind the first. -/
def Ctor.inTail {R : Type} : (c : Ctor ks) → R → consT (Ctor.den E c) R
  | .nullary, r => some r
  | .fields _, r => .inr r

/-- A value of a union from one of its constructors and that constructor's fields. -/
def CtorIx.inject : {cs : Ctors ks} → {c : Ctor ks} → CtorIx cs c → DenList E c.binds →
    Ctors.den E cs
  | .two c d, _, .two₁, v => Ctor.inTwo₁ c d v
  | .two c d, _, .two₂, v => Ctor.inTwo₂ c d v
  | .cons c _, _, .head, v => Ctor.inHead c v
  | .cons c _, _, .tail ix, v => Ctor.inTail c (CtorIx.inject ix v)

/-- Case analysis of a value of two constructors. -/
def Ctor.twoCase {R : Type} : (c d : Ctor ks) → twoT (Ctor.den E c) (Ctor.den E d) →
    (DenList E c.binds → R) → (DenList E d.binds → R) → R
  | .nullary, .nullary, b, k₁, k₂ => match b with | false => k₁ PUnit.unit | true => k₂ PUnit.unit
  | .nullary, .fields fs, o, k₁, k₂ =>
      match o with | none => k₁ PUnit.unit | some x => k₂ (Fields.toDL fs x)
  | .fields fs, .nullary, o, k₁, k₂ =>
      match o with | some x => k₁ (Fields.toDL fs x) | none => k₂ PUnit.unit
  | .fields fc, .fields fd, x, k₁, k₂ =>
      match x with | .inl a => k₁ (Fields.toDL fc a) | .inr b => k₂ (Fields.toDL fd b)

/-- Case analysis of a value of a constructor in front of the others. -/
def Ctor.consCase {R RT : Type} : (c : Ctor ks) → consT (Ctor.den E c) RT →
    (DenList E c.binds → R) → (RT → R) → R
  | .nullary, o, k₁, k₂ => match o with | none => k₁ PUnit.unit | some r => k₂ r
  | .fields fs, x, k₁, k₂ => match x with | .inl a => k₁ (Fields.toDL fs a) | .inr r => k₂ r

end Values

/-- `Nat.rec` with a non-dependent motive, by structural recursion. -/
def natIter {α : Type} (z : α) (s : Nat → α → α) : Nat → α
  | 0 => z
  | n + 1 => s n (natIter z s n)

section Eval
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- The value of a term in an environment. -/
def Term.eval : {Γ : Ctx ks} → {τ : Ty ks} → Term Δ Γ τ → Env Δ Γ → Ty.Den Δ τ
  | _, _, .var x, ρ => ρ.get x
  | _, _, .letE e b, ρ => b.eval (e.eval ρ, ρ)
  | _, _, .lam b, ρ => fun v => b.eval (v, ρ)
  | _, _, .app f a, ρ => f.eval ρ (a.eval ρ)
  | _, _, .lit _ _ v, _ => v
  | _, _, .extern _ f args, ρ => f (args.eval ρ)
  | _, _, .ite c t e, ρ => match (c.eval ρ : Bool) with
      | true => t.eval ρ
      | false => e.eval ρ
  | _, _, .nat_rec n z s, ρ =>
      natIter (z.eval ρ) (fun k acc => s.eval (acc, k, ρ)) (n.eval ρ)
  | _, _, .enum_mk _ i, _ => i
  | _, _, .enum_casesOn e bs, ρ => (bs (e.eval ρ)).eval ρ
  | _, _, .record_mk (fs := fs) args, ρ =>
      let v := args.eval ρ
      (v.1, Fields.ofDL fs v.2)
  | _, _, .record_casesOn (fs := fs) e body, ρ =>
      let x := e.eval ρ
      body.eval (DenList.append (x.1, Fields.toDL fs x.2) ρ)
  | _, _, .union_mk ix args, ρ => ix.inject (args.eval ρ)
  | _, _, .union_casesOn e bs, ρ => bs.eval ρ (e.eval ρ)
  | _, _, .array_mk es, ρ => (es.eval ρ).toArray
  | _, _, .array_foldl a z s, ρ =>
      (a.eval ρ).foldl (fun acc x => s.eval (x, acc, ρ)) (z.eval ρ)
  | _, _, .thunk_mk e, ρ => e.eval ρ
  | _, _, .thunk_force e, ρ => e.eval ρ
  | _, _, .lazy_mk e, ρ => e.eval ρ
  | _, _, .lazy_force e, ρ => e.eval ρ
  | _, _, .data_in b j e, ρ => Δ.dataIn b j (e.eval ρ)
  | _, _, .data_out b j e, ρ => Δ.dataOut b j (e.eval ρ)
  | _, _, .data_rec b ρt brs j e, ρ => Δ.dataRec b ρt (fun i x => (brs i).eval (x, ρ)) j (e.eval ρ)
  termination_by structural _ _ e _ => e
/-- The values of the arguments. -/
def Args.eval : {Γ : Ctx ks} → {σs : List (Ty ks)} → Args Δ Γ σs → Env Δ Γ →
    DenList (DSig.refDen Δ) σs
  | _, _, .nil, _ => PUnit.unit
  | _, _, .cons a as, ρ => (a.eval ρ, as.eval ρ)
  termination_by structural _ _ a _ => a
/-- Dispatch a value of a union to its branch. -/
def Branches.eval : {Γ : Ctx ks} → {cs : Ctors ks} → {τ : Ty ks} → Branches Δ Γ cs τ →
    Env Δ Γ → Ctors.den (DSig.refDen Δ) cs → Ty.Den Δ τ
  | _, _, _, .two (c := c) (d := d) bc bd, ρ, x =>
      Ctor.twoCase c d x (fun v => bc.eval (DenList.append v ρ)) (fun v => bd.eval (DenList.append v ρ))
  | _, _, _, .cons (c := c) b bs, ρ, x =>
      Ctor.consCase c x (fun v => b.eval (DenList.append v ρ)) (fun r => bs.eval ρ r)
  termination_by structural _ _ _ b _ _ => b
/-- The values of the elements of an array literal. -/
def Elems.eval : {Γ : Ctx ks} → {t : Ty ks} → Elems Δ Γ t → Env Δ Γ → List (Ty.Den Δ t)
  | _, _, .nil, _ => []
  | _, _, .cons e es, ρ => e.eval ρ :: es.eval ρ
  termination_by structural _ _ e _ => e
end

end Eval

/-- `data_out` undoes `data_in`: one layer out of a layer just put on is the value it was
    built from. -/
theorem Term.eval_data_out_data_in {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (b : BRef ks)
    (j : Fin ((Δ.block b).k + 1)) (e : Term Δ Γ ((Δ.block b).unfold j)) (ρ : Env Δ Γ) :
    (Term.data_out b j (.data_in b j e)).eval ρ = e.eval ρ := by
  simp only [Term.eval]
  exact DSig.dataOut_dataIn Δ b j _

/-- The value of a closed term. -/
abbrev Term.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} (e : Term Δ [] τ) : Ty.Den Δ τ :=
  e.eval PUnit.unit

end Nominal

end LeanScript

end
