module

public import LeanScript.Term.Term
public import LeanScript.Ty.DenFacts

@[expose] public section

set_option autoImplicit false

/-!
# The evaluators of the three layers of `Term`

`PExpr.eval e env`, `Comp.eval c env : Ty.Den Δ τ` and `Term.eval t env κ : Ty.Den Δ τ`, where
`κ : JEnv Δ τ js` holds the closures of the join points in scope — total, structural, no
fuel.  Environments and `JEnv`s are `Tuple`s, so they have no trailing `PUnit`: a value is
bound in front with `Tuple.cons` and read with `Tuple.get`.  `PExpr.eval` is not mutual with the two others.  The datatype formers evaluate to
`DSig.dataIn`, `DSig.dataOut`, `DSig.dataRec` and `DSig.dataBrec`, so a translated program
computes by `rfl`.
-/

namespace LeanScript



/-- An environment: a value of every variable in scope. -/
abbrev Env {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : Type := DenList (DSig.refDen Δ) Γ

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

/-- The values of the join points in scope, for statements of type `τ`: each one is the
    closure of its body over the environment it was defined in.  A `Tuple`, so there is no
    trailing `PUnit`: `JEnv Δ τ [σ₁, σ₂] = (Ty.Den Δ σ₁ → Ty.Den Δ τ) × (Ty.Den Δ σ₂ → Ty.Den Δ τ)`,
    `JEnv Δ τ [σ] = (Ty.Den Δ σ → Ty.Den Δ τ)` and `JEnv Δ τ [] = PUnit`. -/
abbrev JEnv {ks : List Nat} (Δ : DSig ks) (τ : Ty ks) : JCtx ks → Type :=
  Tuple (fun σ => Ty.Den Δ σ → Ty.Den Δ τ)

/-- The closure of a join point. -/
abbrev JEnv.get {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} {js : JCtx ks} {σ : Ty ks}
    (κ : JEnv Δ τ js) (j : JVar js σ) : Ty.Den Δ σ → Ty.Den Δ τ :=
  Tuple.get κ j

section Eval
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- The value of a pure expression in an environment. -/
def PExpr.eval {Γ : Ctx ks} : {τ : Ty ks} → PExpr Δ Γ τ → Env Δ Γ → Ty.Den Δ τ
  | _, .var x, ρ => ρ.get x
  | _, .lit _ v, _ => v
  | _, .enum_mk _ i, _ => i
  | _, .record_mk (fs := fs) args, ρ =>
      let v := args.eval ρ
      (v.head, Fields.ofDL fs v.tail)
  | _, .union_mk ix args, ρ => ix.inject (args.eval ρ)
  | _, .array_mk es, ρ => (es.eval ρ).toArray
  | _, .data_in b j e, ρ => Δ.dataIn b j (e.eval ρ)
  | _, .data_out b j e, ρ => Δ.dataOut b j (e.eval ρ)
  | _, .cond c a b, ρ => match (c.eval ρ : Bool) with
      | true => a.eval ρ
      | false => b.eval ρ
  | _, .extern _ f args, ρ => f (args.eval ρ)
  termination_by structural _ e _ => e
/-- The values of the arguments. -/
def Args.eval {Γ : Ctx ks} : {σs : List (Ty ks)} → Args Δ Γ σs → Env Δ Γ →
    DenList (DSig.refDen Δ) σs
  | _, .nil, _ => PUnit.unit
  | _, .cons a as, ρ => Tuple.cons (a.eval ρ) (as.eval ρ)
  termination_by structural _ a _ => a
/-- The values of the elements of an array literal. -/
def Elems.eval {Γ : Ctx ks} : {t : Ty ks} → Elems Δ Γ t → Env Δ Γ → List (Ty.Den Δ t)
  | _, .nil, _ => []
  | _, .cons e es, ρ => e.eval ρ :: es.eval ρ
  termination_by structural _ e _ => e
end

mutual
/-- The value of a computation in an environment. -/
def Comp.eval : {Γ : Ctx ks} → {τ : Ty ks} → Comp Δ Γ τ → Env Δ Γ → Ty.Den Δ τ
  | _, _, .app f a, ρ => f.eval ρ (a.eval ρ)
  | _, _, .lam b, ρ => fun v => b.eval (Tuple.cons v ρ) PUnit.unit
  | _, _, .share e, ρ => e.eval ρ
  | _, _, .extern _ f args, ρ => f (args.eval ρ)
  | _, _, .nat_rec n z s, ρ =>
      natIter (z.eval ρ) (fun k acc => s.eval (Tuple.cons acc (Tuple.cons k ρ)) PUnit.unit)
        (n.eval ρ)
  | _, _, .array_foldl a z s, ρ =>
      (a.eval ρ).foldl (fun acc x => s.eval (Tuple.cons x (Tuple.cons acc ρ)) PUnit.unit)
        (z.eval ρ)
  | _, _, .data_rec b ρt brs j e, ρ =>
      Δ.dataRec b ρt (fun i x => (brs i).eval (Tuple.cons x ρ) PUnit.unit) j (e.eval ρ)
  | _, _, .data_brec b ρt k brs j e, ρ =>
      Δ.dataBrec b ρt k (fun i x => (brs i).eval (Tuple.cons x ρ) PUnit.unit) j (e.eval ρ)
  | _, _, .thunk_mk (τ := τ) e, ρ => Ty.ofRelax _ τ (e.eval ρ PUnit.unit)
  | _, _, .thunk_force (τ := τ) e, ρ => Ty.toRelax _ τ (e.eval ρ)
  | _, _, .lazy_mk (τ := τ) e, ρ => Ty.ofRelax _ τ (e.eval ρ PUnit.unit)
  | _, _, .lazy_force (τ := τ) e, ρ => Ty.toRelax _ τ (e.eval ρ)
  termination_by structural _ _ c _ => c
/-- The value of a statement in an environment, given the closures of its join points. -/
def Term.eval : {Γ : Ctx ks} → {τ : Ty ks} → {js : JCtx ks} → Term Δ Γ τ js → Env Δ Γ →
    JEnv Δ τ js → Ty.Den Δ τ
  | _, _, _, .ret e, ρ, _ => e.eval ρ
  | _, _, _, .letE c b, ρ, κ => b.eval (Tuple.cons (c.eval ρ) ρ) κ
  | _, _, _, .record_casesOn (fs := fs) e body, ρ, κ =>
      let x := e.eval ρ
      body.eval (DenList.append (Tuple.cons x.1 (Fields.toDL fs x.2)) ρ) κ
  | _, _, _, .ite c t e, ρ, κ => match (c.eval ρ : Bool) with
      | true => t.eval ρ κ
      | false => e.eval ρ κ
  | _, _, _, .enum_casesOn e bs, ρ, κ => (bs (e.eval ρ)).eval ρ κ
  | _, _, _, .union_casesOn e bs, ρ, κ => bs.eval ρ κ (e.eval ρ)
  | _, _, _, .join _ body main, ρ, κ => main.eval ρ (Tuple.cons (fun v => body.eval (Tuple.cons v ρ) κ) κ)
  | _, _, _, .jump j e, ρ, κ => κ.get j (e.eval ρ)
  termination_by structural _ _ _ t _ _ => t
/-- Dispatch a value of a union to its branch. -/
def Branches.eval : {Γ : Ctx ks} → {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} →
    {js : JCtx ks} → Branches Δ Γ cs τ js → Env Δ Γ → JEnv Δ τ js →
    Ctors.den (DSig.refDen Δ) cs → Ty.Den Δ τ
  | _, _, _, _, _, .two (c := c) (d := d) bc bd, ρ, κ, x =>
      Ctor.twoCase c d x (fun v => bc.eval (DenList.append v ρ) κ)
        (fun v => bd.eval (DenList.append v ρ) κ)
  | _, _, _, _, _, .cons (c := c) b bs, ρ, κ, x =>
      Ctor.consCase c x (fun v => b.eval (DenList.append v ρ) κ) (fun r => bs.eval ρ κ r)
  termination_by structural _ _ _ _ _ b _ _ _ => b
end

end Eval

/-- `data_out` undoes `data_in`: one layer out of a layer just put on is the value it was
    built from. -/
theorem PExpr.eval_data_out_data_in {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (b : BRef ks)
    (j : Fin ((Δ.block b).k + 1)) (e : PExpr Δ Γ ((Δ.block b).unfold j)) (ρ : Env Δ Γ) :
    (PExpr.data_out b j (.data_in b j e)).eval ρ = e.eval ρ := by
  simp only [PExpr.eval]
  exact DSig.dataOut_dataIn Δ b j _

/-- Course-of-values recursion on a value built by `data_in` runs the branch of its member on
    its body, every child replaced by its window (`DSig.dataBrec_dataIn`). -/
theorem Comp.eval_data_brec_data_in {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (b : BRef ks)
    (ρt : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
    (brs : (i : Fin ((Δ.block b).k + 1)) → Term Δ ((Δ.block b).brecBody ρt k i :: Γ) (ρt i) [])
    (j : Fin ((Δ.block b).k + 1)) (e : PExpr Δ Γ ((Δ.block b).unfold j)) (ρ : Env Δ Γ) :
    (Comp.data_brec b ρt k brs j (.data_in b j e)).eval ρ =
      (brs j).eval (Tuple.cons ((Δ.block b).mapInst
        (fun i c => Δ.dataWin b ρt k (fun i x => (brs i).eval (Tuple.cons x ρ) PUnit.unit) i c) j
          (e.eval ρ)) ρ) PUnit.unit := by
  simp only [Comp.eval, PExpr.eval]
  exact DSig.dataBrec_dataIn Δ b ρt k _ j _

/-- The fold on a value built by `data_in` runs the branch of its member on its body, every
    child replaced by the pair of the child and the answer at it (`DSig.dataRec_dataIn`). -/
theorem Comp.eval_data_rec_data_in {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (b : BRef ks)
    (ρt : Fin ((Δ.block b).k + 1) → Ty ks)
    (brs : (i : Fin ((Δ.block b).k + 1)) → Term Δ ((Δ.block b).recBody ρt i :: Γ) (ρt i) [])
    (j : Fin ((Δ.block b).k + 1)) (e : PExpr Δ Γ ((Δ.block b).unfold j)) (ρ : Env Δ Γ) :
    (Comp.data_rec b ρt brs j (.data_in b j e)).eval ρ =
      (brs j).eval (Tuple.cons ((Δ.block b).mapInst
        (σ' := fun i => Ty.pair (.data ((Δ.block b).ref i)) (ρt i))
        (fun i c => (c, Δ.dataRec b ρt (fun i x => (brs i).eval (Tuple.cons x ρ) PUnit.unit) i c)) j
          (e.eval ρ)) ρ) PUnit.unit := by
  simp only [Comp.eval, PExpr.eval]
  exact DSig.dataRec_dataIn Δ b ρt _ j _

/-- The value of a closed statement with no join point in scope. -/
abbrev Term.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} (e : Term Δ [] τ []) : Ty.Den Δ τ :=
  e.eval PUnit.unit PUnit.unit

/-- The value of a closed pure expression. -/
abbrev PExpr.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} (e : PExpr Δ [] τ) : Ty.Den Δ τ :=
  e.eval PUnit.unit

/-- The value of a closed computation. -/
abbrev Comp.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} (c : Comp Δ [] τ) : Ty.Den Δ τ :=
  c.eval PUnit.unit

end LeanScript

end
