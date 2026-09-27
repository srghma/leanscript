module

public import LeanScript.Term.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Eliminations that reduce: the smart forms of `data_out`, `cond`, `ite` and `enum_casesOn`

The grammar of `LeanScript.Term` rules out ι-redexes: every elimination takes a *neutral*
expression (`Neu`).  When the value to take apart is an arbitrary pure expression — after a
substitution, or when a term is built by a program — the elimination is written with one of the
smart forms here, which **reduce** the redex when the value is an introduction form and build
the elimination of the neutral expression otherwise:

* `PExpr.mkDataOut b j e`: `e'` when `e` is `data_in b j e'`, else `data_out b j e`;
* `PExpr.mkCond c a b`: `a` or `b` when `c` is a literal, else `cond c a b`;
* `Term.mkIte c t e`: `t` or `e` when `c` is a literal, else `ite c t e`;
* `Term.mkEnumCases e bs`: `bs i` when `e` is `enum_mk s i`, else `enum_casesOn e bs`;
* `Branches.select brs ix`: the branch of the constructor `ix`, which `union_casesOn` of
  `union_mk ix args` reduces to (the reduction itself substitutes `args`, so it is in
  `LeanScript.Term.TermSubst`).

Each one means what the elimination means (`PExpr.eval_mkDataOut`, …).
-/

namespace LeanScript

/-- The members of the blocks of a signature have distinct names: `ref` is injective in the
    block and the member. -/
theorem DSig.Block.ref_inj : {ks : List Nat} → (Δ : DSig ks) → (b b' : BRef ks) →
    (j : Fin ((Δ.block b).k + 1)) → (j' : Fin ((Δ.block b').k + 1)) →
    (Δ.block b).ref j = (Δ.block b').ref j' → b = b' ∧ HEq j j'
  | _, .cons _ _ _, .here, .here, j, j', h => by
      simp only [DSig.Block.ref] at h
      cases h; exact ⟨rfl, HEq.rfl⟩
  | _, .cons _ _ _, .here, .there _, _, _, h => by
      simp only [DSig.Block.ref] at h; cases h
  | _, .cons _ _ _, .there _, .here, _, _, h => by
      simp only [DSig.Block.ref] at h; cases h
  | _, .cons Δ _ _, .there b, .there b', j, j', h => by
      obtain ⟨rfl, hj⟩ := DSig.Block.ref_inj Δ b b' j j' (Ref.there.inj h)
      exact ⟨rfl, hj⟩

section Smart
variable {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks}

/-- The unfolded bodies of two members with the same name are the same type. -/
theorem DSig.Block.unfold_eq_of_ref_eq {b b' : BRef ks} {j : Fin ((Δ.block b).k + 1)}
    {j' : Fin ((Δ.block b').k + 1)} (h : (Δ.block b').ref j' = (Δ.block b).ref j) :
    PExpr Δ Γ ((Δ.block b').unfold j') = PExpr Δ Γ ((Δ.block b).unfold j) := by
  obtain ⟨rfl, hj⟩ := DSig.Block.ref_inj Δ b' b j' j h
  cases hj; rfl

/-- `PExpr.mkDataOut` at a type known to be that of member `j` of block `b`. -/
def PExpr.mkDataOutAux (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
    {τ : Ty ks} → PExpr Δ Γ τ → τ = .data ((Δ.block b).ref j) →
    PExpr Δ Γ ((Δ.block b).unfold j)
  | _, .neu n, h => .neu (.data_out b j (h ▸ n))
  | _, .data_in _ _ e, h => cast (DSig.Block.unfold_eq_of_ref_eq (Ty.data.inj h)) e
  | _, .lit _ _, h => nomatch h
  | _, .enum_mk _ _, h => nomatch h
  | _, .record_mk _, h => nomatch h
  | _, .union_mk _ _, h => nomatch h
  | _, .array_mk _, h => nomatch h

/-- One layer out of a pure expression, reducing `data_out b j (data_in b j e)` to `e`. -/
abbrev PExpr.mkDataOut (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (e : PExpr Δ Γ (.data ((Δ.block b).ref j))) : PExpr Δ Γ ((Δ.block b).unfold j) :=
  PExpr.mkDataOutAux b j e rfl

theorem PExpr.eval_mkDataOutAux (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) (ρ : Env Δ Γ) :
    {τ : Ty ks} → (e : PExpr Δ Γ τ) → (h : τ = .data ((Δ.block b).ref j)) →
    (PExpr.mkDataOutAux b j e h).eval ρ = Δ.dataOut b j (h ▸ e.eval ρ)
  | _, .neu n, h => by
      subst h; rfl
  | _, .data_in b' j' e, h => by
      obtain ⟨rfl, hj⟩ := DSig.Block.ref_inj Δ b' b j' j (Ty.data.inj h)
      cases hj
      exact (DSig.dataOut_dataIn Δ b' j' _).symm
  | _, .lit _ _, h => nomatch h
  | _, .enum_mk _ _, h => nomatch h
  | _, .record_mk _, h => nomatch h
  | _, .union_mk _ _, h => nomatch h
  | _, .array_mk _, h => nomatch h

theorem PExpr.eval_mkDataOut (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (e : PExpr Δ Γ (.data ((Δ.block b).ref j))) (ρ : Env Δ Γ) :
    (PExpr.mkDataOut b j e).eval ρ = Δ.dataOut b j (e.eval ρ) :=
  PExpr.eval_mkDataOutAux b j ρ e rfl

/-- The pure conditional of a pure condition, reducing `cond (lit .bool v) a b` to `a` or
    `b`. -/
def PExpr.mkCond {τ : Ty ks} : PExpr Δ Γ .bool → PExpr Δ Γ τ → PExpr Δ Γ τ → PExpr Δ Γ τ
  | .neu c, a, b => .neu (.cond c a b)
  | .lit _ v, a, b => match (v : Bool) with
      | true => a
      | false => b

theorem PExpr.eval_mkCond {τ : Ty ks} (c : PExpr Δ Γ .bool) (a b : PExpr Δ Γ τ)
    (ρ : Env Δ Γ) : (PExpr.mkCond c a b).eval ρ = match (c.eval ρ : Bool) with
      | true => a.eval ρ
      | false => b.eval ρ := by
  cases c with
  | neu c => rfl
  | lit _ v =>
      simp only [PExpr.mkCond, PExpr.eval]
      cases (v : Bool) <;> rfl

/-- `if c then t else e` of a pure condition, reducing on a literal. -/
def Term.mkIte {τ : Ty ks} {js : JCtx ks} :
    PExpr Δ Γ .bool → Term Δ Γ τ js → Term Δ Γ τ js → Term Δ Γ τ js
  | .neu c, t, e => .ite c t e
  | .lit _ v, t, e => match (v : Bool) with
      | true => t
      | false => e

theorem Term.eval_mkIte {τ : Ty ks} {js : JCtx ks} (c : PExpr Δ Γ .bool) (t e : Term Δ Γ τ js)
    (ρ : Env Δ Γ) (κ : JEnv Δ τ js) : (Term.mkIte c t e).eval ρ κ =
      match (c.eval ρ : Bool) with
      | true => t.eval ρ κ
      | false => e.eval ρ κ := by
  cases c with
  | neu c => rfl
  | lit _ v =>
      simp only [Term.mkIte, PExpr.eval]
      cases (v : Bool) <;> rfl

/-- Case analysis of an enum given by a pure expression, reducing on a constructor. -/
def Term.mkEnumCases {s : LeanEnumSchema} {τ : Ty ks} {js : JCtx ks} :
    PExpr Δ Γ (.enum s) → (Fin s.nOfConstructors → Term Δ Γ τ js) → Term Δ Γ τ js
  | .neu e, bs => .enum_casesOn e bs
  | .enum_mk _ i, bs => bs i

theorem Term.eval_mkEnumCases {s : LeanEnumSchema} {τ : Ty ks} {js : JCtx ks}
    (e : PExpr Δ Γ (.enum s)) (bs : Fin s.nOfConstructors → Term Δ Γ τ js) (ρ : Env Δ Γ)
    (κ : JEnv Δ τ js) : (Term.mkEnumCases e bs).eval ρ κ = (bs (e.eval ρ)).eval ρ κ := by
  cases e <;> rfl

/-- The branch of constructor `ix`. -/
def Branches.select {js : JCtx ks} {τ : Ty ks} :
    {bs : List Bool} → {cs : Ctors ks bs} → {b : Bool} → {c : Ctor ks b} →
    Branches Δ Γ cs τ js → CtorIx cs c → Term Δ (c.binds ++ Γ) τ js
  | _, _, _, _, .two bc _, .two₁ => bc
  | _, _, _, _, .two _ bd, .two₂ => bd
  | _, _, _, _, .cons b _, .head => b
  | _, _, _, _, .cons _ bs, .tail ix => bs.select ix

end Smart

section Roundtrip
variable {ks : List Nat} {E : Ref ks → Type}

/-- The fields of a record built from a list of values are that list. -/
theorem Fields.toDL_ofDL : (fs : Fields ks) → (v : DenList E fs.toList) →
    Fields.toDL fs (Fields.ofDL fs v) = v
  | .one _, _ => rfl
  | .cons t fs, v => by
      simp only [Fields.toDL, Fields.ofDL]
      rw [Fields.toDL_ofDL fs v.tail]
      exact Tuple.cons_head_tail (F := Ty.den E) (a := t) (as := fs.toList) v

theorem Ctor.twoCase_inTwo₁ {a b : Bool} {R : Type} (c : Ctor ks a) (d : Ctor ks b)
    (v : DenList E c.binds) (k₁ : DenList E c.binds → R) (k₂ : DenList E d.binds → R) :
    Ctor.twoCase c d (Ctor.inTwo₁ c d v) k₁ k₂ = k₁ v := by
  cases c <;> cases d <;> simp only [Ctor.inTwo₁, Ctor.twoCase] <;> first | rfl | exact congrArg _ (Fields.toDL_ofDL _ v)

theorem Ctor.twoCase_inTwo₂ {a b : Bool} {R : Type} (c : Ctor ks a) (d : Ctor ks b)
    (v : DenList E d.binds) (k₁ : DenList E c.binds → R) (k₂ : DenList E d.binds → R) :
    Ctor.twoCase c d (Ctor.inTwo₂ c d v) k₁ k₂ = k₂ v := by
  cases c <;> cases d <;> simp only [Ctor.inTwo₂, Ctor.twoCase] <;> first | rfl | exact congrArg _ (Fields.toDL_ofDL _ v)

theorem Ctor.consCase_inHead {a : Bool} {R RT : Type} (c : Ctor ks a) (v : DenList E c.binds)
    (k₁ : DenList E c.binds → R) (k₂ : RT → R) :
    Ctor.consCase c (Ctor.inHead c v) k₁ k₂ = k₁ v := by
  cases c <;> simp only [Ctor.inHead, Ctor.consCase] <;> first | rfl | exact congrArg _ (Fields.toDL_ofDL _ v)

theorem Ctor.consCase_inTail {a : Bool} {R RT : Type} (c : Ctor ks a) (r : RT)
    (k₁ : DenList E c.binds → R) (k₂ : RT → R) :
    Ctor.consCase c (Ctor.inTail c r) k₁ k₂ = k₂ r := by
  cases c <;> simp only [Ctor.inTail, Ctor.consCase]

end Roundtrip

/-- Case analysis of a union built by constructor `ix` runs the branch of `ix` on its
    fields. -/
theorem Branches.eval_inject {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {js : JCtx ks}
    {τ : Ty ks} : {bs : List Bool} → {cs : Ctors ks bs} → {b : Bool} → {c : Ctor ks b} →
    (brs : Branches Δ Γ cs τ js) → (ix : CtorIx cs c) → (v : DenList (DSig.refDen Δ) c.binds) →
    (ρ : Env Δ Γ) → (κ : JEnv Δ τ js) →
    brs.eval ρ κ (ix.inject v) = (brs.select ix).eval (DenList.append v ρ) κ
  | _, _, _, _, .two _ _, .two₁, v, ρ, κ => by
      simp only [Branches.eval, Branches.select, CtorIx.inject]
      exact Ctor.twoCase_inTwo₁ _ _ v _ _
  | _, _, _, _, .two _ _, .two₂, v, ρ, κ => by
      simp only [Branches.eval, Branches.select, CtorIx.inject]
      exact Ctor.twoCase_inTwo₂ _ _ v _ _
  | _, _, _, _, .cons _ _, .head, v, ρ, κ => by
      simp only [Branches.eval, Branches.select, CtorIx.inject]
      exact Ctor.consCase_inHead _ v _ _
  | _, _, _, _, .cons _ bs, .tail ix, v, ρ, κ => by
      simp only [Branches.eval, Branches.select, CtorIx.inject]
      exact (Ctor.consCase_inTail _ _ _ _).trans (Branches.eval_inject bs ix v ρ κ)

end LeanScript

end
