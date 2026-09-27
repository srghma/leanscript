module

public import LeanScript.Term.Term
public import LeanScript.Term.Den

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of normal-form terms

`Term.eval t κ ρ jκ : Ty.Den Δ τ`, where `κ : KEnv Δ Φ` holds the known values, `ρ : UEnv Δ Γ`
the unknowns and `jκ : JEnv Δ τ js` the closures of the join points.  Total and structural, as
for `LeanScript.Term`; it reuses the value-level helpers of `LeanScript.Term.Eval`
(`Fields.ofDL`, `CtorIx.inject`, `Ctor.twoCase`, `natIter`, …).  Depths, levels and usages
play no role in the value.
-/

namespace LeanScript

/-- Values of the unknowns in scope. -/
abbrev UEnv {ks : List Nat} (Δ : DSig ks) (Γ : UCtx ks) : Type :=
  Tuple (fun b : UBinder ks => Ty.Den Δ b.ty) Γ

/-- Values of the known values in scope. -/
abbrev KEnv {ks : List Nat} (Δ : DSig ks) (Φ : KCtx ks) : Type :=
  Tuple (fun b : KBinder ks => Ty.Den Δ b.ty) Φ

/-- The closures of the join points in scope, for statements of type `τ`. -/
abbrev JEnv {ks : List Nat} (Δ : DSig ks) (τ : Ty ks) (js : JCtx ks) : Type :=
  Tuple (fun b : JBinder ks => Ty.Den Δ b.ty → Ty.Den Δ τ) js

section Env
variable {ks : List Nat} {Δ : DSig ks}

/-- The value of an unknown in an environment. -/
def UEnv.get : {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} → UEnv Δ Γ → UVar Γ τ ℓ → Ty.Den Δ τ
  | _ :: _, _, _, ρ, .head _ => ρ.head
  | _ :: _, _, _, ρ, .tail x => UEnv.get ρ.tail x

/-- The closure of a join point. -/
def JEnv.get {τ : Ty ks} : {js : JCtx ks} → {σ : Ty ks} → JEnv Δ τ js → JVar js σ →
    Ty.Den Δ σ → Ty.Den Δ τ
  | _ :: _, _, κ, .head => κ.head
  | _ :: _, _, κ, .tail x => JEnv.get κ.tail x

/-- The value of a known variable. -/
def KEnv.get : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} → KEnv Δ Φ → KVar Φ τ o → Ty.Den Δ τ
  | _ :: _, _, _, κ, .head => κ.head
  | _ :: _, _, _, κ, .tail x => KEnv.get κ.tail x

/-- The known values, as seen from a closed body (the same values). -/
def KEnv.closedOnly : {Φ : KCtx ks} → KEnv Δ Φ → KEnv Δ (KCtx.closedOnly Φ)
  | [], _ => PUnit.unit
  | ⟨_, _, some _, _⟩ :: _, κ => Tuple.cons κ.head (KEnv.closedOnly κ.tail)
  | ⟨_, _, none, _⟩ :: _, κ => Tuple.cons κ.head (KEnv.closedOnly κ.tail)

/-- The values of fields, as an environment of annotated binders. -/
def UEnv.ofDL (ℓ : Nat) : (ts : List (Ty ks)) → (us : List Usage01ω) →
    DenList (DSig.refDen Δ) ts → UEnv Δ (UCtx.annot ℓ ts us)
  | [], _, _ => PUnit.unit
  | _ :: ts, [], v => Tuple.cons v.head (UEnv.ofDL ℓ ts [] v.tail)
  | _ :: ts, _ :: us, v => Tuple.cons v.head (UEnv.ofDL ℓ ts us v.tail)

end Env

section Eval
variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- The value of a neutral expression. -/
def Neu.eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ →
    KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | _, _, .var x, _, ρ => ρ.get x
  | _, _, .data_out b j e, κ, ρ => Δ.dataOut b j (e.eval κ ρ)
  | _, _, .cond c a b, κ, ρ => match (c.eval κ ρ : Bool) with
      | true => a.eval κ ρ
      | false => b.eval κ ρ
  | _, _, .extern e args _, κ, ρ => Extern.eval (DSig.refDen Δ) e (args.eval κ ρ)
  termination_by structural _ _ e _ _ => e
/-- The value of a pure expression. -/
def PExpr.eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | _, _, .neu n, κ, ρ => n.eval κ ρ
  | _, _, .kvar k, κ, _ => κ.get k
  | _, _, .lit _ v, _, _ => v
  | _, _, .enum_mk _ i, _, _ => i
  | _, _, .record_mk (fs := fs) args, κ, ρ =>
      let v := args.eval κ ρ
      (v.head, Fields.ofDL fs v.tail)
  | _, _, .union_mk ix args, κ, ρ => ix.inject (args.eval κ ρ)
  | _, _, .array_mk es, κ, ρ => (es.eval κ ρ).toArray
  | _, _, .list_mk es, κ, ρ => es.eval κ ρ
  | _, _, .data_in b j e, κ, ρ => Δ.dataIn b j (e.eval κ ρ)
  termination_by structural _ _ e _ _ => e
/-- The values of arguments. -/
def Args.eval {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → KEnv Δ Φ → UEnv Δ Γ → DenList (DSig.refDen Δ) σs
  | _, _, .nil, _, _ => PUnit.unit
  | _, _, .cons a as, κ, ρ => Tuple.cons (a.eval κ ρ) (as.eval κ ρ)
  termination_by structural _ _ a _ _ => a
/-- The values of the elements of a literal. -/
def Elems.eval {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    KEnv Δ Φ → UEnv Δ Γ → List (Ty.Den Δ t)
  | _, _, .nil, _, _ => []
  | _, _, .cons e es, κ, ρ => e.eval κ ρ :: es.eval κ ρ
  termination_by structural _ _ e _ _ => e
end

mutual
/-- The value of a value. -/
def Val.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | _, _, _, _, _, .lam b, κ, ρ => fun v => b.eval κ ρ (Tuple.cons v Tuple.nil)
  | _, _, _, _, _, .thunk_mk (τ := τ) b, κ, ρ => Ty.ofRelax _ τ (b.eval κ ρ Tuple.nil)
  | _, _, _, _, _, .lazy_mk (τ := τ) b, κ, ρ => Ty.ofRelax _ τ (b.eval κ ρ Tuple.nil)
  | _, _, _, _, _, .record_mk (fs := fs) args, κ, ρ =>
      let v := args.eval κ ρ
      (v.head, Fields.ofDL fs v.tail)
  | _, _, _, _, _, .union_mk ix args, κ, ρ => ix.inject (args.eval κ ρ)
  | _, _, _, _, _, .array_mk es, κ, ρ => (es.eval κ ρ).toArray
  | _, _, _, _, _, .list_mk es, κ, ρ => es.eval κ ρ
  | _, _, _, _, _, .data_in b j e, κ, ρ => Δ.dataIn b j (e.eval κ ρ)
  termination_by structural _ _ _ _ _ v _ _ => v
/-- The value of a body, given the values of its binders. -/
def Body.eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → KEnv Δ Φ → UEnv Δ Γ → UEnv Δ bs → Ty.Den Δ τ
  | _, _, _, _, _, _, .closed t, κ, _, vs => t.eval κ.closedOnly vs PUnit.unit
  | _, _, _, _, _, _, .opened t _, κ, ρ, vs => t.eval κ (Tuple.append vs ρ) PUnit.unit
  termination_by structural _ _ _ _ _ _ b _ _ _ => b
/-- The value of a computation. -/
def Comp.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | _, _, _, _, _, .app f a _, κ, ρ => f.eval κ ρ (a.eval κ ρ)
  | _, _, _, _, _, .share n, κ, ρ => n.eval κ ρ
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ =>
      natIter (z.eval κ ρ)
        (fun k acc => s.eval κ ρ (Tuple.cons acc (Tuple.cons k Tuple.nil))) (n.eval κ ρ)
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ =>
      (a.eval κ ρ).foldl (fun acc x => s.eval κ ρ (Tuple.cons x (Tuple.cons acc Tuple.nil)))
        (z.eval κ ρ)
  | _, _, _, _, _, .data_rec b ρt _ brs j e _, κ, ρ =>
      Δ.dataRec b ρt (fun i x => (brs i).eval κ ρ (Tuple.cons x Tuple.nil)) j (e.eval κ ρ)
  | _, _, _, _, _, .data_brec b ρt k _ brs j e _, κ, ρ =>
      Δ.dataBrec b ρt k (fun i x => (brs i).eval κ ρ (Tuple.cons x Tuple.nil)) j (e.eval κ ρ)
  | _, _, _, _, _, .thunk_force (τ := τ) e, κ, ρ => Ty.toRelax _ τ (e.eval κ ρ)
  | _, _, _, _, _, .lazy_force (τ := τ) e, κ, ρ => Ty.toRelax _ τ (e.eval κ ρ)
  termination_by structural _ _ _ _ _ c _ _ => c
/-- The value of a statement. -/
def Term.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → KEnv Δ Φ → UEnv Δ Γ → JEnv Δ τ js → Ty.Den Δ τ
  | _, _, _, _, _, _, .ret e, κ, ρ, _ => e.eval κ ρ
  | _, _, _, _, _, _, .letV _ v b, κ, ρ, jκ => b.eval (Tuple.cons (v.eval κ ρ) κ) ρ jκ
  | _, _, _, _, _, _, .letE _ c b, κ, ρ, jκ => b.eval κ (Tuple.cons (c.eval κ ρ) ρ) jκ
  | d, _, _, _, _, _, .record_casesOn (fs := fs) us e body, κ, ρ, jκ =>
      let x := e.eval κ ρ
      body.eval κ (Tuple.append (UEnv.ofDL d _ us (Tuple.cons x.1 (Fields.toDL fs x.2))) ρ) jκ
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => br.eval κ ρ jκ
  | _, _, _, _, _, _, .jump j e, κ, ρ, jκ => jκ.get j (e.eval κ ρ)
  termination_by structural _ _ _ _ _ _ t _ _ _ => t
/-- The value of a branch. -/
def Branch.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → KEnv Δ Φ → UEnv Δ Γ → JEnv Δ τ js → Ty.Den Δ τ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => match (c.eval κ ρ : Bool) with
      | true => t.eval κ ρ jκ
      | false => e.eval κ ρ jκ
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => (bs (e.eval κ ρ)).eval κ ρ jκ
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => bs.eval κ ρ jκ (e.eval κ ρ)
  | _, _, _, _, _, _, .join _ _ _ body main, κ, ρ, jκ =>
      main.eval κ ρ (Tuple.cons (fun v => body.eval κ (Tuple.cons v ρ) jκ) jκ)
  termination_by structural _ _ _ _ _ _ b _ _ _ => b
/-- Dispatch a value of a union to its branch. -/
def Branches.eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → KEnv Δ Φ → UEnv Δ Γ →
    JEnv Δ τ js → Ctors.den (DSig.refDen Δ) cs → Ty.Den Δ τ
  | d, _, _, _, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) us₁ us₂ bc bd, κ, ρ, jκ, x =>
      Ctor.twoCase c₁ c₂ x (fun v => bc.eval κ (Tuple.append (UEnv.ofDL d _ us₁ v) ρ) jκ)
        (fun v => bd.eval κ (Tuple.append (UEnv.ofDL d _ us₂ v) ρ) jκ)
  | d, _, _, _, _, _, _, _, .cons (c := c) us b bs, κ, ρ, jκ, x =>
      Ctor.consCase c x (fun v => b.eval κ (Tuple.append (UEnv.ofDL d _ us v) ρ) jκ)
        (fun r => bs.eval κ ρ jκ r)
  termination_by structural _ _ _ _ _ _ _ _ b _ _ _ _ => b
end

end Eval

/-- The value of a whole program: a statement at depth `0` with no known value, no unknown
    and no join point. -/
abbrev Term.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    Ty.Den Δ τ :=
  t.eval PUnit.unit PUnit.unit PUnit.unit

/-- The value of a closed pure expression (no known value, no unknown). -/
abbrev PExpr.run {ks : List Nat} {Δ : DSig ks} {τ : Ty ks} {o : Lvl} (e : PExpr Δ [] [] τ o) :
    Ty.Den Δ τ :=
  e.eval PUnit.unit PUnit.unit

end LeanScript

end
