module

public import LeanScript.Term.Optimize.ShareTest
public import LeanScript.Term.Optimize.Hoist

@[expose] public section

set_option autoImplicit false

/-!
# Arms that differ only by a literal: one join point

`Branch.factorAt`: a case analysis of an enum whose arms all answer an expression written the
same way except for one literal (the `Repr` instance that `deriving Repr` writes for an enum:
`| .Foo => Repr.addAppParen (Format.group (Format.nest 2 "Test.Foo")) prec | .Bar => … "Test.Bar" …`)

```
case x of                              join j (s : String) := ret E[s]
| 0 => ret E["Test.Foo"]       ⟹      case x of
| 1 => ret E["Test.Bar"]               | 0 => jump j "Test.Foo"
…                                      | 1 => jump j "Test.Bar"
                                       …
```

so that the common expression `E` is written once.  The JavaScript printer writes such a join
point as a variable assigned by the arms (`let s; if (x === 0) s = "Test.Foo"; else …; return
E[s];`), with no closure.

* `PExpr.lits`: the literals of an expression, in order; the first position where the literals of
  two arms differ gives the literal `v₀` of the first arm and the literal of the other
  (`litFirstDiff`).  This search is only a heuristic: nothing about it is proved.
* `PExpr.abstrLit x v e`: every literal `v` of `e` replaced by the unknown `x`; when `x` holds
  `v`, the value is the same (`PExpr.abstrLit_eval`).
* The common expression `E` is the first arm with its literals `v₀` replaced by the parameter of
  the join point; an arm `ret eᵢ` is accepted with the literal `vᵢ` when `eᵢ` with its literals
  `vᵢ` replaced by the parameter is **written the same way** as `E` (`PExpr.same`), so
  `E[vᵢ]` has the value of `eᵢ` (`PExpr.factorLit?_eval`).
* The rewrite is done only when every arm is accepted, when the copies of `E` it saves are big
  enough (`12 ≤ (n - 1) * size E`, `PExpr.size`, for `n` arms: `case x of | 0 => ret "a" | 1 =>
  ret "b"` is kept), and when it keeps the level of the branch.

The value does not change (`Branch.factorAt_eval`, `Term.factorWalk_eval`), and no call is added
(`Term.numCalls_factorWalk`: the arms and the join point are pure answers and jumps).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Literals -/

/-- A literal of a leaf type. -/
abbrev SomeLit : Type := (p : LeanPrimTy) × p.denote

/-- Are two literals recognised as equal (`LeanPrimTy.litBEq`)? -/
def SomeLit.beq (a b : SomeLit) : Bool :=
  if h : a.1 = b.1 then b.1.litBEq (h ▸ a.2) b.2 else false

/-- The first pair of literals that differ, position by position. -/
def litFirstDiff : List SomeLit → List SomeLit → Option (SomeLit × SomeLit)
  | a :: as, b :: bs => if a.beq b then litFirstDiff as bs else some (a, b)
  | _, _ => none

section Lits
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
/-- The literals of a neutral expression, in order. -/
def Neu.lits : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → List SomeLit
  | _, _, .var _ => []
  | _, _, .data_out _ _ n => n.lits
  | _, _, .cond c a b => c.lits ++ a.lits ++ b.lits
  | _, _, .extern _ args _ => args.lits
/-- The literals of a pure expression, in order. -/
def PExpr.lits : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → List SomeLit
  | _, _, .neu n => n.lits
  | _, _, .kvar _ => []
  | _, _, .lit p v => [⟨p, v⟩]
  | _, _, .enum_mk _ _ => []
  | _, _, .record_mk args => args.lits
  | _, _, .union_mk _ args => args.lits
  | _, _, .array_mk es => es.lits
  | _, _, .list_mk es => es.lits
  | _, _, .data_in _ _ e => e.lits
/-- The literals of arguments, in order. -/
def Args.lits : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → List SomeLit
  | _, _, .nil => []
  | _, _, .cons a as => a.lits ++ as.lits
/-- The literals of elements, in order. -/
def Elems.lits : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → List SomeLit
  | _, _, .nil => []
  | _, _, .cons e es => e.lits ++ es.lits
end

mutual
/-- The number of nodes of a neutral expression. -/
def Neu.size : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Nat
  | _, _, .var _ => 1
  | _, _, .data_out _ _ n => n.size + 1
  | _, _, .cond c a b => c.size + a.size + b.size + 1
  | _, _, .extern _ args _ => args.size + 1
/-- The number of nodes of a pure expression. -/
def PExpr.size : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Nat
  | _, _, .neu n => n.size
  | _, _, .kvar _ => 1
  | _, _, .lit _ _ => 1
  | _, _, .enum_mk _ _ => 1
  | _, _, .record_mk args => args.size + 1
  | _, _, .union_mk _ args => args.size + 1
  | _, _, .array_mk es => es.size + 1
  | _, _, .list_mk es => es.size + 1
  | _, _, .data_in _ _ e => e.size
/-- The number of nodes of arguments. -/
def Args.size : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Nat
  | _, _, .nil => 0
  | _, _, .cons a as => a.size + as.size
/-- The number of nodes of elements. -/
def Elems.size : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Nat
  | _, _, .nil => 0
  | _, _, .cons e es => e.size + es.size
end

end Lits

/-! ## Replacing a literal by an unknown -/

section Abstr
variable {Φ : KCtx ks} {Γ : UCtx ks} {p : LeanPrimTy} {d : Nat}

/-- The unknown `x` in place of the literal `v'` (of `p'`) when it is the literal `v`. -/
def PExpr.abstrLitHere (x : UVar Γ (.prim p) d) (v : p.denote) (p' : LeanPrimTy)
    (v' : p'.denote) : (o : Lvl) × PExpr Δ Φ Γ (.prim p') o :=
  if h : p = p' then
    if p'.litBEq (h ▸ v) v' then ⟨_, .neu (.var (h ▸ x))⟩ else ⟨_, .lit p' v'⟩
  else ⟨_, .lit p' v'⟩

theorem PExpr.abstrLitHere_eval (x : UVar Γ (.prim p) d) (v : p.denote) (p' : LeanPrimTy)
    (v' : p'.denote) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (hx : ρ.get x = v) :
    (PExpr.abstrLitHere (Δ := Δ) (Φ := Φ) x v p' v').2.eval κ ρ = v' := by
  unfold PExpr.abstrLitHere
  by_cases h : p = p'
  · subst h
    rw [dite_eq_left rfl]
    by_cases hb : p.litBEq v v' = true
    · rw [ite_eq_left hb]
      have := LeanPrimTy.eq_of_litBEq _ _ _ hb
      subst this
      simp only [PExpr.eval, Neu.eval]
      exact hx
    · rw [ite_eq_right hb]; rfl
  · rw [dite_eq_right h]; rfl

mutual
/-- Every literal `v` of a neutral expression replaced by the unknown `x`. -/
def Neu.abstrLit (x : UVar Γ (.prim p) d) (v : p.denote) : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → (ℓ' : Nat) × Neu Δ Φ Γ τ ℓ'
  | _, _, .var y => ⟨_, .var y⟩
  | _, _, .data_out b j n => ⟨_, .data_out b j (n.abstrLit x v).2⟩
  | _, _, .cond c a b => ⟨_, .cond (c.abstrLit x v).2 (a.abstrLit x v).2 (b.abstrLit x v).2⟩
  | _, _, .extern e args h => Neu.mkExtern e args h (args.abstrLit x v)
/-- `Neu.abstrLit` in a pure expression. -/
def PExpr.abstrLit (x : UVar Γ (.prim p) d) (v : p.denote) : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | _, _, .neu n => ⟨_, .neu (n.abstrLit x v).2⟩
  | _, _, .kvar k => ⟨_, .kvar k⟩
  | _, _, .lit p' v' => PExpr.abstrLitHere x v p' v'
  | _, _, .enum_mk sc i => ⟨_, .enum_mk sc i⟩
  | _, _, .record_mk args => ⟨_, .record_mk (args.abstrLit x v).2⟩
  | _, _, .union_mk ix args => ⟨_, .union_mk ix (args.abstrLit x v).2⟩
  | _, _, .array_mk es => ⟨_, .array_mk (es.abstrLit x v).2⟩
  | _, _, .list_mk es => ⟨_, .list_mk (es.abstrLit x v).2⟩
  | _, _, .data_in b j e => ⟨_, .data_in b j (e.abstrLit x v).2⟩
/-- `Neu.abstrLit` in arguments. -/
def Args.abstrLit (x : UVar Γ (.prim p) d) (v : p.denote) : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → (o' : Lvl) × Args Δ Φ Γ σs o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons a as => ⟨_, .cons (a.abstrLit x v).2 (as.abstrLit x v).2⟩
/-- `Neu.abstrLit` in elements. -/
def Elems.abstrLit (x : UVar Γ (.prim p) d) (v : p.denote) : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → (o' : Lvl) × Elems Δ Φ Γ t o'
  | _, _, .nil => ⟨_, .nil⟩
  | _, _, .cons e es => ⟨_, .cons (e.abstrLit x v).2 (es.abstrLit x v).2⟩
end

mutual
theorem Neu.abstrLit_eval (x : UVar Γ (.prim p) d) (v : p.denote) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hx : ρ.get x = v) : {τ : Ty ks} → {ℓ : Nat} → (n : Neu Δ Φ Γ τ ℓ) →
    (n.abstrLit x v).2.eval κ ρ = n.eval κ ρ
  | _, _, .var _ => rfl
  | _, _, .data_out b j n => by
      simp only [Neu.abstrLit, Neu.eval, Neu.abstrLit_eval x v κ ρ hx n]
  | _, _, .cond c a b => by
      simp only [Neu.abstrLit, Neu.eval, Neu.abstrLit_eval x v κ ρ hx c,
        PExpr.abstrLit_eval x v κ ρ hx a, PExpr.abstrLit_eval x v κ ρ hx b]
  | _, _, .extern e args h =>
      Neu.mkExtern_eval e args h _ κ ρ (Args.abstrLit_eval x v κ ρ hx args)
theorem PExpr.abstrLit_eval (x : UVar Γ (.prim p) d) (v : p.denote) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hx : ρ.get x = v) : {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ τ o) →
    (e.abstrLit x v).2.eval κ ρ = e.eval κ ρ
  | _, _, .neu n => by simp only [PExpr.abstrLit, PExpr.eval, Neu.abstrLit_eval x v κ ρ hx n]
  | _, _, .kvar _ => rfl
  | _, _, .lit p' v' => PExpr.abstrLitHere_eval x v p' v' κ ρ hx
  | _, _, .enum_mk _ _ => rfl
  | _, _, .record_mk args => by
      simp only [PExpr.abstrLit, PExpr.eval, Args.abstrLit_eval x v κ ρ hx args] <;> rfl
  | _, _, .union_mk ix args => by
      simp only [PExpr.abstrLit, PExpr.eval, Args.abstrLit_eval x v κ ρ hx args] <;> rfl
  | _, _, .array_mk es => by
      simp only [PExpr.abstrLit, PExpr.eval, Elems.abstrLit_eval x v κ ρ hx es] <;> rfl
  | _, _, .list_mk es => by
      simp only [PExpr.abstrLit, PExpr.eval, Elems.abstrLit_eval x v κ ρ hx es] <;> rfl
  | _, _, .data_in b j e => by
      simp only [PExpr.abstrLit, PExpr.eval, PExpr.abstrLit_eval x v κ ρ hx e] <;> rfl
theorem Args.abstrLit_eval (x : UVar Γ (.prim p) d) (v : p.denote) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hx : ρ.get x = v) : {σs : List (Ty ks)} → {o : Lvl} →
    (as : Args Δ Φ Γ σs o) → (as.abstrLit x v).2.eval κ ρ = as.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons a as => by
      simp only [Args.abstrLit, Args.eval, PExpr.abstrLit_eval x v κ ρ hx a,
        Args.abstrLit_eval x v κ ρ hx as]
theorem Elems.abstrLit_eval (x : UVar Γ (.prim p) d) (v : p.denote) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (hx : ρ.get x = v) : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ Φ Γ t o) → (es.abstrLit x v).2.eval κ ρ = es.eval κ ρ
  | _, _, .nil => rfl
  | _, _, .cons e es => by
      simp only [Elems.abstrLit, Elems.eval, PExpr.abstrLit_eval x v κ ρ hx e,
        Elems.abstrLit_eval x v κ ρ hx es]
end

end Abstr


/-! ## One arm -/

section Arm
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- The answer of a statement that is only an answer. -/
def Term.retView? : {o : Lvl} → Term Δ d Φ Γ τ js o → Option (PExpr Δ Φ Γ τ o)
  | _, .ret e => some e
  | _, _ => none

theorem Term.retView?_eval {o : Lvl} (t : Term Δ d Φ Γ τ js o) (e : PExpr Δ Φ Γ τ o)
    (h : t.retView? = some e) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.eval κ ρ jκ = e.eval κ ρ := by
  cases t <;> simp only [Term.retView?, reduceCtorEq, Option.some.injEq] at h
  subst h; rfl

/-- The parameter of the join point: a literal of `p`, at the depth of the branch. -/
abbrev factorBinder (p : LeanPrimTy) (d : Nat) : UBinder ks := ⟨.prim p, .many, d⟩

/-- The parameter of the join point, as an unknown. -/
def factorVar (p : LeanPrimTy) (d : Nat) : UVar (factorBinder (ks := ks) p d :: Γ) (.prim p) d :=
  .head (by decide)

/-- The literal of an arm `e` at the position where the first arm `e₀` has the literal `v₀`
    (`v₀` itself when the literals of the two arms are the same). -/
def armLit? {o₀ o : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀) (e : PExpr Δ Φ Γ τ o) (p : LeanPrimTy)
    (v₀ : p.denote) : Option p.denote :=
  match litFirstDiff e₀.lits e.lits with
  | none => some v₀
  | some (a, b) =>
    if a.beq ⟨p, v₀⟩ then (if h : b.1 = p then some (h ▸ b.2) else none) else none

/-- **An arm accepted**, with its literal `v`: `e` with its literals `v` replaced by the parameter
    is written the same way as the common expression `E`. -/
def PExpr.factorLit? {o₀ o oE : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀) (p : LeanPrimTy) (v₀ : p.denote)
    (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE) (e : PExpr Δ Φ Γ τ o) : Option p.denote :=
  match armLit? e₀ e p v₀ with
  | none => none
  | some v =>
    match e.rename KRen.id (URen.wk1 (b := factorBinder p d)) with
    | some e' => if ((e'.abstrLit (factorVar p d) v).2.same E) then some v else none
    | none => none

theorem PExpr.factorLit?_eval {o₀ o oE : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀) (p : LeanPrimTy)
    (v₀ : p.denote) (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE) (e : PExpr Δ Φ Γ τ o)
    (v : p.denote) (h : PExpr.factorLit? e₀ p v₀ E e = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    E.eval κ (Tuple.cons v ρ) = e.eval κ ρ := by
  unfold PExpr.factorLit? at h
  split at h
  · cases h
  · rename_i v' _
    split at h
    · rename_i e' he'
      by_cases hs : ((e'.abstrLit (factorVar p d) v').2.same E) = true
      · rw [ite_eq_left hs] at h
        have h' : v = v' := (Option.some.inj h).symm
        subst h'
        have h1 := eq_of_heq ((PExpr.same_eval _ E hs).2 κ (Tuple.cons v ρ))
        rw [← h1, PExpr.abstrLit_eval _ _ κ _ (UEnv.get_cons_head _ _ _)]
        exact PExpr.rename_eval (KRen.Agree.id κ) (URen.Agree.wk1 ρ _) e he'
      · rw [ite_eq_right hs] at h; cases h
    · cases h

end Arm

/-! ## The rewrite -/

theorem Fin.allB_eq_true : (n : Nat) → (f : Fin n → Bool) → Fin.allB n f = true → ∀ i, f i = true
  | 0, _, _, i => i.elim0
  | n + 1, f, h, i => by
      simp only [Fin.allB, Bool.and_eq_true] at h
      cases i using Fin.cases with
      | zero => exact h.1
      | succ j => exact Fin.allB_eq_true n _ h.2 j

theorem Fin.sumNat_zero : (n : Nat) → Fin.sumNat n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by simp only [Fin.sumNat, Fin.sumNat_zero n]

section Factor
variable {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}

/-- `join j (x : p) := ret E; case e of | i => jump j (vᵢ)`. -/
def Branch.factorBuild {s : LeanEnumSchema} {ℓ : Nat} {oE : Lvl} (e : Neu Δ Φ Γ (.enum s) ℓ)
    (p : LeanPrimTy) (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE)
    (val : Fin s.nOfConstructors → p.denote) :
    Branch Δ d Φ Γ τ js
      (Lvl.meetL (Lvl.meetL ℓ (Lvl.meetFin s.nOfConstructors (fun _ => none))) oE) :=
  .join (.prim p) .many .many (.ret E) (.enum_casesOn e (fun i => .jump .head (.lit p (val i))))

theorem Branch.factorBuild_eval {s : LeanEnumSchema} {ℓ : Nat} {oE : Lvl}
    (e : Neu Δ Φ Γ (.enum s) ℓ) (p : LeanPrimTy) (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE)
    (val : Fin s.nOfConstructors → p.denote) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    (Branch.factorBuild (js := js) e p E val).eval κ ρ jκ =
      E.eval κ (Tuple.cons (val (e.eval κ ρ)) ρ) := by
  simp [Branch.factorBuild, Branch.eval, Term.eval, PExpr.eval]

/-- The literal of the first arm at the first position where it differs from another arm. -/
def factorFirstLit? {n : Nat} {os : Fin n → Lvl} {o₀ : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀)
    (bs : (i : Fin n) → Term Δ d Φ Γ τ js (os i)) : Option SomeLit :=
  (List.finRange n).findSome? fun i =>
    match (bs i).retView? with
    | some e => (litFirstDiff e₀.lits e.lits).map (·.1)
    | none => none

/-- The literal of each arm, when it is accepted (`PExpr.factorLit?`). -/
def factorVal? {n : Nat} {os : Fin n → Lvl} {o₀ oE : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀)
    (p : LeanPrimTy) (v₀ : p.denote) (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE)
    (bs : (i : Fin n) → Term Δ d Φ Γ τ js (os i)) (i : Fin n) : Option p.denote :=
  match (bs i).retView? with
  | some e => PExpr.factorLit? e₀ p v₀ E e
  | none => none

theorem factorVal?_eval {n : Nat} {os : Fin n → Lvl} {o₀ oE : Lvl} (e₀ : PExpr Δ Φ Γ τ o₀)
    (p : LeanPrimTy) (v₀ : p.denote) (E : PExpr Δ Φ (factorBinder p d :: Γ) τ oE)
    (bs : (i : Fin n) → Term Δ d Φ Γ τ js (os i)) (i : Fin n) (v : p.denote)
    (h : factorVal? e₀ p v₀ E bs i = some v) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    E.eval κ (Tuple.cons v ρ) = (bs i).eval κ ρ jκ := by
  unfold factorVal? at h
  split at h
  · rename_i e he
    rw [Term.retView?_eval _ e he κ ρ jκ]
    exact PExpr.factorLit?_eval e₀ p v₀ E e v h κ ρ
  · cases h

/-- **The arms of a case analysis of an enum that differ only by a literal**, written once in a
    join point (with the level it comes out with). -/
def Branch.factorEnum {s : LeanEnumSchema} {ℓ : Nat} {os : Fin s.nOfConstructors → Lvl}
    (e : Neu Δ Φ Γ (.enum s) ℓ) (bs : (i : Fin s.nOfConstructors) → Term Δ d Φ Γ τ js (os i)) :
    Option ((ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ') :=
  if h0 : 0 < s.nOfConstructors then
    match (bs ⟨0, h0⟩).retView? with
    | none => none
    | some e₀ =>
      match factorFirstLit? e₀ bs with
      | none => none
      | some ⟨p, v₀⟩ =>
        match e₀.rename KRen.id (URen.wk1 (b := factorBinder p d)) with
        | none => none
        | some e₀' =>
          let E := e₀'.abstrLit (factorVar p d) v₀
          let val := factorVal? e₀ p v₀ E.2 bs
          if Fin.allB _ (fun i => (val i).isSome) &&
              decide (12 ≤ (s.nOfConstructors - 1) * E.2.size) then
            some ⟨_, Branch.factorBuild e p E.2 (fun i => (val i).getD v₀)⟩
          else none
  else none

theorem Branch.factorEnum_eval {s : LeanEnumSchema} {ℓ : Nat} {os : Fin s.nOfConstructors → Lvl}
    (e : Neu Δ Φ Γ (.enum s) ℓ) (bs : (i : Fin s.nOfConstructors) → Term Δ d Φ Γ τ js (os i))
    (r : (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ') (h : Branch.factorEnum e bs = some r)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    r.2.eval κ ρ jκ = (Branch.enum_casesOn e bs).eval κ ρ jκ := by
  unfold Branch.factorEnum at h
  split at h
  · split at h
    · cases h
    · rename_i e₀ _
      split at h
      · cases h
      · rename_i p v₀ _
        split at h
        · cases h
        · rename_i e₀' _
          simp only at h
          split at h
          · rename_i hall
            cases h
            rw [Branch.factorBuild_eval]
            simp only [Branch.eval]
            simp only [Bool.and_eq_true] at hall
            have hs := Fin.allB_eq_true _ _ hall.1 (e.eval κ ρ)
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
            rw [hv, Option.getD_some]
            exact factorVal?_eval _ _ _ _ bs _ v hv κ ρ jκ
          · cases h
  · cases h

/-- `Branch.factorEnum` at a case analysis of an enum, when it keeps the level. -/
def Branch.factorAt {ℓ : Nat} : Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | .enum_casesOn e bs =>
    match Branch.factorEnum e bs with
    | some r => if h : r.1 = _ then r.2.castLvl h else .enum_casesOn e bs
    | none => .enum_casesOn e bs
  | br => br

theorem Branch.factorAt_eval {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) : br.factorAt.eval κ ρ jκ = br.eval κ ρ jκ := by
  cases br with
  | enum_casesOn e bs =>
    simp only [Branch.factorAt]
    split
    · rename_i r hr
      split
      · rw [Branch.eval_castLvl]; exact Branch.factorEnum_eval e bs r hr κ ρ jκ
      · rfl
    · rfl
  | _ => rfl

theorem Branch.numCalls_factorAt {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) :
    br.factorAt.numCalls ≤ br.numCalls := by
  cases br with
  | enum_casesOn e bs =>
    simp only [Branch.factorAt]
    split
    · rename_i r hr
      split
      · rw [Branch.numCalls_castLvl]
        unfold Branch.factorEnum at hr
        split at hr
        · split at hr
          · cases hr
          · split at hr
            · cases hr
            · split at hr
              · cases hr
              · simp only at hr
                split at hr
                · cases hr
                  simp only [Branch.factorBuild, Branch.numCalls, Term.numCalls,
                    Fin.sumNat_zero]
                  exact Nat.zero_le _
                · cases hr
        · cases hr
      · exact Nat.le_refl _
    · exact Nat.le_refl _
  | _ => exact Nat.le_refl _

end Factor

/-! ## The walk -/

mutual
/-- `Term.factorWalk` inside the bodies of a value. -/
def Val.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.factorWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.factorWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.factorWalk
  | _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.factorWalk` in a body. -/
def Body.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.factorWalk
  | _, _, _, _, _, _, .opened t h => .opened t.factorWalk h
/-- `Term.factorWalk` inside the bodies of a computation. -/
def Comp.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n z s.factorWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a z s.factorWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).factorWalk) j e h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).factorWalk) j e h
  | _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **The walk**: bottom-up, `Branch.factorAt` at every case analysis of an enum. -/
def Term.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e
  | _, _, _, _, _, _, .letV u v b => .letV u v.factorWalk b.factorWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.factorWalk b.factorWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n b.factorWalk
  | _, _, _, _, _, _, .branch br => .branch br.factorWalk
  | _, _, _, _, _, _, .jump j e => .jump j e
/-- `Term.factorWalk` in a branch. -/
def Branch.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c t.factorWalk e.factorWalk
  | _, _, _, _, _, _, .enum_casesOn e bs =>
      Branch.factorAt (.enum_casesOn e (fun i => (bs i).factorWalk))
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e bs.factorWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.factorWalk main.factorWalk
/-- `Term.factorWalk` in the branches of a union's case analysis. -/
def Branches.factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.factorWalk b₂.factorWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.factorWalk bs.factorWalk
end

mutual
theorem Val.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.factorWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.factorWalk, Val.eval]; funext x; rw [Body.factorWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.factorWalk, Val.eval]; rw [Body.factorWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.factorWalk, Val.eval]; rw [Body.factorWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.factorWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.factorWalk, Body.eval]; exact Term.factorWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.factorWalk, Body.eval]; exact Term.factorWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.factorWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.factorWalk, Comp.eval]
      congr 1; funext k acc; exact Body.factorWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.factorWalk, Comp.eval]
      congr 1; funext acc x; exact Body.factorWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.factorWalk, Comp.eval]
      congr 1; funext i x; exact Body.factorWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.factorWalk, Comp.eval]
      congr 1; funext i x; exact Body.factorWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.factorWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret _, κ, ρ, jκ => by
      rfl
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.factorWalk, Term.eval, Val.factorWalk_eval v, Term.factorWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.factorWalk, Term.eval, Comp.factorWalk_eval c, Term.factorWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.factorWalk, Term.eval, Term.factorWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.factorWalk, Term.eval, Branch.factorWalk_eval br]
  | _, _, _, _, _, _, .jump _ _, κ, ρ, jκ => by
      rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.factorWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.factorWalk, Branch.eval, Term.factorWalk_eval t, Term.factorWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.factorWalk, Branch.factorAt_eval, Branch.eval]
      exact Term.factorWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.factorWalk, Branch.eval]; exact Branches.factorWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.factorWalk, Branch.eval, Branch.factorWalk_eval main,
        Term.factorWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.factorWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.factorWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.factorWalk, Branches.eval, Term.factorWalk_eval b₁,
        Term.factorWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.factorWalk, Branches.eval, Term.factorWalk_eval b,
        Branches.factorWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.factorWalk.numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b => by
      simp only [Val.factorWalk, Val.numCalls]; exact Body.numCalls_factorWalk b
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.factorWalk, Val.numCalls]; exact Body.numCalls_factorWalk b
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.factorWalk, Val.numCalls]; exact Body.numCalls_factorWalk b
  | _, _, _, _, _, .record_mk _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.factorWalk.numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.factorWalk, Body.numCalls]; exact Term.numCalls_factorWalk t
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.factorWalk, Body.numCalls]; exact Term.numCalls_factorWalk t
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.factorWalk.numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _ => Nat.le_refl _
  | _, _, _, _, _, .share _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _ => by
      simp only [Comp.factorWalk, Comp.numCalls]; exact Body.numCalls_factorWalk s
  | _, _, _, _, _, .array_foldl a z s _ => by
      simp only [Comp.factorWalk, Comp.numCalls]; exact Body.numCalls_factorWalk s
  | _, _, _, _, _, .data_rec b ρt us brs j e _ => by
      simp only [Comp.factorWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_factorWalk (brs i))
  | _, _, _, _, _, .data_brec b ρt k us brs j e _ => by
      simp only [Comp.factorWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_factorWalk (brs i))
  | _, _, _, _, _, .thunk_force _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x => x
/-- **The walk does not add calls.** -/
theorem Term.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.factorWalk.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret e => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b => by
      have hv := Val.numCalls_factorWalk v
      have hb := Term.numCalls_factorWalk b
      simp only [Term.factorWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b => by
      have hc := Comp.numCalls_factorWalk c
      have hb := Term.numCalls_factorWalk b
      simp only [Term.factorWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b => by
      have hb := Term.numCalls_factorWalk b
      simp only [Term.factorWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .branch br => by
      have hb := Branch.numCalls_factorWalk br
      simp only [Term.factorWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .jump j e => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    br.factorWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      have ht := Term.numCalls_factorWalk t
      have he := Term.numCalls_factorWalk e
      simp only [Branch.factorWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs => by
      have := Branch.numCalls_factorAt (Branch.enum_casesOn e (fun i => (bs i).factorWalk))
      have h2 := Fin.sumNat_le _ (fun i => Term.numCalls_factorWalk (bs i))
      simp only [Branch.factorWalk, Branch.numCalls] at this ⊢; omega
  | _, _, _, _, _, _, .union_casesOn e bs => by
      simp only [Branch.factorWalk, Branch.numCalls]; exact Branches.numCalls_factorWalk bs
  | _, _, _, _, _, _, .join σ u uₓ body main => by
      have hb := Term.numCalls_factorWalk body
      have hm := Branch.numCalls_factorWalk main
      simp only [Branch.factorWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_factorWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.factorWalk.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => by
      have h₁ := Term.numCalls_factorWalk b₁
      have h₂ := Term.numCalls_factorWalk b₂
      simp only [Branches.factorWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs => by
      have h₁ := Term.numCalls_factorWalk b
      have h₂ := Branches.numCalls_factorWalk bs
      simp only [Branches.factorWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
