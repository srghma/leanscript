module

public import LeanScript.Term.Eval
public import LeanScript.Term.Closed

@[expose] public section

set_option autoImplicit false

/-!
# A closed statement evaluates to a completely normalised value

`Term.eval` answers a Lean value of `Ty.Den Δ τ`.  This file says which Lean values it can
answer when **every variable is known**: no unknown in scope (`Γ = []`), no open known value
(`KCtx.Closed Φ`), no join point (`js = []`), and the known values themselves completely
normalised.

**Completely normalised values** (`NVal Δ τ`) are trees of constructors, all the way down:

* a literal (`lit`), a constructor of an enum (`enum_mk`), a record (`record_mk`), a
  constructor of a union (`union_mk`), an array or a list literal (`array_mk`, `list_mk`),
  one layer of a declared datatype (`data_in`), each of whose parts is again completely
  normalised (`NArgs`, `NElems`);
* a delay (`thunk_mk`, `lazy_mk`) holding the completely normalised value it denotes (the
  delay has been forced: a delay denotes the value it holds);
* a closure (`lam`): a closed body — a normal-form `Term` over the closed known values and
  the parameter — together with the completely normalised values of those known values
  (`NEnv`).

`NVal.den` reads such a value as a Lean value, the way `Term.eval` does.

**The theorem** (`Term.eval_normal`): for such a statement `t` and completely normalised known
values `nκ`, there is a completely normalised value `n` with
`n.den = t.eval nκ.den PUnit.unit PUnit.unit`.  In particular the result of every whole program
is one (`Term.run_normal`).

At a first-order type (no function inside) every Lean value is the reading of some `NVal`, so the
content of the theorem is at the higher types: every function that `Term.eval` answers, even
deep inside a record, a union, an array or a datatype, is the reading of a syntactic closure
over completely normalised values.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

mutual
/-- **A completely normalised value** of type `τ`: a tree of constructors whose leaves are
    literals and closures over completely normalised values. -/
inductive NVal {ks : List Nat} (Δ : DSig ks) : Ty ks → Type where
  /-- A literal of a leaf type. -/
  | lit (p : LeanPrimTy) (v : p.denote) : NVal Δ (.prim p)
  /-- A constructor of an enum. -/
  | enum_mk (s : LeanEnumSchema) (i : Fin s.nOfConstructors) : NVal Δ (.enum s)
  /-- A record, from its completely normalised fields. -/
  | record_mk {t : Ty ks} {fs : Fields ks} : NArgs Δ (t :: fs.toList) → NVal Δ (.record t fs)
  /-- A constructor of a union, from its completely normalised fields. -/
  | union_mk {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {h : UnionShape bs}
      {c : Ctor ks b} : CtorIx cs c → NArgs Δ c.binds → NVal Δ (.union cs (h := h))
  /-- An array of completely normalised elements. -/
  | array_mk {t : Ty ks} : NElems Δ t → NVal Δ (.array t)
  /-- A list of completely normalised elements. -/
  | list_mk {t : Ty ks} : NElems Δ t → NVal Δ (.list t)
  /-- One layer of a declared datatype, around a completely normalised value. -/
  | data_in (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      NVal Δ ((Δ.block b).unfold j) → NVal Δ (.data ((Δ.block b).ref j))
  /-- A closure: a closed body (it sees only the closed known values and its parameter),
      with the completely normalised values of the known values. -/
  | lam {d : Nat} {Φ : KCtx ks} {σ τ : Ty ks} {u : Usage01ω} {o : Lvl} :
      NEnv Δ (KCtx.closedOnly Φ) →
      Term Δ (d + 1) (KCtx.closedOnly Φ) [⟨σ, u, d + 1⟩] τ [] o → NVal Δ (.fn σ τ)
  /-- A memoised delay, holding the completely normalised value it denotes. -/
  | thunk_mk {τ : Ty ks false} : NVal Δ τ.relax → NVal Δ (.thunk τ)
  /-- A lazy delay, holding the completely normalised value it denotes. -/
  | lazy_mk {τ : Ty ks false} : NVal Δ τ.relax → NVal Δ (.lazy τ)
/-- Completely normalised values of a list of types. -/
inductive NArgs {ks : List Nat} (Δ : DSig ks) : List (Ty ks) → Type where
  | nil : NArgs Δ []
  | cons {σ : Ty ks} {σs : List (Ty ks)} : NVal Δ σ → NArgs Δ σs → NArgs Δ (σ :: σs)
/-- Completely normalised elements of an array or a list. -/
inductive NElems {ks : List Nat} (Δ : DSig ks) : Ty ks → Type where
  | nil {t : Ty ks} : NElems Δ t
  | cons {t : Ty ks} : NVal Δ t → NElems Δ t → NElems Δ t
/-- Completely normalised values of the known values of a context. -/
inductive NEnv {ks : List Nat} (Δ : DSig ks) : KCtx ks → Type where
  | nil : NEnv Δ []
  | cons {b : KBinder ks} {Φ : KCtx ks} : NVal Δ b.ty → NEnv Δ Φ → NEnv Δ (b :: Φ)
end

mutual
/-- The Lean value a completely normalised value stands for. -/
def NVal.den : {τ : Ty ks} → NVal Δ τ → Ty.Den Δ τ
  | _, .lit _ v => v
  | _, .enum_mk _ i => i
  | _, .record_mk (fs := fs) args =>
      let v := args.den
      (v.head, Fields.ofDL fs v.tail)
  | _, .union_mk ix args => ix.inject args.den
  | _, .array_mk es => es.den.toArray
  | _, .list_mk es => es.den
  | _, .data_in b j n => Δ.dataIn b j n.den
  | _, .lam κ t => fun v => t.eval κ.den (Tuple.cons v Tuple.nil) PUnit.unit
  | _, .thunk_mk (τ := τ) n => Ty.ofRelax _ τ n.den
  | _, .lazy_mk (τ := τ) n => Ty.ofRelax _ τ n.den
/-- The Lean values of completely normalised values of a list of types. -/
def NArgs.den : {σs : List (Ty ks)} → NArgs Δ σs → DenList (DSig.refDen Δ) σs
  | _, .nil => PUnit.unit
  | _, .cons n ns => Tuple.cons n.den ns.den
/-- The Lean values of completely normalised elements. -/
def NElems.den : {t : Ty ks} → NElems Δ t → List (Ty.Den Δ t)
  | _, .nil => []
  | _, .cons n ns => n.den :: ns.den
/-- The environment of Lean values of completely normalised known values. -/
def NEnv.den : {Φ : KCtx ks} → NEnv Δ Φ → KEnv Δ Φ
  | _, .nil => PUnit.unit
  | _, .cons n ns => Tuple.cons n.den ns.den
end

/-- The completely normalised value of a known variable. -/
def NEnv.get : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} → NEnv Δ Φ → KVar Φ τ o → NVal Δ τ
  | _, _, _, .cons n _, .head => n
  | _, _, _, .cons _ ns, .tail x => NEnv.get ns x

/-- The completely normalised known values, as seen from a closed body. -/
def NEnv.closedOnly : {Φ : KCtx ks} → NEnv Δ Φ → NEnv Δ (KCtx.closedOnly Φ)
  | [], _ => .nil
  | ⟨_, _, some _, _⟩ :: _, .cons n ns => .cons n (NEnv.closedOnly ns)
  | ⟨_, _, none, _⟩ :: _, .cons n ns => .cons n (NEnv.closedOnly ns)

theorem NEnv.den_get : {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} → (nκ : NEnv Δ Φ) →
    (x : KVar Φ τ o) → (nκ.get x).den = nκ.den.get x
  | _, _, _, .cons n ns, .head => by simp [NEnv.get, NEnv.den, KEnv.get]
  | _, _, _, .cons n ns, .tail x => by
      simp only [NEnv.get, NEnv.den, KEnv.get, Tuple.tail_cons]; exact NEnv.den_get ns x

theorem NEnv.den_closedOnly : {Φ : KCtx ks} → (nκ : NEnv Δ Φ) →
    nκ.closedOnly.den = nκ.den.closedOnly
  | [], .nil => rfl
  | ⟨t, u, some m, _⟩ :: _, .cons n ns => by
      have e : (NEnv.cons n ns).closedOnly =
          NEnv.cons (b := ⟨t, u, some m, false⟩) n ns.closedOnly := rfl
      rw [e]
      simp only [NEnv.den, KEnv.closedOnly, Tuple.head_cons, Tuple.tail_cons,
        NEnv.den_closedOnly ns]
      rfl
  | ⟨t, u, none, v⟩ :: _, .cons n ns => by
      have e : (NEnv.cons n ns).closedOnly =
          NEnv.cons (b := ⟨t, u, none, v⟩) n ns.closedOnly := rfl
      rw [e]
      simp only [NEnv.den, KEnv.closedOnly, Tuple.head_cons, Tuple.tail_cons,
        NEnv.den_closedOnly ns]
      rfl

section Normal
variable {Φ : KCtx ks}

mutual
/-- A closed pure expression over completely normalised known values is completely
    normalised. -/
theorem PExpr.eval_normal (hΦ : KCtx.Closed Φ) (nκ : NEnv Δ Φ) :
    {τ : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ [] τ o) →
      ∃ n : NVal Δ τ, n.den = e.eval nκ.den PUnit.unit
  | _, _, .neu n => (Neu.not_closed hΦ n).elim
  | _, _, .kvar k => ⟨nκ.get k, by rw [NEnv.den_get]; rfl⟩
  | _, _, .lit p v => ⟨.lit p v, rfl⟩
  | _, _, .enum_mk s i => ⟨.enum_mk s i, rfl⟩
  | _, _, .record_mk args => by
      obtain ⟨na, h⟩ := Args.eval_normal hΦ nκ args
      exact ⟨.record_mk na, by simp only [NVal.den, PExpr.eval, h] <;> rfl⟩
  | _, _, .union_mk ix args => by
      obtain ⟨na, h⟩ := Args.eval_normal hΦ nκ args
      exact ⟨.union_mk ix na, by simp only [NVal.den, PExpr.eval, h] <;> rfl⟩
  | _, _, .array_mk es => by
      obtain ⟨ne, h⟩ := Elems.eval_normal hΦ nκ es
      exact ⟨.array_mk ne, by simp only [NVal.den, PExpr.eval, h] <;> rfl⟩
  | _, _, .list_mk es => by
      obtain ⟨ne, h⟩ := Elems.eval_normal hΦ nκ es
      exact ⟨.list_mk ne, by simp only [NVal.den, PExpr.eval, h] <;> rfl⟩
  | _, _, .data_in b j e => by
      obtain ⟨n, h⟩ := PExpr.eval_normal hΦ nκ e
      exact ⟨.data_in b j n, by simp only [NVal.den, PExpr.eval, h] <;> rfl⟩
/-- Closed arguments are completely normalised. -/
theorem Args.eval_normal (hΦ : KCtx.Closed Φ) (nκ : NEnv Δ Φ) :
    {σs : List (Ty ks)} → {o : Lvl} → (args : Args Δ Φ [] σs o) →
      ∃ n : NArgs Δ σs, n.den = args.eval nκ.den PUnit.unit
  | _, _, .nil => ⟨.nil, rfl⟩
  | _, _, .cons a as => by
      obtain ⟨n, h⟩ := PExpr.eval_normal hΦ nκ a
      obtain ⟨ns, hs⟩ := Args.eval_normal hΦ nκ as
      exact ⟨.cons n ns, by simp only [NArgs.den, Args.eval, h, hs] <;> rfl⟩
/-- Closed elements are completely normalised. -/
theorem Elems.eval_normal (hΦ : KCtx.Closed Φ) (nκ : NEnv Δ Φ) :
    {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ [] t o) →
      ∃ n : NElems Δ t, n.den = es.eval nκ.den PUnit.unit
  | _, _, .nil => ⟨.nil, rfl⟩
  | _, _, .cons e es => by
      obtain ⟨n, h⟩ := PExpr.eval_normal hΦ nκ e
      obtain ⟨ns, hs⟩ := Elems.eval_normal hΦ nκ es
      exact ⟨.cons n ns, by simp only [NElems.den, Elems.eval, h, hs] <;> rfl⟩
end

end Normal

mutual
/-- A value with no unknown, over completely normalised closed known values, is completely
    normalised. -/
theorem Val.eval_normal : {d : Nat} → {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KCtx.Closed Φ → (nκ : NEnv Δ Φ) → (v : Val Δ d Φ [] τ o) →
      ∃ n : NVal Δ τ, n.den = v.eval nκ.den PUnit.unit
  | _, _, _, _, _, nκ, .lam (.closed t) =>
      ⟨.lam nκ.closedOnly t, by
        simp only [NVal.den, Val.eval, Body.eval, NEnv.den_closedOnly] <;> rfl⟩
  | _, _, _, _, hΦ, _, .lam (.opened t hm) =>
      nomatch Val.closed hΦ (.lam (.opened t hm))
  | _, _, _, _, hΦ, nκ, .thunk_mk b => by
      obtain ⟨n, h⟩ := Body.eval_normal hΦ nκ b
      exact ⟨.thunk_mk n, by simp only [NVal.den, Val.eval, h]; rfl⟩
  | _, _, _, _, hΦ, nκ, .lazy_mk b => by
      obtain ⟨n, h⟩ := Body.eval_normal hΦ nκ b
      exact ⟨.lazy_mk n, by simp only [NVal.den, Val.eval, h]; rfl⟩
  | _, _, _, _, hΦ, nκ, .record_mk args => by
      obtain ⟨na, h⟩ := Args.eval_normal hΦ nκ args
      exact ⟨.record_mk na, by simp only [NVal.den, Val.eval, h] <;> rfl⟩
  | _, _, _, _, hΦ, nκ, .union_mk ix args => by
      obtain ⟨na, h⟩ := Args.eval_normal hΦ nκ args
      exact ⟨.union_mk ix na, by simp only [NVal.den, Val.eval, h] <;> rfl⟩
  | _, _, _, _, hΦ, nκ, .array_mk es => by
      obtain ⟨ne, h⟩ := Elems.eval_normal hΦ nκ es
      exact ⟨.array_mk ne, by simp only [NVal.den, Val.eval, h] <;> rfl⟩
  | _, _, _, _, hΦ, nκ, .list_mk es => by
      obtain ⟨ne, h⟩ := Elems.eval_normal hΦ nκ es
      exact ⟨.list_mk ne, by simp only [NVal.den, Val.eval, h] <;> rfl⟩
  | _, _, _, _, hΦ, nκ, .data_in b j e => by
      obtain ⟨n, h⟩ := PExpr.eval_normal hΦ nκ e
      exact ⟨.data_in b j n, by simp only [NVal.den, Val.eval, h] <;> rfl⟩
  termination_by _ _ _ _ _ _ v => sizeOf v
  decreasing_by all_goals simp_wf; omega

/-- The body of a delay with no unknown, over completely normalised closed known values,
    evaluates to a completely normalised value. -/
theorem Body.eval_normal : {d : Nat} → {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KCtx.Closed Φ → (nκ : NEnv Δ Φ) → (b : Body Δ d Φ [] [] τ o) →
      ∃ n : NVal Δ τ, n.den = b.eval nκ.den PUnit.unit PUnit.unit
  | _, _, _, _, _, nκ, .closed t => by
      obtain ⟨n, h⟩ := Term.eval_normal (KCtx.Closed.closedOnly _) nκ.closedOnly t
      exact ⟨n, by simp only [Body.eval, h, NEnv.den_closedOnly]⟩
  | _, _, _, _, hΦ, _, .opened t hm => nomatch Body.closed_eq hΦ (UCtx.Ge.nil _) (.opened t hm)
  termination_by _ _ _ _ _ _ b => sizeOf b
  decreasing_by all_goals simp_wf; omega

/-- **A statement in which every variable is known evaluates to a completely normalised
    value**: no unknown, no open known value, no join point, and completely normalised known
    values. -/
theorem Term.eval_normal : {d : Nat} → {Φ : KCtx ks} → {τ : Ty ks} → {o : Lvl} →
    KCtx.Closed Φ → (nκ : NEnv Δ Φ) → (t : Term Δ d Φ [] τ [] o) →
      ∃ n : NVal Δ τ, n.den = t.eval nκ.den PUnit.unit PUnit.unit
  | _, _, _, _, hΦ, nκ, .ret e => by
      obtain ⟨n, h⟩ := PExpr.eval_normal hΦ nκ e
      exact ⟨n, by simp only [Term.eval, h] <;> rfl⟩
  | _, _, _, _, hΦ, nκ, .letV (o := o) u v b => by
      have ho : o = none := Val.closed hΦ v
      obtain ⟨nv, hv⟩ := Val.eval_normal hΦ nκ v
      obtain ⟨n, h⟩ := Term.eval_normal (ho ▸ KCtx.Closed.cons hΦ) (.cons nv nκ) b
      exact ⟨n, by simp only [Term.eval, h, NEnv.den, hv] <;> rfl⟩
  | _, _, _, _, hΦ, _, .letE _ c _ => (Comp.not_closed hΦ c).elim
  | _, _, _, _, hΦ, _, .record_casesOn _ n _ => (Neu.not_closed hΦ n).elim
  | _, _, _, _, hΦ, _, .branch br => (Branch.not_closed hΦ br).elim
  | _, _, _, _, _, _, .jump j _ => nomatch j
  termination_by _ _ _ _ _ _ t => sizeOf t
  decreasing_by all_goals simp_wf; omega
end

/-- **The result of every whole program is a completely normalised value.** -/
theorem Term.run_normal {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    ∃ n : NVal Δ τ, n.den = t.run :=
  t.eval_normal KCtx.Closed.nil .nil

end LeanScript

end
