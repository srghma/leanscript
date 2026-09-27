module

public import LeanScript.Term.Term

@[expose] public section

set_option autoImplicit false

/-!
# Occurrence analysis: how often a variable is used

`Term.countU i t`, `Term.countK i t` and `Term.countJ i t` are the `Usage01ω` (`0 | 1 | ω`) of
the unknown, the known value and the join point at de Bruijn position `i` in `t`:

* every occurrence counts `1`, and the occurrences in the parts of a straight-line piece of
  code add up (`1 + 1 = ω`);
* across the arms of a branch (`ite`, `enum_casesOn`, `union_casesOn`) the counts take the
  **maximum** (`Usage01ω.max`): only one arm runs, so a variable used once in each arm is used
  once (`1`), and it can be inlined into each arm without duplicating work.  The body and the
  main part of a join point both run on the same path, so their counts add up;
* an occurrence inside the body of a closure, a delay or a loop counts `ω` (`Usage01ω.scale`),
  because that body may run many times;
* a closed body does not see the unknowns at all, so they never occur in it.

These are the counts that `Term.dce` (`LeanScript.Term.Dce`) writes into the binders.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- The sum of finitely many usages (parts that all run). -/
def Fin.sumU : (n : Nat) → (Fin n → Usage01ω) → Usage01ω
  | 0, _ => .zero
  | n + 1, f => f 0 + Fin.sumU n (fun i => f i.succ)

/-- The maximum of finitely many usages (arms of a branch, only one of which runs). -/
def Fin.maxU : (n : Nat) → (Fin n → Usage01ω) → Usage01ω
  | 0, _ => .zero
  | n + 1, f => Usage01ω.max (f 0) (Fin.maxU n (fun i => f i.succ))

/-- `one` exactly when the positions agree. -/
def Usage01ω.at (i j : Nat) : Usage01ω := if i = j then .one else .zero

section Layer1
variable {Φ : KCtx ks} {Γ : UCtx ks}

mutual
/-- Occurrences of the unknown at position `i`. -/
def Neu.countU (i : Nat) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Usage01ω
  | _, _,  .var x => Usage01ω.at x.index i
  | _, _,  .data_out _ _ n => n.countU i
  | _, _,  .cond c a b => c.countU i + a.countU i + b.countU i
  | _, _,  .extern _ args _ => args.countU i
/-- Occurrences of the unknown at position `i`. -/
def PExpr.countU (i : Nat) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Usage01ω
  | _, _, .neu n => n.countU i
  | _, _, .kvar _ => .zero
  | _, _, .lit _ _ => .zero
  | _, _, .enum_mk _ _ => .zero
  | _, _, .record_mk args => args.countU i
  | _, _, .union_mk _ args => args.countU i
  | _, _, .array_mk es => es.countU i
  | _, _, .list_mk es => es.countU i
  | _, _, .data_in _ _ e => e.countU i
/-- Occurrences of the unknown at position `i`. -/
def Args.countU (i : Nat) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Usage01ω
  | _, _, .nil => .zero
  | _, _, .cons a as => a.countU i + as.countU i
/-- Occurrences of the unknown at position `i`. -/
def Elems.countU (i : Nat) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Usage01ω
  | _, _, .nil => .zero
  | _, _, .cons e es => e.countU i + es.countU i
end

mutual
/-- Occurrences of the known value at position `i`. -/
def Neu.countK (i : Nat) : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Usage01ω
  | _, _,  .var _ => .zero
  | _, _,  .data_out _ _ n => n.countK i
  | _, _,  .cond c a b => c.countK i + a.countK i + b.countK i
  | _, _,  .extern _ args _ => args.countK i
/-- Occurrences of the known value at position `i`. -/
def PExpr.countK (i : Nat) : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Usage01ω
  | _, _, .neu n => n.countK i
  | _, _, .kvar k => Usage01ω.at k.index i
  | _, _, .lit _ _ => .zero
  | _, _, .enum_mk _ _ => .zero
  | _, _, .record_mk args => args.countK i
  | _, _, .union_mk _ args => args.countK i
  | _, _, .array_mk es => es.countK i
  | _, _, .list_mk es => es.countK i
  | _, _, .data_in _ _ e => e.countK i
/-- Occurrences of the known value at position `i`. -/
def Args.countK (i : Nat) : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Usage01ω
  | _, _, .nil => .zero
  | _, _, .cons a as => a.countK i + as.countK i
/-- Occurrences of the known value at position `i`. -/
def Elems.countK (i : Nat) : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Usage01ω
  | _, _, .nil => .zero
  | _, _, .cons e es => e.countK i + es.countK i
end

end Layer1

mutual
/-- Occurrences of the unknown at position `i`. -/
def Val.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Val Δ d Φ Γ τ o → Usage01ω
  | _, _, _, _, _, .lam b => b.countU i
  | _, _, _, _, _, .thunk_mk b => b.countU i
  | _, _, _, _, _, .lazy_mk b => b.countU i
  | _, _, _, _, _, .record_mk args => args.countU i
  | _, _, _, _, _, .union_mk _ args => args.countU i
  | _, _, _, _, _, .array_mk es => es.countU i
  | _, _, _, _, _, .list_mk es => es.countU i
  | _, _, _, _, _, .data_in _ _ e => e.countU i
/-- Occurrences of the unknown at position `i` (of the context outside the body). -/
def Body.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Body Δ d Φ Γ bs τ o → Usage01ω
  | _, _, _, _, _, _, .closed _ => .zero
  | _, _, _, bs, _, _, .opened t _ => (t.countU (i + bs.length)).scale
/-- Occurrences of the unknown at position `i`. -/
def Comp.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → Comp Δ d Φ Γ τ ℓ → Usage01ω
  | _, _, _, _, _, .app f a _ => f.countU i + a.countU i
  | _, _, _, _, _, .share n => n.countU i
  | _, _, _, _, _, .nat_rec n z s _ => n.countU i + z.countU i + s.countU i
  | _, _, _, _, _, .array_foldl a z s _ => a.countU i + z.countU i + s.countU i
  | _, _, _, _, _, .data_rec _ _ _ brs _ e _ => Fin.sumU _ (fun j => (brs j).countU i) + e.countU i
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ e _ =>
      Fin.sumU _ (fun j => (brs j).countU i) + e.countU i
  | _, _, _, _, _, .thunk_force e => e.countU i
  | _, _, _, _, _, .lazy_force e => e.countU i
/-- Occurrences of the unknown at position `i`. -/
def Term.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Usage01ω
  | _, _, _, _, _, _, .ret e => e.countU i
  | _, _, _, _, _, _, .letV _ v b => v.countU i + b.countU i
  | _, _, _, _, _, _, .letE _ c b => c.countU i + b.countU (i + 1)
  | _, _, _, _, _, _, .record_casesOn (t := t) (fs := fs) _ n b =>
      n.countU i + b.countU (i + (t :: fs.toList).length)
  | _, _, _, _, _, _, .branch br => br.countU i
  | _, _, _, _, _, _, .jump _ e => e.countU i
/-- Occurrences of the unknown at position `i`: the arms take the maximum. -/
def Branch.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Usage01ω
  | _, _, _, _, _, _, .ite c t e => c.countU i + Usage01ω.max (t.countU i) (e.countU i)
  | _, _, _, _, _, _, .enum_casesOn e bs => e.countU i + Fin.maxU _ (fun j => (bs j).countU i)
  | _, _, _, _, _, _, .union_casesOn e bs => e.countU i + bs.countU i
  | _, _, _, _, _, _, .join _ _ _ body main => body.countU (i + 1) + main.countU i
/-- Occurrences of the unknown at position `i`: the arms take the maximum. -/
def Branches.countU (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Usage01ω
  | _, _, _, _, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) _ _ b₁ b₂ =>
      Usage01ω.max (b₁.countU (i + c₁.binds.length)) (b₂.countU (i + c₂.binds.length))
  | _, _, _, _, _, _, _, _, .cons (c := c) _ b bs =>
      Usage01ω.max (b.countU (i + c.binds.length)) (bs.countU i)
end

mutual
/-- Occurrences of the known value at position `i`. -/
def Val.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Val Δ d Φ Γ τ o → Usage01ω
  | _, _, _, _, _, .lam b => b.countK i
  | _, _, _, _, _, .thunk_mk b => b.countK i
  | _, _, _, _, _, .lazy_mk b => b.countK i
  | _, _, _, _, _, .record_mk args => args.countK i
  | _, _, _, _, _, .union_mk _ args => args.countK i
  | _, _, _, _, _, .array_mk es => es.countK i
  | _, _, _, _, _, .list_mk es => es.countK i
  | _, _, _, _, _, .data_in _ _ e => e.countK i
/-- Occurrences of the known value at position `i`. -/
def Body.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → Body Δ d Φ Γ bs τ o → Usage01ω
  | _, _, _, _, _, _, .closed t => (t.countK i).scale
  | _, _, _, _, _, _, .opened t _ => (t.countK i).scale
/-- Occurrences of the known value at position `i`. -/
def Comp.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → Comp Δ d Φ Γ τ ℓ → Usage01ω
  | _, _, _, _, _, .app f a _ => f.countK i + a.countK i
  | _, _, _, _, _, .share n => n.countK i
  | _, _, _, _, _, .nat_rec n z s _ => n.countK i + z.countK i + s.countK i
  | _, _, _, _, _, .array_foldl a z s _ => a.countK i + z.countK i + s.countK i
  | _, _, _, _, _, .data_rec _ _ _ brs _ e _ => Fin.sumU _ (fun j => (brs j).countK i) + e.countK i
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ e _ =>
      Fin.sumU _ (fun j => (brs j).countK i) + e.countK i
  | _, _, _, _, _, .thunk_force e => e.countK i
  | _, _, _, _, _, .lazy_force e => e.countK i
/-- Occurrences of the known value at position `i`. -/
def Term.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Usage01ω
  | _, _, _, _, _, _, .ret e => e.countK i
  | _, _, _, _, _, _, .letV _ v b => v.countK i + b.countK (i + 1)
  | _, _, _, _, _, _, .letE _ c b => c.countK i + b.countK i
  | _, _, _, _, _, _, .record_casesOn _ n b => n.countK i + b.countK i
  | _, _, _, _, _, _, .branch br => br.countK i
  | _, _, _, _, _, _, .jump _ e => e.countK i
/-- Occurrences of the known value at position `i`: the arms take the maximum. -/
def Branch.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Usage01ω
  | _, _, _, _, _, _, .ite c t e => c.countK i + Usage01ω.max (t.countK i) (e.countK i)
  | _, _, _, _, _, _, .enum_casesOn e bs => e.countK i + Fin.maxU _ (fun j => (bs j).countK i)
  | _, _, _, _, _, _, .union_casesOn e bs => e.countK i + bs.countK i
  | _, _, _, _, _, _, .join _ _ _ body main => body.countK i + main.countK i
/-- Occurrences of the known value at position `i`: the arms take the maximum. -/
def Branches.countK (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Usage01ω
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => Usage01ω.max (b₁.countK i) (b₂.countK i)
  | _, _, _, _, _, _, _, _, .cons _ b bs => Usage01ω.max (b.countK i) (bs.countK i)
end

mutual
/-- Jumps to the join point at position `i`. -/
def Term.countJ (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Usage01ω
  | _, _, _, _, _, _, .ret _ => .zero
  | _, _, _, _, _, _, .letV _ _ b => b.countJ i
  | _, _, _, _, _, _, .letE _ _ b => b.countJ i
  | _, _, _, _, _, _, .record_casesOn _ _ b => b.countJ i
  | _, _, _, _, _, _, .branch br => br.countJ i
  | _, _, _, _, _, _, .jump j _ => Usage01ω.at j.index i
/-- Jumps to the join point at position `i`: the arms take the maximum. -/
def Branch.countJ (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Usage01ω
  | _, _, _, _, _, _, .ite _ t e => Usage01ω.max (t.countJ i) (e.countJ i)
  | _, _, _, _, _, _, .enum_casesOn _ bs => Fin.maxU _ (fun j => (bs j).countJ i)
  | _, _, _, _, _, _, .union_casesOn _ bs => bs.countJ i
  | _, _, _, _, _, _, .join _ _ _ body main => body.countJ i + main.countJ (i + 1)
/-- Jumps to the join point at position `i`: the arms take the maximum. -/
def Branches.countJ (i : Nat) : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Usage01ω
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => Usage01ω.max (b₁.countJ i) (b₂.countJ i)
  | _, _, _, _, _, _, _, _, .cons _ b bs => Usage01ω.max (b.countJ i) (bs.countJ i)
end

end LeanScript

end
