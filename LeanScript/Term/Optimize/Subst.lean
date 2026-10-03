module

public import LeanScript.Term.Optimize.InlineBlock
public import LeanScript.Term.Optimize.Fold

@[expose] public section

set_option autoImplicit false

/-!
# Substituting pure expressions for unknowns, levels and depths allowed to change

`Term.relvl` (`LeanScript.Term.Rename.Relevel`) renames unknowns to unknowns.  To inline a known
closure on an argument that is not neutral (a known closure passed to it, a literal, a record
built for the call), or to bind the answer of an inlined body that is not neutral, an unknown
must be replaced by a **pure expression**: a known variable, a literal, a constructor.

`Term.subst` does it: the unknowns are mapped by a `USub` to pure expressions of the target
contexts (the known values by a `KLRen`, as in `Term.relvl`).  A pure expression replaces the
unknown wherever it is used as a pure expression; where a *neutral* expression is needed (the
operand of a case analysis, of `share`, of `data_out`, the condition of `cond`) the result must
still be neutral, otherwise the substitution fails (`none`) — with a few exceptions, which are
steps of normalisation: a case analysis `record_casesOn` of a record literal binds its fields to
the fields of the literal (the fields are substituted in turn) and disappears, and so does a
case analysis of an enum or union literal (its arm is kept); an `if` or a conditional `c ? a :
b` whose condition becomes a boolean literal is the arm it takes; an extern call whose
arguments all become constants is the literal of its value when the result is of a leaf type
(`Neu.mkExtern?`: `lean_nat_dec_eq 3 3` is `true`).

No computation is repeated: inside a body (of a closure, a delay, a loop) only the pure
expressions that cost nothing to repeat are substituted (`USub.cheapOnly`: an unknown, a known
value by name, a literal), and so is a field of a record literal that is used more than once.
Where another one would be needed, the substitution fails.

As in `Term.relvl`, the levels are recomputed and the side conditions that depend on them are
checked; the statement moves from depth `D` to depth `D'`.

`Term.subst_eval` (`LeanScript.Term.Optimize.SubstEval`): when the maps agree with the
environments, the value does not change.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Maps -/

/-- A partial map of unknowns to pure expressions of the target contexts. -/
abbrev USub (Δ : DSig ks) (Φ' : KCtx ks) (Γ Γ' : UCtx ks) : Type :=
  ∀ {τ : Ty ks} {ℓ : Nat}, UVar Γ τ ℓ → Option ((o : Lvl) × PExpr Δ Φ' Γ' τ o)

/-- A pure expression that costs nothing to repeat: an unknown, a known value by name, a
    literal. -/
def PExpr.isCheap {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} : {o : Lvl} → PExpr Δ Φ Γ τ o → Bool
  | _, .neu (.var _) => true
  | _, .kvar _ => true
  | _, .lit _ _ => true
  | _, .enum_mk _ _ => true
  | _, _ => false

/-- Whether a variable of this usage can receive a copy of an expression that is not cheap. -/
def Usage01ω.atMostOnce : Usage01ω → Bool
  | .zero => true
  | .one => true
  | .many => false

section Maps
variable {Φ' : KCtx ks} {Γ Γ' : UCtx ks}

/-- A renaming, as a substitution. -/
def USub.ofRen (r : ULRen Γ Γ') : USub Δ Φ' Γ Γ' :=
  fun x => (r x).map fun p => ⟨some p.1, .neu (.var p.2)⟩

/-- One more unknown in the target. -/
def USub.wkU (s : USub Δ Φ' Γ Γ') (b : UBinder ks) : USub Δ Φ' Γ (b :: Γ') :=
  fun x => (s x).bind fun p => (p.2.rename KRen.id URen.wk1).map fun e => ⟨p.1, e⟩

/-- One more known value in the target. -/
def USub.wkK (s : USub Δ Φ' Γ Γ') (b : KBinder ks) : USub Δ (b :: Φ') Γ Γ' :=
  fun x => (s x).bind fun p => (p.2.rename KRen.wk1 URen.id).map fun e => ⟨p.1, e⟩

/-- Under one more binder, moved to level `L'`. -/
def USub.lift (s : USub Δ Φ' Γ Γ') (σ : Ty ks) (u : Usage01ω) (L L' : Nat) :
    USub Δ Φ' (⟨σ, u, L⟩ :: Γ) (⟨σ, u, L'⟩ :: Γ')
  | _, _, .head h => some ⟨some L', .neu (.var (.head h))⟩
  | _, _, .tail x => USub.wkU s _ x

/-- Under the binders `bs`, moved to level `L'`. -/
def USub.liftSet (s : USub Δ Φ' Γ Γ') (L' : Nat) :
    (bs : UCtx ks) → USub Δ Φ' (bs ++ Γ) (UCtx.setLv L' bs ++ Γ')
  | [] => s
  | b :: bs => USub.lift (USub.liftSet s L' bs) b.ty b.use b.lv L'

/-- Under the fields of a case analysis, moved from level `L` to level `L'`. -/
def USub.liftAnnot (s : USub Δ Φ' Γ Γ') (L L' : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) →
    USub Δ Φ' (UCtx.annot L ts us ++ Γ) (UCtx.annot L' ts us ++ Γ')
  | [], _ => s
  | t :: ts, [] => USub.lift (USub.liftAnnot s L L' ts []) t .many L L'
  | t :: ts, u :: us => USub.lift (USub.liftAnnot s L L' ts us) t u L L'

/-- One more unknown in the source, mapped to `a`. -/
def USub.cons {σ : Ty ks} {u : Usage01ω} {L : Nat} (a : (o : Lvl) × PExpr Δ Φ' Γ' σ o)
    (s : USub Δ Φ' Γ Γ') : USub Δ Φ' (⟨σ, u, L⟩ :: Γ) Γ'
  | _, _, .head _ => some a
  | _, _, .tail x => s x

/-- One more unknown in the source, mapped to `a` if any (not substituted otherwise). -/
def USub.consOpt {σ : Ty ks} {u : Usage01ω} {L : Nat} (a : Option ((o : Lvl) × PExpr Δ Φ' Γ' σ o))
    (s : USub Δ Φ' Γ Γ') : USub Δ Φ' (⟨σ, u, L⟩ :: Γ) Γ'
  | _, _, .head _ => a
  | _, _, .tail x => s x

/-- Only the pure expressions that cost nothing to repeat (`PExpr.isCheap`). -/
def USub.cheapOnly (s : USub Δ Φ' Γ Γ') : USub Δ Φ' Γ Γ' :=
  fun x => (s x).bind fun p => if p.2.isCheap then some p else none

/-- The fields of a case analysis mapped to the fields of a record literal; a field used more
    than once gets only a field that costs nothing to repeat (otherwise the substitution fails
    where it is used), so that no computation is repeated. -/
def USub.ofArgs (s : USub Δ Φ' Γ Γ') (L : Nat) :
    (ts : List (Ty ks)) → (us : List Usage01ω) → {o : Lvl} → Args Δ Φ' Γ' ts o →
    USub Δ Φ' (UCtx.annot L ts us ++ Γ) Γ'
  | [], _, _, .nil => s
  | _ :: ts, [], _, .cons a as =>
      USub.consOpt (if a.isCheap then some ⟨_, a⟩ else none) (USub.ofArgs s L ts [] as)
  | _ :: ts, u :: us, _, .cons a as =>
      USub.consOpt (if a.isCheap || u.atMostOnce then some ⟨_, a⟩ else none)
        (USub.ofArgs s L ts us as)

end Maps

/-- The fields of a record literal. -/
def PExpr.recordArgs? {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {fs : Fields ks} :
    {o : Lvl} → PExpr Δ Φ Γ (.record t fs) o → Option ((o' : Lvl) × Args Δ Φ Γ (t :: fs.toList) o')
  | _, .record_mk args => some ⟨_, args⟩
  | _, _ => none

/-! ## Pure expressions -/

section Layer1
variable {Φ Φ' : KCtx ks} {Γ Γ' : UCtx ks} (rk : KLRen Φ Φ') (s : USub Δ Φ' Γ Γ')

mutual
/-- Substitute in a neutral expression; the result is a pure expression. -/
def Neu.subst : {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → Option ((o : Lvl) × PExpr Δ Φ' Γ' τ o)
  | _, _, .var x => s x
  | _, _, .data_out b j n => do
      let p ← Neu.subst n
      let m ← p.2.toNeu?
      pure ⟨_, .neu (.data_out b j m.2)⟩
  | _, _, .cond c a b => do
      let p ← Neu.subst c
      match p.2.boolLit? with
      | some true => PExpr.subst a
      | some false => PExpr.subst b
      | none =>
          let m ← p.2.toNeu?
          let a ← PExpr.subst a
          let b ← PExpr.subst b
          pure ⟨_, .neu (.cond m.2 a.2 b.2)⟩
  | _, _, .extern e args _ => do
      let as ← Args.subst args
      Neu.mkExtern? e as.2
/-- Substitute in a pure expression, recomputing its level. -/
def PExpr.subst : {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o →
    Option ((o' : Lvl) × PExpr Δ Φ' Γ' τ o')
  | _, _, .neu n => Neu.subst n
  | _, _, .kvar k => (rk k).map fun p => ⟨_, .kvar p.2⟩
  | _, _, .lit p v => some ⟨_, .lit p v⟩
  | _, _, .enum_mk s i => some ⟨_, .enum_mk s i⟩
  | _, _, .record_mk args => (Args.subst args).map fun p => ⟨_, .record_mk p.2⟩
  | _, _, .union_mk ix args => (Args.subst args).map fun p => ⟨_, .union_mk ix p.2⟩
  | _, _, .array_mk es => (Elems.subst es).map fun p => ⟨_, .array_mk p.2⟩
  | _, _, .list_mk es => (Elems.subst es).map fun p => ⟨_, .list_mk p.2⟩
  | _, _, .data_in b j e => (PExpr.subst e).map fun p => ⟨_, .data_in b j p.2⟩
/-- Substitute in arguments, recomputing their level. -/
def Args.subst : {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o →
    Option ((o' : Lvl) × Args Δ Φ' Γ' σs o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons a as => do
      let a ← PExpr.subst a
      let as ← Args.subst as
      pure ⟨_, .cons a.2 as.2⟩
/-- Substitute in elements, recomputing their level. -/
def Elems.subst : {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o →
    Option ((o' : Lvl) × Elems Δ Φ' Γ' t o')
  | _, _, .nil => some ⟨_, .nil⟩
  | _, _, .cons e es => do
      let e ← PExpr.subst e
      let es ← Elems.subst es
      pure ⟨_, .cons e.2 es.2⟩
end

/-- Substitute in a neutral expression that must stay neutral. -/
def Neu.substN {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) : Option ((ℓ' : Nat) × Neu Δ Φ' Γ' τ ℓ') :=
  (n.subst rk s).bind fun p => p.2.toNeu?

end Layer1

/-- The constructor of an enum literal. -/
def PExpr.enumLit? {Φ : KCtx ks} {Γ : UCtx ks} {e : LeanEnumSchema} :
    {o : Lvl} → PExpr Δ Φ Γ (.enum e) o → Option (Fin e.nOfConstructors)
  | _, .enum_mk _ i => some i
  | _, _ => none

/-- A jump out of the branch of a join point `j`: to `j` itself (`inl`, its argument of the type
    of the parameter of `j`) or to a join point further out (`inr`). -/
def JVar.split {σ τ' : Ty ks} {u : Usage1ω} {js : JCtx ks} :
    JVar (⟨σ, u⟩ :: js) τ' → PLift (τ' = σ) ⊕ JVar js τ'
  | .head => .inl ⟨rfl⟩
  | .tail j => .inr j

/-- The branch a statement is, if it is one. -/
def Term.asBranch? {D : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} :
    {o : Lvl} → Term Δ D Φ Γ τ js o → Option ((ℓ : Nat) × Branch Δ D Φ Γ τ js ℓ)
  | _, .branch b => some ⟨_, b⟩
  | _, _ => none

/-- The jump a statement is, if it is one. -/
def Term.asJump? {D : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} :
    {o : Lvl} → Term Δ D Φ Γ τ js o →
      Option ((σ : Ty ks) × JVar js σ × (o' : Lvl) × PExpr Δ Φ Γ σ o')
  | _, .jump j a => some ⟨_, j, _, a⟩
  | _, _ => none

/-- The constructor and the fields of a union literal. -/
def PExpr.unionLit? {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {h : UnionShape bs} : {o : Lvl} → PExpr Δ Φ Γ (.union cs (h := h)) o →
    Option ((b : Bool) × (c : Ctor ks b) × CtorIx cs c × (o' : Lvl) × Args Δ Φ Γ c.binds o')
  | _, .union_mk ix args => some ⟨_, _, ix, _, args⟩
  | _, _ => none

/-! ## Statements -/

mutual
/-- Substitute in a value and move it from depth `D` to depth `D'`. -/
def Val.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' →
    USub Δ Φ' Γ Γ' → {τ : Ty ks} → {o : Lvl} → Val Δ D Φ Γ τ o →
    Option ((o' : Lvl) × Val Δ D' Φ' Γ' τ o')
  | _, _, _, _, _, _, rk, s, _, _, .lam b => (b.subst rk s).map fun p => ⟨_, .lam p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .thunk_mk b => (b.subst rk s).map fun p => ⟨_, .thunk_mk p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .lazy_mk b => (b.subst rk s).map fun p => ⟨_, .lazy_mk p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .record_mk args =>
      (args.subst rk s).map fun p => ⟨_, .record_mk p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .union_mk ix args =>
      (args.subst rk s).map fun p => ⟨_, .union_mk ix p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .array_mk es => (es.subst rk s).map fun p => ⟨_, .array_mk p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .list_mk es => (es.subst rk s).map fun p => ⟨_, .list_mk p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .data_in b j e =>
      (e.subst rk s).map fun p => ⟨_, .data_in b j p.2⟩
/-- Substitute in a body and move it from depth `D` to depth `D'`. -/
def Body.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' →
    USub Δ Φ' Γ Γ' → {bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} → Body Δ D Φ Γ bs τ o →
    Option ((o' : Lvl) × Body Δ D' Φ' Γ' (UCtx.setLv (D' + 1) bs) τ o')
  | _, D', _, _, _, _, rk, _, bs, _, _, .closed t =>
      (t.relvl (D' := D' + 1) (KLRen.closedOnly rk) (ULRen.setLvOnly (D' + 1) bs) JRen.nil).map
        fun p => ⟨_, .closed p.2⟩
  | _, D', _, _, _, _, rk, s, bs, _, _, .opened t _ => do
      let p ← t.subst (D' := D' + 1) rk (USub.liftSet s.cheapOnly (D' + 1) bs) JRen.nil
      let m ← Lvl.some? p.1
      if hm : m.1 ≤ D' then pure ⟨_, .opened (m.2 ▸ p.2) hm⟩ else none
/-- Substitute in a computation and move it from depth `D` to depth `D'`. -/
def Comp.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → KLRen Φ Φ' →
    USub Δ Φ' Γ Γ' → {τ : Ty ks} → {ℓ : Nat} → Comp Δ D Φ Γ τ ℓ →
    Option ((ℓ' : Nat) × Comp Δ D' Φ' Γ' τ ℓ')
  | _, _, _, _, _, _, rk, s, _, _, .app f a _ => do
      let f ← f.subst rk s
      let a ← a.subst rk s
      let h ← Lvl.some? (Lvl.meet f.1 a.1)
      pure ⟨_, .app f.2 a.2 h.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .share n => (n.substN rk s).map fun p => ⟨_, .share p.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .nat_rec n z st _ => do
      let n ← n.subst rk s
      let z ← z.subst rk s
      let st ← st.subst rk s
      let h ← Lvl.some? (Lvl.meet (Lvl.meet n.1 z.1) st.1)
      pure ⟨_, .nat_rec n.2 z.2 st.2 h.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .array_foldl a z st _ => do
      let a ← a.subst rk s
      let z ← z.subst rk s
      let st ← st.subst rk s
      let h ← Lvl.some? (Lvl.meet (Lvl.meet a.1 z.1) st.1)
      pure ⟨_, .array_foldl a.2 z.2 st.2 h.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .data_rec b ρ us brs j e _ => do
      let brs ← Fin.optAll (fun i => (brs i).subst rk s)
      let e ← e.subst rk s
      let h ← Lvl.some? (Lvl.meet e.1 (Lvl.meetFin _ (fun i => (brs i).1)))
      pure ⟨_, .data_rec b ρ us (fun i => (brs i).2) j e.2 h.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .data_brec b ρ k us brs j e _ => do
      let brs ← Fin.optAll (fun i => (brs i).subst rk s)
      let e ← e.subst rk s
      let h ← Lvl.some? (Lvl.meet e.1 (Lvl.meetFin _ (fun i => (brs i).1)))
      pure ⟨_, .data_brec b ρ k us (fun i => (brs i).2) j e.2 h.2⟩
  | _, _, _, _, _, _, rk, s, _, _, .thunk_force e => do
      let e ← e.subst rk s
      let h ← Lvl.some? e.1
      pure ⟨_, .thunk_force (h.2 ▸ e.2)⟩
  | _, _, _, _, _, _, rk, s, _, _, .lazy_force e => do
      let e ← e.subst rk s
      let h ← Lvl.some? e.1
      pure ⟨_, .lazy_force (h.2 ▸ e.2)⟩
/-- Substitute in a statement and move it from depth `D` to depth `D'`. -/
def Term.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → USub Δ Φ' Γ Γ' → JRen js js' → {τ : Ty ks} → {o : Lvl} →
    Term Δ D Φ Γ τ js o → Option ((o' : Lvl) × Term Δ D' Φ' Γ' τ js' o')
  | _, _, _, _, _, _, _, _, rk, s, _, _, _, .ret e => (e.subst rk s).map fun p => ⟨_, .ret p.2⟩
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .letV (σ := σ) (o := o) u v b => do
      let v ← v.subst rk s
      let b ← b.subst (KLRen.lift rk σ u o v.1) (USub.wkK s _) rj
      pure ⟨_, .letV u v.2 b.2⟩
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, .letE (σ := σ) u c b => do
      let c ← c.subst rk s
      let b ← b.subst (D' := D') rk (USub.lift s σ u.toUsage01ω D D') rj
      pure ⟨_, .letE u c.2 b.2⟩
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, .record_casesOn (t := t) (fs := fs) us n b => do
      let p ← n.subst rk s
      match p.2.toNeu? with
      | some m =>
          let b ← b.subst (D' := D') rk (USub.liftAnnot s D D' (t :: fs.toList) us) rj
          pure ⟨_, .record_casesOn us m.2 b.2⟩
      | none =>
          let as ← p.2.recordArgs?
          b.subst (D' := D') rk (USub.ofArgs s D (t :: fs.toList) us as.2) rj
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .branch br => br.subst rk s rj
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .jump j e => do
      let j ← rj j
      let e ← e.subst rk s
      pure ⟨_, .jump j e.2⟩
/-- Substitute in a branch and move it from depth `D` to depth `D'`; the result is a statement,
    because a case analysis of a constructor that the substitution makes known is reduced:
    `case e of …` where `e` becomes an enum literal is the arm of its constructor (and so for a
    union literal, its fields bound to the fields of the literal, `Branches.substSel`),
    `if c then t else e` where `c` becomes a boolean literal is the arm it takes, and a join
    point whose branch becomes a jump is gone (`join j x := body; jump j a` is `body[x := a]`,
    when `a` costs nothing to repeat or `x` is used at most once; a jump to a join point further
    out stays that jump). -/
def Branch.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → USub Δ Φ' Γ Γ' → JRen js js' → {τ : Ty ks} → {ℓ : Nat} →
    Branch Δ D Φ Γ τ js ℓ → Option ((o' : Lvl) × Term Δ D' Φ' Γ' τ js' o')
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .ite c t e => do
      let p ← c.subst rk s
      match p.2.boolLit? with
      | some true => t.subst rk s rj
      | some false => e.subst rk s rj
      | none =>
          let c ← p.2.toNeu?
          let t ← t.subst rk s rj
          let e ← e.subst rk s rj
          pure ⟨_, .branch (.ite c.2 t.2 e.2)⟩
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .enum_casesOn e bs => do
      let p ← e.subst rk s
      match p.2.toNeu? with
      | some m =>
          let bs ← Fin.optAll (fun i => (bs i).subst rk s rj)
          pure ⟨_, .branch (.enum_casesOn m.2 (fun i => (bs i).2))⟩
      | none =>
          let i ← p.2.enumLit?
          (bs i).subst rk s rj
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, .union_casesOn e bs => do
      let p ← e.subst rk s
      match p.2.toNeu? with
      | some m =>
          let bs ← bs.subst rk s rj
          pure ⟨_, .branch (.union_casesOn m.2 bs.2)⟩
      | none =>
          let ⟨_, _, ix, _, args⟩ ← p.2.unionLit?
          bs.substSel rk s rj ix args
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, .join σ u uₓ body main => do
      let m ← main.subst rk s (JRen.lift rj _)
      match m.2.asBranch? with
      | some b =>
          let body ← body.subst (D' := D') rk (USub.lift s σ uₓ D D') rj
          pure ⟨_, .branch (.join σ u uₓ body.2 b.2)⟩
      | none =>
          match m.2.asJump? with
          | some ⟨_, j, _, a⟩ =>
              match j.split with
              | .inl h =>
                  if a.isCheap || uₓ.atMostOnce then
                    body.subst (D' := D') rk (USub.cons ⟨_, h.down ▸ a⟩ s) rj
                  else none
              | .inr j' => pure ⟨_, .jump j' a⟩
          | none => none
/-- Substitute in the branches of a union's case analysis. -/
def Branches.subst : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → USub Δ Φ' Γ Γ' → JRen js js' → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → {o : Lvl} → Branches Δ D Φ Γ cs τ js o →
    Option ((o' : Lvl) × Branches Δ D' Φ' Γ' cs τ js' o')
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, _, _, .two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂ => do
      let b₁ ← b₁.subst (D' := D') rk (USub.liftAnnot s D D' c₁.binds us₁) rj
      let b₂ ← b₂.subst (D' := D') rk (USub.liftAnnot s D D' c₂.binds us₂) rj
      pure ⟨_, .two us₁ us₂ b₁.2 b₂.2⟩
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, _, _, .cons (c := c) us b bs => do
      let b ← b.subst (D' := D') rk (USub.liftAnnot s D D' c.binds us) rj
      let bs ← bs.subst rk s rj
      pure ⟨_, .cons us b.2 bs.2⟩
/-- Substitute in the arm of the constructor `ix` of a union's case analysis, its fields bound
    to the fields `args` of a union literal (`USub.ofArgs`): the case analysis of a literal is
    reduced. -/
def Branches.substSel : {D D' : Nat} → {Φ Φ' : KCtx ks} → {Γ Γ' : UCtx ks} → {js js' : JCtx ks} →
    KLRen Φ Φ' → USub Δ Φ' Γ Γ' → JRen js js' → {bs : List Bool} → {cs : Ctors ks bs} →
    {τ : Ty ks} → {o : Lvl} → Branches Δ D Φ Γ cs τ js o → {b : Bool} → {c : Ctor ks b} →
    CtorIx cs c → {oa : Lvl} → Args Δ Φ' Γ' c.binds oa →
    Option ((o' : Lvl) × Term Δ D' Φ' Γ' τ js' o')
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, _, _, .two (c₁ := c₁) us₁ _ b₁ _, _, _, .two₁, _, args =>
      b₁.subst (D' := D') rk (USub.ofArgs s D c₁.binds us₁ args) rj
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, _, _, .two (c₂ := c₂) _ us₂ _ b₂, _, _, .two₂, _, args =>
      b₂.subst (D' := D') rk (USub.ofArgs s D c₂.binds us₂ args) rj
  | D, D', _, _, _, _, _, _, rk, s, rj, _, _, _, _, .cons (c := c) us b _, _, _, .head, _, args =>
      b.subst (D' := D') rk (USub.ofArgs s D c.binds us args) rj
  | _, _, _, _, _, _, _, _, rk, s, rj, _, _, _, _, .cons _ _ bs, _, _, .tail ix, _, args =>
      bs.substSel rk s rj ix args
end

end LeanScript

end
