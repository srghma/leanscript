module

public import LeanScript.Term.Syntax.Term

@[expose] public section

set_option autoImplicit false

/-!
# Levels are sound, and a statement with nothing unknown is a value

**Levels.**  Everything is at least as deep as what is in scope: when every unknown and every
known value in scope has a level `≥ L` (`UCtx.Ge`, `KCtx.Ge`), so has everything built in that
scope at a depth `≥ L` (`Term.level_ge` and its companions for the other classes).  In
particular a body at depth `d` in which nothing bound outside of it is visible is **closed**
(`Body.closed_of_ge`): `Body.opened` really needs something from outside.

**Values.**  The central property of the normal form, enforced by the types: when there is no
unknown in scope (`Γ = []`) and no usable known value is open (`KCtx.Closed Φ`), there is

* no neutral expression, no computation and no branch (`Neu.not_closed`, `Comp.not_closed`,
  `Branch.not_closed`), and every pure expression, value and body is closed
  (`PExpr.closed`, `Val.closed`, `Body.closed_eq`);
* so a statement is a chain of `letV`s of closed values ending in `ret v` with `v` closed
  (`Term.closed_isValue`): **nothing is left to compute**.

In particular a whole program (`Term Δ 0 [] [] τ [] o`) is a value (`Term.run_isValue`), and so
is the body of every closed closure, closed delay and closed loop body once its own
parameters are known — the body of a closed delay, which has no parameter, is already a value
(`Term.closedBody_isValue`).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Lower bounds of levels -/

/-- `o` is at least `L`: closed, or open at a level `≥ L`. -/
def Lvl.Ge (L : Nat) : Lvl → Prop
  | none => True
  | some m => L ≤ m

/-- Every usable unknown has a level `≥ L`. -/
def UCtx.Ge (L : Nat) (Γ : UCtx ks) : Prop := ∀ {τ : Ty ks} {ℓ : Nat}, UVar Γ τ ℓ → L ≤ ℓ

/-- Every visible known value has a level `≥ L`. -/
def KCtx.Ge (L : Nat) (Φ : KCtx ks) : Prop := ∀ {τ : Ty ks} {o : Lvl}, KVar Φ τ o → Lvl.Ge L o

theorem Lvl.Ge.meet {L : Nat} : {o₁ o₂ : Lvl} → Lvl.Ge L o₁ → Lvl.Ge L o₂ →
    Lvl.Ge L (Lvl.meet o₁ o₂)
  | none, _, _, h => h
  | some _, none, h, _ => h
  | some _, some _, h₁, h₂ => Nat.le_min.mpr ⟨h₁, h₂⟩

theorem Lvl.Ge.meetL {L ℓ : Nat} : {o : Lvl} → L ≤ ℓ → Lvl.Ge L o → L ≤ Lvl.meetL ℓ o
  | none, h, _ => h
  | some _, h₁, h₂ => Nat.le_min.mpr ⟨h₁, h₂⟩

theorem Lvl.Ge.meetFin {L : Nat} : (n : Nat) → {f : Fin n → Lvl} → (∀ i, Lvl.Ge L (f i)) →
    Lvl.Ge L (Lvl.meetFin n f)
  | 0, _, _ => trivial
  | n + 1, _, h => Lvl.Ge.meet (h 0) (Lvl.Ge.meetFin n (fun i => h i.succ))

theorem UCtx.Ge.nil (L : Nat) : UCtx.Ge L ([] : UCtx ks) := fun x => nomatch x

theorem UCtx.Ge.cons {L : Nat} {Γ : UCtx ks} (b : UBinder ks) (hb : L ≤ b.lv) (h : UCtx.Ge L Γ) :
    UCtx.Ge L (b :: Γ) := fun
  | .head _ => hb
  | .tail x => h x

theorem UCtx.Ge.append {L : Nat} {Γ : UCtx ks} : (bs : UCtx ks) → UCtx.Ge L bs → UCtx.Ge L Γ →
    UCtx.Ge L (bs ++ Γ)
  | [], _, h => h
  | ⟨_, _, _⟩ :: bs, hbs, h => fun
    | .head hu => hbs (.head hu)
    | .tail x => UCtx.Ge.append bs (fun y => hbs (.tail y)) h x

theorem UCtx.Ge.annot {L d : Nat} (hL : L ≤ d) :
    (ts : List (Ty ks)) → (us : List Usage01ω) → UCtx.Ge L (UCtx.annot d ts us)
  | [], _ => UCtx.Ge.nil L
  | t :: ts, [] => UCtx.Ge.cons ⟨t, .many, d⟩ hL (UCtx.Ge.annot hL ts [])
  | t :: ts, u :: us => UCtx.Ge.cons ⟨t, u, d⟩ hL (UCtx.Ge.annot hL ts us)

theorem KCtx.Ge.cons {L : Nat} {Φ : KCtx ks} (b : KBinder ks) (hb : Lvl.Ge L b.lv)
    (h : KCtx.Ge L Φ) : KCtx.Ge L (b :: Φ) := fun
  | .head => hb
  | .tail x => h x

/-! ## Levels are sound -/

/-- An operand condition `meet … = some ℓ` bounds `ℓ` from below. -/
theorem Lvl.Ge.of_eq_some {L ℓ : Nat} {o : Lvl} (h : o = some ℓ) (hge : Lvl.Ge L o) : L ≤ ℓ := by
  subst h; exact hge


section Layer1
variable {Φ : KCtx ks} {Γ : UCtx ks} {L : Nat}

mutual
theorem Neu.level_ge (hΦ : KCtx.Ge L Φ) (hΓ : UCtx.Ge L Γ) :
    {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ Γ τ ℓ → L ≤ ℓ
  | _, _, .var x => hΓ x
  | _, _, .data_out _ _ n => Neu.level_ge hΦ hΓ n
  | _, _, .cond c a b =>
      Lvl.Ge.meetL (Neu.level_ge hΦ hΓ c) (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ a) (PExpr.level_ge hΦ hΓ b))
  | _, _, .extern _ args h => Lvl.Ge.of_eq_some h (Args.level_ge hΦ hΓ args)
theorem PExpr.level_ge (hΦ : KCtx.Ge L Φ) (hΓ : UCtx.Ge L Γ) :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ Γ τ o → Lvl.Ge L o
  | _, _, .neu n => Neu.level_ge hΦ hΓ n
  | _, _, .kvar k => hΦ k
  | _, _, .lit _ _ => trivial
  | _, _, .enum_mk _ _ => trivial
  | _, _, .record_mk args => Args.level_ge hΦ hΓ args
  | _, _, .union_mk _ args => Args.level_ge hΦ hΓ args
  | _, _, .array_mk es => Elems.level_ge hΦ hΓ es
  | _, _, .list_mk es => Elems.level_ge hΦ hΓ es
  | _, _, .data_in _ _ e => PExpr.level_ge hΦ hΓ e
theorem Args.level_ge (hΦ : KCtx.Ge L Φ) (hΓ : UCtx.Ge L Γ) :
    {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ Γ σs o → Lvl.Ge L o
  | _, _, .nil => trivial
  | _, _, .cons a as => Lvl.Ge.meet (PExpr.level_ge hΦ hΓ a) (Args.level_ge hΦ hΓ as)
theorem Elems.level_ge (hΦ : KCtx.Ge L Φ) (hΓ : UCtx.Ge L Γ) :
    {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → Lvl.Ge L o
  | _, _, .nil => trivial
  | _, _, .cons e es => Lvl.Ge.meet (PExpr.level_ge hΦ hΓ e) (Elems.level_ge hΦ hΓ es)
end

end Layer1

mutual
theorem Val.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    {L : Nat} → L ≤ d → KCtx.Ge L Φ → UCtx.Ge L Γ → Val Δ d Φ Γ τ o → Lvl.Ge L o
  | _, _, _, _, _, _, hL, hΦ, hΓ, .lam b =>
      Body.level_ge hL hΦ hΓ (UCtx.Ge.cons _ (Nat.le_succ_of_le hL) (UCtx.Ge.nil _)) b
  | _, _, _, _, _, _, hL, hΦ, hΓ, .thunk_mk b => Body.level_ge hL hΦ hΓ (UCtx.Ge.nil _) b
  | _, _, _, _, _, _, hL, hΦ, hΓ, .lazy_mk b => Body.level_ge hL hΦ hΓ (UCtx.Ge.nil _) b
  | _, _, _, _, _, _, _, hΦ, hΓ, .record_mk args => Args.level_ge hΦ hΓ args
  | _, _, _, _, _, _, _, hΦ, hΓ, .union_mk _ args => Args.level_ge hΦ hΓ args
  | _, _, _, _, _, _, _, hΦ, hΓ, .array_mk es => Elems.level_ge hΦ hΓ es
  | _, _, _, _, _, _, _, hΦ, hΓ, .list_mk es => Elems.level_ge hΦ hΓ es
  | _, _, _, _, _, _, _, hΦ, hΓ, .data_in _ _ e => PExpr.level_ge hΦ hΓ e
  termination_by structural _ _ _ _ _ _ _ _ _ x => x
theorem Body.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → {L : Nat} → L ≤ d → KCtx.Ge L Φ → UCtx.Ge L Γ → UCtx.Ge L bs →
    Body Δ d Φ Γ bs τ o → Lvl.Ge L o
  | _, _, _, _, _, _, _, _, _, _, _, .closed _ => trivial
  | _, _, _, bs, _, _, _, hL, hΦ, hΓ, hbs, .opened t _ =>
      Term.level_ge (Nat.le_succ_of_le hL) hΦ (UCtx.Ge.append bs hbs hΓ) t
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ x => x
theorem Comp.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    {L : Nat} → L ≤ d → KCtx.Ge L Φ → UCtx.Ge L Γ → Comp Δ d Φ Γ τ ℓ → L ≤ ℓ
  | _, _, _, _, _, _, _, hΦ, hΓ, .app f a h =>
      Lvl.Ge.of_eq_some h (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ f) (PExpr.level_ge hΦ hΓ a))
  | _, _, _, _, _, _, _, hΦ, hΓ, .share n => Neu.level_ge hΦ hΓ n
  | _, _, _, _, _, _, hL, hΦ, hΓ, .nat_rec n z s h =>
      Lvl.Ge.of_eq_some h (Lvl.Ge.meet
        (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ n) (PExpr.level_ge hΦ hΓ z))
        (Body.level_ge hL hΦ hΓ (UCtx.Ge.cons _ (Nat.le_succ_of_le hL)
          (UCtx.Ge.cons _ (Nat.le_succ_of_le hL) (UCtx.Ge.nil _))) s))
  | _, _, _, _, _, _, hL, hΦ, hΓ, .array_foldl a z s h =>
      Lvl.Ge.of_eq_some h (Lvl.Ge.meet
        (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ a) (PExpr.level_ge hΦ hΓ z))
        (Body.level_ge hL hΦ hΓ (UCtx.Ge.cons _ (Nat.le_succ_of_le hL)
          (UCtx.Ge.cons _ (Nat.le_succ_of_le hL) (UCtx.Ge.nil _))) s))
  | _, _, _, _, _, _, hL, hΦ, hΓ, .data_rec _ _ _ brs _ e h =>
      Lvl.Ge.of_eq_some h (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ e)
        (Lvl.Ge.meetFin _ (fun i => Body.level_ge hL hΦ hΓ
          (UCtx.Ge.cons _ (Nat.le_succ_of_le hL) (UCtx.Ge.nil _)) (brs i))))
  | _, _, _, _, _, _, hL, hΦ, hΓ, .data_brec _ _ _ _ brs _ e h =>
      Lvl.Ge.of_eq_some h (Lvl.Ge.meet (PExpr.level_ge hΦ hΓ e)
        (Lvl.Ge.meetFin _ (fun i => Body.level_ge hL hΦ hΓ
          (UCtx.Ge.cons _ (Nat.le_succ_of_le hL) (UCtx.Ge.nil _)) (brs i))))
  | _, _, _, _, _, _, _, hΦ, hΓ, .thunk_force e => PExpr.level_ge hΦ hΓ e
  | _, _, _, _, _, _, _, hΦ, hΓ, .lazy_force e => PExpr.level_ge hΦ hΓ e
  termination_by structural _ _ _ _ _ _ _ _ _ x => x
theorem Term.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → {L : Nat} → L ≤ d → KCtx.Ge L Φ → UCtx.Ge L Γ →
    Term Δ d Φ Γ τ js o → Lvl.Ge L o
  | _, _, _, _, _, _, _, _, hΦ, hΓ, .ret e => PExpr.level_ge hΦ hΓ e
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .letV _ v b =>
      have hv := Val.level_ge hL hΦ hΓ v
      Lvl.Ge.meet hv (Term.level_ge hL (KCtx.Ge.cons _ hv hΦ) hΓ b)
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .letE _ c b =>
      Lvl.Ge.meetL (Comp.level_ge hL hΦ hΓ c) (Term.level_ge hL hΦ (UCtx.Ge.cons _ hL hΓ) b)
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .record_casesOn us n b =>
      Lvl.Ge.meetL (Neu.level_ge hΦ hΓ n)
        (Term.level_ge hL hΦ (UCtx.Ge.append _ (UCtx.Ge.annot hL _ us) hΓ) b)
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .branch br => Branch.level_ge hL hΦ hΓ br
  | _, _, _, _, _, _, _, _, hΦ, hΓ, .jump _ e => PExpr.level_ge hΦ hΓ e
  termination_by structural _ _ _ _ _ _ _ _ _ _ x => x
theorem Branch.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → {L : Nat} → L ≤ d → KCtx.Ge L Φ → UCtx.Ge L Γ →
    Branch Δ d Φ Γ τ js ℓ → L ≤ ℓ
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .ite c t e =>
      Lvl.Ge.meetL (Neu.level_ge hΦ hΓ c)
        (Lvl.Ge.meet (Term.level_ge hL hΦ hΓ t) (Term.level_ge hL hΦ hΓ e))
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .enum_casesOn e bs =>
      Lvl.Ge.meetL (Neu.level_ge hΦ hΓ e)
        (Lvl.Ge.meetFin _ (fun i => Term.level_ge hL hΦ hΓ (bs i)))
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .union_casesOn e bs =>
      Lvl.Ge.meetL (Neu.level_ge hΦ hΓ e) (Branches.level_ge hL hΦ hΓ bs)
  | _, _, _, _, _, _, _, hL, hΦ, hΓ, .join _ _ _ body main =>
      Lvl.Ge.meetL (Branch.level_ge hL hΦ hΓ main)
        (Term.level_ge hL hΦ (UCtx.Ge.cons _ hL hΓ) body)
  termination_by structural _ _ _ _ _ _ _ _ _ _ x => x
theorem Branches.level_ge : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → {L : Nat} → L ≤ d →
    KCtx.Ge L Φ → UCtx.Ge L Γ → Branches Δ d Φ Γ cs τ js o → Lvl.Ge L o
  | _, _, _, _, _, _, _, _, _, hL, hΦ, hΓ, .two us₁ us₂ b₁ b₂ =>
      Lvl.Ge.meet (Term.level_ge hL hΦ (UCtx.Ge.append _ (UCtx.Ge.annot hL _ us₁) hΓ) b₁)
        (Term.level_ge hL hΦ (UCtx.Ge.append _ (UCtx.Ge.annot hL _ us₂) hΓ) b₂)
  | _, _, _, _, _, _, _, _, _, hL, hΦ, hΓ, .cons us b bs =>
      Lvl.Ge.meet (Term.level_ge hL hΦ (UCtx.Ge.append _ (UCtx.Ge.annot hL _ us) hΓ) b)
        (Branches.level_ge hL hΦ hΓ bs)
  termination_by structural _ _ _ _ _ _ _ _ _ _ _ _ x => x
end

/-- **Open bodies are exact**: a body at depth `d` in which nothing bound outside of it is
    visible (every unknown and known value in scope, and its own parameters, are at level
    `d + 1` or deeper) is closed.  So `Body.opened` can only be used for a body that mentions
    an unknown or an open known value bound outside of it. -/
theorem Body.closed_of_ge {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (hΦ : KCtx.Ge (d + 1) Φ) (hΓ : UCtx.Ge (d + 1) Γ) (hbs : UCtx.Ge (d + 1) bs) :
    Body Δ d Φ Γ bs τ o → o = none
  | .closed _ => rfl
  | .opened t h =>
      absurd h (Nat.not_le.mpr (Term.level_ge (Nat.le_refl _) hΦ (UCtx.Ge.append bs hbs hΓ) t))

/-! ## A statement with nothing unknown is a value -/

/-- No usable known value is open. -/
def KCtx.Closed (Φ : KCtx ks) : Prop := ∀ (τ : Ty ks) (ℓ : Nat), KVar Φ τ (some ℓ) → False

theorem KCtx.Closed.nil : KCtx.Closed ([] : KCtx ks) := fun _ _ x => nomatch x

theorem KCtx.Closed.cons {Φ : KCtx ks} {σ : Ty ks} {u : Usage1ω} {v : Bool} (h : KCtx.Closed Φ) :
    KCtx.Closed (⟨σ, u, none, v⟩ :: Φ) := fun
  | _, _, .tail x => h _ _ x

/-- The known values seen from a closed body are closed. -/
theorem KCtx.Closed.closedOnly (Φ : KCtx ks) : KCtx.Closed (KCtx.closedOnly Φ) :=
  fun _ _ x => nomatch x.closedOnly_closed

theorem KCtx.Closed.ofAllClosed {Φ : KCtx ks} (h : KCtx.AllClosed Φ) : KCtx.Closed Φ :=
  fun _ _ x => nomatch x.allClosed h

theorem KVar.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} :
    {o : Lvl} → KVar Φ τ o → o = none
  | none, _ => rfl
  | some _, x => (hΦ _ _ x).elim

/-- Closed known values are at every level. -/
theorem KCtx.Closed.ge {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) (L : Nat) : KCtx.Ge L Φ := fun x => by
  rw [x.closed hΦ]; trivial

mutual
/-- There is no neutral expression without an unknown. -/
theorem Neu.not_closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) :
    {τ : Ty ks} → {ℓ : Nat} → Neu Δ Φ [] τ ℓ → False
  | _, _, .var x => nomatch x
  | _, _, .data_out _ _ n => Neu.not_closed hΦ n
  | _, _, .cond c _ _ => Neu.not_closed hΦ c
  | _, _, .extern _ args h => by rw [Args.closed hΦ args] at h; exact nomatch h
/-- A pure expression without an unknown is closed. -/
theorem PExpr.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) :
    {τ : Ty ks} → {o : Lvl} → PExpr Δ Φ [] τ o → o = none
  | _, _, .neu n => (Neu.not_closed hΦ n).elim
  | _, _, .kvar k => k.closed hΦ
  | _, _, .lit _ _ => rfl
  | _, _, .enum_mk _ _ => rfl
  | _, _, .record_mk args => Args.closed hΦ args
  | _, _, .union_mk _ args => Args.closed hΦ args
  | _, _, .array_mk es => Elems.closed hΦ es
  | _, _, .list_mk es => Elems.closed hΦ es
  | _, _, .data_in _ _ e => PExpr.closed hΦ e
/-- Arguments without an unknown are closed. -/
theorem Args.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) :
    {σs : List (Ty ks)} → {o : Lvl} → Args Δ Φ [] σs o → o = none
  | _, _, .nil => rfl
  | _, _, .cons a as => by rw [PExpr.closed hΦ a, Args.closed hΦ as]; rfl
/-- Elements without an unknown are closed. -/
theorem Elems.closed {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) :
    {t : Ty ks} → {o : Lvl} → Elems Δ Φ [] t o → o = none
  | _, _, .nil => rfl
  | _, _, .cons e es => by rw [PExpr.closed hΦ e, Elems.closed hΦ es]; rfl
end

/-- A body without an unknown in scope, whose known values are closed, is closed. -/
theorem Body.closed_eq {d : Nat} {Φ : KCtx ks} {bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (hΦ : KCtx.Closed Φ) (hbs : UCtx.Ge (d + 1) bs) (b : Body Δ d Φ [] bs τ o) : o = none :=
  b.closed_of_ge (hΦ.ge _) (UCtx.Ge.nil _) hbs

/-- The parameters of the bodies of values and computations at depth `d` are at level
    `d + 1`. -/
theorem UCtx.Ge.params1 (d : Nat) (σ : Ty ks) (u : Usage01ω) :
    UCtx.Ge (d + 1) ([⟨σ, u, d + 1⟩] : UCtx ks) :=
  UCtx.Ge.cons _ (Nat.le_refl _) (UCtx.Ge.nil _)

theorem UCtx.Ge.params2 (d : Nat) (σ₁ σ₂ : Ty ks) (u₁ u₂ : Usage01ω) :
    UCtx.Ge (d + 1) ([⟨σ₁, u₁, d + 1⟩, ⟨σ₂, u₂, d + 1⟩] : UCtx ks) :=
  UCtx.Ge.cons _ (Nat.le_refl _) (UCtx.Ge.params1 d σ₂ u₂)

/-- A value without an unknown is closed. -/
theorem Val.closed {d : Nat} {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} {o : Lvl} :
    Val Δ d Φ [] τ o → o = none
  | .lam b => b.closed_eq hΦ (UCtx.Ge.params1 _ _ _)
  | .thunk_mk b => b.closed_eq hΦ (UCtx.Ge.nil _)
  | .lazy_mk b => b.closed_eq hΦ (UCtx.Ge.nil _)
  | .record_mk args => Args.closed hΦ args
  | .union_mk _ args => Args.closed hΦ args
  | .array_mk es => Elems.closed hΦ es
  | .list_mk es => Elems.closed hΦ es
  | .data_in _ _ e => PExpr.closed hΦ e

/-- There is no computation without an unknown. -/
theorem Comp.not_closed {d : Nat} {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ [] τ ℓ → False
  | .app f a h => by
      rw [PExpr.closed hΦ f, PExpr.closed hΦ a] at h; exact nomatch h
  | .share n => Neu.not_closed hΦ n
  | .nat_rec n z s h => by
      rw [PExpr.closed hΦ n, PExpr.closed hΦ z, s.closed_eq hΦ (UCtx.Ge.params2 _ _ _ _ _)] at h
      exact nomatch h
  | .array_foldl a z s h => by
      rw [PExpr.closed hΦ a, PExpr.closed hΦ z, s.closed_eq hΦ (UCtx.Ge.params2 _ _ _ _ _)] at h
      exact nomatch h
  | .data_rec (os := os) _ _ _ brs _ e h => by
      have hos : os = fun _ => none :=
        funext fun i => (brs i).closed_eq hΦ (UCtx.Ge.params1 _ _ _)
      rw [PExpr.closed hΦ e, hos, Lvl.meetFin_none] at h; exact nomatch h
  | .data_brec (os := os) _ _ _ _ brs _ e h => by
      have hos : os = fun _ => none :=
        funext fun i => (brs i).closed_eq hΦ (UCtx.Ge.params1 _ _ _)
      rw [PExpr.closed hΦ e, hos, Lvl.meetFin_none] at h; exact nomatch h
  | .thunk_force e => nomatch PExpr.closed hΦ e
  | .lazy_force e => nomatch PExpr.closed hΦ e

/-- There is no branch without an unknown. -/
theorem Branch.not_closed {d : Nat} {Φ : KCtx ks} (hΦ : KCtx.Closed Φ) {τ : Ty ks} :
    {js : JCtx ks} → {ℓ : Nat} → Branch Δ d Φ [] τ js ℓ → False
  | _, _, .ite c _ _ => Neu.not_closed hΦ c
  | _, _, .enum_casesOn e _ => Neu.not_closed hΦ e
  | _, _, .union_casesOn e _ => Neu.not_closed hΦ e
  | _, _, .join _ _ _ _ main => Branch.not_closed hΦ main

/-- **A value**: a chain of `letV`s of closed values ending in the answer, a closed pure
    expression. -/
inductive Term.IsValue : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → Term Δ d Φ Γ τ js o → Prop where
  | ret {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
      (e : PExpr Δ Φ Γ τ o) : o = none → Term.IsValue (.ret (d := d) (js := js) e)
  | letV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
      (u : Usage1ω) (v : Val Δ d Φ Γ σ o) {b : Term Δ d (⟨σ, u, o, true⟩ :: Φ) Γ τ js o'} :
      o = none → Term.IsValue b → Term.IsValue (.letV u v b)

theorem Term.closed_isValue_aux {τ : Ty ks} :
    {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {js : JCtx ks} → {o : Lvl} → KCtx.Closed Φ →
      Γ = [] → js = [] → (t : Term Δ d Φ Γ τ js o) → t.IsValue
  | _, _, _, _, _, hΦ, hΓ, _, .ret e => .ret e (by subst hΓ; exact PExpr.closed hΦ e)
  | _, _, _, _, _, hΦ, hΓ, hjs, .letV (o := o) u v b =>
      have h : o = none := by subst hΓ; exact Val.closed hΦ v
      .letV u v h (Term.closed_isValue_aux (h ▸ KCtx.Closed.cons hΦ) hΓ hjs b)
  | _, _, _, _, _, hΦ, hΓ, _, .letE _ c _ => by subst hΓ; exact (Comp.not_closed hΦ c).elim
  | _, _, _, _, _, hΦ, hΓ, _, .record_casesOn _ n _ => by
      subst hΓ; exact (Neu.not_closed hΦ n).elim
  | _, _, _, _, _, hΦ, hΓ, _, .branch br => by subst hΓ; exact (Branch.not_closed hΦ br).elim
  | _, _, _, _, _, _, _, hjs, .jump j _ => by subst hjs; exact nomatch j
  termination_by _ _ _ _ _ _ _ _ t => sizeOf t
  decreasing_by simp_wf; omega

/-- **A statement with no unknown and no open known value is a value**: nothing is left to
    compute. -/
theorem Term.closed_isValue {d : Nat} {τ : Ty ks} {Φ : KCtx ks} {o : Lvl} (hΦ : KCtx.Closed Φ)
    (t : Term Δ d Φ [] τ [] o) : t.IsValue :=
  Term.closed_isValue_aux hΦ rfl rfl t

/-- A whole program is a value. -/
theorem Term.run_isValue {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) : t.IsValue :=
  t.closed_isValue KCtx.Closed.nil

/-- The body of a closed delay (a closed body with no parameter) is a value. -/
theorem Term.closedBody_isValue {d : Nat} {Φ : KCtx ks} {τ : Ty ks} {o : Lvl}
    (t : Term Δ d (KCtx.closedOnly Φ) [] τ [] o) : t.IsValue :=
  t.closed_isValue (KCtx.Closed.closedOnly Φ)

end LeanScript

end
