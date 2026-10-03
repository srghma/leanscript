module

public import LeanScript.Term.Optimize.FieldsWalk
public import LeanScript.Term.Optimize.Cond
public import LeanScript.Term.Optimize.CountDce
public import LeanScript.Term.Optimize.Atom

@[expose] public section

set_option autoImplicit false

/-!
# Tests whose answer is already known

`if c then (if c then X else Y) else (if c then Z else W)`: inside an arm of `if c` the value of
`c` is known, so the inner tests can be dropped, and the statement is
`if c then X else W`.  Lean writes such repeated tests when a condition is read again after an
`if` on it: `let r := { c := c, d := x }; if r.c then (if r.c then x else 0) else …`
(`Tests/SnapshotsMy/IfThenElseKnownField.lean`, the variants of
`Tests/SnapshotsPBOPure/InlineReferenceIfThenElse.lean`).

`Term.knownTestWalk facts t` walks a statement knowing, for some boolean unknowns, their value
(`BoolFact`: an unknown `x : UVar Γ .bool ℓ` and a boolean).  At `if c then t else e`:

* when `c` is a known unknown (or the negation `!x` of one, `Neu.negView?`), the `if` is replaced
  by the arm it takes (`Term.knownTestWalk` answers a statement of *another* level: the walk
  returns the level with the statement);
* otherwise `t` is walked knowing that `c` holds, and `e` knowing that it does not
  (`BoolFact.extend`).

The conditional answer `ret (c ? a : b)` on a known `c` is the answer `ret a` (or `ret b`).  The
facts are weakened under binders (`BoolFact.weaken`, `BoolFact.weakenN`), carried into open
bodies (whose environment extends the one where the facts hold) and dropped in closed bodies.  A
body or a value must keep its level (it is recorded in the known context, or in the side
conditions of a computation): when the walked body has another level, the original body is kept.

**Proved:** `Term.knownTests_eval` (the value does not change) and `Term.numCalls_knownTests` (no
call is added: an arm is dropped, nothing is copied).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Facts -/

/-- A boolean unknown whose value is known. -/
structure BoolFact (Γ : UCtx ks) where
  lv : Nat
  x : UVar Γ .bool lv
  val : Bool

namespace BoolFact

variable {Γ : UCtx ks}

/-- The fact holds in an environment. -/
def Holds (f : BoolFact Γ) (ρ : UEnv Δ Γ) : Prop := (ρ.get f.x : Bool) = f.val

/-- Under one more binder. -/
def weaken (b : UBinder ks) (f : BoolFact Γ) : BoolFact (b :: Γ) := ⟨f.lv, .tail f.x, f.val⟩

/-- Under the binders `bs`. -/
def weakenN (bs : UCtx ks) (f : BoolFact Γ) : BoolFact (bs ++ Γ) :=
  ⟨f.lv, UVar.weakenN bs f.x, f.val⟩

/-- The value of an unknown, if a fact gives it. -/
def find? : List (BoolFact Γ) → {ℓ : Nat} → UVar Γ .bool ℓ → Option Bool
  | [], _, _ => none
  | f :: fs, _, y => if f.x.index = y.index then some f.val else find? fs y

theorem map_weaken_holds {b : UBinder ks} (v : Ty.Den Δ b.ty) {ρ : UEnv Δ Γ}
    {facts : List (BoolFact Γ)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (BoolFact.weaken b), f.Holds (Tuple.cons v ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  have := h g hg
  simp only [Holds, weaken] at this ⊢
  simpa using this

theorem map_weakenN_holds (bs : UCtx ks) (vs : UEnv Δ bs) {ρ : UEnv Δ Γ}
    {facts : List (BoolFact Γ)} (h : ∀ f ∈ facts, f.Holds ρ) :
    ∀ f ∈ facts.map (BoolFact.weakenN bs), f.Holds (Tuple.append vs ρ) := by
  intro f hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  have := h g hg
  simp only [Holds, weakenN] at this ⊢
  rw [UEnv.get_weakenN]; exact this

theorem find?_holds {ρ : UEnv Δ Γ} : (facts : List (BoolFact Γ)) → (∀ f ∈ facts, f.Holds ρ) →
    {ℓ : Nat} → (y : UVar Γ .bool ℓ) → (b : Bool) → find? facts y = some b →
    (ρ.get y : Bool) = b
  | [], _, _, _, _, hb => by simp [find?] at hb
  | f :: fs, h, _, y, b, hb => by
      simp only [find?] at hb
      split at hb
      · rename_i hi
        cases hb
        have ⟨_, hx⟩ := UVar.eq_of_index_eq (Δ := Δ) f.x y hi
        have := h f (List.mem_cons_self ..)
        simp only [Holds] at this
        rw [← this]; exact (eq_of_heq (hx ρ)).symm
      · exact find?_holds fs (fun g hg => h g (List.mem_cons_of_mem _ hg)) y b hb

end BoolFact

section Cond
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The unknown a neutral expression is, if it is one. -/
def Neu.uvar? {τ : Ty ks} {ℓ : Nat} : Neu Δ Φ Γ τ ℓ → Option (UVar Γ τ ℓ)
  | .var x => some x
  | _ => none

theorem Neu.uvar?_eval {τ : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ τ ℓ) (x : UVar Γ τ ℓ)
    (h : n.uvar? = some x) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : n.eval κ ρ = ρ.get x := by
  cases n with
  | var y => simp only [Neu.uvar?, Option.some.injEq] at h; subst h; rfl
  | _ => simp [Neu.uvar?] at h

/-- The condition as an unknown and a polarity: `x` (`true`) or `!x` (`false`). -/
def Neu.boolVar? {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) : Option (UVar Γ .bool ℓ × Bool) :=
  match c.uvar? with
  | some x => some (x, true)
  | none =>
    match c.negView? with
    | some c' => c'.uvar?.map fun x => (x, false)
    | none => none

theorem Neu.boolVar?_eval {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) (x : UVar Γ .bool ℓ) (p : Bool)
    (h : c.boolVar? = some (x, p)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (c.eval κ ρ : Bool) = (if p then (ρ.get x : Bool) else !(ρ.get x : Bool)) := by
  unfold Neu.boolVar? at h
  split at h
  · rename_i y hy
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Neu.uvar?_eval c _ hy κ ρ]
  · split at h
    · rename_i c' hc'
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨y, hy, rfl, rfl⟩ := h
      rw [Neu.negView?_eval c c' hc' κ ρ, Neu.uvar?_eval c' _ hy κ ρ]
      rfl
    · cases h

/-- The value of a condition, when the facts give it. -/
def Neu.knownBool? {ℓ : Nat} (facts : List (BoolFact Γ)) (c : Neu Δ Φ Γ .bool ℓ) :
    Option Bool :=
  match c.boolVar? with
  | some (x, p) => (BoolFact.find? facts x).map fun v => if p then v else !v
  | none => none

theorem Neu.knownBool?_eval {ℓ : Nat} (facts : List (BoolFact Γ)) (c : Neu Δ Φ Γ .bool ℓ)
    (b : Bool) (h : c.knownBool? facts = some b) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (hf : ∀ f ∈ facts, f.Holds ρ) : (c.eval κ ρ : Bool) = b := by
  unfold Neu.knownBool? at h
  split at h
  · rename_i x p hx
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    rw [Neu.boolVar?_eval c x p hx κ ρ, BoolFact.find?_holds facts hf x v hv]
    rfl
  · cases h

/-- The facts known in an arm of `if c`: `c` has the value `b`. -/
def BoolFact.extend {ℓ : Nat} (facts : List (BoolFact Γ)) (c : Neu Δ Φ Γ .bool ℓ) (b : Bool) :
    List (BoolFact Γ) :=
  match c.boolVar? with
  | some (x, p) => ⟨_, x, if p then b else !b⟩ :: facts
  | none => facts

theorem BoolFact.extend_holds {ℓ : Nat} (facts : List (BoolFact Γ)) (c : Neu Δ Φ Γ .bool ℓ)
    (b : Bool) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (hf : ∀ f ∈ facts, f.Holds ρ)
    (hc : (c.eval κ ρ : Bool) = b) : ∀ f ∈ BoolFact.extend facts c b, f.Holds ρ := by
  unfold BoolFact.extend
  split
  · rename_i x p hx
    intro f hf'
    rcases List.mem_cons.1 hf' with rfl | hf'
    · have := Neu.boolVar?_eval c x p hx κ ρ
      rw [hc] at this
      simp only [BoolFact.Holds]
      obtain ⟨v, hv⟩ : ∃ v : Bool, ρ.get x = v := ⟨_, rfl⟩
      rw [hv] at this ⊢
      subst this
      cases p <;> cases v <;> rfl
    · exact hf f hf'
  · exact hf

/-- A conditional `c ? a : b` on a known `c` is `a` (or `b`); returned with its level. -/
def Neu.knownCond {τ : Ty ks} {ℓ : Nat} (facts : List (BoolFact Γ)) :
    Neu Δ Φ Γ τ ℓ → (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | .cond c a b => match c.knownBool? facts with
    | some true => ⟨_, a⟩
    | some false => ⟨_, b⟩
    | none => ⟨_, .neu (.cond c a b)⟩
  | n => ⟨_, .neu n⟩

theorem Neu.knownCond_eval {τ : Ty ks} {ℓ : Nat} (facts : List (BoolFact Γ))
    (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (hf : ∀ f ∈ facts, f.Holds ρ) :
    (n.knownCond facts).2.eval κ ρ = n.eval κ ρ := by
  cases n with
  | cond c a b =>
    simp only [Neu.knownCond]
    split
    · rename_i h
      simp only [Neu.eval, Neu.knownBool?_eval facts c true h κ ρ hf]
    · rename_i h
      simp only [Neu.eval, Neu.knownBool?_eval facts c false h κ ρ hf]
    · rfl
  | _ => rfl

/-- The answer `ret e`, where `e` is a conditional `c ? a : b` on a known `c`, is the answer
    `ret a` (or `ret b`); returned with its level. -/
def PExpr.knownCond {τ : Ty ks} {o : Lvl} (facts : List (BoolFact Γ)) :
    PExpr Δ Φ Γ τ o → (o' : Lvl) × PExpr Δ Φ Γ τ o'
  | .neu n => n.knownCond facts
  | e => ⟨_, e⟩

theorem PExpr.knownCond_eval {τ : Ty ks} {o : Lvl} (facts : List (BoolFact Γ))
    (e : PExpr Δ Φ Γ τ o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (hf : ∀ f ∈ facts, f.Holds ρ) :
    (e.knownCond facts).2.eval κ ρ = e.eval κ ρ := by
  cases e with
  | neu n => exact Neu.knownCond_eval facts n κ ρ hf
  | _ => rfl

end Cond

/-! ## The walk -/

mutual
/-- `Term.knownTestWalk` inside the bodies of a value (the value keeps its level). -/
def Val.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    List (BoolFact Γ) → Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, facts, .lam b => .lam (b.knownTestWalk facts)
  | _, _, _, _, _, facts, .thunk_mk b => .thunk_mk (b.knownTestWalk facts)
  | _, _, _, _, _, facts, .lazy_mk b => .lazy_mk (b.knownTestWalk facts)
  | _, _, _, _, _, _, .record_mk args => .record_mk args
  | _, _, _, _, _, _, .union_mk ix args => .union_mk ix args
  | _, _, _, _, _, _, .array_mk es => .array_mk es
  | _, _, _, _, _, _, .list_mk es => .list_mk es
  | _, _, _, _, _, _, .data_in b j e => .data_in b j e
/-- `Term.knownTestWalk` in a body: a closed body starts with no fact, an open one with the
    facts of its context; an open body keeps its level (or is kept as it is). -/
def Body.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → List (BoolFact Γ) → Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, _, .closed t => .closed (t.knownTestWalk []).2
  | _, _, _, bs, _, _, facts, .opened (m := m) t h =>
      let r := t.knownTestWalk (facts.map (BoolFact.weakenN bs))
      if hr : r.1 = some m then .opened (r.2.castLvl hr) h else .opened t h
/-- `Term.knownTestWalk` inside the bodies of a computation. -/
def Comp.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    List (BoolFact Γ) → Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, _, .app f a h => .app f a h
  | _, _, _, _, _, _, .share n => .share n
  | _, _, _, _, _, facts, .nat_rec n z s h => .nat_rec n z (s.knownTestWalk facts) h
  | _, _, _, _, _, facts, .array_foldl a z s h => .array_foldl a z (s.knownTestWalk facts) h
  | _, _, _, _, _, facts, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).knownTestWalk facts) j e h
  | _, _, _, _, _, facts, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).knownTestWalk facts) j e h
  | _, _, _, _, _, _, .thunk_force e => .thunk_force e
  | _, _, _, _, _, _, .lazy_force e => .lazy_force e
/-- **Known tests**: walk a statement knowing the values of some boolean unknowns; an `if` on a
    known condition is replaced by the arm it takes, and the arms of any other `if` on an
    unknown know its value.  The result may have another level, and is returned with it. -/
def Term.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → List (BoolFact Γ) → Term Δ d Φ Γ τ js o →
    (o' : Lvl) × Term Δ d Φ Γ τ js o'
  | _, _, _, _, _, _, facts, .ret e => ⟨_, .ret (e.knownCond facts).2⟩
  | _, _, _, _, _, _, facts, .letV u v b =>
      ⟨_, .letV u (v.knownTestWalk facts) (b.knownTestWalk facts).2⟩
  | _, _, _, _, _, _, facts, .letE u c b =>
      ⟨_, .letE u (c.knownTestWalk facts)
        (b.knownTestWalk (facts.map (BoolFact.weaken _))).2⟩
  | _, _, _, _, _, _, facts, .record_casesOn us n b =>
      ⟨_, .record_casesOn us n (b.knownTestWalk (facts.map (BoolFact.weakenN _))).2⟩
  | _, _, _, _, _, _, facts, .branch (.ite c t e) =>
      match c.knownBool? facts with
      | some true => t.knownTestWalk facts
      | some false => e.knownTestWalk facts
      | none => ⟨_, .branch (.ite c (t.knownTestWalk (BoolFact.extend facts c true)).2
          (e.knownTestWalk (BoolFact.extend facts c false)).2)⟩
  | _, _, _, _, _, _, facts, .branch (.enum_casesOn e bs) =>
      ⟨_, .branch (.enum_casesOn e (fun i => ((bs i).knownTestWalk facts).2))⟩
  | _, _, _, _, _, _, facts, .branch (.union_casesOn e bs) =>
      ⟨_, .branch (.union_casesOn e (bs.knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, facts, .branch (.join σ u uₓ body main) =>
      ⟨_, .branch (.join σ u uₓ (body.knownTestWalk (facts.map (BoolFact.weaken _))).2
        (main.knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, _, .jump j e => ⟨_, .jump j e⟩
/-- `Term.knownTestWalk` in a branch that must stay a branch (the main part of a join point):
    no `if` is dropped at its head. -/
def Branch.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → List (BoolFact Γ) → Branch Δ d Φ Γ τ js ℓ →
    (ℓ' : Nat) × Branch Δ d Φ Γ τ js ℓ'
  | _, _, _, _, _, _, facts, .ite c t e =>
      ⟨_, .ite c (t.knownTestWalk (BoolFact.extend facts c true)).2
        (e.knownTestWalk (BoolFact.extend facts c false)).2⟩
  | _, _, _, _, _, _, facts, .enum_casesOn e bs =>
      ⟨_, .enum_casesOn e (fun i => ((bs i).knownTestWalk facts).2)⟩
  | _, _, _, _, _, _, facts, .union_casesOn e bs => ⟨_, .union_casesOn e (bs.knownTestWalk facts).2⟩
  | _, _, _, _, _, _, facts, .join σ u uₓ body main =>
      ⟨_, .join σ u uₓ (body.knownTestWalk (facts.map (BoolFact.weaken _))).2
        (main.knownTestWalk facts).2⟩
/-- `Term.knownTestWalk` in the branches of a union's case analysis. -/
def Branches.knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → List (BoolFact Γ) →
    Branches Δ d Φ Γ cs τ js o → (o' : Lvl) × Branches Δ d Φ Γ cs τ js o'
  | _, _, _, _, _, _, _, _, facts, .two us₁ us₂ b₁ b₂ =>
      ⟨_, .two us₁ us₂ (b₁.knownTestWalk (facts.map (BoolFact.weakenN _))).2
        (b₂.knownTestWalk (facts.map (BoolFact.weakenN _))).2⟩
  | _, _, _, _, _, _, _, _, facts, .cons us b bs =>
      ⟨_, .cons us (b.knownTestWalk (facts.map (BoolFact.weakenN _))).2
        (bs.knownTestWalk facts).2⟩
end

/-! ## The value does not change -/

mutual
theorem Val.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) → (v.knownTestWalk facts).eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; funext x
      rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .thunk_mk b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .lazy_mk b, facts, κ, ρ, h => by
      simp only [Val.knownTestWalk, Val.eval]; rw [Body.knownTestWalk_eval b facts κ ρ _ h]
  | _, _, _, _, _, .record_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .union_mk _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .array_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .list_mk _, _, _, _, _ => rfl
  | _, _, _, _, _, .data_in _ _ _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Body.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (∀ f ∈ facts, f.Holds ρ) →
    (b.knownTestWalk facts).eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _, _, _ => by
      simp only [Body.knownTestWalk, Body.eval]
      exact Term.knownTestWalk_eval t [] _ _ _ (fun _ h => nomatch h)
  | _, _, _, _, _, _, .opened t _, facts, κ, ρ, vs, h => by
      simp only [Body.knownTestWalk]
      split
      · simp only [Body.eval]
        exact (Term.eval_castLvl _ _ _ _ _).trans
          (Term.knownTestWalk_eval t _ _ _ _ (BoolFact.map_weakenN_holds _ vs h))
      · rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Comp.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (∀ f ∈ facts, f.Holds ρ) → (c.knownTestWalk facts).eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app _ _ _, _, _, _, _ => rfl
  | _, _, _, _, _, .share _, _, _, _, _ => rfl
  | _, _, _, _, _, .nat_rec n z s _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext k acc; exact Body.knownTestWalk_eval s facts κ ρ _ h
  | _, _, _, _, _, .array_foldl a z s _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext acc x; exact Body.knownTestWalk_eval s facts κ ρ _ h
  | _, _, _, _, _, .data_rec b ρt us brs j e _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.knownTestWalk_eval (brs i) facts κ ρ _ h
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, facts, κ, ρ, h => by
      simp only [Comp.knownTestWalk, Comp.eval]
      congr 1; funext i x; exact Body.knownTestWalk_eval (brs i) facts κ ρ _ h
  | _, _, _, _, _, .thunk_force _, _, _, _, _ => rfl
  | _, _, _, _, _, .lazy_force _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ x _ _ _ _ => x
theorem Term.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (t.knownTestWalk facts).2.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, facts, κ, ρ, _, h => by
      simp only [Term.knownTestWalk, Term.eval]; exact PExpr.knownCond_eval facts e κ ρ h
  | _, _, _, _, _, _, .letV u v b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Val.knownTestWalk_eval v facts κ ρ h]
      exact Term.knownTestWalk_eval b facts _ ρ jκ h
  | _, _, _, _, _, _, .letE u c b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Comp.knownTestWalk_eval c facts κ ρ h]
      exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weaken_holds _ h)
  | _, _, _, _, _, _, .record_casesOn us n b, facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval]
      exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
  | _, _, _, _, _, _, .branch (.ite c t e), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk]
      split
      · rename_i hc
        rw [Term.knownTestWalk_eval t facts κ ρ jκ h]
        simp only [Term.eval, Branch.eval, Neu.knownBool?_eval facts c true hc κ ρ h]
      · rename_i hc
        rw [Term.knownTestWalk_eval e facts κ ρ jκ h]
        simp only [Term.eval, Branch.eval, Neu.knownBool?_eval facts c false hc κ ρ h]
      · simp only [Term.eval, Branch.eval]
        split
        · rename_i hv
          exact Term.knownTestWalk_eval t _ κ ρ jκ (BoolFact.extend_holds facts c true κ ρ h hv)
        · rename_i hv
          exact Term.knownTestWalk_eval e _ κ ρ jκ
            (BoolFact.extend_holds facts c false κ ρ h hv)
  | _, _, _, _, _, _, .branch (.enum_casesOn e bs), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Branch.eval]
      exact Term.knownTestWalk_eval _ facts κ ρ jκ h
  | _, _, _, _, _, _, .branch (.union_casesOn e bs), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Branch.eval]
      exact Branches.knownTestWalk_eval bs facts κ ρ jκ h _
  | _, _, _, _, _, _, .branch (.join σ u uₓ body main), facts, κ, ρ, jκ, h => by
      simp only [Term.knownTestWalk, Term.eval, Branch.eval,
        Branch.knownTestWalk_eval main facts κ ρ _ h]
      congr 2
      funext v
      exact Term.knownTestWalk_eval body _ κ _ jκ
        (BoolFact.map_weaken_holds (b := ⟨σ, uₓ, _⟩) v h)
  | _, _, _, _, _, _, .jump _ _, _, _, _, _, _ => rfl
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branch.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (facts : List (BoolFact Γ)) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
    (br.knownTestWalk facts).2.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval]
      split
      · rename_i hv
        exact Term.knownTestWalk_eval t _ κ ρ jκ (BoolFact.extend_holds facts c true κ ρ h hv)
      · rename_i hv
        exact Term.knownTestWalk_eval e _ κ ρ jκ (BoolFact.extend_holds facts c false κ ρ h hv)
  | _, _, _, _, _, _, .enum_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval]
      exact Term.knownTestWalk_eval _ facts κ ρ jκ h
  | _, _, _, _, _, _, .union_casesOn e bs, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval]
      exact Branches.knownTestWalk_eval bs facts κ ρ jκ h _
  | _, _, _, _, _, _, .join σ u uₓ body main, facts, κ, ρ, jκ, h => by
      simp only [Branch.knownTestWalk, Branch.eval, Branch.knownTestWalk_eval main facts κ ρ _ h]
      congr 2
      funext v
      exact Term.knownTestWalk_eval body _ κ _ jκ
        (BoolFact.map_weaken_holds (b := ⟨σ, uₓ, _⟩) v h)
  termination_by structural _ _ _ _ _ _ x _ _ _ _ _ => x
theorem Branches.knownTestWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (BoolFact Γ)) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → (∀ f ∈ facts, f.Holds ρ) →
      ∀ x, (br.knownTestWalk facts).2.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.knownTestWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.knownTestWalk_eval b₁ _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
      · funext v
        exact Term.knownTestWalk_eval b₂ _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
  | _, _, _, _, _, _, _, _, .cons us b bs, facts, κ, ρ, jκ, h, x => by
      simp only [Branches.knownTestWalk, Branches.eval]
      congr 1
      · funext v
        exact Term.knownTestWalk_eval b _ κ _ jκ (BoolFact.map_weakenN_holds _ _ h)
      · funext r
        exact Branches.knownTestWalk_eval bs facts κ ρ jκ h r
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (facts : List (BoolFact Γ)) →
    (v.knownTestWalk facts).numCalls ≤ v.numCalls
  | _, _, _, _, _, .lam b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .thunk_mk b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .lazy_mk b, facts => by
      simp only [Val.knownTestWalk, Val.numCalls]; exact Body.numCalls_knownTestWalk b facts
  | _, _, _, _, _, .record_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .union_mk _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .array_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .list_mk _, _ => Nat.le_refl _
  | _, _, _, _, _, .data_in _ _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Body.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} →
    {τ : Ty ks} → {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (facts : List (BoolFact Γ)) →
    (b.knownTestWalk facts).numCalls ≤ b.numCalls
  | _, _, _, _, _, _, .closed t, _ => by
      simp only [Body.knownTestWalk, Body.numCalls]; exact Term.numCalls_knownTestWalk t []
  | _, _, _, _, _, _, .opened t _, facts => by
      simp only [Body.knownTestWalk]
      split
      · simp only [Body.numCalls, Term.numCalls_castLvl]
        exact Term.numCalls_knownTestWalk t _
      · exact Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Comp.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (facts : List (BoolFact Γ)) →
    (c.knownTestWalk facts).numCalls ≤ c.numCalls
  | _, _, _, _, _, .app _ _ _, _ => Nat.le_refl _
  | _, _, _, _, _, .share _, _ => Nat.le_refl _
  | _, _, _, _, _, .nat_rec n z s _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]; exact Body.numCalls_knownTestWalk s facts
  | _, _, _, _, _, .array_foldl a z s _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]; exact Body.numCalls_knownTestWalk s facts
  | _, _, _, _, _, .data_rec b ρt us brs j e _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_knownTestWalk (brs i) facts)
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, facts => by
      simp only [Comp.knownTestWalk, Comp.numCalls]
      exact Fin.sumNat_le _ (fun i => Body.numCalls_knownTestWalk (brs i) facts)
  | _, _, _, _, _, .thunk_force _, _ => Nat.le_refl _
  | _, _, _, _, _, .lazy_force _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ x _ => x
theorem Term.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) →
    (facts : List (BoolFact Γ)) → (t.knownTestWalk facts).2.numCalls ≤ t.numCalls
  | _, _, _, _, _, _, .ret _, _ => Nat.le_refl _
  | _, _, _, _, _, _, .letV u v b, facts => by
      have h₁ := Val.numCalls_knownTestWalk v facts
      have h₂ := Term.numCalls_knownTestWalk b facts
      simp only [Term.knownTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .letE u c b, facts => by
      have h₁ := Comp.numCalls_knownTestWalk c facts
      have h₂ := Term.numCalls_knownTestWalk b (facts.map (BoolFact.weaken _))
      simp only [Term.knownTestWalk, Term.numCalls]; omega
  | _, _, _, _, _, _, .record_casesOn us n b, facts => by
      simp only [Term.knownTestWalk, Term.numCalls]
      exact Term.numCalls_knownTestWalk b _
  | _, _, _, _, _, _, .branch (.ite c t e), facts => by
      have h₁ := Term.numCalls_knownTestWalk t facts
      have h₂ := Term.numCalls_knownTestWalk e facts
      have h₃ := Term.numCalls_knownTestWalk t (BoolFact.extend facts c true)
      have h₄ := Term.numCalls_knownTestWalk e (BoolFact.extend facts c false)
      simp only [Term.knownTestWalk]
      split <;> simp only [Term.numCalls, Branch.numCalls] <;> omega
  | _, _, _, _, _, _, .branch (.enum_casesOn e bs), facts => by
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_knownTestWalk (bs i) facts)
  | _, _, _, _, _, _, .branch (.union_casesOn e bs), facts => by
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]
      exact Branches.numCalls_knownTestWalk bs facts
  | _, _, _, _, _, _, .branch (.join σ u uₓ body main), facts => by
      have h₁ := Term.numCalls_knownTestWalk body (facts.map (BoolFact.weaken _))
      have h₂ := Branch.numCalls_knownTestWalk main facts
      simp only [Term.knownTestWalk, Term.numCalls, Branch.numCalls]; omega
  | _, _, _, _, _, _, .jump _ _, _ => Nat.le_refl _
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branch.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {τ : Ty ks} → {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    (facts : List (BoolFact Γ)) → (br.knownTestWalk facts).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, .ite c t e, facts => by
      have h₁ := Term.numCalls_knownTestWalk t (BoolFact.extend facts c true)
      have h₂ := Term.numCalls_knownTestWalk e (BoolFact.extend facts c false)
      simp only [Branch.knownTestWalk, Branch.numCalls]; omega
  | _, _, _, _, _, _, .enum_casesOn e bs, facts => by
      simp only [Branch.knownTestWalk, Branch.numCalls]
      exact Fin.sumNat_le _ (fun i => Term.numCalls_knownTestWalk (bs i) facts)
  | _, _, _, _, _, _, .union_casesOn e bs, facts => by
      simp only [Branch.knownTestWalk, Branch.numCalls]
      exact Branches.numCalls_knownTestWalk bs facts
  | _, _, _, _, _, _, .join σ u uₓ body main, facts => by
      have h₁ := Term.numCalls_knownTestWalk body (facts.map (BoolFact.weaken _))
      have h₂ := Branch.numCalls_knownTestWalk main facts
      simp only [Branch.knownTestWalk, Branch.numCalls]; omega
  termination_by structural _ _ _ _ _ _ x _ => x
theorem Branches.numCalls_knownTestWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (facts : List (BoolFact Γ)) →
    (br.knownTestWalk facts).2.numCalls ≤ br.numCalls
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, facts => by
      have h₁ := Term.numCalls_knownTestWalk b₁ (facts.map (BoolFact.weakenN _))
      have h₂ := Term.numCalls_knownTestWalk b₂ (facts.map (BoolFact.weakenN _))
      simp only [Branches.knownTestWalk, Branches.numCalls]; omega
  | _, _, _, _, _, _, _, _, .cons us b bs, facts => by
      have h₁ := Term.numCalls_knownTestWalk b (facts.map (BoolFact.weakenN _))
      have h₂ := Branches.numCalls_knownTestWalk bs facts
      simp only [Branches.knownTestWalk, Branches.numCalls]; omega
  termination_by structural _ _ _ _ _ _ _ _ x _ => x
end

/-- **The known tests of a statement**, dropped (`Term.knownTestWalk` with no fact), when this
    keeps the level of the statement. -/
def Term.knownTests {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) : Term Δ d Φ Γ τ js o :=
  if h : (t.knownTestWalk []).1 = o then (t.knownTestWalk []).2.castLvl h else t

/-- **Dropping the known tests does not change the value.** -/
theorem Term.knownTests_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {o : Lvl} (t : Term Δ d Φ Γ τ js o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (jκ : JEnv Δ τ js) :
    t.knownTests.eval κ ρ jκ = t.eval κ ρ jκ := by
  unfold Term.knownTests
  split
  · rw [Term.eval_castLvl]
    exact Term.knownTestWalk_eval t [] κ ρ jκ (fun _ h => nomatch h)
  · rfl

/-- The same for a whole program. -/
theorem Term.knownTests_run {τ : Ty ks} {o : Lvl} (t : Term Δ 0 [] [] τ [] o) :
    t.knownTests.run = t.run :=
  t.knownTests_eval _ _ _

/-- **Dropping the known tests adds no call.** -/
theorem Term.numCalls_knownTests {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {o : Lvl} (t : Term Δ d Φ Γ τ js o) :
    t.knownTests.numCalls ≤ t.numCalls := by
  unfold Term.knownTests
  split
  · rw [Term.numCalls_castLvl]; exact Term.numCalls_knownTestWalk t []
  · exact Nat.le_refl _

end LeanScript

end
