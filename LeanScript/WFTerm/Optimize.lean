module

public import LeanScript.WFTerm.Eval
public import LeanScript.Term.Optimize.Basic

@[expose] public section

set_option autoImplicit false

/-!
# An optimiser for `WFTerm`

`WFTerm.optimize t` rewrites a statement into one with the same value (`WFTerm.optimize_eval`,
`WFProgram.optimize_run`), keeping its type: the same context, path condition, enclosing
function, postcondition and join points, so every proof obligation of the program (decrease
proofs included) is carried over to the optimised program.  The rewrites:

* **the call-free layer**: every atom is optimised by the proved-correct optimiser of `Term`
  (`Term.optimize`), in `ret`, `ite`, `jump`, call arguments, shared values and folds;
* **constant tests**: `if c then a else b`, where `c` is the literal `true` (resp. `false`) after
  optimisation, becomes `a` (resp. `b`);
* **a join point entered at once**: `join j (v) := body in jump j a` becomes
  `let v := a in body` (a jump whose join point is known is inlined);
* **folds of the empty list**: `map f []` becomes the literal `[]`, and `foldl f init []`
  becomes `init`.

The optimiser walks the statement like `WFTerm.eval` does.  It works *under a stronger path
condition*: `t.optimizeUnder h`, for `h : ∀ e, G₂ e → G e`, is a statement reached under `G₂`.
This is what lets a branch of a constant test, which was typed under `G ∧ c = true`, stand for
the whole test (under `G`), and what lets the continuation of a `let` be typed under the fact
established by the optimised computation.  `WFTerm.optimize` is the case `G₂ = G`.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Atoms -/

/-- An atom optimised by the optimiser of `Term`. -/
def WFAtom.optimize {Γ : WCtx ks} {τ : Ty ks} (a : WFAtom Δ Γ τ) : WFAtom Δ Γ τ :=
  ⟨a.term.optimize⟩

@[simp] theorem WFAtom.optimize_eval {Γ : WCtx ks} {τ : Ty ks} (a : WFAtom Δ Γ τ)
    (e : WEnv Δ Γ) : a.optimize.eval e = a.eval e :=
  Term.optimize_eval _ _ _ _

@[simp] theorem WFAtom.optimize_evalBool {Γ : WCtx ks} (a : WFAtom Δ Γ .bool)
    (e : WEnv Δ Γ) : a.optimize.evalBool e = a.evalBool e :=
  Term.optimize_eval _ _ _ _

@[simp] theorem WFAtom.optimize_evalList {Γ : WCtx ks} {τ : Ty ks} (a : WFAtom Δ Γ (.list τ))
    (e : WEnv Δ Γ) : a.optimize.evalList e = a.evalList e :=
  Term.optimize_eval _ _ _ _

/-- Arguments optimised one by one. -/
def WFAtoms.optimize {Γ : WCtx ks} : {ts : WCtx ks} → WFAtoms Δ Γ ts → WFAtoms Δ Γ ts
  | _, .nil => .nil
  | _, .cons a as => .cons a.optimize as.optimize

@[simp] theorem WFAtoms.optimize_eval {Γ : WCtx ks} : {ts : WCtx ks} → (as : WFAtoms Δ Γ ts) →
    (e : WEnv Δ Γ) → as.optimize.eval e = as.eval e
  | _, .nil, _ => rfl
  | _, .cons a as, e => by
      simp only [WFAtoms.optimize, WFAtoms.eval, WFAtom.optimize_eval, WFAtoms.optimize_eval]

/-- The value of a test, when it is a literal. -/
def WFAtom.boolConst? {Γ : WCtx ks} (c : WFAtom Δ Γ .bool) :
    Option {b : Bool // ∀ e, c.evalBool e = b} :=
  match c with
  | ⟨.ret (.lit _ v)⟩ => some ⟨v, fun _ => rfl⟩
  | _ => none

/-- A proof that a list is empty, when it is the literal `[]`. -/
def WFAtom.nilConst? {Γ : WCtx ks} {τ : Ty ks} (l : WFAtom Δ Γ (.list τ)) :
    Option (PLift (∀ e, l.evalList e = [])) :=
  match l with
  | ⟨.ret (.list_mk .nil)⟩ => some ⟨fun _ => rfl⟩
  | _ => none

/-- The literal `[]`. -/
def WFAtom.nil {Γ : WCtx ks} (τ : Ty ks) : WFAtom Δ Γ (.list τ) :=
  ⟨(Term.ret (.list_mk .nil) : Term Δ 0 [] (WCtx.toU Γ) (.list τ) [] none)⟩

@[simp] theorem WFAtom.nil_eval {Γ : WCtx ks} (τ : Ty ks) (e : WEnv Δ Γ) :
    (WFAtom.nil τ).evalList e = [] := rfl

/-! ## Join points entered at once -/

/-- A statement that is a jump to the innermost join point, with its argument. -/
structure WFJumpHere {GL : List (WFFn Δ)} {Γ : WCtx ks} {G : WEnv Δ Γ → Prop}
    {sf : Option (WFSelf Δ Γ)} {t : Ty ks} {Q : WEnv Δ Γ → Ty.Den Δ t → Prop}
    {js : WFJScope Δ Γ t} {s : Ty ks} {P : WEnv Δ Γ → Ty.Den Δ s → Prop}
    (m : WFTerm Δ GL Γ G sf t Q (.bind js s P Q)) where
  /-- The argument of the jump. -/
  arg : WFAtom Δ Γ s
  /-- It satisfies the precondition of the join point. -/
  hpre : ∀ e, G e → P e (arg.eval e)
  /-- The statement is the jump. -/
  eval_eq : ∀ (fe : WFFEnv GL) (e : WEnv Δ Γ) (hG : G e) (sv : WFSelfEnv sf e)
    (je : WFJEnv (.bind js s P Q) e), (m.eval fe e hG sv je).1 = (je.1 (arg.eval e) (hpre e hG)).1

/-- Is the statement a jump to the innermost join point? -/
def WFTerm.asJumpHere? {GL : List (WFFn Δ)} {Γ : WCtx ks} {G : WEnv Δ Γ → Prop}
    {sf : Option (WFSelf Δ Γ)} {t : Ty ks} {Q : WEnv Δ Γ → Ty.Den Δ t → Prop}
    {js : WFJScope Δ Γ t} {s : Ty ks} {P : WEnv Δ Γ → Ty.Den Δ s → Prop}
    (m : WFTerm Δ GL Γ G sf t Q (.bind js s P Q)) : Option (WFJumpHere m) :=
  match m with
  | .jump .here a hpre _ => some ⟨a, hpre, fun _ _ _ _ _ => rfl⟩
  | _ => none

/-! ## The optimiser -/

/-- An optimised computation: it may establish a different fact (e.g. about optimised
arguments), which implies the original one. -/
structure WFOptComp (GL : List (WFFn Δ)) (Γ : WCtx ks) (G : WEnv Δ Γ → Prop)
    (sf : Option (WFSelf Δ Γ)) (u : Ty ks) (F : WEnv Δ (u :: Γ) → Prop) where
  /-- The fact the optimised computation establishes. -/
  fact : WEnv Δ (u :: Γ) → Prop
  /-- The optimised computation. -/
  comp : WFComp Δ GL Γ G sf u fact
  /-- The fact implies the original one. -/
  imp : ∀ e, fact e → F e

section Optimize
variable {GL : List (WFFn Δ)}

mutual

/-- Optimise a computation, under a stronger path condition `G₂`. -/
def WFComp.optimize : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} → {sf : Option (WFSelf Δ Γ)} →
    {u : Ty ks} → {F : WEnv Δ (u :: Γ) → Prop} → WFComp Δ GL Γ G sf u F →
    {G₂ : WEnv Δ Γ → Prop} → (∀ e, G₂ e → G e) → WFOptComp GL Γ G₂ sf u F
  | _, _, _, _, _, .self args dec hpre, _, h =>
      ⟨_, .self args.optimize (fun e hg => by rw [WFAtoms.optimize_eval]; exact dec e (h e hg))
          (fun e hg => by rw [WFAtoms.optimize_eval]; exact hpre e (h e hg)),
        fun e hf => by simpa only [WFAtoms.optimize_eval] using hf⟩
  | _, _, _, _, _, .call i args hpre, _, h =>
      ⟨_, .call i args.optimize (fun e hg => by rw [WFAtoms.optimize_eval]; exact hpre e (h e hg)),
        fun e hf => by simpa only [WFAtoms.optimize_eval] using hf⟩
  | _, _, _, _, _, .share a, _, _ =>
      ⟨_, .share a.optimize, fun e hf => by simpa only [WFAtom.optimize_eval] using hf⟩
  | _, _, _, _, _, .map (u := u) l body, _, h =>
      match l.optimize.nilConst? with
      | some _ => ⟨_, .share (WFAtom.nil u), fun _ _ => trivial⟩
      | none =>
          ⟨_, .map l.optimize (body.optimizeUnder (fun e hg =>
              ⟨h _ hg.1, by simpa only [WFAtom.optimize_evalList] using hg.2⟩)),
            fun _ _ => trivial⟩
  | _, _, _, _, _, .foldl l init body, _, h =>
      match l.optimize.nilConst? with
      | some _ => ⟨_, .share init.optimize, fun _ _ => trivial⟩
      | none =>
          ⟨_, .foldl l.optimize init.optimize (body.optimizeUnder (fun e hg =>
              ⟨h _ hg.1, by simpa only [WFAtom.optimize_evalList] using hg.2⟩)),
            fun _ _ => trivial⟩
  termination_by structural _ _ _ _ _ c => c

/-- Optimise a statement, under a stronger path condition `G₂`. -/
def WFTerm.optimizeUnder : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} →
    {sf : Option (WFSelf Δ Γ)} → {t : Ty ks} → {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} →
    {js : WFJScope Δ Γ t} → WFTerm Δ GL Γ G sf t Q js →
    {G₂ : WEnv Δ Γ → Prop} → (∀ e, G₂ e → G e) → WFTerm Δ GL Γ G₂ sf t Q js
  | _, _, _, _, _, _, .ret a post, _, h =>
      .ret a.optimize (fun e hg => by rw [WFAtom.optimize_eval]; exact post e (h e hg))
  | _, _, _, _, _, _, .ite c a b, _, h =>
      match c.optimize.boolConst? with
      | some ⟨true, hc⟩ =>
          a.optimizeUnder (fun e hg => ⟨h e hg, by rw [← WFAtom.optimize_evalBool]; exact hc e⟩)
      | some ⟨false, hc⟩ =>
          b.optimizeUnder (fun e hg => ⟨h e hg, by rw [← WFAtom.optimize_evalBool]; exact hc e⟩)
      | none =>
          .ite c.optimize
            (a.optimizeUnder (fun e hg =>
              ⟨h e hg.1, by simpa only [WFAtom.optimize_evalBool] using hg.2⟩))
            (b.optimizeUnder (fun e hg =>
              ⟨h e hg.1, by simpa only [WFAtom.optimize_evalBool] using hg.2⟩))
  | _, _, _, _, _, _, .letE c k, _, h =>
      let oc := c.optimize h
      .letE oc.comp (k.optimizeUnder (fun e hg => ⟨h _ hg.1, oc.imp e hg.2⟩))
  | _, _, _, _, _, _, .join s P body m, _, h =>
      let m' := m.optimizeUnder h
      match m'.asJumpHere? with
      | some jh =>
          .letE (.share jh.arg) (body.optimizeUnder (fun e hg =>
            ⟨h _ hg.1, by rw [hg.2]; exact jh.hpre e.2 hg.1⟩))
      | none => .join s P (body.optimizeUnder (fun e hg => ⟨h _ hg.1, hg.2⟩)) m'
  | _, _, _, _, _, _, .joinrec s P R wf body m, _, h =>
      .joinrec s P R wf (body.optimizeUnder (fun e hg => ⟨h _ hg.1, hg.2⟩)) (m.optimizeUnder h)
  | _, _, _, _, _, _, .jump i a hpre hpost, _, h =>
      .jump i a.optimize (fun e hg => by rw [WFAtom.optimize_eval]; exact hpre e (h e hg))
        (fun e hg => hpost e (h e hg))
  termination_by structural _ _ _ _ _ _ t => t

end

/-- Optimise a statement. -/
def WFTerm.optimize {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)} {t : Ty ks}
    {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t} (x : WFTerm Δ GL Γ G sf t Q js) :
    WFTerm Δ GL Γ G sf t Q js :=
  x.optimizeUnder (fun _ h => h)

end Optimize

/-- Optimise every global function. -/
def WFGlobals.optimize : {GL : List (WFFn Δ)} → WFGlobals Δ GL → WFGlobals Δ GL
  | _, .nil => .nil
  | _, .cons gs f R wf body => .cons gs.optimize f R wf body.optimize

/-- Optimise a program: its global functions and its main statement. -/
def WFProgram.optimize {τ : Ty ks} {Q : Ty.Den Δ τ → Prop} (p : WFProgram Δ τ Q) :
    WFProgram Δ τ Q :=
  { GL := p.GL, globals := p.globals.optimize, main := p.main.optimize }

/-! ## The optimiser does not change the value -/

/-- The value of a function with a subtype result does not depend on the proofs it is given. -/
theorem WFTerm.val_congr2 {α β : Type} {A : α → Prop} {P : α → β → Prop}
    (g : (x : α) → A x → {v : β // P x v}) {a b : α} (hab : a = b) (p : A a) (q : A b) :
    (g a p).1 = (g b q).1 := by
  subst hab; rfl

/-- The value of a function with a subtype result does not depend on the proofs it is given. -/
theorem WFTerm.val_congr3 {α β : Type} {A B : α → Prop} {P : α → β → Prop}
    (g : (x : α) → A x → B x → {v : β // P x v}) {a b : α} (hab : a = b) (p : A a) (q : B a)
    (p' : A b) (q' : B b) : (g a p q).1 = (g b p' q').1 := by
  subst hab; rfl

theorem WFTerm.attach_map_nil {α β : Type} (L : List α) (hL : L = [])
    (f : {x // x ∈ L} → β) : L.attach.map f = [] := by
  subst hL; rfl

theorem WFTerm.attach_foldl_nil {α β : Type} (L : List α) (hL : L = [])
    (f : β → {x // x ∈ L} → β) (b : β) : L.attach.foldl f b = b := by
  subst hL; rfl

theorem WFTerm.attach_map_congr {α β : Type} {L₁ L₂ : List α} (hL : L₁ = L₂)
    (f₁ : {x // x ∈ L₁} → β) (f₂ : {x // x ∈ L₂} → β)
    (hf : ∀ x h₁ h₂, f₁ ⟨x, h₁⟩ = f₂ ⟨x, h₂⟩) : L₁.attach.map f₁ = L₂.attach.map f₂ := by
  subst hL
  congr 1
  funext ⟨x, h⟩
  exact hf x h h

theorem WFTerm.attach_foldl_congr {α β : Type} {L₁ L₂ : List α} (hL : L₁ = L₂)
    (f₁ : β → {x // x ∈ L₁} → β) (f₂ : β → {x // x ∈ L₂} → β)
    (hf : ∀ b x h₁ h₂, f₁ b ⟨x, h₁⟩ = f₂ b ⟨x, h₂⟩) (b : β) :
    L₁.attach.foldl f₁ b = L₂.attach.foldl f₂ b := by
  subst hL
  congr 1
  funext b ⟨x, h⟩
  exact hf b x h h

section Correct
variable {GL : List (WFFn Δ)} (fe : WFFEnv GL)

theorem WFTerm.fix_congr {α : Type} {C : α → Sort _} {r : α → α → Prop} (hwf : WellFounded r)
    (F₁ F₂ : ∀ x, (∀ y, r y x → C y) → C x) (h : F₁ = F₂) :
    WellFounded.fix hwf F₁ = WellFounded.fix hwf F₂ := by
  subst h; rfl

/-- The continuation of a `let` run on equal values gives equal answers. -/
theorem WFTerm.eval_congr_head {Γ : WCtx ks} {sf : Option (WFSelf Δ Γ)} {t u : Ty ks}
    {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t} {G' : WEnv Δ (u :: Γ) → Prop}
    (k : WFTerm Δ GL (u :: Γ) G' (sf.map (·.push u)) t (fun e v => Q e.2 v) (.wk js u))
    (e : WEnv Δ Γ) (sv : WFSelfEnv sf e) (je : WFJEnv js e) {x y : Ty.Den Δ u} (hxy : x = y)
    (hx : G' (x, e)) (hy : G' (y, e)) :
    k.eval fe (x, e) hx (sv.push x) je = k.eval fe (y, e) hy (sv.push y) je := by
  subst hxy; rfl

mutual

theorem WFComp.optimize_eval : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} →
    {sf : Option (WFSelf Δ Γ)} → {u : Ty ks} → {F : WEnv Δ (u :: Γ) → Prop} →
    (c : WFComp Δ GL Γ G sf u F) → {G₂ : WEnv Δ Γ → Prop} → (h : ∀ e, G₂ e → G e) →
    (e : WEnv Δ Γ) → (hg : G₂ e) → (sv : WFSelfEnv sf e) →
    ((c.optimize h).comp.eval fe e hg sv).1 = (c.eval fe e (h e hg) sv).1
  | _, _, _, _, _, .self args dec hpre, _, h, e, hg, sv => by
      simp only [WFComp.optimize, WFComp.eval]
      exact WFTerm.val_congr3 sv (WFAtoms.optimize_eval args e) _ _ _ _
  | _, _, _, _, _, .call i args hpre, _, h, e, hg, sv => by
      simp only [WFComp.optimize, WFComp.eval]
      exact WFTerm.val_congr2 (i.get fe) (WFAtoms.optimize_eval args e) _ _
  | _, _, _, _, _, .share a, _, h, e, hg, sv => by
      simp only [WFComp.optimize, WFComp.eval, WFAtom.optimize_eval]
  | _, _, _, _, _, .map l body, _, h, e, hg, sv => by
      simp only [WFComp.optimize]
      split
      · next pf _ =>
        simp only [WFComp.eval]
        refine (WFTerm.attach_map_nil _ ?_ _).symm
        rw [← WFAtom.optimize_evalList]
        exact pf.down e
      · simp only [WFComp.eval]
        refine WFTerm.attach_map_congr (WFAtom.optimize_evalList l e) _ _ ?_
        intro x h₁ h₂
        exact congrArg Subtype.val (WFTerm.optimizeUnder_eval body _ (x, e) _ _ ())
  | _, _, _, _, _, .foldl l init body, _, h, e, hg, sv => by
      simp only [WFComp.optimize]
      split
      · next pf _ =>
        simp only [WFComp.eval, WFAtom.optimize_eval]
        refine (WFTerm.attach_foldl_nil _ ?_ _ _).symm
        rw [← WFAtom.optimize_evalList]
        exact pf.down e
      · simp only [WFComp.eval, WFAtom.optimize_eval]
        refine WFTerm.attach_foldl_congr (WFAtom.optimize_evalList l e) _ _ ?_ _
        intro b x h₁ h₂
        exact congrArg Subtype.val (WFTerm.optimizeUnder_eval body _ (b, x, e) _ _ ())

theorem WFTerm.optimizeUnder_eval : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} →
    {sf : Option (WFSelf Δ Γ)} → {t : Ty ks} → {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} →
    {js : WFJScope Δ Γ t} → (x : WFTerm Δ GL Γ G sf t Q js) →
    {G₂ : WEnv Δ Γ → Prop} → (h : ∀ e, G₂ e → G e) →
    (e : WEnv Δ Γ) → (hg : G₂ e) → (sv : WFSelfEnv sf e) → (je : WFJEnv js e) →
    (x.optimizeUnder h).eval fe e hg sv je = x.eval fe e (h e hg) sv je
  | _, _, _, _, _, _, .ret a post, _, h, e, hg, sv, je => by
      apply Subtype.ext
      simp only [WFTerm.optimizeUnder, WFTerm.eval, WFAtom.optimize_eval]
  | _, _, _, _, _, _, .ite c a b, _, h, e, hg, sv, je => by
      simp only [WFTerm.optimizeUnder]
      split
      · next hc _ =>
        have hce : c.evalBool e = true := by rw [← WFAtom.optimize_evalBool]; exact hc e
        refine (WFTerm.optimizeUnder_eval a _ e hg sv je).trans ?_
        simp only [WFTerm.eval]
        rw [dite_eq_left_of_eq_true (eq_true hce)]
      · next hc _ =>
        have hce : ¬ c.evalBool e = true := by
          rw [← WFAtom.optimize_evalBool, hc e]; exact Bool.false_ne_true
        refine (WFTerm.optimizeUnder_eval b _ e hg sv je).trans ?_
        simp only [WFTerm.eval]
        rw [dite_eq_right_of_eq_false (eq_false hce)]
      · simp only [WFTerm.eval]
        by_cases hce : c.evalBool e = true
        · rw [dite_eq_left_of_eq_true (eq_true (by rwa [WFAtom.optimize_evalBool])),
            dite_eq_left_of_eq_true (eq_true hce)]
          exact WFTerm.optimizeUnder_eval a _ e _ sv je
        · rw [dite_eq_right_of_eq_false (eq_false (by rwa [WFAtom.optimize_evalBool])),
            dite_eq_right_of_eq_false (eq_false hce)]
          exact WFTerm.optimizeUnder_eval b _ e _ sv je
  | _, _, _, _, _, _, .letE c k, _, h, e, hg, sv, je => by
      simp only [WFTerm.optimizeUnder, WFTerm.eval]
      rw [WFTerm.optimizeUnder_eval k]
      exact WFTerm.eval_congr_head fe k e sv je (WFComp.optimize_eval c h e hg sv) _ _
  | _, _, _, _, _, _, .join s P body m, _, h, e, hg, sv, je => by
      simp only [WFTerm.optimizeUnder]
      split
      · next jh _ =>
        simp only [WFTerm.eval, WFComp.eval]
        apply Subtype.ext
        rw [← WFTerm.optimizeUnder_eval m h e hg, jh.eval_eq]
        exact congrArg Subtype.val
          (WFTerm.optimizeUnder_eval body _ (jh.arg.eval e, e) _ (sv.push (jh.arg.eval e)) je)
      · simp only [WFTerm.eval]
        refine (WFTerm.optimizeUnder_eval m h e hg sv _).trans ?_
        congr 2
        funext v hP
        exact WFTerm.optimizeUnder_eval body _ (v, e) _ (sv.push v) je
  | _, _, _, _, _, _, .joinrec s P R wf body m, _, h, e, hg, sv, je => by
      simp only [WFTerm.optimizeUnder, WFTerm.eval]
      refine (WFTerm.optimizeUnder_eval m h e hg sv _).trans ?_
      congr 2
      exact WFTerm.fix_congr (wf e) _ _ (funext fun x => funext fun ih =>
        funext fun hP => WFTerm.optimizeUnder_eval body _ (x, e) _ (sv.push x) _)
  | _, _, _, _, _, _, .jump i a hpre hpost, _, h, e, hg, sv, je => by
      apply Subtype.ext
      simp only [WFTerm.optimizeUnder, WFTerm.eval]
      congr 2
      exact WFAtom.optimize_eval a e

end

/-- **The optimiser does not change the value of a statement**, in every environment. -/
theorem WFTerm.optimize_eval {Γ : WCtx ks} {G : WEnv Δ Γ → Prop} {sf : Option (WFSelf Δ Γ)}
    {t : Ty ks} {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} {js : WFJScope Δ Γ t}
    (x : WFTerm Δ GL Γ G sf t Q js) (e : WEnv Δ Γ) (hG : G e) (sv : WFSelfEnv sf e)
    (je : WFJEnv js e) : x.optimize.eval fe e hG sv je = x.eval fe e hG sv je :=
  x.optimizeUnder_eval fe (fun _ h => h) e hG sv je

end Correct

/-- The optimised global functions have the same values. -/
theorem WFGlobals.optimize_eval : {GL : List (WFFn Δ)} → (gs : WFGlobals Δ GL) →
    gs.optimize.eval = gs.eval
  | _, .nil => rfl
  | _, .cons gs f R wf body => by
      simp only [WFGlobals.optimize, WFGlobals.eval, WFGlobals.optimize_eval gs]
      congr 1
      unfold WFFn.fix
      funext x hx
      refine congrArg (fun F =>
        WellFounded.fix (C := fun x => f.pre x → {v : Ty.Den Δ f.ret // f.post x v}) wf F x hx) ?_
      funext y ih hy
      exact body.optimize_eval _ _ _ _ _

/-- **The optimiser does not change the value of a program.** -/
theorem WFProgram.optimize_run {τ : Ty ks} {Q : Ty.Den Δ τ → Prop} (p : WFProgram Δ τ Q) :
    p.optimize.run = p.run := by
  simp only [WFProgram.run, WFProgram.optimize, WFGlobals.optimize_eval]
  exact p.main.optimize_eval _ _ _ _ _

end LeanScript

end
