module

public import LeanScript.WFTerm.Syntax

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of `WFTerm`: total, without fuel, measures or default values

`WFTerm.eval fe t e hG sv je : {r // Q e r}` runs the statement `t` in the environment `e`,
given

* `fe : WFFEnv GL`, the values of the global functions;
* `hG : G e`, the path condition (a proof: erased at runtime);
* `sv : WFSelfEnv sf e`, the enclosing recursive function, restricted to the arguments that are
  below the current ones along its well-founded relation (so a recursive call must pass the
  decrease proof it carries);
* `je : WFJEnv js e`, the closures of the join points in scope.

It is defined by **structural** recursion on the syntax (`WFTerm`/`WFComp`).  The only other
recursion is `WellFounded.fix`, for the global functions (`WFFn.fix`, `WFGlobals.eval`) and the
recursive join points (`joinrec`): its well-foundedness argument is a proof, so nothing is
checked or counted at runtime, and the answer always satisfies the postcondition.
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-- Values of the join points in scope at the environment `e`: the closures of their bodies. -/
@[reducible] def WFJEnv : {Γ : WCtx ks} → {t : Ty ks} → WFJScope Δ Γ t → WEnv Δ Γ → Type
  | _, _, .nil, _ => Unit
  | _, t, .bind js s P Q, e =>
      ((v : Ty.Den Δ s) → P e v → {r : Ty.Den Δ t // Q e r}) × WFJEnv js e
  | _, _, .wk js _, e => WFJEnv js e.2

/-- Lookup of a join point. -/
def WFJVar.get : {Γ : WCtx ks} → {t : Ty ks} → {js : WFJScope Δ Γ t} → (i : WFJVar js) →
    {e : WEnv Δ Γ} → WFJEnv js e → (v : Ty.Den Δ i.arg) → i.pre e v →
    {r : Ty.Den Δ t // i.post e r}
  | _, _, .bind _ _ _ _, .here, _, je => je.1
  | _, _, .bind _ _ _ _, .there i, _, je => i.get je.2
  | _, _, .wk _ _, .wk i, _, je => i.get je

/-- The enclosing recursive function at the environment `e`, on the arguments that are below its
current ones (`sf.cur e`) and satisfy its precondition. -/
@[reducible] def WFSelfEnv {Γ : WCtx ks} : Option (WFSelf Δ Γ) → WEnv Δ Γ → Type
  | none, _ => Unit
  | some sf, e =>
      (x : WEnv Δ sf.params) → sf.R x (sf.cur e) → sf.pre x → {v : Ty.Den Δ sf.ret // sf.post x v}

/-- The enclosing recursive function, seen under one more variable (the same function). -/
def WFSelfEnv.push {Γ : WCtx ks} {u : Ty ks} : {sf : Option (WFSelf Δ Γ)} → {e : WEnv Δ Γ} →
    WFSelfEnv sf e → (v : Ty.Den Δ u) → WFSelfEnv (sf.map (·.push u)) ((v, e) : WEnv Δ (u :: Γ))
  | none, _, _, _ => ()
  | some _, _, sv, _ => sv

section Eval
variable {GL : List (WFFn Δ)} (fe : WFFEnv GL)

mutual

/-- The value of a computation, with the fact it establishes. -/
def WFComp.eval : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} → {sf : Option (WFSelf Δ Γ)} →
    {u : Ty ks} → {F : WEnv Δ (u :: Γ) → Prop} → WFComp Δ GL Γ G sf u F →
    (e : WEnv Δ Γ) → G e → WFSelfEnv sf e → {v : Ty.Den Δ u // F (v, e)}
  | _, _, _, _, _, .self args dec hpre, e, hG, sv => sv (args.eval e) (dec e hG) (hpre e hG)
  | _, _, _, _, _, .call i args hpre, e, hG, _ => i.get fe (args.eval e) (hpre e hG)
  | _, _, _, _, _, .share a, e, _, _ => ⟨a.eval e, rfl⟩
  | _, _, _, _, _, .map l body, e, hG, sv =>
      ⟨(l.evalList e).attach.map (fun x => (body.eval (x.1, e) ⟨hG, x.2⟩ (sv.push x.1) ()).1),
        trivial⟩
  | _, _, _, _, _, .foldl l init body, e, hG, sv =>
      ⟨(l.evalList e).attach.foldl
        (fun acc x => (body.eval (acc, x.1, e) ⟨hG, x.2⟩ ((sv.push x.1).push acc) ()).1)
        (init.eval e), trivial⟩
  termination_by structural _ _ _ _ _ c => c

/-- The value of a statement, with the proof that it satisfies the postcondition. -/
def WFTerm.eval : {Γ : WCtx ks} → {G : WEnv Δ Γ → Prop} → {sf : Option (WFSelf Δ Γ)} →
    {t : Ty ks} → {Q : WEnv Δ Γ → Ty.Den Δ t → Prop} → {js : WFJScope Δ Γ t} →
    WFTerm Δ GL Γ G sf t Q js →
    (e : WEnv Δ Γ) → G e → WFSelfEnv sf e → WFJEnv js e → {r : Ty.Den Δ t // Q e r}
  | _, _, _, _, _, _, .ret a post, e, hG, _, _ => ⟨a.eval e, post e hG⟩
  | _, _, _, _, _, _, .ite c a b, e, hG, sv, je =>
      if h : c.evalBool e = true then a.eval e ⟨hG, h⟩ sv je
      else b.eval e ⟨hG, Bool.of_not_eq_true h⟩ sv je
  | _, _, _, _, _, _, .letE c k, e, hG, sv, je =>
      let v := c.eval e hG sv
      k.eval (v.1, e) ⟨hG, v.2⟩ (sv.push v.1) je
  | _, _, _, _, _, _, .join _ _ body m, e, hG, sv, je =>
      m.eval e hG sv (fun v hP => body.eval (v, e) ⟨hG, hP⟩ (sv.push v) je, je)
  | _, _, _, _, _, _, .joinrec _ _ _ wf body m, e, hG, sv, je =>
      m.eval e hG sv
        (WellFounded.fix (wf e) (fun x ih hP =>
          body.eval (x, e) ⟨hG, hP⟩ (sv.push x) (fun v h => ih v h.2 h.1, je)), je)
  | _, _, _, _, _, _, .jump i a hpre hpost, e, hG, _, je =>
      let r := i.get je (a.eval e) (hpre e hG)
      ⟨r.1, hpost e hG r.1 r.2⟩
  termination_by structural _ _ _ _ _ _ t => t

end

end Eval

/-! ## Global functions and programs -/

/-- The value of a global function defined by well-founded recursion: its body, in which the
recursive calls (`WFComp.self`) run the function itself on smaller arguments. -/
def WFFn.fix {GL : List (WFFn Δ)} (fe : WFFEnv GL) (f : WFFn Δ)
    (R : WEnv Δ f.params → WEnv Δ f.params → Prop) (wf : WellFounded R)
    (body : WFTerm Δ GL f.params f.pre (some (WFSelf.top f R)) f.ret f.post .nil) : WFFnVal f :=
  fun x hx =>
    WellFounded.fix (C := fun x => f.pre x → {v : Ty.Den Δ f.ret // f.post x v}) wf
      (fun x ih hx => body.eval fe x hx (fun y hy hpre => ih y hy hpre) ()) x hx

/-- The values of the global functions. -/
def WFGlobals.eval : {GL : List (WFFn Δ)} → WFGlobals Δ GL → WFFEnv GL
  | _, .nil => ()
  | _, .cons gs f R wf body => let fe := gs.eval; (WFFn.fix fe f R wf body, fe)

/-- The value of a program, with the proof that it satisfies the postcondition. -/
def WFProgram.run {τ : Ty ks} {Q : Ty.Den Δ τ → Prop} (p : WFProgram Δ τ Q) :
    {r : Ty.Den Δ τ // Q r} :=
  p.main.eval p.globals.eval () trivial () ()

/-- The unfolding equation of a global function: its value is its body, run with the function
itself (on smaller arguments) as the enclosing recursive function. -/
theorem WFFn.fix_eq {GL : List (WFFn Δ)} (fe : WFFEnv GL) (f : WFFn Δ)
    (R : WEnv Δ f.params → WEnv Δ f.params → Prop) (wf : WellFounded R)
    (body : WFTerm Δ GL f.params f.pre (some (WFSelf.top f R)) f.ret f.post .nil)
    (x : WEnv Δ f.params) (hx : f.pre x) :
    WFFn.fix fe f R wf body x hx =
      body.eval fe x hx (fun y _ hpre => WFFn.fix fe f R wf body y hpre) () := by
  unfold WFFn.fix
  rw [WellFounded.fix_eq]

end LeanScript

end
