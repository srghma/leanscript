module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Optimized terms do not duplicate work

Two properties of the optimized grammar, and of what `#leanscript_to_term` emits:

* **A `let` is never inlined where it would run more often.**  A use of a variable under
  a `fun`, in the branch of a fold or in an unmemoised delay counts as many uses
  (`LeanScript.Usage.many`), so `let x = n + n; fun y => x + y` keeps its `let` — the
  term with `n + n` moved into the `fun` would recompute it at every call.  A memoised
  delay (`thunk`) runs its body at most once, so a `let` read once there is still
  inlined.
* **A `let` does not hide a redex.**  The grammar is in A-normal form, so a `let` never
  stands where it is applied or forced: `(let x = e; fun y => b) a` and forcing
  `let x = e; thunk …` are rejected.  The translation floats the `let` out and reduces
  what is then exposed.
-/

namespace TermTests.Sharing

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Written by hand: what the grammar accepts -/

/-- `fun n => let x = n + n; fun y => x + y`: `x` is read once, but under a `fun`, so the
    `let` is kept. -/
def shareUnderFun :=
  (.lam (.letE
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
     (.lam (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run shareUnderFun 3 4 = 10 := rfl

/-- `fun m n => let x = n + n; Nat.rec 0 (fun _ acc => acc + x) m`: `x` is read once, but in
    the branch of a fold, which runs `m` times, so the `let` is kept. -/
def shareInFold :=
  (.lam (.lam (.letE
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
     (.nat_rec 0 (.var (v♯2)) (.cons (.nat_mk 0) .nil)
       (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯2)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run shareInFold 3 5 = 30 := rfl

/-- `fun n => let x = n + n; lazy x`: a `lazy` value runs its body at every force, so the
    `let` is kept. -/
def shareInLazy :=
  (.lam (.letE
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
     (.lazy_mk (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.lazy (TyWf.prim .nat)) .lam)

-- A `thunk` runs its body at most once: a `let` read once in it is inlined, not kept.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.letUsed (Usage.single DeBruijn.head).cond.head ((Usage.single DeBruijn.head).cond.opnd 0) = true
is false
---
error: could not synthesize default value for parameter 'hPlace' using tactics
---
error: Tactic `decide` proved that the proposition
  (Usage.single DeBruijn.head).cond.confined 0 = false
is false
-/
#guard_msgs (error) in
def letInThunk :=
  (.lam (.letE
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
     (.thunk_mk (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.thunk (TyWf.prim .nat)) .lam)

-- A β-redex behind a `let`: `fun n => (let x = n + n; fun y => x + y) n`.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.lam.letIn.isCallee && (Head.var (Var.index DeBruijn.head)).isAtom) = true
is false
-/
#guard_msgs (error) in
def hiddenBeta :=
  (.lam (.ap
     (.letE
       (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
       (.lam (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) :
         Term sig0 [TyWf.prim .nat, TyWf.prim .nat] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _))
     (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- A force of a delay built behind a `let`: `fun n => (let x = n + n; thunk (x + x)).force`.
/--
error: could not synthesize default value for parameter 'hPlace' using tactics
---
error: Tactic `decide` proved that the proposition
  (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0)).cond.confined
      0 =
    false
is false
---
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.ctorOf [Head.comp]).letIn.isName = true
is false
-/
#guard_msgs (error) in
def hiddenForce :=
  (.lam (.thunk_force
     (.letE
       (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
       (.thunk_mk (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-! ## Translated: what `#leanscript_to_term` emits -/

def shareUnderFunDef (n : Nat) : Nat → Nat := let x := n * n; fun y => x + y

def shareUnderFunDef_term :=
  (#leanscript_to_term shareUnderFunDef :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run shareUnderFunDef_term 3 4 = 13 := rfl

-- The `let` is kept, outside the inner `fun`.
/--
info: Term.atom
  (Atom.lam
    (Term.letE
      (Comp.externCall
        (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head))
          (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯)
      (Term.atom
        (Atom.lam
          (Term.comp
            (Comp.externCall
              (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail))
                (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) Spine.nil))
              (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯)
            shareUnderFunDef_term._proof_7)
          ⋯))
      ⋯ ⋯ ⋯ ⋯)
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) shareUnderFunDef_term

def shareInFoldDef (n m : Nat) : Nat :=
  let x := n * n
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => acc + x) m

def shareInFoldDef_term :=
  (#leanscript_to_term shareInFoldDef :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run shareInFoldDef_term 3 5 = 45 := rfl

-- The `let` is kept, outside the fold.
/--
info: Term.atom
  (Atom.lam
    (Term.atom
      (Atom.lam
        (Term.letE
          (Comp.externCall
            (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail))
              (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail)) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯)
          (Term.comp
            (Comp.nat_rec 0 (Atom.ref (Ref.var DeBruijnProj.head.tail)) (Spine.cons (Atom.nat_mk 0) Spine.nil)
              (Term.comp
                (Comp.externCall
                  (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail))
                    (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail.tail)) Spine.nil))
                  (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯)
                shareUnderFunDef_term._proof_7)
              ⋯ shareInFoldDef_term._proof_6 ⋯)
            shareUnderFunDef_term._proof_7)
          ⋯ ⋯ ⋯ ⋯)
        ⋯))
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) shareInFoldDef_term

/-- A β-redex behind a `let`, in the source.  The translation floats the `let` out, reduces
    the β-redex, and then inlines `x`, which is read once and not under a `fun` any more:
    what is left is `fun n => let x = n * n; x + n` — the `let` is kept, since in A-normal
    form an argument of an extern is an atom. -/
def hiddenBetaDef (n : Nat) : Nat := (let x := n * n; fun y => x + y) n

def hiddenBetaDef_term :=
  (#leanscript_to_term hiddenBetaDef : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run hiddenBetaDef_term 5 = 30 := rfl

/--
info: Term.atom
  (Atom.lam
    (Term.letE
      (Comp.externCall
        (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head))
          (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯)
      (Term.comp
        (Comp.externCall
          (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head))
            (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail)) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯)
        shareUnderFunDef_term._proof_7)
      ⋯ ⋯ ⋯ ⋯)
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) hiddenBetaDef_term

end TermTests.Sharing
