module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Two more redexes: an application or a force of a dispatch, and a fold that is a case

* **A dispatch that may answer with an introduction form** — a `fun`, a delay, a literal,
  a constructor — has the head `LeanScript.Head.caseIntro`, computed from the heads of its
  branches (`LeanScript.Head.join`).  Applying one to an argument, or forcing one, is a
  redex: `(if c then fun y => b else g) a` is `if c then b[a/y] else g a`, and
  `(if c then thunk e else t).get` is `if c then e else t.get`.  `Term.ap`,
  `Term.thunk_force` and `Term.lazy_force` reject it, and the translation moves the
  application (the argument bound by a `let` first when it is not a variable or a literal)
  or the force into the branches.
* **A fold whose branch reads none of its answers** is a case analysis: `Term.nat_rec` and
  `Term.array_rec` ask that the branch reads at least one answer (`hRec`), and the
  translation writes such a fold as `k + 1` nested `nat_casesOn` / `array_casesOn`.
-/

namespace TermTests.DispatchAndFold

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Written by hand: what the grammar accepts and rejects -/

/-- `fun c f g => (if c then f else g) 3`: no branch is an introduction form, so the
    dispatch is a plain computation and may be applied. -/
def appVarBranches :=
  (.lam (.lam (.lam (.ap (.bool_casesOn (.var (v♯2)) (.var (v♯1)) (.var (v♯0))) (.nat_mk 3)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒
      (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

-- `fun c a => (if c then fun y => y else fun y => y) a`: a β-redex in each branch.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.lam.join Head.lam).isFunLike = false
is false
-/
#guard_msgs (error) in
def appFunBranches :=
  (.lam (.lam (.ap (.bool_casesOn (.var (v♯1)) (.lam (.var (v♯0))) (.lam (.var (v♯0))))
    (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- `fun c t => (if c then thunk 5 else t).get`: a force of a delay built in a branch.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  ((Head.ctorOf [Head.lit]).join Head.var).isCtorLike = false
is false
-/
#guard_msgs (error) in
def forceThunkBranch :=
  (.lam (.lam (.thunk_force (.bool_casesOn (.var (v♯1)) (.thunk_mk (.nat_mk 5)) (.var (v♯0))))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.thunk (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- `fun c n => let g = (if c then fun y => y + n else fun y => y); g 1 + g 2`: a dispatch
    that answers with a `fun` is a computation, so a `let` may share it. -/
def shareCaseIntro :=
  (.lam (.lam (.letE
     (.bool_casesOn (.var (v♯1))
       (.lam (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
         fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))
       (.lam (.var (v♯0))) :
       Term sig0 [TyWf.prim .nat, TyWf.prim .bool] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _)
     (.externCall (.cons (.ap (.var (v♯0)) (.nat_mk 1)) (.cons (.ap (.var (v♯0)) (.nat_mk 2)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run shareCaseIntro true 10 = 23 := rfl
example : run shareCaseIntro false 10 = 3 := rfl

-- `fun n => Nat.rec 0 (fun m _ => m) n`: the branch reads the predecessor but not the
-- answer, so this fold is the case analysis `match n with | 0 => 0 | m + 1 => m`.
/--
error: could not synthesize default value for parameter 'hRec' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < Usage.sumN (TyWf.prim LeanPrimTy.nat) (0 + 1) (Usage.single DeBruijn.head).tail
is false
---
error: could not synthesize default value for parameter 'hStep' using tactics
---
error: Tactic `decide` proved that the proposition
  0 = 0 → Head.var ≠ Head.var
is false
-/
#guard_msgs (error) in
def foldNoAnswer :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil) (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- `(if b then fun y => y + 1 else fun y => y * 2) n` becomes
    `if b then n + 1 else n * 2`: the argument, a variable, is moved into both branches. -/
def appIfDef (b : Bool) (n : Nat) : Nat :=
  (if b then fun y => y + 1 else fun y => y * 2) n

def appIfDef_term :=
  (#leanscript_to_term appIfDef :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run appIfDef_term true 5 = 6 := rfl
example : run appIfDef_term false 5 = 10 := rfl

/--
info: ((Term.var DeBruijnProj.head.tail).bool_casesOn
      (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 1) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) appIfDef_term._proof_4 ⋯)
      (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 2) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) appIfDef_term._proof_4 ⋯)
      appIfDef_term._proof_6 appIfDef_term._proof_7).lam.lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) appIfDef_term

/-- The argument `n * n` is a computation, so it is bound first:
    `let z = n * n; if b then z + z else 0`. -/
def appIfCompDef (b : Bool) (n : Nat) : Nat :=
  (if b then fun y => y + y else fun _ => 0) (n * n)

def appIfCompDef_term :=
  (#leanscript_to_term appIfCompDef :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run appIfCompDef_term true 3 = 18 := rfl

/--
info: ((Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1))
          appIfCompDef_term._proof_1 ⋯).letE
      ((Term.var DeBruijnProj.head.tail.tail).bool_casesOn
        (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1))
          appIfCompDef_term._proof_1 ⋯)
        (Term.nat_mk 0) appIfDef_term._proof_6 appIfCompDef_term._proof_4)
      appIfCompDef_term._proof_5 ⋯ ⋯).lam.lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) appIfCompDef_term

/-- `(if b then Thunk.mk (fun _ => 5) else t).get` becomes `if b then 5 else t.get`. -/
def forceIfDef (b : Bool) (t : Thunk Nat) : Nat :=
  (if b then Thunk.mk (fun _ => 5) else t).get

def forceIfDef_term :=
  (#leanscript_to_term forceIfDef :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.thunk (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/--
info: ((Term.var DeBruijnProj.head.tail).bool_casesOn (Term.nat_mk 5)
      ((Term.var DeBruijnProj.head).thunk_force forceIfDef_term._proof_3 ⋯) appIfDef_term._proof_6
      forceIfDef_term._proof_5).lam.lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) forceIfDef_term

/-- A `match` that answers with functions, applied: the application moves into each
    branch, `match o with | some k => n + k | none => n`. -/
def appMatchDef (o : Option Nat) (n : Nat) : Nat :=
  (match o with
   | some k => fun y => y + k
   | none => fun y => y) n

def appMatchDef_term :=
  (#leanscript_to_term appMatchDef :
    Term sig0 [] _ (tyWfOf (Option Nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run appMatchDef_term ⟨⟨1, by decide⟩, (3, ())⟩ 4 = 7 := rfl
example : run appMatchDef_term ⟨⟨0, by decide⟩, ()⟩ 4 = 4 := rfl

/--
info: ((Term.var DeBruijnProj.head.tail).taggedUnion_casesOn
      (TaggedUnionCases.skip (Term.var DeBruijnProj.head)
        (CtorsWithPayloadCases.here
          (Term.externCall
            (Spine.cons (Term.var DeBruijnProj.head.tail) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1))
            appIfCompDef_term._proof_1 ⋯)
          TaggedUnionCasesRest.nil))
      appMatchDef_term._proof_3 ⋯).lam.lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) appMatchDef_term


/-- `Nat.rec` whose step reads its accumulator only in a branch that is never taken
    (`cond true …`): once that branch is gone, the fold is `match m with | 0 => 7 |
    n + 1 => n * 2`. -/
def foldNoAccDef (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 7 (fun n acc => cond true (n * 2) acc) m

def foldNoAccDef_term :=
  (#leanscript_to_term foldNoAccDef : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run foldNoAccDef_term 0 = 7 := rfl
example : run foldNoAccDef_term 5 = 8 := rfl

/--
info: ((Term.var DeBruijnProj.head).nat_casesOn (Term.nat_mk 7)
    (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 2) Spine.nil))
      (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) appIfDef_term._proof_4 ⋯)
    foldNoAccDef_term._proof_2).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) foldNoAccDef_term

/-- A two-step recursion whose recursive calls are dead: `nat_rec 1` becomes two nested
    `nat_casesOn`. -/
def deepNoAcc : Nat → Nat
  | 0 => 1
  | 1 => 2
  | n + 2 => cond true (n + 10) (deepNoAcc n + deepNoAcc (n + 1))

def deepNoAcc_term :=
  (#leanscript_to_term deepNoAcc : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run deepNoAcc_term 0 = 1 := rfl
example : run deepNoAcc_term 1 = 2 := rfl
example : run deepNoAcc_term 5 = 13 := rfl

/--
info: ((Term.var DeBruijnProj.head).nat_casesOn (Term.nat_mk 1)
    ((Term.var DeBruijnProj.head).nat_casesOn (Term.nat_mk 2)
      (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 10) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) appIfDef_term._proof_4 ⋯)
      foldNoAccDef_term._proof_2)
    foldNoAccDef_term._proof_2).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) deepNoAcc_term

/-- A two-element-window recursion on the elements of an array whose recursive calls are
    dead: `array_rec 1` becomes two nested `array_casesOn`. -/
def arrNoAcc (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 0
    | [x] => x
    | x :: y :: xs => cond true (x * 3) (go (y :: xs) + go xs)

def arrNoAcc_term :=
  (#leanscript_to_term arrNoAcc :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : run arrNoAcc_term #[] = 0 := rfl
example : run arrNoAcc_term #[4] = 4 := rfl
example : run arrNoAcc_term #[1, 2, 3] = 3 := rfl

/--
info: ((Term.var DeBruijnProj.head).array_casesOn (Term.nat_mk 0)
    ((Term.var DeBruijnProj.head.tail).array_casesOn (Term.var DeBruijnProj.head)
      (Term.externCall (Spine.cons (Term.var DeBruijnProj.head.tail.tail) (Spine.cons (Term.nat_mk 3) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) appIfDef_term._proof_4 ⋯)
      arrNoAcc_term._proof_3 ⋯)
    arrNoAcc_term._proof_3 ⋯).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) arrNoAcc_term

end TermTests.DispatchAndFold
