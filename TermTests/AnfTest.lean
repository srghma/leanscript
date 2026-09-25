module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Terms are in A-normal form by construction

`LeanScript.Term` accepts only terms in **A-normal form**: every operand is an **atom**
(`LeanScript.Head.isAtom` — a variable, a declaration, a literal, a closed value or a
`fun`), every scrutinee and every forced term is a **name** (`LeanScript.Head.isName`),
what an application calls is a name or another application
(`LeanScript.Head.isCallee`), and a `let` never binds another `let`.  Every
intermediate computation is named by a `let` — and only there: a `let` is kept only when
its variable is shared or read as an operand (`LeanScript.Head.letUsed`).

The first half writes terms by hand: the direct forms are rejected, and their A-normal
forms accepted.  The second half translates Lean programs with `#leanscript_to_term`,
which emits the A-normal form.
-/

namespace TermTests.Anf

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Written by hand: the direct forms are not terms -/

-- `fun n => (n + n) + n`: an argument of an extern that is a computation.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.isAtom = true
is false
-/
#guard_msgs (error) in
def nestedExtern :=
  (.lam (.externCall
    (.consT (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
      (.cons (.var (v♯0)) .nil))
    fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Its A-normal form, `fun n => let x = n + n; x + n`, is a term. -/
def nestedExternAnf :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run nestedExternAnf 5 = 15 := rfl

-- `fun f g n => f (g n)`: an argument of an application that is a computation.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  ((Head.var (Var.index DeBruijn.head.tail.tail)).isCallee &&
      (Head.app (Head.var (Var.index DeBruijn.head)).isVar0).isAtom) =
    true
is false
-/
#guard_msgs (error) in
def nestedApp :=
  (.lam (.lam (.lam (.ap (.var (v♯2)) (.ap (.var (v♯1)) (.var (v♯0)))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒
      TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Its A-normal form, `fun f g n => let x = g n; f x`, is a term. -/
def nestedAppAnf :=
  (.lam (.lam (.lam (.letE (.ap (.var (v♯1)) (.var (v♯0))) (.ap (.var (v♯3)) (.var (v♯0)))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒
      TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run nestedAppAnf (· * 2) (· + 1) 4 = 10 := rfl

-- `fun n => if n < 3 then 1 else 0`: a dispatch on a computation.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.isName = true
is false
-/
#guard_msgs (error) in
def testComputation :=
  (.lam (.bool_casesOn
    (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 3) .nil))
      fun vs => .preludeExtern (.lean_nat_dec_lt vs.1 vs.2.1))
    (.nat_mk 1) (.nat_mk 0)) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Its A-normal form, `fun n => let b = n < 3; if b then 1 else 0`, is a term: the
    variable of the `let` is read once, as the scrutinee, which is an operand. -/
def testComputationAnf :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 3) .nil))
      fun vs => .preludeExtern (.lean_nat_dec_lt vs.1 vs.2.1))
    (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run testComputationAnf 2 = 1 := rfl
example : run testComputationAnf 7 = 0 := rfl

-- `fun n => (n * n, n + 1)`: fields of a constructor that are computations.
/-- The schema of a pair of naturals. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.isAtom = true
is false
---
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.isAtom = true
is false
-/
#guard_msgs (error) in
def pairOfComputations :=
  (.lam (.record_mk pairSchema
    (.consT (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
      (.consT (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 1) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) .nil))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.record pairSchema) .lam)

/-- Its A-normal form, `fun n => let a = n * n; let b = n + 1; (a, b)`, is a term. -/
def pairOfComputationsAnf :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
    (.letE
      (.externCall (.cons (.var (v♯1)) (.cons (.nat_mk 1) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
      (.record_mk pairSchema (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.record pairSchema) .lam)

-- `fun n => let x = (let y = n + n; y * y); x + x`: a `let` that binds a `let`.
/--
error: could not synthesize default value for parameter 'hValue' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.letIn.isBindable = true
is false
-/
#guard_msgs (error) in
def letOfLet :=
  (.lam (.letT
    (.letE
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1)) :
      Term sig0 [TyWf.prim .nat] _ (TyWf.prim .nat) _)
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Its A-normal form, `fun n => let y = n + n; let x = y * y; x + x`, is a term. -/
def letOfLetAnf :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.letE
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run letOfLetAnf 3 = 72 := rfl

-- A `let` whose variable is read once, and not as an operand, is not A-normal form's:
-- `fun n => let x = n + n; x` is `fun n => n + n`.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.comp.letUsed (Usage.single DeBruijn.head).head ((Usage.single DeBruijn.head).opnd 0) = true
is false
-/
#guard_msgs (error) in
def letNotNeeded :=
  (.lam (.letE
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
    (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-! ## Translated: `#leanscript_to_term` emits the A-normal form -/

/-- A sum of two products. -/
def sumSq (a b : Nat) : Nat := a * a + b * b

/-- `fun a b => let x = a * a; let y = b * b; x + y`. -/
def sumSq_term :=
  (#leanscript_to_term sumSq :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : sumSq_term =
    (.lam (.lam (.letE
      (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯1)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
      (.letE
        (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯1)) .nil))
          fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
        (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
          fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
      Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam) := rfl

example : run sumSq_term 3 4 = 25 := rfl

/-- A function applied to its own result. -/
def applyTwice (f : Nat → Nat) (n : Nat) : Nat := f (f n)

/-- `fun f n => let x = f n; f x`. -/
def applyTwice_term :=
  (#leanscript_to_term applyTwice :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : applyTwice_term =
    (.lam (.lam (.letE (.ap (.var (v♯1)) (.var (v♯0))) (.ap (.var (v♯2)) (.var (v♯0))))) :
      Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat)
        .lam) := rfl

example : run applyTwice_term (· + 3) 1 = 7 := rfl

/-- A test on a computation. -/
def smallTimesSix (n : Nat) : Nat := if n < 3 then n * 6 else 0

/-- The test is bound by a `let` before it is taken apart. -/
def smallTimesSix_term :=
  (#leanscript_to_term smallTimesSix : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/--
info: Term.atom
  (Atom.lam
    (Term.letE
      (Comp.externCall (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) (Spine.cons (Atom.nat_mk 3) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_dec_lt vs.1 vs.2.1)) ⋯ ⋯)
      (Term.comp
        (Comp.bool_casesOn (Ref.var DeBruijnProj.head)
          (Term.comp
            (Comp.externCall
              (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail)) (Spine.cons (Atom.nat_mk 6) Spine.nil))
              (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯)
            sumSq_term._proof_9)
          (Term.atom (Atom.nat_mk 0)) smallTimesSix_term._proof_5 smallTimesSix_term._proof_6 ⋯ ⋯)
        smallTimesSix_term._proof_9)
      ⋯ ⋯ ⋯ ⋯)
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) smallTimesSix_term

example : run smallTimesSix_term 2 = 12 := rfl
example : run smallTimesSix_term 5 = 0 := rfl

/-- A pair of computations. -/
def squareAndSucc (n : Nat) : Nat × Nat := (n * n, n + 1)

/-- The fields are bound by `let`s, and the pair holds their variables. -/
def squareAndSucc_term :=
  (#leanscript_to_term squareAndSucc :
    Term sig0 [] _ (TyWf.prim .nat ⇒ tyWfOf (Nat × Nat)) .lam)

/--
info: Term.atom
  (Atom.lam
    (Term.letE
      (Comp.externCall
        (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head))
          (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯)
      (Term.letE
        (Comp.externCall (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail)) (Spine.cons (Atom.nat_mk 1) Spine.nil))
          (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯)
        (Term.comp
          (Comp.record_mk
            { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := sumSq_term._proof_1 },
              snd := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := sumSq_term._proof_1 }, rest := [] }
            (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head.tail))
              (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) Spine.nil)))
          ⋯)
        ⋯ ⋯ ⋯ ⋯)
      ⋯ ⋯ ⋯ ⋯)
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) squareAndSucc_term

example : run squareAndSucc_term 4 = ((16, 5, PUnit.unit) : Nat × Nat × PUnit) := rfl

/-- A computation read once, in a branch: it is not bound (a branch is not an operand). -/
def branchComputation (b : Bool) (n : Nat) : Nat := if b then n * n else n

/-- `fun b n => if b then n * n else n`: no `let`. -/
def branchComputation_term :=
  (#leanscript_to_term branchComputation :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : branchComputation_term =
    (.lam (.lam (.bool_casesOn (.var (v♯1))
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
      (.var (v♯0)))) :
      Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam) := rfl

end TermTests.Anf
