module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# Closed computations are written as their values

A computation that reads no variable and no top-level declaration — a **closed**
computation (`LeanScript.Usage.closed`) — has a value that is known where the term is
written.  When that value can be written back as a term (`LeanScript.TyWf.quotable`), the
computation is a redex: the grammar rejects it (`hClosed`, `LeanScript.Head.closedComp`),
and `#leanscript_to_term` computes the value instead.

This covers what the rule for externs on values did not: a fold on a literal, a `let` of
a value read by a computation, a closed computation under a `fun` (which would otherwise
be recomputed at every call).  A reference to a top-level declaration is **not** closed —
its value is only known when the term runs — and a `let` or a constructor of a closed
value is not a computation, so both stay.
-/

namespace TermTests.ClosedComputation

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- A signature with one declaration, `add : nat ⇒ nat ⇒ nat`. -/
def sigAdd : Sig := ⟨[⟨"add", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-! ## The translation computes closed folds -/

/-- A structural recursion, inlined at its call sites. -/
@[inline] def sumBelow : Nat → Nat
  | 0 => 0
  | n + 1 => sumBelow n + n

/-- `sumBelow 5` is a fold on the literal `5`: it is written as its value. -/
def sum5 : Nat := sumBelow 5

def sum5_term := (#leanscript_to_term sum5 : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : sum5_term = .nat_mk 10 := rfl
example : run sum5_term = sum5 := rfl

/-- Under a `fun`, the closed fold `sumBelow 4` would run at every call; it is computed
    once, where the term is written. -/
def addSum4 (x : Nat) : Nat := x + sumBelow 4

def addSum4_term :=
  (#leanscript_to_term addSum4 : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : addSum4_term =
    .lam (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 6) .nil))
      (fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) := rfl
example : run addSum4_term 10 = addSum4 10 := rfl

/-- The fold still runs where its argument is not known. -/
def sumBelowFn (n : Nat) : Nat := sumBelow n

def sumBelowFn_term :=
  (#leanscript_to_term sumBelowFn : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Is this term `fun n => nat_rec …`? -/
def isNatRecFn {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {h : Head} : Term sig0 Γ u τ h → Bool
  | .lam (.nat_rec ..) _ => true
  | _ => false

example : isNatRecFn sumBelowFn_term = true := rfl
example : run sumBelowFn_term 5 = 10 := rfl

/-- A structural recursion on a list, inlined. -/
@[inline] def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- `sumList [1, 2, 3]` folds over a literal list: it is written as its value. -/
def sumOneTwoThree : Nat := sumList [1, 2, 3]

def sumOneTwoThree_term :=
  (#leanscript_to_term sumOneTwoThree : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : sumOneTwoThree_term = .nat_mk 6 := rfl

/-! ## The grammar rejects closed computations -/

-- A fold on a literal whose branch reads no free name is rejected…
/--
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp
      (Usage.arg Head.lit 0 + (Usage.arg Head.lit 0 + 0) +
        (Usage.dropN (TyWf.prim LeanPrimTy.nat) (0 + 1)
            (Usage.arg (Head.var (Var.index DeBruijn.head.tail)) (Usage.single DeBruijn.head.tail) +
                (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0)).tail).many)
      (TyWf.prim LeanPrimTy.nat) Head.comp =
    false
is false
---
error: (kernel) declaration has metavariables 'TermTests.ClosedComputation.foldOnLiteral'
-/
#guard_msgs (error) in
def foldOnLiteral :=
  (.nat_rec 0 (.nat_mk 5) (.cons (.nat_mk 0) .nil)
    (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
      (fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term sig0 [] _ (TyWf.prim .nat) .comp)

/-- …and its value is accepted. -/
example : Term sig0 [] 0 (TyWf.prim .nat) .lit := .nat_mk 10

/-- The same fold on a variable is not closed, and is accepted. -/
def foldOnVar :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil)
    (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
      (fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run foldOnVar 5 = 10 := rfl

/-- A fold on a literal whose branch calls a top-level declaration is not closed — the
    declaration's value is only known when the term runs — and is accepted. -/
def foldWithGlobal :=
  (.nat_rec 0 (.nat_mk 5) (.cons (.nat_mk 0) .nil)
    (.ap (.ap (.global .here) (.var (v♯1))) (.var (v♯0))) :
    Term sigAdd [] _ (TyWf.prim .nat) .comp)

-- A `let` of a literal array read by an extern is a closed computation, and rejected.
/--
error: could not synthesize default value for parameter 'hAnf' using tactics
---
error: Expected type must not contain metavariables
  Head.allAtom [Head.var (Var.index DeBruijn.head), Head.ctorOf [Head.var (Var.index DeBruijn.head)]] = true
---
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Expected type must not contain metavariables
  (Head.ctorOf [Head.lit, Head.lit]).letUsed
      (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
          (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
              (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
            0)).head
      ((Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
            (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
                (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
              0)).opnd
        0) =
    true
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Expected type must not contain metavariables
  Head.closedComp
      ((Usage.arg Head.lit 0 + (Usage.arg Head.lit 0 + 0)).letU
        (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
          (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
              (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
            0)))
      (Coe.coe (LeanPrimTyCovariant.array (TyWf.prim LeanPrimTy.nat).array)) Head.comp =
    false
---
error: could not synthesize default value for parameter 'hKnownLet' using tactics
---
error: Expected type must not contain metavariables
  (Head.ctorOf [Head.lit, Head.lit]).letKnown (TyWf.prim LeanPrimTy.nat).array
      (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
        (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
          0)) =
    false
---
error: could not synthesize default value for parameter 'hPlace' using tactics
---
error: Expected type must not contain metavariables
  (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
          (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
              (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
            0)).confined
      0 =
    false
---
error: Type mismatch
  (Term.array_mk (Terms.cons (Term.nat_mk 1) (Terms.cons (Term.nat_mk 2) Terms.nil)) letValueComp._proof_1).letE
    (Term.externCall
      (Spine.cons (Term.var DeBruijn.head)
        (Spine.cons (Term.array_mk (Terms.cons (Term.var DeBruijn.head) Terms.nil) ⋯) Spine.nil))
      (fun vs =>
        LeanInitPureExtern.preludeExtern (PreludeExtern.lean_array_push (TyWf.prim LeanPrimTy.nat).array vs.2.1 vs.1))
      ⋯ ?m.121 ⋯)
    letValueComp._proof_7 ?m.124 ?m.125 ?m.126 ?m.127
has type
  Term ?m.93 ?m.88
    ((Usage.arg Head.lit 0 + (Usage.arg Head.lit 0 + 0)).letU
      (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
        (Usage.arg (Head.ctorOf [Head.var (Var.index DeBruijn.head)])
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0) +
          0)))
    (Coe.coe (LeanPrimTyCovariant.array (TyWf.prim LeanPrimTy.nat).array)) Head.comp.letIn
but is expected to have type
  Term sig0 [] ?m.129 (TyWf.prim LeanPrimTy.nat).array.array Head.comp
-/
#guard_msgs (error) in
def letValueComp :=
  (.letE (.array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) .nil)))
    (.externCall (.cons (.var (v♯0)) (.cons (.array_mk (.cons (.var (v♯0)) .nil)) .nil))
      (fun vs => .preludeExtern (.lean_array_push (TyWf.array (TyWf.prim .nat)) vs.2.1 vs.1))) :
    Term sig0 [] _ (TyWf.array (TyWf.array (TyWf.prim .nat))) .comp)

/-- A `let` that shares a closed value in a constructor is not a computation, and is
    accepted: `let x = #[1, 2]; (x, x)`. -/
def shareValue :=
  (.letE (.array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) .nil)))
    (.record_mk ⟨TyWf.array (TyWf.prim .nat), TyWf.array (TyWf.prim .nat), []⟩
      (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))) :
    Term sig0 [] _ (.record ⟨TyWf.array (TyWf.prim .nat), TyWf.array (TyWf.prim .nat), []⟩)
      (.letIn _))

end TermTests.ClosedComputation

end
