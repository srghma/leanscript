module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# A-normal form: where the `let`s go

`TermTests.Anf` checks that every operand of a `LeanScript.Term` is an atom and that every
intermediate computation is named by a `let`.  This file checks the two rules that make
that A-normal form **one** form per program:

* **A `let` stands where its variable is needed** (`Term.letE`'s `hPlace`,
  `LeanScript.Usage.confined`).  A `let` whose variable is read only in one branch of a
  dispatch, or only in a memoised delay, is not a term: it belongs inside that branch or
  that delay, where it runs only when it is needed.  A `let` read in two branches, or by
  something that always runs, or under a `fun` (whose body may run many times), stays.
* **A `let` in a branch does not hide what the branch answers with** (`Head.letIn`
  records the head of its body).  A-normal form writes `if c then some (f y) else none` as
  `if c then (let a = f y; some a) else none`; that dispatch still answers with a known
  constructor in every branch, so a dispatch on it is still seen to be the case-of-case
  redex it is.

The first half writes terms by hand; the second translates Lean programs with
`#leanscript_to_term`, and rewrites a hand-written term with `#leanscript_optimize`.
-/

namespace TermTests.AnfPlacement

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- The type `Bool → (Nat → Nat) → (Nat → Nat) → Nat → Nat`. -/
abbrev brTy : TyWf :=
  TyWf.prim .bool ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒
    TyWf.prim .nat ⇒ TyWf.prim .nat

/-! ## Written by hand: a `let` above the one branch that reads it is not a term -/

-- `fun c f g y => let x = f y; if c then g x else 0`
/--
error: could not synthesize default value for parameter 'hPlace' using tactics
---
error: Tactic `decide` proved that the proposition
  (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail.tail.tail.tail))
          (Usage.single DeBruijn.head.tail.tail.tail.tail +
              (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail.tail))
                  (Usage.arg (Head.var (Var.index DeBruijn.head))
                    (Usage.single DeBruijn.head.tail.tail + Usage.single DeBruijn.head))).cond +
            Usage.cond 0)).confined
      0 =
    false
is false
-/
#guard_msgs (error) in
def hoisted :=
  (.lam (.lam (.lam (.lam (.letE (.ap (.var (v♯2)) (.var (v♯0)))
      (.bool_casesOn (.var (v♯4)) (.ap (.var (v♯2)) (.var (v♯0))) (.nat_mk 0)))))) :
    Term sig0 [] _ brTy .lam)

/-- Its placed form, `fun c f g y => if c then (let x = f y; g x) else 0`, is a term. -/
def placed :=
  (.lam (.lam (.lam (.lam (.bool_casesOn (.var (v♯3))
      (.letE (.ap (.var (v♯2)) (.var (v♯0))) (.ap (.var (v♯2)) (.var (v♯0))))
      (.nat_mk 0))))) :
    Term sig0 [] _ brTy .lam)

example : run placed true (· + 1) (· * 2) 3 = 8 := rfl
example : run placed false (· + 1) (· * 2) 3 = 0 := rfl

/-- A `let` read in **both** branches stays above them:
    `fun c f g y => let x = f y; if c then g x else x`. -/
def sharedByBranches :=
  (.lam (.lam (.lam (.lam (.letE (.ap (.var (v♯2)) (.var (v♯0)))
      (.bool_casesOn (.var (v♯4)) (.ap (.var (v♯2)) (.var (v♯0))) (.var (v♯0))))))) :
    Term sig0 [] _ brTy .lam)

example : run sharedByBranches false (· + 1) (· * 2) 3 = 4 := rfl

/-- A `let` read by something that always runs and by a branch stays above the dispatch:
    `fun f n => let x = f n; let b = (x == 0); if b then 1 else x` — the test reads `x`
    whichever branch is taken. -/
def sharedByScrutinee :=
  (.lam (.lam (.letE (.ap (.var (v♯1)) (.var (v♯0)))
    (.letE (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 0) .nil))
        fun vs => .preludeExtern (.lean_nat_dec_eq__Nat_decEq vs.1 vs.2.1))
      (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.var (v♯1)))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run sharedByScrutinee (· - 3) 3 = 1 := rfl
example : run sharedByScrutinee (· - 3) 7 = 4 := rfl

/-- A `let` read under a `fun` stays outside it — the body may run many times, and the
    `let` shares the computation between the calls:
    `fun f n => let x = f n; fun m => x + m`. -/
def sharedByFun :=
  (.lam (.lam (.letE (.ap (.var (v♯1)) (.var (v♯0)))
    (.lam (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒
      TyWf.prim .nat) .lam)

example : run sharedByFun (· * 2) 3 4 = 10 := rfl

-- `fun f n => let x = f n; Thunk.mk (fun _ => x + x)`: a `let` above the memoised delay
-- that is the only place that reads it.
/--
error: could not synthesize default value for parameter 'hPlace' using tactics
---
error: Tactic `decide` proved that the proposition
  (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) + 0)).cond.confined
      0 =
    false
is false
-/
#guard_msgs (error) in
def hoistedOverThunk :=
  (.lam (.lam (.letE (.ap (.var (v♯1)) (.var (v♯0)))
    (.thunk_mk (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
      TyWf.thunk (TyWf.prim .nat)) .lam)

/-- Its placed form, `fun f n => Thunk.mk (fun _ => let x = f n; x + x)`, is a term: `f n`
    runs only if the thunk is forced. -/
def placedInThunk :=
  (.lam (.lam (.thunk_mk (.letE (.ap (.var (v♯1)) (.var (v♯0)))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
      TyWf.thunk (TyWf.prim .nat)) .lam)

/-! ## Written by hand: a `let` in a branch does not hide a case-of-case redex -/

/-- The schema of a pair of naturals. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

-- `fun c n => let p = (if c then (let a = n * n; (a, n)) else (n, n)); match p with
-- | (x, y) => x + y`: the dispatch bound to `p` answers with a pair in both branches —
-- one of them behind a `let` — so the `match` on `p` is a case of case.
/--
error: could not synthesize default value for parameter 'hKnownLet' using tactics
---
error: Tactic `decide` proved that the proposition
  ((Head.ctorOf [Head.var (Var.index DeBruijn.head), Head.var (Var.index DeBruijn.head.tail)]).letIn.join
          (Head.ctorOf [Head.var (Var.index DeBruijn.head), Head.var (Var.index DeBruijn.head)])).letKnown
      (TyWf.record pairSchema)
      (Usage.scrutinize (Head.var (Var.index DeBruijn.head))
        (Usage.single DeBruijn.head +
          Usage.drop pairSchema.toList
            (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
              (Usage.arg (Head.var (Var.index DeBruijn.head.tail)) (Usage.single DeBruijn.head.tail) + 0)))) =
    false
is false
-/
#guard_msgs (error) in
noncomputable def caseOfCaseBehindLet :=
  (.lam (.lam (.letE
    (.bool_casesOn (.var (v♯1))
      (.letE (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
          fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
        (.record_mk pairSchema (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))))
      (.record_mk pairSchema (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))))
    (.record_casesOn (.var (v♯0))
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- Its optimized form, `fun c n => if c then (let a = n * n; a + n) else n + n`. -/
def caseOfCaseReduced :=
  (.lam (.lam (.bool_casesOn (.var (v♯1))
    (.letE (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_mul vs.1 vs.2.1))
      (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run caseOfCaseReduced true 3 = 12 := rfl
example : run caseOfCaseReduced false 3 = 6 := rfl

/-! ## Translated: `#leanscript_to_term` places every `let` -/

/-- A `let` written above an `if`, read in one branch. -/
def br2 (c : Bool) (f g : Nat → Nat) (y : Nat) : Nat :=
  let x := f y
  if c then g x else 0

/-- It is moved into that branch: the translation is `placed`. -/
def br2_term := (#leanscript_to_term br2 : Term sig0 [] _ brTy .lam)

example : br2_term = placed := rfl

/-- Two `let`s: one read in both branches, one only in a nested branch. -/
def deep (c d : Bool) (f : Nat → Nat) (y : Nat) : Nat :=
  let x := f y
  let z := f (y + 1)
  if c then (if d then x + z else x) else z

/-- `z` stays on top (read in both branches, and `y + 1` with it, which only `z` reads);
    `x` moves into the `then` branch, above the inner `if`, both of whose branches read
    it. -/
def deep_term :=
  (#leanscript_to_term deep :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒
      TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/--
info: (((((Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 1) Spine.nil))
                      (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯).letE
                  (((Term.var DeBruijnProj.head.tail.tail).ap (Term.var DeBruijnProj.head) ⋯ ⋯).letE
                    ((Term.var DeBruijnProj.head.tail.tail.tail.tail.tail).bool_casesOn
                      (((Term.var DeBruijnProj.head.tail.tail.tail).ap (Term.var DeBruijnProj.head.tail.tail) ⋯ ⋯).letE
                        ((Term.var DeBruijnProj.head.tail.tail.tail.tail.tail).bool_casesOn
                          (Term.externCall
                            (Spine.cons (Term.var DeBruijnProj.head)
                              (Spine.cons (Term.var DeBruijnProj.head.tail) Spine.nil))
                            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯)
                          (Term.var DeBruijnProj.head) ⋯ ⋯ ⋯ ⋯ ⋯)
                        ⋯ ⋯ ⋯ ⋯ ⋯)
                      (Term.var DeBruijnProj.head) ⋯ ⋯ ⋯ ⋯ ⋯)
                    ⋯ ⋯ ⋯ ⋯ ⋯)
                  deep_term._proof_32 ⋯ ⋯ ⋯ ⋯).lam
              ⋯).lam
          ⋯).lam
      ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) deep_term

example : run deep_term true true (· + 1) 3 = 9 := rfl
example : run deep_term true false (· + 1) 3 = 4 := rfl
example : run deep_term false true (· + 1) 3 = 5 := rfl

/-- A `let` read only in a thunk. -/
def thk (f : Nat → Nat) (y : Nat) : Thunk Nat :=
  let x := f y
  Thunk.mk (fun _ => x + x)

/-- It is moved into the thunk: the translation is `placedInThunk`. -/
def thk_term :=
  (#leanscript_to_term thk :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
      TyWf.thunk (TyWf.prim .nat)) .lam)

example : thk_term = placedInThunk := rfl

/-- A dispatch on a dispatch one of whose branches A-normal form writes with a `let`. -/
def coc (c : Bool) (n : Nat) : Nat :=
  match (if c then (n * n, n) else (n, n)) with
  | (x, y) => x + y

/-- The case of case is reduced: the translation is `caseOfCaseReduced`. -/
def coc_term :=
  (#leanscript_to_term coc : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : coc_term = caseOfCaseReduced := rfl

/-- The same through an `Option`. -/
def cocOpt (c : Bool) (f : Nat → Nat) (y : Nat) : Nat :=
  match (if c then some (f y) else none) with
  | some x => x + 1
  | none => 0

/-- `fun c f y => if c then (let a = f y; a + 1) else 0`: no `Option` is built. -/
def cocOpt_term :=
  (#leanscript_to_term cocOpt :
    Term sig0 [] _ (TyWf.prim .bool ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
      TyWf.prim .nat) .lam)

example : cocOpt_term =
    (.lam (.lam (.lam (.bool_casesOn (.var (v♯2))
      (.letE (.ap (.var (v♯1)) (.var (v♯0)))
        (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 1) .nil))
          fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))
      (.nat_mk 0)))) :
      Term sig0 [] _ (TyWf.prim .bool ⇒ (TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
        TyWf.prim .nat) .lam) := rfl

example : run cocOpt_term true (· * 3) 2 = 7 := rfl
example : run cocOpt_term false (· * 3) 2 = 0 := rfl

/-! ## `#leanscript_optimize` places the `let`s of a hand-written term -/

/-- `hoisted`, rewritten: it is `placed`. -/
example : (#leanscript_optimize
    (.lam (.lam (.lam (.lam (.letE (.ap (.var (v♯2)) (.var (v♯0)))
      (.bool_casesOn (.var (v♯4)) (.ap (.var (v♯2)) (.var (v♯0))) (.nat_mk 0))))))) :
    Term sig0 [] _ brTy _) = placed := rfl

end TermTests.AnfPlacement
