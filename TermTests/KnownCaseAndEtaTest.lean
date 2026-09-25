module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Three more redexes: η, a dispatch whose branches are the same leaf, and a known case

* **η-redex**: `fun x => f x`, where `f` does not read `x`, is `f`.  The head of an
  application records whether its argument is the innermost variable (`Head.app`), and
  `Term.lam` asks that its body is not such an application that reads the variable only
  there (`hEta`, `Head.isEtaRedex`).  The translation already η-reduced; now the grammar
  rejects the redex too.
* **The same leaf in both branches**: `if c then x else x` is `x`, and
  `if c then b else b` is `b` for a boolean literal `b` — which is what `c || true` and
  `c && false` are.  The head of a variable records its de Bruijn index (`Head.var`), so
  `Term.bool_casesOn` can ask that its branches are not the same leaf (`hSame`,
  `Head.sameLeaf`).
* **Case of a known constructor, on a variable**: a dispatch on a variable `x` inside a
  branch of a dispatch on `x` is a redex — in that branch the constructor of `x` is known,
  and its fields are bound.  The grade vector counts, for each variable, how many times it
  is taken apart (`Usage.scrut`, `Usage.scrutinize`), and a dispatch on a variable asks
  that its branches do not take it apart again (`hKnown`, `Head.rescrutinizes`).  The
  translation replaces each inner dispatch by its branch for the known constructor
  (`knownCase?`).  This covers `Bool`, enums, records, tagged unions and recursive ones;
  the default branch of a partial dispatch knows no constructor, and is not concerned.

Each translation is checked against the Lean function by `rfl`, and its shape by a
printed snapshot.
-/

namespace TermTests.KnownCaseAndEta

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- The type of `Option Nat`. -/
abbrev optNat : TyWf := tyWfOf (Option Nat)

/-- The type of `Nat × Nat`. -/
abbrev pairNat : TyWf := tyWfOf (Nat × Nat)

/-- A record of two naturals, written out, for terms written by hand. -/
abbrev pairRec : TyWf := TyWf.record ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/-! ## Written by hand: what the grammar accepts and rejects -/

-- `fun f x => f x`: the inner `fun` is `f`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.app (Head.var (Var.index DeBruijn.head)).isVar0).isEtaRedex
      (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
          (Usage.arg (Head.var (Var.index DeBruijn.head))
            (Usage.single DeBruijn.head.tail + Usage.single DeBruijn.head))).head =
    false
is false
-/
#guard_msgs (error) in
def etaApply :=
  (.lam (.lam (.ap (.var (v♯1)) (.var (v♯0)))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun f => f`, the η-reduced form, is a term. -/
def etaReduced :=
  (.lam (.var (v♯0)) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun f x => f x x`: the function applied to `x` reads `x` too, so this is not an
    η-redex. -/
def notEtaTwice :=
  (.lam (.lam (.ap (.ap (.var (v♯1)) (.var (v♯0))) (.var (v♯0)))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒
      TyWf.prim .nat) .lam)

/-- `fun f y x => f y`: the argument is not the variable the `fun` binds. -/
def notEtaOther :=
  (.lam (.lam (.lam (.ap (.var (v♯2)) (.var (v♯1))))) :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒
      TyWf.prim .nat) .lam)

example : run notEtaTwice (· + ·) 4 = 8 := rfl
example : run notEtaOther (· * 3) 4 5 = 12 := rfl

-- `fun c x => if c then x else x`: both branches are `x`.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).sameLeaf (Head.var (Var.index DeBruijn.head)) = false
is false
-/
#guard_msgs (error) in
def ifSameVar :=
  (.lam (.lam (.bool_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- `fun c => if c then true else true`, which is what `c || true` is.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.bool true).sameLeaf (Head.bool true) = false
is false
-/
#guard_msgs (error) in
def ifSameBool :=
  (.lam (.bool_casesOn (.var (v♯0)) (.bool_mk true) (.bool_mk true)) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

/-- `fun c x y => if c then x else y`: two different variables, a term. -/
def ifTwoVars :=
  (.lam (.lam (.lam (.bool_casesOn (.var (v♯2)) (.var (v♯1)) (.var (v♯0))))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifTwoVars true 1 2 = 1 := rfl
example : run ifTwoVars false 1 2 = 2 := rfl

-- `fun c x => if c then (if c then x else 2) else 3`: in the outer `then` branch, `c` is
-- known to be `true`.
/--
error: could not synthesize default value for parameter 'hKnown' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head.tail)).rescrutinizes
      (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
          (Usage.single DeBruijn.head.tail + (Usage.single DeBruijn.head).cond + Usage.cond 0) +
        0) =
    false
is false
---
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head.tail)).readsScrutinee
      (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail))
          (Usage.single DeBruijn.head.tail + (Usage.single DeBruijn.head).cond + Usage.cond 0) +
        0) =
    false
is false
-/
#guard_msgs (error) in
def ifIfSame :=
  (.lam (.lam (.bool_casesOn (.var (v♯1))
    (.bool_casesOn (.var (v♯1)) (.var (v♯0)) (.nat_mk 2)) (.nat_mk 3))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun c d x => if c then (if d then x else 2) else 3`: the inner `if` is on another
    variable, a term. -/
def ifIfOther :=
  (.lam (.lam (.lam (.bool_casesOn (.var (v♯2))
    (.bool_casesOn (.var (v♯1)) (.var (v♯0)) (.nat_mk 2)) (.nat_mk 3)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifIfOther true false 1 = 2 := rfl

-- `fun p => match p with | (a, b) => match p with | (c, d) => c + a`: in the branch, `p`
-- is known to be `(a, b)`.
/--
error: could not synthesize default value for parameter 'hKnown' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).rescrutinizes
      (Usage.drop { fst := TyWf.prim LeanPrimTy.nat, snd := TyWf.prim LeanPrimTy.nat, rest := [] }.toList
        (Usage.scrutinize (Head.var (Var.index DeBruijn.head.tail.tail))
          (Usage.single DeBruijn.head.tail.tail +
            Usage.drop { fst := TyWf.prim LeanPrimTy.nat, snd := TyWf.prim LeanPrimTy.nat, rest := [] }.toList
              (Usage.arg (Head.var (Var.index DeBruijn.head)) (Usage.single DeBruijn.head) +
                (Usage.arg (Head.var (Var.index DeBruijn.head.tail.tail)) (Usage.single DeBruijn.head.tail.tail) +
                  0))))) =
    false
is false
-/
#guard_msgs (error) in
def pairTwice :=
  (.lam (.record_casesOn (.var (v♯0)) (.record_casesOn (.var (v♯2))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯2)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (pairRec ⇒ TyWf.prim .nat) .lam)

/-- `fun p => let a = (match p with | (a, _) => a); let b = (match p with | (_, b) => b); a + b`:
    two dispatches on `p` side by side, neither inside the other, are terms (in A-normal form
    each is bound by a `let` before it is added). -/
def pairSideBySide :=
  (.lam (.letE (.record_casesOn (.var (v♯0)) (.var (v♯0)))
    (.letE (.record_casesOn (.var (v♯1)) (.var (v♯1)))
      (.externCall (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil))
        fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)))) :
    Term sig0 [] _ (pairRec ⇒ TyWf.prim .nat) .lam)

example : run pairSideBySide (cast (Ty.denRecord_eq _).symm ((3, 4, ()) : Nat × Nat × Unit)) =
    7 := rfl

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- `b || true` is `true`. -/
def orTrue (b : Bool) : Bool := b || true

def orTrue_term := (#leanscript_to_term orTrue : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

example : run orTrue_term false = true := rfl

/--
info: (Term.bool_mk true).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) orTrue_term

/-- `b && false` is `false`. -/
def andFalse (b : Bool) : Bool := b && false

def andFalse_term :=
  (#leanscript_to_term andFalse : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

example : run andFalse_term true = false := rfl

/--
info: (Term.bool_mk false).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) andFalse_term

/-- `if b then n else n` is `n`. -/
def ifSame (b : Bool) (n : Nat) : Nat := if b then n else n

def ifSame_term :=
  (#leanscript_to_term ifSame : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifSame_term true 4 = 4 := rfl

/--
info: ((Term.var DeBruijnProj.head).lam ⋯).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) ifSame_term

/-- `if b then (if b then n else 2) else 3` is `if b then n else 3`. -/
def ifIf (b : Bool) (n : Nat) : Nat := if b then (if b then n else 2) else 3

def ifIf_term :=
  (#leanscript_to_term ifIf : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifIf_term true 5 = 5 := rfl
example : run ifIf_term false 5 = 3 := rfl

/--
info: (((Term.var DeBruijnProj.head.tail).bool_casesOn (Term.var DeBruijnProj.head) (Term.nat_mk 3) ⋯ ⋯ ⋯ ⋯ ⋯).lam ⋯).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) ifIf_term

/-- `if b then (if b then n else m) else (if b then 1 else m)`: both inner `if`s are known,
    and what is left, `if b then n else m`, is one `if`. -/
def ifIfBoth (b : Bool) (n m : Nat) : Nat :=
  if b then (if b then n else m) else (if b then 1 else m)

def ifIfBoth_term :=
  (#leanscript_to_term ifIfBoth :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifIfBoth_term true 5 6 = 5 := rfl
example : run ifIfBoth_term false 5 6 = 6 := rfl

/--
info: ((((Term.var DeBruijnProj.head.tail.tail).bool_casesOn (Term.var DeBruijnProj.head.tail) (Term.var DeBruijnProj.head) ⋯
              ⋯ ⋯ ⋯ ⋯).lam
          ⋯).lam
      ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) ifIfBoth_term

/-- `match o with | some x => x + o.getD 0 | none => 1`: in the `some x` branch, `o.getD 0`
    is `x`, so the branch is `x + x`. -/
def optTwice (o : Option Nat) : Nat :=
  match o with
  | some x => x + o.getD 0
  | none => 1

def optTwice_term :=
  (#leanscript_to_term optTwice : Term sig0 [] _ (optNat ⇒ TyWf.prim .nat) .lam)

example : run optTwice_term ⟨⟨1, by decide⟩, (3, ())⟩ = 6 := rfl
example : run optTwice_term ⟨⟨0, by decide⟩, ()⟩ = 1 := rfl

/--
info: ((Term.var DeBruijnProj.head).taggedUnion_casesOn
      (TaggedUnionCases.skip (Term.nat_mk 1)
        (CtorsWithPayloadCases.here
          (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head) Spine.nil))
            (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1)) ⋯ ⋯ ⋯)
          TaggedUnionCasesRest.nil))
      ⋯ ⋯ ⋯ optTwice_term._proof_8 ⋯ optTwice_term._proof_10).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) optTwice_term

/-- A projection of a pair inside a `match` on it: `match p with | (a, _) => a * p.2` is
    `match p with | (a, b) => a * b`. -/
def pairProj (p : Nat × Nat) : Nat :=
  match p with
  | (a, _) => a * p.2

def pairProj_term :=
  (#leanscript_to_term pairProj : Term sig0 [] _ (pairNat ⇒ TyWf.prim .nat) .lam)

example : run pairProj_term (cast (Ty.denRecord_eq _).symm ((3, 4, ()) : Nat × Nat × Unit)) =
    12 := rfl

/--
info: ((Term.var DeBruijnProj.head).record_casesOn
      (Term.externCall
        (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.var DeBruijnProj.head.tail) Spine.nil))
        (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_mul vs.1 vs.2.1)) ⋯ ⋯ ⋯)
      ⋯ ⋯ ⋯ ⋯ pairProj_term._proof_9).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) pairProj_term

/-- `fun f x => f x`, applied under another binder: `fun g => (fun x => g x)` is
    `fun g => g`. -/
def etaDef (g : Nat → Nat) : Nat → Nat := fun x => g x

def etaDef_term :=
  (#leanscript_to_term etaDef :
    Term sig0 [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run etaDef_term (· + 1) 4 = 5 := rfl

/--
info: (Term.var DeBruijnProj.head).lam ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) etaDef_term

end TermTests.KnownCaseAndEta
