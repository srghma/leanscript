module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# Two more redexes: a dispatch that reads no field, and a fold whose step is the identity

* **A dispatch on a value with one constructor whose branch reads none of the fields** — a
  record, a recursive record or newtype, or a primitive wrapper (`Char`, `UInt8`, …,
  `Float`, `String.Pos.Raw`, `Substring.Raw`, …) — does not need the value taken apart: the
  language is pure and total, so `match p with | (a, b) => e`, where `e` reads neither `a`
  nor `b`, is `e`.  `Term.record_casesOn`, `Term.recObject_casesOn`,
  `Term.recAlias_casesOn` and every primitive `…_casesOn` with one branch ask that the
  branch reads at least one field (`hUsed`, counted with `Usage.front`), and the
  translation drops such a dispatch.  (A dispatch with several branches still decides
  which branch runs, so it is not concerned.)
* **A one-step fold whose branch is the answer it is given** — `Nat.rec b (fun _ ih => ih)`,
  or the fold of an array whose branch is the answer over the tail — is its base value,
  at every argument.  `Term.nat_rec` and `Term.array_rec` at depth `0` ask that their
  branch is not a variable (`hStep`): such a branch reads an answer (`hRec`), so it *is*
  the answer.  The translation writes the base instead.

Both redexes are found in programs as they are written (`constDown` of
`TermTests/ToTermTest/Recursion.lean` used to translate to `nat_rec 0 n 7 (fun _ ih => ih)`)
and, more often, once dead code is removed (`cond true …` below).
-/

namespace TermTests.UnusedFieldsAndIdFold

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-! ## Written by hand: what the grammar rejects -/

-- `fun p => match p with | (a, b) => 0`: the branch reads neither field.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < Usage.front { fst := TyWf.prim LeanPrimTy.nat, snd := TyWf.prim LeanPrimTy.nat, rest := [] }.toList 0
is false
-/
#guard_msgs (error) in
def recordIgnored :=
  (.lam (.record_casesOn (.var (v♯0)) (.nat_mk 0)) :
    Term sig0 [] _
      (TyWf.record ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩ ⇒ TyWf.prim .nat) .lam)

/-- `fun p => match p with | (a, b) => b`, a projection, reads a field and is a term. -/
def recordSnd :=
  (.lam (.record_casesOn (.var (v♯0)) (.var (v♯1))) :
    Term sig0 [] _
      (TyWf.record ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩ ⇒ TyWf.prim .nat) .lam)

example : run recordSnd (cast (Ty.denRecord_eq _).symm ((3, 4, ()) : Nat × Nat × Unit)) = 4 :=
  rfl

-- `fun s n => match s with | ⟨str, start, stop⟩ => n`: the branch reads none of the three
-- fields of the substring.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  0 <
    Usage.front [TyWf.prim LeanPrimTy.string, TyWf.prim LeanPrimTy.stringPosRaw, TyWf.prim LeanPrimTy.stringPosRaw]
      (Usage.single DeBruijn.head.tail.tail.tail)
is false
-/
#guard_msgs (error) in
def substringIgnored :=
  (.lam (.lam (.substringRaw_casesOn (.var (v♯1)) (.var (v♯3)))) :
    Term sig0 [] _ (TyWf.prim .substringRaw ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- `fun n => Nat.rec 5 (fun _ ih => ih) n` is `fun n => 5`.
/--
error: could not synthesize default value for parameter 'hStep' using tactics
---
error: Tactic `decide` proved that the proposition
  0 = 0 → Head.var ≠ Head.var
is false
-/
#guard_msgs (error) in
def foldIdentity :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 5) .nil) (.var (v♯1))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- At depth `1` a branch that is one of its answers is not the identity — `f (n + 2) = f n`
    alternates between the two base values — so it is a term. -/
def foldAlternate :=
  (.lam (.nat_rec 1 (.var (v♯0)) (.cons (.nat_mk 1) (.cons (.nat_mk 0) .nil)) (.var (v♯2))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run foldAlternate 6 = 0 := rfl
example : run foldAlternate 7 = 1 := rfl

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- A recursion whose step is the recursive call: `fun n => 7`. -/
def constDown : Nat → Nat
  | 0 => 7
  | n + 1 => constDown n

def constDown_term :=
  (#leanscript_to_term constDown : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run constDown_term 0 = 7 := rfl
example : run constDown_term 9 = 7 := rfl

/--
info: (Term.nat_mk 7).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) constDown_term

/-- The same on the elements of an array: `fun a => 3`. -/
def constArr (a : Array Nat) : Nat := go a.toList
where
  go : List Nat → Nat
    | [] => 3
    | _ :: xs => go xs

def constArr_term :=
  (#leanscript_to_term constArr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : run constArr_term #[] = 3 := rfl
example : run constArr_term #[1, 2, 3] = 3 := rfl

/--
info: (Term.nat_mk 3).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) constArr_term

/-- A `match` on a pair that binds nothing it uses: `fun p => 5`. -/
def ignorePair (p : Nat × Nat) : Nat :=
  match p with
  | (_, _) => 5

def ignorePair_term :=
  (#leanscript_to_term ignorePair : Term sig0 [] _ (tyWfOf (Nat × Nat) ⇒ TyWf.prim .nat) .lam)

/--
info: (Term.nat_mk 5).lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) ignorePair_term

/-- A field read only in dead code: once `cond true …` is gone, the `match` reads nothing,
    and what is left is `fun p n => n + 1`. -/
def deadField (p : Nat × Nat) (n : Nat) : Nat :=
  match p with
  | (a, _) => cond true (n + 1) a

def deadField_term :=
  (#leanscript_to_term deadField :
    Term sig0 [] _ (tyWfOf (Nat × Nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run deadField_term (cast (Ty.denRecord_eq _).symm ((3, 4, ()) : Nat × Nat × Unit)) 10 =
    11 := rfl

/--
info: (Term.externCall (Spine.cons (Term.var DeBruijnProj.head) (Spine.cons (Term.nat_mk 1) Spine.nil))
      (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_add vs.1 vs.2.1))
      deadField_term._proof_2).lam.lam
-/
#guard_msgs in
#reduce (proofs := false) (types := false) deadField_term

end TermTests.UnusedFieldsAndIdFold
