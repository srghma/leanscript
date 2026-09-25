module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# More optimizations of `#leanscript_to_term`

* **case-of-case**: a dispatch on a dispatch whose branches are all known (literals,
  constructors, values, or such dispatches themselves) is pushed into the branches of the
  inner one, where it reduces — the grammar rejects the redex (`Head.caseCtor`);
* **`if c then true else false`** is `c` — the grammar rejects it (`Head.bool`);
* `!`, `&&`, `||`, `decide`, `¬`, `≠`, `∧`, `∨`, Bool equality and `%` are translated
  directly, so they fold like any other dispatch;
* **η-reduction**: `fun x => f x` is `f` (translation only);
* **accumulator loops**: a tail recursion on one accumulator,
  `go (k + 1) a = go k (F k a)`, is a fold at the accumulator's type rather than a fold
  building one closure per step (translation only).

Each translation is checked against the Lean function by `rfl`, and its shape by `decide`.
-/

namespace TermTests.CaseOfCaseAndLoops

open LeanScript

def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- The number of `if`s (`Term.bool_casesOn`) in the term, looking under binders,
    applications and `let`s. -/
def ifs {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} : Term sig0 Γ u τ k → Nat
  | .lam b _ => ifs b
  | .ap f a .. => ifs f + ifs a
  | .letE a b .. => ifs a + ifs b
  | .bool_casesOn c t e .. => 1 + ifs c + ifs t + ifs e
  | _ => 0

/-- Whether the term is `fun x₁ … xₙ => y` for a variable `y`. -/
def lamsOfVar {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} : Term sig0 Γ u τ k → Bool
  | .lam b _ => lamsOfVar b
  | .var _ => true
  | _ => false

/-- Whether some `Term.nat_rec` in the term (under binders and `let`s) has a `fun` for its
    step — a fold at a function type, which builds one closure per step. -/
def foldsClosures {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} :
    Term sig0 Γ u τ k → Bool
  | .lam b _ => foldsClosures b
  | .letE a b .. => foldsClosures a || foldsClosures b
  | .nat_rec _ _ _ (.lam _ _) .. => true
  | .nat_rec _ _ _ b .. => foldsClosures b
  | _ => false

/-! ## The grammar rejects the redexes

Written by hand, `if c then true else false` and `if (if c then false else true) then x
else y` do not elaborate: their default proofs fail.  The forms they reduce to do. -/

abbrev boolT : TyWf := .prim .bool
abbrev natT : TyWf := .prim .nat

example : True := by
  fail_if_success exact
    (let _t := (.bool_casesOn (.var (v♯0)) (.bool_mk true) (.bool_mk false) :
      Term sig0 [boolT] _ boolT _)
    trivial)
  trivial

example : True := by
  fail_if_success exact
    (let _t := (.bool_casesOn (.bool_casesOn (.var (v♯0)) (.bool_mk false) (.bool_mk true))
        (.var (v♯1)) (.var (v♯2)) : Term sig0 [boolT, natT, natT] _ natT _)
    trivial)
  trivial

-- the reduced forms, written the same way
example : True := by
  exact
    (let _t := (.bool_casesOn (.var (v♯0)) (.bool_mk false) (.bool_mk true) :
      Term sig0 [boolT] _ boolT _)
    trivial)

example : True := by
  exact
    (let _t := (.bool_casesOn (.var (v♯0)) (.var (v♯2)) (.var (v♯1)) :
      Term sig0 [boolT, natT, natT] _ natT _)
    trivial)

/-! ## Case-of-case -/

def optMap (o : Option Nat) : Nat := match o.map (· + 1) with | some x => x | none => 0

def optMap_term := (#leanscript_to_term optMap : Term sig0 [] _ _ _)

example : run optMap_term ⟨⟨1, by decide⟩, (4, ())⟩ = 5 := rfl
example : run optMap_term ⟨⟨0, by decide⟩, ()⟩ = 0 := rfl

def optMatch (o : Option Nat) (d : Nat) : Nat :=
  match (match o with | some x => some (x + 1) | none => none) with
  | some x => x * 2
  | none => d

def optMatch_term := (#leanscript_to_term optMatch : Term sig0 [] _ _ _)

example : run optMatch_term ⟨⟨1, by decide⟩, (4, ())⟩ 7 = 10 := rfl
example : run optMatch_term ⟨⟨0, by decide⟩, ()⟩ 7 = 7 := rfl

def notIf (b : Bool) (x y : Nat) : Nat := if (if b then false else true) then x else y

def notIf_term := (#leanscript_to_term notIf : Term sig0 [] _ _ _)

-- the two `if`s are one
example : ifs notIf_term = 1 := by decide
example : run notIf_term true 1 2 = 2 := rfl
example : run notIf_term false 1 2 = 1 := rfl

/-! ## Boolean identities and connectives -/

def ifId (b : Bool) : Bool := if b then true else false

def ifId_term := (#leanscript_to_term ifId : Term sig0 [] _ _ _)

example : lamsOfVar ifId_term = true := by decide

def notNot (b : Bool) : Bool := !(!b)

def notNot_term := (#leanscript_to_term notNot : Term sig0 [] _ _ _)

example : lamsOfVar notNot_term = true := by decide

def both (n m : Nat) : Nat := if n == 3 && m == 4 then 1 else 2

def both_term := (#leanscript_to_term both : Term sig0 [] _ _ _)

example : run both_term 3 4 = 1 := rfl
example : run both_term 3 5 = 2 := rfl
example : run both_term 2 4 = 2 := rfl

def props (n : Nat) : Nat := if (n > 5 ∧ n < 10) ∨ n = 0 then 1 else 0

def props_term := (#leanscript_to_term props : Term sig0 [] _ _ _)

example : run props_term 7 = 1 := rfl
example : run props_term 0 = 1 := rfl
example : run props_term 3 = 0 := rfl
example : run props_term 12 = 0 := rfl

def ne (a b : Nat) : Bool := a ≠ b

def ne_term := (#leanscript_to_term ne : Term sig0 [] _ _ _)

example : run ne_term 1 2 = true := rfl
example : run ne_term 2 2 = false := rfl

def boolEq (a b : Bool) : Bool := a == b

def boolEq_term := (#leanscript_to_term boolEq : Term sig0 [] _ _ _)

example : run boolEq_term true true = true := rfl
example : run boolEq_term true false = false := rfl
example : run boolEq_term false false = true := rfl

def even (n : Nat) : Bool := n % 2 == 0

def even_term := (#leanscript_to_term even : Term sig0 [] _ _ _)

example : run even_term 4 = true := rfl
example : run even_term 7 = false := rfl

/-! ## η-reduction -/

def etaApp (f : Nat → Nat) : Nat → Nat := fun x => f x

def etaApp_term := (#leanscript_to_term etaApp : Term sig0 [] _ _ _)

-- `fun f => f`
example : lamsOfVar etaApp_term = true := by decide

/-! ## Accumulator loops -/

@[inline] def loopAcc : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => loopAcc n (acc + n)

def loopAcc_term := (#leanscript_to_term loopAcc : Term sig0 [] _ _ _)

example : foldsClosures loopAcc_term = false := by decide
example : run loopAcc_term 0 3 = loopAcc 0 3 := rfl
example : run loopAcc_term 1 3 = loopAcc 1 3 := rfl
example : run loopAcc_term 5 3 = loopAcc 5 3 := rfl

def sumTo (n : Nat) : Nat := loopAcc n 0

def sumTo_term := (#leanscript_to_term sumTo : Term sig0 [] _ _ _)

example : run sumTo_term 10 = 45 := rfl

/-- The counter is read twice by the step: bound once per step by a `let`. -/
def powAcc : Nat → Nat → Nat
  | 0, acc => acc + acc
  | n + 1, acc => powAcc n (acc * 2 + n * n)

def powAcc_term := (#leanscript_to_term powAcc : Term sig0 [] _ _ _)

example : foldsClosures powAcc_term = false := by decide
example : run powAcc_term 4 1 = powAcc 4 1 := rfl
example : run powAcc_term 0 1 = powAcc 0 1 := rfl

/-- Not a tail call: the answer at the predecessor is used, not returned — still a fold at
    the function type. -/
def notTail : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => notTail n acc + acc

def notTail_term := (#leanscript_to_term notTail : Term sig0 [] _ _ _)

example : foldsClosures notTail_term = true := by decide
example : run notTail_term 3 2 = notTail 3 2 := rfl

end TermTests.CaseOfCaseAndLoops
