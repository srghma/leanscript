module

public import LeanScript.Eval
-- The kernel checks of `Lean.Name.beq` below need its body, which `Init` does not expose.
import all Init.Prelude
public import LeanScript.Ty.Instances
public meta import LeanScript.ToTerm.Elab

@[expose] public section

/-!
# Externs in functions translated by `#leanscript_to_term`

A call of a Lean function implemented by a pure extern of `Init` is translated to the
entry of the catalogue `LeanScript.LeanInitPureExtern` that models it:

* with arguments known only when the term runs, to `Term.externCall` — the terms of the
  arguments, and the function that builds the entry from their values;
* for an entry that takes a proof, to `Term.externCallChecked`: the proposition is decided
  on the values when the term runs and the proof handed to the entry, with a fallback for
  values that do not satisfy it (which a Lean program cannot give);
* with arguments that are all literals or closed values, to **the value** of the call:
  the grammar rejects an extern on values whose result can be written as a term
  (`TyWf.quotable`), so the translation computes it where the term is written — `1 + 2`
  is the literal `3`, and `#[1, 2, 3][1]` (with the program's own proof) is `2`.

Each value is checked by `rfl`.
-/

namespace TermTests.ExternToTerm

open LeanScript

def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- The first of `Term.extern`, `Term.externCall` and `Term.externCallChecked` in the term,
    looking under binders, applications and `let`s.  (The translation of `a + b` goes
    through the instances `HAdd Nat` and `Add Nat`, each a function applied to its
    arguments, before it reaches `Nat.add`.) -/
def externForm? {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head} :
    Term sig0 Γ u τ k → Option String
  | .lam b => externForm? b
  | .ap f a _ => externForm? f <|> externForm? a
  | .letE a b _ _ => externForm? a <|> externForm? b
  | .extern _ _ => some "extern"
  | .externCall _ _ _ => some "externCall"
  | .externCallChecked _ _ _ _ => some "externCallChecked"
  | _ => none

/-! ## An extern without a proof: `Term.externCall` -/

def addN (a b : Nat) : Nat := a + b

def addN_term :=
  (#leanscript_to_term addN :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : externForm? addN_term = some "externCall" := by decide
example : run addN_term 2 3 = 5 := rfl

/-- `Array.toList` is the extern `lean_array_to_list`, whose value is a list of the
    language. -/
def asList (a : Array Nat) : List Nat := a.toList

def asList_term :=
  (#leanscript_to_term asList :
    Term sig0 [] _ (TyWf.array (TyWf.prim .nat) ⇒ tyWfOf (List Nat)) .lam)

example : Ty.DenRec.toList (.prim .nat) (run asList_term #[4, 5, 6]) = [4, 5, 6] := by decide

/-! ## An extern that takes a proof: `Term.externCallChecked`

`xs[i]` in the branch of `if h : i < xs.size` is `Array.getInternal xs i h`.  The proof is
erased, so the term decides `i < xs.size` again when it runs and hands the proof it gets
to `Array.getInternal`. -/

def getOr (a : Array Nat) (i : Nat) : Nat := if h : i < a.size then a[i] else 0

def getOr_term :=
  (#leanscript_to_term getOr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run getOr_term #[10, 20, 30] 0 = 10 := rfl
example : run getOr_term #[10, 20, 30] 2 = 30 := rfl
example : run getOr_term #[10, 20, 30] 5 = 0 := rfl
example : run getOr_term #[10, 20, 30] 1 = getOr #[10, 20, 30] 1 := rfl

/-- `Array.set` with its proof. -/
def setOr (a : Array Nat) (i v : Nat) : Array Nat := if h : i < a.size then a.set i v h else a

def setOr_term :=
  (#leanscript_to_term setOr :
    Term sig0 [] _ (TyWf.array (.prim .nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.array (.prim .nat)) .lam)

example : run setOr_term #[1, 2, 3] 1 7 = #[1, 7, 3] := rfl
example : run setOr_term #[1, 2, 3] 3 7 = #[1, 2, 3] := rfl

/-! ## Closed arguments: the value of the call

An extern called on literals and closed values is computed where the term is written, and
the term is its value: no extern is left. -/

/-- `Array.getInternal` on an array literal, with the program's own proof. -/
def second : Nat := #[1, 2, 3][1]

def second_term := (#leanscript_to_term second : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : externForm? second_term = none := rfl
example : run second_term = 2 := rfl

/-- `Nat.add` on two literals. -/
def onePlusTwo : Nat := 1 + 2

def onePlusTwo_term := (#leanscript_to_term onePlusTwo : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : externForm? onePlusTwo_term = none := rfl
example : run onePlusTwo_term = 3 := rfl

/-- An extern whose result is an array: the value is an array literal, a closed value. -/
def pushed : Array Nat := #[1, 2].push 3

def pushed_term :=
  (#leanscript_to_term pushed : Term sig0 [] _ (TyWf.array (TyWf.prim .nat)) .val)

example : externForm? pushed_term = none := rfl
example : run pushed_term = #[1, 2, 3] := rfl

/-- Externs on values nested inside a function: `(1 + 2) * n` computes `1 + 2` where the
    term is written, and keeps the multiplication by the argument. -/
def timesThree (n : Nat) : Nat := (1 + 2) * n

def timesThree_term :=
  (#leanscript_to_term timesThree : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run timesThree_term 5 = 15 := rfl

/-- A string extern on literals. -/
def greeting : String := "lean" ++ "script"

def greeting_term :=
  (#leanscript_to_term greeting : Term sig0 [] _ (TyWf.prim .string) .lit)

example : externForm? greeting_term = none := rfl

/-- More results that are literals: a boolean and the length of a string. -/
def twoIsTwo : Bool := Nat.beq 2 2
def abcLength : Nat := "abc".length

def twoIsTwo_term := (#leanscript_to_term twoIsTwo : Term sig0 [] _ (TyWf.prim .bool) .lit)
def abcLength_term := (#leanscript_to_term abcLength : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : run twoIsTwo_term = true := rfl
example : run abcLength_term = 3 := rfl

/-- An extern whose result is not quotable (a list, a recursive tagged union) stays an
    extern on values: `Term.extern`. -/
def chars : List Char := "ab".toList

def chars_term := (#leanscript_to_term chars : Term sig0 [] _ (tyWfOf (List Char)) .comp)

example : externForm? chars_term = some "extern" := rfl
example : Ty.DenRec.toList (.prim .char) (run chars_term) = ['a', 'b'] := by decide

/-! ## `Lean.Name` is an ordinary inductive of the language -/

def sameName (a b : Lean.Name) : Bool := a == b

def sameName_term :=
  (#leanscript_to_term sameName :
    Term sig0 [] _ (TyWf.leanName ⇒ TyWf.leanName ⇒ TyWf.prim .bool) .lam)

example : run sameName_term (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.b) = true := by decide +kernel
example : run sameName_term (TyWf.Den.ofName `a.b) (TyWf.Den.ofName `a.c) = false := by decide +kernel

/-! ## `Nat.gcd` is an ordinary function

It is translated as if it had no `@[extern]`: a call of it is a call of the declaration
`gcd` of the signature. -/

def sigGcd : Sig :=
  ⟨[⟨"gcd", TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

def gcdTwice (a : Nat) : Nat := Nat.gcd a (2 * a)

def gcdTwice_term :=
  (#leanscript_to_term gcdTwice :
    Term sigGcd [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : (Term.run (Sg := sigGcd) (Nat.gcd, PUnit.unit) gcdTwice_term) 6 = 6 := by decide

end TermTests.ExternToTerm
