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
* with arguments that are all closed Lean values, for an entry that takes a proof, to
  `Term.extern` of the entry with the program's own proof.

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
  | .extern _ => some "extern"
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

/-! ## Closed arguments: `Term.extern`, with the program's own proof -/

def second : Nat := #[1, 2, 3][1]

def second_term := (#leanscript_to_term second : Term sig0 [] _ (TyWf.prim .nat) .comp)

example : externForm? second_term = some "extern" := rfl
example : run second_term = 2 := rfl

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
