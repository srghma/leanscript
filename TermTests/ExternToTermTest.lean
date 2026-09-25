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
  | .lam b _ => externForm? b
  | .ap f a .. => externForm? f <|> externForm? a
  | .letE a b .. => externForm? a <|> externForm? b
  | .extern _ _ => some "extern"
  | .externCall .. => some "externCall"
  | .externCallChecked .. => some "externCallChecked"
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

def twoIsTwo_term := (#leanscript_to_term twoIsTwo : Term sig0 [] _ (TyWf.prim .bool) (.bool true))
def abcLength_term := (#leanscript_to_term abcLength : Term sig0 [] _ (TyWf.prim .nat) .lit)

example : run twoIsTwo_term = true := rfl
example : run abcLength_term = 3 := rfl

/-! ## Results that are lists, options, pairs, positions and float models

Every value that holds no function can be written as a term (`TyWf.quotable`), so an
extern on values is computed whatever its result: a list is written as its constructors,
an `Option` as `none` or `some`, a pair as the record of its fields, a checked position or
a string slice as its literal (whose validity proof is rebuilt by `decide`). -/

/-- `"ab".toList` is the list `['a', 'b']`, written out: a closed value (`Head.val`). -/
def chars : List Char := "ab".toList

def chars_term := (#leanscript_to_term chars : Term sig0 [] _ (tyWfOf (List Char)) .val)

example : externForm? chars_term = none := rfl
example : Ty.DenRec.toList (.prim .char) (run chars_term) = ['a', 'b'] := by decide

/-- An `Option`: the character at byte `1` of `"ab"` is `some 'b'`.  (The raw position
    `⟨1⟩` is a value of a terminal type built from a literal: it is computed too.) -/
def secondChar : Option Char := String.Pos.Raw.get? "ab" ⟨1⟩

def secondChar_term :=
  (#leanscript_to_term secondChar : Term sig0 [] _ (tyWfOf (Option Char)) .val)

example : externForm? secondChar_term = none := rfl
example : run secondChar_term = TyWf.Den.ofOption (α := .prim .char) (some 'b') := rfl

/-- …and at byte `5` it is `none`. -/
def noChar : Option Char := String.Pos.Raw.get? "ab" ⟨5⟩

def noChar_term := (#leanscript_to_term noChar : Term sig0 [] _ (tyWfOf (Option Char)) (.ctorAt 0 0))

example : externForm? noChar_term = none := rfl
example : run noChar_term = TyWf.Den.ofOption (α := .prim .char) none := rfl

/-- A pair: `Float.frExp 8.0` is the record of its two fields. -/
def frexpEight : Float × Int := Float.frExp 8.0

def frexpEight_term :=
  (#leanscript_to_term frexpEight : Term sig0 [] _ (tyWfOf (Float × Int)) .val)

example : externForm? frexpEight_term = none := rfl

/-- A field of that pair: the dispatch on the computed record is reduced as well, so the
    term is the literal `4`. -/
def frexpEightExp : Int := (Float.frExp 8.0).2

def frexpEightExp_term :=
  (#leanscript_to_term frexpEightExp : Term sig0 [] _ (tyWfOf Int) .lit)

example : run frexpEightExp_term = 4 := rfl

/-- A checked position: `"ab".startPos.next h` is the literal position `1` into `"ab"`,
    with its validity proved by `decide`. -/
def secondPos : ("ab" : String).Pos := ("ab" : String).startPos.next (by decide)

def secondPos_term :=
  (#leanscript_to_term secondPos : Term sig0 [] _ (TyWf.prim (.stringPos "ab")) .lit)

example : externForm? secondPos_term = none := rfl
example : run secondPos_term = ("ab" : String).startPos.next (by decide) := by decide

/-- The model of a float: `Float.toModel 1.5` is the literal of its bits, whose validity is
    proved by `decide`. -/
def modelOfOneHalf : Float.Model := Float.toModel 1.5

def modelOfOneHalf_term :=
  (#leanscript_to_term modelOfOneHalf : Term sig0 [] _ (TyWf.prim .floatModel) .lit)

example : externForm? modelOfOneHalf_term = none := rfl

-- The literals whose proofs are rebuilt by `decide` — a string slice, and the models of a
-- single- and a double-precision float (`NaN` included) — are written back from their
-- values as well-typed terms.
#guard_msgs in
run_meta do
  let γ := Lean.mkApp (Lean.mkConst ``List.nil [0]) (Lean.mkConst ``LeanScript.TyWf)
  let prim (p : Lean.Name) := Lean.mkApp (Lean.mkConst ``LeanScript.TyWf.prim) (Lean.mkConst p)
  let cases : List (Lean.Expr × LeanScript.Quoted) :=
    [(prim ``LeanScript.LeanPrimTy.stringSlice, .stringSlice "héllo" 1 3),
     (prim ``LeanScript.LeanPrimTy.float32Model, .floatModel true (Float32.toBits 1.5).toNat),
     (prim ``LeanScript.LeanPrimTy.floatModel, .floatModel false (Float.toBits (0.0 / 0.0)).toNat)]
  for (τ, q) in cases do
    let t ← LeanScript.ToTerm.quotedTerm (Lean.mkConst ``sig0) γ τ q
    Lean.Meta.check t

/-! ## Arguments that are lists

A list (or an option, a pair, a record) of literals is a closed value too (`Head.val`), so
an extern called on one is computed where the term is written. -/

/-- `String.ofList ['l', 'e', 'a', 'n']` is the literal `"lean"`. -/
def ofChars : String := String.ofList ['l', 'e', 'a', 'n']

def ofChars_term := (#leanscript_to_term ofChars : Term sig0 [] _ (TyWf.prim .string) .lit)

example : externForm? ofChars_term = none := rfl
example : run ofChars_term = "lean" := rfl

/-- The round trip `String.ofList "ab".toList`: both calls are computed, the result is
    `"ab"`. -/
def roundTrip : String := String.ofList "ab".toList

def roundTrip_term := (#leanscript_to_term roundTrip : Term sig0 [] _ (TyWf.prim .string) .lit)

example : run roundTrip_term = "ab" := rfl

/-- On a variable, the list is only known when the term runs: `Term.externCall`. -/
def toListOf (s : String) : List Char := s.toList

def toListOf_term :=
  (#leanscript_to_term toListOf : Term sig0 [] _ (TyWf.prim .string ⇒ tyWfOf (List Char)) .lam)

example : externForm? toListOf_term = some "externCall" := rfl

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
