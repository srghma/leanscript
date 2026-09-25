module

public import LeanScript.Eval

@[expose] public section

/-!
# The evaluator, run

Every example below writes a closed term of `LeanScript.Term` and the value
`LeanScript.Term.eval` gives it, and checks the two agree by `rfl` — that is, by the
kernel.  The terms mirror those of `TermTests.TermTest`, which pins that the *grammar* is
usable; this file pins what each of them *computes*.

Nothing here supplies fuel or handles a failure: `Term.eval` is a total function, so a
term of type `τ` simply **has** a value of `LeanScript.Ty.Den τ`.
-/

namespace TermTests.Eval

open LeanScript

/-- The empty signature: a module that refers to no top-level declaration. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The values of the declarations of `doubleSig`: the one function `double`. -/
def doubleEnv : GlobalEnv doubleSig.decls := (fun n => 2 * n, PUnit.unit)

/-- Running a closed term of `emptySig`.  It is a macro rather than a function so that
    the term is the *whole* of its argument: `Term.run` takes the proof that the term
    builds no recursive value as a trailing argument written by `no_rec_mk`, and a
    function applied to one more argument would pass that argument as the proof. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := emptySig) GlobalEnv.nil $t)

/-! ## Variables, functions, applications and `let` -/

/-- `fun x => x`, at `nat ⇒ nat`. -/
def idNat := (.lam (.var (v♯0)) : Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun x => fun y => x`. -/
def constNat :=
  (.lam (.lam (.var (v♯1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .bool ⇒ TyWf.prim .nat) .lam)

/-- `fun n => let x = n + 2; x + x`.  The bound value is a computation and the variable is
    used twice: a `let` of a literal, or of a variable used once, is a redex, and is not a
    term.  (Nor is `let x = 1 + 2; …`: an extern on literals is a redex too, whose value
    `3` is a literal.) -/
def letSix :=
  (.lam (.letE (.externCall (.cons (.var (v♯0)) (.cons (.nat_mk 2) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- A call of the one declaration of `doubleSig`. -/
def callDouble := (.ap (.global .here) (.nat_mk 21) : Term doubleSig [] _ (TyWf.prim .nat) (.app false))

example : run idNat 7 = 7 := rfl
-- `Term.run'` is the same thing for a module that declares nothing.
example : (Term.run' idNat) 7 = 7 := rfl
example : run constNat 7 true = 7 := rfl
example : run letSix 1 = 6 := rfl
example : Term.run doubleEnv callDouble = 42 := rfl

/-! ## Literals -/

example : run (.bitvec_mk (v := 7#8)) = 7#8 := rfl
example : run (.string_mk "hello") = "hello" := rfl
example : run (.char_mk 'a') = 'a' := rfl
example : run (.int_mk (-2)) = -2 := rfl
example : run (.uint8_mk 255) = 255 := rfl

/-! ## Eliminators of the terminal types -/

/-- `fun b => if b then 1 else 0`. -/
def boolToNat :=
  (.lam (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat) .lam)

/-- The predecessor, by case analysis on a natural number. -/
def pred :=
  (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- A fold over a natural number whose successor branch adds the predecessor to the value
    of the fold at it: `0 + 1 + ⋯ + (n - 1)`.  (A successor branch that answers with the
    value of the fold at the predecessor alone, `nat_rec 0 n 0 (fun _ ih => ih)`, is not a
    term: that fold is its base, `0`, however big the number is.) -/
def foldNatSum :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil)
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- The predecessor, by case analysis.  (As a fold whose successor branch answers with the
    predecessor, `nat_rec 0 n 0 (fun m _ => m)`, it is not a term: that branch reads none of
    the answers the fold gives it, so it is this case analysis.) -/
def foldNatPred :=
  (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun i => match i with | .ofNat n => n | .negSucc n => n`. -/
def intMagnitude :=
  (.lam (.int_casesOn (.var (v♯0)) (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .int ⇒ TyWf.prim .nat) .lam)

/-- The code point of a character. -/
def charCode :=
  (.lam (.char_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .char ⇒ TyWf.prim .uint32) .lam)

/-- The byte index of an unchecked position. -/
def rawByteIdx :=
  (.lam (.stringPosRaw_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .stringPosRaw ⇒ TyWf.prim .nat) .lam)

/-- The string an unchecked substring is into. -/
def substringStr :=
  (.lam (.substringRaw_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .substringRaw ⇒ TyWf.prim .string) .lam)

/-- The bit vector inside an 8-bit unsigned value. -/
def uint8Bits :=
  (.lam (.uint8_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .uint8 ⇒ TyWf.prim (.bitvec 8)) .lam)

example : run boolToNat true = 1 := rfl
example : run boolToNat false = 0 := rfl
example : run pred 0 = 0 := rfl
example : run pred 5 = 4 := rfl
example : run foldNatSum 5 = 10 := rfl
example : run foldNatPred 5 = 4 := rfl
example : run intMagnitude 7 = 7 := rfl
example : run intMagnitude (-8) = 7 := rfl
example : run charCode 'a' = 97 := rfl
example : run rawByteIdx ⟨12⟩ = 12 := rfl
example : run substringStr ⟨"abc", ⟨0⟩, ⟨3⟩⟩ = "abc" := rfl
example : run uint8Bits 5 = 5#8 := rfl

/-! ## Delays, and arrays -/

/-- `fun n => let t := Thunk.mk (fun _ => n); t.get + t.get`.  Forcing a delay built in
    place is a redex, and is not a term, so the delay is bound and forced through its
    variable.  (It takes `n` as an argument: on a literal, the whole `let` would be a closed
    computation, which the grammar asks to be written as its value, `6`.) -/
def thunkTwice :=
  (.lam (.letE (.thunk_mk (.var (v♯0)))
     (.externCall (.cons (.thunk_force (.var (v♯0))) (.cons (.thunk_force (.var (v♯0))) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- The same with an unmemoised delay. -/
def lazyTwice :=
  (.lam (.letE (.lazy_mk (.var (v♯0)))
     (.externCall (.cons (.lazy_force (.var (v♯0))) (.cons (.lazy_force (.var (v♯0))) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run thunkTwice 3 = 6 := rfl
example : run lazyTwice 3 = 6 := rfl

/-- The same `let` on the literal `3` is a closed computation: the grammar rejects it,
    since its value is known where it is written. -/
example : True := by
  fail_if_success
    have := (.letE (.thunk_mk (.nat_mk 3))
      (.externCall (.cons (.thunk_force (.var (v♯0))) (.cons (.thunk_force (.var (v♯0))) .nil))
        (fun vs => .lean_nat_add vs.1 vs.2.1)) :
      Term emptySig [] _ (TyWf.prim .nat) .comp)
  trivial

/-- The array `#[1, 2, 3]`. -/
def oneTwoThree :=
  (.array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat)) .val)

/-- The first element of an array of naturals, or `0`. -/
def headOrZero :=
  (.lam (.array_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- A fold over an array that adds the head to the value of the fold over the tail: the
    sum of the elements.  (One that answers with the value of the fold over the tail alone
    is not a term: that fold is its base, `0`, however long the array is.) -/
def foldArraySum :=
  (.lam (.array_rec 0 (.var (v♯0)) (.nil (.nat_mk 0))
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯2)) .nil))
       (fun vs => .lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- A fold over an array that answers with its **last** element, or `0`: the branch
    takes the head when the fold over the tail is the answer for the empty tail. -/
def lastOrZero :=
  (.lam (.array_rec 0 (.var (v♯0)) (.nil (.nat_mk 0))
     (.array_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯4)))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

example : run oneTwoThree = #[1, 2, 3] := rfl
example : run headOrZero #[1, 2, 3] = 1 := rfl
example : run headOrZero #[] = 0 := rfl
example : run foldArraySum #[1, 2, 3] = 6 := rfl
example : run lastOrZero #[1, 2, 3] = 3 := rfl
example : run lastOrZero #[] = 0 := rfl

/-! ## Enums -/

/-- An enum of exactly three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- An enum of five constructors. -/
def five : LeanEnumSchema := ⟨2, 0⟩

/-- The middle constructor of `three`. -/
def middle := (.enum_mk three ⟨1, by decide⟩ : Term emptySig [] _ (TyWf.enum three) .lit)

/-- A dispatch on `three`: one branch per constructor, and no default. -/
def enumToNat :=
  (.lam (.enum_casesOn (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2))) :
    Term emptySig [] _ (TyWf.enum three ⇒ TyWf.prim .nat) .lam)

/-- A dispatch on `five`. -/
def fiveToNat :=
  (.lam (.enum_casesOn (.var (v♯0))
     (.cons (.nat_mk 0) (.cons (.nat_mk 1)
       (.three (.nat_mk 2) (.nat_mk 3) (.nat_mk 4))))) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

/-- A dispatch on `three` that names only its last constructor. -/
def enumLastOrZero :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0)) (.last ⟨2, by decide⟩ (.nat_mk 2))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum three ⇒ TyWf.prim .nat) .lam)

/-- Two of the five constructors, named smallest first. -/
def fiveTwoOrZero :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0))
     (.cons 1 (.nat_mk 1) (.last 3 (.nat_mk 3))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

example : run middle = ⟨1, by decide⟩ := rfl
example : run enumToNat ⟨0, by decide⟩ = 0 := rfl
example : run enumToNat ⟨1, by decide⟩ = 1 := rfl
example : run enumToNat ⟨2, by decide⟩ = 2 := rfl
example : run fiveToNat ⟨0, by decide⟩ = 0 := rfl
example : run fiveToNat ⟨3, by decide⟩ = 3 := rfl
example : run fiveToNat ⟨4, by decide⟩ = 4 := rfl
example : run enumLastOrZero ⟨2, by decide⟩ = 2 := rfl
example : run enumLastOrZero ⟨0, by decide⟩ = 0 := rfl
example : run fiveTwoOrZero ⟨1, by decide⟩ = 1 := rfl
example : run fiveTwoOrZero ⟨3, by decide⟩ = 3 := rfl
example : run fiveTwoOrZero ⟨4, by decide⟩ = 0 := rfl

/-! ## Records -/

/-- A record of a `nat` and a `bool`. -/
abbrev pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .bool, []⟩

/-- The record `(3, true)`. -/
def pair :=
  (.record_mk pairSchema (.cons (.nat_mk 3) (.cons (.bool_mk true) .nil)) :
    Term emptySig [] _ (TyWf.record pairSchema) .val)

/-- The first projection.  Projecting out of a record built in place is a redex, and is
    not a term, so the projections are functions, applied to the value of `pair`. -/
def pairFst :=
  (.lam (.record_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.record pairSchema ⇒ TyWf.prim .nat) .lam)

/-- The second projection. -/
def pairSnd :=
  (.lam (.record_casesOn (.var (v♯0)) (.var (v♯1))) :
    Term emptySig [] _ (TyWf.record pairSchema ⇒ TyWf.prim .bool) .lam)

example : run pair = (3, true, PUnit.unit) := rfl
example : run pairFst (run pair) = 3 := rfl
example : run pairSnd (run pair) = true := rfl

/-! ## Tagged unions

A value of a union is its constructor's number together with exactly that constructor's
fields. -/

/-- A union of a constructor with one `nat` field and a field-less one. -/
def optNat : LeanTaggedUnionSchema TyWf := .payloadFirst ⟨TyWf.prim .nat, []⟩ [] []

/-- Its first constructor, applied to `3`. -/
def someThree :=
  (.taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion optNat) .val)

/-- Its second, field-less constructor. -/
def noneNat :=
  (.taggedUnion_mk optNat 1 (fields := .nil) :
    Term emptySig [] _ (TyWf.taggedUnion optNat) .val)

/-- A dispatch on it, with one branch per constructor. -/
def optNatOrZero :=
  (.lam (.taggedUnion_casesOn (.var (v♯0)) (.payloadFirst (.var (v♯0)) (.nat_mk 0) .nil)) :
    Term emptySig [] _ (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) .lam)

/-- A dispatch on only its first constructor, with a default. -/
def optNatOrZeroWithDefault :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.last 0 (branch := .var (v♯0))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) .lam)

example : (run someThree).1 = ⟨0, by decide⟩ := rfl
example : (run someThree).2 = (3, PUnit.unit) := rfl
example : (run noneNat).1 = ⟨1, by decide⟩ := rfl
example : run optNatOrZero (run someThree) = 3 := rfl
example : run optNatOrZero (run noneNat) = 0 := rfl
example : run optNatOrZeroWithDefault (run someThree) = 3 := rfl
example : run optNatOrZeroWithDefault (run noneNat) = 0 := rfl

/-- A union whose first constructor carries no fields. -/
def natOrNothing : LeanTaggedUnionSchema TyWf := .skip (.here ⟨TyWf.prim .nat, []⟩ [])

/-- Its dispatch. -/
def natOrNothingToNat :=
  (.lam (.taggedUnion_casesOn (.var (v♯0)) (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil))) :
    Term emptySig [] _ (TyWf.taggedUnion natOrNothing ⇒ TyWf.prim .nat) .lam)

/-- Its field-less constructor. -/
def nothing' :=
  (.taggedUnion_mk natOrNothing 0 (fields := .nil) :
    Term emptySig [] _ (TyWf.taggedUnion natOrNothing) .val)

/-- Its constructor that carries a `nat`, applied to `5`. -/
def justFive :=
  (.taggedUnion_mk natOrNothing 1 (fields := .cons (.nat_mk 5) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion natOrNothing) .val)

example : run natOrNothingToNat (run nothing') = 0 := rfl
example : run natOrNothingToNat (run justFive) = 5 := rfl

/-- A union with three constructors: `nat`, `bool`, `nat`. -/
def natBoolNat : LeanTaggedUnionSchema TyWf :=
  .payloadFirst ⟨TyWf.prim .nat, []⟩ [TyWf.prim .bool] [[TyWf.prim .nat]]

/-- Two of its three constructors, each binding its field; the third takes the
    default. -/
def natBoolNatTwoOrZero :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 0 (branch := .var (v♯0)) (rest := .last 2 (branch := .var (v♯0))))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

/-- One branch per constructor, with no default: the middle constructor's branch binds
    its `bool`. -/
def natBoolNatAll :=
  (.lam (.taggedUnion_casesOn (.var (v♯0))
     (.payloadFirst (.var (v♯0)) (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))
       (.cons (.var (v♯0)) .nil))) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

/-- Constructor `0` of `natBoolNat`, carrying a `nat`. -/
def nbnZero :=
  (.taggedUnion_mk natBoolNat 0 (fields := .cons (.nat_mk 7) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat) .val)

/-- Constructor `1`, carrying a `bool`. -/
def nbnOne :=
  (.taggedUnion_mk natBoolNat 1 (fields := .cons (.bool_mk true) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat) .val)

/-- Constructor `2`, carrying a `nat`. -/
def nbnTwo :=
  (.taggedUnion_mk natBoolNat 2 (fields := .cons (.nat_mk 9) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat) .val)

example : run natBoolNatTwoOrZero (run nbnZero) = 7 := rfl
example : run natBoolNatTwoOrZero (run nbnOne) = 0 := rfl
example : run natBoolNatTwoOrZero (run nbnTwo) = 9 := rfl
example : run natBoolNatAll (run nbnZero) = 7 := rfl
example : run natBoolNatAll (run nbnOne) = 1 := rfl
example : run natBoolNatAll (run nbnTwo) = 9 := rfl

end TermTests.Eval

end
