module

public import LeanScript.Expr

/-!
# The grammar is usable: a few terms, written out

Each example below builds a `LeanScript.Term` of a stated type, so the file fails to
build if a constructor of the grammar cannot be applied as its documentation says.
-/

namespace TyTests

open LeanScript

/-- The empty signature: a module that refers to no top-level declaration. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", Ty.prim .nat ⇒ Ty.prim .nat⟩], by decide⟩

/-! ## Variables, functions and applications -/

/-- `fun x => x`, at `nat ⇒ nat`. -/
def idNat : Term emptySig [] (Ty.prim .nat ⇒ Ty.prim .nat) := .lam (.var (v♯0))

/-- `(fun x => x) 3`. -/
def idNatAt3 : Term emptySig [] (Ty.prim .nat) := .ap idNat (.nat_mk 3)

/-- `fun x => fun y => x`: a curried constant function. -/
def constNat : Term emptySig []
    (Ty.prim .nat ⇒ Ty.prim .bool ⇒ Ty.prim .nat) :=
  .lam (.lam (.var (v♯1)))

/-- `let x = 3; x`. -/
def letThree : Term emptySig [] (Ty.prim .nat) := .letE (.nat_mk 3) (.var (v♯0))

/-- A call of the one declaration of `doubleSig`. -/
def callDouble : Term doubleSig [] (Ty.prim .nat) :=
  .ap (.global .here) (.nat_mk 21)

/-! ## Literals -/

/-- A bit-vector literal: the positivity of the width is written by `by decide`. -/
def bv : Term emptySig [] (Ty.prim (.bitvec 8)) := .bitvec_mk (v := 7#8)

/-- A string literal. -/
def hello : Term emptySig [] (Ty.prim .string) := .string_mk "hello"

/-- A character literal. -/
def theLetterA : Term emptySig [] (Ty.prim .char) := .char_mk 'a'

/-- A 64-bit float literal. -/
def half : Term emptySig [] (Ty.prim .float) := .float_mk 0.5

/-! ## Eliminators of the terminal types -/

/-- `if b then 1 else 0`, as a function of `b`. -/
def boolToNat : Term emptySig [] (Ty.prim .bool ⇒ Ty.prim .nat) :=
  .lam (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0))

/-- `fun n => match n with | 0 => 0 | k + 1 => k`: the predecessor, by case analysis. -/
def pred : Term emptySig [] (Ty.prim .nat ⇒ Ty.prim .nat) :=
  .lam (.nat_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- `fun n => Nat.rec 0 (fun k ih => ih) n`: a fold over a natural number.  The
    successor branch binds the predecessor at index `0` and the value of the fold at
    index `1`, and this one answers with the latter. -/
def foldNat : Term emptySig [] (Ty.prim .nat ⇒ Ty.prim .nat) :=
  .lam (.nat_rec (.var (v♯0)) (.nat_mk 0) (.var (v♯1)))

/-- The code point of a character, as a `uint32`. -/
def charCode : Term emptySig [] (Ty.prim .char ⇒ Ty.prim .uint32) :=
  .lam (.char_casesOn (.var (v♯0)) (.var (v♯0)))

/-- The byte index of an unchecked position. -/
def rawByteIdx : Term emptySig [] (Ty.prim .stringPosRaw ⇒ Ty.prim .nat) :=
  .lam (.stringPosRaw_casesOn (.var (v♯0)) (.var (v♯0)))

/-- The string an unchecked substring is into: its branch binds the three fields, and
    the string is the first of them. -/
def substringStr : Term emptySig [] (Ty.prim .substringRaw ⇒ Ty.prim .string) :=
  .lam (.substringRaw_casesOn (.var (v♯0)) (.var (v♯0)))

/-! ## Delays, and arrays -/

/-- A memoised delay of `3`, forced again. -/
def thunkedThree : Term emptySig [] (Ty.prim .nat) :=
  .thunk_force (.thunk_mk (.nat_mk 3))

/-- An unmemoised delay of `3`, forced again. -/
def lazyThree : Term emptySig [] (Ty.prim .nat) :=
  .lazy_force (.lazy_mk (.nat_mk 3))

/-- The array `#[1, 2, 3]`. -/
def oneTwoThree : Term emptySig [] (Ty.array (Ty.prim .nat)) :=
  .array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil)))

/-- The first element of an array of naturals, or `0`: the non-empty branch binds the
    head and the tail, in that order. -/
def headOrZero : Term emptySig [] (Ty.array (Ty.prim .nat) ⇒ Ty.prim .nat) :=
  .lam (.array_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0)))

/-- The fold of an array: the non-empty branch binds the head at index `0`, the tail at
    index `1` and the value of the fold over the tail at index `2`. -/
def foldArray : Term emptySig [] (Ty.array (Ty.prim .nat) ⇒ Ty.prim .nat) :=
  .lam (.array_rec (.var (v♯0)) (.nat_mk 0) (.var (v♯2)))

/-! ## The user-defined shapes -/

/-- An enum of exactly three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- The middle constructor of `three`. -/
def middle : Term emptySig [] (Ty.enum three) := .enum_mk three ⟨1, by decide⟩

/-- A dispatch on `three`: one branch per constructor, and no default.  The branches
    follow the shape of the schema, which has exactly the three constructors an enum has
    at minimum. -/
def enumToNat : Term emptySig [] (Ty.enum three ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOn (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2)))

/-- An enum of five constructors: two beyond the minimum. -/
def five : LeanEnumSchema := ⟨2, 0⟩

/-- Its dispatch: a branch for each of the two extra constructors, and then the three an
    enum always has. -/
def fiveToNat : Term emptySig [] (Ty.enum five ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOn (.var (v♯0))
    (.cons (.nat_mk 0) (.cons (.nat_mk 1)
      (.three (.nat_mk 2) (.nat_mk 3) (.nat_mk 4)))))

/-- A record of a `nat` and a `bool`. -/
def pairSchema : LeanRecordSchema Ty := ⟨Ty.prim .nat, Ty.prim .bool, []⟩

/-- The record `(3, true)`. -/
def pair : Term emptySig [] (Ty.record pairSchema) :=
  .record_mk pairSchema (.cons (.nat_mk 3) (.cons (.bool_mk true) .nil))

/-- Its first field: the eliminator binds both fields, and the first is index `0`. -/
def pairFst : Term emptySig [] (Ty.prim .nat) :=
  .record_casesOn pair (.var (v♯0))

/-- Its second field, at index `1`. -/
def pairSnd : Term emptySig [] (Ty.prim .bool) :=
  .record_casesOn pair (.var (v♯1))

/-- A union of a constructor with one `nat` field and a field-less one. -/
def optNat : LeanTaggedUnionSchema Ty := .payloadFirst ⟨Ty.prim .nat, []⟩ [] []

/-- Its first constructor, applied to `3`: the bound on the tag is written by the
    default tactic, so nothing stands between the tag and the fields. -/
def someThree : Term emptySig [] (Ty.taggedUnion optNat) :=
  .taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil)

/-- Its second, field-less constructor: the tag is `1`, which is in range because the
    union has two constructors. -/
def noneNat : Term emptySig [] (Ty.taggedUnion optNat) :=
  .taggedUnion_mk optNat 1 (fields := .nil)

/-- A bound that is given by hand still works. -/
def someThree' : Term emptySig [] (Ty.taggedUnion optNat) :=
  .taggedUnion_mk optNat 0 (by decide) (.cons (.nat_mk 3) .nil)

/-- A dispatch on it: the branches follow the shape of the schema — the first
    constructor carries a field, so its branch binds it; the second binds nothing; and
    there is no constructor after them. -/
def optNatOrZero : Term emptySig [] (Ty.taggedUnion optNat ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOn (.var (v♯0)) (.payloadFirst (.var (v♯0)) (.nat_mk 0) .nil))

/-- A dispatch on *some* of its constructors, with a default: only constructor `0` gets
    a branch — and that branch binds its field — while constructor `1` falls to the
    default.  A one-branch list is `last`; the bound on the tag is written by `ctor_tag`
    and the bound that keeps the numbers in order by `ctor_ge`. -/
def optNatOrZeroWithDefault : Term emptySig [] (Ty.taggedUnion optNat ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
    (.last 0 (branch := .var (v♯0))) (.nat_mk 0))

/-- A union whose first constructor carries no fields: the branches then go through
    `CtorsWithPayloadCases`. -/
def natOrNothing : LeanTaggedUnionSchema Ty := .skip (.here ⟨Ty.prim .nat, []⟩ [])

/-- Its dispatch: a branch for the field-less constructor, then the branch of the
    constructor that carries the `nat`, which binds it. -/
def natOrNothingToNat : Term emptySig [] (Ty.taggedUnion natOrNothing ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOn (.var (v♯0)) (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil)))

/-- A dispatch on the enum `three` that names only its last constructor and sends the
    other two to the default.  A one-branch list is `last`, and the bound that keeps the
    numbers in order is written by `ctor_ge`. -/
def enumLastOrZero : Term emptySig [] (Ty.enum three ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOnWithDefault (.var (v♯0)) (.last ⟨2, by decide⟩ (.nat_mk 2))
    (.nat_mk 0))

/-- Two of the five constructors, named smallest first; the other three take the
    default. -/
def fiveTwoOrZero : Term emptySig [] (Ty.enum five ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOnWithDefault (.var (v♯0))
    (.cons 1 (.nat_mk 1) (.last 3 (.nat_mk 3))) (.nat_mk 0))

-- The order is not a convention but a typing rule: a list whose numbers go down does
-- not elaborate.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  ↑3 + 1 ≤ ↑1
is false
-/
#guard_msgs (error) in
def fiveOutOfOrder : Term emptySig [] (Ty.enum five ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOnWithDefault (.var (v♯0))
    (.cons 3 (.nat_mk 3) (.last 1 (.nat_mk 1))) (.nat_mk 0))

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  ↑1 + 1 ≤ ↑1
is false
-/
#guard_msgs (error) in
def fiveRepeated : Term emptySig [] (Ty.enum five ⇒ Ty.prim .nat) :=
  .lam (.enum_casesOnWithDefault (.var (v♯0))
    (.cons 1 (.nat_mk 1) (.last 1 (.nat_mk 2))) (.nat_mk 0))

/-! ## A partial dispatch on a union is validated the same way -/

/-- A union with three constructors: `nat`, `bool`, `nat`. -/
def natBoolNat : LeanTaggedUnionSchema Ty :=
  .payloadFirst ⟨Ty.prim .nat, []⟩ [Ty.prim .bool] [[Ty.prim .nat]]

/-- Two of its three constructors, named smallest first, each binding its field; the
    third takes the default.  Both bounds — the tag's and the order's — are written by
    the default tactics. -/
def natBoolNatTwoOrZero :
    Term emptySig [] (Ty.taggedUnion natBoolNat ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 2 (branch := .var (v♯0))))
    (.nat_mk 0))

-- As for an enum, the order is a typing rule: a list whose numbers go down does not
-- elaborate.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  2 + 1 ≤ 0
is false
-/
#guard_msgs (error) in
def natBoolNatOutOfOrder :
    Term emptySig [] (Ty.taggedUnion natBoolNat ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
    (.cons 2 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
    (.nat_mk 0))

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  0 + 1 ≤ 0
is false
-/
#guard_msgs (error) in
def natBoolNatRepeated :
    Term emptySig [] (Ty.taggedUnion natBoolNat ⇒ Ty.prim .nat) :=
  .lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
    (.cons 0 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
    (.nat_mk 0))

end TyTests
