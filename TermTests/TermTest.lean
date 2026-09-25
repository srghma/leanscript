module

public import LeanScript.Expr.Term

/-!
# The grammar is usable: a few terms, written out

Each example below builds a `LeanScript.Term` of a stated type, so the file fails to
build if a constructor of the grammar cannot be applied as its documentation says.
-/

namespace TermTests

open LeanScript

/-- The empty signature: a module that refers to no top-level declaration. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-! ## Variables, functions and applications -/

/-- `fun x => x`, at `nat ⇒ nat`. -/
def idNat := (.lam (.var (v♯0)) : Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `f 3`, for a function `f` that is a variable: an application whose function is not
    a `fun`. -/
def applyTo3 :=
  (.lam (.ap (.var (v♯0)) (.nat_mk 3)) :
    Term emptySig [] _ ((TyWf.prim .nat ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- `fun x => fun y => x`: a curried constant function. -/
def constNat :=
  (.lam (.lam (.var (v♯1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .bool ⇒ TyWf.prim .nat) .lam)

/-- `fun n => let x = n + n; x + x`: a `let` of a computation whose variable is used
    twice — the one `let` the grammar keeps. -/
def letTwice :=
  (.lam (.letE
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))
     (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
       fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- A call of the one declaration of `doubleSig`. -/
def callDouble := (.ap (.global .here) (.nat_mk 21) : Term doubleSig [] _ (TyWf.prim .nat) (.app false))

/-! ## Literals -/

/-- A bit-vector literal: the positivity of the width is written by `by decide`. -/
def bv := (.bitvec_mk (v := 7#8) : Term emptySig [] _ (TyWf.prim (.bitvec 8)) .lit)

/-- A string literal. -/
def hello := (.string_mk "hello.term" : Term emptySig [] _ (TyWf.prim .string) .lit)

/-- A character literal. -/
def theLetterA := (.char_mk 'a' : Term emptySig [] _ (TyWf.prim .char) .lit)

/-- A 64-bit float literal. -/
def half := (.float_mk 0.5 : Term emptySig [] _ (TyWf.prim .float) .lit)

/-! ## Eliminators of the terminal types -/

/-- `if b then 1 else 0`, as a function of `b`. -/
def boolToNat :=
  (.lam (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat) .lam)

/-- `fun n => match n with | 0 => 0 | k + 1 => k`: the predecessor, by case analysis. -/
def pred :=
  (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- `fun n => Nat.rec 0 (fun k ih => k + ih) n`: a fold over a natural number.  The
    successor branch binds the predecessor at index `0` and the value of the fold at
    index `1`, and this one adds them. -/
def foldNat :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil)
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- `fun n => Nat.rec 0 (fun k ih => ih) n`: a one-step fold whose branch is the answer it is
-- given is its base, `0`, at every `n` — so it is rejected (`hStep`).
/--
error: could not synthesize default value for parameter 'hStep' using tactics
---
error: Tactic `decide` proved that the proposition
  0 = 0 → (Head.var (Var.index DeBruijn.head.tail)).isVar = false
is false
-/
#guard_msgs (error) in
def foldNatId :=
  (.lam (.nat_rec 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil) (.var (v♯1))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

/-- The code point of a character, as a `uint32`. -/
def charCode :=
  (.lam (.char_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .char ⇒ TyWf.prim .uint32) .lam)

/-- The byte index of an unchecked position. -/
def rawByteIdx :=
  (.lam (.stringPosRaw_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .stringPosRaw ⇒ TyWf.prim .nat) .lam)

/-- The string an unchecked substring is into: its branch binds the three fields, and
    the string is the first of them. -/
def substringStr :=
  (.lam (.substringRaw_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .substringRaw ⇒ TyWf.prim .string) .lam)

/-! ## Delays, and arrays -/

/-- A memoised delay of `3`: a closed value (`Head.val`), since what it delays is a
    literal. -/
def thunkedThree := (.thunk_mk (.nat_mk 3) : Term emptySig [] _ (TyWf.thunk (TyWf.prim .nat)) .val)

/-- Forcing a memoised delay given as an argument. -/
def forceThunk :=
  (.lam (.thunk_force (.var (v♯0))) :
    Term emptySig [] _ (TyWf.thunk (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- An unmemoised delay of `3`. -/
def lazyThree := (.lazy_mk (.nat_mk 3) : Term emptySig [] _ (TyWf.lazy (TyWf.prim .nat)) .val)

/-- The array `#[1, 2, 3]`: a closed value (`Head.val`), since its elements are literals. -/
def oneTwoThree :=
  (.array_mk (.cons (.nat_mk 1) (.cons (.nat_mk 2) (.cons (.nat_mk 3) .nil))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat)) .val)

/-- The first element of an array of naturals, or `0`: the non-empty branch binds the
    head and the tail, in that order. -/
def headOrZero :=
  (.lam (.array_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

/-- The fold of an array: the non-empty branch binds the head at index `0`, the tail at
    index `1` and the value of the fold over the tail at index `2`; this one adds the head
    to the latter. -/
def foldArray :=
  (.lam (.array_rec 0 (.var (v♯0)) (.nil (.nat_mk 0))
    (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯2)) .nil))
      fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

-- A one-step fold of an array whose branch is the answer over the tail is its base.
/--
error: could not synthesize default value for parameter 'hStep' using tactics
---
error: Tactic `decide` proved that the proposition
  0 = 0 → (Head.var (Var.index DeBruijn.head.tail.tail)).isVar = false
is false
-/
#guard_msgs (error) in
def foldArrayId :=
  (.lam (.array_rec 0 (.var (v♯0)) (.nil (.nat_mk 0)) (.var (v♯2))) :
    Term emptySig [] _ (TyWf.array (TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)

-- A dispatch on a one-constructor value whose branch reads none of the fields is its
-- branch: `match c with | ⟨code⟩ => 0` is `0`.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  0 < Usage.head 0
is false
-/
#guard_msgs (error) in
def charIgnored :=
  (.lam (.char_casesOn (.var (v♯0)) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.prim .char ⇒ TyWf.prim .nat) .lam)

/-! ## The user-defined shapes -/

/-- An enum of exactly three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- The middle constructor of `three`. -/
def middle := (.enum_mk three ⟨1, by decide⟩ : Term emptySig [] _ (TyWf.enum three) .lit)

/-- A dispatch on `three`: one branch per constructor, and no default.  The branches
    follow the shape of the schema, which has exactly the three constructors an enum has
    at minimum. -/
def enumToNat :=
  (.lam (.enum_casesOn (.var (v♯0)) (.three (.nat_mk 0) (.nat_mk 1) (.nat_mk 2))) :
    Term emptySig [] _ (TyWf.enum three ⇒ TyWf.prim .nat) .lam)

/-- An enum of five constructors: two beyond the minimum. -/
def five : LeanEnumSchema := ⟨2, 0⟩

/-- Its dispatch: a branch for each of the two extra constructors, and then the three an
    enum always has. -/
def fiveToNat :=
  (.lam (.enum_casesOn (.var (v♯0))
     (.cons (.nat_mk 0) (.cons (.nat_mk 1)
       (.three (.nat_mk 2) (.nat_mk 3) (.nat_mk 4))))) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

/-- A record of a `nat` and a `bool`. -/
def pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .bool, []⟩

/-- The record `(3, true)`. -/
def pair :=
  (.record_mk pairSchema (.cons (.nat_mk 3) (.cons (.bool_mk true) .nil)) :
    Term emptySig [] _ (TyWf.record pairSchema) .val)

/-- The first field of such a record: the eliminator binds both fields, and the first is
    index `0`. -/
def pairFst :=
  (.lam (.record_casesOn (.var (v♯0)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.record pairSchema ⇒ TyWf.prim .nat) .lam)

/-- Its second field, at index `1`. -/
def pairSnd :=
  (.lam (.record_casesOn (.var (v♯0)) (.var (v♯1))) :
    Term emptySig [] _ (TyWf.record pairSchema ⇒ TyWf.prim .bool) .lam)

/-- A union of a constructor with one `nat` field and a field-less one. -/
def optNat : LeanTaggedUnionSchema TyWf := .payloadFirst ⟨TyWf.prim .nat, []⟩ [] []

/-- Its first constructor, applied to `3`: the bound on the tag is written by the
    default tactic, so nothing stands between the tag and the fields. -/
def someThree :=
  (.taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion optNat) .val)

/-- Its second, field-less constructor: the tag is `1`, which is in range because the
    union has two constructors. -/
def noneNat :=
  (.taggedUnion_mk optNat 1 (fields := .nil) :
    Term emptySig [] _ (TyWf.taggedUnion optNat) .val)

/-- A bound that is given by hand still works. -/
def someThree' :=
  (.taggedUnion_mk optNat 0 (by decide) (.cons (.nat_mk 3) .nil) :
    Term emptySig [] _ (TyWf.taggedUnion optNat) .val)

/-- A dispatch on it: the branches follow the shape of the schema — the first
    constructor carries a field, so its branch binds it; the second binds nothing; and
    there is no constructor after them. -/
def optNatOrZero :=
  (.lam (.taggedUnion_casesOn (.var (v♯0)) (.payloadFirst (.var (v♯0)) (.nat_mk 0) .nil)) :
    Term emptySig [] _ (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) .lam)

/-- A dispatch on *some* of its constructors, with a default: only constructor `0` gets
    a branch — and that branch binds its field — while constructor `1` falls to the
    default.  A one-branch list is `last`; the bound on the tag is written by `ctor_tag`
    and the bound that keeps the numbers in order by `ctor_ge`. -/
def optNatOrZeroWithDefault :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.last 0 (branch := .var (v♯0))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) .lam)

/-- A union whose first constructor carries no fields: the branches then go through
    `CtorsWithPayloadCases`. -/
def natOrNothing : LeanTaggedUnionSchema TyWf := .skip (.here ⟨TyWf.prim .nat, []⟩ [])

/-- Its dispatch: a branch for the field-less constructor, then the branch of the
    constructor that carries the `nat`, which binds it. -/
def natOrNothingToNat :=
  (.lam (.taggedUnion_casesOn (.var (v♯0)) (.skip (.nat_mk 0) (.here (.var (v♯0)) .nil))) :
    Term emptySig [] _ (TyWf.taggedUnion natOrNothing ⇒ TyWf.prim .nat) .lam)

/-- A dispatch on the enum `three` that names only its last constructor and sends the
    other two to the default.  A one-branch list is `last`, and the bound that keeps the
    numbers in order is written by `ctor_ge`. -/
def enumLastOrZero :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0)) (.last ⟨2, by decide⟩ (.nat_mk 2))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum three ⇒ TyWf.prim .nat) .lam)

/-- Two of the five constructors, named smallest first; the other three take the
    default. -/
def fiveTwoOrZero :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0))
     (.cons 1 (.nat_mk 1) (.last 3 (.nat_mk 3))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

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
def fiveOutOfOrder :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0))
     (.cons 3 (.nat_mk 3) (.last 1 (.nat_mk 1))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  ↑1 + 1 ≤ ↑1
is false
-/
#guard_msgs (error) in
def fiveRepeated :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0))
     (.cons 1 (.nat_mk 1) (.last 1 (.nat_mk 2))) (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.enum five ⇒ TyWf.prim .nat) .lam)

/-! ## A partial dispatch on a union is validated the same way -/

/-- A union with three constructors: `nat`, `bool`, `nat`. -/
def natBoolNat : LeanTaggedUnionSchema TyWf :=
  .payloadFirst ⟨TyWf.prim .nat, []⟩ [TyWf.prim .bool] [[TyWf.prim .nat]]

/-- Two of its three constructors, named smallest first, each binding its field; the
    third takes the default.  Both bounds — the tag's and the order's — are written by
    the default tactics. -/
def natBoolNatTwoOrZero :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 0 (branch := .var (v♯0)) (rest := .last 2 (branch := .var (v♯0))))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

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
def natBoolNatOutOfOrder :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 2 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

-- Nor does one that names the same constructor twice.
/--
error: could not synthesize default value for parameter 'hi' using tactics
---
error: Tactic `decide` proved that the proposition
  0 + 1 ≤ 0
is false
-/
#guard_msgs (error) in
def natBoolNatRepeated :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 0 (branch := .var (v♯0)) (rest := .last 0 (branch := .var (v♯0))))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

/-! ## A partial dispatch may not name **every** constructor

The default of a `xxx_casesOnWithDefault` has to be reachable.  A list of branches that
names every constructor of the type leaves the default unreachable — it is an exhaustive
dispatch written the long way round, and `Term.enum_casesOn` /
`Term.taggedUnion_casesOn` is how it has to be written.  The branch list **counts its
branches**, and the count is bounded by the number of constructors, so the long way
round does not elaborate. -/

-- All three constructors of `three` named, with a default that can never be taken.
/--
error: could not synthesize default value for parameter 'hk' using tactics
---
error: Tactic `decide` proved that the proposition
  1 + 1 + 1 < three.nOfConstructors
is false
-/
#guard_msgs (error) in
def threeAllNamed :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0))
     (.cons 0 (.nat_mk 0) (.cons 1 (.nat_mk 1) (.last 2 (.nat_mk 2))))
     (.nat_mk 9)) :
    Term emptySig [] _ (TyWf.enum three ⇒ TyWf.prim .nat) .lam)

-- Both constructors of `optNat` named, likewise.
/--
error: could not synthesize default value for parameter 'hk' using tactics
---
error: Tactic `decide` proved that the proposition
  1 + 1 < optNat.length
is false
-/
#guard_msgs (error) in
def optNatAllNamed :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 0 (branch := .var (v♯0)) (rest := .last 1 (branch := .nat_mk 1)))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion optNat ⇒ TyWf.prim .nat) .lam)

/-- Naming all but one constructor is still fine: the two smallest constructors of
    `natBoolNat`, with the third taking the default — one fewer branch than the union has
    constructors, which is what `ctor_lt` checks. -/
def natBoolNatAllButOne :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
     (.cons 0 (branch := .var (v♯0)) (rest := .last 1 (branch := .nat_mk 1)))
     (.nat_mk 0)) :
    Term emptySig [] _ (TyWf.taggedUnion natBoolNat ⇒ TyWf.prim .nat) .lam)

/-! ## A term is indexed by a **type**, not by a tree

`Term` and `Ctx` are indexed by `LeanScript.TyWf` — a tree together with the proof that it
is a type of the language — so the type of a term, and every type in its context, is a
type by construction.  Nothing has to be written by hand for it: `TyWf.prim`, `⇒`,
`TyWf.array`, `TyWf.record`, `TyWf.taggedUnion`, … compose the proof out of their
arguments'. -/

/-- The type of a term is always a type of the language: its proof is part of the index.
    (This is why no introduction form of a non-recursive shape has to ask for one.) -/
theorem type_of_term_is_wf {Sg : Sig} {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (_t : Term Sg Γ u τ k) :
    Ty.Wf τ.toTy := τ.isWf

/-- Every type in the context of a term is a type of the language, for the same reason. -/
theorem ctx_of_term_is_wf {Sg : Sig} {Γ : Ctx} {u : Usage Γ} {τ : TyWf} {k : Head}
    (_t : Term Sg Γ u τ k) :
    Ty.WfAllIn 0 (Γ.map TyWf.toTy) := Ty.wfAllIn_map_toTy Γ

-- A tree becomes an index by `Ty.toTyWf`, whose proof is written by `ty_wf` — and a tree
-- that is not a type is refused there, so it indexes no term at all.  A free occurrence
-- leaf is one such tree.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ty_wf: `Ty.self` is not a type in a scope of 0 members
-/
#guard_msgs (error) in
def atOccurrenceLeaf := (.nat_mk 0 : Term emptySig [] _ (Ty.self.toTyWf) .lit)

-- So is a binder that mentions itself to the left of an arrow.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs (error) in
def atNonPositiveBinder :=
  (.nat_mk 0 :
    Term emptySig [] _ ((Ty.recTaggedUnion (.payloadFirst ⟨.fn .self (.prim .nat), []⟩ [] [])).toTyWf) .lit)

/-! ## A redex does not elaborate

`Term` is optimized by construction: every constructor that could form a redex carries a
proof that it does not, written by `decide` on the indices of its subterms.  Writing a
redex out by hand therefore fails, and says which rule it breaks. -/

-- A β-redex: `(fun x => x) 3`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.lam.isFunLike = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp ((Usage.single DeBruijn.head).tail.many + 0) (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs (error) in
def idNatAt3 := (.ap (.lam (.var (v♯0))) (.nat_mk 3) : Term emptySig [] _ (TyWf.prim .nat) (.app false))

-- A `let` of a literal: `let x = 3; x + x`.  A value is inlined, never bound.
/--
error: could not synthesize default value for parameter 'hValue' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.lit.isBindable = true
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (Usage.letU 0 (Usage.single DeBruijn.head + (Usage.single DeBruijn.head + 0)))
      (Coe.coe LeanPrimTy.nat) Head.comp =
    false
is false
-/
#guard_msgs (error) in
def letThree :=
  (.letE (.nat_mk 3) (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
     fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) :
    Term emptySig [] _ (TyWf.prim .nat) .comp)

-- A `let` whose variable is used once: `fun n => let x = n + n; x`.
/--
error: could not synthesize default value for parameter 'hUsed' using tactics
---
error: Tactic `decide` proved that the proposition
  2 ≤ (Usage.single DeBruijn.head).head
is false
-/
#guard_msgs (error) in
def letOnce :=
  (.lam (.letE (.externCall (.cons (.var (v♯0)) (.cons (.var (v♯0)) .nil))
     fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1)) (.var (v♯0))) :
    Term emptySig [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

-- A test on a literal: `if true then 1 else 0`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.bool true).isKnown = false
is false
-/
#guard_msgs (error) in
def ifTrue :=
  (.bool_casesOn (.bool_mk true) (.nat_mk 1) (.nat_mk 0) :
    Term emptySig [] _ (TyWf.prim .nat) .comp)

-- A forced delay: `(thunk 3).force`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.ctorOf [Head.lit]).isCtorLike = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp 0 (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs (error) in
def thunkedThreeForced :=
  (.thunk_force (.thunk_mk (.nat_mk 3)) :
    Term emptySig [] _ (TyWf.prim .nat) .comp)

-- A dispatch on a constructor: the first field of the record `(3, true)`.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.ctorOf [Head.lit, Head.bool true]).isKnown = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (0 + (0 + 0) + Usage.drop pairSchema.toList (Usage.single DeBruijn.head)) pairSchema.fst
      ((Head.var (Var.index DeBruijn.head)).join Head.empty) =
    false
is false
-/
#guard_msgs (error) in
def pairFstOfPair := (.record_casesOn pair (.var (v♯0)) : Term emptySig [] _ (TyWf.prim .nat) .comp)

-- An extern called on literals only: `1 + 2`, which is a constant.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allValue [Head.lit, Head.lit] = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (0 + (0 + 0)) (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs (error) in
def onePlusTwo :=
  (.externCall (.cons (.nat_mk 1) (.cons (.nat_mk 2) .nil))
     fun vs => .preludeExtern (.lean_nat_add vs.1 vs.2.1) :
    Term emptySig [] _ (TyWf.prim .nat) .comp)

-- `#[1, 2, 3][2]'h`: an extern that takes a proof, called on an array literal and a
-- literal.  An array of literals is a closed value, so the call is computed where the term
-- is written (it is `3`).
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.allValue [Head.ctorOf [Head.lit, Head.lit, Head.lit], Head.lit] = false
is false
---
error: could not synthesize default value for parameter 'hClosed' using tactics
---
error: Tactic `decide` proved that the proposition
  Head.closedComp (0 + (0 + (0 + 0)) + (0 + 0) + 0) (TyWf.prim LeanPrimTy.nat) Head.comp = false
is false
-/
#guard_msgs (error) in
def oneTwoThreeAt2 :=
  (.externCallChecked (.cons oneTwoThree (.cons (.nat_mk 2) .nil))
     (fun vs => if h : vs.2.1 < vs.1.size then
       some (.preludeExtern (.lean_array_fget (TyWf.prim .nat) vs.1 vs.2.1 h)) else none)
     (.nat_mk 0) :
    Term emptySig [] _ (TyWf.prim .nat) .comp)

-- An extern on values held directly: `Nat.add 1 2`, whose value `3` is a literal.
/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: Tactic `decide` proved that the proposition
  (TyWf.prim LeanPrimTy.nat).quotable = false
is false
-/
#guard_msgs (error) in
def onePlusTwoExtern :=
  (.extern (.preludeExtern (.lean_nat_add 1 2)) : Term emptySig [] _ (TyWf.prim .nat) .comp)

end TermTests
