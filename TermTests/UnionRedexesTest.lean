module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# More redexes: dispatches on unions and enums

* **A dispatch whose branches are all the same leaf.**  As `if c then x else x` already
  was, `match o with | none => x | some _ => x` is `x`, for tagged unions, recursive tagged
  unions (lists) and enums, with or without a default branch (`hSame`, `Head.isCaseLeaf`).
  A leaf is a variable bound outside the dispatch, a `bool` literal or an enum literal.
* **The union η-redex.**  `match o with | none => none | some a => some a` is `o`: every
  branch rebuilds its own constructor from exactly the fields it binds (`hEta`,
  `Head.isUnionEta`).  With a default branch, `match s with | .circle r => .circle r | _ => s`
  is `s` (`Head.isUnionEtaDflt`).  The same for enums: `match c with | .red => .red | ...`.
* **A read of the scrutinee in a field-less branch.**  In the `none` branch of a dispatch on
  `o`, `o` *is* `none`, a literal: the branch may not read `o` (`hLit`,
  `Head.readsInFieldless`).  The translation writes the constructor instead.

Each redex written by hand is rejected (the errors are pinned), nearby legal forms are
accepted and run, `#leanscript_optimize` turns each redex into the expected term (by `rfl`),
and the translations of Lean functions are pinned by `rfl` or printed snapshots.
-/

namespace TermTests.UnionRedexes

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- `Option Nat`: constructor `0` carries a `nat`, constructor `1` nothing. -/
def optNat : LeanTaggedUnionSchema TyWf := .payloadFirst ⟨TyWf.prim .nat, []⟩ [] []

/-- An enum of three constructors. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-- The type of `optNat`. -/
abbrev optTy : TyWf := TyWf.taggedUnion optNat

/-! ## Written by hand: what the grammar rejects and accepts -/

-- `fun o x => match o with | some _ => x | none => x` is `fun o x => x`.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.branchAt { head := TyWf.prim LeanPrimTy.nat, tail := [] }.toList.length ([].length + 1)
        (Head.var (Var.index DeBruijn.head.tail))
        (Head.branchAt [].length [].length (Head.var (Var.index DeBruijn.head)) Head.empty)).isCaseLeaf =
    false
is false
-/
#guard_msgs (error) in
def optSameH :=
  (.lam (.lam (.taggedUnion_casesOn (.var (v♯1)) (.payloadFirst (.var (v♯1)) (.var (v♯0)) .nil))) :
    Term sig0 [] _ (optTy ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _)

-- `fun o => match o with | some a => some a | none => none` is `fun o => o`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.branchAt { head := TyWf.prim LeanPrimTy.nat, tail := [] }.toList.length ([].length + 1)
          (Head.ctorAtOf 0 [Head.var (Var.index DeBruijn.head)])
          (Head.branchAt [].length [].length (Head.ctorAtOf 1 []) Head.empty)).isUnionEta
      optNat.length (optTy.isTaggedUnionOf optNat.length) =
    false
is false
-/
#guard_msgs (error) in
def optEtaH :=
  (.lam (.taggedUnion_casesOn (.var (v♯0))
    (.payloadFirst (.taggedUnion_mk optNat 0 (fields := .cons (.var (v♯0)) .nil))
      (.taggedUnion_mk optNat 1 (fields := .nil)) .nil)) :
    Term sig0 [] _ (optTy ⇒ optTy) _)

-- `fun o => match o with | some a => some a | _ => o` is `fun o => o`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.branchTag (optNat.get 0 ⋯).length 0 (Head.ctorAtOf 0 [Head.var (Var.index DeBruijn.head)])
          Head.empty).isUnionEtaDflt
      (Head.var (Var.index DeBruijn.head)) (Head.var (Var.index DeBruijn.head)) (optTy.isTaggedUnionOf optNat.length) =
    false
is false
-/
#guard_msgs (error) in
def optEtaDfltH :=
  (.lam (.taggedUnion_casesOnWithDefault (.var (v♯0))
    (.last 0 (branch := .taggedUnion_mk optNat 0 (fields := .cons (.var (v♯0)) .nil)))
    (.var (v♯0))) :
    Term sig0 [] _ (optTy ⇒ optTy) _)

-- `fun o f => match o with | some a => a | none => f o`: in the `none` branch, `o` is `none`.
/--
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head.tail)).readsInFieldless
      (Usage.alt { head := TyWf.prim LeanPrimTy.nat, tail := [] }.toList (Usage.single DeBruijn.head) +
          Usage.alt []
            (Usage.scrutinize (Head.var (Var.index DeBruijn.head))
              (Usage.arg (Head.var (Var.index DeBruijn.head.tail))
                (Usage.single DeBruijn.head + Usage.single DeBruijn.head.tail))) +
        0) =
    false
is false
-/
#guard_msgs (error) in
def noneReadH :=
  (.lam (.lam (.taggedUnion_casesOn (.var (v♯1))
    (.payloadFirst (.var (v♯0)) (.ap (.var (v♯0)) (.var (v♯1))) .nil))) :
    Term sig0 [] _ (optTy ⇒ (optTy ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) _)

-- `fun e => match e with | a => a | b => b | c => c` is `fun e => e`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.branchAt 0 2 (Head.enumLit ↑⟨0, ⋯⟩)
          (Head.branchAt 0 1 (Head.enumLit ↑⟨1, ⋯⟩) (Head.branchAt 0 0 (Head.enumLit ↑⟨2, ⋯⟩) Head.empty))).isUnionEta
      three.nOfConstructors ((TyWf.enum three).isEnumOf three) =
    false
is false
-/
#guard_msgs (error) in
def enumEtaH :=
  (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨0, by decide⟩) (.enum_mk three ⟨1, by decide⟩)
      (.enum_mk three ⟨2, by decide⟩))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

-- `fun e => match e with | a => b | b => b | c => b` is `fun e => b`.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.branchAt 0 2 (Head.enumLit ↑⟨1, ⋯⟩)
        (Head.branchAt 0 1 (Head.enumLit ↑⟨1, ⋯⟩) (Head.branchAt 0 0 (Head.enumLit ↑⟨1, ⋯⟩) Head.empty))).isCaseLeaf =
    false
is false
-/
#guard_msgs (error) in
def enumConstH :=
  (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨1, by decide⟩) (.enum_mk three ⟨1, by decide⟩)
      (.enum_mk three ⟨1, by decide⟩))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

/-- A permutation of the constructors: a term. -/
def enumSwap :=
  (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨1, by decide⟩) (.enum_mk three ⟨0, by decide⟩)
      (.enum_mk three ⟨2, by decide⟩))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

/-- `match o with | some a => some a | none => some 0`: not every branch rebuilds its own
    constructor — a term. -/
def optSomeZero :=
  (.lam (.taggedUnion_casesOn (.var (v♯0))
    (.payloadFirst (.taggedUnion_mk optNat 0 (fields := .cons (.var (v♯0)) .nil))
      (.taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 0) .nil)) .nil)) :
    Term sig0 [] _ (optTy ⇒ optTy) _)

/-- `match o with | some _ => f o | none => 0`: the branch with a field may read `o` — a
    term. -/
def optReadInSome :=
  (.lam (.lam (.taggedUnion_casesOn (.var (v♯1))
    (.payloadFirst (.ap (.var (v♯1)) (.var (v♯2))) (.nat_mk 0) .nil))) :
    Term sig0 [] _ (optTy ⇒ (optTy ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) _)


/-- A value of `optNat`: constructor `0` applied to `3`. -/
def someThree :=
  (.taggedUnion_mk optNat 0 (fields := .cons (.nat_mk 3) .nil) :
    Term sig0 [] _ (TyWf.taggedUnion optNat) _)

/-- The field-less constructor of `optNat`. -/
def noneNat :=
  (.taggedUnion_mk optNat 1 (fields := .nil) :
    Term sig0 [] _ (TyWf.taggedUnion optNat) (.ctorAt 1 0))

example : run enumSwap ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
example : run enumSwap ⟨2, by decide⟩ = ⟨2, by decide⟩ := rfl
example : (run optSomeZero (run noneNat)).1 = ⟨0, by decide⟩ := rfl
example : (run optSomeZero (run someThree)).1 = ⟨0, by decide⟩ := rfl
example : run optReadInSome (run someThree) (fun _ => 9) = 9 := rfl
example : run optReadInSome (run noneNat) (fun _ => 9) = 0 := rfl

/-! ## Written by hand, then optimized: `#leanscript_optimize` -/

/-- `match o with | some _ => x | none => x` is `x`. -/
example : (#leanscript_optimize
    (.lam (.lam (.taggedUnion_casesOn (.var (v♯1)) (.payloadFirst (.var (v♯1)) (.var (v♯0)) .nil)))) :
    Term sig0 [] _ (optTy ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _) = .lam (.lam (.var (v♯0))) := rfl

/-- `match o with | some a => some a | none => none` is `o`. -/
example : (#leanscript_optimize (.lam (.taggedUnion_casesOn (.var (v♯0))
    (.payloadFirst (.taggedUnion_mk optNat 0 (fields := .cons (.var (v♯0)) .nil))
      (.taggedUnion_mk optNat 1 (fields := .nil)) .nil))) :
    Term sig0 [] _ (optTy ⇒ optTy) _) = .lam (.var (v♯0)) := rfl

/-- `match e with | a => a | b => b | c => c` is `e`. -/
example : (#leanscript_optimize (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨0, by decide⟩) (.enum_mk three ⟨1, by decide⟩)
      (.enum_mk three ⟨2, by decide⟩)))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _) = .lam (.var (v♯0)) := rfl

/-- `match e with | a => b | b => b | c => b` is `b`. -/
example : (#leanscript_optimize (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨1, by decide⟩) (.enum_mk three ⟨1, by decide⟩)
      (.enum_mk three ⟨1, by decide⟩)))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _) =
  .lam (.enum_mk three ⟨1, by decide⟩) := rfl

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- An enum. -/
inductive Colour where
  | red | green | blue
  deriving LeanScriptTyWf

/-- A union with two constructors with a field and one without. -/
inductive Shape where
  | circle (r : Nat)
  | square (s : Nat)
  | dot
  deriving LeanScriptTyWf

def optSame (o : Option Nat) (x : Nat) : Nat := match o with | none => x | some _ => x
def optTrue (o : Option Nat) : Bool := match o with | none => true | some _ => true
def optId (o : Option Nat) : Option Nat := match o with | none => none | some a => some a
def optMapId (o : Option Nat) : Option Nat := o.map id
def listId (l : List Nat) : List Nat := match l with | [] => [] | x :: xs => x :: xs
def colourId (c : Colour) : Colour := match c with | .red => .red | .green => .green | .blue => .blue
def colourId2 (c : Colour) : Colour := match c with | .red => c | .green => c | .blue => c
def colourConst (c : Colour) : Colour := match c with | .red => .green | .green => .green | .blue => .green
def colourWD (c : Colour) : Colour := match c with | .red => .red | _ => c
def shapeWD (s : Shape) : Shape := match s with | .circle r => .circle r | _ => s
def shapeId (s : Shape) : Shape := match s with | .circle r => .circle r | .square x => .square x | .dot => .dot
def shapeSwap (s : Shape) : Shape := match s with | .circle r => .square r | .square x => .circle x | .dot => .dot
def optNoneRead (o : Option Nat) (f : Option Nat → Nat) : Nat := match o with | none => f o | some a => a

def optSame_term := (#leanscript_to_term optSame : Term sig0 [] _ (tyWfOf (Option Nat) ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)
example : optSame_term = .lam (.lam (.var (v♯0))) := rfl
def optTrue_term := (#leanscript_to_term optTrue : Term sig0 [] _ (tyWfOf (Option Nat) ⇒ TyWf.prim .bool) .lam)
example : optTrue_term = .lam (.bool_mk true) := rfl
def optId_term := (#leanscript_to_term optId : Term sig0 [] _ (tyWfOf (Option Nat) ⇒ tyWfOf (Option Nat)) .lam)
example : optId_term = .lam (.var (v♯0)) := rfl
def optMapId_term := (#leanscript_to_term optMapId : Term sig0 [] _ (tyWfOf (Option Nat) ⇒ tyWfOf (Option Nat)) .lam)
example : optMapId_term = .lam (.var (v♯0)) := rfl
def listId_term := (#leanscript_to_term listId : Term sig0 [] _ (tyWfOf (List Nat) ⇒ tyWfOf (List Nat)) .lam)
example : listId_term = .lam (.var (v♯0)) := rfl
def colourId_term := (#leanscript_to_term colourId : Term sig0 [] _ (tyWfOf Colour ⇒ tyWfOf Colour) .lam)
example : colourId_term = .lam (.var (v♯0)) := rfl
def colourId2_term := (#leanscript_to_term colourId2 : Term sig0 [] _ (tyWfOf Colour ⇒ tyWfOf Colour) .lam)
example : colourId2_term = .lam (.var (v♯0)) := rfl
def colourConst_term := (#leanscript_to_term colourConst : Term sig0 [] _ (tyWfOf Colour ⇒ tyWfOf Colour) .lam)
example : colourConst_term = .lam (.enum_mk _ ⟨1, by decide⟩) := rfl
def colourWD_term := (#leanscript_to_term colourWD : Term sig0 [] _ (tyWfOf Colour ⇒ tyWfOf Colour) .lam)
example : colourWD_term = .lam (.var (v♯0)) := rfl
def shapeWD_term := (#leanscript_to_term shapeWD : Term sig0 [] _ (tyWfOf Shape ⇒ tyWfOf Shape) .lam)
example : shapeWD_term = .lam (.var (v♯0)) := rfl
def shapeId_term := (#leanscript_to_term shapeId : Term sig0 [] _ (tyWfOf Shape ⇒ tyWfOf Shape) .lam)
example : shapeId_term = .lam (.var (v♯0)) := rfl
def shapeSwap_term := (#leanscript_to_term shapeSwap : Term sig0 [] _ (tyWfOf Shape ⇒ tyWfOf Shape) .lam)
-- Swapping the constructors is not an η-redex: the dispatch stays.
/--
info: ((Term.var DeBruijnProj.head).taggedUnion_casesOn
      (TaggedUnionCases.payloadFirst
        (Term.taggedUnion_mk
          (LeanTaggedUnionSchema.payloadFirst
            { head := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }, tail := [] }
            [{ toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }] [[]])
          1 shapeSwap_term._proof_1 (Spine.cons (Term.var DeBruijnProj.head) Spine.nil) ⋯)
        (Term.taggedUnion_mk
          (LeanTaggedUnionSchema.payloadFirst
            { head := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }, tail := [] }
            [{ toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }] [[]])
          0 shapeSwap_term._proof_3 (Spine.cons (Term.var DeBruijnProj.head) Spine.nil) ⋯)
        (TaggedUnionCasesRest.cons
          (Term.taggedUnion_mk
            (LeanTaggedUnionSchema.payloadFirst
              { head := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }, tail := [] }
              [{ toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 }] [[]])
            2 shapeSwap_term._proof_4 Spine.nil shapeSwap_term._proof_5)
          TaggedUnionCasesRest.nil))
      ⋯ ⋯ ⋯ ⋯ ⋯ ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) shapeSwap_term
def optNoneRead_term := (#leanscript_to_term optNoneRead : Term sig0 [] _ (tyWfOf (Option Nat) ⇒ (tyWfOf (Option Nat) ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) .lam)
-- In the `none` branch, `f o` is `f none`.
/--
info: (((Term.var DeBruijnProj.head.tail).taggedUnion_casesOn
          (TaggedUnionCases.skip
            ((Term.var DeBruijnProj.head).ap
              (Term.taggedUnion_mk
                (LeanTaggedUnionSchema.skip
                  (CtorsWithPayload.here
                    { head := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := optSame_term._proof_3 },
                      tail := [] }
                    []))
                0 optNoneRead_term._proof_3 Spine.nil shapeSwap_term._proof_5)
              ⋯ ⋯)
            (CtorsWithPayloadCases.here (Term.var DeBruijnProj.head) TaggedUnionCasesRest.nil))
          ⋯ ⋯ ⋯ ⋯ ⋯ ⋯).lam
      ⋯).lam
  ⋯
-/
#guard_msgs in
#reduce (proofs := false) (types := false) optNoneRead_term

end TermTests.UnionRedexes
