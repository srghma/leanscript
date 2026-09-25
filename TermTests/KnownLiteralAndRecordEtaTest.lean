module

public import LeanScript.Eval
public import LeanScript.Ty.Instances
public meta import LeanScript.Ty.Deriving
public meta import LeanScript.ToTerm.Elab

/-!
# More redexes: a read of a scrutinee known to be a literal, dispatches on numbers whose
# branches are the same leaf, and the record η-redex

* **A read of a scrutinee whose value is a known literal.**  In a branch of a dispatch on a
  variable `x` for a constructor with no fields, `x` *is* that constructor, a literal:
  `true`/`false` in the branches of an `if`, the branch's constructor in a dispatch on an
  enum, `0` in the zero branch of a dispatch on a natural number.  A read of `x` there is
  a redex — the literal is what it reads — so `Term.bool_casesOn`, `Term.enum_casesOn`,
  `Term.enum_casesOnWithDefault` (for its named branches) and `Term.nat_casesOn` (for its
  zero branch) ask that those branches do not read `x` at all (`hLit`,
  `Head.readsScrutinee`).  The translation substitutes the literal, and reduces what that
  makes a redex: `b && b` is `if b then b else false`, which becomes
  `if b then true else false`, which is `b`.
* **The record η-redex.**  `match p with | (a, b) => (a, b)` is `p`.  A constructor
  applied to the innermost variables in order records it in its head
  (`Head.rebuild n`, computed by `Head.ctorOf`), and `Term.record_casesOn` asks that its
  body is not a record built that way from exactly the fields it binds (`hEta`,
  `Head.isRecordEta`).  The translation answers the scrutinee instead: `{ s with b := s.b }`
  is `s`.
* **A dispatch on a number whose branches are the same leaf.**  As `if c then x else x`
  already was, `match n with | 0 => x | _ + 1 => x` and
  `match i with | .ofNat _ => x | .negSucc _ => x` are `x` (`hSame`, `Head.sameLeafOver`,
  `Head.sameLeafPast`: the successor branch binds one variable more).

Each redex written by hand is rejected (the errors are pinned), the nearby legal forms are
accepted, `#leanscript_optimize` turns each redex into the expected term (by `rfl`), and
the translations of Lean functions are pinned by printed snapshots and run against the
Lean functions by `rfl`.
-/

namespace TermTests.KnownLiteral

open LeanScript

/-- The empty signature. -/
def sig0 : Sig := ⟨[], by decide⟩

/-- Running a closed term of `sig0`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig0) GlobalEnv.nil $t)

/-- An enum of three constructors, for terms written by hand. -/
def three : LeanEnumSchema := ⟨0, 0⟩

/-! ## Written by hand: what the grammar rejects and accepts -/

-- `fun b => if b then b else false` (what `b && b` is): in the `then` branch, `b` is `true`.
/--
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).readsScrutinee (Usage.single DeBruijn.head + 0) = false
is false
-/
#guard_msgs (error) in
def andSelfH :=
  (.lam (.bool_casesOn (.var (v♯0)) (.var (v♯0)) (.bool_mk false)) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) _)

/-- `fun b f => if b then f true else 0`: the literal is written, a term. -/
def ifLitArg :=
  (.lam (.lam (.bool_casesOn (.var (v♯1)) (.ap (.var (v♯0)) (.bool_mk true)) (.nat_mk 0))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ (TyWf.prim .bool ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) _)

example : run ifLitArg true (fun b => if b then 7 else 8) = 7 := rfl

-- `fun n => match n with | 0 => n | k + 1 => k`: in the zero branch, `n` is `0`.
/--
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).readsScrutinee (Usage.single DeBruijn.head) = false
is false
-/
#guard_msgs (error) in
def natZeroH :=
  (.lam (.nat_casesOn (.var (v♯0)) (.var (v♯0)) (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _)

/-- `fun n => match n with | 0 => 1 | k + 1 => n`: the successor branch may read `n` —
    there it is `k + 1`, a computation, not a literal — a term. -/
def natSuccReads :=
  (.lam (.nat_casesOn (.var (v♯0)) (.nat_mk 1) (.var (v♯1))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _)

example : run natSuccReads 0 = 1 := rfl
example : run natSuccReads 5 = 5 := rfl

-- `fun n x => match n with | 0 => x | _ + 1 => x` is `fun n x => x`.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).sameLeafOver (Head.var (Var.index DeBruijn.head.tail)) = false
is false
-/
#guard_msgs (error) in
def natSameH :=
  (.lam (.lam (.nat_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯1)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _)

-- `fun i x => match i with | .ofNat _ => x | .negSucc _ => x` is `fun i x => x`.
/--
error: could not synthesize default value for parameter 'hSame' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head.tail)).sameLeafPast (Head.var (Var.index DeBruijn.head.tail)) = false
is false
-/
#guard_msgs (error) in
def intSameH :=
  (.lam (.lam (.int_casesOn (.var (v♯1)) (.var (v♯1)) (.var (v♯1)))) :
    Term sig0 [] _ (TyWf.prim .int ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _)

/-- `fun i => match i with | .ofNat n => n | .negSucc n => n`: each branch reads its own
    variable, not the same leaf of the context outside — a term. -/
def intOwn :=
  (.lam (.int_casesOn (.var (v♯0)) (.var (v♯0)) (.var (v♯0))) :
    Term sig0 [] _ (TyWf.prim .int ⇒ TyWf.prim .nat) _)

example : run intOwn (-3) = 2 := rfl

-- `fun e => match e with | a => b | b => e | c => e`: in each branch, `e` is its constructor.
/--
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).readsScrutinee
      (Usage.cond 0 + (Usage.single DeBruijn.head).cond + (Usage.single DeBruijn.head).cond) =
    false
is false
-/
#guard_msgs (error) in
def enumH :=
  (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨1, by decide⟩) (.var (v♯0)) (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

-- A named branch of a dispatch with a default: there, too, `e` is known.
/--
error: could not synthesize default value for parameter 'hLit' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.var (Var.index DeBruijn.head)).readsScrutinee (Usage.single DeBruijn.head).cond = false
is false
-/
#guard_msgs (error) in
def enumSomeH :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0)) (.last ⟨2, by decide⟩ (.var (v♯0)))
     (.enum_mk three ⟨0, by decide⟩)) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

/-- `fun e => match e with | a => b | _ => e`: the default branch knows no constructor, and
    may read `e` — a term. -/
def enumDefaultReads :=
  (.lam (.enum_casesOnWithDefault (.var (v♯0)) (.last ⟨0, by decide⟩ (.enum_mk three ⟨1, by decide⟩))
     (.var (v♯0))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _)

example : run enumDefaultReads ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl
example : run enumDefaultReads ⟨2, by decide⟩ = ⟨2, by decide⟩ := rfl

/-! ## Written by hand, then optimized: `#leanscript_optimize` -/

/-- `if b then b else false` is `b`. -/
example : (#leanscript_optimize (.lam (.bool_casesOn (.var (v♯0)) (.var (v♯0)) (.bool_mk false))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) _) = .lam (.var (v♯0)) := rfl

/-- `if b then f b else 0` is `if b then f true else 0`. -/
example : (#leanscript_optimize
    (.lam (.lam (.bool_casesOn (.var (v♯1)) (.ap (.var (v♯0)) (.var (v♯1))) (.nat_mk 0)))) :
    Term sig0 [] _ (TyWf.prim .bool ⇒ (TyWf.prim .bool ⇒ TyWf.prim .nat) ⇒ TyWf.prim .nat) _) =
  ifLitArg := rfl

/-- `match n with | 0 => n | k + 1 => k` is `match n with | 0 => 0 | k + 1 => k`. -/
example : (#leanscript_optimize (.lam (.nat_casesOn (.var (v♯0)) (.var (v♯0)) (.var (v♯0)))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) _) =
  .lam (.nat_casesOn (.var (v♯0)) (.nat_mk 0) (.var (v♯0))) := rfl

/-- `match n with | 0 => x | _ + 1 => x` is `x`. -/
example : (#leanscript_optimize
    (.lam (.lam (.nat_casesOn (.var (v♯1)) (.var (v♯0)) (.var (v♯1))))) :
    Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _) =
  .lam (.lam (.var (v♯0))) := rfl

/-- `match i with | .ofNat _ => x | .negSucc _ => x` is `x`. -/
example : (#leanscript_optimize
    (.lam (.lam (.int_casesOn (.var (v♯1)) (.var (v♯1)) (.var (v♯1))))) :
    Term sig0 [] _ (TyWf.prim .int ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) _) =
  .lam (.lam (.var (v♯0))) := rfl

/-- `match e with | a => b | b => e | c => e` is `match e with | a => b | b => b | c => c`. -/
example : (#leanscript_optimize (.lam (.enum_casesOn (.var (v♯0))
    (.three (.enum_mk three ⟨1, by decide⟩) (.var (v♯0)) (.var (v♯0))))) :
    Term sig0 [] _ (TyWf.enum three ⇒ TyWf.enum three) _) =
  .lam (.enum_casesOn (.var (v♯0)) (.three (.enum_mk three ⟨1, by decide⟩)
    (.enum_mk three ⟨1, by decide⟩) (.enum_mk three ⟨2, by decide⟩))) := rfl

/-! ## Translated: what `#leanscript_to_term` emits -/

/-- `b && b` is `b`. -/
def andSelf (b : Bool) : Bool := b && b

def andSelf_term :=
  (#leanscript_to_term andSelf : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

example : andSelf_term = .lam (.var (v♯0)) := rfl

/-- `b || b` is `b`. -/
def orSelf (b : Bool) : Bool := b || b

def orSelf_term :=
  (#leanscript_to_term orSelf : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

example : orSelf_term = .lam (.var (v♯0)) := rfl

/-- `b == b` is `true`. -/
def beqSelf (b : Bool) : Bool := b == b

def beqSelf_term :=
  (#leanscript_to_term beqSelf : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .bool) .lam)

example : beqSelf_term = .lam (.bool_mk true) := rfl

/-- In the `then` branch, `b && n == 3` is `n == 3`:
    `if b then (if n == 3 then 1 else 2) else 0`. -/
def ifPass (b : Bool) (n : Nat) : Nat := if b then (if b && n == 3 then 1 else 2) else 0

def ifPass_term :=
  (#leanscript_to_term ifPass : Term sig0 [] _ (TyWf.prim .bool ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : run ifPass_term true 3 = 1 := rfl
example : run ifPass_term true 4 = 2 := rfl
example : run ifPass_term false 3 = 0 := rfl

/--
info: Term.atom
  (Atom.lam
    (Term.atom
      (Atom.lam
        (Term.comp
          (Comp.bool_casesOn (Ref.var DeBruijnProj.head.tail)
            (Term.letE
              (Comp.externCall
                (Spine.cons (Atom.ref (Ref.var DeBruijnProj.head)) (Spine.cons (Atom.nat_mk 3) Spine.nil))
                (fun vs => LeanInitPureExtern.preludeExtern (PreludeExtern.lean_nat_dec_eq__Nat_decEq vs.1 vs.2.1)) ⋯ ⋯)
              (Term.comp
                (Comp.bool_casesOn (Ref.var DeBruijnProj.head) (Term.atom (Atom.nat_mk 1)) (Term.atom (Atom.nat_mk 2))
                  ifPass_term._proof_5 ifPass_term._proof_6 ⋯ ⋯)
                ifPass_term._proof_9)
              ⋯ ⋯ ⋯ ⋯)
            (Term.atom (Atom.nat_mk 0)) ifPass_term._proof_14 ifPass_term._proof_15 ⋯ ⋯)
          ifPass_term._proof_18)
        ⋯))
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) ifPass_term

/-- In the zero branch, `n + 5` is `0 + 5`, a closed computation, which is `5`. -/
def natZeroRead (n : Nat) : Nat :=
  match n with
  | 0 => n + 5
  | k + 1 => k

def natZeroRead_term :=
  (#leanscript_to_term natZeroRead : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : natZeroRead_term = .lam (.nat_casesOn (.var (v♯0)) (.nat_mk 5) (.var (v♯0))) := rfl
example : run natZeroRead_term 0 = 5 := rfl
example : run natZeroRead_term 4 = 3 := rfl

/-- `match n with | 0 => x | _ + 1 => x` is `x`. -/
def natSame (n x : Nat) : Nat :=
  match n with
  | 0 => x
  | _ + 1 => x

def natSame_term :=
  (#leanscript_to_term natSame : Term sig0 [] _ (TyWf.prim .nat ⇒ TyWf.prim .nat ⇒ TyWf.prim .nat) .lam)

example : natSame_term = .lam (.lam (.var (v♯0))) := rfl

/-- An enum. -/
inductive Colour where
  | red
  | green
  | blue
  deriving LeanScriptTyWf

/-- The branches for `green` and `blue` read `c`: in each, `c` is the branch's constructor. -/
def colourKeep (c : Colour) : Nat × Colour :=
  match c with
  | .red => (0, .green)
  | .green => (1, c)
  | .blue => (2, c)

def colourKeep_term :=
  (#leanscript_to_term colourKeep : Term sig0 [] _ (tyWfOf Colour ⇒ tyWfOf (Nat × Colour)) .lam)

/--
info: Term.atom
  (Atom.lam
    (Term.comp
      (Comp.enum_casesOn (Ref.var DeBruijnProj.head)
        (EnumCases.three
          (Term.atom
            (Atom.val
              (Comp.record_mk
                { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := ifPass_term._proof_1 },
                  snd := { toTy := Ty.shape (TyShape.enum { shift := Int.ofNat 0 }), isWf := colourKeep_term._proof_1 },
                  rest := [] }
                (Spine.cons (Atom.nat_mk 0)
                  (Spine.cons (Atom.enum_mk { shift := Int.ofNat 0 } ⟨1, colourKeep_term._proof_2⟩) Spine.nil)))
              ⋯))
          (Term.atom
            (Atom.val
              (Comp.record_mk
                { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := ifPass_term._proof_1 },
                  snd := { toTy := Ty.shape (TyShape.enum { shift := Int.ofNat 0 }), isWf := colourKeep_term._proof_1 },
                  rest := [] }
                (Spine.cons (Atom.nat_mk 1)
                  (Spine.cons (Atom.enum_mk { shift := Int.ofNat 0 } ⟨1, colourKeep_term._proof_2⟩) Spine.nil)))
              ⋯))
          (Term.atom
            (Atom.val
              (Comp.record_mk
                { fst := { toTy := Ty.shape (TyShape.prim LeanPrimTy.nat), isWf := ifPass_term._proof_1 },
                  snd := { toTy := Ty.shape (TyShape.enum { shift := Int.ofNat 0 }), isWf := colourKeep_term._proof_1 },
                  rest := [] }
                (Spine.cons (Atom.nat_mk 2)
                  (Spine.cons (Atom.enum_mk { shift := Int.ofNat 0 } ⟨2, colourKeep_term._proof_3⟩) Spine.nil)))
              ⋯)))
        ⋯ ⋯ colourKeep_term._proof_7 colourKeep_term._proof_8)
      colourKeep_term._proof_9)
    ⋯)
-/
#guard_msgs in
#reduce (proofs := false) (types := false) colourKeep_term

/-! ## The record η-redex -/

/-- The schema of a record of two naturals, for terms written by hand. -/
def pairSchema : LeanRecordSchema TyWf := ⟨TyWf.prim .nat, TyWf.prim .nat, []⟩

/-- A record of two naturals. -/
abbrev pairRec : TyWf := TyWf.record pairSchema

-- `fun p => match p with | (a, b) => (a, b)` is `fun p => p`.
/--
error: could not synthesize default value for parameter 'hEta' using tactics
---
error: Tactic `decide` proved that the proposition
  (Head.ctorOf [Head.var (Var.index DeBruijn.head), Head.var (Var.index DeBruijn.head.tail)]).isRecordEta
      pairSchema.toList.length pairRec =
    false
is false
-/
#guard_msgs (error) in
def recordEtaH :=
  (.lam (.record_casesOn (.var (v♯0))
    (.record_mk pairSchema (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil)))) :
    Term sig0 [] _ (pairRec ⇒ pairRec) _)

/-- `fun p => match p with | (a, b) => (b, a)`: the fields out of order, a term. -/
def recordSwap :=
  (.lam (.record_casesOn (.var (v♯0))
    (.record_mk pairSchema (.cons (.var (v♯1)) (.cons (.var (v♯0)) .nil)))) :
    Term sig0 [] _ (pairRec ⇒ pairRec) _)

/-- The η-redex, optimized: the identity. -/
example : (#leanscript_optimize (.lam (.record_casesOn (.var (v♯0))
    (.record_mk pairSchema (.cons (.var (v♯0)) (.cons (.var (v♯1)) .nil))))) :
    Term sig0 [] _ (pairRec ⇒ pairRec) _) = .lam (.var (v♯0)) := rfl

/-- `match p with | (a, b) => (a, b)` is `p`. -/
def pairId (p : Nat × Nat) : Nat × Nat :=
  match p with
  | (a, b) => (a, b)

def pairId_term :=
  (#leanscript_to_term pairId : Term sig0 [] _ (tyWfOf (Nat × Nat) ⇒ tyWfOf (Nat × Nat)) .lam)

example : pairId_term = .lam (.var (v♯0)) := rfl

/-- A structure of three fields. -/
structure Triple where
  a : Nat
  b : Bool
  c : Nat
  deriving LeanScriptTyWf

/-- An update that writes back the field it reads is the structure itself. -/
def sameUpdate (s : Triple) : Triple := { s with b := s.b }

def sameUpdate_term :=
  (#leanscript_to_term sameUpdate : Term sig0 [] _ (tyWfOf Triple ⇒ tyWfOf Triple) .lam)

example : sameUpdate_term = .lam (.var (v♯0)) := rfl

end TermTests.KnownLiteral
