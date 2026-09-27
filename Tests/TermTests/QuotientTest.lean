module

public import LeanScript.Term.Build
public meta import LeanScript.TermElab.ToTerm
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Quotients and proof-carrying data (§6 of `proposals/UnrepresentableLeanTypes.lean`)

The language has no quotients and no proofs.  Both are read through their **erasure**:

* A proof field is dropped, so a structure of one value and proofs is that value:
  `Pos` (`n : Nat`, `pos : n > 0`) is `nat`.
* A quotient `Quot r` (and `Quotient s`, which unfolds to it) is read as its **carrier**
  (`LeanScript.Gen.quotCarrier?`): a value of the quotient is one of its representatives.
  `QT.node : Quot (· % 2 = · % 2) → QT → QT` has a `nat` field, so `QT` is a declared
  datatype `leaf | node nat QT`.
  - `Quot.mk r a` (`Quotient.mk s a`, `⟦a⟧`) is `a`;
  - a function on the quotient, `Quot.lift f h q` (`Quot.liftOn`, `Quotient.lift`,
    `Quotient.lift₂`, `Quot.rec`, `Quot.recOn`, `Quot.hrecOn`, `Quot.recOnSubsingleton`, …),
    is `f` applied to the representative;
  - a decision on a quotient (`decide (p = q)`, by `Quot.recOnSubsingleton`) is the
    decision of its instance at the representative;
  - a function *returning* a quotient that is not a `Quot.mk` (after unfolding) is refused:
    the language would need a representative (`Quot.out` is not computable).

This is faithful for everything Lean can write on a quotient: `Quot.lift f h` only sees
representatives, and `h` says the result does not depend on which one.  But the erased type
has more values than the Lean one (like a subtype, `Fin n`, or an erased index): the quotient
of `Nat` by parity has two values, it is read as `Nat`.  `TermTests/QuotientProofs.lean`
proves that every `QT` has a value in the language, and that the translation of `QT.odds` is
correct on every representative of every `QT`.

Types of no, one or two values stay refused, also behind a quotient (a `Unit` carrier), and
two points are still only `bool`.
-/

namespace QuotientTest

open LeanScript

/-- Parity. -/
def Par (a b : Nat) : Prop := a % 2 = b % 2

inductive QT where
  | leaf
  | node : Quot (fun (a b : Nat) => a % 2 = b % 2) → QT → QT

structure Pos where
  n : Nat
  pos : n > 0 -- erased

leanscript_signature Prog where
  qt := QT
  pos := Pos

/-! ## The types -/

-- a proof is erased: `Pos` is its number
-- [SKIPPED BY PROFILE_LAKE] example : Prog.pos = .nat := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty Pos : Ty []) = .nat := rfl

-- a quotient is its carrier
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Quot Par) : Ty []) = .nat := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Quot Par → Array (Quot Par)) : Ty []) = .fn .nat (.array .nat) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

-- `QT` is a declared datatype: `leaf`, or `node` of a number and a `QT`
-- [SKIPPED BY PROFILE_LAKE] example : Prog.qt = .data (.here 0) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : Prog.block0 = .cons (.union (.two₁ .nullary
-- [SKIPPED BY PROFILE_LAKE]     (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil := rfl

/--
info: QuotientTest.Prog.QT.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0)) o1) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0)) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor QT.node

/-! ## Values: a class is given by a representative -/

def q3 : QT := .node (Quot.mk _ 3) (.node (Quot.mk _ 4) .leaf)
def q3T := #leanscript_to_term q3

-- [SKIPPED BY PROFILE_LAKE] example : q3T = .ret (Prog.QT.node (.lit .nat 3) (Prog.QT.node (.lit .nat 4) Prog.QT.leaf)) := rfl

/-! ## Functions on quotients: applied to the representative -/

/-- The number of odd classes. -/
def QT.odds : QT → Nat
  | .leaf => 0
  | .node q t => Quot.lift (fun a => a % 2) (fun _ _ h => h) q + t.odds

def oddsT := #leanscript_to_term QT.odds
-- [SKIPPED BY PROFILE_LAKE] example : oddsT.run q3T.run = (1 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] #guard q3.odds == 1

-- the same with `Quot.liftOn`
def QT.odds' : QT → Nat
  | .leaf => 0
  | .node q t => q.liftOn (fun a => a % 2) (fun _ _ h => h) + t.odds'

def odds'T := #leanscript_to_term QT.odds'
-- [SKIPPED BY PROFILE_LAKE] example : odds'T.run q3T.run = (1 : Nat) := by kernel_rfl

-- another representative of the same classes gives the same answer
-- [SKIPPED BY PROFILE_LAKE] example : oddsT.run (Prog.QT.node (.lit .nat 5) (Prog.QT.node (.lit .nat 0) Prog.QT.leaf)
-- [SKIPPED BY PROFILE_LAKE]     (Φ := []) (Γ := [])).run = (1 : Nat) := by kernel_rfl

/-- `Quot.lift` on a parameter: the representative is bound, then `f` applied to it. -/
def parity (q : Quot Par) : Nat := Quot.lift (fun a => a % 2) (fun _ _ h => h) q

/--
info: fun {ks} {Δ} =>
  id
    (Term.letV Usage1ω.many
      (Val.lam
        (Body.closed
          (Term.ret
            (PExpr.neu
              (Neu.extern LeanInitPureExtern.lean_nat_mod__Nat_mod
                (Args.cons (PExpr.neu (Neu.var (UVar.head ⋯))) (Args.cons (PExpr.lit LeanPrimTy.nat 2) Args.nil)) ⋯)))))
      (Term.ret
        (PExpr.kvar
          KVar.head))) : {ks : List Nat} →
  {Δ : DSig ks} → Term Δ 0 [] [] ((Ty.prim LeanPrimTy.nat).fn (Ty.prim LeanPrimTy.nat)) [] none
-/
#guard_msgs in
#check #leanscript_to_term parity

/-- `Quot.hrecOn` with a constant motive. -/
def parity' (q : Quot Par) : Nat :=
  Quot.hrecOn (motive := fun _ => Nat) q (fun a => a % 2) (fun _ _ h => heq_of_eq h)
def parity'T := #leanscript_to_term parity'
-- [SKIPPED BY PROFILE_LAKE] example : (parity'T (Δ := DSig.nil)).run (7 : Nat) = (1 : Nat) := rfl

/-! ## `Quotient` -/

/-- Numbers modulo 3. -/
def mod3 : Setoid Nat :=
  ⟨fun a b => a % 3 = b % 3, ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩⟩

def rem3 (q : Quotient mod3) : Nat := Quotient.lift (s := mod3) (fun a => a % 3) (fun _ _ h => h) q
def succ3 (n : Nat) : Quotient mod3 := Quotient.mk mod3 (n + 1)
def sum3 (p q : Quotient mod3) : Nat :=
  Quotient.lift₂ (s₁ := mod3) (s₂ := mod3) (fun a b => (a + b) % 3) (fun a b c d h1 h2 => by
    have h1 : a % 3 = c % 3 := h1
    have h2 : b % 3 = d % 3 := h2
    show (a + b) % 3 = (c + d) % 3
    omega) p q

def rem3T := #leanscript_to_term rem3
def succ3T := #leanscript_to_term succ3
def sum3T := #leanscript_to_term sum3
-- [SKIPPED BY PROFILE_LAKE] example : (rem3T (Δ := DSig.nil)).run ((succ3T (Δ := DSig.nil)).run (7 : Nat)) = (2 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (sum3T (Δ := DSig.nil)).run ((succ3T (Δ := DSig.nil)).run (7 : Nat)) (5 : Nat) = (1 : Nat) := rfl

/-! ## Externs on quotients: given the class of the representative -/

instance : DecidableEq (Quot Par) := fun a b =>
  Quot.recOnSubsingleton (motive := fun a => Decidable (a = b)) a fun x =>
  Quot.recOnSubsingleton (motive := fun b => Decidable (Quot.mk Par x = b)) b fun y =>
    if h : x % 2 = y % 2 then isTrue (Quot.sound h)
    else isFalse fun e => h (congrArg (Quot.lift (fun a => a % 2) (fun _ _ h => h)) e)

def same (p q : Quot Par) : Bool := decide (p = q)
def sameT := #leanscript_to_term same

/--
info: fun {ks} {Δ} =>
  id
    (Term.letV Usage1ω.many
      (Val.lam
        (Body.closed
          (Term.letV Usage1ω.many
            (Val.lam
              (Body.opened
                (id
                  (Term.ret
                    (PExpr.neu
                      (Neu.extern LeanInitPureExtern.lean_nat_dec_eq__Nat_decEq
                        (Args.cons
                          (PExpr.neu
                            (Neu.extern LeanInitPureExtern.lean_nat_mod__Nat_mod
                              (Args.cons (PExpr.neu (Neu.var (UVar.head ⋯).tail))
                                (Args.cons (PExpr.lit LeanPrimTy.nat 2) Args.nil))
                              ⋯))
                          (Args.cons
                            (PExpr.neu
                              (Neu.extern LeanInitPureExtern.lean_nat_mod__Nat_mod
                                (Args.cons (PExpr.neu (Neu.var (UVar.head ⋯)))
                                  (Args.cons (PExpr.lit LeanPrimTy.nat 2) Args.nil))
                                ⋯))
                            Args.nil))
                        ⋯))))
                ⋯))
            (Term.ret (PExpr.kvar KVar.head)))))
      (Term.ret
        (PExpr.kvar
          KVar.head))) : {ks : List Nat} →
  {Δ : DSig ks} →
    Term Δ 0 [] [] ((Ty.prim LeanPrimTy.nat).fn ((Ty.prim LeanPrimTy.nat).fn (Ty.prim LeanPrimTy.bool))) [] none
-/
#guard_msgs in
#check #leanscript_to_term same

-- `3` and `5` are representatives of the same class
-- [SKIPPED BY PROFILE_LAKE] example : (sameT (Δ := DSig.nil)).run (3 : Nat) (5 : Nat) = true := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (sameT (Δ := DSig.nil)).run (3 : Nat) (4 : Nat) = false := rfl

/-- A structure with a quotient and an array of quotients: a record of `nat` and `nat` array. -/
structure S where
  q : Quot Par
  xs : Array (Quot Par)

def S.odds (s : S) : Nat :=
  s.xs.foldl (fun acc q => acc + Quot.lift (fun a => a % 2) (fun _ _ h => h) q) (parity s.q)

def sOddsT := #leanscript_to_term S.odds
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty S : Ty []) = .pair .nat (.array .nat) := rfl
-- the fold is `Comp.array_foldl` over the array of the representatives
-- [SKIPPED BY PROFILE_LAKE] example : (sOddsT (Δ := DSig.nil)).run ((3 : Nat), (#[1, 2, 5] : Array Nat)) = (3 : Nat) := rfl

/-! ## `Pos`: the proof is erased -/

def Pos.pred (p : Pos) : Nat := p.n - 1
def Pos.one : Pos := ⟨1, by decide⟩
def Pos.succ (n : Nat) : Pos := ⟨n + 1, by omega⟩

def predT := #leanscript_to_term Pos.pred
def oneT := #leanscript_to_term Pos.one
def succT := #leanscript_to_term Pos.succ
-- [SKIPPED BY PROFILE_LAKE] example : oneT (Δ := DSig.nil) = .ret (.lit .nat 1) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (predT (Δ := DSig.nil)).run ((succT (Δ := DSig.nil)).run (4 : Nat)) = (4 : Nat) := rfl

/-! ## Refusals -/

/-- A quotient of `Unit` is read as `Unit`: one value, refused. -/
inductive UQ where
  | a
  | b (q : Quot (fun (_ _ : Unit) => True)) (n : Nat)

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature ProgU where
  u := UQ

-- [SKIPPED BY PROFILE_LAKE] /-- A quotient of `Bool` is `bool` (two points are only `bool`), even when it has one value. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Quot (fun (_ _ : Bool) => True)) : Ty []) = .bool := rfl

/-- A call returning a class that is not built by `Quot.mk`: no representative to compute. -/
opaque pick : Nat → Quot Par := fun n => Quot.mk _ n
def usePick (n : Nat) : Quot Par := pick n

/--
error: LeanScript: the call
  pick n
returns a value of a quotient, read as its carrier: the language would need a representative of the class (`Quot.out` is not computable)
-/
#guard_msgs in
#check #leanscript_to_term usePick

end QuotientTest
