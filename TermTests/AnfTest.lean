module

public import LeanScript.Eval
public meta import LeanScript.KernelRfl

@[expose] public section

/-!
# Strict A-normal form, pinned

`LeanScript.Term` is in **strict A-normal form by construction**: the operands of a step
are atoms, a `let` binds one computation step (`LeanScript.Comp`) and never a dispatch or
a fold, and a dispatch or a fold is always the last thing a block does.  A dispatch or a
fold whose value is *used* is written with a **join point** (`Term.letJ`) that its tails
jump to (`Term.jump`, `LeanScript.Dest.jump`); join points live in their own context
(`LeanScript.JCtx`), apart from the variables.

The functions named like the direct-style constructors (`Term.ap`, `Term.bool_casesOn'`,
`Term.nat_rec'`, `Term.letE'`, …) put arbitrary terms in that form.  Each example below
states, by `rfl`, the exact A-normal term such a function builds, and then checks by the
kernel that it computes what the direct-style term means.
-/

namespace TermTests.Anf

open LeanScript

/-- A signature with one declaration, `double : nat ⇒ nat`. -/
def doubleSig : Sig := ⟨[⟨"double", TyWf.prim .nat ⇒ TyWf.prim .nat⟩], by decide⟩

/-- The value of `double`. -/
def doubleEnv : GlobalEnv doubleSig.decls := (fun n => 2 * n, PUnit.unit)

abbrev natT : TyWf := TyWf.prim .nat
abbrev boolT : TyWf := TyWf.prim .bool

/-! ## A nested application: the inner call is named by a `let` -/

/-- `double (double 1)`. -/
def doubleTwice : Term doubleSig [] natT :=
  .ap (.global .here) (.ap (.global .here) (.nat_mk 1))

example : doubleTwice =
    .letE (.ap (.global .here) (.nat_mk 1)) (.ret (.ap (.global .here) (.var .head))) := rfl

example : Term.run doubleEnv doubleTwice = 4 := by kernel_rfl

/-! ## A dispatch used as an operand: it becomes the tail, and what uses it a join point -/

/-- `fun b => double (if b then 1 else 2)`. -/
def doubleIf : Term doubleSig [] (boolT ⇒ natT) :=
  .lam (.ap (.global .here) (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 2)))

example : doubleIf =
    .lam (.letJ (.ret (.ap (.global .here) (.var .head)))
      (.bool_casesOn (.var .head) (.jump .head (.nat_mk 1)) (.jump .head (.nat_mk 2)))) := rfl

example : Term.run doubleEnv doubleIf true = 2 := by kernel_rfl
example : Term.run doubleEnv doubleIf false = 4 := by kernel_rfl

/-! ## A dispatch bound by a `let`: the body becomes the join point -/

/-- `fun n => let m := (match n with | 0 => 10 | k + 1 => k); double m`. -/
def letOfMatch : Term doubleSig [] (natT ⇒ natT) :=
  .lam (.letE' (.nat_casesOn' (.var (v♯0)) (.nat_mk 10) (.var (v♯0)))
    (.ap (.global .here) (.var (v♯0))))

example : letOfMatch =
    .lam (.letJ (.ret (.ap (.global .here) (.var .head)))
      (.nat_casesOn (.var .head) (.jump .head (.nat_mk 10)) (.jump .head (.var .head)))) := rfl

example : Term.run doubleEnv letOfMatch 0 = 20 := by kernel_rfl
example : Term.run doubleEnv letOfMatch 8 = 14 := by kernel_rfl

/-! ## A fold used as an operand: its answer is sent to a join point -/

/-- `fun n => double (Nat.rec 0 (fun _ ih => ih + 1) n)`, with the successor written as an
    extern call. -/
def doubleFold : Term doubleSig [] (natT ⇒ natT) :=
  .lam (.ap (.global .here)
    (.nat_rec' 0 (.var (v♯0)) (.cons (.nat_mk 0) .nil)
      (.externCall (.cons (.var (v♯1)) .nil) fun vs => .lean_nat_add vs.1 1)))

example : doubleFold =
    .lam (.letJ (.ret (.ap (.global .here) (.var .head)))
      (.nat_rec 0 (.var .head) (.cons (.nat_mk 0) .nil)
        (.ret (.externCall (.cons (.var (.tail .head)) .nil) fun vs => .lean_nat_add vs.1 1))
        (.jump .head))) := rfl

example : Term.run doubleEnv doubleFold 5 = 10 := by kernel_rfl

/-! ## Two dispatches in a row: two join points, each in its own context -/

/-- `fun b => (if b then 1 else 2) + (if b then 3 else 4)`, written with an extern call:
    both operands are dispatches, so each one ends a block and jumps to the join point
    that holds the rest. -/
def sumOfIfs : Term doubleSig [] (boolT ⇒ natT) :=
  .lam (.externCall
    (.cons (.bool_casesOn' (.var (v♯0)) (.nat_mk 1) (.nat_mk 2))
      (.cons (.bool_casesOn' (.var (v♯0)) (.nat_mk 3) (.nat_mk 4)) .nil))
    fun vs => .lean_nat_add vs.1 vs.2.1)

example : Term.run doubleEnv sumOfIfs true = 4 := by kernel_rfl
example : Term.run doubleEnv sumOfIfs false = 6 := by kernel_rfl

end TermTests.Anf

end
