module

public import LeanScript.Eval
public import LeanScript.TyNotation
public meta import LeanScript.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# Delays: `Thunk τ` and `Unit → τ`

A Lean `Thunk τ` is read as `Ty.thunk τ` and a Lean `Unit → τ` as `Ty.lazy τ`.  Delays never
nest: the contents of a delay are a `Ty ks false`, which has no `thunk` / `lazy` constructor,
so several delays around a type are read as one, a `thunk` absorbing a `lazy`.  A delay denotes
the value it holds (`Ty.den`), and its term formers evaluate as the identity.
-/

namespace DelayTest

open LeanScript

/-! ## Reading Lean types -/

-- `Unit → X` is `.lazy X`
example : (#leanscript_get_ty (Unit → Nat) : Ty []) = .lazy (.prim .nat) := rfl
-- `Unit → Unit → X` is `.lazy X`
example : (#leanscript_get_ty (Unit → Unit → Nat) : Ty []) = .lazy (.prim .nat) := rfl
-- `Unit → Thunk X` is `.thunk X`
example : (#leanscript_get_ty (Unit → Thunk Nat) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk X` is `.thunk X`
example : (#leanscript_get_ty (Thunk Nat) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk (Unit → X)` is `.thunk X`
example : (#leanscript_get_ty (Thunk (Unit → Nat)) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk (Unit → Array X)` is `.thunk (.array X)`
example : (#leanscript_get_ty (Thunk (Unit → Array Nat)) : Ty []) = .thunk (.array .nat) := rfl
-- `Thunk (Unit → Unit → Array X)` is `.thunk (.array X)`
example : (#leanscript_get_ty (Thunk (Unit → Unit → Array Nat)) : Ty []) =
    .thunk (.array .nat) := rfl
-- `Unit → Unit → Thunk (Unit → Unit → Array X)` is `.thunk (.array X)`
example : (#leanscript_get_ty (Unit → Unit → Thunk (Unit → Unit → Array Nat)) : Ty []) =
    .thunk (.array .nat) := rfl
-- `Thunk (Thunk X)` is `.thunk X`
example : (#leanscript_get_ty (Thunk (Thunk Nat)) : Ty []) = .thunk (.prim .nat) := rfl
-- a delay inside another type former is kept where it is
example : (#leanscript_get_ty (Array (Unit → Nat) → Thunk Bool) : Ty []) =
    .fn (.array (.lazy (.prim .nat))) (.thunk (.prim .bool)) := rfl
-- `Unit` alone has one value: it is not a type
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
example : Ty [] := #leanscript_get_ty Unit

/-! ## The same rules as functions on `Ty` (`Ty.mkLazy`, `Ty.mkThunk`) -/

example (X : Ty []) :
    Ty.mkLazy (Ty.mkLazy (Ty.mkThunk (Ty.mkLazy (Ty.mkLazy (.array X))))) = .thunk (.array X) :=
  rfl
example (X : Ty []) : Ty.mkThunk (Ty.mkLazy (Ty.mkLazy (.array X))) = .thunk (.array X) := rfl
example (t : Ty []) : Ty.mkLazy (Ty.mkLazy t) = Ty.mkLazy t := Ty.mkLazy_mkLazy t

/-! ## Delays never nest -/

example (t u : Ty [] false) : t.relax ≠ .lazy u := Ty.lazy_not_in_lazy t u
example (t u : Ty [] false) : t.relax ≠ .thunk u := Ty.thunk_not_in_lazy t u
example (t u : Ty [] false) : t.relax ≠ .lazy u := Ty.lazy_not_in_thunk t u
-- `Ty.lazy (Ty.lazy _)` does not typecheck: the contents of a delay are a `Ty ks false`
/--
error: Application type mismatch: The argument
  [Ty| Unit → Nat]
has type
  Ty ?m.4
but is expected to have type
  Ty [] false
in the application
  [Ty| Unit → Unit → Nat]
-/
#guard_msgs in
example : Ty [] := .lazy (.lazy (.prim .nat))

/-! ## The notation -/

example : ([Ty| Unit → Nat] : Ty []) = .lazy (.prim .nat) := rfl
example : ([Ty| Unit → Unit → Thunk (Unit → Array Nat)] : Ty []) = .thunk (.array .nat) := rfl
example : ([Ty| Thunk (Option Nat)] : Ty []) = .thunk (.union (.two .nullary (.fields (.one .nat)))) :=
  rfl

/-- info: [Ty| Unit → Nat] : Ty [] -/
#guard_msgs in
#check (Ty.lazy (.prim .nat) : Ty [])

/-- info: [Ty| Thunk (Array Nat)] : Ty [] -/
#guard_msgs in
#check (Ty.thunk (.array .nat) : Ty [])

/-- info: [Ty| (Unit → Nat) → Thunk Bool] : Ty [] -/
#guard_msgs in
#check (Ty.fn (.lazy (.prim .nat)) (.thunk (.prim .bool)) : Ty [])

/-! ## Meaning and evaluation: a delay is the identity -/

example : Ty.den (fun _ => Empty) (Ty.thunk (.array .nat) : Ty []) = Array Nat := rfl
example : Ty.den (fun _ => Empty) (Ty.lazy (.prim .nat) : Ty []) = Nat := rfl

/-- `fun x => (lazy_mk x)` forced: the identity on `Nat`.  In A-normal form the delay is
    named by a `let` before it is forced. -/
def forceLazy {ks : List Nat} {Δ : DSig ks} : Comp Δ [] (.fn .nat .nat) :=
  .lam (.letE (.lazy_mk (.ret (.var .head)))
    (.ofComp (.lazy_force (τ := .prim .nat) (.var .head))))

/-- A thunk of an array, built from the array. -/
def thunkArr {ks : List Nat} {Δ : DSig ks} : Comp Δ [] (.thunk (.array .nat)) :=
  .thunk_mk (.ret (.array_mk (.cons (.lit .nat 1) (.cons (.lit .nat 2) .nil))))

example : (forceLazy (Δ := .nil)).run (5 : Nat) = (5 : Nat) := rfl
example : (thunkArr (Δ := .nil)).run = (#[1, 2] : Array Nat) := rfl
example : (Term.letE thunkArr (.ofComp (.thunk_force (.var .head))) :
    Term (DSig.nil) [] (.array .nat) []).run = (#[1, 2] : Array Nat) := rfl

end DelayTest
