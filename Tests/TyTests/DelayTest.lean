module

public import LeanScript.Term.Build
public import LeanScript.TyElab.Notation
public meta import LeanScript.GenElab.GetCtor

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
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Unit → Nat) : Ty []) = .lazy (.prim .nat) := rfl
-- `Unit → Unit → X` is `.lazy X`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Unit → Unit → Nat) : Ty []) = .lazy (.prim .nat) := rfl
-- `Unit → Thunk X` is `.thunk X`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Unit → Thunk Nat) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk X` is `.thunk X`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Thunk Nat) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk (Unit → X)` is `.thunk X`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Thunk (Unit → Nat)) : Ty []) = .thunk (.prim .nat) := rfl
-- `Thunk (Unit → Array X)` is `.thunk (.array X)`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Thunk (Unit → Array Nat)) : Ty []) = .thunk (.array .nat) := rfl
-- `Thunk (Unit → Unit → Array X)` is `.thunk (.array X)`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Thunk (Unit → Unit → Array Nat)) : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .thunk (.array .nat) := rfl
-- `Unit → Unit → Thunk (Unit → Unit → Array X)` is `.thunk (.array X)`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Unit → Unit → Thunk (Unit → Unit → Array Nat)) : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .thunk (.array .nat) := rfl
-- `Thunk (Thunk X)` is `.thunk X`
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Thunk (Thunk Nat)) : Ty []) = .thunk (.prim .nat) := rfl
-- a delay inside another type former is kept where it is
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Array (Unit → Nat) → Thunk Bool) : Ty []) =
-- [SKIPPED BY PROFILE_LAKE]     .fn (.array (.lazy (.prim .nat))) (.thunk (.prim .bool)) := rfl
-- `Unit` alone has one value: it is not a type
/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
example : Ty [] := #leanscript_get_ty Unit

/-! ## The same rules as functions on `Ty` (`Ty.mkLazy`, `Ty.mkThunk`) -/

-- [SKIPPED BY PROFILE_LAKE] example (X : Ty []) :
-- [SKIPPED BY PROFILE_LAKE]     Ty.mkLazy (Ty.mkLazy (Ty.mkThunk (Ty.mkLazy (Ty.mkLazy (.array X))))) = .thunk (.array X) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl
-- [SKIPPED BY PROFILE_LAKE] example (X : Ty []) : Ty.mkThunk (Ty.mkLazy (Ty.mkLazy (.array X))) = .thunk (.array X) := rfl
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

-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Unit → Nat] : Ty []) = .lazy (.prim .nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Unit → Unit → Thunk (Unit → Array Nat)] : Ty []) = .thunk (.array .nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Ty| Thunk (Option Nat)] : Ty []) = .thunk (.union (.two .nullary (.fields (.one .nat)))) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl

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

-- [SKIPPED BY PROFILE_LAKE] example : Ty.den (fun _ => Empty) (Ty.thunk (.array .nat) : Ty []) = Array Nat := rfl
-- [SKIPPED BY PROFILE_LAKE] example : Ty.den (fun _ => Empty) (Ty.lazy (.prim .nat) : Ty []) = Nat := rfl

/-- `fun x => force (lazy_mk x)`: the identity on `Nat`.  The delay mentions `x`, so it is
    open: it is bound by `letV` and its force is kept as a computation. -/
def forceLazy {ks : List Nat} {Δ : DSig ks} : Term Δ 0 [] [] (.fn .nat .nat) [] none :=
  .letV .one
    (.lam (u := .many) (.closed
      (.letV .one (.lazy_mk (τ := .prim .nat) (.opened (.ret (.neu (.var (.head (by decide))))) (by decide)))
        (.letE .one (.lazy_force (.kvar .head)) (.ret (.neu (.var (.head (by decide)))))))))
    (.ret (.kvar .head))

/-- A thunk of an array, built from the array: a closed value. -/
def thunkArr {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} :
    Val Δ 0 Φ Γ (.thunk (.array .nat)) none :=
  .thunk_mk (.closed (Γ := Γ) (.ret (.array_mk (.cons (.lit .nat 1) (.cons (.lit .nat 2) .nil)))))

-- [SKIPPED BY PROFILE_LAKE] example : (forceLazy (Δ := .nil)).run (5 : Nat) = (5 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (Term.letV .one thunkArr (.ret (.kvar .head)) :
-- [SKIPPED BY PROFILE_LAKE]     Term DSig.nil 0 [] [] (.thunk (.array .nat)) [] none).run = (#[1, 2] : Array Nat) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The force of a closed delay cannot be written: its body is already a value. -/
-- [SKIPPED BY PROFILE_LAKE] example : True := by
-- [SKIPPED BY PROFILE_LAKE]   fail_if_success
-- [SKIPPED BY PROFILE_LAKE]     have : Term DSig.nil 0 [] [] (.array .nat) [] (some 0) :=
-- [SKIPPED BY PROFILE_LAKE]       .letV .one thunkArr (.letE .one (.thunk_force (.kvar .head)) (.ret (.neu (.var (.head (by decide))))))
-- [SKIPPED BY PROFILE_LAKE]   trivial

end DelayTest
