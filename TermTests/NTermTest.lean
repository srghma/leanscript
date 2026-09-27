module

public import LeanScript.NTerm.Closed
public import LeanScript.NTerm.Dce

@[expose] public section

set_option autoImplicit false

/-!
# Normal-form terms with known and unknown contexts (`LeanScript.NTerm`)

Hand-written normal forms of the examples of `proposals/NormalFormProposals.md` §B.5, their
values (by `rfl`), what the types reject, and dead-code elimination.
-/

namespace NTermTest

open LeanScript LeanScript.NTerm

/-- Statements over the empty signature. -/
abbrev T (Φ : KCtx []) (Γ : UCtx []) (τ : Ty []) : Type := Term DSig.nil Φ Γ τ []

/-- The innermost unknown, used. -/
abbrev x0 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage} (h : u ≠ .zero := by decide) :
    PExpr DSig.nil Φ (⟨τ, u⟩ :: Γ) τ true :=
  .neu (.var (.head h))

/-- The unknown one binder further out. -/
abbrev x1 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage} {b : UBinder []}
    (h : u ≠ .zero := by decide) : PExpr DSig.nil Φ (b :: ⟨τ, u⟩ :: Γ) τ true :=
  .neu (.var (.tail (.head h)))

/-! ## 1. A shared extern call: `fun n => let a := n * 7; a + a` -/

/-- `fun n => let a := share (n * 7); a + a`: the call is computed once (`a` is used ω times),
    the closure is a closed known value, and the program is `val %f := …; %f`. -/
def mulTwice : T [] [] (.fn .nat .nat) :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letE .many (.share (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil))))
        (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil))))))))
    (.ret (.kvar (.head (by decide))))

example : mulTwice.run (3 : Nat) = (42 : Nat) := rfl

/-- A whole program is a value: here, a known closure and its name. -/
example : mulTwice.IsValue := mulTwice.run_isValue

/-! ## 2. A closure shared by name and passed twice to an unknown function -/

/-- `fun g n => val %f := fun x => x + n; g %f + g %f`: `%f` is an *open* known value (it
    mentions the unknown `n`), passed twice by name to the unknown `g`, never copied. -/
def shareTwice : T [] [] (.fn (.fn (.fn .nat .nat) .nat) (.fn .nat .nat)) :=
  .letV .one
    (.lam (u := .many) (.closed
      (.letV .one
        (.lam (u := .many) (.opened
          (.letV .one
            (.lam (u := .one) (.opened
              (.ret (.neu (.extern .lean_nat_add
                (.cons (x0 (τ := .nat)) (.cons (x1 (τ := .nat)) .nil)))))))
            (.letE .one (.app (x1 (τ := .fn (.fn .nat .nat) .nat)) (.kvar (.head (by decide))) rfl)
              (.letE .one (.app (.neu (.var (.tail (.tail (.head (by decide))))))
                  (.kvar (.head (by decide))) rfl)
                (.ret (.neu (.extern .lean_nat_add
                  (.cons (x1 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil))))))))))
        (.ret (.kvar (.head (by decide)))))))
    (.ret (.kvar (.head (by decide))))

example : shareTwice.run (fun f => f (1 : Nat)) (10 : Nat) = (22 : Nat) := rfl

/-! ## 3. A known closure called on an unknown: the call is kept, not inlined -/

/-- `fun n => val %sq := fun x => x * x; %sq n`: `%sq` is closed, but the argument is open, so
    the call is not a closed redex; the closure stays shared. -/
def callOpen : T [] [] (.fn .nat .nat) :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letV .one
        (.lam (u := .many) (.closed
          (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil)))))))
        (.letE .one (.app (.kvar (.head (by decide))) (x0 (τ := .nat)) rfl)
          (.ret (x0 (τ := .nat)))))))
    (.ret (.kvar (.head (by decide))))

example : callOpen.run (9 : Nat) = (81 : Nat) := rfl

/-! ## 4. What the types reject -/

/-- `3 + 4` cannot be written when nothing is unknown: an extern needs an open argument. -/
example (args : Args DSig.nil [] [] [.nat, .nat] true) : False :=
  Bool.noConfusion (Args.closed KCtx.Closed.nil args)

/-- A closed known closure cannot be called on a closed argument (the normaliser β-reduces
    it): `%f 3` has no open operand. -/
example (_f : PExpr DSig.nil [⟨.fn .nat .nat, .one, false⟩] [] (.fn .nat .nat) false) :
    (false || false) ≠ true := by decide

/-- A known record is never taken apart: `record_casesOn` needs a neutral scrutinee, and there
    is no neutral expression without an unknown. -/
example (n : Neu DSig.nil [⟨.pair .nat .nat, .one, false⟩] [] (.pair .nat .nat)) : False :=
  Neu.not_closed (KCtx.Closed.cons KCtx.Closed.nil) n

/-- There is no computation at all in a program without unknowns. -/
example {τ : Ty []} (c : Comp DSig.nil [] [] τ) : False := Comp.not_closed KCtx.Closed.nil c

/-- A binder annotated `0` cannot be referenced. -/
example {Γ : UCtx []} {τ : Ty []} (x : UVar (⟨τ, .zero⟩ :: Γ) τ) : x.index ≠ 0 := by
  cases x with
  | head h => exact absurd rfl h
  | tail _ => simp [UVar.index]

/-! ## 5. Dead-code elimination and usage annotation -/

/-- `fun n => let a := share (n * 7); val %p := ⟨n, n⟩; n + 1`, everything annotated ω:
    `a` and `%p` are dead. -/
def deadLets : T [] [] (.fn .nat .nat) :=
  .letV .one
    (.lam (u := .many) (.closed
      (.letE .many (.share (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil))))
        (.letV .many (.record_mk (fs := .one .nat) (.cons (x1 (τ := .nat)) (.cons (x1 (τ := .nat)) .nil)))
          (.ret (.neu (.extern .lean_nat_add (.cons (x1 (τ := .nat)) (.cons (.lit .nat 1) .nil)))))))))
    (.ret (.kvar (.head (by decide))))

/-- After `dce`: `fun n => n + 1`, the parameter used once. -/
def deadLetsDce : T [] [] (.fn .nat .nat) :=
  .letV .one
    (.lam (u := .one) (.closed
      (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (.lit .nat 1) .nil)))))))
    (.ret (.kvar (.head (by decide))))

example : deadLets.dce = deadLetsDce := by rfl

example : deadLets.dce.run (4 : Nat) = (5 : Nat) := by rw [deadLets.dce_run]; rfl

/-- The usage of the parameter of `mulTwice`'s closure is recounted to `one`; the shared call
    stays `ω`. -/
example : mulTwice.dce = mulTwice := by rfl

end NTermTest

end
