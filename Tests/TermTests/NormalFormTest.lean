module

public import LeanScript.Term.Closed
public import LeanScript.Term.Dce

@[expose] public section

set_option autoImplicit false

/-!
# Hand-written normal forms

Normal forms written by hand (the examples of `proposals/NormalFormProposals.md` §B.5), their
values (by `rfl`), what the types reject (closed redexes, dead or wrongly open bodies,
references to binders annotated `0`), usage counts across branches, and dead-code elimination.
-/

namespace NormalFormTest

open LeanScript

/-- Statements at depth `d` over the empty signature. -/
abbrev T (d : Nat) (Φ : KCtx []) (Γ : UCtx []) (τ : Ty []) (o : Lvl) : Type :=
  Term DSig.nil d Φ Γ τ [] o

/-- The innermost unknown, used. -/
abbrev x0 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage01ω} {ℓ : Nat}
    (h : u ≠ .zero := by decide) : PExpr DSig.nil Φ (⟨τ, u, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.head h))

/-- The unknown one binder further out. -/
abbrev x1 {Φ : KCtx []} {Γ : UCtx []} {τ : Ty []} {u : Usage01ω} {ℓ : Nat} {b : UBinder []}
    (h : u ≠ .zero := by decide) : PExpr DSig.nil Φ (b :: ⟨τ, u, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.tail (.head h)))

/-! ## 1. A shared extern call: `fun n => let a := n * 7; a + a` -/

/-- `fun n => let a := share (n * 7); a + a`: the call is computed once (`a` is used ω times),
    the closure is a closed known value, and the program is `val %f := …; %f`. -/
def mulTwice : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letE .many (.share (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil)) rfl))
        (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil)) rfl))))))
    (.ret (.kvar .head))

-- [SKIPPED BY PROFILE_LAKE] example : mulTwice.run (3 : Nat) = (42 : Nat) := rfl

/-- A whole program is a value: here, a known closure and its name. -/
example : mulTwice.IsValue := mulTwice.run_isValue

/-! ## 2. A closure shared by name and passed twice to an unknown function -/

/-- `fun g n => val %f := fun x => x + n; g %f + g %f`: `%f` is an *open* known value (it
    mentions the unknown `n`, of level `2`), passed twice by name to the unknown `g`, never
    copied.  The body of `%f` is open (it mentions `n`, bound outside of it); the body of
    `fun n => …` is open too (it mentions `g`). -/
def shareTwice : T 0 [] [] (.fn (.fn (.fn .nat .nat) .nat) (.fn .nat .nat)) none :=
  .letV .one
    (.lam (u := .many) (.closed
      (.letV .one
        (.lam (u := .many) (.opened
          (.letV .one
            (.lam (u := .one) (.opened
              (.ret (.neu (.extern .lean_nat_add
                (.cons (x0 (τ := .nat)) (.cons (x1 (τ := .nat)) .nil)) rfl)))
              (by decide)))
            (.letE .one (.app (x1 (τ := .fn (.fn .nat .nat) .nat)) (.kvar .head) rfl)
              (.letE .one (.app (.neu (.var (.tail (.tail (.head (by decide))))))
                  (.kvar .head) rfl)
                (.ret (.neu (.extern .lean_nat_add
                  (.cons (x1 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil)) rfl))))))
          (by decide)))
        (.ret (.kvar .head)))))
    (.ret (.kvar .head))

-- [SKIPPED BY PROFILE_LAKE] example : shareTwice.run (fun f => f (1 : Nat)) (10 : Nat) = (22 : Nat) := rfl

/-! ## 3. A known closure called on an unknown: the call is kept, not inlined -/

/-- `fun n => val %sq := fun x => x * x; %sq n`: `%sq` is closed, but the argument is open, so
    the call is not a closed redex; the closure stays shared. -/
def callOpen : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letV .one
        (.lam (u := .many) (.closed
          (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (x0 (τ := .nat)) .nil)) rfl)))))
        (.letE .one (.app (.kvar .head) (x0 (τ := .nat)) rfl)
          (.ret (x0 (τ := .nat)))))))
    (.ret (.kvar .head))

-- [SKIPPED BY PROFILE_LAKE] example : callOpen.run (9 : Nat) = (81 : Nat) := rfl

/-! ## 4. What the types reject -/

/-- `3 + 4` cannot be written when nothing is unknown: an extern needs an open argument. -/
example {ℓ : Nat} (args : Args DSig.nil [] [] [.nat, .nat] (some ℓ)) : False :=
  nomatch Args.closed KCtx.Closed.nil args

/-- A closed known closure cannot be called on a closed argument (the normaliser β-reduces
    it): `%f 3` has no open operand. -/
example (ℓ : Nat) : Lvl.meet none none ≠ some ℓ := nofun

/-- A known record is never taken apart: `record_casesOn` needs a neutral scrutinee, and there
    is no neutral expression without an unknown. -/
example {ℓ : Nat} (n : Neu DSig.nil [⟨.pair .nat .nat, .one, none, true⟩] [] (.pair .nat .nat) ℓ) :
    False :=
  Neu.not_closed (KCtx.Closed.cons KCtx.Closed.nil) n

/-- There is no computation at all in a program without unknowns. -/
example {τ : Ty []} {ℓ : Nat} (c : Comp DSig.nil 0 [] [] τ ℓ) : False :=
  Comp.not_closed KCtx.Closed.nil c

-- [SKIPPED BY PROFILE_LAKE] /-- A pattern binder annotated `0` cannot be referenced. -/
-- [SKIPPED BY PROFILE_LAKE] example {Γ : UCtx []} {τ : Ty []} {ℓ : Nat} (x : UVar (⟨τ, .zero, ℓ⟩ :: Γ) τ ℓ) : x.index ≠ 0 := by
-- [SKIPPED BY PROFILE_LAKE]   cases x with
-- [SKIPPED BY PROFILE_LAKE]   | head h => exact absurd rfl h
-- [SKIPPED BY PROFILE_LAKE]   | tail _ => simp [UVar.index]

/-- **An open body must mention something from outside**: a closure body at depth `0` whose
    parameter is its only unknown has level `1` (or is closed), so it cannot be marked open
    (`Body.opened` needs a level `≤ 0`). -/
example (t : Term DSig.nil 1 [] ([⟨.nat, .one, 1⟩] ++ []) .nat [] (some 0)) : False :=
  absurd (Term.level_ge (Nat.le_refl 1) (KCtx.Closed.nil.ge 1)
    (UCtx.Ge.params1 0 .nat .one) t) (Nat.not_succ_le_zero 0)

/-- Every body at depth `0` of a program is closed: nothing is bound outside of it. -/
example {σ τ : Ty []} {u : Usage01ω} {o : Lvl} (b : Body DSig.nil 0 [] [] [⟨σ, u, 1⟩] τ o) :
    o = none :=
  b.closed_eq KCtx.Closed.nil (UCtx.Ge.params1 0 σ u)

/-! ## 5. Usage counts: the arms of a branch take the maximum -/

/-- `fun b n => if b then n + 1 else n * 2`: `n` is used once in each arm, so once. -/
def armsOnce : T 0 [] [] (.fn .bool (.fn .nat .nat)) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.letV .one
        (.lam (u := .one) (.opened
          (.branch (.ite (.var (.tail (.head (by decide))))
            (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (.lit .nat 1) .nil)) rfl)))
            (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 2) .nil)) rfl)))))
          (by decide)))
        (.ret (.kvar .head)))))
    (.ret (.kvar .head))

-- [SKIPPED BY PROFILE_LAKE] example : armsOnce.run true (4 : Nat) = (5 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : armsOnce.run false (4 : Nat) = (8 : Nat) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The parameter `n` of the inner closure: once in each arm is once. -/
-- [SKIPPED BY PROFILE_LAKE] example : (Term.countU (Δ := DSig.nil) (d := 2) (Φ := [⟨.fn .nat .nat, .one, some 1, true⟩, ⟨.fn .bool (.fn .nat .nat), .one, none, true⟩])
-- [SKIPPED BY PROFILE_LAKE]     (Γ := [⟨.nat, .one, 2⟩, ⟨.bool, .one, 1⟩]) (τ := .nat) (js := [])
-- [SKIPPED BY PROFILE_LAKE]     0 (.branch (.ite (.var (.tail (.head (by decide))))
-- [SKIPPED BY PROFILE_LAKE]       (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (.lit .nat 1) .nil)) rfl)))
-- [SKIPPED BY PROFILE_LAKE]       (.ret (.neu (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 2) .nil)) rfl)))))) =
-- [SKIPPED BY PROFILE_LAKE]     .one := rfl

/-! ## 6. Dead-code elimination and usage annotation -/

/-- `fun n => let a := share (n * 7); val %p := ⟨n, n⟩; n + 1`, everything annotated ω:
    `a` and `%p` are dead. -/
def deadLets : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .many) (.closed
      (.letE .many (.share (.extern .lean_nat_mul (.cons (x0 (τ := .nat)) (.cons (.lit .nat 7) .nil)) rfl))
        (.letV .many (.record_mk (fs := .one .nat) (.cons (x1 (τ := .nat)) (.cons (x1 (τ := .nat)) .nil)))
          (.ret (.neu (.extern .lean_nat_add (.cons (x1 (τ := .nat)) (.cons (.lit .nat 1) .nil)) rfl)))))))
    (.ret (.kvar .head))

/-- After `dce`: `fun n => n + 1`, the parameter used once. -/
def deadLetsDce : T 0 [] [] (.fn .nat .nat) none :=
  .letV .one
    (.lam (u := .one) (.closed
      (.ret (.neu (.extern .lean_nat_add (.cons (x0 (τ := .nat)) (.cons (.lit .nat 1) .nil)) rfl)))))
    (.ret (.kvar .head))

-- [SKIPPED BY PROFILE_LAKE] example : deadLets.dce = deadLetsDce := by rfl

-- [SKIPPED BY PROFILE_LAKE] example : deadLets.dce.run (4 : Nat) = (5 : Nat) := by rw [deadLets.dce_run]; rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The usage of the parameter of `mulTwice`'s closure is recounted to `one`; the shared call
-- [SKIPPED BY PROFILE_LAKE]     stays `ω`. -/
-- [SKIPPED BY PROFILE_LAKE] example : mulTwice.dce = mulTwice := by rfl

end NormalFormTest

end
