module

public import LeanScript.WFTerm.Optimize
public import LeanScript.Term.ExternShorthands

@[expose] public section

set_option autoImplicit false

/-!
# `WFTerm`: well-founded recursion around `Term`

Hand-written programs of `LeanScript.WFTerm`: a global function by well-founded recursion
(`gcd`, along the second argument), nested recursion along a lexicographic order (Ackermann's
function), a recursive join point (a loop in the main statement, whose postcondition is carried
to the answer), a `map` whose body calls a global function, and the rewrites of the optimiser
(checked by `rfl`).  Every decrease proof is a `Prop` carried by the syntax.  The programs are
run, compiled, by `Tests/Main.lean` (`wfTermSpec`).
-/

namespace WFTermTest

open LeanScript

abbrev D : DSig [] := DSig.nil

/-- A value of type `nat` as a `Nat`. -/
abbrev natOf (x : Ty.Den D .nat) : Nat := x

/-- The innermost variable. -/
abbrev x0 {τ : Ty []} {Γ : WCtx []} : PExpr D [] (WCtx.toU (τ :: Γ)) τ (some 0) :=
  .neu (.var (.head (by decide)))

/-- A numeral. -/
abbrev lit {Γ : WCtx []} (n : Nat) : PExpr D [] (WCtx.toU Γ) .nat none := .lit .nat n

/-- The variable one binder further out. -/
abbrev x1 {τ σ : Ty []} {Γ : WCtx []} : PExpr D [] (WCtx.toU (σ :: τ :: Γ)) τ (some 0) :=
  .neu (.var (.tail (.head (by decide))))

/-! ## A global function by well-founded recursion: `gcd` -/

/-- `gcd a b` (parameters `a` = index 0, `b` = index 1). -/
def gcdFn : WFFn D where
  params := [.nat, .nat]
  ret := .nat
  pre _ := True
  post _ _ := True

/-- The second parameter decreases. -/
def gcdR (x y : WEnv D gcdFn.params) : Prop := Nat.lt x.2.1 y.2.1

theorem gcdR_wf : WellFounded gcdR :=
  InvImage.wf (β := Nat) (fun x : WEnv D gcdFn.params => x.2.1) Nat.lt_wfRel.wf

def gcdBody : WFTerm D [] gcdFn.params gcdFn.pre (some (WFSelf.top gcdFn gcdR)) gcdFn.ret
    gcdFn.post .nil :=
  .ite (.pure (PExpr.lean_nat_dec_eq__Nat_beq x1 (.lit .nat 0)))
    (.ret (.pure x0) (fun _ _ => trivial))
    (.letE (.self (.cons (.pure x1) (.cons (.pure (PExpr.lean_nat_mod__Nat_mod x0 x1)) .nil))
        (fun e h => by
          obtain ⟨a, b, ⟨⟩⟩ := e
          change Nat at a b
          have hb : b ≠ 0 := by
            intro hb; subst hb; exact Bool.noConfusion h.2
          exact Nat.mod_lt a (Nat.pos_of_ne_zero hb))
        (fun _ _ => trivial))
      (.ret (.pure x0) (fun _ _ => trivial)))

/-- The global functions: `gcd`. -/
def gcdGlobals : WFGlobals D [gcdFn] := .cons .nil gcdFn gcdR gcdR_wf gcdBody

/-- `gcd a b`, as a program. -/
def gcdProg (a b : Nat) : WFProgram D .nat (fun _ => True) where
  GL := [gcdFn]
  globals := gcdGlobals
  main := .letE (.call .here (.cons (.pure (.lit .nat a)) (.cons (.pure (.lit .nat b)) .nil))
      (fun _ _ => trivial))
    (.ret (.pure x0) (fun _ _ => trivial))



/-! ## Nested recursion along a lexicographic order: Ackermann's function -/

/-- `ack m n` (parameters `m` = index 0, `n` = index 1). -/
def ackFn : WFFn D where
  params := [.nat, .nat]
  ret := .nat
  pre _ := True
  post _ _ := True

/-- `(m, n)` decreases lexicographically. -/
def ackR (x y : WEnv D ackFn.params) : Prop :=
  (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).rel (x.1, x.2.1) (y.1, y.2.1)

theorem ackR_wf : WellFounded ackR :=
  InvImage.wf (β := Nat × Nat) (fun x : WEnv D ackFn.params => (x.1, x.2.1))
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

/-- `ack m n = if m == 0 then n + 1 else if n == 0 then ack (m - 1) 1
    else let r := ack m (n - 1); ack (m - 1) r`. -/
def ackBody : WFTerm D [] ackFn.params ackFn.pre (some (WFSelf.top ackFn ackR)) ackFn.ret
    ackFn.post .nil :=
  .ite (.pure (PExpr.lean_nat_dec_eq__Nat_beq x0 (lit 0)))
    (.ret (.pure (PExpr.lean_nat_add x1 (lit 1))) (fun _ _ => trivial))
    (.ite (.pure (PExpr.lean_nat_dec_eq__Nat_beq x1 (lit 0)))
      (.letE (.self (.cons (.pure (PExpr.lean_nat_sub x0 (lit 1))) (.cons (.pure (lit 1)) .nil))
          (fun e h => by
            obtain ⟨m, n, ⟨⟩⟩ := e
            change Nat at m n
            have hm : m ≠ 0 := by intro hm; subst hm; exact Bool.noConfusion h.1.2
            exact Prod.Lex.left _ _ (Nat.sub_lt (Nat.pos_of_ne_zero hm) Nat.one_pos))
          (fun _ _ => trivial))
        (.ret (.pure x0) (fun _ _ => trivial)))
      (.letE (.self (.cons (.pure x0) (.cons (.pure (PExpr.lean_nat_sub x1 (lit 1))) .nil))
          (fun e h => by
            obtain ⟨m, n, ⟨⟩⟩ := e
            change Nat at m n
            have hn : n ≠ 0 := by intro hn; subst hn; exact Bool.noConfusion h.2
            exact Prod.Lex.right _ (Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos))
          (fun _ _ => trivial))
        (.letE (.self (.cons (.pure (PExpr.lean_nat_sub x1 (lit 1))) (.cons (.pure x0) .nil))
            (fun e h => by
              obtain ⟨r, m, n, ⟨⟩⟩ := e
              change Nat at r m n
              have hm : m ≠ 0 := by intro hm; subst hm; exact Bool.noConfusion h.1.1.2
              exact Prod.Lex.left _ _ (Nat.sub_lt (Nat.pos_of_ne_zero hm) Nat.one_pos))
            (fun _ _ => trivial))
          (.ret (.pure x0) (fun _ _ => trivial)))))

/-- `ack m n`, as a program. -/
def ackProg (m n : Nat) : WFProgram D .nat (fun _ => True) where
  GL := [ackFn]
  globals := .cons .nil ackFn ackR ackR_wf ackBody
  main := .letE (.call .here (.cons (.pure (lit m)) (.cons (.pure (lit n)) .nil))
      (fun _ _ => trivial))
    (.ret (.pure x0) (fun _ _ => trivial))

/-! ## A recursive join point: a loop in the main statement -/

/-- `joinrec j (i : nat) [<] := if i == 0 then ret 7 else jump j (i - 1) in jump j n`: every
back edge proves `i - 1 < i` from the test. -/
def countdown (n : Nat) : WFProgram D .nat (fun v => natOf v = 7) where
  GL := []
  globals := .nil
  main :=
    .joinrec .nat (fun _ _ => True) (fun _ v x => Nat.lt v x) (fun _ => Nat.lt_wfRel.wf)
      (.ite (.pure (PExpr.lean_nat_dec_eq__Nat_beq x0 (lit 0)))
        (.ret (.pure (lit 7)) (fun _ _ => rfl))
        (.jump .here (.pure (PExpr.lean_nat_sub x0 (lit 1)))
          (fun e h => by
            obtain ⟨i, ⟨⟩⟩ := e
            change Nat at i
            have hi : i ≠ 0 := by intro hi; subst hi; exact Bool.noConfusion h.2
            exact ⟨trivial, Nat.sub_lt (Nat.pos_of_ne_zero hi) Nat.one_pos⟩)
          (fun _ _ _ h => h)))
      (.jump .here (.pure (lit n)) (fun _ _ => trivial) (fun _ _ _ h => h))

/-- The postcondition is carried to the answer: the loop always answers `7`. -/
theorem countdown_run (n : Nat) : natOf (countdown n).run.1 = 7 := (countdown n).run.2

/-! ## `map` with calls in its body -/

/-- `List.map (fun x => gcd x 12) [8, 9, 10]`. -/
def gcdMap : WFProgram D (.list .nat) (fun _ => True) where
  GL := [gcdFn]
  globals := gcdGlobals
  main :=
    .letE (.map (.pure (.list_mk (.cons (lit 8) (.cons (lit 9) (.cons (lit 10) .nil)))))
        (.letE (.call .here (.cons (.pure x0) (.cons (.pure (lit 12)) .nil)) (fun _ _ => trivial))
          (.ret (.pure x0) (fun _ _ => trivial))))
      (.ret (.pure x0) (fun _ _ => trivial))

/-! ## The optimiser -/

/-- `join j (v : nat) := ret (v + 1) in if true then jump j 41 else ret 0`. -/
def joinDemo : WFTerm D [] [] (fun _ => True) none .nat (fun _ _ => True) .nil :=
  .join .nat (fun _ _ => True) (.ret (.pure (PExpr.lean_nat_add x0 (lit 1))) (fun _ _ => trivial))
    (.ite (.pure (.lit .bool true))
      (.jump .here (.pure (lit 41)) (fun _ _ => trivial) (fun _ _ _ h => h))
      (.ret (.pure (lit 0)) (fun _ _ => trivial)))

/-- The constant test is resolved, and the join point entered at once is inlined:
`let v := 41 in ret (v + 1)`. -/
def joinDemoOpt : WFTerm D [] [] (fun _ => True) none .nat (fun _ _ => True) .nil :=
  .letE (.share (.pure (lit 41)))
    (.ret (.pure (PExpr.lean_nat_add x0 (lit 1))) (fun _ _ => trivial))

example : joinDemo.optimize = joinDemoOpt := by rfl

/-- `List.map (fun x => gcd x 12) []` is the literal `[]`. -/
def mapNil : WFTerm D [gcdFn] [] (fun _ => True) none (.list .nat) (fun _ _ => True) .nil :=
  .letE (.map (.pure (.list_mk .nil))
      (.letE (.call .here (.cons (.pure x0) (.cons (.pure (lit 12)) .nil)) (fun _ _ => trivial))
        (.ret (.pure x0) (fun _ _ => trivial))))
    (.ret (.pure x0) (fun _ _ => trivial))

example : mapNil.optimize =
    .letE (.share (WFAtom.nil .nat)) (.ret (.pure x0) (fun _ _ => trivial)) := by rfl

/-- The optimised programs compute the same answers, for every input. -/
example (a b : Nat) : (gcdProg a b).optimize.run = (gcdProg a b).run := WFProgram.optimize_run _
example (m n : Nat) : (ackProg m n).optimize.run = (ackProg m n).run := WFProgram.optimize_run _

end WFTermTest
