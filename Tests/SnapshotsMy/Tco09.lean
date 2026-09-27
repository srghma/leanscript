-- The front end runs *in this file*: the command at the bottom,
-- `#leanjs_generate_program_from_all_public_defs_in_current_file`, translates every
-- public definition below into a term of the one grammar of `LeanScript.Expr` and adds the
-- resulting program — a `GlobalDecl`, a `Sig` and a `Term` per declaration, and the
-- `Program` telescope — to this very module, in the namespace `ProgramSnapshotsMyTco09`.
-- There is no `.olean` to read and no second file to keep in step.
import LeanScript.GenerateProgram

-- Four well-founded recursions whose measures are *not* one argument going down.
--
-- * `diagonal`   — lexicographic `(m + n, m)`: the first component is a sum of two
--                  arguments, so no single parameter decreases.
-- * `hyper`      — lexicographic `(n, b)` with a *nested* recursive call in the second
--                  argument of the outer call.
-- * `ackRev`     — Ackermann with the arguments swapped, so the lexicographic order
--                  `(m, n)` mentions the *second* parameter first.
-- * `Mc91`       — McCarthy's 91 function: the measure `101 - n` is a subtraction that
--                  goes *up* in the argument, and the recursion is nested through a
--                  subtype carrying the proof that makes the measure decrease.
--
-- `Mc91` is written with `where`, so the recursion actually lives in the auxiliary
-- declaration `Mc91.M`, whose result type is a `Subtype`.
--
-- Note: the original request wrote `import Mathlib` at the top of this file.  This
-- package does not depend on Mathlib, and none of the four definitions needs it:
-- `omega`, `calc`, `Subtype` and `termination_by`/`decreasing_by` are all core Lean.
-- The file is therefore kept import-free so that it builds in this tree.

def diagonal : Nat → Nat → Nat
  | 0,     0     => 0
  | 0,     n + 1 => diagonal n 0 + 1
  | m + 1, n     => diagonal m (n + 1) + 1
termination_by m n => (m + n, m)
decreasing_by all_goals omega

def hyper : Nat → Nat → Nat → Nat
  | 0,     _, b     => b + 1
  | 1,     a, 0     => a
  | 2,     _, 0     => 0
  | _ + 3, _, 0     => 1
  | n + 1, a, b + 1 => hyper n a (hyper (n + 1) a b)
termination_by n _ b => (n, b)
decreasing_by all_goals omega

def ackRev : Nat → Nat → Nat
  | n,     0     => n + 1
  | 0,     m + 1 => ackRev 1 m
  | n + 1, m + 1 => ackRev (ackRev n (m + 1)) m
termination_by n m => (m, n)
decreasing_by all_goals omega

def Mc91 (n : Nat) : Nat :=
  (M n).val
where
  M (n : Nat) : { m : Nat // m ≥ n - 10 } :=
    if h : n > 100 then
      ⟨n - 10, by omega⟩
    else
      have : n + 11 - 10 ≤ M (n + 11) := (M (n + 11)).property
      have lem : n - 10 ≤ M (M (n + 11)) := calc
        _ ≤ (n + 11) - 10 - 10 := by omega
        _ ≤ (M (n + 11)) - 10 := by omega
        _ ≤ M (M (n + 11)) := (M (M (n + 11)).val).property

      ⟨M (M (n + 11)), lem⟩
  termination_by 101 - n

-- ── the module as a Program of the one grammar ──────────────────────────
-- Every recursion below becomes the one recursion node of the grammar, `Term.fixAcc`,
-- carrying an order, a subject, accessibility evidence for that subject, an invariant and
-- a body.  It is written `Term.fixStruct` when the subject is one named argument in the
-- order the language fixes, and `Term.fixNatWith` when it is the subject Lean's
-- `termination_by` names.  Where the self calls stand is not a choice of node: it is
-- reported afterwards by `Term.schemeOf` as `tail` (a `while` loop, no frame) or `deep`
-- (native recursion).  No node carries a measure the front end had to invent, and none
-- carries a descent proof, so nothing generated here is a `sorry`.
#leanjs_generate_program_from_all_public_defs_in_current_file

-- ── the generated program, run against the functions it was translated from ─────
-- `Term` takes no fuel and the recursion node carries no invented measure, so running one of
-- the terms above is an ordinary total Lean computation.  What the checks below add is
-- that the translation is *faithful*: on the inputs enumerated, each generated term
-- computes exactly the Lean function of this file it came from — in particular the
-- recursion is never cut short.  The section after them proves the same thing at *every*
-- input, with no enumeration: see `runAckRev_eq`, `runDiagonal_eq`, `runHyper_eq`,
-- `runMc91_eq` and `runMc91_eq_91` below.

namespace SnapshotsMy.Tco09Check

open LeanScript LeanScript.Expr ProgramSnapshotsMyTco09

/-- The declarations `diagonal` is written against, as a program. -/
def pDiagonal : Program sig_diagonal.decls := .cons d_ackRev (by decide) tm_ackRev .nil

/-- The declarations `hyper` is written against, as a program. -/
def pHyper : Program sig_hyper.decls :=
  .cons d_diagonal (by decide) tm_diagonal pDiagonal

/-- The declarations `Mc91.M` is written against, as a program. -/
def pMc91M : Program sig_Mc91_M.decls := .cons d_hyper (by decide) tm_hyper pHyper

/-- The declarations `Mc91` is written against, as a program. -/
def pMc91 : Program sig_Mc91.decls := .cons d_Mc91_M (by decide) tm_Mc91_M pMc91M

/-- `ackRev`, as the generated term computes it. -/
def runAckRev (n m : Nat) : Nat := Term.run tm_ackRev n m

/-- `diagonal`, as the generated term computes it. -/
def runDiagonal (m n : Nat) : Nat := Program.run pDiagonal tm_diagonal m n

/-- `hyper`, as the generated term computes it. -/
def runHyper (n a b : Nat) : Nat := Program.run pHyper tm_hyper n a b

/-- `Mc91`, as the generated term computes it. -/
def runMc91 (n : Nat) : Nat := Program.run pMc91 tm_Mc91 n

/-- The generated term and the Lean function agree on a square of inputs. -/
def agrees2 (bound : Nat) (f g : Nat → Nat → Nat) : Bool :=
  (List.range bound).all fun i => (List.range bound).all fun j => f i j == g i j

theorem ackRev_agrees : agrees2 4 runAckRev ackRev = true := by native_decide

theorem diagonal_agrees : agrees2 8 runDiagonal diagonal = true := by native_decide

theorem hyper_agrees :
    ((List.range 4).all fun n => (List.range 3).all fun a => (List.range 3).all fun b =>
      runHyper n a b == hyper n a b) = true := by native_decide

theorem Mc91_agrees :
    ((List.range 130).all fun n => runMc91 n == Mc91 n) = true := by native_decide

/-- McCarthy's 91 function is 91 below 101, which the generated term reproduces.  The
    same, at every `n ≤ 100` rather than at the enumerated ones, is `runMc91_eq_91`. -/
theorem Mc91_is_91 : ((List.range 101).all fun n => runMc91 n == 91) = true := by
  native_decide

end SnapshotsMy.Tco09Check

/-!
# The generated program is the source module — on **every** input

The checks above run the generated terms against the functions they were translated from
on an enumerated square of inputs.  This section proves the same thing *without* the
enumeration: for each of the four declarations of this module,

> the term `#leanjs_generate_program_from_all_public_defs_in_current_file` produced
> computes the Lean function of this file, at **every** argument.

That is `runAckRev_eq`, `runDiagonal_eq`, `runHyper_eq` and `runMc91_eq`, and it is the
statement the recursion node is shaped for: it answers with `Ty.dflt` at a
self call that does not descend in its subject, so "the run is never cut short" is a
theorem about the *subject* the front end transcribed, and each proof below discharges it
— `Term.fixNatWith_implements` for a recursion whose descent is unconditional, and
`Term.fixNatWith_implements_on` for the inner recursion of a lexicographic pair, whose
descent holds only on the domain the enclosing recursion keeps (`ackRev`: the second
argument is fixed; `diagonal`: the sum of the arguments is fixed).  `Mc91.M` is the case
where the descent of the *second* self call is not syntactic at all: it holds because of
the `Subtype` bound the source function carries, and the proof below uses exactly that.

Nothing here is an enumeration, a `decide` or a `native_decide`: each theorem is a
well-founded induction on the subject the generated term descends in.
-/

namespace SnapshotsMy.Tco09Agree

open LeanScript LeanScript.Ty LeanScript.Expr LeanScript.Expr.Ops ProgramSnapshotsMyTco09
open SnapshotsMy.Tco09Check

/-- `Mc91.M`, as a function of an argument environment. -/
def mFun (as : Env [Ty.nat]) : Ty.nat.den := (Mc91.M (as.get .head)).val

/-- The equation of `Mc91.M` above `100`. -/
theorem Mc91M_gt (n : Nat) (h : n > 100) : (Mc91.M n).val = n - 10 := by
  rw [Mc91.M.eq_def]
  simp [h]

/-- The equation of `Mc91.M` at or below `100`. -/
theorem Mc91M_le (n : Nat) (h : ¬ n > 100) :
    (Mc91.M n).val = (Mc91.M (Mc91.M (n + 11)).val).val := by
  have e := Mc91.M.eq_def n
  simp only [h, reduceDIte] at e
  rw [e]

/-- One unrolling of the generated body of `Mc91.M`, against `Mc91.M` itself. -/
theorem mc91M_step (g : Env [Ty.nat] → Ty.nat.den) (n : Nat)
    (hg : ∀ v : Nat, 101 - v < 101 - n → g (.cons v .nil) = (Mc91.M v).val) :
    (if cond (decide (100 < n)) true false then (n - 10 : Nat)
      else g (.cons (g (.cons (n + 11 : Nat) .nil)) .nil)) = (Mc91.M n).val := by
  simp only [cond_true_false_self, decide_eq_true_eq]
  by_cases h : 100 < n
  · rw [ite_eq_left h, Mc91M_gt n (by omega)]
  · have h11 := hg (n + 11) (by omega)
    have hge : (Mc91.M (n + 11)).val ≥ n + 11 - 10 := (Mc91.M (n + 11)).property
    have hv := hg (Mc91.M (n + 11)).val (by omega)
    rw [ite_eq_right h, h11, hv, Mc91M_le n (by omega)]

theorem mc91M_implements (δ : GEnv sig_Mc91_M.decls) : tm_Mc91_M.Implements δ mFun := by
  intro args
  refine Term.fixNatWith_implements (fun as => 101 - as.get .head) (fun _ => True) _
    δ .nil .nil mFun (fun g as hg => ?_) args
  match as with
  | .cons n .nil =>
    show (if cond (decide (100 < (n : Nat))) true false then ((n : Nat) - 10)
          else g (.cons (g (.cons ((n : Nat) + 11) .nil)) .nil)) = mFun (.cons n .nil)
    exact mc91M_step g n (fun v hv => hg (.cons v .nil) hv)

/-! ## `ackRev` -/

/-- A two-argument recursion applied to two terms, on a domain `D`. -/
theorem eval_ap2_fixNatWith {Sg : Sig} {Γ : Ctx} {Ρ : RCtx}
    (subj : Env [Ty.nat, Ty.nat] → Nat) (inv : Env [Ty.nat, Ty.nat] → Prop)
    (body : Term Sg ([Ty.nat, Ty.nat] ++ Γ) (⟨[Ty.nat, Ty.nat], Ty.nat⟩ :: Ρ) Ty.nat)
    (x y : Term Sg Γ Ρ Ty.nat)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (D : Env [Ty.nat, Ty.nat] → Prop) (f : Env [Ty.nat, Ty.nat] → Ty.nat.den)
    (hstep : ∀ (g : Env [Ty.nat, Ty.nat] → Ty.nat.den) (as : Env [Ty.nat, Ty.nat]), D as →
      (∀ bs : Env [Ty.nat, Ty.nat], D bs → subj bs < subj as → g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (hD : D (.cons (x.eval δ γ ρ) (.cons (y.eval δ γ ρ) .nil))) :
    (Term.ap (Term.ap (Term.fixNatWith [Ty.nat, Ty.nat] subj inv body) x) y).eval δ γ ρ
      = f (.cons (x.eval δ γ ρ) (.cons (y.eval δ γ ρ) .nil)) :=
  Term.fixNatWith_implements_on subj inv body δ γ ρ D f hstep _ hD

/-- `ackRev`, as a function of an argument environment. -/
def ackFun (as : Env [Ty.nat, Ty.nat]) : Ty.nat.den :=
  ackRev (as.get .head) (as.get (.tail .head))

theorem ackRev_zero (n : Nat) : ackRev n 0 = n + 1 := by simp [ackRev]

theorem ackRev_zero_succ (m : Nat) : ackRev 0 (m + 1) = ackRev 1 m := by simp [ackRev]

theorem ackRev_succ_succ (n m : Nat) :
    ackRev (n + 1) (m + 1) = ackRev (ackRev n (m + 1)) m := by simp [ackRev]

/-- One unrolling of the generated inner body of `ackRev`. -/
theorem ackRev_step (o i : Env [Ty.nat, Ty.nat] → Ty.nat.den) (m a b : Nat) (hb : b = m)
    (ho : ∀ x y : Nat, y < m → o (.cons x (.cons y .nil)) = ackRev x y)
    (hi : ∀ x y : Nat, y = m → x < a → i (.cons x (.cons y .nil)) = ackRev x y) :
    (if cond (decide (b = 0)) true false then (a + 1)
      else if cond (decide (a = 0)) true false then o (.cons 1 (.cons (b - 1) .nil))
      else o (.cons (i (.cons (a - 1) (.cons ((b - 1) + 1) .nil))) (.cons (b - 1) .nil)))
      = ackRev a b := by
  simp only [cond_true_false_self, decide_eq_true_eq]
  by_cases hb0 : b = 0
  · subst hb0
    simp [ackRev_zero]
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.succ_ne_zero, Nat.add_sub_cancel, reduceIte]
    by_cases ha0 : a = 0
    · subst ha0
      rw [ho 1 b' (by omega), ackRev_zero_succ]
      simp
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      simp only [Nat.succ_ne_zero, reduceIte, Nat.add_sub_cancel]
      rw [hi a' (b' + 1) (by omega) (by omega), ho (ackRev a' (b' + 1)) b' (by omega),
        ackRev_succ_succ]

theorem ackRev_implements (δ : GEnv sig_ackRev.decls) : tm_ackRev.Implements δ ackFun := by
  intro args
  refine Term.fixNatWith_implements (fun as => as.get (.tail .head)) (fun _ => True) _
    δ .nil .nil ackFun (fun o as ho => ?_) args
  match as with
  | .cons n (.cons m .nil) =>
    refine eval_ap2_fixNatWith _ _ _ _ _ δ _ _
      (fun bs => bs.get (.tail .head) = (m : Nat)) ackFun (fun i bs hbs hi => ?_) rfl
    match bs with
    | .cons a (.cons b .nil) =>
      show (if cond (decide ((b : Nat) = 0)) true false then ((a : Nat) + 1)
        else if cond (decide ((a : Nat) = 0)) true false then
          o (.cons 1 (.cons ((b : Nat) - 1) .nil))
        else o (.cons (i (.cons ((a : Nat) - 1) (.cons (((b : Nat) - 1) + 1) .nil)))
          (.cons ((b : Nat) - 1) .nil)))
        = ackFun (.cons a (.cons b .nil))
      exact ackRev_step o i m a b hbs
        (fun x y hy => ho (.cons x (.cons y .nil)) hy)
        (fun x y hy hx => hi (.cons x (.cons y .nil)) hy hx)

/-- **`ackRev`, on every input.** -/
theorem runAckRev_eq (n m : Nat) : runAckRev n m = ackRev n m :=
  Term.apply2_of_implements (ackRev_implements .nil) n m

/-! ## `diagonal` -/

/-- `diagonal`, as a function of an argument environment. -/
def diagFun (as : Env [Ty.nat, Ty.nat]) : Ty.nat.den :=
  diagonal (as.get .head) (as.get (.tail .head))

theorem diagonal_zero_zero : diagonal 0 0 = 0 := by simp [diagonal]

theorem diagonal_zero_succ (n : Nat) : diagonal 0 (n + 1) = diagonal n 0 + 1 := by
  simp [diagonal]

theorem diagonal_succ (m n : Nat) : diagonal (m + 1) n = diagonal m (n + 1) + 1 := by
  simp [diagonal]

/-- One unrolling of the generated inner body of `diagonal`. -/
theorem diagonal_step (o i : Env [Ty.nat, Ty.nat] → Ty.nat.den) (s a b : Nat)
    (hs : a + b = s)
    (ho : ∀ x y : Nat, x + y < s → o (.cons x (.cons y .nil)) = diagonal x y)
    (hi : ∀ x y : Nat, x + y = s → x < a → i (.cons x (.cons y .nil)) = diagonal x y) :
    (if cond (decide (a = 0)) true false then
        (if cond (decide (b = 0)) true false then (0 : Nat)
          else o (.cons (b - 1) (.cons 0 .nil)) + 1)
      else i (.cons (a - 1) (.cons (b + 1) .nil)) + 1)
      = diagonal a b := by
  simp only [cond_true_false_self, decide_eq_true_eq]
  by_cases ha0 : a = 0
  · subst ha0
    simp only [reduceIte]
    by_cases hb0 : b = 0
    · subst hb0
      simp [diagonal_zero_zero]
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.succ_ne_zero, reduceIte, Nat.add_sub_cancel]
      rw [ho b' 0 (by omega), diagonal_zero_succ]
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.succ_ne_zero, reduceIte, Nat.add_sub_cancel]
    rw [hi a' (b + 1) (by omega) (by omega), diagonal_succ]

theorem diagonal_implements (δ : GEnv sig_diagonal.decls) :
    tm_diagonal.Implements δ diagFun := by
  intro args
  refine Term.fixNatWith_implements (fun as => as.get .head + as.get (.tail .head))
    (fun _ => True) _ δ .nil .nil diagFun (fun o as ho => ?_) args
  match as with
  | .cons n (.cons m .nil) =>
    refine eval_ap2_fixNatWith _ _ _ _ _ δ _ _
      (fun bs => bs.get .head + bs.get (.tail .head) = (n : Nat) + (m : Nat)) diagFun
      (fun i bs hbs hi => ?_) rfl
    match bs with
    | .cons a (.cons b .nil) =>
      show (if cond (decide ((a : Nat) = 0)) true false then
          (if cond (decide ((b : Nat) = 0)) true false then (0 : Nat)
            else o (.cons ((b : Nat) - 1) (.cons 0 .nil)) + 1)
        else i (.cons ((a : Nat) - 1) (.cons ((b : Nat) + 1) .nil)) + 1)
        = diagFun (.cons a (.cons b .nil))
      exact diagonal_step o i ((n : Nat) + (m : Nat)) a b hbs
        (fun x y hy => ho (.cons x (.cons y .nil)) hy)
        (fun x y hy hx => hi (.cons x (.cons y .nil)) hy hx)

/-- **`diagonal`, on every input.** -/
theorem runDiagonal_eq (m n : Nat) : runDiagonal m n = diagonal m n :=
  Term.apply2_of_implements (diagonal_implements pDiagonal.env) m n

/-! ## `hyper` -/

/-- A two-argument recursion applied to two values, on a domain `D`. -/
theorem eval_fix2_app {Sg : Sig} {Γ : Ctx} {Ρ : RCtx}
    (subj : Env [Ty.nat, Ty.nat] → Nat) (inv : Env [Ty.nat, Ty.nat] → Prop)
    (body : Term Sg ([Ty.nat, Ty.nat] ++ Γ) (⟨[Ty.nat, Ty.nat], Ty.nat⟩ :: Ρ) Ty.nat)
    (δ : GEnv Sg.decls) (γ : Env Γ) (ρ : REnv Ρ)
    (D : Env [Ty.nat, Ty.nat] → Prop) (f : Env [Ty.nat, Ty.nat] → Ty.nat.den)
    (hstep : ∀ (g : Env [Ty.nat, Ty.nat] → Ty.nat.den) (as : Env [Ty.nat, Ty.nat]), D as →
      (∀ bs : Env [Ty.nat, Ty.nat], D bs → subj bs < subj as → g bs = f bs) →
      body.eval δ (as.append γ) (.cons g ρ) = f as)
    (x y : Nat) (hD : D (.cons x (.cons y .nil))) :
    ((Term.fixNatWith [Ty.nat, Ty.nat] subj inv body).eval δ γ ρ) x y
      = f (.cons x (.cons y .nil)) :=
  Term.fixNatWith_implements_on subj inv body δ γ ρ D f hstep _ hD

/-- `hyper`, as a function of the outer recursion's argument environment. -/
def hyperFun (as : Env [Ty.nat]) : (Ty.nat ⇒ Ty.nat ⇒ Ty.nat).den :=
  fun a b => hyper (as.get .head) a b

theorem hyper_zero (a b : Nat) : hyper 0 a b = b + 1 := by simp [hyper]

theorem hyper_one_zero (a : Nat) : hyper 1 a 0 = a := by simp [hyper]

theorem hyper_two_zero (a : Nat) : hyper 2 a 0 = 0 := by simp [hyper]

theorem hyper_succ3_zero (k a : Nat) : hyper (k + 3) a 0 = 1 := by simp [hyper]

theorem hyper_succ_succ (n a b : Nat) :
    hyper (n + 1) a (b + 1) = hyper n a (hyper (n + 1) a b) := by simp [hyper]

/-- One unrolling of the generated inner body of `hyper`. -/
theorem hyper_step (o : Env [Ty.nat] → (Ty.nat ⇒ Ty.nat ⇒ Ty.nat).den)
    (i : Env [Ty.nat, Ty.nat] → Ty.nat.den) (n a b : Nat)
    (ho : ∀ x y z : Nat, x < n → o (.cons x .nil) y z = hyper x y z)
    (hi : ∀ x y : Nat, y < b → i (.cons x (.cons y .nil)) = hyper n x y) :
    (if cond (decide (n = 0)) true false then b + 1
      else if cond (decide (n - 1 = 0)) true false then
        (if cond (decide (b = 0)) true false then a
          else o (.cons (n - 1) .nil) a (i (.cons a (.cons (b - 1) .nil))))
      else if cond (decide (n - 1 - 1 = 0)) true false then
        (if cond (decide (b = 0)) true false then (0 : Nat)
          else o (.cons (n - 1) .nil) a (i (.cons a (.cons (b - 1) .nil))))
      else (if cond (decide (b = 0)) true false then (1 : Nat)
          else o (.cons (n - 1) .nil) a (i (.cons a (.cons (b - 1) .nil)))))
      = hyper n a b := by
  simp only [cond_true_false_self, decide_eq_true_eq]
  by_cases hn0 : n = 0
  · subst hn0
    simp [hyper_zero]
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hgen : b ≠ 0 →
        o (.cons (n' + 1 - 1) .nil) a (i (.cons a (.cons (b - 1) .nil)))
          = hyper (n' + 1) a b := by
      intro hb0
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, hi a b' (by omega),
        ho n' a (hyper (n' + 1) a b') (by omega), hyper_succ_succ]
    simp only [Nat.succ_ne_zero, reduceIte, Nat.add_sub_cancel]
    by_cases hn1 : n' = 0
    · subst hn1
      simp only [reduceIte]
      by_cases hb0 : b = 0
      · subst hb0
        simp [hyper_one_zero]
      · rw [ite_eq_right hb0]
        simpa using hgen hb0
    · obtain ⟨n'', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
      simp only [Nat.succ_ne_zero, reduceIte, Nat.add_sub_cancel]
      by_cases hn2 : n'' = 0
      · subst hn2
        simp only [reduceIte]
        by_cases hb0 : b = 0
        · subst hb0
          simp [hyper_two_zero]
        · rw [ite_eq_right hb0]
          simpa using hgen hb0
      · obtain ⟨k, rfl⟩ : ∃ k, n'' = k + 1 := ⟨n'' - 1, by omega⟩
        simp only [Nat.succ_ne_zero, reduceIte]
        by_cases hb0 : b = 0
        · subst hb0
          show (1 : Nat) = hyper (k + 3) a 0
          rw [hyper_succ3_zero]
        · rw [ite_eq_right hb0]
          simpa using hgen hb0

theorem hyper_implements (δ : GEnv sig_hyper.decls) : tm_hyper.Implements δ hyperFun := by
  intro args
  refine Term.fixNatWith_implements (fun as => as.get .head) (fun _ => True) _
    δ .nil .nil hyperFun (fun o as ho => ?_) args
  match as with
  | .cons n .nil =>
    funext a b
    refine eval_fix2_app _ _ _ δ _ _ (fun _ => True)
      (fun bs => hyper (n : Nat) (bs.get .head) (bs.get (.tail .head)))
      (fun i bs _ hi => ?_) a b trivial
    match bs with
    | .cons x (.cons y .nil) =>
      show (if cond (decide ((n : Nat) = 0)) true false then (y : Nat) + 1
        else if cond (decide ((n : Nat) - 1 = 0)) true false then
          (if cond (decide ((y : Nat) = 0)) true false then (x : Nat)
            else o (.cons ((n : Nat) - 1) .nil) x (i (.cons x (.cons ((y : Nat) - 1) .nil))))
        else if cond (decide ((n : Nat) - 1 - 1 = 0)) true false then
          (if cond (decide ((y : Nat) = 0)) true false then (0 : Nat)
            else o (.cons ((n : Nat) - 1) .nil) x (i (.cons x (.cons ((y : Nat) - 1) .nil))))
        else (if cond (decide ((y : Nat) = 0)) true false then (1 : Nat)
            else o (.cons ((n : Nat) - 1) .nil) x (i (.cons x (.cons ((y : Nat) - 1) .nil)))))
        = hyper (n : Nat) x y
      exact hyper_step o i n x y
        (fun p q r hp => congrFun (congrFun (ho (.cons p .nil) hp) q) r)
        (fun p q hq => hi (.cons p (.cons q .nil)) trivial hq)

/-- **`hyper`, on every input.** -/
theorem runHyper_eq (n a b : Nat) : runHyper n a b = hyper n a b :=
  congrFun (congrFun (hyper_implements pHyper.env (.cons n .nil)) a) b

/-- **`Mc91`, on every input.** -/
theorem runMc91_eq (n : Nat) : runMc91 n = Mc91 n :=
  mc91M_implements pMc91M.env (.cons n .nil)

/-! ### And what the generated term therefore computes below `101` -/

/-- McCarthy's 91 function is `91` at every `n ≤ 100`, by induction on `101 - n`. -/
theorem Mc91M_eq_91_of_le : ∀ k n : Nat, 101 - n ≤ k → n ≤ 100 → (Mc91.M n).val = 91 := by
  intro k
  induction k with
  | zero => intro n h1 h2; omega
  | succ k ih =>
    intro n h1 h2
    rw [Mc91M_le n (by omega)]
    by_cases hn : 90 ≤ n
    · rw [Mc91M_gt (n + 11) (by omega)]
      by_cases hn100 : n = 100
      · subst hn100
        exact Mc91M_gt 101 (by omega)
      · exact ih (n + 11 - 10) (by omega) (by omega)
    · rw [ih (n + 11) (by omega) (by omega)]
      exact ih 91 (by omega) (by omega)

/-- **The generated term computes `91` at every input below `101`** — not only at the
    inputs an enumeration reaches. -/
theorem runMc91_eq_91 (n : Nat) (h : n ≤ 100) : runMc91 n = 91 := by
  rw [runMc91_eq]
  exact Mc91M_eq_91_of_le (101 - n) n (Nat.le_refl _) h

end SnapshotsMy.Tco09Agree

/-!
# How the generated terms were generated — and which scheme each one landed in

`#leanjs_generate_program_from_all_public_defs_in_current_file` wrote the declarations
`tm_ackRev`, `tm_diagonal`, `tm_hyper`, `tm_Mc91_M` and `tm_Mc91` of
`ProgramSnapshotsMyTco09` above.  This section shows their **bodies**, checked with
`#guard_msgs`, so the text below is not a comment that can drift: if the front end ever
emits something else, this file stops compiling.

Each term is shown twice — once as Lean prints the generated definition (`#print`), and
once in the notation of `LeanScript.ExprPretty`, which is the readable form.

## Where do their self calls stand?

Every recursion node of every term of *this* file is a `Term.fixAcc` — there is only one
recursion node in the grammar — and every one of them is classified **`deep`**.  That is
not a comment either: `Term.schemes` (`LeanScript/SchemeCensus.lean`) lists the verdict for
every recursion node of a term, and the `*_schemes` theorems below are `rfl`.  Note that
`tm_Mc91` contains **no** recursion node at all: `Mc91` is not recursive, it calls the
`where`-auxiliary `Mc91.M`, and the recursion is `tm_Mc91_M`.  The three genuinely
recursive terms each hold **two** nested `fixAcc`, because a lexicographic
`termination_by` becomes a recursion inside a recursion.

Two things are uniform here, and for different reasons:

* **the subject is a transcribed measure, not a named argument.**  Which one a recursion
  gets is read off Lean's own record of how it elaborated the recursion, not guessed from
  the measure.  All four functions of this file carry an explicit `termination_by`, and
  none of them is elaborated structurally — `diagonal`'s and `ackRev`'s measures are
  lexicographic pairs, `hyper`'s too, and `Mc91.M`'s is `101 - n`, which *grows* in the
  argument.  So every node below is written `Term.fixNatWith`, and the subject printed as
  `⟨Lean function⟩` is Lean's own `termination_by` expression transcribed;
* **the self calls are all `deep`.**  `Mc91.M` calls itself inside its own argument
  (`M (M (n + 11))`), and `diagonal`'s outer call stands under `+ 1`, so these two need a
  frame however the test is written.  `ackRev` and `hyper` are the interesting ones: in
  the bodies printed below, every call of the *outer* recursion (`self1`) does hand its
  answer straight back, so the outer recursion is a loop *relative to the inner one* — a
  labelled `continue`.  The tail test does not see that, because it does not look inside
  a nested recursion or inside an application, and the outer body here *is* the inner
  recursion (applied, for `ackRev` and `diagonal`).  Reading a lexicographic pair as two
  nested loops is therefore a real refinement left open; it is not what the current front
  end claims.

So the uniformity is a property of the four functions this file happens to contain — all
of them `termination_by`, all of them Ackermann-shaped — and not of the translation.  The
other combinations are reachable and are tested: `SnapshotsMy/FourSchemes.lean` translates
four functions covering both kinds of subject and both self-call verdicts (`sumAcc` →
structural subject, `tail`; `factD` → structural subject, `deep`; `gcdT` → transcribed
subject, `tail`; `stepsDown` → transcribed subject, `deep`) and proves where each one
landed.
-/

namespace SnapshotsMy.Tco09Schemes

open LeanScript LeanScript.Expr ProgramSnapshotsMyTco09

/-! ## Where the self calls of every recursion node of every generated term stand -/

/-- The lexicographic `(m, n)` of `ackRev` is two nested well-founded recursions, and the
    self call of each stands under a context. -/
theorem ackRev_schemes : Term.schemes tm_ackRev = ["deep", "deep"] := rfl

/-- The lexicographic `(m + n, m)` of `diagonal`, likewise. -/
theorem diagonal_schemes : Term.schemes tm_diagonal = ["deep", "deep"] := rfl

/-- The lexicographic `(n, b)` of `hyper`, likewise. -/
theorem hyper_schemes : Term.schemes tm_hyper = ["deep", "deep"] := rfl

/-- `Mc91.M` is one recursion, on the measure `101 - n`, with a self call nested inside a
    self call. -/
theorem Mc91_M_schemes : Term.schemes tm_Mc91_M = ["deep"] := rfl

/-- `Mc91` itself is **not** a recursion: it calls the global `Mc91.M`. -/
theorem Mc91_schemes : Term.schemes tm_Mc91 = [] := rfl

/-- Every recursion node the module generates, in declaration order: seven of them, all
    the same one. -/
theorem module_schemes :
    Term.schemes tm_ackRev ++ Term.schemes tm_diagonal ++ Term.schemes tm_hyper ++
        Term.schemes tm_Mc91_M ++ Term.schemes tm_Mc91 =
      List.replicate 7 "deep" := rfl

/-! ## The generated bodies, as Lean prints them -/

/--
info: def ProgramSnapshotsMyTco09.tm_ackRev : Term sig_ackRev [] [] (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
Term.fixNatWith [Ty.nat, Ty.nat] (fun as => as.get DeBruijn.head.tail) (fun x => True)
  (Term.fixNatWith [Ty.nat, Ty.nat] (fun as => as.get DeBruijn.head) (fun x => True)
        ((Ops.natEq (Term.var DeBruijn.head.tail) (Term.natL 0)).ite
          ((Term.natL 1).letE
            ((Ops.natAdd (Term.var DeBruijn.head.tail) (Term.var DeBruijn.head)).letE (Term.var DeBruijn.head)))
          ((Ops.natEq (Term.var DeBruijn.head) (Term.natL 0)).ite
            ((Term.natL 1).letE
              ((Term.selfCall RVar.head.tail
                    (Spine.cons (Term.var DeBruijn.head)
                      (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1)) Spine.nil))).letE
                (Term.var DeBruijn.head)))
            ((Term.natL 1).letE
              ((Ops.natAdd (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1)) (Term.var DeBruijn.head)).letE
                ((Term.selfCall RVar.head
                      (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1))
                        (Spine.cons (Term.var DeBruijn.head) Spine.nil))).letE
                  ((Term.selfCall RVar.head.tail
                        (Spine.cons (Term.var DeBruijn.head)
                          (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail.tail) (Term.natL 1))
                            Spine.nil))).letE
                    (Term.var DeBruijn.head))))))) ⬝
      Term.var DeBruijn.head ⬝
    Term.var DeBruijn.head.tail)
-/
#guard_msgs in
#print tm_ackRev

/--
info: def ProgramSnapshotsMyTco09.tm_diagonal : Term sig_diagonal [] [] (Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
Term.fixNatWith [Ty.nat, Ty.nat] (fun as => as.get DeBruijn.head + as.get DeBruijn.head.tail) (fun x => True)
  (Term.fixNatWith [Ty.nat, Ty.nat] (fun as => as.get DeBruijn.head) (fun x => True)
        ((Ops.natEq (Term.var DeBruijn.head) (Term.natL 0)).ite
          ((Ops.natEq (Term.var DeBruijn.head.tail) (Term.natL 0)).ite ((Term.natL 0).letE (Term.var DeBruijn.head))
            ((Term.natL 0).letE
              ((Term.selfCall RVar.head.tail
                    (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1))
                      (Spine.cons (Term.var DeBruijn.head) Spine.nil))).letE
                ((Term.natL 1).letE
                  ((Ops.natAdd (Term.var DeBruijn.head.tail) (Term.var DeBruijn.head)).letE
                    (Term.var DeBruijn.head))))))
          ((Term.natL 1).letE
            ((Ops.natAdd (Term.var DeBruijn.head.tail.tail) (Term.var DeBruijn.head)).letE
              ((Term.selfCall RVar.head
                    (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1))
                      (Spine.cons (Term.var DeBruijn.head) Spine.nil))).letE
                ((Ops.natAdd (Term.var DeBruijn.head) (Term.var DeBruijn.head.tail.tail)).letE
                  (Term.var DeBruijn.head)))))) ⬝
      Term.var DeBruijn.head ⬝
    Term.var DeBruijn.head.tail)
-/
#guard_msgs in
#print tm_diagonal

/--
info: def ProgramSnapshotsMyTco09.tm_hyper : Term sig_hyper [] [] (Ty.nat ⇒ Ty.nat ⇒ Ty.nat ⇒ Ty.nat) :=
Term.fixNatWith [Ty.nat] (fun as => as.get DeBruijn.head) (fun x => True)
  (Term.fixNatWith [Ty.nat, Ty.nat] (fun as => as.get DeBruijn.head.tail) (fun x => True)
    ((Ops.natEq (Term.var DeBruijn.head.tail.tail) (Term.natL 0)).ite
      ((Term.natL 1).letE
        ((Ops.natAdd (Term.var DeBruijn.head.tail.tail) (Term.var DeBruijn.head)).letE (Term.var DeBruijn.head)))
      ((Ops.natEq (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1)) (Term.natL 0)).ite
        ((Ops.natEq (Term.var DeBruijn.head.tail) (Term.natL 0)).ite (Term.var DeBruijn.head)
          ((Term.natL 1).letE
            ((Ops.natAdd (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1))
                  (Term.var DeBruijn.head)).letE
              ((Term.selfCall RVar.head
                    (Spine.cons (Term.var DeBruijn.head.tail.tail)
                      (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1)) Spine.nil))).letE
                ((Term.selfCall RVar.head.tail
                          (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail.tail.tail) (Term.natL 1))
                            Spine.nil) ⬝
                        Term.var DeBruijn.head.tail.tail.tail ⬝
                      Term.var DeBruijn.head).letE
                  (Term.var DeBruijn.head))))))
        ((Ops.natEq (Ops.natSub (Ops.natSub (Term.var DeBruijn.head.tail.tail) (Term.natL 1)) (Term.natL 1))
              (Term.natL 0)).ite
          ((Ops.natEq (Term.var DeBruijn.head.tail) (Term.natL 0)).ite ((Term.natL 0).letE (Term.var DeBruijn.head))
            ((Term.natL 1).letE
              ((Ops.natAdd (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1))
                    (Term.var DeBruijn.head)).letE
                ((Term.selfCall RVar.head
                      (Spine.cons (Term.var DeBruijn.head.tail.tail)
                        (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1)) Spine.nil))).letE
                  ((Term.selfCall RVar.head.tail
                            (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail.tail.tail) (Term.natL 1))
                              Spine.nil) ⬝
                          Term.var DeBruijn.head.tail.tail.tail ⬝
                        Term.var DeBruijn.head).letE
                    (Term.var DeBruijn.head))))))
          ((Ops.natEq (Term.var DeBruijn.head.tail) (Term.natL 0)).ite ((Term.natL 1).letE (Term.var DeBruijn.head))
            ((Term.natL 1).letE
              ((Ops.natAdd (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1))
                    (Term.var DeBruijn.head)).letE
                ((Term.selfCall RVar.head
                      (Spine.cons (Term.var DeBruijn.head.tail.tail)
                        (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.natL 1)) Spine.nil))).letE
                  ((Term.selfCall RVar.head.tail
                            (Spine.cons (Ops.natSub (Term.var DeBruijn.head.tail.tail.tail.tail.tail) (Term.natL 1))
                              Spine.nil) ⬝
                          Term.var DeBruijn.head.tail.tail.tail ⬝
                        Term.var DeBruijn.head).letE
                    (Term.var DeBruijn.head))))))))))
-/
#guard_msgs in
#print tm_hyper

/--
info: def ProgramSnapshotsMyTco09.tm_Mc91_M : Term sig_Mc91_M [] [] (Ty.nat ⇒ Ty.nat) :=
Term.fixNatWith [Ty.nat] (fun as => 101 - as.get DeBruijn.head) (fun x => True)
  ((Term.natL 100).letE
    ((Ops.natLt (Term.var DeBruijn.head) (Term.var DeBruijn.head.tail)).letE
      ((Term.var DeBruijn.head).ite
        ((Term.natL 10).letE
          ((Ops.natSub (Term.var DeBruijn.head.tail.tail.tail) (Term.var DeBruijn.head)).letE
            ((Term.var DeBruijn.head).letE (Term.var DeBruijn.head))))
        ((Term.natL 11).letE
          ((Ops.natAdd (Term.var DeBruijn.head.tail.tail.tail) (Term.var DeBruijn.head)).letE
            ((Term.selfCall RVar.head (Spine.cons (Term.var DeBruijn.head) Spine.nil)).letE
              ((Term.var DeBruijn.head).letE
                ((Term.selfCall RVar.head (Spine.cons (Term.var DeBruijn.head) Spine.nil)).letE
                  ((Term.var DeBruijn.head).letE ((Term.var DeBruijn.head).letE (Term.var DeBruijn.head)))))))))))
-/
#guard_msgs in
#print tm_Mc91_M

/--
info: def ProgramSnapshotsMyTco09.tm_Mc91 : Term sig_Mc91 [] [] (Ty.nat ⇒ Ty.nat) :=
ƛ (Term.global GlobalRef.here ⬝ Term.var DeBruijn.head).letE ((Term.var DeBruijn.head).letE (Term.var DeBruijn.head))
-/
#guard_msgs in
#print tm_Mc91

/-! ## The same bodies in the notation of `LeanScript.ExprPretty`

`♯n` is the local variable at de Bruijn index `n`, `selfk⟨↓⟩(…)` a call of the recursion
`k` levels out, `extern⟨…⟩` a call of the runtime, and
`fixAcc (σ…) subject { ⟨Lean function⟩ } body { … }` the recursion node of the grammar,
whose subject is a Lean function of the arguments and so has nothing of the object
language to print. -/

/--
info: fixAcc (nat nat) subject { ⟨Lean function⟩ } body {
  ((fixAcc (nat nat) subject { ⟨Lean function⟩ } body {
    if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
    ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then let ♯ := 1#;
    let ♯ := self1⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#));
    ♯0 else let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#)) ⬝ ♯0);
    let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
    let ♯ := self1⟨↓⟩(♯0, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯4) ⬝ 1#));
    ♯0
  } ⬝ ♯0) ⬝ ♯1)
}
-/
#guard_msgs in
#eval IO.println (Term.pretty tm_ackRev 0)

/--
info: fixAcc (nat nat) subject { ⟨Lean function⟩ } body {
  ((fixAcc (nat nat) subject { ⟨Lean function⟩ } body {
    if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 0#;
    ♯0 else let ♯ := 0#;
    let ♯ := self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
    let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯1) ⬝ ♯0);
    ♯0 else let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
    let ♯ := self0⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#), ♯0);
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯0) ⬝ ♯2);
    ♯0
  } ⬝ ♯0) ⬝ ♯1)
}
-/
#guard_msgs in
#eval IO.println (Term.pretty tm_diagonal 0)

/--
info: fixAcc (nat) subject { ⟨Lean function⟩ } body {
  fixAcc (nat nat) subject { ⟨Lean function⟩ } body {
    if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯2) ⬝ 0#) then let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ ♯0);
    ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#)) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then ♯0 else let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#)) ⬝ ♯0);
    let ♯ := self0⟨↓⟩(♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#));
    let ♯ := ((self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ 1#)) ⬝ ♯3) ⬝ ♯0);
    ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯2) ⬝ 1#)) ⬝ 1#)) ⬝ 0#) then if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 0#;
    ♯0 else let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#)) ⬝ ♯0);
    let ♯ := self0⟨↓⟩(♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#));
    let ♯ := ((self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ 1#)) ⬝ ♯3) ⬝ ♯0);
    ♯0 else if ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯1) ⬝ 0#) then let ♯ := 1#;
    ♯0 else let ♯ := 1#;
    let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#)) ⬝ ♯0);
    let ♯ := self0⟨↓⟩(♯2, ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ 1#));
    let ♯ := ((self1⟨↓⟩(((extern⟨nat nat ⇒ nat⟩ ⬝ ♯5) ⬝ 1#)) ⬝ ♯3) ⬝ ♯0);
    ♯0
  }
}
-/
#guard_msgs in
#eval IO.println (Term.pretty tm_hyper 0)

/--
info: fixAcc (nat) subject { ⟨Lean function⟩ } body {
  let ♯ := 100#;
  let ♯ := ((extern⟨nat nat ⇒ bool⟩ ⬝ ♯0) ⬝ ♯1);
  if ♯0 then let ♯ := 10#;
  let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
  let ♯ := ♯0;
  ♯0 else let ♯ := 11#;
  let ♯ := ((extern⟨nat nat ⇒ nat⟩ ⬝ ♯3) ⬝ ♯0);
  let ♯ := self0⟨↓⟩(♯0);
  let ♯ := ♯0;
  let ♯ := self0⟨↓⟩(♯0);
  let ♯ := ♯0;
  let ♯ := ♯0;
  ♯0
}
-/
#guard_msgs in
#eval IO.println (Term.pretty tm_Mc91_M 0)

/--
info: ƛ let ♯ := (@Mc91.M ⬝ ♯0);
let ♯ := ♯0;
♯0
-/
#guard_msgs in
#eval IO.println (Term.pretty tm_Mc91 0)

end SnapshotsMy.Tco09Schemes
