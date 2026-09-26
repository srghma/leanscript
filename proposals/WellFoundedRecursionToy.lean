module

/-
Toy model for `proposals/WellFoundedRecursionAssessment.md` (not part of the Lake build; it only
uses the Lean core library).  Check it with the plain compiler:

    lean proposals/WellFoundedRecursionToy.lean

It checks the claims the assessment relies on:

1. `fuelFix` / `checkedFix`: a well-founded recursion on a `Nat` measure, **with no proof in
   the program**, is a total function defined by structural recursion on a fuel (the scheme
   of Lean's own `WellFounded.Nat.fix`).  It agrees with every function that satisfies the
   recursive equation, provided the body only uses the recursive calls on smaller arguments
   (`fuelFix_agree`, `checkedFix_agree`).  So the proof that a translation is correct is a
   theorem stated *afterwards*, not a proof carried by the term.
2. `checkedFix` (the calls are checked when they run) has an **unconditional** unfolding
   equation (`checkedFix_eq`).
3. A tiny term language whose `fix` node binds the recursive function as an ordinary
   variable of function type (so recursive calls are ordinary applications, also inside
   lambdas), with a structural evaluator, and a correctness theorem for one translated
   function (`log2T_correct`).
4. Kernel reduction: the toy terms evaluate by `decide +kernel`; Lean's lexicographic
   well-founded recursion (`termination_by (a, b)`) does not (`lexLoop`).
-/

namespace WfToy

/-! ## 1. The two combinators -/

section
variable {α β : Type} (μ : α → Nat) (fb : α → β) (F : α → (α → β) → β)

/-- Fuel only: the fuel is `μ x + 1` at the entry, and every recursive call uses up one unit.
No check at the calls; the fallback `fb` answers when the fuel runs out, which never happens
when every call goes down along `μ`. -/
def fuelFix (x : α) : β := go (μ x + 1) x
where
  go : Nat → α → β
    | 0, x => fb x
    | n + 1, x => F x (go n)

/-- Checked: every recursive call compares the measures when it runs, and answers with the
fallback if the argument is not smaller. -/
def checkedFix (x : α) : β := go (μ x + 1) x
where
  go : Nat → α → β
    | 0, x => fb x
    | n + 1, x => F x (fun y => if μ y < μ x then go n y else fb y)

/-- The body uses the recursive calls only on arguments below the current one.  This is what
the (erased) decreasing proofs of a Lean definition guarantee. -/
def Respects : Prop :=
  ∀ x (g g' : α → β), (∀ y, μ y < μ x → g y = g' y) → F x g = F x g'

theorem fuelFix_go_agree (f : α → β) (hF : Respects μ F) (hf : ∀ x, f x = F x f) :
    ∀ n x, μ x < n → fuelFix.go fb F n x = f x := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    show F x (fuelFix.go fb F n) = f x
    rw [hf x]
    exact hF x _ _ fun y hy => ih y (by omega)

/-- **Agreement (fuel)**: the fuelled recursion computes every solution of the recursive
equation of a body that respects the measure. -/
theorem fuelFix_agree (f : α → β) (hF : Respects μ F) (hf : ∀ x, f x = F x f) (x : α) :
    fuelFix μ fb F x = f x :=
  fuelFix_go_agree μ fb F f hF hf _ x (Nat.lt_succ_self _)

theorem checkedFix_go_agree (f : α → β) (hF : Respects μ F) (hf : ∀ x, f x = F x f) :
    ∀ n x, μ x < n → checkedFix.go μ fb F n x = f x := by
  intro n
  induction n with
  | zero => intro x h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro x hx
    show F x (fun y => if μ y < μ x then checkedFix.go μ fb F n y else fb y) = f x
    rw [hf x]
    refine hF x _ _ fun y hy => ?_
    rw [ite_eq_left hy]
    exact ih y (by omega)

/-- **Agreement (checked)**. -/
theorem checkedFix_agree (f : α → β) (hF : Respects μ F) (hf : ∀ x, f x = F x f) (x : α) :
    checkedFix μ fb F x = f x :=
  checkedFix_go_agree μ fb F f hF hf _ x (Nat.lt_succ_self _)

theorem checkedFix_go_stable :
    ∀ n m x, μ x < n → μ x < m → checkedFix.go μ fb F n x = checkedFix.go μ fb F m x := by
  intro n
  induction n with
  | zero => intro m x h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro m x hn hm
    cases m with
    | zero => exact absurd hm (Nat.not_lt_zero _)
    | succ m =>
      show F x (fun y => if μ y < μ x then checkedFix.go μ fb F n y else fb y) =
        F x (fun y => if μ y < μ x then checkedFix.go μ fb F m y else fb y)
      congr 1
      funext y
      by_cases hy : μ y < μ x
      · rw [ite_eq_left hy, ite_eq_left hy]; exact ih m y (by omega) (by omega)
      · rw [ite_eq_right hy, ite_eq_right hy]

/-- **Unfolding (checked)**, with no hypothesis at all: a checked recursion is its body,
applied to the checked recursive function. -/
theorem checkedFix_eq (x : α) :
    checkedFix μ fb F x =
      F x (fun y => if μ y < μ x then checkedFix μ fb F y else fb y) := by
  show F x (fun y => if μ y < μ x then checkedFix.go μ fb F (μ x) y else fb y) = _
  congr 1
  funext y
  by_cases hy : μ y < μ x
  · rw [ite_eq_left hy, ite_eq_left hy]
    exact checkedFix_go_stable μ fb F _ _ y hy (Nat.lt_succ_self _)
  · rw [ite_eq_right hy, ite_eq_right hy]

end

/-! ## 2. A tiny term language with a proof-free `fix` node -/

inductive Ty | nat | bool | fn (a b : Ty)

abbrev Ty.Den : Ty → Type
  | .nat => Nat
  | .bool => Bool
  | .fn a b => a.Den → b.Den

abbrev Env : List Ty → Type
  | [] => Unit
  | t :: ts => t.Den × Env ts

inductive Var : List Ty → Ty → Type
  | here {Γ t} : Var (t :: Γ) t
  | there {Γ s t} : Var Γ t → Var (s :: Γ) t

def Var.get : {Γ : List Ty} → {t : Ty} → Var Γ t → Env Γ → t.Den
  | _ :: _, _, .here, e => e.1
  | _ :: _, _, .there v, e => v.get e.2

inductive Term : List Ty → Ty → Type
  | var {Γ t} : Var Γ t → Term Γ t
  | lit {Γ} : Nat → Term Γ .nat
  | sub {Γ} : Term Γ .nat → Term Γ .nat → Term Γ .nat
  | add {Γ} : Term Γ .nat → Term Γ .nat → Term Γ .nat
  | div {Γ} : Term Γ .nat → Term Γ .nat → Term Γ .nat
  | le {Γ} : Term Γ .nat → Term Γ .nat → Term Γ .bool
  | ite {Γ t} : Term Γ .bool → Term Γ t → Term Γ t → Term Γ t
  | lam {Γ a b} : Term (a :: Γ) b → Term Γ (.fn a b)
  | ap {Γ a b} : Term Γ (.fn a b) → Term Γ a → Term Γ b
  /-- `fix f x. body`, recursive on the `Nat` measure `μ` of its parameter.  In `body`, the
  parameter is variable `1` and the recursive function itself is variable `0`: an ordinary
  variable of function type, so a recursive call is an ordinary application (also under a
  `lam`, or passed to another function).  No proof: the fallback `fb` answers a call that
  does not go down. -/
  | fix {Γ a b} (μ : Term (a :: Γ) .nat) (fb : Term (a :: Γ) b)
      (body : Term (.fn a b :: a :: Γ) b) : Term Γ (.fn a b)

/-- The evaluator: structural recursion on the term; a `fix` node runs `checkedFix`, whose
own recursion is structural on the fuel. -/
def Term.eval : {Γ : List Ty} → {t : Ty} → Term Γ t → Env Γ → t.Den
  | _, _, .var v, e => v.get e
  | _, _, .lit n, _ => n
  | _, _, .sub a b, e => a.eval e - b.eval e
  | _, _, .add a b, e => a.eval e + b.eval e
  | _, _, .div a b, e => a.eval e / b.eval e
  | _, _, .le a b, e => decide (a.eval e ≤ b.eval e)
  | _, _, .ite c a b, e => if c.eval e then a.eval e else b.eval e
  | _, _, .lam b, e => fun x => b.eval (x, e)
  | _, _, .ap f a, e => f.eval e (a.eval e)
  | _, _, .fix μ fb body, e =>
      checkedFix (fun x => μ.eval (x, e)) (fun x => fb.eval (x, e))
        (fun x rec => body.eval (rec, x, e))

/-- `log2 n = if n ≤ 1 then 0 else log2 (n / 2) + 1`, as Lean compiles it: a well-founded
recursion on the measure `n` (`WellFounded.Nat.fix`), with a decreasing proof. -/
def log2 (n : Nat) : Nat := if n ≤ 1 then 0 else log2 (n / 2) + 1
termination_by n
decreasing_by omega

/-- Its translation: the same body, the recursive call an application of variable `0`, the
decreasing proof erased, the measure `n` kept (it is data). -/
def log2T : Term [] (.fn .nat .nat) :=
  .fix (.var .here) (.lit 0)
    (.ite (.le (.var (.there .here)) (.lit 1)) (.lit 0)
      (.add (.ap (.var .here) (.div (.var (.there .here)) (.lit 2))) (.lit 1)))

example : log2T.eval () 1000 = 9 := by decide +kernel
example : log2T.eval () 1 = 0 := by decide +kernel

/-- **The translation is correct**, proved after the fact from the recursive equation of the
Lean function (`log2.eq_1`), with the fact that the body only calls on smaller arguments;
the term itself holds no proof. -/
theorem log2T_correct (n : Nat) : log2T.eval () n = log2 n := by
  show checkedFix _ _ _ n = log2 n
  refine checkedFix_agree _ _ _ log2 ?_ ?_ n
  · intro x g g' h
    show (if decide (x ≤ 1) = true then 0 else g (x / 2) + 1) =
      (if decide (x ≤ 1) = true then 0 else g' (x / 2) + 1)
    by_cases hx : x ≤ 1
    · simp [hx]
    · simp only [hx, decide_false, Bool.false_eq_true, ite_false]
      rw [h (x / 2) (by show x / 2 < x; omega)]
  · intro x
    rw [log2.eq_1]
    show _ = (if decide (x ≤ 1) = true then 0 else log2 (x / 2) + 1)
    by_cases hx : x ≤ 1 <;> simp [hx]

/-- A recursive call **under a lambda**: `sumTo n = n + (fun k => sumTo k) (n - 1)`; with the
recursive function an ordinary variable, nothing special is needed. -/
def sumToT : Term [] (.fn .nat .nat) :=
  .fix (.var .here) (.lit 0)
    (.ite (.le (.var (.there .here)) (.lit 0)) (.lit 0)
      (.add (.var (.there .here))
        (.ap (.lam (.ap (.var (.there .here)) (.var .here)))
          (.sub (.var (.there .here)) (.lit 1)))))

example : sumToT.eval () 100 = 5050 := by decide +kernel

/-! ## 3. Kernel reduction of Lean's own well-founded definitions -/

/-- A `Nat` measure: Lean compiles it with `WellFounded.Nat.fix` (a fuel), which the kernel
reduces. -/
def countDown (n acc : Nat) : Nat := if n = 0 then acc else countDown (n - 1) (acc + 1)
termination_by n

example : countDown 2000 0 = 2000 := by decide +kernel

/-- A lexicographic measure: Lean compiles it with `WellFounded.fix` on `Prod.Lex`, which the
kernel does **not** reduce. -/
def lexLoop (a b : Nat) : Nat :=
  if a = 0 then b else if b = 0 then lexLoop (a - 1) 5 else lexLoop a (b - 1) + 1
termination_by (a, b)

example : True := by
  fail_if_success (have : lexLoop 3 2 = 17 := by decide +kernel)
  trivial

/-! ## 4. A lexicographic measure with two fuels, no proof

The outer fuel bounds the first component, the inner one the second; the inner fuel is
renewed (from the measure of the new argument) whenever the first component goes down.  Both
recursions are structural, so the kernel reduces it (the agreement theorem for this
combinator is not proved here; only the evaluations below are checked). -/

section
variable {α β : Type} (μ1 μ2 : α → Nat) (fb : α → β) (F : α → (α → β) → β)

def lexStep (prev : Nat → α → β) : Nat → α → β
  | 0, x => fb x
  | nb + 1, x => F x (fun y =>
      if μ1 y < μ1 x then prev (μ2 y + 1) y
      else if μ1 y = μ1 x ∧ μ2 y < μ2 x then lexStep prev nb y else fb y)

def lexGo : Nat → Nat → α → β
  | 0 => fun _ x => fb x
  | na + 1 => lexStep μ1 μ2 fb F (lexGo na)

def lexFix (x : α) : β := lexGo μ1 μ2 fb F (μ1 x + 1) (μ2 x + 1) x

end

/-- Ackermann's function, `termination_by (m, n)`, with the proofs erased. -/
def ackT : Nat × Nat → Nat :=
  lexFix (fun p => p.1) (fun p => p.2) (fun _ => 0) fun p rec =>
    match p with
    | (0, n) => n + 1
    | (m + 1, 0) => rec (m, 1)
    | (m + 1, n + 1) => rec (m, rec (m + 1, n))

example : ackT (2, 3) = 9 := by decide +kernel
example : ackT (3, 3) = 61 := by decide +kernel

/-- The same loop as `lexLoop`, which the kernel could not run. -/
def lexLoopT : Nat × Nat → Nat :=
  lexFix (fun p => p.1) (fun p => p.2) (fun _ => 0) fun p rec =>
    if p.1 = 0 then p.2 else if p.2 = 0 then rec (p.1 - 1, 5) else rec (p.1, p.2 - 1) + 1

example : lexLoopT (3, 2) = 17 := by decide +kernel

end WfToy
