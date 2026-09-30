module

@[expose] public section

set_option autoImplicit false

/-!
# The JavaScript rewrites of `CaseGuarded`, in a model of JavaScript

Three rewrites of the JavaScript backend have no counterpart in `Term` (whose optimiser is
proved in `LeanScript/Term/Optimize/`): they are about JavaScript's own operators and
statements.  This file proves them in a small model of JavaScript, where an expression or a
statement is a computation that reads and writes a state `σ` and may throw an exception `ε`
(`Js σ ε α`, `StateT σ (Except ε) α`), so evaluation order, effects and exceptions all count.

* **`&&` and `||`** (the printer, `JsTerm/Print/Mini/Block.lean`): a boolean `c ? a : false` is
  `c && a` and `c ? true : b` is `c || b` (`cond_false_eq_and`, `cond_true_eq_or`); a chain may
  be grouped to the left (`jsAnd_assoc`, `jsOr_assoc`).
* **Tests ending in the same statements** (`JsTerm/Lower/MergeIte.lean`, `JsBlock.mergeIte`):
  the rewrite is modelled on syntax (`Cnd`, `Stmt`; the same dump is modelled as syntactic
  equality) with the same algorithm (`Cnd.mkAnd`, `Cnd.mkOr`, `Stmt.mkIte`, `Stmt.mergeIte`),
  and proved to leave the meaning of every statement unchanged (`Stmt.mergeIte_den`), for any
  meaning of the tests and of the other statements (`atom`, `leaf`).
* **Digits in a concatenation** (the printer): `s + String(x)` is `s + x`, and
  `String(x) + s` is `x + s`, when `s` is a string (`plus_str_digits`, `plus_digits_str`), in a
  model of JavaScript's `+` on numbers, `BigInt`s and strings (`JsVal.plus`), where the string of
  an integer (JavaScript's `ToString`, exact for safe integers and every `BigInt`) is its decimal
  digits, Lean's `toString` (`JsVal.toStr`).  So `"n: " + n` is Lean's `"n: " ++ toString n`
  (`plus_str_num`).
-/

namespace JsSpec

/-- A JavaScript computation: it reads and writes the state `σ`, and may throw `ε`. -/
abbrev Js (σ ε α : Type) : Type := StateT σ (Except ε) α

variable {σ ε : Type}

/-! ## `&&` and `||` -/

/-- `c ? a : b`: `c` first, then one of the branches. -/
def cond {α : Type} (c : Js σ ε Bool) (a b : Js σ ε α) : Js σ ε α := do
  if (← c) then a else b

/-- JavaScript's `a && b`: `a` first; its value when it is falsy, otherwise `b`. -/
def jsAnd (a b : Js σ ε Bool) : Js σ ε Bool := do
  let x ← a
  if x then b else pure x

/-- JavaScript's `a || b`: `a` first; its value when it is truthy, otherwise `b`. -/
def jsOr (a b : Js σ ε Bool) : Js σ ε Bool := do
  let x ← a
  if x then pure x else b

/-- `c ? a : false` is `c && a`. -/
theorem cond_false_eq_and (c a : Js σ ε Bool) : cond c a (pure false) = jsAnd c a := by
  funext s
  simp only [cond, jsAnd, bind, StateT.bind]
  cases c s with
  | error e => rfl
  | ok p =>
    rcases p with ⟨x, s'⟩
    cases x <;> rfl

/-- `c ? true : b` is `c || b`. -/
theorem cond_true_eq_or (c b : Js σ ε Bool) : cond c (pure true) b = jsOr c b := by
  funext s
  simp only [cond, jsOr, bind, StateT.bind]
  cases c s with
  | error e => rfl
  | ok p =>
    rcases p with ⟨x, s'⟩
    cases x <;> rfl

/-- `a && (b && c)` is `(a && b) && c`. -/
theorem jsAnd_assoc (a b c : Js σ ε Bool) : jsAnd a (jsAnd b c) = jsAnd (jsAnd a b) c := by
  funext s
  simp only [jsAnd, bind, StateT.bind, pure]
  rcases a s with e | ⟨x, s'⟩
  · rfl
  · cases x <;> simp only [Except.bind, StateT.bind, Bool.false_eq_true, ite_true, ite_false] <;>
      rcases b s' with e | ⟨y, s''⟩ <;> (try cases y) <;>
      simp [Except.bind, StateT.pure, pure, Except.pure, bind]

/-- `a || (b || c)` is `(a || b) || c`. -/
theorem jsOr_assoc (a b c : Js σ ε Bool) : jsOr a (jsOr b c) = jsOr (jsOr a b) c := by
  funext s
  simp only [jsOr, bind, StateT.bind, pure]
  rcases a s with e | ⟨x, s'⟩
  · rfl
  · cases x <;> simp only [Except.bind, StateT.bind, Bool.false_eq_true, ite_true, ite_false] <;>
      rcases b s' with e | ⟨y, s''⟩ <;> (try cases y) <;>
      simp [Except.bind, StateT.pure, pure, Except.pure, bind]

/-! ## Tests ending in the same statements -/

/-- Tests: an atom (any expression, by its position), `a && b`, `a || b`. -/
inductive Cnd where
  | atom (i : Nat)
  | and (a b : Cnd)
  | or (a b : Cnd)
  deriving DecidableEq

/-- Statements: a statement that is not a test (any statement, by its position), and
    `if (c) { t } else { e }`. -/
inductive Stmt where
  | leaf (i : Nat)
  | ite (c : Cnd) (t e : Stmt)
  deriving DecidableEq

section Den
variable {R : Type} (atom : Nat → Js σ ε Bool) (leaf : Nat → Js σ ε R)

/-- The meaning of a test. -/
def Cnd.den : Cnd → Js σ ε Bool
  | .atom i => atom i
  | .and a b => jsAnd (a.den) (b.den)
  | .or a b => jsOr (a.den) (b.den)

/-- The meaning of a statement: the test first, then one branch. -/
def Stmt.den : Stmt → Js σ ε R
  | .leaf i => leaf i
  | .ite c t e => cond (c.den atom) (t.den) (e.den)

end Den

/-- `a && b`, grouped to the left (`JsExpr.mkAnd`). -/
def Cnd.mkAnd (a : Cnd) : Cnd → Cnd
  | .and b₁ b₂ => .and (Cnd.mkAnd a b₁) b₂
  | b => .and a b

/-- `a || b`, grouped to the left (`JsExpr.mkOr`). -/
def Cnd.mkOr (a : Cnd) : Cnd → Cnd
  | .or b₁ b₂ => .or (Cnd.mkOr a b₁) b₂
  | b => .or a b

theorem Cnd.mkAnd_den (atom : Nat → Js σ ε Bool) (a : Cnd) :
    ∀ b : Cnd, (Cnd.mkAnd a b).den atom = jsAnd (a.den atom) (b.den atom)
  | .and b₁ b₂ => by
    simp only [Cnd.mkAnd, Cnd.den, Cnd.mkAnd_den atom a b₁, jsAnd_assoc]
  | .atom _ => rfl
  | .or _ _ => rfl

theorem Cnd.mkOr_den (atom : Nat → Js σ ε Bool) (a : Cnd) :
    ∀ b : Cnd, (Cnd.mkOr a b).den atom = jsOr (a.den atom) (b.den atom)
  | .or b₁ b₂ => by
    simp only [Cnd.mkOr, Cnd.den, Cnd.mkOr_den atom a b₁, jsOr_assoc]
  | .atom _ => rfl
  | .and _ _ => rfl

/-- `if (c) { t } else { e }`, merged as `JsBlock.mkIte` does:
    `if (c) { if (b) { t' } else { e' } } else { e }` is `if (c && b) { t' } else { e' }` when
    `e'` is `e`, and `if (c) { t } else { if (b) { e' } else { t' } }` is
    `if (c || b) { t } else { t' }` when `e'` is `t`. -/
def Stmt.mkIte (c : Cnd) (t e : Stmt) : Stmt :=
  let viaAnd? : Option Stmt := match t with
    | .ite b t' e' => if e' = e then some (.ite (Cnd.mkAnd c b) t' e') else none
    | _ => none
  match viaAnd? with
  | some r => r
  | none =>
    match e with
    | .ite b e' t' => if t = e' then .ite (Cnd.mkOr c b) t t' else .ite c t e
    | _ => .ite c t e

/-- `Stmt.mkIte` everywhere, bottom-up (`JsBlock.mergeIte`). -/
def Stmt.mergeIte : Stmt → Stmt
  | .leaf i => .leaf i
  | .ite c t e => Stmt.mkIte c t.mergeIte e.mergeIte

section Correct
variable {R : Type} (atom : Nat → Js σ ε Bool) (leaf : Nat → Js σ ε R)

/-- `if (a) { if (b) { t } else { e } } else { e }` is `if (a && b) { t } else { e }`. -/
theorem cond_cond_same_else (a b : Js σ ε Bool) (t e : Js σ ε R) :
    cond a (cond b t e) e = cond (jsAnd a b) t e := by
  funext s
  simp only [cond, jsAnd, bind, StateT.bind, pure]
  rcases a s with e | ⟨x, s'⟩
  · rfl
  · cases x <;> simp only [Except.bind, StateT.bind, Bool.false_eq_true, ite_true, ite_false] <;>
      rcases b s' with e | ⟨y, s''⟩ <;> (try cases y) <;>
      simp [Except.bind, StateT.pure, pure, Except.pure, bind]

/-- `if (a) { t } else { if (b) { t } else { e } }` is `if (a || b) { t } else { e }`. -/
theorem cond_same_then_cond (a b : Js σ ε Bool) (t e : Js σ ε R) :
    cond a t (cond b t e) = cond (jsOr a b) t e := by
  funext s
  simp only [cond, jsOr, bind, StateT.bind, pure]
  rcases a s with e | ⟨x, s'⟩
  · rfl
  · cases x <;> simp only [Except.bind, StateT.bind, Bool.false_eq_true, ite_true, ite_false] <;>
      rcases b s' with e | ⟨y, s''⟩ <;> (try cases y) <;>
      simp [Except.bind, StateT.pure, pure, Except.pure, bind]

/-- The merge of two tests leaves the meaning of the statement unchanged. -/
theorem Stmt.mkIte_den (c : Cnd) (t e : Stmt) :
    (Stmt.mkIte c t e).den atom leaf = (Stmt.ite c t e).den atom leaf := by
  cases t with
  | ite b t' e' =>
    by_cases he : e' = e
    · subst he
      simp [Stmt.mkIte, Stmt.den, Cnd.mkAnd_den, cond_cond_same_else]
    · cases e with
      | ite b₂ e₂ t₂ =>
        by_cases ht : Stmt.ite b t' e' = e₂
        · subst ht
          simp [Stmt.mkIte, he, Stmt.den, Cnd.mkOr_den, cond_same_then_cond]
        · simp [Stmt.mkIte, he, ht]
      | leaf i => simp [Stmt.mkIte, he]
  | leaf i =>
    cases e with
    | ite b₂ e₂ t₂ =>
      by_cases ht : Stmt.leaf i = e₂
      · subst ht
        simp [Stmt.mkIte, Stmt.den, Cnd.mkOr_den, cond_same_then_cond]
      · simp [Stmt.mkIte, ht]
    | leaf j => rfl

/-- **The rewrite of `JsBlock.mergeIte` is correct**: merging, everywhere in a statement, the
    tests that end in the same statements leaves its meaning unchanged, for every meaning of
    the tests and of the other statements (their effects and exceptions included). -/
theorem Stmt.mergeIte_den : ∀ s : Stmt, s.mergeIte.den atom leaf = s.den atom leaf
  | .leaf _ => rfl
  | .ite c t e => by
    rw [Stmt.mergeIte, Stmt.mkIte_den]
    simp only [Stmt.den, Stmt.mergeIte_den t, Stmt.mergeIte_den e]

end Correct

/-! ## Digits in a concatenation -/

/-- JavaScript values: a `number` holding an integer, a `BigInt`, a string. -/
inductive JsVal where
  | num (n : Int)
  | big (n : Int)
  | str (s : String)
  deriving DecidableEq

/-- JavaScript's `ToString`: the decimal digits of an integer (with a `-` when negative), a
    string itself. -/
def JsVal.toStr : JsVal → String
  | .num n => toString n
  | .big n => toString n
  | .str s => s

/-- `String(x)`. -/
def JsVal.digits (v : JsVal) : JsVal := .str v.toStr

/-- JavaScript's `a + b`: a concatenation when either operand is a string, an addition of two
    numbers or of two `BigInt`s, a `TypeError` when a `number` is added to a `BigInt`. -/
def JsVal.plus : JsVal → JsVal → Except String JsVal
  | .str a, b => .ok (.str (a ++ b.toStr))
  | a, .str b => .ok (.str (a.toStr ++ b))
  | .num a, .num b => .ok (.num (a + b))
  | .big a, .big b => .ok (.big (a + b))
  | _, _ => .error "TypeError"

/-- `s + String(x)` is `s + x`, when `s` is a string. -/
theorem plus_str_digits (s : String) (v : JsVal) :
    (JsVal.str s).plus v.digits = (JsVal.str s).plus v := by
  cases v <;> rfl

/-- `String(x) + s` is `x + s`, when `s` is a string. -/
theorem plus_digits_str (v : JsVal) (s : String) :
    v.digits.plus (.str s) = v.plus (.str s) := by
  cases v <;> rfl

/-- `"n: " + n` is Lean's `"n: " ++ toString n`, for a `number` or a `BigInt` `n`. -/
theorem plus_str_num (s : String) (n : Int) :
    (JsVal.str s).plus (.num n) = .ok (.str (s ++ toString n)) ∧
      (JsVal.str s).plus (.big n) = .ok (.str (s ++ toString n)) :=
  ⟨rfl, rfl⟩

end JsSpec

end
