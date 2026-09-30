module

public import LeanScript.Term.Semantics.Eval
public import LeanScript.Term.Extern.Eval

@[expose] public section

set_option autoImplicit false

/-!
# String append chains

`StrApp.normNeu` regroups a chain of string appends (`String.append`, the extern
`lean_string_append__String_append`, and `String.push` of a literal character, which is the
append of a one-character literal): the chain is read into its operands (`StrApp.flat`),
empty string literals are dropped and neighbouring string literals are merged into one
(`StrApp.merge`), and the operands are appended again **from the left**,
`((x₁ ++ x₂) ++ …) ++ xₙ` (`StrApp.buildL`).

`"a" ++ (((("b" ++ x) ++ x) ++ x) ++ x ++ "c") ++ "d"` becomes
`(((("ab" ++ x) ++ x) ++ x) ++ x) ++ "cd"`, which the JavaScript backend writes without
parentheses, `"ab" + x + x + x + x + "cd"`.

The left grouping is the one both targets append best with: `String.append` appends its second
operand onto its first (in place when nothing else refers to it), and JavaScript's `+` groups
to the left, so no parenthesis is needed.

Proved: the value is unchanged (`StrApp.normNeu_eval`), from the associativity of `String.append`
and `""` being its unit.  It is run by `Neu.normAppend` (`LeanScript.Term.Optimize.Append`), so
it is part of `Term.appendWalk` and of `Term.optimize`.
-/

namespace LeanScript
namespace StrApp
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

/-- The string type. -/
abbrev strTy : Ty ks := .prim .string

/-- An operand of a string append chain: a pure string expression, at any level. -/
abbrev Opnd (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) : Type :=
  Σ o : Lvl, PExpr Δ Φ Γ strTy o

/-- The value of a string expression. -/
def val {o : Lvl} (e : PExpr Δ Φ Γ strTy o) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : String :=
  e.eval κ ρ

/-- The operands, appended one after the other. -/
def den (ops : List (Opnd Δ Φ Γ)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : String :=
  ops.foldr (fun p acc => val p.2 κ ρ ++ acc) ""

@[simp] theorem den_nil (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : den ([] : List (Opnd Δ Φ Γ)) κ ρ = "" :=
  rfl

@[simp] theorem den_cons (p : Opnd Δ Φ Γ) (ops : List (Opnd Δ Φ Γ)) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) : den (p :: ops) κ ρ = val p.2 κ ρ ++ den ops κ ρ := rfl

@[simp] theorem den_append (ops ops' : List (Opnd Δ Φ Γ)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    den (ops ++ ops') κ ρ = den ops κ ρ ++ den ops' κ ρ := by
  induction ops with
  | nil => simp [String.empty_append]
  | cons p ops ih => simp [ih, String.append_assoc]

/-- The two operands of a string append, with the fact that the append is their concatenation. -/
structure Split {o : Lvl} (e : PExpr Δ Φ Γ strTy o) where
  o₁ : Lvl
  o₂ : Lvl
  a : PExpr Δ Φ Γ strTy o₁
  b : PExpr Δ Φ Γ strTy o₂
  eval : ∀ κ ρ, val e κ ρ = val a κ ρ ++ val b κ ρ

/-- The character of a character literal. -/
def charLit? : {o : Lvl} → (e : PExpr Δ Φ Γ (.prim .char) o) →
    Option {c : Char // ∀ κ ρ, e.eval κ ρ = c}
  | _, .lit .char c => some ⟨c, fun _ _ => rfl⟩
  | _, _ => none

/-- The operands of a string append, when a pure expression is one. -/
def view : {o : Lvl} → (e : PExpr Δ Φ Γ strTy o) → Option (Split e)
  | _, .neu (.extern (.stringDefsExtern .lean_string_append__String_append)
      (.cons a (.cons b .nil)) _) => some ⟨_, _, a, b, fun _ _ => rfl⟩
  | _, .neu (.extern (.stringBootstrapExtern .lean_string_push) (.cons a (.cons b .nil)) _) =>
      match charLit? b with
      | some c => some ⟨_, _, a, .lit .string (String.singleton c.1), fun κ ρ => by
          show String.push (val a κ ρ) (b.eval κ ρ) = _
          rw [c.2 κ ρ]; exact String.push_eq_append c.1⟩
      | none => none
  | _, _ => none

/-- The operands of a string append chain, however it is grouped (at most `n` levels deep). -/
def flat : Nat → {o : Lvl} → PExpr Δ Φ Γ strTy o → List (Opnd Δ Φ Γ)
  | 0, _, e => [⟨_, e⟩]
  | n + 1, _, e =>
    match view e with
    | some s => flat n s.a ++ flat n s.b
    | none => [⟨_, e⟩]

theorem flat_den (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (n : Nat) → {o : Lvl} → (e : PExpr Δ Φ Γ strTy o) → den (flat n e) κ ρ = val e κ ρ
  | 0, _, _ => by simp [flat, String.append_empty]
  | n + 1, _, e => by
    unfold flat
    split
    · rename_i s _
      rw [den_append, flat_den κ ρ n, flat_den κ ρ n, s.eval]
    · simp [String.append_empty]

/-- The string of a string literal. -/
def litView : {o : Lvl} → (e : PExpr Δ Φ Γ strTy o) → Option {s : String // ∀ κ ρ, val e κ ρ = s}
  | _, .lit .string v => some ⟨v, fun _ _ => rfl⟩
  | _, _ => none

/-- A string literal. -/
def lit (s : String) : Opnd Δ Φ Γ := ⟨none, .lit .string s⟩

@[simp] theorem lit_val (s : String) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : val (lit (Δ := Δ) (Φ := Φ) (Γ := Γ) s).2 κ ρ = s :=
  rfl

/-- An operand in front of operands: an empty literal is dropped, and two literals next to
    each other become one. -/
def consLit (x : Opnd Δ Φ Γ) (ys : List (Opnd Δ Φ Γ)) : List (Opnd Δ Φ Γ) :=
  match litView x.2 with
  | some l =>
    if l.1 = "" then ys
    else
      match ys with
      | y :: ys' =>
        match litView y.2 with
        | some m => lit (l.1 ++ m.1) :: ys'
        | none => x :: ys
      | [] => [x]
  | none => x :: ys

theorem consLit_den (x : Opnd Δ Φ Γ) (ys : List (Opnd Δ Φ Γ)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    den (consLit x ys) κ ρ = den (x :: ys) κ ρ := by
  unfold consLit
  split
  · rename_i l _
    split
    · rename_i hn
      rw [den_cons, l.2, hn, String.empty_append]
    · split
      · rename_i y ys'
        split
        · rename_i m _
          rw [den_cons, den_cons, den_cons, lit_val, l.2, m.2, String.append_assoc]
        · rfl
      · rfl
  · rfl

/-- The operands, with empty literals dropped and neighbouring literals merged. -/
def merge : List (Opnd Δ Φ Γ) → List (Opnd Δ Φ Γ)
  | [] => []
  | x :: xs => consLit x (merge xs)

theorem merge_den (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (ops : List (Opnd Δ Φ Γ)) → den (merge ops) κ ρ = den ops κ ρ
  | [] => rfl
  | x :: xs => by rw [merge, consLit_den, den_cons, den_cons, merge_den κ ρ xs]

/-- The string append of two operands, when one at least is open. -/
def mkApp (x r : Opnd Δ Φ Γ) : Option (Opnd Δ Φ Γ) :=
  match h : Lvl.meet x.1 r.1 with
  | some ℓ => some ⟨some ℓ, .neu (.extern (.stringDefsExtern .lean_string_append__String_append)
      (.cons x.2 (.cons r.2 .nil)) (by rw [Lvl.meet_none]; exact h))⟩
  | none => none

theorem mkApp_den (x r p : Opnd Δ Φ Γ) (h : mkApp x r = some p) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    val p.2 κ ρ = val x.2 κ ρ ++ val r.2 κ ρ := by
  unfold mkApp at h
  split at h
  · cases h; rfl
  · cases h

/-- `a ++ c₁ ++ … ++ cₙ`, grouped to the left. -/
def foldApp : Opnd Δ Φ Γ → List (Opnd Δ Φ Γ) → Option (Opnd Δ Φ Γ)
  | a, [] => some a
  | a, c :: cs =>
    match mkApp a c with
    | some a' => foldApp a' cs
    | none => none

theorem foldApp_den (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (a : Opnd Δ Φ Γ) → (cs : List (Opnd Δ Φ Γ)) → (p : Opnd Δ Φ Γ) → foldApp a cs = some p →
    val p.2 κ ρ = val a.2 κ ρ ++ den cs κ ρ
  | a, [], p, h => by
    simp only [foldApp, Option.some.injEq] at h; subst h; simp [String.append_empty]
  | a, c :: cs, p, h => by
    simp only [foldApp] at h
    split at h
    · rename_i a' ha
      rw [foldApp_den κ ρ a' cs p h, mkApp_den a c a' ha, den_cons, String.append_assoc]
    · cases h

/-- The operands appended from the left, `((x₁ ++ x₂) ++ …) ++ xₙ`. -/
def buildL : List (Opnd Δ Φ Γ) → Option (Opnd Δ Φ Γ)
  | [] => some (lit "")
  | a :: cs => foldApp a cs

theorem buildL_den (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (ops : List (Opnd Δ Φ Γ)) (p : Opnd Δ Φ Γ)
    (h : buildL ops = some p) : val p.2 κ ρ = den ops κ ρ := by
  cases ops with
  | nil => simp only [buildL, Option.some.injEq] at h; subst h; rfl
  | cons a cs => rw [foldApp_den κ ρ a cs p h, den_cons]

/-- How deep a string append chain is taken apart. -/
def flatFuel : Nat := 256

/-- **A string append chain regrouped** from the left, empty literals dropped and neighbouring
    literals merged, when the result is still a neutral expression of the same level
    (otherwise the expression is kept). -/
def normNeu {ℓ : Nat} (n : Neu Δ Φ Γ strTy ℓ) : Neu Δ Φ Γ strTy ℓ :=
  match buildL (merge (flat flatFuel (.neu n))) with
  | some ⟨o, p⟩ =>
    if h : o = some ℓ then
      match h ▸ p with
      | .neu m => m
      | _ => n
    else n
  | none => n

theorem normNeu_eval {ℓ : Nat} (n : Neu Δ Φ Γ strTy ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (normNeu n).eval κ ρ = n.eval κ ρ := by
  unfold normNeu
  split
  · rename_i o p hb
    split
    · rename_i h
      have e1 := buildL_den κ ρ _ _ hb
      rw [merge_den, flat_den] at e1
      subst h
      split
      · rename_i m hm
        have : val (PExpr.neu m) κ ρ = val (PExpr.neu n) κ ρ := by
          rw [← hm]; exact e1
        exact this
      · rfl
    · rfl
  · rfl

end StrApp
end LeanScript

end
