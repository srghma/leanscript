module

public import LeanScript.Term.Semantics.Eval
public import LeanScript.Term.Extern.Eval
public import LeanScript.Term.Optimize.Count

@[expose] public section

set_option autoImplicit false

/-!
# Append chains

`Term.appendWalk` regroups every chain of appends of arrays (`Array.append`, the extern
`lean_array_append`) and of lists (`List.append`, `lean_list_append`), drops the empty literals
of the chain and merges neighbouring literals into one.  Both are target-agnostic: appending is
associative, and a literal followed by a literal is one literal.

The grouping is the one each sequence type appends best with:

* **arrays from the left**, `((x₁ ++ x₂) ++ …) ++ xₙ`: `Array.append` pushes the elements of
  its second operand onto its first (in place when nothing else refers to it), so every operand
  after the first is copied once.  `#["a"] ++ (#["b"] ++ (arr ++ #["c"])) ++ #["d"]` is
  `((#["a", "b"] ++ arr) ++ #["c", "d"])`, which the JavaScript backend writes as the literal
  `["a", "b", ...arr, "c", "d"]`;
* **lists from the right**, `x₁ ++ (x₂ ++ (… ++ xₙ))`: `List.append` copies the cells of its
  first operand, so every operand but the last is copied once.

An append needs an open operand (`Neu.extern`), so closed operands before the first open one
(arrays), or after the last open one (lists), are grouped the other way around it.

The chain is read into its operands (`SeqKind.flat`), the operands merged (`SeqKind.merge`) and
appended again (`SeqKind.build`); the result replaces the chain when it is still a neutral
expression of the same level (`SeqKind.normNeu`), which is decided on the spot.  Proved: the
value is unchanged (`Term.appendWalk_eval`) and no call is added (`Term.numCalls_appendWalk`:
only pure expressions change).
-/

namespace LeanScript
variable {ks : List Nat} {Δ : DSig ks}

/-- The two sequence types whose appends are regrouped: arrays and lists. -/
inductive SeqKind where
  | array
  | list
  deriving DecidableEq, Repr

namespace SeqKind

/-- The sequence type of elements `t`. -/
def ty : SeqKind → Ty ks → Ty ks
  | .array, t => .array t
  | .list, t => .list t

/-- A value of the sequence type, as the list of its elements. -/
def toL : (k : SeqKind) → {t : Ty ks} → Ty.Den Δ (k.ty t) → List (Ty.Den Δ t)
  | .array, _, x => (x : Array _).toList
  | .list, _, x => (x : List _)

theorem toL_inj : (k : SeqKind) → {t : Ty ks} → {x y : Ty.Den Δ (k.ty t)} →
    k.toL (Δ := Δ) x = k.toL y → x = y
  | .array, _, _, _, h => Array.toList_inj.mp h
  | .list, _, _, _, h => h

variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The two operands of an append, with the fact that the append is their concatenation. -/
structure Split (k : SeqKind) {t : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ (k.ty t) o) where
  o₁ : Lvl
  o₂ : Lvl
  a : PExpr Δ Φ Γ (k.ty t) o₁
  b : PExpr Δ Φ Γ (k.ty t) o₂
  eval : ∀ κ ρ, k.toL (e.eval κ ρ) = k.toL (a.eval κ ρ) ++ k.toL (b.eval κ ρ)

/-- The operands of an append, when a pure expression is one. -/
def view : (k : SeqKind) → {t : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ (k.ty t) o) →
    Option (k.Split e)
  | .array, _, _,
      .neu (.extern (.arrayStdExtern (.lean_array_append _)) (.cons a (.cons b .nil)) _) =>
      some ⟨_, _, a, b, fun _ _ => by
        simp only [PExpr.eval, Neu.eval, Args.eval, Extern.eval, ArrayStdExtern.eval, toL]
        exact Array.toList_append⟩
  | .array, _, _, _ => none
  | .list, _, _,
      .neu (.extern (.arrayStdExtern (.lean_list_append _)) (.cons a (.cons b .nil)) _) =>
      some ⟨_, _, a, b, fun _ _ => rfl⟩
  | .list, _, _, _ => none

/-- The elements of a literal, with the fact that the literal is its elements. -/
structure Lit (k : SeqKind) {t : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ (k.ty t) o) where
  o' : Lvl
  es : Elems Δ Φ Γ t o'
  eval : ∀ κ ρ, k.toL (e.eval κ ρ) = es.eval κ ρ

/-- The elements of a literal, when a pure expression is one. -/
def litView : (k : SeqKind) → {t : Ty ks} → {o : Lvl} → (e : PExpr Δ Φ Γ (k.ty t) o) →
    Option (k.Lit e)
  | .array, _, _, .array_mk es => some ⟨_, es, fun _ _ => by simp [PExpr.eval, toL]⟩
  | .array, _, _, _ => none
  | .list, _, _, .list_mk es => some ⟨_, es, fun _ _ => rfl⟩
  | .list, _, _, _ => none

/-- The literal of the sequence type. -/
def lit : (k : SeqKind) → {t : Ty ks} → {o : Lvl} → Elems Δ Φ Γ t o → PExpr Δ Φ Γ (k.ty t) o
  | .array, _, _, es => .array_mk es
  | .list, _, _, es => .list_mk es

theorem lit_eval : (k : SeqKind) → {t : Ty ks} → {o : Lvl} → (es : Elems Δ Φ Γ t o) →
    (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → k.toL ((k.lit es).eval κ ρ) = es.eval κ ρ
  | .array, _, _, _, _, _ => by simp [SeqKind.lit, PExpr.eval, SeqKind.toL]
  | .list, _, _, _, _, _ => rfl

/-- The append of the sequence type, on two operands of which one at least is open. -/
def app : (k : SeqKind) → {t : Ty ks} → {o₁ o₂ : Lvl} → {ℓ : Nat} →
    PExpr Δ Φ Γ (k.ty t) o₁ → PExpr Δ Φ Γ (k.ty t) o₂ → Lvl.meet o₁ o₂ = some ℓ →
    PExpr Δ Φ Γ (k.ty t) (some ℓ)
  | .array, t, _, _, _, a, b, h =>
      .neu (.extern (.arrayStdExtern (.lean_array_append t)) (.cons a (.cons b .nil))
        (by rw [Lvl.meet_none]; exact h))
  | .list, t, _, _, _, a, b, h =>
      .neu (.extern (.arrayStdExtern (.lean_list_append t)) (.cons a (.cons b .nil))
        (by rw [Lvl.meet_none]; exact h))

theorem app_eval : (k : SeqKind) → {t : Ty ks} → {o₁ o₂ : Lvl} → {ℓ : Nat} →
    (a : PExpr Δ Φ Γ (k.ty t) o₁) → (b : PExpr Δ Φ Γ (k.ty t) o₂) →
    (h : Lvl.meet o₁ o₂ = some ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    k.toL ((k.app a b h).eval κ ρ) = k.toL (a.eval κ ρ) ++ k.toL (b.eval κ ρ)
  | .array, _, _, _, _, _, _, _, _, _ => by
      simp only [SeqKind.app, PExpr.eval, Neu.eval, Args.eval, Extern.eval, ArrayStdExtern.eval,
        toL]
      exact Array.toList_append
  | .list, _, _, _, _, _, _, _, _, _ => rfl



/-- An operand of an append chain: a pure expression of the sequence type, at any level. -/
abbrev Opnd (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) (k : SeqKind) (t : Ty ks) : Type :=
  Σ o : Lvl, PExpr Δ Φ Γ (k.ty t) o

/-- The elements of operands, one operand after the other. -/
def den (k : SeqKind) {t : Ty ks} (ops : List (Opnd Δ Φ Γ k t)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    List (Ty.Den Δ t) :=
  ops.flatMap fun p => k.toL (p.2.eval κ ρ)

@[simp] theorem den_nil (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    den k ([] : List (Opnd Δ Φ Γ k t)) κ ρ = [] := rfl

@[simp] theorem den_cons (k : SeqKind) {t : Ty ks} (p : Opnd Δ Φ Γ k t)
    (ops : List (Opnd Δ Φ Γ k t)) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    den k (p :: ops) κ ρ = k.toL (p.2.eval κ ρ) ++ den k ops κ ρ := rfl

@[simp] theorem den_append (k : SeqKind) {t : Ty ks} (ops ops' : List (Opnd Δ Φ Γ k t))
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : den k (ops ++ ops') κ ρ = den k ops κ ρ ++ den k ops' κ ρ := by
  simp [den]

/-- The operands of an append chain, however it is grouped (at most `n` levels deep). -/
def flat (k : SeqKind) {t : Ty ks} : Nat → {o : Lvl} → PExpr Δ Φ Γ (k.ty t) o →
    List (Opnd Δ Φ Γ k t)
  | 0, _, e => [⟨_, e⟩]
  | n + 1, _, e =>
    match k.view e with
    | some s => flat k n s.a ++ flat k n s.b
    | none => [⟨_, e⟩]

theorem flat_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (n : Nat) → {o : Lvl} → (e : PExpr Δ Φ Γ (k.ty t) o) →
    den k (flat k n e) κ ρ = k.toL (e.eval κ ρ)
  | 0, _, _ => by simp [flat]
  | n + 1, _, e => by
    unfold flat
    split
    · rename_i s _
      rw [den_append, flat_den k κ ρ n, flat_den k κ ρ n, s.eval]
    · simp

/-- Whether the elements of a literal are none. -/
def _root_.LeanScript.Elems.isNil {t : Ty ks} {o : Lvl} : Elems Δ Φ Γ t o → Bool
  | .nil => true
  | .cons _ _ => false

theorem _root_.LeanScript.Elems.isNil_eval {t : Ty ks} {o : Lvl} (es : Elems Δ Φ Γ t o)
    (h : es.isNil = true) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : es.eval κ ρ = [] := by
  cases es with
  | nil => rfl
  | cons _ _ => simp [Elems.isNil] at h

/-- The elements of two literals, one after the other. -/
def _root_.LeanScript.Elems.append {t : Ty ks} : {o₁ o₂ : Lvl} → Elems Δ Φ Γ t o₁ →
    Elems Δ Φ Γ t o₂ → Σ o, Elems Δ Φ Γ t o
  | _, _, .nil, fs => ⟨_, fs⟩
  | _, _, .cons e es, fs => ⟨_, .cons e (Elems.append es fs).2⟩

theorem _root_.LeanScript.Elems.append_eval {t : Ty ks} : {o₁ o₂ : Lvl} →
    (es : Elems Δ Φ Γ t o₁) → (fs : Elems Δ Φ Γ t o₂) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (Elems.append es fs).2.eval κ ρ = es.eval κ ρ ++ fs.eval κ ρ
  | _, _, .nil, _, _, _ => by simp [Elems.append, Elems.eval]
  | _, _, .cons e es, fs, κ, ρ => by
      simp [Elems.append, Elems.eval, Elems.append_eval es fs κ ρ]

/-- An operand in front of operands: an empty literal is dropped, and two literals next to
    each other become one. -/
def consLit (k : SeqKind) {t : Ty ks} (x : Opnd Δ Φ Γ k t) (ys : List (Opnd Δ Φ Γ k t)) :
    List (Opnd Δ Φ Γ k t) :=
  match k.litView x.2 with
  | some l =>
    if l.es.isNil then ys
    else
      match ys with
      | y :: ys' =>
        match k.litView y.2 with
        | some m => ⟨_, k.lit (Elems.append l.es m.es).2⟩ :: ys'
        | none => x :: ys
      | [] => [x]
  | none => x :: ys

theorem consLit_den (k : SeqKind) {t : Ty ks} (x : Opnd Δ Φ Γ k t) (ys : List (Opnd Δ Φ Γ k t))
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : den k (consLit k x ys) κ ρ = den k (x :: ys) κ ρ := by
  unfold consLit
  split
  · rename_i l _
    split
    · rename_i hn
      rw [den_cons, l.eval, Elems.isNil_eval _ hn]; rfl
    · split
      · rename_i y ys'
        split
        · rename_i m _
          rw [den_cons, den_cons, den_cons, lit_eval, Elems.append_eval, ← l.eval, ← m.eval,
            List.append_assoc]
        · rfl
      · rfl
  · rfl

/-- The operands, with empty literals dropped and neighbouring literals merged. -/
def merge (k : SeqKind) {t : Ty ks} : List (Opnd Δ Φ Γ k t) → List (Opnd Δ Φ Γ k t)
  | [] => []
  | x :: xs => consLit k x (merge k xs)

theorem merge_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (ops : List (Opnd Δ Φ Γ k t)) → den k (merge k ops) κ ρ = den k ops κ ρ
  | [] => rfl
  | x :: xs => by rw [merge, consLit_den, den_cons, den_cons, merge_den k κ ρ xs]

/-- The append of two operands, when one at least is open. -/
def mkApp (k : SeqKind) {t : Ty ks} (x r : Opnd Δ Φ Γ k t) : Option (Opnd Δ Φ Γ k t) :=
  match h : Lvl.meet x.1 r.1 with
  | some ℓ => some ⟨some ℓ, k.app x.2 r.2 h⟩
  | none => none

theorem mkApp_den (k : SeqKind) {t : Ty ks} (x r p : Opnd Δ Φ Γ k t)
    (h : mkApp k x r = some p) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    k.toL (p.2.eval κ ρ) = k.toL (x.2.eval κ ρ) ++ k.toL (r.2.eval κ ρ) := by
  unfold mkApp at h
  split at h
  · cases h; exact app_eval k _ _ _ κ ρ
  · cases h

/-- `a ++ c₁ ++ … ++ cₙ`, grouped to the left (`a` is open, so every append is). -/
def foldApp (k : SeqKind) {t : Ty ks} : Opnd Δ Φ Γ k t → List (Opnd Δ Φ Γ k t) →
    Option (Opnd Δ Φ Γ k t)
  | a, [] => some a
  | a, c :: cs =>
    match mkApp k a c with
    | some a' => foldApp k a' cs
    | none => none

theorem foldApp_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (a : Opnd Δ Φ Γ k t) → (cs : List (Opnd Δ Φ Γ k t)) → (p : Opnd Δ Φ Γ k t) →
    foldApp k a cs = some p → k.toL (p.2.eval κ ρ) = den k (a :: cs) κ ρ
  | a, [], p, h => by
      simp only [foldApp, Option.some.injEq] at h; subst h; simp
  | a, c :: cs, p, h => by
      simp only [foldApp] at h
      split at h
      · rename_i a' ha
        rw [foldApp_den k κ ρ a' cs p h, den_cons, mkApp_den k a c a' ha, den_cons, den_cons,
          List.append_assoc]
      · cases h

/-- The operands appended so far, from the right: an open expression, or closed operands
    not appended yet (a closed append cannot be written). -/
inductive Built (Δ : DSig ks) (Φ : KCtx ks) (Γ : UCtx ks) (k : SeqKind) (t : Ty ks) where
  | opn : Opnd Δ Φ Γ k t → Built Δ Φ Γ k t
  | cls : List (Opnd Δ Φ Γ k t) → Built Δ Φ Γ k t

/-- The elements of what is built. -/
def Built.den {k : SeqKind} {t : Ty ks} : Built Δ Φ Γ k t → KEnv Δ Φ → UEnv Δ Γ →
    List (Ty.Den Δ t)
  | .opn p, κ, ρ => k.toL (p.2.eval κ ρ)
  | .cls cs, κ, ρ => SeqKind.den k cs κ ρ

/-- One more operand in front: `x ++ r` when `r` is open; when the operands so far are all
    closed, they are kept aside until an open operand comes, which they are appended to from
    the left (`(y ++ c₁) ++ c₂`). -/
def step (k : SeqKind) {t : Ty ks} (x : Opnd Δ Φ Γ k t) :
    Option (Built Δ Φ Γ k t) → Option (Built Δ Φ Γ k t)
  | some (.opn r) => (mkApp k x r).map .opn
  | some (.cls cs) =>
    if x.1.isSome then (foldApp k x cs).map .opn else some (.cls (x :: cs))
  | none => none

theorem step_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (x : Opnd Δ Φ Γ k t) (acc : Option (Built Δ Φ Γ k t)) (b b' : Built Δ Φ Γ k t)
    (hacc : acc = some b) (h : step k x acc = some b') :
    b'.den κ ρ = k.toL (x.2.eval κ ρ) ++ b.den κ ρ := by
  subst hacc
  cases b with
  | opn r =>
    simp only [step] at h
    cases hm : mkApp k x r with
    | none => rw [hm] at h; cases h
    | some p =>
      rw [hm] at h; cases h
      exact mkApp_den k x r p hm κ ρ
  | cls cs =>
    simp only [step] at h
    split at h
    · cases hf : foldApp k x cs with
      | none => rw [hf] at h; cases h
      | some p =>
        rw [hf] at h; cases h
        exact foldApp_den k κ ρ x cs p hf
    · cases h; rfl

theorem foldr_step_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (ops : List (Opnd Δ Φ Γ k t)) → (b : Built Δ Φ Γ k t) →
    ops.foldr (step k) (some (.cls [])) = some b → b.den κ ρ = den k ops κ ρ
  | [], b, h => by simp only [List.foldr_nil, Option.some.injEq] at h; subst h; rfl
  | x :: xs, b, h => by
      simp only [List.foldr_cons] at h
      cases hr : xs.foldr (step k) (some (.cls [])) with
      | none => rw [hr] at h; simp [step] at h
      | some r =>
        rw [step_den k κ ρ x _ r b hr h, foldr_step_den k κ ρ xs r hr, den_cons]

/-- The operands, appended from the right, `x₁ ++ (x₂ ++ (… ++ xₙ))`, except that closed
    operands after the last open one are appended to it from the left. -/
def buildR (k : SeqKind) {t : Ty ks} (ops : List (Opnd Δ Φ Γ k t)) : Option (Opnd Δ Φ Γ k t) :=
  match ops.foldr (step k) (some (.cls [])) with
  | some (.opn p) => some p
  | some (.cls []) => some ⟨none, k.lit .nil⟩
  | some (.cls [x]) => some x
  | _ => none

theorem buildR_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (ops : List (Opnd Δ Φ Γ k t)) (p : Opnd Δ Φ Γ k t) (h : buildR k ops = some p) :
    k.toL (p.2.eval κ ρ) = den k ops κ ρ := by
  unfold buildR at h
  split at h
  · rename_i p' hb; cases h
    exact foldr_step_den k κ ρ ops _ hb
  · rename_i hb; cases h
    rw [← foldr_step_den k κ ρ ops _ hb, lit_eval]; rfl
  · rename_i x hb; cases h
    rw [← foldr_step_den k κ ρ ops _ hb]; simp [Built.den]
  · cases h

/-- `c₁ ++ (c₂ ++ (… ++ a))`, grouped to the right (`a` is open, so every append is). -/
def foldAppR (k : SeqKind) {t : Ty ks} : List (Opnd Δ Φ Γ k t) → Opnd Δ Φ Γ k t →
    Option (Opnd Δ Φ Γ k t)
  | [], a => some a
  | c :: cs, a =>
    match foldAppR k cs a with
    | some r => mkApp k c r
    | none => none

theorem foldAppR_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (cs : List (Opnd Δ Φ Γ k t)) → (a : Opnd Δ Φ Γ k t) → (p : Opnd Δ Φ Γ k t) →
    foldAppR k cs a = some p → k.toL (p.2.eval κ ρ) = den k (cs ++ [a]) κ ρ
  | [], a, p, h => by
      simp only [foldAppR, Option.some.injEq] at h; subst h; simp
  | c :: cs, a, p, h => by
      simp only [foldAppR] at h
      split at h
      · rename_i r hr
        rw [mkApp_den k c r p h, foldAppR_den k κ ρ cs a r hr]; rfl
      · cases h

/-- One more operand at the end: `r ++ x` when `r` is open; when the operands so far are all
    closed, they are kept aside until an open operand comes, which they are put in front of
    from the right (`c₁ ++ (c₂ ++ y)`). -/
def stepL (k : SeqKind) {t : Ty ks} :
    Option (Built Δ Φ Γ k t) → Opnd Δ Φ Γ k t → Option (Built Δ Φ Γ k t)
  | some (.opn r), x => (mkApp k r x).map .opn
  | some (.cls cs), x =>
    if x.1.isSome then (foldAppR k cs x).map .opn else some (.cls (cs ++ [x]))
  | none, _ => none

theorem stepL_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (x : Opnd Δ Φ Γ k t) (b b' : Built Δ Φ Γ k t) (h : stepL k (some b) x = some b') :
    b'.den κ ρ = b.den κ ρ ++ k.toL (x.2.eval κ ρ) := by
  cases b with
  | opn r =>
    simp only [stepL] at h
    cases hm : mkApp k r x with
    | none => rw [hm] at h; cases h
    | some p =>
      rw [hm] at h; cases h
      exact mkApp_den k r x p hm κ ρ
  | cls cs =>
    simp only [stepL] at h
    split at h
    · cases hf : foldAppR k cs x with
      | none => rw [hf] at h; cases h
      | some p =>
        rw [hf] at h; cases h
        rw [Built.den, foldAppR_den k κ ρ cs x p hf, den_append]; simp [Built.den]
    · cases h; simp [Built.den]

theorem foldl_stepL_none (k : SeqKind) {t : Ty ks} :
    (ops : List (Opnd Δ Φ Γ k t)) → ops.foldl (stepL k) none = none
  | [] => rfl
  | _ :: xs => by simp only [List.foldl_cons, stepL]; exact foldl_stepL_none k xs

theorem foldl_stepL_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (ops : List (Opnd Δ Φ Γ k t)) → (b₀ b : Built Δ Φ Γ k t) →
    ops.foldl (stepL k) (some b₀) = some b → b.den κ ρ = b₀.den κ ρ ++ den k ops κ ρ
  | [], b₀, b, h => by simp only [List.foldl_nil, Option.some.injEq] at h; subst h; simp
  | x :: xs, b₀, b, h => by
      simp only [List.foldl_cons] at h
      cases hs : stepL k (some b₀) x with
      | none => rw [hs, foldl_stepL_none] at h; cases h
      | some b₁ =>
        rw [hs] at h
        rw [foldl_stepL_den k κ ρ xs b₁ b h, stepL_den k κ ρ x b₀ b₁ hs, den_cons,
          List.append_assoc]

/-- The operands, appended from the left, `((x₁ ++ x₂) ++ …) ++ xₙ`, except that closed
    operands before the first open one are put in front of it from the right. -/
def buildL (k : SeqKind) {t : Ty ks} (ops : List (Opnd Δ Φ Γ k t)) : Option (Opnd Δ Φ Γ k t) :=
  match ops.foldl (stepL k) (some (.cls [])) with
  | some (.opn p) => some p
  | some (.cls []) => some ⟨none, k.lit .nil⟩
  | some (.cls [x]) => some x
  | _ => none

theorem buildL_den (k : SeqKind) {t : Ty ks} (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (ops : List (Opnd Δ Φ Γ k t)) (p : Opnd Δ Φ Γ k t) (h : buildL k ops = some p) :
    k.toL (p.2.eval κ ρ) = den k ops κ ρ := by
  unfold buildL at h
  split at h
  · rename_i p' hb; cases h
    have := foldl_stepL_den k κ ρ ops _ _ hb
    simpa [Built.den] using this
  · rename_i hb; cases h
    have := foldl_stepL_den k κ ρ ops _ _ hb
    simp only [Built.den, den_nil, List.nil_append] at this
    rw [← this, lit_eval]; rfl
  · rename_i x hb; cases h
    have := foldl_stepL_den k κ ρ ops _ _ hb
    simp only [Built.den, den_nil, List.nil_append] at this
    rw [← this]; simp
  · cases h

/-- The operands appended again, the way the sequence type appends best: arrays from the
    left (`Array.append` pushes the elements of its second operand onto its first, in place when
    nothing else refers to it, so `(a ++ b) ++ c` copies `b` and `c` once, into `a`), lists from
    the right (`List.append` copies the cells of its first operand, so `a ++ (b ++ c)` copies
    those of `a` and `b` once). -/
def build : (k : SeqKind) → {t : Ty ks} → List (Opnd Δ Φ Γ k t) → Option (Opnd Δ Φ Γ k t)
  | .array, _, ops => buildL .array ops
  | .list, _, ops => buildR .list ops

theorem build_den : (k : SeqKind) → {t : Ty ks} → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (ops : List (Opnd Δ Φ Γ k t)) → (p : Opnd Δ Φ Γ k t) → build k ops = some p →
    k.toL (p.2.eval κ ρ) = den k ops κ ρ
  | .array, _, κ, ρ, ops, p, h => buildL_den .array κ ρ ops p h
  | .list, _, κ, ρ, ops, p, h => buildR_den .list κ ρ ops p h

end SeqKind

/-- The neutral expression a pure expression is, with the fact that they have the same value. -/
def PExpr.asNeu? {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    (e : PExpr Δ Φ Γ τ (some ℓ)) →
    Option {n : Neu Δ Φ Γ τ ℓ // ∀ κ ρ, n.eval κ ρ = e.eval κ ρ}
  | _, _, .neu n => some ⟨n, fun _ _ => rfl⟩
  | _, _, _ => none

namespace SeqKind
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- How deep an append chain is taken apart. -/
def flatFuel : Nat := 256

/-- **An append chain regrouped** (`SeqKind.build`), empty literals dropped and
    neighbouring literals merged, when the result is still a neutral expression of the same
    level (otherwise the expression is kept). -/
def normNeu (k : SeqKind) {t : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ (k.ty t) ℓ) :
    Neu Δ Φ Γ (k.ty t) ℓ :=
  match build k (merge k (flat k flatFuel (.neu n))) with
  | some ⟨o, p⟩ =>
    if h : o = some ℓ then
      match PExpr.asNeu? (h ▸ p) with
      | some m => m.1
      | none => n
    else n
  | none => n

theorem normNeu_eval (k : SeqKind) {t : Ty ks} {ℓ : Nat} (n : Neu Δ Φ Γ (k.ty t) ℓ)
    (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : (k.normNeu n).eval κ ρ = n.eval κ ρ := by
  unfold normNeu
  split
  · rename_i o p hb
    split
    · rename_i h
      split
      · rename_i m _
        apply k.toL_inj
        rw [m.2]
        have e1 := build_den k κ ρ _ _ hb
        rw [merge_den, flat_den] at e1
        subst h
        exact e1
      · rfl
    · rfl
  · rfl

end SeqKind

/-- `SeqKind.normNeu` on a neutral expression of an array or list type. -/
def Neu.normAppend {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | .array t, _, n => SeqKind.normNeu .array (t := t) n
  | .list t, _, n => SeqKind.normNeu .list (t := t) n
  | _, _, n => n

theorem Neu.normAppend_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    n.normAppend.eval κ ρ = n.eval κ ρ := by
  cases τ with
  | array t => exact SeqKind.normNeu_eval .array (t := t) n κ ρ
  | list t => exact SeqKind.normNeu_eval .list (t := t) n κ ρ
  | _ => rfl

/-! ## The walk -/

mutual
/-- `Neu.normAppend` at every extern call of a neutral expression, bottom-up. -/
def Neu.appendWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    Neu Δ Φ Γ τ ℓ → Neu Δ Φ Γ τ ℓ
  | _, _, .var x => .var x
  | _, _, .data_out b j e => .data_out b j e.appendWalk
  | _, _, .cond c a b => .cond c.appendWalk a.appendWalk b.appendWalk
  | _, _, .extern e args h => Neu.normAppend (.extern e args.appendWalk h)
/-- `Neu.appendWalk` in a pure expression. -/
def PExpr.appendWalk {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → PExpr Δ Φ Γ τ o
  | _, _, .neu n => .neu n.appendWalk
  | _, _, .kvar k => .kvar k
  | _, _, .lit p v => .lit p v
  | _, _, .enum_mk s i => .enum_mk s i
  | _, _, .record_mk args => .record_mk args.appendWalk
  | _, _, .union_mk ix args => .union_mk ix args.appendWalk
  | _, _, .array_mk es => .array_mk es.appendWalk
  | _, _, .list_mk es => .list_mk es.appendWalk
  | _, _, .data_in b j e => .data_in b j e.appendWalk
/-- `Neu.appendWalk` in arguments. -/
def Args.appendWalk {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    Args Δ Φ Γ σs o → Args Δ Φ Γ σs o
  | _, _, .nil => .nil
  | _, _, .cons a as => .cons a.appendWalk as.appendWalk
/-- `Neu.appendWalk` in the elements of a literal. -/
def Elems.appendWalk {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    Elems Δ Φ Γ t o → Elems Δ Φ Γ t o
  | _, _, .nil => .nil
  | _, _, .cons e es => .cons e.appendWalk es.appendWalk
end

mutual
theorem Neu.appendWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    (n : Neu Δ Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → n.appendWalk.eval κ ρ = n.eval κ ρ
  | _, _, .var _, _, _ => rfl
  | _, _, .data_out b j e, κ, ρ => by
      simp only [Neu.appendWalk, Neu.eval, Neu.appendWalk_eval e]
  | _, _, .cond c a b, κ, ρ => by
      simp only [Neu.appendWalk, Neu.eval, Neu.appendWalk_eval c, PExpr.appendWalk_eval a,
        PExpr.appendWalk_eval b]
  | _, _, .extern e args _, κ, ρ => by
      simp only [Neu.appendWalk]
      rw [Neu.normAppend_eval]
      simp only [Neu.eval, Args.appendWalk_eval args]
theorem PExpr.appendWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    (e : PExpr Δ Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → e.appendWalk.eval κ ρ = e.eval κ ρ
  | _, _, .neu n, κ, ρ => by simp only [PExpr.appendWalk, PExpr.eval, Neu.appendWalk_eval n]
  | _, _, .kvar _, _, _ => rfl
  | _, _, .lit _ _, _, _ => rfl
  | _, _, .enum_mk _ _, _, _ => rfl
  | _, _, .record_mk args, κ, ρ => by
      simp only [PExpr.appendWalk, PExpr.eval, Args.appendWalk_eval args] <;> rfl
  | _, _, .union_mk _ args, κ, ρ => by
      simp only [PExpr.appendWalk, PExpr.eval, Args.appendWalk_eval args] <;> rfl
  | _, _, .array_mk es, κ, ρ => by
      simp only [PExpr.appendWalk, PExpr.eval, Elems.appendWalk_eval es] <;> rfl
  | _, _, .list_mk es, κ, ρ => by
      simp only [PExpr.appendWalk, PExpr.eval, Elems.appendWalk_eval es] <;> rfl
  | _, _, .data_in _ _ e, κ, ρ => by
      simp only [PExpr.appendWalk, PExpr.eval, PExpr.appendWalk_eval e]
theorem Args.appendWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {σs : List (Ty ks)} → {o : Lvl} →
    (as : Args Δ Φ Γ σs o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → as.appendWalk.eval κ ρ = as.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons a as, κ, ρ => by
      simp only [Args.appendWalk, Args.eval, PExpr.appendWalk_eval a, Args.appendWalk_eval as]
theorem Elems.appendWalk_eval {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    (es : Elems Δ Φ Γ t o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → es.appendWalk.eval κ ρ = es.eval κ ρ
  | _, _, .nil, _, _ => rfl
  | _, _, .cons e es, κ, ρ => by
      simp only [Elems.appendWalk, Elems.eval, PExpr.appendWalk_eval e, Elems.appendWalk_eval es] <;> rfl
end

mutual
/-- `Term.appendWalk` in a value. -/
def Val.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Val Δ d Φ Γ τ o → Val Δ d Φ Γ τ o
  | _, _, _, _, _, .lam b => .lam b.appendWalk
  | _, _, _, _, _, .thunk_mk b => .thunk_mk b.appendWalk
  | _, _, _, _, _, .lazy_mk b => .lazy_mk b.appendWalk
  | _, _, _, _, _, .record_mk args => .record_mk args.appendWalk
  | _, _, _, _, _, .union_mk ix args => .union_mk ix args.appendWalk
  | _, _, _, _, _, .array_mk es => .array_mk es.appendWalk
  | _, _, _, _, _, .list_mk es => .list_mk es.appendWalk
  | _, _, _, _, _, .data_in b j e => .data_in b j e.appendWalk
/-- `Term.appendWalk` in a body. -/
def Body.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} → {o : Lvl} →
    Body Δ d Φ Γ bs τ o → Body Δ d Φ Γ bs τ o
  | _, _, _, _, _, _, .closed t => .closed t.appendWalk
  | _, _, _, _, _, _, .opened t h => .opened t.appendWalk h
/-- `Term.appendWalk` in a computation. -/
def Comp.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {ℓ : Nat} →
    Comp Δ d Φ Γ τ ℓ → Comp Δ d Φ Γ τ ℓ
  | _, _, _, _, _, .app f a h => .app f.appendWalk a.appendWalk h
  | _, _, _, _, _, .share n => .share n.appendWalk
  | _, _, _, _, _, .nat_rec n z s h => .nat_rec n.appendWalk z.appendWalk s.appendWalk h
  | _, _, _, _, _, .array_foldl a z s h => .array_foldl a.appendWalk z.appendWalk s.appendWalk h
  | _, _, _, _, _, .data_rec b ρ us brs j e h =>
      .data_rec b ρ us (fun i => (brs i).appendWalk) j e.appendWalk h
  | _, _, _, _, _, .data_brec b ρ k us brs j e h =>
      .data_brec b ρ k us (fun i => (brs i).appendWalk) j e.appendWalk h
  | _, _, _, _, _, .thunk_force e => .thunk_force e.appendWalk
  | _, _, _, _, _, .lazy_force e => .lazy_force e.appendWalk
/-- **Append chains regrouped** everywhere in a statement (`Neu.normAppend`), bottom-up. -/
def Term.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {o : Lvl} → Term Δ d Φ Γ τ js o → Term Δ d Φ Γ τ js o
  | _, _, _, _, _, _, .ret e => .ret e.appendWalk
  | _, _, _, _, _, _, .letV u v b => .letV u v.appendWalk b.appendWalk
  | _, _, _, _, _, _, .letE u c b => .letE u c.appendWalk b.appendWalk
  | _, _, _, _, _, _, .record_casesOn us n b => .record_casesOn us n.appendWalk b.appendWalk
  | _, _, _, _, _, _, .branch br => .branch br.appendWalk
  | _, _, _, _, _, _, .jump j e => .jump j e.appendWalk
/-- `Term.appendWalk` in a branch. -/
def Branch.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} → {js : JCtx ks} →
    {ℓ : Nat} → Branch Δ d Φ Γ τ js ℓ → Branch Δ d Φ Γ τ js ℓ
  | _, _, _, _, _, _, .ite c t e => .ite c.appendWalk t.appendWalk e.appendWalk
  | _, _, _, _, _, _, .enum_casesOn e bs => .enum_casesOn e.appendWalk (fun i => (bs i).appendWalk)
  | _, _, _, _, _, _, .union_casesOn e bs => .union_casesOn e.appendWalk bs.appendWalk
  | _, _, _, _, _, _, .join σ u uₓ body main => .join σ u uₓ body.appendWalk main.appendWalk
/-- `Term.appendWalk` in the branches of a union's case analysis. -/
def Branches.appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    Branches Δ d Φ Γ cs τ js o → Branches Δ d Φ Γ cs τ js o
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂ => .two us₁ us₂ b₁.appendWalk b₂.appendWalk
  | _, _, _, _, _, _, _, _, .cons us b bs => .cons us b.appendWalk bs.appendWalk
end

mutual
theorem Val.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    v.appendWalk.eval κ ρ = v.eval κ ρ
  | _, _, _, _, _, .lam b, κ, ρ => by
      simp only [Val.appendWalk, Val.eval]; funext x; rw [Body.appendWalk_eval b κ ρ]
  | _, _, _, _, _, .thunk_mk b, κ, ρ => by
      simp only [Val.appendWalk, Val.eval]; rw [Body.appendWalk_eval b κ ρ]
  | _, _, _, _, _, .lazy_mk b, κ, ρ => by
      simp only [Val.appendWalk, Val.eval]; rw [Body.appendWalk_eval b κ ρ]
  | _, _, _, _, _, .record_mk args, κ, ρ => by
      simp only [Val.appendWalk, Val.eval, Args.appendWalk_eval args] <;> rfl
  | _, _, _, _, _, .union_mk _ args, κ, ρ => by
      simp only [Val.appendWalk, Val.eval, Args.appendWalk_eval args] <;> rfl
  | _, _, _, _, _, .array_mk es, κ, ρ => by
      simp only [Val.appendWalk, Val.eval, Elems.appendWalk_eval es] <;> rfl
  | _, _, _, _, _, .list_mk es, κ, ρ => by
      simp only [Val.appendWalk, Val.eval, Elems.appendWalk_eval es] <;> rfl
  | _, _, _, _, _, .data_in _ _ e, κ, ρ => by
      simp only [Val.appendWalk, Val.eval, PExpr.appendWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Body.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    (vs : UEnv Δ bs) → b.appendWalk.eval κ ρ vs = b.eval κ ρ vs
  | _, _, _, _, _, _, .closed t, _, _, _ => by
      simp only [Body.appendWalk, Body.eval]; exact Term.appendWalk_eval t _ _ _
  | _, _, _, _, _, _, .opened t _, _, _, _ => by
      simp only [Body.appendWalk, Body.eval]; exact Term.appendWalk_eval t _ _ _
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Comp.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) →
    c.appendWalk.eval κ ρ = c.eval κ ρ
  | _, _, _, _, _, .app f a _, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval f, PExpr.appendWalk_eval a]
  | _, _, _, _, _, .share n, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, Neu.appendWalk_eval n]
  | _, _, _, _, _, .nat_rec n z s _, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval n, PExpr.appendWalk_eval z]
      congr 1; funext k acc; exact Body.appendWalk_eval s κ ρ _
  | _, _, _, _, _, .array_foldl a z s _, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval]
      rw [PExpr.appendWalk_eval a κ ρ, PExpr.appendWalk_eval z κ ρ]
      congr 1; funext acc x; exact Body.appendWalk_eval s κ ρ _
  | _, _, _, _, _, .data_rec b ρt us brs j e _, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval e]
      congr 1; funext i x; exact Body.appendWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .data_brec b ρt k us brs j e _, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval e]
      congr 1; funext i x; exact Body.appendWalk_eval (brs i) κ ρ _
  | _, _, _, _, _, .thunk_force e, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval e]
  | _, _, _, _, _, .lazy_force e, κ, ρ => by
      simp only [Comp.appendWalk, Comp.eval, PExpr.appendWalk_eval e]
  termination_by structural _ _ _ _ _ x _ _ => x
theorem Term.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → t.appendWalk.eval κ ρ jκ = t.eval κ ρ jκ
  | _, _, _, _, _, _, .ret e, κ, ρ, _ => by
      simp only [Term.appendWalk, Term.eval, PExpr.appendWalk_eval e]
  | _, _, _, _, _, _, .letV u v b, κ, ρ, jκ => by
      simp only [Term.appendWalk, Term.eval, Val.appendWalk_eval v, Term.appendWalk_eval b]
  | _, _, _, _, _, _, .letE u c b, κ, ρ, jκ => by
      simp only [Term.appendWalk, Term.eval, Comp.appendWalk_eval c, Term.appendWalk_eval b]
  | _, _, _, _, _, _, .record_casesOn us n b, κ, ρ, jκ => by
      simp only [Term.appendWalk, Term.eval, Neu.appendWalk_eval n, Term.appendWalk_eval b]
  | _, _, _, _, _, _, .branch br, κ, ρ, jκ => by
      simp only [Term.appendWalk, Term.eval, Branch.appendWalk_eval br]
  | _, _, _, _, _, _, .jump _ e, κ, ρ, jκ => by
      simp only [Term.appendWalk, Term.eval, PExpr.appendWalk_eval e]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branch.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) → br.appendWalk.eval κ ρ jκ = br.eval κ ρ jκ
  | _, _, _, _, _, _, .ite c t e, κ, ρ, jκ => by
      simp only [Branch.appendWalk, Branch.eval, Neu.appendWalk_eval c, Term.appendWalk_eval t,
        Term.appendWalk_eval e]
  | _, _, _, _, _, _, .enum_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.appendWalk, Branch.eval]; rw [Neu.appendWalk_eval e]
      exact Term.appendWalk_eval _ _ _ _
  | _, _, _, _, _, _, .union_casesOn e bs, κ, ρ, jκ => by
      simp only [Branch.appendWalk, Branch.eval, Neu.appendWalk_eval e]
      exact Branches.appendWalk_eval bs κ ρ jκ _
  | _, _, _, _, _, _, .join σ u uₓ body main, κ, ρ, jκ => by
      simp only [Branch.appendWalk, Branch.eval, Branch.appendWalk_eval main, Term.appendWalk_eval body]
  termination_by structural _ _ _ _ _ _ x _ _ _ => x
theorem Branches.appendWalk_eval : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {bs : List Bool} →
    {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → (κ : KEnv Δ Φ) → (ρ : UEnv Δ Γ) → (jκ : JEnv Δ τ js) →
      ∀ x, br.appendWalk.eval κ ρ jκ x = br.eval κ ρ jκ x
  | _, _, _, _, _, _, _, _, .two us₁ us₂ b₁ b₂, κ, ρ, jκ, x => by
      simp only [Branches.appendWalk, Branches.eval, Term.appendWalk_eval b₁, Term.appendWalk_eval b₂]
  | _, _, _, _, _, _, _, _, .cons us b bs, κ, ρ, jκ, x => by
      simp only [Branches.appendWalk, Branches.eval, Term.appendWalk_eval b,
        Branches.appendWalk_eval bs]
  termination_by structural _ _ _ _ _ _ _ _ x _ _ _ _ => x
end

/-! ## No call is added -/

mutual
theorem Val.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (v : Val Δ d Φ Γ τ o) → v.appendWalk.numCalls = v.numCalls
  | _, _, _, _, _, .lam b => by simp only [Val.appendWalk, Val.numCalls, Body.numCalls_appendWalk b]
  | _, _, _, _, _, .thunk_mk b => by
      simp only [Val.appendWalk, Val.numCalls, Body.numCalls_appendWalk b]
  | _, _, _, _, _, .lazy_mk b => by
      simp only [Val.appendWalk, Val.numCalls, Body.numCalls_appendWalk b]
  | _, _, _, _, _, .record_mk _ => rfl
  | _, _, _, _, _, .union_mk _ _ => rfl
  | _, _, _, _, _, .array_mk _ => rfl
  | _, _, _, _, _, .list_mk _ => rfl
  | _, _, _, _, _, .data_in _ _ _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Body.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ bs : UCtx ks} → {τ : Ty ks} →
    {o : Lvl} → (b : Body Δ d Φ Γ bs τ o) → b.appendWalk.numCalls = b.numCalls
  | _, _, _, _, _, _, .closed t => by
      simp only [Body.appendWalk, Body.numCalls, Term.numCalls_appendWalk t]
  | _, _, _, _, _, _, .opened t _ => by
      simp only [Body.appendWalk, Body.numCalls, Term.numCalls_appendWalk t]
  termination_by structural _ _ _ _ _ _ x => x
theorem Comp.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {ℓ : Nat} → (c : Comp Δ d Φ Γ τ ℓ) → c.appendWalk.numCalls = c.numCalls
  | _, _, _, _, _, .app _ _ _ => rfl
  | _, _, _, _, _, .share _ => rfl
  | _, _, _, _, _, .nat_rec _ _ s _ => by
      simp only [Comp.appendWalk, Comp.numCalls, Body.numCalls_appendWalk s]
  | _, _, _, _, _, .array_foldl _ _ s _ => by
      simp only [Comp.appendWalk, Comp.numCalls, Body.numCalls_appendWalk s]
  | _, _, _, _, _, .data_rec _ _ _ brs _ _ _ => by
      simp only [Comp.appendWalk, Comp.numCalls, Body.numCalls_appendWalk]
  | _, _, _, _, _, .data_brec _ _ _ _ brs _ _ _ => by
      simp only [Comp.appendWalk, Comp.numCalls, Body.numCalls_appendWalk]
  | _, _, _, _, _, .thunk_force _ => rfl
  | _, _, _, _, _, .lazy_force _ => rfl
  termination_by structural _ _ _ _ _ x => x
theorem Term.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {o : Lvl} → (t : Term Δ d Φ Γ τ js o) → t.appendWalk.numCalls = t.numCalls
  | _, _, _, _, _, _, .ret _ => rfl
  | _, _, _, _, _, _, .letV _ v b => by
      simp only [Term.appendWalk, Term.numCalls, Val.numCalls_appendWalk v, Term.numCalls_appendWalk b]
  | _, _, _, _, _, _, .letE _ c b => by
      simp only [Term.appendWalk, Term.numCalls, Comp.numCalls_appendWalk c, Term.numCalls_appendWalk b]
  | _, _, _, _, _, _, .record_casesOn _ _ b => by
      simp only [Term.appendWalk, Term.numCalls, Term.numCalls_appendWalk b]
  | _, _, _, _, _, _, .branch br => by
      simp only [Term.appendWalk, Term.numCalls, Branch.numCalls_appendWalk br]
  | _, _, _, _, _, _, .jump _ _ => rfl
  termination_by structural _ _ _ _ _ _ x => x
theorem Branch.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} → {τ : Ty ks} →
    {js : JCtx ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) → br.appendWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, .ite c t e => by
      simp only [Branch.appendWalk, Branch.numCalls, Term.numCalls_appendWalk t,
        Term.numCalls_appendWalk e]
  | _, _, _, _, _, _, .enum_casesOn _ bs => by
      simp only [Branch.appendWalk, Branch.numCalls, Term.numCalls_appendWalk]
  | _, _, _, _, _, _, .union_casesOn _ bs => by
      simp only [Branch.appendWalk, Branch.numCalls, Branches.numCalls_appendWalk bs]
  | _, _, _, _, _, _, .join _ _ _ body main => by
      simp only [Branch.appendWalk, Branch.numCalls, Term.numCalls_appendWalk body,
        Branch.numCalls_appendWalk main]
  termination_by structural _ _ _ _ _ _ x => x
theorem Branches.numCalls_appendWalk : {d : Nat} → {Φ : KCtx ks} → {Γ : UCtx ks} →
    {bs : List Bool} → {cs : Ctors ks bs} → {τ : Ty ks} → {js : JCtx ks} → {o : Lvl} →
    (br : Branches Δ d Φ Γ cs τ js o) → br.appendWalk.numCalls = br.numCalls
  | _, _, _, _, _, _, _, _, .two _ _ b₁ b₂ => by
      simp only [Branches.appendWalk, Branches.numCalls, Term.numCalls_appendWalk b₁,
        Term.numCalls_appendWalk b₂]
  | _, _, _, _, _, _, _, _, .cons _ b bs => by
      simp only [Branches.appendWalk, Branches.numCalls, Term.numCalls_appendWalk b,
        Branches.numCalls_appendWalk bs]
  termination_by structural _ _ _ _ _ _ _ _ x => x
end

end LeanScript

end
