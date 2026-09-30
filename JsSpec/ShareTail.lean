module

public import JsSpec.MergeIte

@[expose] public section

set_option autoImplicit false

/-!
# The rewrites of `CaseHeuristics`, in a model of JavaScript

The decision trees of `Tests/SnapshotsPBOPure/CaseHeuristics.lean` are printed shorter by three
rewrites of the JavaScript backend that `Term` cannot express (it has neither labelled blocks
nor a default arm): they are proved here in the model of `JsSpec.MergeIte` (a computation reads
and writes a state and may throw, `Js σ ε α`), so evaluation order, effects and exceptions all
count.

* **Shared tails behind a labelled block** (`JsTerm/Lower/ShareTail.lean`, `JsBlock.shareTails`):
  the copies of a block `D` in tail position are replaced by `break L;` and `D` is written
  once after the labelled block `L: { … }`.  A copy is `D` itself, or `D` with the branches
  of its tests that the tests around the copy already decided taken (`TStmt.assume`), and
  `return c ? a : b` is `if (c) { return a; } else { break L; }` when `return b` is such a copy.
  The tests remembered are the *stable* ones (`TStmt.test`: a constant's tag, a comparison of
  constants, whose value is the same wherever it is read, `env`); the other tests (`TStmt.ite`)
  may have effects and throw, and are remembered nothing.  The rewrite is modelled on syntax
  with the same algorithm (`TStmt.share`, the same dump modelled as syntactic equality), and
  proved to leave the meaning unchanged (`TStmt.labelled_share_den`).  A case analysis on a
  constant is a chain of stable tests of its tag, so it is covered by `TStmt.test`.
* **One test for two nested ones** (the printer, `mkIf`): `if (c) { if (b) { s } }` is
  `if (c && b) { s }` — `cond_cond_same_else` of `JsSpec.MergeIte`, the `else` being the
  statements after the `if` — and `!(x === l₁) && x === l₂` is `x === l₂` when `l₁ ≠ l₂`
  (`jsAnd_not_eq_eq`).
* **The arms of a case analysis grouped** (the printer, `groupedChain`): the arms that are the
  same statements are written once, under one test `s.tag === i || s.tag === j`, the most
  frequent ones last without a test; the chain computes the arm of the tag
  (`chain_eq_arm`).
-/

namespace JsSpec

variable {σ ε : Type}

/-! ## Shared tails behind a labelled block -/

/-- Statements in tail position: a statement that leaves the function (`return e;`, `throw`,
    a jump out, by its position), `return c ? a : b` (`c` any test), a stable test, any test,
    and `break L;` to the labelled block of the shared tail. -/
inductive TStmt where
  | leaf (i : Nat)
  | retCond (c a b : Nat)
  | test (c : Nat) (t e : TStmt)
  | ite (c : Nat) (t e : TStmt)
  | brk
  deriving DecidableEq

section Den
variable {R : Type} (env : Nat → Bool) (atom : Nat → Js σ ε Bool) (leaf : Nat → Js σ ε R)

/-- The meaning of a statement: `some r` when it leaves the function with `r`, `none` when it
    breaks out of the labelled block.  A stable test reads the environment `env` (no effect, the
    same value everywhere), any other test is a computation `atom c`. -/
def TStmt.den : TStmt → Js σ ε (Option R)
  | .leaf i => some <$> leaf i
  | .retCond c a b => cond (atom c) (some <$> leaf a) (some <$> leaf b)
  | .test c t e => if env c then t.den else e.den
  | .ite c t e => cond (atom c) t.den e.den
  | .brk => pure none

/-- `L: { b } d`: the block, then `d` when it breaks out. -/
def TStmt.labelled (b d : TStmt) : Js σ ε (Option R) := do
  match ← b.den env atom leaf with
  | some r => pure (some r)
  | none => d.den env atom leaf

end Den

/-- Does the statement break out of no labelled block? -/
def TStmt.noBrk : TStmt → Bool
  | .test _ t e | .ite _ t e => t.noBrk && e.noBrk
  | .brk => false
  | _ => true

/-- The statement where the stable tests `facts` have the values they give: the branches they
    decide taken, as long as they are (`JsBlock.assume`). -/
def TStmt.assume (facts : List (Nat × Bool)) : TStmt → TStmt
  | .test c t e =>
    match facts.lookup c with
    | some true => t.assume facts
    | some false => e.assume facts
    | none => .test c t e
  | s => s

/-- The statement with the copies of `D` (where the tests on the way decided them) replaced by
    `break L;` (`JsBlock.shareGo`); a `return c ? a : b` whose `return b` (or `return a`) is a
    copy is `if (c) { return a; } else { break L; }` (or the other way round). -/
def TStmt.share (D : TStmt) (facts : List (Nat × Bool)) : TStmt → TStmt
  | .brk => .brk
  | .leaf i => if D.assume facts = .leaf i then .brk else .leaf i
  | .retCond c a b =>
    if D.assume facts = .retCond c a b then .brk
    else if D.assume facts = .leaf b then .ite c (.leaf a) .brk
    else if D.assume facts = .leaf a then .ite c .brk (.leaf b)
    else .retCond c a b
  | .test c t e =>
    if D.assume facts = .test c t e then .brk
    else .test c (TStmt.share D ((c, true) :: facts) t) (TStmt.share D ((c, false) :: facts) e)
  | .ite c t e =>
    if D.assume facts = .ite c t e then .brk
    else .ite c (TStmt.share D facts t) (TStmt.share D facts e)

section Correct
variable {R : Type} (env : Nat → Bool) (atom : Nat → Js σ ε Bool) (leaf : Nat → Js σ ε R)

/-- The tests hold: each has the value the environment gives it. -/
def FactsHold (env : Nat → Bool) (facts : List (Nat × Bool)) : Prop :=
  ∀ c b, facts.lookup c = some b → env c = b

theorem FactsHold.cons {facts : List (Nat × Bool)} (h : FactsHold env facts) (c : Nat) :
    FactsHold env ((c, env c) :: facts) := by
  intro c' b hb
  by_cases hc : c' = c
  · subst hc
    simp [List.lookup] at hb
    exact hb
  · have : ((c, env c) :: facts).lookup c' = facts.lookup c' := by
      have : (c' == c) = false := by simpa using hc
      simp [List.lookup, this]
    exact h c' b (this ▸ hb)

/-- Where the tests hold, `D` with the branches they decide taken means `D`. -/
theorem TStmt.assume_den {facts : List (Nat × Bool)} (h : FactsHold env facts) :
    ∀ D : TStmt, (D.assume facts).den env atom leaf = D.den env atom leaf
  | .test c t e => by
    unfold TStmt.assume
    split
    · rename_i hl
      rw [TStmt.assume_den h t]
      simp [TStmt.den, h c true hl]
    · rename_i hl
      rw [TStmt.assume_den h e]
      simp [TStmt.den, h c false hl]
    · rfl
  | .leaf _ | .retCond .. | .ite .. | .brk => rfl

/-- The continuation of the labelled block: `r` when the block left the function, `D` when it
    broke out. -/
def afterBlock (D : TStmt) : Option R → Js σ ε (Option R)
  | some r => pure (some r)
  | none => D.den env atom leaf

theorem cond_bind {α β : Type} (c : Js σ ε Bool) (a b : Js σ ε α) (k : α → Js σ ε β) :
    cond c a b >>= k = cond c (a >>= k) (b >>= k) := by
  simp only [cond, bind_assoc]
  congr 1
  funext x
  cases x <;> rfl

theorem some_map_bind (m : Js σ ε R) (D : TStmt) :
    (some <$> m) >>= afterBlock env atom leaf D = some <$> m := by
  simp only [map_eq_pure_bind, bind_assoc, pure_bind, afterBlock]

/-- A copy of `D` replaced by `break L;`, followed by `D`, means the copy. -/
theorem copy_den {facts : List (Nat × Bool)} (h : FactsHold env facts) (D s : TStmt)
    (hc : D.assume facts = s) :
    (TStmt.brk.den env atom leaf : Js σ ε (Option R)) >>= afterBlock env atom leaf D =
      s.den env atom leaf := by
  simp only [TStmt.den, pure_bind, afterBlock]
  rw [← hc, TStmt.assume_den env atom leaf h]

/-- The statement with the copies of `D` replaced by `break L;`, followed by `D` where it
    breaks out, means the statement (from any tests that hold). -/
theorem TStmt.share_den (D : TStmt) :
    ∀ (s : TStmt) (facts : List (Nat × Bool)), FactsHold env facts → s.noBrk →
      (TStmt.share D facts s).den env atom leaf >>= afterBlock env atom leaf D =
        s.den env atom leaf
  | .brk, _, _, hs => by simp [TStmt.noBrk] at hs
  | .leaf i, facts, h, _ => by
    simp only [TStmt.share]
    split
    · exact copy_den env atom leaf h D _ (by assumption)
    · exact some_map_bind env atom leaf (leaf i) D
  | .retCond c a b, facts, h, _ => by
    simp only [TStmt.share]
    split
    · exact copy_den env atom leaf h D _ (by assumption)
    split
    · rename_i hb
      simp only [TStmt.den, cond_bind, some_map_bind, pure_bind, afterBlock]
      rw [← TStmt.assume_den env atom leaf h D, hb]
      rfl
    split
    · rename_i ha
      simp only [TStmt.den, cond_bind, some_map_bind, pure_bind, afterBlock]
      rw [← TStmt.assume_den env atom leaf h D, ha]
      rfl
    simp only [TStmt.den, cond_bind, some_map_bind]
  | .test c t e, facts, h, hs => by
    simp only [TStmt.noBrk, Bool.and_eq_true] at hs
    simp only [TStmt.share]
    split
    · exact copy_den env atom leaf h D _ (by assumption)
    simp only [TStmt.den]
    cases hc : env c
    · simp only [Bool.false_eq_true, ite_false]
      exact TStmt.share_den D e _ (hc ▸ h.cons env c) hs.2
    · simp only [ite_true]
      exact TStmt.share_den D t _ (hc ▸ h.cons env c) hs.1
  | .ite c t e, facts, h, hs => by
    simp only [TStmt.noBrk, Bool.and_eq_true] at hs
    simp only [TStmt.share]
    split
    · exact copy_den env atom leaf h D _ (by assumption)
    simp only [TStmt.den, cond_bind, TStmt.share_den D t facts h hs.1,
      TStmt.share_den D e facts h hs.2]

/-- **The rewrite of `JsBlock.shareTails` is correct**: `L: { s' } D`, where `s'` is `s` with
    the copies of `D` replaced by `break L;` (`D` itself, or `D` where the stable tests around
    the copy decide it, and `return c ? a : b` around such a copy), means `s`, for every meaning
    of the tests and of the statements that leave the function (their effects and exceptions
    included).  (Neither `s` nor `D` breaks out of a labelled block of its own: the jumps to the
    join points around are statements that leave, `TStmt.leaf`.) -/
theorem TStmt.labelled_share_den (D s : TStmt) (hs : s.noBrk) :
    TStmt.labelled env atom leaf (TStmt.share D [] s) D = s.den env atom leaf := by
  rw [← TStmt.share_den env atom leaf D s [] (fun _ _ h => by simp [List.lookup] at h) hs]
  simp only [TStmt.labelled]
  congr 1

end Correct

/-! ## One test for two nested ones -/

/-- `!a`, in the model. -/
def jsNot (a : Js σ ε Bool) : Js σ ε Bool := do return !(← a)

/-- `!(x === l₁) && x === l₂` is `x === l₂` for two different literals `l₁ ≠ l₂`, `x` read
    without effect (a name or a field, `read`). -/
theorem jsAnd_not_eq_eq {α : Type} [DecidableEq α] (read : σ → α) (l₁ l₂ : α) (h : l₁ ≠ l₂) :
    jsAnd (jsNot (fun s => .ok (decide (read s = l₁), s)))
        (fun s => .ok (decide (read s = l₂), s)) =
      ((fun s => .ok (decide (read s = l₂), s)) : Js σ ε Bool) := by
  funext s
  by_cases h₁ : read s = l₁
  · simp [jsAnd, jsNot, h₁, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, h]
  · simp [jsAnd, jsNot, h₁, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]

/-! ## The arms of a case analysis grouped -/

/-- The chain `if (s.tag === i || s.tag === j …) { b } else …`, then `dflt`: the statements of
    the first group whose tags contain the tag (the tests read the tag without effect). -/
def chain {α : Type} (tag : Nat) : List (List Nat × α) → α → α
  | [], dflt => dflt
  | (ts, b) :: rest, dflt => if tag ∈ ts then b else chain tag rest dflt

/-- The chain is the statements `arm` when every group containing the tag has them, and `dflt`
    are them when no group contains the tag. -/
theorem chain_eq_of {α : Type} (arm : α) (tag : Nat) (dflt : α) :
    ∀ groups : List (List Nat × α),
      (∀ g ∈ groups, tag ∈ g.1 → g.2 = arm) → ((∀ g ∈ groups, tag ∉ g.1) → dflt = arm) →
      chain tag groups dflt = arm
  | [], _, hd => hd (by simp)
  | (ts, b) :: rest, hg, hd => by
    simp only [chain]
    split
    · rename_i h
      exact hg (ts, b) (by simp) h
    · rename_i h
      exact chain_eq_of arm tag dflt rest (fun g hg' => hg g (by simp [hg']))
        (fun hn => hd (fun g hg' => by
          simp only [List.mem_cons] at hg'
          rcases hg' with rfl | hg'
          · exact h
          · exact hn g hg'))

/-- **The chain of `groupedChain` computes the arm of the tag**: when every tag of a group has
    the group's statements as its arm, and every tag of no group has the last statements
    `dflt`, the chain is the arm of the tag. -/
theorem chain_eq_arm {α : Type} (arms : Nat → α) (tag : Nat) (dflt : α)
    (groups : List (List Nat × α)) (hg : ∀ g ∈ groups, ∀ i ∈ g.1, arms i = g.2)
    (hd : ∀ i, (∀ g ∈ groups, i ∉ g.1) → arms i = dflt) :
    chain tag groups dflt = arms tag :=
  chain_eq_of (arms tag) tag dflt groups (fun g hg' ht => (hg g hg' tag ht).symm)
    (fun hn => (hd tag hn).symm)

end JsSpec
