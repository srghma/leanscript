module

public import LeanScript.Term.Optimize.Dce

@[expose] public section

set_option autoImplicit false

/-!
# Atoms and simple computations

The shared vocabulary of the rewrites of `LeanScript.Term.Optimize.Cse`:

* an **atom** (`Atom Φ Γ τ`) is an unknown, a known value or a literal: a pure expression
  that costs nothing and can be moved into any larger context (`Atom.wkU`, `Atom.wkUN`,
  `Atom.wkK`) without changing its value;
* a **simple computation** (`SimpleComp Φ Γ τ`) is a call of an atom on an atom, or the
  force of an atom (`f a`, `force t`, `t ()`): the computations whose repetitions common
  subexpression elimination recognises.  Both have decidable equality, so two occurrences of
  the same computation in the same context are recognised syntactically.

Each comes with its value (`Atom.eval`, `SimpleComp.eval`), and the conversions to and from
the grammar of `Term` preserve it (`Atom.toPExpr_eval`, `SimpleComp.ofComp?_eval`, …).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Renamings used by the rewrites -/

/-- Rename the innermost unknown to the unknown `x` (of the same type and level). -/
def URen.subst {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat} (x : UVar Γ σ ℓ)
    (h : ℓ = d) : URen (⟨σ, u, d⟩ :: Γ) Γ
  | _, _, .head _ => some (h ▸ x)
  | _, _, .tail y => some y

/-- Drop the binders `bs` in front of a context (none of them may be used). -/
def URen.dropN {Γ : UCtx ks} : (bs : UCtx ks) → URen (bs ++ Γ) Γ
  | [] => URen.id
  | ⟨_, _, _⟩ :: bs => fun x => match x with
    | .head _ => none
    | .tail y => URen.dropN bs y

theorem URen.Agree.subst {Γ : UCtx ks} {σ : Ty ks} {u : Usage01ω} {d ℓ : Nat} (x : UVar Γ σ ℓ)
    (h : ℓ = d) (ρ : UEnv Δ Γ) :
    URen.Agree (URen.subst (u := u) x h) (Tuple.cons (ρ.get x) ρ) ρ := by
  subst h
  intro _ _ y z hyz
  cases y with
  | head _ =>
      simp only [URen.subst, Option.some.injEq] at hyz
      subst hyz; simp
  | tail y =>
      simp only [URen.subst, Option.some.injEq] at hyz
      subst hyz; simp

theorem URen.Agree.dropN {Γ : UCtx ks} (ρ : UEnv Δ Γ) : (bs : UCtx ks) → (vs : UEnv Δ bs) →
    URen.Agree (URen.dropN (Γ := Γ) bs) (Tuple.append vs ρ) ρ
  | [], _ => URen.Agree.id ρ
  | ⟨_, _, _⟩ :: bs, vs => by
      intro y z hyz
      cases y with
      | head _ => simp [URen.dropN] at hyz
      | tail y =>
          simp only [URen.dropN] at hyz
          rw [Tuple.append_cons, UEnv.get_cons_tail]
          exact URen.Agree.dropN ρ bs vs.tail y z hyz

/-- An unknown of the context under one more binder that is not the innermost one, as an
    unknown of the context without it. -/
def UVar.pred? {Γ : UCtx ks} {b : UBinder ks} {τ : Ty ks} {ℓ : Nat} :
    UVar (b :: Γ) τ ℓ → Option (UVar Γ τ ℓ)
  | .head _ => none
  | .tail x => some x

theorem UVar.pred?_get {Γ : UCtx ks} {b : UBinder ks} {τ : Ty ks} {ℓ : Nat}
    (x : UVar (b :: Γ) τ ℓ) {y : UVar Γ τ ℓ} (h : x.pred? = some y) (ρ : UEnv Δ Γ)
    (v : Ty.Den Δ b.ty) : UEnv.get (Tuple.cons v ρ) x = ρ.get y := by
  cases x with
  | head => cases h
  | tail x => cases h; simp

/-- Two unknowns at the same position have the same type and level, and the same value. -/
theorem UVar.eq_of_index_eq : {Γ : UCtx ks} → {τ τ' : Ty ks} → {ℓ ℓ' : Nat} →
    (x : UVar Γ τ ℓ) → (y : UVar Γ τ' ℓ') → x.index = y.index →
    τ = τ' ∧ ∀ ρ : UEnv Δ Γ, HEq (ρ.get x) (ρ.get y)
  | _ :: _, _, _, _, _, .head _, .head _, _ => ⟨rfl, fun _ => HEq.rfl⟩
  | _ :: _, _, _, _, _, .tail x, .tail y, h => by
      have ⟨h1, h2⟩ := UVar.eq_of_index_eq x y (by simpa [UVar.index] using h)
      exact ⟨h1, fun ρ => by simpa [UEnv.get] using h2 ρ.tail⟩
  | _ :: _, _, _, _, _, .head _, .tail _, h => by simp [UVar.index] at h
  | _ :: _, _, _, _, _, .tail _, .head _, h => by simp [UVar.index] at h

/-- Two known values at the same position have the same type, and the same value. -/
theorem KVar.eq_of_index_eq : {Φ : KCtx ks} → {τ τ' : Ty ks} → {o o' : Lvl} →
    (x : KVar Φ τ o) → (y : KVar Φ τ' o') → x.index = y.index →
    τ = τ' ∧ ∀ κ : KEnv Δ Φ, HEq (κ.get x) (κ.get y)
  | _ :: _, _, _, _, _, .head, .head, _ => ⟨rfl, fun _ => HEq.rfl⟩
  | _ :: _, _, _, _, _, .tail x, .tail y, h => by
      have ⟨h1, h2⟩ := KVar.eq_of_index_eq x y (by simpa [KVar.index] using h)
      exact ⟨h1, fun κ => by simpa [KEnv.get] using h2 κ.tail⟩
  | _ :: _, _, _, _, _, .head, .tail _, h => by simp [KVar.index] at h
  | _ :: _, _, _, _, _, .tail _, .head, h => by simp [KVar.index] at h

/-- What identifies an atom in its context. -/
inductive AtomKey where
  | u (i : Nat)
  | k (i : Nat)
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  deriving DecidableEq

/-- What identifies a simple computation in its context. -/
inductive CompKey where
  | app (f a : AtomKey)
  | lazyForce (a : AtomKey)
  | thunkForce (a : AtomKey)
  deriving DecidableEq

/-- An atom: an unknown, a known value or a literal (of `Bool`, `Nat`, `Int` or `String`, the
    leaves whose literals are compared structurally). -/
inductive Atom (Φ : KCtx ks) (Γ : UCtx ks) : Ty ks → Type where
  | u {τ : Ty ks} {ℓ : Nat} (x : UVar Γ τ ℓ) : Atom Φ Γ τ
  | k {τ : Ty ks} {o : Lvl} (x : KVar Φ τ o) : Atom Φ Γ τ
  | bool (b : Bool) : Atom Φ Γ .bool
  | nat (n : Nat) : Atom Φ Γ (.prim .nat)
  | int (i : Int) : Atom Φ Γ (.prim .int)
  | str (s : String) : Atom Φ Γ (.prim .string)

/-- A simple computation: a call of an atom on an atom, or a force of an atom. -/
inductive SimpleComp (Φ : KCtx ks) (Γ : UCtx ks) : Ty ks → Type where
  | app {σ τ : Ty ks} (f : Atom Φ Γ (.fn σ τ)) (a : Atom Φ Γ σ) : SimpleComp Φ Γ τ
  | lazyForce {τ : Ty ks false} (a : Atom Φ Γ (.lazy τ)) : SimpleComp Φ Γ τ.relax
  | thunkForce {τ : Ty ks false} (a : Atom Φ Γ (.thunk τ)) : SimpleComp Φ Γ τ.relax

namespace Atom
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The value of an atom. -/
def eval {τ : Ty ks} : Atom Φ Γ τ → KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | .u x, _, ρ => ρ.get x
  | .k x, κ, _ => κ.get x
  | .bool b, _, _ => b
  | .nat n, _, _ => n
  | .int i, _, _ => i
  | .str s, _, _ => s

/-- What identifies the atom. -/
def key {τ : Ty ks} : Atom Φ Γ τ → AtomKey
  | .u x => .u x.index
  | .k x => .k x.index
  | .bool b => .bool b
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s

/-- Two atoms with the same key have the same type and the same value. -/
theorem eq_of_key_eq {τ τ' : Ty ks} (a : Atom Φ Γ τ) (a' : Atom Φ Γ τ') (h : a.key = a'.key) :
    τ = τ' ∧ ∀ (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ), HEq (a.eval κ ρ) (a'.eval κ ρ) := by
  cases a with
  | u x =>
      cases a' with
      | u y =>
          have ⟨h1, h2⟩ := UVar.eq_of_index_eq (Δ := Δ) x y (by simpa [key] using h)
          exact ⟨h1, fun _ ρ => h2 ρ⟩
      | _ => simp [key] at h
  | k x =>
      cases a' with
      | k y =>
          have ⟨h1, h2⟩ := KVar.eq_of_index_eq (Δ := Δ) x y (by simpa [key] using h)
          exact ⟨h1, fun κ _ => h2 κ⟩
      | _ => simp [key] at h
  | bool b =>
      cases a' with
      | bool b' => simp only [key, AtomKey.bool.injEq] at h; subst h; exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [key] at h
  | nat n =>
      cases a' with
      | nat n' => simp only [key, AtomKey.nat.injEq] at h; subst h; exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [key] at h
  | int i =>
      cases a' with
      | int i' => simp only [key, AtomKey.int.injEq] at h; subst h; exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [key] at h
  | str s =>
      cases a' with
      | str s' => simp only [key, AtomKey.str.injEq] at h; subst h; exact ⟨rfl, fun _ _ => HEq.rfl⟩
      | _ => simp [key] at h

/-- The atom under one more unknown. -/
def wkU {τ : Ty ks} (b : UBinder ks) : Atom Φ Γ τ → Atom Φ (b :: Γ) τ
  | .u x => .u x.tail
  | .k x => .k x
  | .bool v => .bool v
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s

/-- The atom under more unknowns. -/
def wkUN {τ : Ty ks} : (bs : UCtx ks) → Atom Φ Γ τ → Atom Φ (bs ++ Γ) τ
  | [], a => a
  | b :: bs, a => (wkUN bs a).wkU b

/-- The atom under one more known value. -/
def wkK {τ : Ty ks} (b : KBinder ks) : Atom Φ Γ τ → Atom (b :: Φ) Γ τ
  | .u x => .u x
  | .k x => .k x.tail
  | .bool v => .bool v
  | .nat n => .nat n
  | .int i => .int i
  | .str s => .str s

@[simp] theorem wkU_eval {τ : Ty ks} (b : UBinder ks) (a : Atom Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (a.wkU b).eval κ (Tuple.cons v ρ) = a.eval κ ρ := by
  cases a <;> first | rfl | simp [wkU, eval]

theorem wkUN_eval {τ : Ty ks} : (bs : UCtx ks) → (a : Atom Φ Γ τ) → (κ : KEnv Δ Φ) →
    (ρ : UEnv Δ Γ) → (vs : UEnv Δ bs) → (a.wkUN bs).eval κ (Tuple.append vs ρ) = a.eval κ ρ
  | [], _, _, _, _ => rfl
  | b :: bs, a, κ, ρ, vs => by
      rw [wkUN, Tuple.append_cons, wkU_eval, wkUN_eval bs a κ ρ vs.tail]

@[simp] theorem wkK_eval {τ : Ty ks} (b : KBinder ks) (a : Atom Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (a.wkK b).eval (Tuple.cons v κ) ρ = a.eval κ ρ := by
  cases a <;> first | rfl | simp [wkK, eval]

/-- The level of an atom as a pure expression. -/
def lvl {τ : Ty ks} : Atom Φ Γ τ → Lvl
  | @Atom.u _ _ _ _ ℓ _ => some ℓ
  | @Atom.k _ _ _ _ o _ => o
  | .bool _ | .nat _ | .int _ | .str _ => none

/-- An atom as a pure expression. -/
def toPExpr {τ : Ty ks} : (a : Atom Φ Γ τ) → PExpr Δ Φ Γ τ a.lvl
  | .u x => .neu (.var x)
  | .k x => .kvar x
  | .bool b => .lit .bool b
  | .nat n => .lit .nat n
  | .int i => .lit .int i
  | .str s => .lit .string s

@[simp] theorem toPExpr_eval {τ : Ty ks} (a : Atom Φ Γ τ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    (a.toPExpr (Δ := Δ)).eval κ ρ = a.eval κ ρ := by
  cases a <;> rfl

/-- A pure expression that is an atom, as one. -/
def ofPExpr? {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Option (Atom Φ Γ τ)
  | .neu (.var x) => some (.u x)
  | .kvar x => some (.k x)
  | _ => none

theorem ofPExpr?_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o) {a : Atom Φ Γ τ}
    (h : ofPExpr? e = some a) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.eval κ ρ = e.eval κ ρ := by
  unfold ofPExpr? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- A literal is not an unknown nor a known value. -/
@[simp] theorem ofPExpr?_lit (p : LeanPrimTy) (v : p.denote) :
    ofPExpr? (PExpr.lit (Δ := Δ) (Φ := Φ) (Γ := Γ) p v) = none := rfl

/-- A literal of `Bool`, `Nat`, `Int` or `String`, as an atom. -/
def ofLit? {τ : Ty ks} {o : Lvl} : PExpr Δ Φ Γ τ o → Option (Atom Φ Γ τ)
  | .lit .bool b => some (.bool b)
  | .lit .nat n => some (.nat n)
  | .lit .int i => some (.int i)
  | .lit .string s => some (.str s)
  | _ => none

theorem ofLit?_eval {τ : Ty ks} {o : Lvl} (e : PExpr Δ Φ Γ τ o) {a : Atom Φ Γ τ}
    (h : ofLit? e = some a) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : a.eval κ ρ = e.eval κ ρ := by
  unfold ofLit? at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- Does a computation of this type answer a function (a partial application, when it is a
    call)? -/
def _root_.LeanScript.Ty.answersFn : Ty ks → Bool
  | .fn _ _ => true
  | _ => false

/-- The argument of a call, as an atom: an unknown or a known value (`ofPExpr?`), or a literal
    (`ofLit?`) when the call does not answer a function.  (A partial application on a literal,
    `f "a"`, is not worth sharing: the JavaScript calls `f` with all its arguments at once.) -/
def ofArg? {τ : Ty ks} {o : Lvl} (answersFn : Bool) (e : PExpr Δ Φ Γ τ o) :
    Option (Atom Φ Γ τ) :=
  match ofPExpr? e with
  | some a => some a
  | none => if answersFn then none else ofLit? e

theorem ofArg?_eval {τ : Ty ks} {o : Lvl} (answersFn : Bool) (e : PExpr Δ Φ Γ τ o)
    {a : Atom Φ Γ τ} (h : ofArg? answersFn e = some a) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    a.eval κ ρ = e.eval κ ρ := by
  unfold ofArg? at h
  split at h
  · rename_i a' ha'
    cases h; exact ofPExpr?_eval e ha' κ ρ
  · split at h
    · cases h
    · exact ofLit?_eval e h κ ρ

/-- An atom of the context under one more unknown that does not mention it, as an atom of
    the context without it. -/
def strengthen? {τ : Ty ks} {b : UBinder ks} : Atom Φ (b :: Γ) τ → Option (Atom Φ Γ τ)
  | .u x => x.pred?.map .u
  | .k x => some (.k x)
  | .bool v => some (.bool v)
  | .nat n => some (.nat n)
  | .int i => some (.int i)
  | .str s => some (.str s)

theorem strengthen?_eval {τ : Ty ks} {b : UBinder ks} (a : Atom Φ (b :: Γ) τ) {a' : Atom Φ Γ τ}
    (h : strengthen? a = some a') (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) :
    a.eval κ (Tuple.cons v ρ) = a'.eval κ ρ := by
  cases a with
  | u x =>
      simp only [strengthen?, Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      exact UVar.pred?_get x hy ρ v
  | k x => simp only [strengthen?, Option.some.injEq] at h; subst h; rfl
  | bool v => simp only [strengthen?, Option.some.injEq] at h; subst h; rfl
  | nat n => simp only [strengthen?, Option.some.injEq] at h; subst h; rfl
  | int i => simp only [strengthen?, Option.some.injEq] at h; subst h; rfl
  | str s => simp only [strengthen?, Option.some.injEq] at h; subst h; rfl

end Atom

namespace SimpleComp
variable {Φ : KCtx ks} {Γ : UCtx ks}

/-- The value of a simple computation. -/
def eval {τ : Ty ks} : SimpleComp Φ Γ τ → KEnv Δ Φ → UEnv Δ Γ → Ty.Den Δ τ
  | .app f a, κ, ρ => f.eval κ ρ (a.eval κ ρ)
  | .lazyForce (τ := τ) a, κ, ρ => Ty.toRelax _ τ (a.eval κ ρ)
  | .thunkForce (τ := τ) a, κ, ρ => Ty.toRelax _ τ (a.eval κ ρ)

/-- What identifies the computation. -/
def key {τ : Ty ks} : SimpleComp Φ Γ τ → CompKey
  | .app f a => .app f.key a.key
  | .lazyForce a => .lazyForce a.key
  | .thunkForce a => .thunkForce a.key

/-- Two simple computations of the same type with the same key have the same value. -/
theorem eval_eq_of_key_eq {τ τ' : Ty ks} (s : SimpleComp Φ Γ τ) (s' : SimpleComp Φ Γ τ')
    (h : s.key = s'.key) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) : HEq (s.eval κ ρ) (s'.eval κ ρ) := by
  cases s with
  | app f a =>
      cases s' with
      | app f' a' =>
          simp only [key, CompKey.app.injEq] at h
          have ⟨hf1, hf2⟩ := Atom.eq_of_key_eq (Δ := Δ) f f' h.1
          have ⟨ha1, ha2⟩ := Atom.eq_of_key_eq (Δ := Δ) a a' h.2
          cases ha1
          simp only [Ty.fn.injEq] at hf1
          obtain ⟨-, rfl⟩ := hf1
          have e1 := eq_of_heq (hf2 κ ρ)
          have e2 := eq_of_heq (ha2 κ ρ)
          simp only [eval, e1, e2]; exact HEq.rfl
      | _ => simp [key] at h
  | lazyForce a =>
      cases s' with
      | lazyForce a' =>
          simp only [key, CompKey.lazyForce.injEq] at h
          have ⟨h1, h2⟩ := Atom.eq_of_key_eq (Δ := Δ) a a' h
          simp only [Ty.lazy.injEq] at h1
          subst h1
          simp only [eval, eq_of_heq (h2 κ ρ)]; exact HEq.rfl
      | _ => simp [key] at h
  | thunkForce a =>
      cases s' with
      | thunkForce a' =>
          simp only [key, CompKey.thunkForce.injEq] at h
          have ⟨h1, h2⟩ := Atom.eq_of_key_eq (Δ := Δ) a a' h
          simp only [Ty.thunk.injEq] at h1
          subst h1
          simp only [eval, eq_of_heq (h2 κ ρ)]; exact HEq.rfl
      | _ => simp [key] at h

/-- The computation under one more unknown. -/
def wkU {τ : Ty ks} (b : UBinder ks) : SimpleComp Φ Γ τ → SimpleComp Φ (b :: Γ) τ
  | .app f a => .app (f.wkU b) (a.wkU b)
  | .lazyForce a => .lazyForce (a.wkU b)
  | .thunkForce a => .thunkForce (a.wkU b)

/-- The computation under more unknowns. -/
def wkUN {τ : Ty ks} (bs : UCtx ks) : SimpleComp Φ Γ τ → SimpleComp Φ (bs ++ Γ) τ
  | .app f a => .app (f.wkUN bs) (a.wkUN bs)
  | .lazyForce a => .lazyForce (a.wkUN bs)
  | .thunkForce a => .thunkForce (a.wkUN bs)

/-- The computation under one more known value. -/
def wkK {τ : Ty ks} (b : KBinder ks) : SimpleComp Φ Γ τ → SimpleComp (b :: Φ) Γ τ
  | .app f a => .app (f.wkK b) (a.wkK b)
  | .lazyForce a => .lazyForce (a.wkK b)
  | .thunkForce a => .thunkForce (a.wkK b)

@[simp] theorem wkU_eval {τ : Ty ks} (b : UBinder ks) (s : SimpleComp Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (s.wkU b).eval κ (Tuple.cons v ρ) = s.eval κ ρ := by
  cases s <;> simp [wkU, eval]

theorem wkUN_eval {τ : Ty ks} (bs : UCtx ks) (s : SimpleComp Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (vs : UEnv Δ bs) : (s.wkUN bs).eval κ (Tuple.append vs ρ) = s.eval κ ρ := by
  cases s <;> simp [wkUN, eval, Atom.wkUN_eval]

@[simp] theorem wkK_eval {τ : Ty ks} (b : KBinder ks) (s : SimpleComp Φ Γ τ) (κ : KEnv Δ Φ)
    (ρ : UEnv Δ Γ) (v : Ty.Den Δ b.ty) : (s.wkK b).eval (Tuple.cons v κ) ρ = s.eval κ ρ := by
  cases s <;> simp [wkK, eval]

/-- A computation that is simple, as one. -/
def ofComp? {d : Nat} {τ : Ty ks} {ℓ : Nat} : Comp Δ d Φ Γ τ ℓ → Option (SimpleComp Φ Γ τ)
  | .app f a _ => do
      let f ← Atom.ofPExpr? f
      let a ← Atom.ofArg? τ.answersFn a
      pure (.app f a)
  | .lazy_force e => (Atom.ofPExpr? e).map .lazyForce
  | .thunk_force e => (Atom.ofPExpr? e).map .thunkForce
  | _ => none

theorem ofComp?_eval {d : Nat} {τ : Ty ks} {ℓ : Nat} (c : Comp Δ d Φ Γ τ ℓ)
    {s : SimpleComp Φ Γ τ} (h : ofComp? c = some s) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    s.eval κ ρ = c.eval κ ρ := by
  cases c with
  | app f a _ =>
      simp only [ofComp?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨f', hf, a', ha, h⟩ := h
      cases h
      simp only [eval, Comp.eval, Atom.ofPExpr?_eval f hf, Atom.ofArg?_eval _ a ha]
  | lazy_force e =>
      simp only [ofComp?, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp only [eval, Comp.eval, Atom.ofPExpr?_eval e ha]
  | thunk_force e =>
      simp only [ofComp?, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      simp only [eval, Comp.eval, Atom.ofPExpr?_eval e ha]
  | _ => simp [ofComp?] at h

/-- A call of an atom on an `Int` literal that does not answer a function is a simple
    computation (so that `f 2`, repeated, is shared by common subexpression elimination). -/
theorem ofComp?_app_int {d : Nat} {σ τ : Ty ks} {ℓ : Nat} {of : Lvl} {f : PExpr Δ Φ Γ (.fn σ τ) of}
    {af : Atom Φ Γ (.fn σ τ)} (hf : Atom.ofPExpr? f = some af) (hτ : τ.answersFn = false)
    (hσ : σ = .prim .int) (n : Int) (h : Lvl.meet of none = some ℓ) :
    ofComp? (d := d) (.app f (hσ ▸ PExpr.lit .int n) h) = some (.app af (hσ ▸ Atom.int n)) := by
  subst hσ
  simp [ofComp?, hf, Atom.ofArg?, Atom.ofPExpr?_lit, Atom.ofLit?, hτ]

/-- The same for a `Nat` literal. -/
theorem ofComp?_app_nat {d : Nat} {σ τ : Ty ks} {ℓ : Nat} {of : Lvl} {f : PExpr Δ Φ Γ (.fn σ τ) of}
    {af : Atom Φ Γ (.fn σ τ)} (hf : Atom.ofPExpr? f = some af) (hτ : τ.answersFn = false)
    (hσ : σ = .prim .nat) (n : Nat) (h : Lvl.meet of none = some ℓ) :
    ofComp? (d := d) (.app f (hσ ▸ PExpr.lit .nat n) h) = some (.app af (hσ ▸ Atom.nat n)) := by
  subst hσ
  simp [ofComp?, hf, Atom.ofArg?, Atom.ofPExpr?_lit, Atom.ofLit?, hτ]

/-- The same for a `String` literal. -/
theorem ofComp?_app_str {d : Nat} {σ τ : Ty ks} {ℓ : Nat} {of : Lvl} {f : PExpr Δ Φ Γ (.fn σ τ) of}
    {af : Atom Φ Γ (.fn σ τ)} (hf : Atom.ofPExpr? f = some af) (hτ : τ.answersFn = false)
    (hσ : σ = .prim .string) (s : String) (h : Lvl.meet of none = some ℓ) :
    ofComp? (d := d) (.app f (hσ ▸ PExpr.lit .string s) h) = some (.app af (hσ ▸ Atom.str s)) := by
  subst hσ
  simp [ofComp?, hf, Atom.ofArg?, Atom.ofPExpr?_lit, Atom.ofLit?, hτ]

/-- A partial application on a literal (a call answering a function) is not a simple
    computation: it is left alone. -/
theorem ofComp?_app_lit_fn {d : Nat} {τ₁ τ₂ : Ty ks} {ℓ : Nat} {of : Lvl} (p : LeanPrimTy)
    (f : PExpr Δ Φ Γ (.fn (.prim p) (.fn τ₁ τ₂)) of) (v : p.denote)
    (h : Lvl.meet of none = some ℓ) :
    ofComp? (d := d) (.app f (PExpr.lit p v) h) = none := by
  cases hf : Atom.ofPExpr? f <;>
    simp [ofComp?, hf, Atom.ofArg?, Atom.ofPExpr?_lit, Ty.answersFn]

end SimpleComp

end LeanScript

end
