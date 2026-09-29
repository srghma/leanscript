module

/-!
# Toy model for `proposals/TypedDataProposals3.md`, Proposal P (nominal object types with
parameters)

Self-contained (no imports, not part of the Lake build).  Check it with

```
lake env lean proposals/TypedDataNodeToy.lean
```

The design: **every tagged-object type is a name.**  There is no structural `union` in the
type of an expression any more; a union type is `obj n args`, the declaration `n` of the
module's table applied to the closed types `args`.  A structural union of the source becomes an
anonymous, non-recursive declaration; a declared datatype a (possibly recursive) one.  The
fields of a declaration may mention its parameters (`param i`) and any declaration, itself
included.

What this file checks:

* the constructor former `mk` and the case analysis `case` are indexed by the *same* index
  `obj n args`, and read their constructors from the table (`Sig.fieldsOf`).  The
  case-of-known-constructor rewrite (`Expr.knownCtor`) is written with **no cast and no proof
  field**, and it preserves evaluation (`Expr.knownCtor_eval`);
* one declaration `List α` serves `List Nat` and `List (List Nat)` (examples at the end): the
  layout, the name printed, and any helper emitted per declaration are shared;
* type equality is decidable (a name and a list of arguments), not
  by comparing constructor lists;
* values are an inductive family and evaluation is structural, with no fuel.
-/

set_option autoImplicit false

namespace TypedDataNodeToy

/-- Membership with a position (a typed de Bruijn index). -/
inductive Mem {α : Type} : List α → α → Type where
  | zero {x : α} {xs : List α} : Mem (x :: xs) x
  | succ {x y : α} {xs : List α} : Mem xs x → Mem (y :: xs) x

/-- Closed types: a leaf, or a declaration applied to closed types. -/
inductive Ty where
  | nat
  | obj (n : Nat) (args : List Ty)

mutual
/-- Decidable equality of closed types (written by hand: `Ty` is a nested inductive). -/
def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .nat, .nat => isTrue rfl
  | .nat, .obj .. => isFalse (fun h => by cases h)
  | .obj .., .nat => isFalse (fun h => by cases h)
  | .obj n as, .obj m bs =>
    if h : n = m then
      match Ty.decEqList as bs with
      | isTrue h' => isTrue (by subst h h'; rfl)
      | isFalse h' => isFalse (fun e => by cases e; exact h' rfl)
    else isFalse (fun e => by cases e; exact h rfl)
/-- `Ty.decEq` on lists. -/
def Ty.decEqList : (as bs : List Ty) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | a :: as, b :: bs =>
    match Ty.decEq a b, Ty.decEqList as bs with
    | isTrue h, isTrue h' => isTrue (by subst h h'; rfl)
    | isFalse h, _ => isFalse (fun e => by cases e; exact h rfl)
    | _, isFalse h' => isFalse (fun e => by cases e; exact h' rfl)
end

instance : DecidableEq Ty := Ty.decEq

/-- Types in a declaration: they may mention the declaration's parameters. -/
inductive PTy where
  | nat
  | param (i : Nat)
  | obj (n : Nat) (args : List PTy)

mutual
/-- Instantiate the parameters of a declaration.  First order: no binder, no capture. -/
def PTy.inst (as : List Ty) : PTy → Ty
  | .nat => .nat
  | .param i => as.getD i .nat
  | .obj n ps => .obj n (PTy.instList as ps)
/-- `PTy.inst` on a list. -/
def PTy.instList (as : List Ty) : List PTy → List Ty
  | [] => []
  | p :: ps => p.inst as :: PTy.instList as ps
end

/-- The table of declarations: the constructors of each one, each the list of its fields. -/
structure Sig where
  ctors : Nat → List (List PTy)

/-- The constructors of `obj n args`, instantiated. -/
abbrev Sig.fieldsOf (S : Sig) (n : Nat) (args : List Ty) : List (List Ty) :=
  (S.ctors n).map (PTy.instList args)

/-! ## Values -/

mutual
/-- Values.  A constructed value is at `obj n args`; its fields are at the instantiated field
    types. -/
inductive Val (S : Sig) : Ty → Type where
  | nat (k : Nat) : Val S .nat
  | ctor {n : Nat} {args fs : List Ty} (ix : Mem (S.fieldsOf n args) fs) (vs : Vals S fs) :
      Val S (.obj n args)
/-- Lists of values. -/
inductive Vals (S : Sig) : List Ty → Type where
  | nil : Vals S []
  | cons {t : Ty} {ts : List Ty} (v : Val S t) (vs : Vals S ts) : Vals S (t :: ts)
end

/-- The value of a variable. -/
def Vals.get {S : Sig} : {Γ : List Ty} → {τ : Ty} → Vals S Γ → Mem Γ τ → Val S τ
  | _ :: _, _, .cons v _, .zero => v
  | _ :: _, _, .cons _ vs, .succ x => vs.get x

/-- Concatenation of environments (the fields bound by an arm, innermost first). -/
def Vals.append {S : Sig} : {ts Γ : List Ty} → Vals S ts → Vals S Γ → Vals S (ts ++ Γ)
  | [], _, .nil, ρ => ρ
  | _ :: _, _, .cons v vs, ρ => .cons v (vs.append ρ)

/-- The number a value of `nat` holds. -/
def Val.toNat {S : Sig} : Val S .nat → Nat
  | .nat k => k

/-! ## Expressions -/

mutual
/-- Expressions.  `mk` and `case` are the only forms that touch tagged objects. -/
inductive Expr (S : Sig) : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} (x : Mem Γ τ) : Expr S Γ τ
  | lit {Γ : List Ty} (k : Nat) : Expr S Γ .nat
  | add {Γ : List Ty} (a b : Expr S Γ .nat) : Expr S Γ .nat
  /-- `{ tag: i, _1: a₁, … }`. -/
  | mk {Γ : List Ty} {n : Nat} {args fs : List Ty} (ix : Mem (S.fieldsOf n args) fs)
      (as : Args S Γ fs) : Expr S Γ (.obj n args)
  /-- A case analysis: arm `i` binds the fields of constructor `i`. -/
  | case {Γ : List Ty} {n : Nat} {args : List Ty} {τ : Ty} (e : Expr S Γ (.obj n args))
      (arms : Arms S Γ τ (S.fieldsOf n args)) : Expr S Γ τ
  /-- `const x₁ = a₁, …; body` (what the known-constructor rewrite produces). -/
  | lets {Γ ts : List Ty} {τ : Ty} (as : Args S Γ ts) (body : Expr S (ts ++ Γ) τ) :
      Expr S Γ τ
/-- Arguments. -/
inductive Args (S : Sig) : List Ty → List Ty → Type where
  | nil {Γ : List Ty} : Args S Γ []
  | cons {Γ : List Ty} {t : Ty} {ts : List Ty} (a : Expr S Γ t) (as : Args S Γ ts) :
      Args S Γ (t :: ts)
/-- The arms of a case analysis on the constructors `cs`. -/
inductive Arms (S : Sig) : List Ty → Ty → List (List Ty) → Type where
  | nil {Γ : List Ty} {τ : Ty} : Arms S Γ τ []
  | cons {Γ : List Ty} {τ : Ty} {fs : List Ty} {cs : List (List Ty)}
      (b : Expr S (fs ++ Γ) τ) (rest : Arms S Γ τ cs) : Arms S Γ τ (fs :: cs)
end

/-! ## Evaluation (structural, no fuel) -/

mutual
def Expr.eval {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ) : Expr S Γ τ → Val S τ
  | .var x => ρ.get x
  | .lit k => .nat k
  | .add a b => .nat ((a.eval ρ).toNat + (b.eval ρ).toNat)
  | .mk ix as => .ctor ix (as.eval ρ)
  | .case e arms =>
    match e.eval ρ with
    | .ctor ix vs => arms.select ρ ix vs
  | .lets as body => body.eval ((as.eval ρ).append ρ)
def Args.eval {S : Sig} {Γ : List Ty} {ts : List Ty} (ρ : Vals S Γ) : Args S Γ ts → Vals S ts
  | .nil => .nil
  | .cons a as => .cons (a.eval ρ) (as.eval ρ)
def Arms.select {S : Sig} {Γ : List Ty} {τ : Ty} {cs : List (List Ty)} {fs : List Ty}
    (ρ : Vals S Γ) : Arms S Γ τ cs → Mem cs fs → Vals S fs → Val S τ
  | .cons b _, .zero, vs => b.eval (vs.append ρ)
  | .cons _ rest, .succ ix, vs => rest.select ρ ix vs
end

/-! ## Case of a known constructor: no cast, no proof, no `▸` -/

/-- The arm of a constructor. -/
def Arms.pick {S : Sig} {Γ : List Ty} {τ : Ty} :
    {cs : List (List Ty)} → {fs : List Ty} → Arms S Γ τ cs → Mem cs fs → Expr S (fs ++ Γ) τ
  | _ :: _, _, .cons b _, .zero => b
  | _ :: _, _, .cons _ rest, .succ ix => rest.pick ix

theorem Arms.select_eq_pick {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ) :
    {cs : List (List Ty)} → {fs : List Ty} → (arms : Arms S Γ τ cs) → (ix : Mem cs fs) →
      (vs : Vals S fs) → arms.select ρ ix vs = (arms.pick ix).eval (vs.append ρ)
  | _ :: _, _, .cons b _, .zero, vs => by simp [Arms.select, Arms.pick]
  | _ :: _, _, .cons _ rest, .succ ix, vs => by
    simp only [Arms.select, Arms.pick]
    exact Arms.select_eq_pick ρ rest ix vs

/-- `case (mk ix as) arms ↦ const fields = as; arm_ix`.  `mk` and `case` share the index
    `obj n args`, so the constructor list of the arms *is* the one `ix` points into. -/
def Expr.knownCtor {S : Sig} {Γ : List Ty} {τ : Ty} : Expr S Γ τ → Expr S Γ τ
  | .case (.mk ix as) arms => .lets as (arms.pick ix)
  | e => e

theorem Expr.knownCtor_eval {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ)
    (e : Expr S Γ τ) : e.knownCtor.eval ρ = e.eval ρ := by
  unfold Expr.knownCtor
  split
  · simp only [Expr.eval]
    rw [Arms.select_eq_pick]
  · rfl

/-! ## Example: one parametric declaration `List α`, used at two instances -/

/-- Declaration `0` is `List α`: `nil | cons α (List α)`.  Declaration `1` is an anonymous
    non-recursive union `none | some Nat` (what a structural union of the source becomes). -/
def sig : Sig := ⟨fun
  | 0 => [[], [.param 0, .obj 0 [.param 0]]]
  | _ => [[], [.nat]]⟩

abbrev listTy (α : Ty) : Ty := .obj 0 [α]

/-- `[]`, at any element type. -/
def nil {Γ : List Ty} (α : Ty) : Expr sig Γ (listTy α) := .mk .zero .nil
/-- `h :: t`. -/
def cons {Γ : List Ty} {α : Ty} (h : Expr sig Γ α) (t : Expr sig Γ (listTy α)) :
    Expr sig Γ (listTy α) :=
  .mk (.succ .zero) (.cons h (.cons t .nil))

/-- `[1, 2] : List Nat`. -/
def oneTwo : Expr sig [] (listTy .nat) := cons (.lit 1) (cons (.lit 2) (nil _))

/-- `[[5]] : List (List Nat)`: the same declaration, the same `mk`. -/
def nested : Expr sig [] (listTy (listTy .nat)) := cons (cons (.lit 5) (nil _)) (nil _)

/-- The second element of `oneTwo`. -/
def second : Expr sig [] .nat :=
  .case oneTwo (.cons (.lit 0)
    (.cons (.case (.var (.succ .zero)) (.cons (.lit 0) (.cons (.var .zero) .nil))) .nil))

/-- The head of the head of `nested`. -/
def headHead : Expr sig [] .nat :=
  .case nested (.cons (.lit 0)
    (.cons (.case (.var .zero) (.cons (.lit 0) (.cons (.var .zero) .nil))) .nil))

example : (second.eval .nil).toNat = 2 := rfl
example : (second.knownCtor.eval .nil).toNat = 2 := rfl
example : (headHead.eval .nil).toNat = 5 := rfl
example : (headHead.knownCtor.eval .nil).toNat = 5 := rfl

/-- The anonymous union `none | some Nat`: the same `mk` and `case`. -/
def optLit : Expr sig [] .nat :=
  .case (.mk (n := 1) (args := []) (.succ .zero) (.cons (.lit 7) .nil))
    (.cons (.lit 0) (.cons (.add (.var .zero) (.lit 1)) .nil))

example : (optLit.knownCtor.eval .nil).toNat = 8 := rfl

/-- Type equality is a comparison of names and arguments. -/
example : listTy .nat ≠ listTy (listTy .nat) := by decide

end TypedDataNodeToy
