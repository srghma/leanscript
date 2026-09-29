module

/-!
# Toy model for `proposals/TypedDataProposals2.md`, Proposal B (types of expressions in head form)

Self-contained (no imports, not part of the Lake build).  Check it with

```
lake env lean proposals/TypedDataHeadToy.lean
```

A declared datatype `data r` is a *name*.  Its constructors are `S.ctors r`, in the signature
`S`, and their fields may mention `data r` again (a recursive type).

The rule of the design: **no expression has a type `data r`.**  Wherever a value of a type
`t` is *bound* (a field bound by a case arm, the argument of a constructor, and in the real
language also a function parameter and an array element), the binder's type is
`t.head S`.  `head` replaces `data r` by its unfolding, `union (S.ctors r)`, one level deep
and nothing more.  The name `data r` stays only in the *field lists* of `union`, where the
recursion is.

The consequences, which this file checks:

* the constructor former `mk` and the case analysis `case` keep the exact shape they have
  today (`mk ix args : Expr S Γ (.union cs)`).  A pass that matches `case (mk ix args) arms`
  finds the same pattern for a structural union and for a declared datatype;
* there is **no cast node and no proof field**.  The case-of-known-constructor rewrite
  (`Expr.knownCtor`) is written without a single `▸`, and it is proved to preserve evaluation
  (`Expr.knownCtor_eval`);
* values of recursive datatypes are an ordinary inductive family (`Val`), and `Expr.eval` is
  structural, so it needs no fuel.
-/

set_option autoImplicit false

namespace TypedDataHeadToy

/-- Membership with a position (a typed de Bruijn index). -/
inductive Mem {α : Type} : List α → α → Type where
  | zero {x : α} {xs : List α} : Mem (x :: xs) x
  | succ {x y : α} {xs : List α} : Mem xs x → Mem (y :: xs) x

/-- Types: a leaf, a structural union (each constructor is the list of its fields), and a
    declared datatype, by its position in the signature. -/
inductive Ty where
  | nat
  | union (cs : List (List Ty))
  | data (r : Nat)

/-- A signature: the constructors of each declared datatype.  It is a list of constructors,
    not a `Ty`, so its unfolding can never be another `data` (a datatype is never an alias). -/
structure Sig where
  ctors : Nat → List (List Ty)

/-- The head form of a type: `data r` unfolded **once**, the other types unchanged.  Its
    result is never a `data`. -/
def Ty.head (S : Sig) : Ty → Ty
  | .data r => .union (S.ctors r)
  | t => t

/-- Head forms of a list of types (the types of the fields bound by an arm). -/
abbrev heads (S : Sig) (fs : List Ty) : List Ty := fs.map (Ty.head S)

theorem Ty.head_head (S : Sig) (t : Ty) : (t.head S).head S = t.head S := by
  cases t <;> rfl

/-! ## Values -/

mutual
/-- Values.  A constructed value is at a `union` type; its fields are at their head forms. -/
inductive Val (S : Sig) : Ty → Type where
  | nat (n : Nat) : Val S .nat
  | ctor {cs : List (List Ty)} {fs : List Ty} (ix : Mem cs fs) (vs : Vals S (heads S fs)) :
      Val S (.union cs)
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
  | .nat n => n

/-! ## Expressions -/

mutual
/-- Expressions.  `mk` and `case` are the only forms that touch unions, structural or
    declared, and they are **exactly** the forms of the language without declared datatypes,
    except that the fields are at their head forms. -/
inductive Expr (S : Sig) : List Ty → Ty → Type where
  | var {Γ : List Ty} {τ : Ty} (x : Mem Γ τ) : Expr S Γ τ
  | lit {Γ : List Ty} (n : Nat) : Expr S Γ .nat
  | add {Γ : List Ty} (a b : Expr S Γ .nat) : Expr S Γ .nat
  /-- `{ tag: i, _1: a₁, … }`. -/
  | mk {Γ : List Ty} {cs : List (List Ty)} {fs : List Ty} (ix : Mem cs fs)
      (args : Args S Γ (heads S fs)) : Expr S Γ (.union cs)
  /-- A case analysis: arm `i` binds the fields of constructor `i`. -/
  | case {Γ : List Ty} {cs : List (List Ty)} {τ : Ty} (e : Expr S Γ (.union cs))
      (arms : Arms S Γ τ cs) : Expr S Γ τ
  /-- `const x₁ = a₁, …; body` (what the known-constructor rewrite produces). -/
  | lets {Γ ts : List Ty} {τ : Ty} (args : Args S Γ ts) (body : Expr S (ts ++ Γ) τ) :
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
      (b : Expr S (heads S fs ++ Γ) τ) (rest : Arms S Γ τ cs) : Arms S Γ τ (fs :: cs)
end

/-! ## Evaluation (structural, no fuel) -/

mutual
def Expr.eval {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ) : Expr S Γ τ → Val S τ
  | .var x => ρ.get x
  | .lit n => .nat n
  | .add a b => .nat ((a.eval ρ).toNat + (b.eval ρ).toNat)
  | .mk ix args => .ctor ix (args.eval ρ)
  | .case e arms =>
    match e.eval ρ with
    | .ctor ix vs => arms.select ρ ix vs
  | .lets args body => body.eval ((args.eval ρ).append ρ)
def Args.eval {S : Sig} {Γ : List Ty} {ts : List Ty} (ρ : Vals S Γ) : Args S Γ ts → Vals S ts
  | .nil => .nil
  | .cons a as => .cons (a.eval ρ) (as.eval ρ)
def Arms.select {S : Sig} {Γ : List Ty} {τ : Ty} {cs : List (List Ty)} {fs : List Ty}
    (ρ : Vals S Γ) : Arms S Γ τ cs → Mem cs fs → Vals S (heads S fs) → Val S τ
  | .cons b _, .zero, vs => b.eval (vs.append ρ)
  | .cons _ rest, .succ ix, vs => rest.select ρ ix vs
end

/-! ## Case of a known constructor: no cast, no proof, no `▸` -/

/-- The arm of a constructor. -/
def Arms.pick {S : Sig} {Γ : List Ty} {τ : Ty} :
    {cs : List (List Ty)} → {fs : List Ty} → Arms S Γ τ cs → Mem cs fs →
      Expr S (heads S fs ++ Γ) τ
  | _ :: _, _, .cons b _, .zero => b
  | _ :: _, _, .cons _ rest, .succ ix => rest.pick ix

theorem Arms.select_eq_pick {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ) :
    {cs : List (List Ty)} → {fs : List Ty} → (arms : Arms S Γ τ cs) → (ix : Mem cs fs) →
      (vs : Vals S (heads S fs)) → arms.select ρ ix vs = (arms.pick ix).eval (vs.append ρ)
  | _ :: _, _, .cons b _, .zero, vs => by simp [Arms.select, Arms.pick]
  | _ :: _, _, .cons _ rest, .succ ix, vs => by
    simp only [Arms.select, Arms.pick]
    exact Arms.select_eq_pick ρ rest ix vs

/-- `case (mk ix args) arms ↦ const fields = args; arm_ix`.  The same rewrite for a
    structural union and for a declared (recursive) datatype: the arguments of `mk` are at the
    head forms of the fields, which is exactly what the arm binds. -/
def Expr.knownCtor {S : Sig} {Γ : List Ty} {τ : Ty} : Expr S Γ τ → Expr S Γ τ
  | .case (.mk ix args) arms => .lets args (arms.pick ix)
  | e => e

theorem Expr.knownCtor_eval {S : Sig} {Γ : List Ty} {τ : Ty} (ρ : Vals S Γ)
    (e : Expr S Γ τ) : e.knownCtor.eval ρ = e.eval ρ := by
  unfold Expr.knownCtor
  split
  · simp only [Expr.eval]
    rw [Arms.select_eq_pick]
  · rfl

/-! ## Example: `List Nat` as a declared datatype, and a structural union of the same shape -/

/-- `data 0` is `List Nat`: `nil | cons Nat (data 0)`. -/
def listSig : Sig := ⟨fun _ => [[], [.nat, .data 0]]⟩

/-- `[1, 2]`: the tail is at the head form of `data 0`, a `union`, so it is an ordinary `mk`. -/
def oneTwo : Expr listSig [] (.union [[], [.nat, .data 0]]) :=
  .mk (.succ .zero) (.cons (.lit 1)
    (.cons (.mk (.succ .zero) (.cons (.lit 2) (.cons (.mk .zero .nil) .nil))) .nil))

/-- The second element: two nested case analyses, the inner one on the bound tail. -/
def second : Expr listSig [] .nat :=
  .case oneTwo (.cons (.lit 0)
    (.cons (.case (.var (.succ .zero)) (.cons (.lit 0) (.cons (.var .zero) .nil))) .nil))

example : (second.eval .nil).toNat = 2 := rfl
example : (second.knownCtor.eval .nil).toNat = 2 := rfl

/-- A structural union of one constructor-free case and a `Nat` case: the same `mk` and `case`. -/
def optLit : Expr listSig [] .nat :=
  .case (.mk (cs := [[], [.nat]]) (.succ .zero) (.cons (.lit 7) .nil))
    (.cons (.lit 0) (.cons (.add (.var .zero) (.lit 1)) .nil))

example : (optLit.knownCtor.eval .nil).toNat = 8 := rfl

end TypedDataHeadToy
