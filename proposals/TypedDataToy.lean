module

/-!
# Toy model for `proposals/TypedDataProposals.md`, Proposal 3 (unfolding carried by a proof)

Self-contained (no imports, not part of the Lake build).  Check it with the bare compiler:

```
lean proposals/TypedDataToy.lean
```

The toy has three types: `nat`, a structural union `union cs`, and a declared datatype
`data r`, where `r : Fin n` names a member of the module's signature `S : Sig n`.  `S r` is
the list of constructors of `data r`, whose fields may mention `data r` again (a recursive
type).

The point of the design: **one** constructor former `mk` and **one** case analysis `case` serve
both structural unions and declared datatypes.  Each takes a proof `h : τ.ctors? S = some cs`
that the type `τ` unfolds to the constructors `cs`.  There is no `fold` / `unfold` cast node in
the syntax, so a rewrite that looks for `case (mk …)` (case of a known constructor) sees the
same pattern whatever the type, and it is proved to preserve evaluation
(`Expr.knownCtor_eval`) once, for both kinds of types.  Values of a recursive datatype are an
ordinary inductive family (`Val`), so the semantics needs no fuel.
-/

set_option autoImplicit false

namespace TypedDataToy

/-- Membership with a position (a typed de Bruijn index). -/
inductive Mem {α : Type} : List α → α → Type where
  | zero {x : α} {xs : List α} : Mem (x :: xs) x
  | succ {x y : α} {xs : List α} : Mem xs x → Mem (y :: xs) x

/-- The types.  `data r` is a *name*: its layout is in the signature, not in the type. -/
inductive Ty (n : Nat) : Type where
  | nat
  | union (cs : List (List (Ty n)))
  | data (r : Fin n)
  deriving Inhabited

/-- A signature: the constructors (each the list of its fields) of every declared member. -/
def Sig (n : Nat) : Type := Fin n → List (List (Ty n))

variable {n : Nat} {S : Sig n}

/-- The constructors a type unfolds to: its own for a union, the signature's for a declared
    datatype, none for a leaf. -/
def Ty.ctors? (S : Sig n) : Ty n → Option (List (List (Ty n)))
  | .nat => none
  | .union cs => some cs
  | .data r => some (S r)

mutual
/-- Expressions over the context `C` (the types of the variables, innermost first). -/
inductive Expr (S : Sig n) : List (Ty n) → Ty n → Type where
  | var {C : List (Ty n)} {τ : Ty n} : Mem C τ → Expr S C τ
  | lit {C : List (Ty n)} : Nat → Expr S C .nat
  /-- Constructor `ix` of `τ`, for a structural union **and** a declared datatype alike. -/
  | mk {C : List (Ty n)} {τ : Ty n} {cs : List (List (Ty n))} {fs : List (Ty n)}
      (h : τ.ctors? S = some cs) (ix : Mem cs fs) (args : Args S C fs) : Expr S C τ
  /-- A case analysis of a value of `τ`; each arm binds the fields of its constructor. -/
  | case {C : List (Ty n)} {τ ρ : Ty n} {cs : List (List (Ty n))}
      (h : τ.ctors? S = some cs) (e : Expr S C τ) (arms : Arms S C cs ρ) : Expr S C ρ
  /-- Bind the arguments, then the body (what a case of a known constructor becomes). -/
  | letArgs {C fs : List (Ty n)} {ρ : Ty n} (args : Args S C fs) (body : Expr S (fs ++ C) ρ) :
      Expr S C ρ
/-- Arguments of the types `fs`. -/
inductive Args (S : Sig n) : List (Ty n) → List (Ty n) → Type where
  | nil {C : List (Ty n)} : Args S C []
  | cons {C : List (Ty n)} {τ : Ty n} {fs : List (Ty n)} :
      Expr S C τ → Args S C fs → Args S C (τ :: fs)
/-- The arms of a case analysis, one per constructor. -/
inductive Arms (S : Sig n) : List (Ty n) → List (List (Ty n)) → Ty n → Type where
  | nil {C : List (Ty n)} {ρ : Ty n} : Arms S C [] ρ
  | cons {C fs : List (Ty n)} {cs : List (List (Ty n))} {ρ : Ty n} :
      Expr S (fs ++ C) ρ → Arms S C cs ρ → Arms S C (fs :: cs) ρ
end

mutual
/-- Values.  A value of a declared (recursive) datatype is a constructor with its fields, as a
    value of a union is: `Val` is an ordinary inductive family. -/
inductive Val (S : Sig n) : Ty n → Type where
  | nat : Nat → Val S .nat
  | ctor {τ : Ty n} {cs : List (List (Ty n))} {fs : List (Ty n)}
      (h : τ.ctors? S = some cs) (ix : Mem cs fs) (vs : Vals S fs) : Val S τ
/-- A list of values of the types `ts`. -/
inductive Vals (S : Sig n) : List (Ty n) → Type where
  | nil : Vals S []
  | cons {τ : Ty n} {ts : List (Ty n)} : Val S τ → Vals S ts → Vals S (τ :: ts)
end

/-- The value at a position. -/
def Vals.get {ts : List (Ty n)} {τ : Ty n} : Vals S ts → Mem ts τ → Val S τ
  | .cons v _, .zero => v
  | .cons _ vs, .succ m => vs.get m

/-- Concatenation. -/
def Vals.append {ts us : List (Ty n)} : Vals S ts → Vals S us → Vals S (ts ++ us)
  | .nil, ws => ws
  | .cons v vs, ws => .cons v (vs.append ws)

/-- The arm of a constructor. -/
def Arms.get {C fs : List (Ty n)} {cs : List (List (Ty n))} {ρ : Ty n} :
    Arms S C cs ρ → Mem cs fs → Expr S (fs ++ C) ρ
  | .cons b _, .zero => b
  | .cons _ as, .succ m => as.get m

/-- Two unfoldings of one type are the same constructors. -/
theorem ctors_unique {τ : Ty n} {cs cs' : List (List (Ty n))}
    (h : τ.ctors? S = some cs) (h' : τ.ctors? S = some cs') : cs' = cs :=
  Option.some.inj (h'.symm.trans h)

mutual
/-- Evaluation (structural: no fuel, even for recursive datatypes). -/
def Expr.eval {C : List (Ty n)} {τ : Ty n} : Expr S C τ → Vals S C → Val S τ
  | .var m, env => env.get m
  | .lit k, _ => .nat k
  | .mk h ix args, env => .ctor h ix (args.eval env)
  | .case (τ := τ) h e arms, env =>
    match τ, e.eval env, h with
    | _, .ctor h' ix vs, h => arms.evalAt ((ctors_unique h h') ▸ ix) vs env
    | _, .nat _, h => nomatch h
  | .letArgs args body, env => body.eval ((args.eval env).append env)
/-- Evaluation of arguments. -/
def Args.eval {C fs : List (Ty n)} : Args S C fs → Vals S C → Vals S fs
  | .nil, _ => .nil
  | .cons e as, env => .cons (e.eval env) (as.eval env)
/-- Evaluation of the arm of a constructor, on its fields. -/
def Arms.evalAt {C fs : List (Ty n)} {cs : List (List (Ty n))} {ρ : Ty n} :
    Arms S C cs ρ → Mem cs fs → Vals S fs → Vals S C → Val S ρ
  | .cons b _, .zero, vs, env => b.eval (vs.append env)
  | .cons _ as, .succ m, vs, env => as.evalAt m vs env
end

theorem Arms.evalAt_eq {C fs : List (Ty n)} {cs : List (List (Ty n))} {ρ : Ty n}
    (as : Arms S C cs ρ) (m : Mem cs fs) (vs : Vals S fs) (env : Vals S C) :
    as.evalAt m vs env = (as.get m).eval (vs.append env) :=
  match as, m with
  | .cons _ _, .zero => by simp [Arms.evalAt, Arms.get]
  | .cons _ as, .succ m => by simp [Arms.evalAt, Arms.get, Arms.evalAt_eq as m]

/-- **Case of a known constructor**, one rewrite for unions and declared datatypes:
    `case (mk ix args) arms` is the arm `ix` with the arguments bound. -/
def Expr.knownCtor {C : List (Ty n)} {ρ : Ty n} : Expr S C ρ → Expr S C ρ
  | .case h (.mk h' ix args) arms => .letArgs args (arms.get ((ctors_unique h h') ▸ ix))
  | e => e

/-- The rewrite preserves evaluation. -/
theorem Expr.knownCtor_eval {C : List (Ty n)} {ρ : Ty n} (e : Expr S C ρ) (env : Vals S C) :
    e.knownCtor.eval env = e.eval env := by
  unfold Expr.knownCtor
  split
  · rename_i h h' ix args arms
    simp only [Expr.eval, Arms.evalAt_eq]
  · rfl

/-! ## An example: `List Nat` as a declared datatype -/

/-- One member: `nil | cons Nat (data 0)`. -/
def listSig : Sig 1 := fun _ => [[], [.nat, .data 0]]

/-- `[5]`, built by the same `mk` as a structural union would be. -/
def five : Expr listSig [] (.data 0) :=
  .mk (cs := [[], [.nat, .data 0]]) rfl (.succ .zero)
    (.cons (.lit 5) (.cons (.mk (cs := [[], [.nat, .data 0]]) rfl .zero .nil) .nil))

/-- `match [5] with | [] => 0 | x :: _ => x`. -/
def headOr0 : Expr listSig [] .nat :=
  .case (cs := [[], [.nat, .data 0]]) rfl five
    (.cons (.lit 0) (.cons (.var .zero) .nil))

/-- The value of an expression of type `nat`, as a number. -/
def Val.toNat? : Val S .nat → Option Nat
  | .nat k => some k
  | .ctor h _ _ => nomatch h

example : (headOr0.eval .nil).toNat? = some 5 := rfl
example : (headOr0.knownCtor.eval .nil).toNat? = some 5 := rfl

end TypedDataToy
