module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false
set_option linter.defProp false

/-!
# The glue the generated terms are written with

`LeanScript.Term.Compile` turns a Lean `def` into a `LeanScript.Expr.Term`.  Three
things in such a term are *Lean* functions rather than syntax of the object language,
and they are all given here so that the generated code is short and, more importantly,
so that every one of them **reduces**: a generated term is checked against the Lean
function it models by `decide +kernel`, which only works if nothing in the way is a
`theorem`.

* `primN` packages an ordinary Lean function of `n` arguments as the function a
  `Term.prim` node takes, which is a function of the *tuple* of its arguments.
* `subjN` is the subject of a recursion that descends in `<` on its `n`-th argument,
  and `accArgN` is the accessibility proof that goes with it (`LeanScript.accNatLt`,
  which is a `def` and reduces).
* `Uncond` is the invariant of a recursion that descends unconditionally.
-/

namespace LeanScript.Term

open LeanScript

/-! ## Packaging a Lean function as the function of a `Term.prim` node -/

/-- A constant, as the function of a nullary `Term.prim`. -/
def prim0 {τ : Ty} (f : τ.den) : Tup (Ty.denList []) → τ.den := fun _ => f

/-- A unary Lean function, as the function of a `Term.prim`. -/
def prim1 {σ₁ τ : Ty} (f : σ₁.den → τ.den) : Tup (Ty.denList [σ₁]) → τ.den :=
  fun p => f p.1

/-- A binary Lean function, as the function of a `Term.prim`. -/
def prim2 {σ₁ σ₂ τ : Ty} (f : σ₁.den → σ₂.den → τ.den) :
    Tup (Ty.denList [σ₁, σ₂]) → τ.den := fun p => f p.1 p.2.1

/-- A ternary Lean function, as the function of a `Term.prim`. -/
def prim3 {σ₁ σ₂ σ₃ τ : Ty} (f : σ₁.den → σ₂.den → σ₃.den → τ.den) :
    Tup (Ty.denList [σ₁, σ₂, σ₃]) → τ.den := fun p => f p.1 p.2.1 p.2.2.1

/-- A function of four arguments, as the function of a `Term.prim`. -/
def prim4 {σ₁ σ₂ σ₃ σ₄ τ : Ty} (f : σ₁.den → σ₂.den → σ₃.den → σ₄.den → τ.den) :
    Tup (Ty.denList [σ₁, σ₂, σ₃, σ₄]) → τ.den :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1

/-- A function of five arguments, as the function of a `Term.prim`. -/
def prim5 {σ₁ σ₂ σ₃ σ₄ σ₅ τ : Ty}
    (f : σ₁.den → σ₂.den → σ₃.den → σ₄.den → σ₅.den → τ.den) :
    Tup (Ty.denList [σ₁, σ₂, σ₃, σ₄, σ₅]) → τ.den :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1

/-! ## The measure of a recursion

A measure is a Lean function of the arguments into whatever the recursion descends in —
a `Nat`, or a pair of them — so it is packaged exactly as a primitive is, but with the
answer an ordinary Lean type rather than the denotation of a `Ty`. -/

/-- A constant measure. -/
def meas0 {α : Type} (f : α) : Tup (Ty.denList []) → α := fun _ => f

/-- A measure of one argument. -/
def meas1 {σ₁ : Ty} {α : Type} (f : σ₁.den → α) : Tup (Ty.denList [σ₁]) → α :=
  fun p => f p.1

/-- A measure of two arguments. -/
def meas2 {σ₁ σ₂ : Ty} {α : Type} (f : σ₁.den → σ₂.den → α) :
    Tup (Ty.denList [σ₁, σ₂]) → α := fun p => f p.1 p.2.1

/-- A measure of three arguments. -/
def meas3 {σ₁ σ₂ σ₃ : Ty} {α : Type} (f : σ₁.den → σ₂.den → σ₃.den → α) :
    Tup (Ty.denList [σ₁, σ₂, σ₃]) → α := fun p => f p.1 p.2.1 p.2.2.1

/-- A measure of four arguments. -/
def meas4 {σ₁ σ₂ σ₃ σ₄ : Ty} {α : Type} (f : σ₁.den → σ₂.den → σ₃.den → σ₄.den → α) :
    Tup (Ty.denList [σ₁, σ₂, σ₃, σ₄]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1

/-- A measure of five arguments. -/
def meas5 {σ₁ σ₂ σ₃ σ₄ σ₅ : Ty} {α : Type}
    (f : σ₁.den → σ₂.den → σ₃.den → σ₄.den → σ₅.den → α) :
    Tup (Ty.denList [σ₁, σ₂, σ₃, σ₄, σ₅]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1

/-- A measure of 6 arguments. -/
def meas6 {σ1 σ2 σ3 σ4 σ5 σ6 : Ty} {α : Type}
    (f : σ1.den → σ2.den → σ3.den → σ4.den → σ5.den → σ6.den → α) :
    Tup (Ty.denList [σ1, σ2, σ3, σ4, σ5, σ6]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1

/-- A measure of 7 arguments. -/
def meas7 {σ1 σ2 σ3 σ4 σ5 σ6 σ7 : Ty} {α : Type}
    (f : σ1.den → σ2.den → σ3.den → σ4.den → σ5.den → σ6.den → σ7.den → α) :
    Tup (Ty.denList [σ1, σ2, σ3, σ4, σ5, σ6, σ7]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1

/-- A measure of 8 arguments. -/
def meas8 {σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 : Ty} {α : Type}
    (f : σ1.den → σ2.den → σ3.den → σ4.den → σ5.den → σ6.den → σ7.den → σ8.den → α) :
    Tup (Ty.denList [σ1, σ2, σ3, σ4, σ5, σ6, σ7, σ8]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1

/-- A measure of 9 arguments. -/
def meas9 {σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9 : Ty} {α : Type}
    (f : σ1.den → σ2.den → σ3.den → σ4.den → σ5.den → σ6.den → σ7.den → σ8.den → σ9.den → α) :
    Tup (Ty.denList [σ1, σ2, σ3, σ4, σ5, σ6, σ7, σ8, σ9]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1

/-- A measure of 10 arguments. -/
def meas10 {σ1 σ2 σ3 σ4 σ5 σ6 σ7 σ8 σ9 σ10 : Ty} {α : Type}
    (f : σ1.den → σ2.den → σ3.den → σ4.den → σ5.den → σ6.den → σ7.den → σ8.den → σ9.den → σ10.den → α) :
    Tup (Ty.denList [σ1, σ2, σ3, σ4, σ5, σ6, σ7, σ8, σ9, σ10]) → α :=
  fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.2.2.1

/-! ## The subject of a recursion, and the proof that it descends

A recursion the compiler produces descends in `<` on one of its arguments, which is a
`Nat`; `subjN` reads that argument out of the argument tuple and `accArgN` is the
accessibility proof for it. -/

/-- The subject of a recursion that descends on its first argument. -/
def subj0 {ps : List Ty} : Env (Ty.prim .nat :: ps) → Nat := fun as => as.1

/-- The subject of a recursion that descends on its second argument. -/
def subj1 {σ₁ : Ty} {ps : List Ty} : Env (σ₁ :: Ty.prim .nat :: ps) → Nat :=
  fun as => as.2.1

/-- The subject of a recursion that descends on its third argument. -/
def subj2 {σ₁ σ₂ : Ty} {ps : List Ty} :
    Env (σ₁ :: σ₂ :: Ty.prim .nat :: ps) → Nat := fun as => as.2.2.1

/-- The subject of a recursion that descends on its fourth argument. -/
def subj3 {σ₁ σ₂ σ₃ : Ty} {ps : List Ty} :
    Env (σ₁ :: σ₂ :: σ₃ :: Ty.prim .nat :: ps) → Nat := fun as => as.2.2.2.1

/-- The subject of a recursion that descends on its fifth argument. -/
def subj4 {σ₁ σ₂ σ₃ σ₄ : Ty} {ps : List Ty} :
    Env (σ₁ :: σ₂ :: σ₃ :: σ₄ :: Ty.prim .nat :: ps) → Nat := fun as => as.2.2.2.2.1

/-- The accessibility field of a recursion, for any `Nat`-valued subject: every natural
    number is accessible for `<`, and `LeanScript.accNatLt` says so with a `def` that
    reduces. -/
def accOf {ps : List Ty} (subject : Env ps → Nat) :
    ∀ as : Env ps, Acc NatLt (subject as) := fun as => accNatLt (subject as)

/-- The accessibility field of a recursion that descends lexicographically at a pair of
    numbers.  `LeanScript.accNatLex` is a `def`, and it reduces. -/
def accLexOf {ps : List Ty} (subject : Env ps → Nat × Nat) :
    ∀ as : Env ps, Acc NatLex (subject as) := fun as => accNatLex (subject as)

/-- The invariant of a recursion that descends unconditionally. -/
def Uncond {ps : List Ty} : Env ps → Prop := fun _ => True

end LeanScript.Term

end
