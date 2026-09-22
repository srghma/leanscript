module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Building a primitive node

`Term.prim` applies a total Lean function to the values of its arguments.  What this
module still provides is the *shape* of such a node — `prim1`, `prim2`, `prim3`, which
save a hand-written tuple pattern at every node — and the smart constructors of the two
shapes that are not primitives at all (`Option`, which is a tagged union, and a pair,
which is a record).

**Which** Lean function may be applied is not listed here: that is
`LeanScript.LeanInitPureExterns`, the catalogue of the pure `@[extern]` functions of the
runtime, and it is the single source of truth for the operations a front end has to
support.  The named wrappers this module used to carry (`natAdd`, `stringPush`, …) were
a second copy of part of that list, so they are gone; they are kept below, commented
out, as the record of what they were.

What made the evaluator total is unchanged, and is a property of the Lean functions
themselves: `Nat.sub` truncates, `Nat.div` answers `0` at a zero divisor, and a read out
of range takes the value to answer with, so no primitive can fail and no term can get
stuck.
-/

namespace LeanScript.Expr

open LeanScript

variable {Sg : Sig} {Γ : Ctx} {Ρ : RCtx}

/-! ## The shapes a primitive has -/

/-- A one-argument primitive: a Lean function of the argument's value. -/
def prim1 {a b : Ty} (f : a.den → b.den) (x : Term Sg Γ Ρ a) : Term Sg Γ Ρ b :=
  .prim [a] (fun as => f as.1) (.cons x .nil)

/-- A two-argument primitive. -/
def prim2 {a b c : Ty} (f : a.den → b.den → c.den)
    (x : Term Sg Γ Ρ a) (y : Term Sg Γ Ρ b) : Term Sg Γ Ρ c :=
  .prim [a, b] (fun as => f as.1 as.2.1) (.cons x (.cons y .nil))

/-- A three-argument primitive. -/
def prim3 {a b c d : Ty} (f : a.den → b.den → c.den → d.den)
    (x : Term Sg Γ Ρ a) (y : Term Sg Γ Ρ b) (z : Term Sg Γ Ρ c) : Term Sg Γ Ρ d :=
  .prim [a, b, c] (fun as => f as.1 as.2.1 as.2.2.1) (.cons x (.cons y (.cons z .nil)))

/-! ## `Option` and pairs, as the tagged union and the record they are -/

/-- `none`. -/
def optionNone {α : Ty} : Term Sg Γ Ρ (Ty.option α) :=
  .taggedUnion_mk (.skip (.here ⟨α, []⟩ [])) 0 (by simp [LeanTaggedUnionSchema.toList,
    CtorsWithPayload.toList]) .nil

/-- `some x`. -/
def optionSome {α : Ty} (x : Term Sg Γ Ρ α) : Term Sg Γ Ρ (Ty.option α) :=
  .taggedUnion_mk (.skip (.here ⟨α, []⟩ [])) 1 (by simp [LeanTaggedUnionSchema.toList,
    CtorsWithPayload.toList]) (.cons x .nil)

/-- `match o with | none => n | some x => s x`, with `x` bound as de Bruijn index `0` of
    `s`. -/
def optionElim {α τ : Ty} (o : Term Sg Γ Ρ (Ty.option α))
    (onNone : Term Sg Γ Ρ τ) (onSome : Term Sg (α :: Γ) Ρ τ) : Term Sg Γ Ρ τ :=
  .taggedUnion_elim o (.cons onNone (.cons onSome .nil))

/-- `(x, y)`. -/
def pairMk {α β : Ty} (x : Term Sg Γ Ρ α) (y : Term Sg Γ Ρ β) : Term Sg Γ Ρ (Ty.prod α β) :=
  .record_mk ⟨α, β, []⟩ (.cons x (.cons y .nil))

/-- `match p with | (x, y) => body`, with `x` bound as de Bruijn index `0` and `y` as
    index `1`. -/
def pairElim {α β τ : Ty} (p : Term Sg Γ Ρ (Ty.prod α β))
    (body : Term Sg (α :: β :: Γ) Ρ τ) : Term Sg Γ Ρ τ :=
  .record_elim p body

end LeanScript.Expr

end
