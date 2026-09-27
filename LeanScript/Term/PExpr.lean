module

public import LeanScript.Term.Common

@[expose] public section

set_option autoImplicit false

/-!
# Layer 1 of `LeanScript.Term`: pure expressions

The pure expressions `PExpr` with the neutral ones `Neu` and the lists `Args` and `Elems`: one
mutual block, not mutual with computations and statements (`LeanScript.Term.Term`).  See the
documentation of `LeanScript.Term.Term` for the whole grammar.
-/

namespace LeanScript

/-! ## Layer 1: pure expressions -/

mutual

/-- **Layer 1a, neutral pure expressions**: the pure expressions whose head is *not* an
    introduction form — a variable, or an elimination (`data_out`, `cond`) whose principal
    argument is itself neutral, or an extern (an opaque operation).  They are the only pure
    expressions that may be taken apart: the argument of `data_out`, the condition of `cond`
    and `Term.ite`, and the scrutinee of `Term.record_casesOn`, `Term.enum_casesOn` and
    `Term.union_casesOn` are neutral.  So no ι-redex (the elimination of an explicitly
    constructed value) can be written: `data_out b j (data_in b j e)`,
    `record_casesOn (record_mk args) body`, `union_casesOn (union_mk ix args) brs`,
    `enum_casesOn (enum_mk s i) brs` and `cond (lit .bool true) a b` are all ill-typed. -/
inductive Neu {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : Ty ks → Type where
  /-- A variable. -/
  | var {τ : Ty ks} : Var Γ τ → Neu Δ Γ τ
  /-- One layer out: the unfolded body of a value of member `j` of block `b`.  The value is
      neutral, so it is never a `data_in` (`data_out b j (data_in b j e)` is ill-typed). -/
  | data_out (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      Neu Δ Γ (.data ((Δ.block b).ref j)) → Neu Δ Γ ((Δ.block b).unfold j)
  /-- The pure conditional `cond c a b` (proposal 4d): `a` when `c` is `true`, else `b`.
      Both branches are pure expressions, so an `if` whose branches make no call needs no
      join point when it is an operand (`(if c then x + 1 else 0) * 2`).  In tail position a
      branch is still written with `Term.ite`.  The condition is neutral, never a literal. -/
  | cond {τ : Ty ks} : Neu Δ Γ .bool → PExpr Δ Γ τ → PExpr Δ Γ τ → Neu Δ Γ τ
  /-- A **cheap** pure extern (proposal 4h): a named operation on the values of its
      arguments, like `Comp.extern`, but so cheap (a machine operation on scalars: `+`, `<`,
      `&&`, a conversion, …) that it may be duplicated or dropped freely, so it needs no
      `let`.  Which externs are cheap is the translator's choice
      (`LeanScript.Extern.isCheap`); every other extern is a named `Comp.extern`. -/
  | extern {σs : List (Ty ks)} {τ : Ty ks} (name : String)
      (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) : Args Δ Γ σs → Neu Δ Γ τ

/-- **Layer 1, pure expressions** (`PCL`'s `PExpr`): the operands of every computation and
    statement.  A pure expression makes no call, binds nothing and never branches, so it may
    be duplicated or dropped freely.  It is a neutral expression (`Neu`) or an introduction
    form: a literal or a constructor.  Its context `Γ` is a parameter: it is not mutual with
    the two other layers. -/
inductive PExpr {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : Ty ks → Type where
  /-- A neutral expression: a variable, an elimination of a neutral value or an extern. -/
  | neu {τ : Ty ks} : Neu Δ Γ τ → PExpr Δ Γ τ
  /-- A literal of a leaf type: `.lit .nat 3`. -/
  | lit (p : LeanPrimTy) (v : p.denote) : PExpr Δ Γ (.prim p)
  /-- A constructor of an enum. -/
  | enum_mk (s : LeanEnumSchema) : Fin s.nOfConstructors → PExpr Δ Γ (.enum s)
  /-- A record, from its fields. -/
  | record_mk {t : Ty ks} {fs : Fields ks} : Args Δ Γ (t :: fs.toList) →
      PExpr Δ Γ (.record t fs)
  /-- A constructor of a union, from its fields. -/
  | union_mk {bs : List Bool} {b : Bool} {cs : Ctors ks bs} {h : UnionShape bs}
      {c : Ctor ks b} : CtorIx cs c → Args Δ Γ c.binds → PExpr Δ Γ (.union cs (h := h))
  /-- An array literal. -/
  | array_mk {t : Ty ks} : Elems Δ Γ t → PExpr Δ Γ (.array t)
  /-- One layer in: a value of member `j` of block `b` from its unfolded body. -/
  | data_in (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      PExpr Δ Γ ((Δ.block b).unfold j) → PExpr Δ Γ (.data ((Δ.block b).ref j))

/-- The arguments of a constructor or an extern: pure expressions. -/
inductive Args {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : List (Ty ks) → Type where
  | nil : Args Δ Γ []
  | cons {σ : Ty ks} {σs : List (Ty ks)} : PExpr Δ Γ σ → Args Δ Γ σs → Args Δ Γ (σ :: σs)

/-- The elements of an array literal: pure expressions. -/
inductive Elems {ks : List Nat} (Δ : DSig ks) (Γ : Ctx ks) : Ty ks → Type where
  | nil {t : Ty ks} : Elems Δ Γ t
  | cons {t : Ty ks} : PExpr Δ Γ t → Elems Δ Γ t → Elems Δ Γ t

end

section NeuAbbrevs
variable {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks}

/-- A variable, as a pure expression (`.neu (.var x)`). -/
abbrev PExpr.var {τ : Ty ks} (x : Var Γ τ) : PExpr Δ Γ τ := .neu (.var x)

/-- One layer out of a neutral value, as a pure expression. -/
abbrev PExpr.data_out (b : BRef ks) (j : Fin ((Δ.block b).k + 1))
    (e : Neu Δ Γ (.data ((Δ.block b).ref j))) : PExpr Δ Γ ((Δ.block b).unfold j) :=
  .neu (.data_out b j e)

/-- The pure conditional on a neutral condition, as a pure expression. -/
abbrev PExpr.cond {τ : Ty ks} (c : Neu Δ Γ .bool) (a b : PExpr Δ Γ τ) : PExpr Δ Γ τ :=
  .neu (.cond c a b)

/-- A cheap extern, as a pure expression. -/
abbrev PExpr.extern {σs : List (Ty ks)} {τ : Ty ks} (name : String)
    (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) (args : Args Δ Γ σs) : PExpr Δ Γ τ :=
  .neu (.extern name f args)

end NeuAbbrevs

/-- The variable at de Bruijn position `i` (`0` is the innermost), as a pure expression:
    `PExpr.bvar 2` instead of `.var (.tail (.tail .head))`.  The side condition that position
    `i` of the context has the expected type is closed by `rfl` when the context is known that
    far. -/
abbrev PExpr.bvar {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {τ : Ty ks} (i : Nat)
    (h : Γ[i]? = some τ := by rfl) : PExpr Δ Γ τ :=
  .var (.ofIndex Γ i h)

/-- The variable at de Bruijn position `i`, as a neutral expression (`Neu.bvar 0` is the
    scrutinee of a `record_casesOn` of the innermost variable). -/
abbrev Neu.bvar {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {τ : Ty ks} (i : Nat)
    (h : Γ[i]? = some τ := by rfl) : Neu Δ Γ τ :=
  .var (.ofIndex Γ i h)

/-- Whether a pure expression is *trivial*: a variable, a literal or a constructor of an enum.
    A trivial expression is used in place: the translator and the notation never `share` one,
    and never bind one by a `let`. -/
def PExpr.isTrivial {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} {τ : Ty ks} :
    PExpr Δ Γ τ → Bool
  | .neu (.var _) | .lit _ _ | .enum_mk _ _ => true
  | _ => false

end LeanScript

end
