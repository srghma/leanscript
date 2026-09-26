module

public import LeanScript.Nominal.Den
public import LeanScript.DeBruijn

@[expose] public section

set_option autoImplicit false

/-!
# `Nominal.Term`: terms over a datatype signature

Step 5 of design **N** of `proposals/NominalTyProposal.md` (§2.5).

A term is indexed by the program's datatype signature `Δ : DSig ks`, a context `Γ` of
closed types and its type.  Recursive datatypes have exactly **three** term formers,
available at every block of the signature:

* `Term.data_in b j e` — one layer in: `e` is a value of member `j`'s unfolded body;
* `Term.data_out b j e` — one layer out; the unfolded body is again a closed type, so it
  is taken apart with the ordinary `Term.record_casesOn` / `Term.union_casesOn`;
* `Term.data_rec b ρ branches j e` — the fold of a whole block, with one answer type
  `ρ i` per member and one branch per member.  Branch `i` binds member `i`'s body in which
  every hole `i'` is the pair of the subvalue and the answer at it.

There is no fixpoint and no fuel: every loop is a fold (`data_rec`, `nat_rec`,
`array_foldl`), so the evaluator (`LeanScript.Nominal.Term.eval`) is total and structural.

The grammar is in direct style.  Leaf operations are `Term.extern`, a named Lean function on
the values of its arguments (as the extern calls of `LeanScript.Term` are); because it holds
a function, `Term` has no decidable equality.
-/

namespace LeanScript

namespace Nominal

/-- A context: the types of the variables in scope, innermost first. -/
abbrev Ctx (ks : List Nat) : Type := List (Ty ks)

/-- A typed de Bruijn variable. -/
abbrev Var {ks : List Nat} (Γ : Ctx ks) (τ : Ty ks) : Type := DeBruijn Γ τ

/-- The values of a list of types: a nested product ending in `PUnit`.  An environment is
    the `DenList` of a context. -/
def DenList {ks : List Nat} (E : Ref ks → Type) : List (Ty ks) → Type
  | [] => PUnit
  | t :: ts => Ty.den E t × DenList E ts

/-- The types of the fields, in order. -/
def Fields.toList {ks : List Nat} : Fields ks → List (Ty ks)
  | .one t => [t]
  | .cons t fs => t :: fs.toList

/-- The types a constructor binds: its fields, or nothing. -/
def Ctor.binds {ks : List Nat} : Ctor ks → List (Ty ks)
  | .nullary => []
  | .fields fs => fs.toList

/-- A constructor of a union: constructive evidence that `c` is one of `cs`, and where. -/
inductive CtorIx {ks : List Nat} : Ctors ks → Ctor ks → Type where
  | two₁ {c d : Ctor ks} : CtorIx (.two c d) c
  | two₂ {c d : Ctor ks} : CtorIx (.two c d) d
  | head {c : Ctor ks} {cs : Ctors ks} : CtorIx (.cons c cs) c
  | tail {c c' : Ctor ks} {cs : Ctors ks} : CtorIx cs c' → CtorIx (.cons c cs) c'
  deriving DecidableEq, Repr

mutual

/-- A term of type `τ` in context `Γ`, over the datatype signature `Δ`. -/
inductive Term {ks : List Nat} (Δ : DSig ks) : Ctx ks → Ty ks → Type where
  /-- A variable. -/
  | var {Γ : Ctx ks} {τ : Ty ks} : Var Γ τ → Term Δ Γ τ
  /-- `let x := e; body`: `x` is de Bruijn index `0` of `body`. -/
  | letE {Γ : Ctx ks} {σ τ : Ty ks} : Term Δ Γ σ → Term Δ (σ :: Γ) τ → Term Δ Γ τ
  /-- `fun x => body`. -/
  | lam {Γ : Ctx ks} {σ τ : Ty ks} : Term Δ (σ :: Γ) τ → Term Δ Γ (.fn σ τ)
  /-- Application. -/
  | app {Γ : Ctx ks} {σ τ : Ty ks} : Term Δ Γ (.fn σ τ) → Term Δ Γ σ → Term Δ Γ τ
  /-- A literal of a leaf type. -/
  | lit {Γ : Ctx ks} (p : LeanPrimTy) (h : p.Nondeg = true) (v : p.denote) : Term Δ Γ (.prim p h)
  /-- A named operation on the values of its arguments (a pure extern). -/
  | extern {Γ : Ctx ks} {σs : List (Ty ks)} {τ : Ty ks} (name : String)
      (f : DenList (DSig.refDen Δ) σs → Ty.Den Δ τ) : Args Δ Γ σs → Term Δ Γ τ
  /-- `if c then t else e`. -/
  | ite {Γ : Ctx ks} {τ : Ty ks} : Term Δ Γ .bool → Term Δ Γ τ → Term Δ Γ τ → Term Δ Γ τ
  /-- `Nat.rec` with a non-dependent motive: the successor branch binds the predecessor
      (index `1`) and the answer at it (index `0`). -/
  | nat_rec {Γ : Ctx ks} {τ : Ty ks} : Term Δ Γ .nat → Term Δ Γ τ → Term Δ (τ :: .nat :: Γ) τ →
      Term Δ Γ τ
  /-- A constructor of an enum. -/
  | enum_mk {Γ : Ctx ks} (s : LeanEnumSchema) : Fin s.nOfConstructors → Term Δ Γ (.enum s)
  /-- Case analysis of an enum: one branch per constructor. -/
  | enum_casesOn {Γ : Ctx ks} {s : LeanEnumSchema} {τ : Ty ks} : Term Δ Γ (.enum s) →
      (Fin s.nOfConstructors → Term Δ Γ τ) → Term Δ Γ τ
  /-- A record, from its fields. -/
  | record_mk {Γ : Ctx ks} {t : Ty ks} {fs : Fields ks} : Args Δ Γ (t :: fs.toList) →
      Term Δ Γ (.record t fs)
  /-- Take a record apart: the body binds the fields, the first field innermost (index `0`). -/
  | record_casesOn {Γ : Ctx ks} {t : Ty ks} {fs : Fields ks} {τ : Ty ks} :
      Term Δ Γ (.record t fs) → Term Δ ((t :: fs.toList) ++ Γ) τ → Term Δ Γ τ
  /-- A constructor of a union, from its fields. -/
  | union_mk {Γ : Ctx ks} {cs : Ctors ks} {c : Ctor ks} : CtorIx cs c → Args Δ Γ c.binds →
      Term Δ Γ (.union cs)
  /-- Case analysis of a union: each branch binds the fields of its constructor. -/
  | union_casesOn {Γ : Ctx ks} {cs : Ctors ks} {τ : Ty ks} : Term Δ Γ (.union cs) →
      Branches Δ Γ cs τ → Term Δ Γ τ
  /-- An array literal. -/
  | array_mk {Γ : Ctx ks} {t : Ty ks} : Elems Δ Γ t → Term Δ Γ (.array t)
  /-- `Array.foldl`: the step binds the element (index `0`) and the accumulator (index `1`). -/
  | array_foldl {Γ : Ctx ks} {t ρ : Ty ks} : Term Δ Γ (.array t) → Term Δ Γ ρ →
      Term Δ (t :: ρ :: Γ) ρ → Term Δ Γ ρ
  /-- Delay a computation (memoised). -/
  | thunk_mk {Γ : Ctx ks} {t : Ty ks} : Term Δ Γ t → Term Δ Γ (.thunk t)
  /-- Force a memoised delay. -/
  | thunk_force {Γ : Ctx ks} {t : Ty ks} : Term Δ Γ (.thunk t) → Term Δ Γ t
  /-- Delay a computation (unmemoised). -/
  | lazy_mk {Γ : Ctx ks} {t : Ty ks} : Term Δ Γ t → Term Δ Γ (.lazy t)
  /-- Force an unmemoised delay. -/
  | lazy_force {Γ : Ctx ks} {t : Ty ks} : Term Δ Γ (.lazy t) → Term Δ Γ t
  /-- One layer in: a value of member `j` of block `b` from its unfolded body. -/
  | data_in {Γ : Ctx ks} (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      Term Δ Γ ((Δ.block b).unfold j) → Term Δ Γ (.data ((Δ.block b).ref j))
  /-- One layer out: the unfolded body of a value of member `j` of block `b`. -/
  | data_out {Γ : Ctx ks} (b : BRef ks) (j : Fin ((Δ.block b).k + 1)) :
      Term Δ Γ (.data ((Δ.block b).ref j)) → Term Δ Γ ((Δ.block b).unfold j)
  /-- The fold of block `b`, answering `ρ i` at member `i`.  Branch `i` binds member `i`'s
      body in which every hole `i'` is the pair of the subvalue and the answer at it. -/
  | data_rec {Γ : Ctx ks} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
      (branches : (i : Fin ((Δ.block b).k + 1)) → Term Δ ((Δ.block b).recBody ρ i :: Γ) (ρ i))
      (j : Fin ((Δ.block b).k + 1)) :
      Term Δ Γ (.data ((Δ.block b).ref j)) → Term Δ Γ (ρ j)

/-- The arguments of a constructor or an extern. -/
inductive Args {ks : List Nat} (Δ : DSig ks) : Ctx ks → List (Ty ks) → Type where
  | nil {Γ : Ctx ks} : Args Δ Γ []
  | cons {Γ : Ctx ks} {σ : Ty ks} {σs : List (Ty ks)} : Term Δ Γ σ → Args Δ Γ σs →
      Args Δ Γ (σ :: σs)

/-- The branches of a union's case analysis, following its constructors. -/
inductive Branches {ks : List Nat} (Δ : DSig ks) : Ctx ks → Ctors ks → Ty ks → Type where
  | two {Γ : Ctx ks} {c d : Ctor ks} {τ : Ty ks} : Term Δ (c.binds ++ Γ) τ →
      Term Δ (d.binds ++ Γ) τ → Branches Δ Γ (.two c d) τ
  | cons {Γ : Ctx ks} {c : Ctor ks} {cs : Ctors ks} {τ : Ty ks} : Term Δ (c.binds ++ Γ) τ →
      Branches Δ Γ cs τ → Branches Δ Γ (.cons c cs) τ

/-- The elements of an array literal. -/
inductive Elems {ks : List Nat} (Δ : DSig ks) : Ctx ks → Ty ks → Type where
  | nil {Γ : Ctx ks} {t : Ty ks} : Elems Δ Γ t
  | cons {Γ : Ctx ks} {t : Ty ks} : Term Δ Γ t → Elems Δ Γ t → Elems Δ Γ t

end

end Nominal

end LeanScript

end
