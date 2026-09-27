module

public import LeanScript.Term.Eval
public import LeanScript.Term.ExternEval

@[expose] public section

set_option autoImplicit false

/-!
# Building normal-form terms

Abbreviations the elaborators (`[Term| …]`, `#leanscript_to_term`, `#leanscript_get_ctor`,
`#leanscript_get_cases`) write, so that the terms they produce elaborate by unification alone.
Each one unfolds to a constructor of `LeanScript.Term`:

* `Ctors.nth`, `Ctors.ix`, `PExpr.inj`, `Val.inj`: a constructor of a union by position;
* `PExpr.ofNat`: a numeral whose leaf type comes from the expected type;
* `PExpr.externLit`: the value of a call of an extern whose arguments are all closed, as a
  literal (a call with no open argument cannot be a `Neu.extern`);
* `Branch.enumList`: a case analysis of an enum whose branches are listed (the levels of the
  branches differ, so the branch function is a list of dependent pairs);
* `Comp.dataRecS`, `Comp.dataBrecS`: the folds, with their branches as dependent pairs of a
  level and a body;
* the tactic `ls_lvl`, which proves the side condition `m ≤ d` of an open body.
-/

namespace LeanScript

/-- Constructor `i` of a union (a field-less one past the end). -/
def Ctors.nth {ks : List Nat} : {bs : List Bool} → Ctors ks bs → (i : Nat) → Ctor ks (bs.getD i false)
  | _, .two c _, 0 => c
  | _, .two _ d, 1 => d
  | _, .two _ _, _ + 2 => .nullary
  | _, .cons c _, 0 => c
  | _, .cons _ cs, i + 1 => cs.nth i

/-- Constructor `i` of a union is one of its constructors. -/
def Ctors.ix {ks : List Nat} : {bs : List Bool} → (cs : Ctors ks bs) → (i : Nat) →
    i < bs.length → CtorIx cs (cs.nth i)
  | _, .two _ _, 0, _ => .two₁
  | _, .two _ _, 1, _ => .two₂
  | _, .two _ _, _ + 2, h => absurd h (by simp)
  | _, .cons _ _, 0, _ => .head
  | _, .cons _ cs, i + 1, h => .tail (cs.ix i (by simp at h; omega))

section
variable {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks}

/-- Constructor `i` of a union, from its fields: `PExpr.inj 1 (.cons x .nil)`. -/
abbrev PExpr.inj {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {o : Lvl}
    (i : Nat) (hi : i < bs.length := by decide) (args : Args Δ Φ Γ (cs.nth i).binds o) :
    PExpr Δ Φ Γ (.union cs (h := h)) o :=
  .union_mk (cs.ix i hi) args

/-- Constructor `i` of a union, from its fields, as a value bound by `letV`. -/
abbrev Val.inj {d : Nat} {bs : List Bool} {cs : Ctors ks bs} {h : UnionShape bs} {o : Lvl}
    (i : Nat) (hi : i < bs.length := by decide) (args : Args Δ Φ Γ (cs.nth i).binds o) :
    Val Δ d Φ Γ (.union cs (h := h)) o :=
  .union_mk (cs.ix i hi) args

/-- A numeral of a leaf type: `PExpr.ofNat 3 : PExpr Δ Φ Γ .nat none`.  Unlike `PExpr.lit`,
    the leaf is found by unification with the expected type. -/
abbrev PExpr.ofNat {p : LeanPrimTy} (n : Nat) [OfNat p.denote n] : PExpr Δ Φ Γ (.prim p) none :=
  .lit p (OfNat.ofNat n)

/-- The value of a call of an extern on closed arguments (written with no variable at all), as a
    literal of its leaf result. -/
abbrev PExpr.externLit {σs : List (Ty ks)} {p : LeanPrimTy} (e : Extern ks σs (.prim p))
    (args : Args Δ [] [] σs none) : PExpr Δ Φ Γ (.prim p) none :=
  .lit p (Extern.eval (DSig.refDen Δ) e (args.eval PUnit.unit PUnit.unit))

/-- A case analysis of a neutral enum whose branches are listed: constructor `i` takes
    `brs[i]`, and `dflt` past the end of the list. -/
abbrev Branch.enumList {d : Nat} {s : LeanEnumSchema} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    (e : Neu Δ Φ Γ (.enum s) ℓ) (brs : List ((o : Lvl) × Term Δ d Φ Γ τ js o))
    (dflt : (o : Lvl) × Term Δ d Φ Γ τ js o) :
    Branch Δ d Φ Γ τ js (Lvl.meetL ℓ (Lvl.meetFin s.nOfConstructors (fun i => (brs.getD i.val dflt).1))) :=
  .enum_casesOn e (fun i => (brs.getD i.val dflt).2)

/-- The fold of block `b`, its branches given as pairs of a level and a body. -/
abbrev Comp.dataRecS {d : Nat} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks)
    (us : Fin ((Δ.block b).k + 1) → Usage01ω)
    (branches : (i : Fin ((Δ.block b).k + 1)) →
      (o : Lvl) × Body Δ d Φ Γ [⟨(Δ.block b).recBody ρ i, us i, d + 1⟩] (ρ i) o)
    (j : Fin ((Δ.block b).k + 1)) {oe : Lvl} {ℓ : Nat}
    (e : PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe)
    (h : Lvl.meet oe (Lvl.meetFin _ (fun i => (branches i).1)) = some ℓ) :
    Comp Δ d Φ Γ (ρ j) ℓ :=
  .data_rec b ρ us (os := fun i => (branches i).1) (fun i => (branches i).2) j e h

/-- Course-of-values recursion over block `b`, its branches given as pairs of a level and a
    body. -/
abbrev Comp.dataBrecS {d : Nat} (b : BRef ks) (ρ : Fin ((Δ.block b).k + 1) → Ty ks) (k : Nat)
    (us : Fin ((Δ.block b).k + 1) → Usage01ω)
    (branches : (i : Fin ((Δ.block b).k + 1)) →
      (o : Lvl) × Body Δ d Φ Γ [⟨(Δ.block b).brecBody ρ k i, us i, d + 1⟩] (ρ i) o)
    (j : Fin ((Δ.block b).k + 1)) {oe : Lvl} {ℓ : Nat}
    (e : PExpr Δ Φ Γ (.data ((Δ.block b).ref j)) oe)
    (h : Lvl.meet oe (Lvl.meetFin _ (fun i => (branches i).1)) = some ℓ) :
    Comp Δ d Φ Γ (ρ j) ℓ :=
  .data_brec b ρ k us (os := fun i => (branches i).1) (fun i => (branches i).2) j e h

end

/-- The side condition `m ≤ d` of an open body (`Body.opened`). -/
macro "ls_lvl" : tactic =>
  `(tactic| first
    | decide
    | omega
    | (simp only [LeanScript.Lvl.meetL, LeanScript.Lvl.meet, Nat.min_def]; split <;> omega))

end LeanScript

end
