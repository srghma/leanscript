module
public import LeanScript.Expr.NatRecCtx

@[expose] public section

set_option autoImplicit false

/-!
# The two indices of an optimized term: its grade vector and its head

`LeanScript.Term` is **optimized by construction**: every constructor that could form a
redex carries a proof that it does not.  For those proofs to be statable *inside* the
inductive, the facts they talk about must be indices of it (a constructor cannot call a
function on the type being defined), and two indices suffice:

* `LeanScript.Usage Γ` — the **grade vector** of a term: how many times each variable of
  `Γ` is used.  `Term.letE` demands that its variable is used at least twice;
* `LeanScript.Head` — **what the root of a term is**: a variable, a `fun`, a literal, a
  constructor, or a computation.  `Term.ap` demands that its function is not a `fun`
  (no β-redex), a dispatch on a primitive demands that its scrutinee is not a literal, a
  dispatch on a datatype that its scrutinee is not a constructor, and `Term.letE` that its
  bound expression is a computation (or a constructor, whose fields it shares).

Both indices are *computed* by the constructors, so writing a term looks exactly like
writing a raw one, and every proof argument is discharged by `decide` on closed indices.
-/

namespace LeanScript

/-- A grade vector: how many times each variable of `Γ` is used. -/
def Usage (Γ : Ctx) : Type := (τ : TyWf) → Var Γ τ → Nat

namespace Usage

variable {Γ : Ctx} {σ : TyWf}

/-- No variable is used. -/
def zero : Usage Γ := fun _ _ => 0

/-- Pointwise sum: the uses of two subterms. -/
def add (u v : Usage Γ) : Usage Γ := fun τ x => u τ x + v τ x

/-- Scaling: the uses of a subterm copied `k` times. -/
def smul (k : Nat) (u : Usage Γ) : Usage Γ := fun τ x => k * u τ x

instance : Zero (Usage Γ) := ⟨zero⟩

instance : Add (Usage Γ) := ⟨add⟩

/-- Extend a grade vector by the grade `k` of a newly bound variable. -/
def cons (k : Nat) (u : Usage Γ) : Usage (σ :: Γ) := fun _ x =>
  match x with
  | .head => k
  | .tail y => u _ y

/-- The grade of the innermost variable. -/
def head (u : Usage (σ :: Γ)) : Nat := u σ .head

/-- Forget the innermost variable. -/
def tail (u : Usage (σ :: Γ)) : Usage Γ := fun τ x => u τ x.tail

/-- The grade vector of a single occurrence of `x`. -/
def single : {Γ : Ctx} → {τ : TyWf} → Var Γ τ → Usage Γ
  | _ :: _, _, .head => cons 1 zero
  | _ :: _, _, .tail x => cons 0 (single x)

/-- The grade vector of `let x = e; b`, where `e` has grades `u` and `b` has grades `v`:
    the uses of `b` except `x`, plus the uses of `e` once per use of `x`.  This is the
    usual graded `let` rule — the grade the term would have after inlining `x`. -/
def letU (u : Usage Γ) (v : Usage (σ :: Γ)) : Usage Γ := smul (head v) u + tail v

/-- Forget the variables a branch binds in front of `Γ`: the fields of a constructor, the
    values of a fold, … (`Δ` is innermost first, as a context is). -/
def drop : (Δ : Ctx) → Usage (Δ ++ Γ) → Usage Γ
  | [], u => u
  | _ :: Δ, u => drop Δ (tail u)

/-- Forget the `n` previous answers a fold binds in front of `Γ` (`LeanScript.natRecCtx`). -/
def dropN (τ : TyWf) : (n : Nat) → Usage (natRecCtx τ n Γ) → Usage Γ
  | 0, u => u
  | n + 1, u => dropN τ n (tail u)

end Usage

/-- What the root of a term is.  It is an index of `LeanScript.Term`, computed by the
    constructors, and it is what the proofs that a node is not a redex talk about. -/
inductive Head where
  /-- a variable, or a reference to a declaration of the signature: a name, which costs
      nothing to repeat -/
  | var
  /-- a `fun` -/
  | lam
  /-- a literal: a value of a primitive type, or a constructor of an enum -/
  | lit
  /-- a constructor applied to its fields: a record, a tagged value, an array, a delay, a
      value of a recursive type -/
  | ctor
  /-- a computation: an application, a `let`, a dispatch, a fold or an extern -/
  | comp
  deriving DecidableEq, Repr, Inhabited

namespace Head

/-- Is every one of these heads a literal?  `Term.externCall` asks that not all of its
    arguments are: a call of an extern on literals is folded into `Term.extern`. -/
def allLit : List Head → Bool
  | [] => true
  | k :: ks => (k == .lit) && allLit ks

end Head

end LeanScript

end
