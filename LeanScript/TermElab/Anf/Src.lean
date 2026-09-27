module

public import LeanScript.Term.Build
public import LeanScript.TermElab.Relvl
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Reduce

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Source trees of the normaliser

The direct-style source trees `Src` that the normaliser (`LeanScript.TermElab.Anf`) takes,
and helpers to build them.
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

/-! ## Source trees -/

/-- The value of a literal, when it is known while normalising. -/
inductive LitVal where
  | nat (n : Nat)
  | bool (b : Bool)
  | other
  deriving Inhabited, Repr, BEq

/-- What the constructor function of a Lean constructor builds (`#leanscript_get_ctor`). -/
inductive CtorKind where
  /-- `false`/`true` of a type of two points. -/
  | bool (b : Bool)
  /-- Constructor `i` of an enum. -/
  | enum (i : Nat)
  /-- The only field of a one-constructor, one-field type: the field itself. -/
  | wrap
  /-- The record of the fields of a one-constructor type. -/
  | record
  /-- The constructor at position `pos` of a union. -/
  | union (pos : Nat)
  deriving Inhabited, Repr

/-- The shape of a constructor function: its kind, and the block and member of `data_in` when
    the type is recursive. -/
structure CtorShape where
  kind : CtorKind
  data? : Option (Lean.Term × Lean.Term) := none
  deriving Inhabited

/-- A direct-style source tree.  Variables and join points are de Bruijn indices of the
    source. -/
inductive Src where
  /-- Variable `i`. -/
  | var (i : Nat)
  /-- A literal (the syntax of a closed `PExpr`), and its value when known. -/
  | lit (stx : Lean.Term) (val : LitVal)
  /-- Constructor `i` of an enum (when known), and its syntax. -/
  | enumMk (i : Option Nat) (stx : Lean.Term)
  /-- A record, from its fields. -/
  | record (args : Array Src)
  /-- A constructor of a union (at position `pos` when known; `ix` a `CtorIx`). -/
  | union (pos : Option Nat) (ix : Lean.Term) (args : Array Src)
  /-- An array literal. -/
  | array (es : Array Src)
  /-- A list literal. -/
  | list (es : Array Src)
  /-- One layer in. -/
  | dataIn (b j : Lean.Term) (e : Src)
  /-- A Lean function of pure expressions, whose level is the smallest of its arguments' (a
      constructor function of `#leanscript_get_ctor`), applied; with its shape when known. -/
  | ctor (f : Lean.Term) (args : Array Src) (shape : Option CtorShape)
  /-- A closed Lean term of type `PExpr`, generic in its contexts. -/
  | embed (stx : Lean.Term)
  /-- One layer out. -/
  | dataOut (b j : Lean.Term) (e : Src)
  /-- The pure conditional. -/
  | cond (c a b : Src)
  /-- A call of an extern (`e` the syntax of an `Extern`). -/
  | extern (e : Lean.Term) (args : Array Src)
  /-- An operand at a given type. -/
  | ascribe (s : Src) (ty : Lean.Term)
  /-- An application. -/
  | app (f a : Src)
  /-- `fun x => body` (`ty?` the type of `x`). -/
  | lam (ty? : Option Lean.Term) (body : Src)
  /-- A delay of `body` (`lazy`: recomputed; else memoised), of contents `τ?`. -/
  | delayMk (lazy : Bool) (τ? : Option Lean.Term) (body : Src)
  /-- The value of a delay. -/
  | force (lazy : Bool) (τ? : Option Lean.Term) (e : Src)
  /-- `Nat.rec`: the step binds the answer (`#0`) and the predecessor (`#1`). -/
  | natRec (τ? : Option Lean.Term) (n z s : Src)
  /-- `Array.foldl`: the step binds the element (`#0`) and the accumulator (`#1`). -/
  | arrayFoldl (a z s : Src)
  /-- The fold of block `b` (course-of-values of depth `k?` when given), one branch per member
      (binding its body). -/
  | dataRec (Δ? : Option Lean.Term) (b ρ : Lean.Term) (k? : Option Lean.Term) (brs : Array Src)
      (j : Lean.Term) (e : Src)
  /-- `let x := v; b`. -/
  | letE (v b : Src)
  /-- Take a record of `n` fields apart; the body binds them (the first field innermost). -/
  | recordCases (scrut : Src) (n : Nat) (body : Src)
  /-- `if c then a else b`. -/
  | ite (ty? : Option Lean.Term) (c a b : Src)
  /-- A case analysis of an enum: branch `k` is the one of constructor `pats[k]`; the last
      branch is the default. -/
  | enumCases (ty? : Option Lean.Term) (scrut : Src) (pats : Array (Option Nat)) (brs : Array Src)
  /-- A case analysis of a union, one branch per constructor (binding its fields). -/
  | unionCases (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src))
  /-- `join j (x : ty) := body; main`: `body` binds `x`, `main` sees the join point `j`. -/
  | join (ty? : Option Lean.Term) (body main : Src)
  /-- Jump to join point `j` of the source. -/
  | jump (j : Nat) (arg : Src)
  deriving Inhabited

/-- The head and the arguments of an application. -/
def Src.spine (s : Src) : Src × List Src :=
  go s []
where
  go : Src → List Src → Src × List Src
    | .app f a, as => go f (a :: as)
    | f, as => (f, as)

/-- The number of leading `fun`s. -/
def Src.lams : Src → Nat
  | .lam _ b => b.lams + 1
  | _ => 0

/-- The types of the first `n` leading `fun`s, and what is under them. -/
def Src.peel : Src → Nat → List (Option Lean.Term) × Src
  | .lam ty? b, n + 1 => let (tys, r) := b.peel n; (ty? :: tys, r)
  | s, _ => ([], s)

/-! ## Building source trees -/

namespace Src

/-- An application of a function value. -/
def apps (f : Src) (as : Array Src) : Src := as.foldl .app f

/-- A literal `PExpr.lit p v`. -/
def lit' (p v : Lean.Term) (val : LitVal := .other) : MetaM Src := do
  return .lit (← `(LeanScript.PExpr.lit $p $v)) val

/-- The literal `true` or `false`. -/
def boolLit (b : Bool) : Src :=
  .lit (if b then Unhygienic.run `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool true)
    else Unhygienic.run `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.bool false)) (.bool b)

/-- Take a record of `n` fields apart. -/
def recordMk (args : Array Src) : Src := .record args

/-- A constructor of a union (`ix` a `CtorIx`, at position `pos` when known). -/
def unionMk (pos? : Option Nat) (ix : Lean.Term) (args : Array Src) : Src := .union pos? ix args

/-- An array literal. -/
def arrayMk (es : Array Src) : Src := .array es

/-- The case analysis of a union. -/
def unionCases' (ty? : Option Lean.Term) (scrut : Src) (brs : Array (Nat × Src)) : Src :=
  .unionCases ty? scrut brs

/-- A memoised delay of `e` (contents `τ`). -/
def thunkMk (τ : Lean.Term) (e : Src) : Src := .delayMk false (some τ) e

/-- The value a memoised delay holds (contents `τ`). -/
def thunkForce (τ : Lean.Term) (e : Src) : Src := .force false (some τ) e

/-- A lazy delay of `e` (contents `τ`). -/
def lazyMk (τ : Lean.Term) (e : Src) : Src := .delayMk true (some τ) e

/-- The value a lazy delay holds (contents `τ`). -/
def lazyForce (τ : Lean.Term) (e : Src) : Src := .force true (some τ) e

end Src

end LeanScript.Anf

end
