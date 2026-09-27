module

public import LeanScript.Eval
public meta import LeanScript.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Fields whose type depends on an earlier field

The language has no dependent types.  A field whose type depends on the value of an earlier
field is read through its *erasure* (`LeanScript.Gen.eraseDeps`): the dependency may only go
through arrows, type arguments, and wrappers of one value whose other fields are proofs
(`Fin n` is `Nat`, `Vector α n` is `Array α`, `{x // p x}` is the type of `x`).

* `Chunk` is a record of a `Nat` and a function `Nat → Nat`.
* `Tele.cons` has two `Nat` fields and the recursive field: `Tele` is a declared datatype.
* `WT α β` (Lean's W-type) is read.  `WT Nat Fin` has a type: its field `Fin a → WT Nat Fin`
  is on the recursive cycle, so it is read as `Nat → Option (WT Nat Fin)` (`finOptArrow`), and
  `a = 0` is a leaf.  `WT Nat (fun _ => Nat)` has no value, in Lean or in the language.

Types of no, one or two values stay refused (`Fin 0`, `Fin 1`, `Fin 2`, a `Unit` field
behind a dependency, …).
-/

namespace DependentFieldTest

open LeanScript

structure Chunk where
  n : Nat
  data : Fin n → Nat

inductive Tele where
  | nil
  | cons (n : Nat) (v : Fin (n + 2)) (rest : Tele)

/-- Lean's own `Sigma`/W-type shape: the arity depends on the shape. -/
inductive WT (α : Type) (β : α → Type) where
  | sup (a : α) (f : β a → WT α β)

leanscript_signature Prog where
  chunk := Chunk
  tele := Tele

/-! ## `Chunk`: a `Nat` and a function `Nat → Nat` -/

example : Prog.chunk = .record .nat (.one (.fn .nat .nat)) := rfl
example : (#leanscript_get_ty Chunk : Ty []) = .record .nat (.one (.fn .nat .nat)) := rfl
example : Ty.Den Prog.Δ Prog.chunk = (Nat × (Nat → Nat)) := rfl

def chunkT : Term DSig.nil [] (#leanscript_get_ty Chunk) :=
  (#leanscript_get_ctor Chunk.mk) (.lit .nat 3) (.lam (.bvar 0))

example : chunkT.run.1 = (3 : Nat) := rfl
example : chunkT.run.2 (7 : Nat) = (7 : Nat) := rfl

def Chunk.size (c : Chunk) : Nat := c.n
def chunkSizeT := #leanscript_to_term Chunk.size
example : (chunkSizeT (Δ := DSig.nil)).run ((3 : Nat), fun (i : Nat) => i + 10) = (3 : Nat) := rfl

/-- `⟨0, h⟩ : Fin c.n` is the number `0`; the proof `h` is erased. -/
def Chunk.first (c : Chunk) : Nat := if h : 0 < c.n then c.data ⟨0, h⟩ else 0
def chunkFirstT := #leanscript_to_term Chunk.first
example : (chunkFirstT (Δ := DSig.nil)).run ((3 : Nat), fun (i : Nat) => i + 10) = (10 : Nat) := rfl
example : (chunkFirstT (Δ := DSig.nil)).run ((0 : Nat), fun (i : Nat) => i + 10) = (0 : Nat) := rfl
#guard (Chunk.first ⟨3, fun i => i.val + 10⟩) == 10

/-! ## `Tele`: a declared datatype whose `cons` has two numbers -/

example : ∃ r, Prog.tele = .data r := ⟨_, rfl⟩

/--
info: DependentFieldTest.Prog.Tele.cons {Γ : Ctx Prog.ks} (x0 x1 : Term Prog.Δ Γ (Ty.prim LeanPrimTy.nat))
  (x2 : Term Prog.Δ Γ (Ty.data (Ref.here 0))) : Term Prog.Δ Γ (Ty.data (Ref.here 0))
-/
#guard_msgs in
#leanscript_get_ctor Tele.cons

def teleT : Term Prog.Δ [] Prog.tele :=
  (#leanscript_get_ctor Tele.cons) (.lit .nat 1) (.lit .nat 2)
    ((#leanscript_get_ctor Tele.cons) (.lit .nat 0) (.lit .nat 1) (#leanscript_get_ctor Tele.nil))

def Tele.total : Tele → Nat
  | .nil => 0
  | .cons n v r => n + v.val + r.total

def teleTotalT := #leanscript_to_term Tele.total
example : teleTotalT.run teleT.run = (4 : Nat) := rfl
#guard (Tele.cons 1 2 (.cons 0 1 .nil)).total == 4

/-- The case analysis binds the two numbers and the rest. -/
def teleHead : Term Prog.Δ [Prog.tele] .nat :=
  (#leanscript_get_cases Tele) (.var .head) (.lit .nat 0) (.var (.tail .head))

example : teleHead.eval (teleT.run, ()) = (2 : Nat) := rfl

/-! ## Other erasures -/

structure V where
  n : Nat
  v : Vector Nat n
  o : Option (Fin n)
  s : {x : Nat // x < n}
  f : (i : Fin n) → Fin (i + 1)

example : (#leanscript_get_ty V : Ty []) =
    .record .nat (.cons (.array .nat) (.cons (Ty.option .nat) (.cons .nat (.one (.fn .nat .nat))))) :=
  rfl

/-- A numeral bound of three or more is `nat`. -/
example : (#leanscript_get_ty (Fin 3) : Ty []) = .nat := rfl

/-! ## `WT Nat Fin`: `Fin`-indexed children on a recursive cycle -/

/- `WT Nat Fin` (`sup (a : Nat) (f : Fin a → WT Nat Fin)`) is the rose tree of `Fin`-indexed
    children: the field `Fin a → WT Nat Fin` is on the recursive cycle, so it is read as
    `Nat → Option (WT Nat Fin)` (`none` from `a` on), and `a = 0` is a leaf. -/
leanscript_signature OkW₁ where
  w := WT Nat Fin

example : ∃ r, OkW₁.w = .data r := ⟨_, rfl⟩

/-! ## Refusals -/


-- A generic `WT α β`: `β` is a family of types, not a type, so it must be given.
/--
error: LeanScript: the parameter `β` of `DependentFieldTest.WT` is not a type; give it as `(β := …)`
-/
#guard_msgs in
#leanscript_get_ctor WT.sup

-- `WT Nat (fun _ => Nat)` has no value in Lean either.
/--
error: LeanScript: these recursive types have no finite value (no grounding order): [WT Nat fun x => Nat]
(an `Array` guards a recursive field, a function field `A → X` does not: every type of the language has values)
-/
#guard_msgs in
leanscript_signature BadW₂ where
  w := WT Nat (fun _ => Nat)

/-- A type computed from the value of a field cannot be erased. -/
structure ByCase where
  b : Bool
  x : cond b Nat String

/--
error: LeanScript: a field of the constructor `DependentFieldTest.ByCase.mk` has the type
  match b with
  | true => Nat
  | false => String
which depends on the value of an earlier field (or of the argument of a dependent arrow) in a way that cannot be erased: only arrows, type arguments, and inductive types with one constructor of one field besides proofs (`Fin n`, `Vector α n`, `{x // p x}`) are erased to a non-dependent type
-/
#guard_msgs in
#leanscript_get_ty ByCase

/-- Types of no, one or two values stay refused, also behind a dependency. -/
structure UnitBehind where
  n : Nat
  u : Fin n → Unit

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
#leanscript_get_ty UnitBehind

/-- error: LeanScript: `Fin 0` has no value -/
#guard_msgs in
#leanscript_get_ty (Fin 0)

/-- error: LeanScript: `Fin 1` has one value -/
#guard_msgs in
#leanscript_get_ty (Fin 1)

/-- error: LeanScript: `Fin 2` has two values: two points are only ever `Bool` -/
#guard_msgs in
#leanscript_get_ty (Fin 2)

end DependentFieldTest
