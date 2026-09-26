module

public import LeanScript.Two
public import LeanScript.Eval
public meta import LeanScript.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# `#leanscript_get_ty` and `#leanscript_get_ctor`

Structural types need no signature: their types and constructor functions are generic in it.
Recursive types are members of the current program's signature (`leanscript_signature`),
and their constructor functions are `data_in` of the payload.  Every generated definition is
cached: asking again gives the same constant.
-/

namespace GetCtorTest

open LeanScript

inductive Color where
  | red | green | blue

structure Point where
  x : Nat
  y : Int

/-- A structure with a proof field, which is erased. -/
structure Pos where
  n : Nat
  pos : 0 < n
  tag : String

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

inductive Rose where
  | node : Nat → List Rose → Rose

/-! ## Structural types: generic in the signature -/

/--
info: TyTests.GetCtorTest.Option.some.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (α : Ty ks)
  (x0 : Term Δ Γ α) : Term Δ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α))))
-/
#guard_msgs in
#leanscript_get_ctor Option.some

/--
info: TyTests.GetCtorTest.Option.none.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (α : Ty ks) :
  Term Δ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α))))
-/
#guard_msgs in
#leanscript_get_ctor Option.none

/--
info: TyTests.GetCtorTest.Prod.mk.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (α β : Ty ks) (x0 : Term Δ Γ α)
  (x1 : Term Δ Γ β) : Term Δ Γ (α.record (Fields.one β))
-/
#guard_msgs in
#leanscript_get_ctor Prod.mk

/-- A parameter given by name is fixed; the others stay arguments. -/
example : Term .nil [] (.record .nat (.one .bool)) :=
  (#leanscript_get_ctor Prod.mk (α := Nat)) _ (.lit .nat rfl 1) (#leanscript_get_ctor Bool.true)

/-- `Bool` is a leaf: its constructors are literals. -/
example : (#leanscript_get_ctor Bool.false : Term DSig.nil [] .bool).run = false := rfl

/-- Three or more constructors without fields are an enum; `Ordering` numbers from `-1`. -/
example : (#leanscript_get_ty Ordering : Ty []) = .enum ⟨0, -1⟩ := rfl
example : (#leanscript_get_ctor Ordering.gt : Term DSig.nil [] (.enum ⟨0, -1⟩)).run = (2 : Fin 3) := rfl
example : (#leanscript_get_ctor Color.green : Term DSig.nil [] (.enum ⟨0, 0⟩)).run = (1 : Fin 3) := rfl

/-- One constructor with two or more fields is a record; `#leanscript_get_ctor Point` names
    its only constructor. -/
example : (#leanscript_get_ty Point : Ty []) = .record .nat (.one .int) := rfl
example : ((#leanscript_get_ctor Point) (.lit .nat rfl 1) (.lit .int rfl (-2)) :
    Term DSig.nil [] _).run = ((1 : Nat), (-2 : Int)) := rfl

/-- The proof field is erased. -/
example : (#leanscript_get_ty Pos : Ty []) = .record .nat (.one .string) := rfl

-- The cache: the same request gives the same constant (no `_1` suffix)…
/--
info: TyTests.GetCtorTest.Option.some.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (α : Ty ks)
  (x0 : Term Δ Γ α) : Term Δ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α))))
-/
#guard_msgs in
#leanscript_get_ctor Option.some

-- …and `#leanscript_get_ty` of a constructor's type is the type it builds.
example : (#leanscript_get_ty (Option Nat) : Ty []) = Ty.option .nat := rfl

def someT : Term DSig.nil [] (#leanscript_get_ty (Option Nat)) :=
  (#leanscript_get_ctor Option.some) _ (.lit .nat rfl 2)

example : someT.run = some (2 : Nat) := rfl

/-! ## Recursive types: members of the current program -/

leanscript_signature Prog where
  listNat := List Nat
  tree := Tree
  rose := Rose

/--
info: GetCtorTest.Prog.Tree.node {Γ : Ctx Prog.ks} (x0 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there))
  (x1 : Term Prog.Δ Γ (Ty.prim LeanPrimTy.nat ⋯)) (x2 : Term Prog.Δ Γ (Ty.data (Ref.here 0).there)) :
  Term Prog.Δ Γ (Ty.data (Ref.here 0).there)
-/
#guard_msgs in
#leanscript_get_ctor Tree.node

/-- `#leanscript_get_ty` of a recursive type is its name in the program. -/
example : (#leanscript_get_ty Tree) = Prog.tree := rfl
example : (#leanscript_get_ty (List Nat)) = Prog.listNat := rfl

/-- A structural type around a recursive one is specialised to the program. -/
example : (#leanscript_get_ty (Option Tree)) = Ty.option Prog.tree := rfl

def leaf : Term Prog.Δ [] Prog.tree := #leanscript_get_ctor Tree.leaf

def treeT : Term Prog.Δ [] Prog.tree :=
  (#leanscript_get_ctor Tree.node) ((#leanscript_get_ctor Tree.node) leaf (.lit .nat rfl 1) leaf)
    (.lit .nat rfl 2) leaf

/-- The sum of a tree, by the fold of its block. -/
def treeSum (t : Ty.Den Prog.Δ Prog.tree) : Nat :=
  Prog.Δ.dataRec (.there .here) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option ((Ty.Den Prog.Δ Prog.tree × Nat) × Nat ×
          (Ty.Den Prog.Δ Prog.tree × Nat))) with
        | none => 0
        | some ((_, a), n, (_, b)) => Nat.add (Nat.add a n) b
      r) 0 t

example : treeSum treeT.run = 3 := rfl

/-- The type parameter of a recursive type is fixed by name. -/
def listT : Term Prog.Δ [] Prog.listNat :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 7)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat rfl 8)
      (#leanscript_get_ctor List.nil (α := Nat)))

/-- The sum of a list, by the fold of its block. -/
def listSum (l : Ty.Den Prog.Δ Prog.listNat) : Nat :=
  Prog.Δ.dataRec (.there (.there .here)) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × Ty.Den Prog.Δ Prog.listNat × Nat)) with
        | none => 0
        | some (a, _, s) => Nat.add a s
      r) 0 l

example : listSum listT.run = 15 := rfl

/-- `Rose`'s children are a `List Rose`: another member of `Rose`'s block. -/
def roseT : Term Prog.Δ [] Prog.rose :=
  (#leanscript_get_ctor Rose.node) (.lit .nat rfl 1)
    ((#leanscript_get_ctor List.cons (α := Rose))
      ((#leanscript_get_ctor Rose.node) (.lit .nat rfl 2) (#leanscript_get_ctor List.nil (α := Rose)))
      (#leanscript_get_ctor List.nil (α := Rose)))

/-! ## Case analysis: `#leanscript_get_cases` -/

/--
info: TyTests.GetCtorTest.Option.leanScriptCases {ks : List Nat} {Δ : DSig ks} {Γ : Ctx ks} (α : Ty ks) {τ : Ty ks}
  (scrut : Term Δ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α))))) (on_none : Term Δ Γ τ)
  (on_some : Term Δ (α :: Γ) τ) : Term Δ Γ τ
-/
#guard_msgs in
#leanscript_get_cases Option

/-- `Option.getD x 0`: the `some` branch binds the field. -/
def getD0 : Term DSig.nil [Ty.option .nat] .nat :=
  (#leanscript_get_cases Option) _ (.var .head) (.lit .nat rfl 0) (.var .head)

example : getD0.eval (some (5 : Nat), ()) = (5 : Nat) := rfl
example : getD0.eval (none, ()) = (0 : Nat) := rfl

/-- A record binds all its fields, the first one innermost. -/
def pointX : Term DSig.nil [#leanscript_get_ty Point] .nat :=
  (#leanscript_get_cases Point) (.var .head) (.var .head)

example : pointX.eval (((3 : Nat), (-1 : Int)), ()) = (3 : Nat) := rfl

/-- `Bool` is `ite`, `Ordering` an enum case analysis. -/
def notT : Term DSig.nil [.bool] .bool :=
  (#leanscript_get_cases Bool) (.var .head) (#leanscript_get_ctor Bool.true)
    (#leanscript_get_ctor Bool.false)

example : notT.eval (true, ()) = false := rfl

def ordT : Term DSig.nil [#leanscript_get_ty Ordering] .nat :=
  (#leanscript_get_cases Ordering) (.var .head) (.lit .nat rfl 10) (.lit .nat rfl 20)
    (.lit .nat rfl 30)

example : ordT.eval ((1 : Fin 3), ()) = (20 : Nat) := rfl

/-- For a recursive type the case analysis is `data_out` followed by the case analysis of
    the unfolded body. -/
def isLeaf : Term Prog.Δ [Prog.tree] .bool :=
  (#leanscript_get_cases Tree) (.var .head) (#leanscript_get_ctor Bool.true)
    (#leanscript_get_ctor Bool.false)

example : isLeaf.eval (leaf.run, ()) = true := rfl
example : isLeaf.eval (treeT.run, ()) = false := rfl

/-- The root label of a tree: the `node` branch binds its three fields. -/
def rootLabel : Term Prog.Δ [Prog.tree] .nat :=
  (#leanscript_get_cases Tree) (.var .head) (.lit .nat rfl 0) (.var (.tail .head))

example : rootLabel.eval (treeT.run, ()) = (2 : Nat) := rfl

/-! ## Refusals -/

/--
error: LeanScript: the layout of
  List α
is recursive and depends on a type parameter; fix the parameter with a named argument `(α := …)`
-/
#guard_msgs in
#leanscript_get_ctor List.cons

/-- An instance of a recursive type that the program does not declare. -/
inductive Other where
  | a : Other
  | b : Other → Other

/--
error: LeanScript: the recursive type
  Other
is not declared in the signature `GetCtorTest.Prog`; add it to `leanscript_signature GetCtorTest.Prog`
-/
#guard_msgs in
#leanscript_get_ctor Other.b

/-! ## Several programs -/

-- A second program declares `Other` and becomes the current one…
leanscript_signature Prog₂ where
  other := Other

example : Term Prog₂.Δ [] Prog₂.other :=
  (#leanscript_get_ctor Other.b) (#leanscript_get_ctor Other.a)

-- …until the first one is chosen again.
leanscript_use_signature Prog

example : Term Prog.Δ [] Prog.tree := #leanscript_get_ctor Tree.leaf

/--
error: LeanScript: `Nat` is a leaf of the language: its values are literals, not constructor applications
-/
#guard_msgs in
#leanscript_get_ctor Nat.succ

/--
error: LeanScript: `Option` has 2 constructors; name the one you mean
-/
#guard_msgs in
#leanscript_get_ctor Option

/--
error: LeanScript: `Prod` has no parameter named [γ]
-/
#guard_msgs in
#leanscript_get_ctor Prod.mk (γ := Nat)

end GetCtorTest

end
