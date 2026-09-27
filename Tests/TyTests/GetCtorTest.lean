module

public import LeanScript.Ty.Two
public import LeanScript.Term.Build
public meta import LeanScript.GenElab.GetCtor

@[expose] public section

set_option autoImplicit false

/-!
# `#leanscript_get_ty` and `#leanscript_get_ctor`

Structural types need no signature: their types and constructor functions are generic in it.
Recursive types are members of the current program's signature (`leanscript_signature`),
and their constructor functions are `data_in` of the payload.  A constructor function builds
a pure expression (`PExpr`) from pure expressions; a case analysis takes a neutral scrutinee and
statements (`Term`) as its branches.  Every generated definition is
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
info: TyTests.GetCtorTest.Option.some.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α : Ty ks)
  {o0 : Lvl} (x0 : PExpr Δ Φ Γ α o0) :
  PExpr Δ Φ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α)))) (o0.meet none)
-/
#guard_msgs in
#leanscript_get_ctor Option.some

/--
info: TyTests.GetCtorTest.Option.none.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α : Ty ks) :
  PExpr Δ Φ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α)))) none
-/
#guard_msgs in
#leanscript_get_ctor Option.none

/--
info: TyTests.GetCtorTest.Prod.mk.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α β : Ty ks)
  {o0 o1 : Lvl} (x0 : PExpr Δ Φ Γ α o0) (x1 : PExpr Δ Φ Γ β o1) :
  PExpr Δ Φ Γ (α.record (Fields.one β)) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor Prod.mk

/-- A parameter given by name is fixed; the others stay arguments. -/
example : PExpr .nil [] [] (.record .nat (.one .bool)) none :=
  (#leanscript_get_ctor Prod.mk (α := Nat)) _ (.lit .nat 1) (#leanscript_get_ctor Bool.true)

-- [SKIPPED BY PROFILE_LAKE] /-- `Bool` is a leaf: its constructors are literals. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ctor Bool.false : PExpr DSig.nil [] [] .bool none).run = false := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- Three or more constructors without fields are an enum; `Ordering` numbers from `-1`. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty Ordering : Ty []) = .enum ⟨0, -1⟩ := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ctor Ordering.gt : PExpr DSig.nil [] [] (.enum ⟨0, -1⟩) none).run = (2 : Fin 3) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ctor Color.green : PExpr DSig.nil [] [] (.enum ⟨0, 0⟩) none).run = (1 : Fin 3) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- One constructor with two or more fields is a record; `#leanscript_get_ctor Point` names
-- [SKIPPED BY PROFILE_LAKE]     its only constructor. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty Point : Ty []) = .record .nat (.one .int) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ((#leanscript_get_ctor Point) (.lit .nat 1) (.lit .int (-2)) :
-- [SKIPPED BY PROFILE_LAKE]     PExpr DSig.nil [] [] _ none).run = ((1 : Nat), (-2 : Int)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- The proof field is erased. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty Pos : Ty []) = .record .nat (.one .string) := rfl

-- The cache: the same request gives the same constant (no `_1` suffix)…
/--
info: TyTests.GetCtorTest.Option.some.leanScriptCtor {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α : Ty ks)
  {o0 : Lvl} (x0 : PExpr Δ Φ Γ α o0) :
  PExpr Δ Φ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α)))) (o0.meet none)
-/
#guard_msgs in
#leanscript_get_ctor Option.some

-- …and `#leanscript_get_ty` of a constructor's type is the type it builds.
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Option Nat) : Ty []) = Ty.option .nat := rfl

def someT : PExpr DSig.nil [] [] (#leanscript_get_ty (Option Nat)) none :=
  (#leanscript_get_ctor Option.some) _ (.lit .nat 2)

-- [SKIPPED BY PROFILE_LAKE] example : someT.run = some (2 : Nat) := rfl

/-! ## Recursive types: members of the current program -/

leanscript_signature Prog where
  listNat := List Nat
  tree := Tree
  rose := Rose

/--
info: GetCtorTest.Prog.Tree.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 o2 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o0) (x1 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o1)
  (x2 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) o2) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there) (o0.meet (o1.meet (o2.meet none)))
-/
#guard_msgs in
#leanscript_get_ctor Tree.node

-- [SKIPPED BY PROFILE_LAKE] /-- `#leanscript_get_ty` of a recursive type is its name in the program. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty Tree) = Prog.tree := rfl
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (List Nat)) = Prog.listNat := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A structural type around a recursive one is specialised to the program. -/
-- [SKIPPED BY PROFILE_LAKE] example : (#leanscript_get_ty (Option Tree)) = Ty.option Prog.tree := rfl

def leaf : PExpr Prog.Δ [] [] Prog.tree none := #leanscript_get_ctor Tree.leaf

def treeT : PExpr Prog.Δ [] [] Prog.tree none :=
  (#leanscript_get_ctor Tree.node) ((#leanscript_get_ctor Tree.node) leaf (.lit .nat 1) leaf)
    (.lit .nat 2) leaf

/-- The sum of a tree, by the fold of its block. -/
def treeSum (t : Ty.Den Prog.Δ Prog.tree) : Nat :=
  Prog.Δ.dataRec (.there .here) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option ((Ty.Den Prog.Δ Prog.tree × Nat) × Nat ×
          (Ty.Den Prog.Δ Prog.tree × Nat))) with
        | none => 0
        | some ((_, a), n, (_, b)) => Nat.add (Nat.add a n) b
      r) 0 t

-- [SKIPPED BY PROFILE_LAKE] example : treeSum treeT.run = 3 := rfl

/-- The type parameter of a recursive type is fixed by name. -/
def listT : PExpr Prog.Δ [] [] Prog.listNat none :=
  (#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 7)
    ((#leanscript_get_ctor List.cons (α := Nat)) (.lit .nat 8)
      (#leanscript_get_ctor List.nil (α := Nat)))

/-- The sum of a list, by the fold of its block. -/
def listSum (l : Ty.Den Prog.Δ Prog.listNat) : Nat :=
  Prog.Δ.dataRec (.there (.there .here)) (fun _ => .nat) (fun
    | ⟨0, _⟩, x =>
      let r : Nat := match (x : Option (Nat × Ty.Den Prog.Δ Prog.listNat × Nat)) with
        | none => 0
        | some (a, _, s) => Nat.add a s
      r) 0 l

-- [SKIPPED BY PROFILE_LAKE] example : listSum listT.run = 15 := rfl

/-- `Rose`'s children are a `List Rose`: another member of `Rose`'s block. -/
def roseT : PExpr Prog.Δ [] [] Prog.rose none :=
  (#leanscript_get_ctor Rose.node) (.lit .nat 1)
    ((#leanscript_get_ctor List.cons (α := Rose))
      ((#leanscript_get_ctor Rose.node) (.lit .nat 2) (#leanscript_get_ctor List.nil (α := Rose)))
      (#leanscript_get_ctor List.nil (α := Rose)))

/-! ## Case analysis: `#leanscript_get_cases` -/

/--
info: TyTests.GetCtorTest.Option.leanScriptCases {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} (α : Ty ks)
  {d : Nat} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} {o0 o1 : Lvl}
  (scrut : Neu Δ Φ Γ (Ty.union (Ctors.two Ctor.nullary (Ctor.fields (Fields.one α)))) ℓ)
  (on_none : Term Δ d Φ (UCtx.annot d [] [] ++ Γ) τ js o0) (on_some : Term Δ d Φ (UCtx.annot d [α] [] ++ Γ) τ js o1) :
  Term Δ d Φ Γ τ js (some (Lvl.meetL ℓ (o0.meet o1)))
-/
#guard_msgs in
#leanscript_get_cases Option

/-- Statements with one unknown of type `σ`. -/
abbrev T1 {ks : List Nat} (Δ : DSig ks) (σ τ : Ty ks) : Type := Term Δ 0 [] [⟨σ, .many, 0⟩] τ [] (some 0)

/-- The innermost unknown. -/
abbrev x0 {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ (⟨τ, .many, ℓ⟩ :: Γ) τ ℓ :=
  .var (.head (by decide))

/-- The unknown one binder further out. -/
abbrev x1 {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    {b : UBinder ks} : Neu Δ Φ (b :: ⟨τ, .many, ℓ⟩ :: Γ) τ ℓ :=
  .var (.tail (.head (by decide)))

/-- `Option.getD x 0`: the `some` branch binds the field. -/
def getD0 : T1 DSig.nil (Ty.option .nat) .nat :=
  (#leanscript_get_cases Option) _ x0 (.ret (.lit .nat 0)) (.ret (.neu x0))

-- [SKIPPED BY PROFILE_LAKE] example : getD0.eval PUnit.unit (some (5 : Nat)) PUnit.unit = (5 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : getD0.eval PUnit.unit none PUnit.unit = (0 : Nat) := rfl

/-- A record binds all its fields, the first one innermost. -/
def pointX : T1 DSig.nil (#leanscript_get_ty Point) .nat :=
  (#leanscript_get_cases Point) x0 (.ret (.neu x0))

-- [SKIPPED BY PROFILE_LAKE] example : pointX.eval PUnit.unit ((3 : Nat), (-1 : Int)) PUnit.unit = (3 : Nat) := rfl

/-- `Bool` is `ite`, `Ordering` an enum case analysis. -/
def notT : T1 DSig.nil .bool .bool :=
  (#leanscript_get_cases Bool) x0 (.ret (#leanscript_get_ctor Bool.true))
    (.ret (#leanscript_get_ctor Bool.false))

-- [SKIPPED BY PROFILE_LAKE] example : notT.eval PUnit.unit true PUnit.unit = false := rfl

def ordT : T1 DSig.nil (#leanscript_get_ty Ordering) .nat :=
  (#leanscript_get_cases Ordering) x0 (.ret (.lit .nat 10)) (.ret (.lit .nat 20))
    (.ret (.lit .nat 30))

-- [SKIPPED BY PROFILE_LAKE] example : ordT.eval PUnit.unit (1 : Fin 3) PUnit.unit = (20 : Nat) := rfl

/-- For a recursive type the case analysis is `data_out` followed by the case analysis of
    the unfolded body. -/
def isLeaf : T1 Prog.Δ Prog.tree .bool :=
  (#leanscript_get_cases Tree) x0 (.ret (#leanscript_get_ctor Bool.true))
    (.ret (#leanscript_get_ctor Bool.false))

-- [SKIPPED BY PROFILE_LAKE] example : isLeaf.eval PUnit.unit leaf.run PUnit.unit = true := rfl
-- [SKIPPED BY PROFILE_LAKE] example : isLeaf.eval PUnit.unit treeT.run PUnit.unit = false := rfl

/-- The root label of a tree: the `node` branch binds its three fields. -/
def rootLabel : T1 Prog.Δ Prog.tree .nat :=
  (#leanscript_get_cases Tree) x0 (.ret (.lit .nat 0)) (.ret (.neu x1))

-- [SKIPPED BY PROFILE_LAKE] example : rootLabel.eval PUnit.unit treeT.run PUnit.unit = (2 : Nat) := rfl

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

example : PExpr Prog₂.Δ [] [] Prog₂.other none :=
  (#leanscript_get_ctor Other.b) (#leanscript_get_ctor Other.a)

-- …until the first one is chosen again.
leanscript_use_signature Prog

example : PExpr Prog.Δ [] [] Prog.tree none := #leanscript_get_ctor Tree.leaf

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
