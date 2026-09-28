module

public import LeanScript.Ty.Den.Two
public import LeanScript.Term.Build
public import LeanScript.TacticElab.KernelRfl
public meta import LeanScript.TermElab.ToTerm

@[expose] public section

set_option autoImplicit false

/-!
# Structured container elements (`T5`) and the three rose trees

* `T5 := node (Array (Option T5 × Nat))` is a block of three members, in grounding order:
  `T5` itself (a wrapper of an `Array`: the empty array is its base), then the generated
  members `Option T5` (base `none`) and `Option T5 × Nat` (a record).  The array's elements are
  the third member.  So `T5` is handled like `RoseA := node (Array RoseA)`, with the structure
  inside the array flattened into members of the block.
* The three rose trees are three different datatypes, and so are their parameterised versions
  `RoseTreeL α`, `RoseTreeA α` and `RoseTreeF α`:

  | Lean | block | the children |
  | :-- | :-- | :-- |
  | `node : List RoseL → RoseL` | `List RoseL := nil \| cons RoseL (List RoseL)`, then `RoseL` | a linked list: a value of the member `List RoseL` |
  | `node : Array RoseA → RoseA` | `RoseA` | a `Ty.array` of `RoseA` |
  | `node : (m : Nat) → (Fin m → RoseF) → RoseF` | `Option RoseF := none \| some RoseF`, then `RoseF` | a record of two fields: `.nat` and a function `.nat → Option RoseF` |

  The third one cannot be the record `.nat × (.nat → RoseF)`: every value of `Nat → RoseF`
  needs a `RoseF` already, so that type has no finite value (it is refused: every type of the
  language has values).  Its function field is read as `Nat → Option RoseF` instead
  (`LeanScript.Gen.finOptArrow`): the children are `some` below `m` and `none` from `m` on, and
  `m = 0` is a leaf (`fun _ => none`).  This happens only for a `Fin m → T` whose bound `m` is an
  earlier field and whose `T` is on a recursive cycle through the constructor's type;
  `Chunk.data : Fin n → Nat` stays `Nat → Nat`.  The same holds when the two fields are packed
  in a `Σ` (`node : ((m : Nat) × (Fin m → RoseS)) → RoseS`) and for Lean's W-type `WT Nat Fin`
  (`TermTests/ToTerm/DependentFieldTest.lean`).
* `#leanscript_to_term` translates values and functions of all of them: an array literal
  `#[a, b]` of values that are not leaves is `PExpr.array_mk`; `Fin.foldl m step z` is
  `Comp.nat_rec` on `m`; a recursive call on `f i` for a field `f : Fin m → RoseF` reads the
  answer at `f i` (the fold's answer at the member `Option RoseF` is `none` or `some` of the
  answer at the `RoseF` inside); `f i` itself is taken apart after `data_out`, and its
  unreachable `none` branch is the `Inhabited` default of the type (refused when there is
  none).
* Types with no, one or two values stay refused (`RoseTreeL Unit`, `RoseTreeF Empty`, …).
-/

namespace RoseVariantsTest

open LeanScript

/-- Section 5 of `proposals/UnrepresentableLeanTypes.lean`: structure inside a container
    element. -/
inductive T5 where
  | node : Array (Option T5 × Nat) → T5

/-- A rose tree whose children are a linked list. -/
inductive RoseL where
  | node : List RoseL → RoseL

/-- A rose tree whose children are an array. -/
inductive RoseA where
  | node : Array RoseA → RoseA

/-- A rose tree whose children are a function on `Fin m`. -/
inductive RoseF where
  | node : (m : Nat) → (Fin m → RoseF) → RoseF

inductive RoseTreeL (α : Type) where
  | node : α → List (RoseTreeL α) → RoseTreeL α

inductive RoseTreeA (α : Type) where
  | node : α → Array (RoseTreeA α) → RoseTreeA α

inductive RoseTreeF (α : Type) where
  | node : α → (m : Nat) → (Fin m → RoseTreeF α) → RoseTreeF α

/-- The children of `RoseF`, packed in a `Σ`. -/
inductive RoseS where
  | node : ((m : Nat) × (Fin m → RoseS)) → RoseS

leanscript_signature Prog where
  t5 := T5
  roseL := RoseL
  roseA := RoseA
  roseF := RoseF
  treeL := RoseTreeL Nat
  treeA := RoseTreeA Nat
  treeF := RoseTreeF Nat
  roseS := RoseS

/-! ## The blocks -/

/-- Eight blocks, one per requested recursive type (newest first): `RoseS` (3 members),
    `RoseTreeF Nat` (2), `RoseTreeA Nat` (1), `RoseTreeL Nat` (2), `RoseF` (2), `RoseA` (1),
    `RoseL` (2), `T5` (3). -/
example : Prog.ks = [2, 1, 0, 1, 1, 0, 1, 2] := rfl

/-- `T5`: `T5 := [Option T5 × Nat]` (the array is the guard), `Option T5 := none | some T5`,
    `Option T5 × Nat := (Option T5, Nat)`. -/
example : Prog.block0 =
    .cons (.wrap (.array (.hole 2 (by decide))))
      (.cons (.union (.two₁ .nullary (.fields (.one (.hole 0 (by decide))))))
        (.cons (.record (.hole 1 (by decide)) (.one (.old .nat))) .nil)) := rfl

/-- `RoseL`: the linked list `List RoseL := nil | cons RoseL (List RoseL)`, then `RoseL`, a
    wrapper of it. -/
example : Prog.block1 =
    .cons (.union (.two₁ .nullary (.fields (.cons (.hole 1 (by decide)) (.one (.hole 0 (by decide)))))))
      (.cons (.wrap (.hole 0 (by decide))) .nil) := rfl

/-- `RoseA`: a wrapper of a `Ty.array` of itself. -/
example : Prog.block2 = .cons (.wrap (.array (.hole 0 (by decide)))) .nil := rfl

/-- `RoseF`: `Option RoseF := none | some RoseF`, then `RoseF := (Nat, Nat → Option RoseF)`. -/
example : Prog.block3 =
    .cons (.union (.two₁ .nullary (.fields (.one (.hole 1 (by decide))))))
      (.cons (.record (.old .nat) (.one (.fn .nat (.hole 0 (by decide))))) .nil) := rfl

/-- `RoseTreeL Nat`: `List (RoseTreeL Nat)`, then `(Nat, List (RoseTreeL Nat))`. -/
example : Prog.block4 =
    .cons (.union (.two₁ .nullary (.fields (.cons (.hole 1 (by decide)) (.one (.hole 0 (by decide)))))))
      (.cons (.record (.old .nat) (.one (.hole 0 (by decide)))) .nil) := rfl

/-- `RoseTreeA Nat`: `(Nat, Array (RoseTreeA Nat))`. -/
example : Prog.block5 = .cons (.record (.old .nat) (.one (.array (.hole 0 (by decide))))) .nil := rfl

/-- `RoseTreeF Nat`: `Option (RoseTreeF Nat)`, then `(Nat, Nat, Nat → Option (RoseTreeF Nat))`. -/
example : Prog.block6 =
    .cons (.union (.two₁ .nullary (.fields (.one (.hole 1 (by decide))))))
      (.cons (.record (.old .nat) (.cons (.old .nat) (.one (.fn .nat (.hole 0 (by decide)))))) .nil) :=
  rfl

/-- `RoseS`: `Option RoseS`, the `Σ` as the record `(Nat, Nat → Option RoseS)`, then `RoseS`, a
    wrapper of it. -/
example : Prog.block7 =
    .cons (.union (.two₁ .nullary (.fields (.one (.hole 2 (by decide))))))
      (.cons (.record (.old .nat) (.one (.fn .nat (.hole 0 (by decide)))))
        (.cons (.wrap (.hole 1 (by decide))) .nil)) := rfl

/-- The three rose trees are three different datatypes. -/
example : Prog.roseL ≠ Prog.roseA ∧ Prog.roseA ≠ Prog.roseF ∧ Prog.roseL ≠ Prog.roseF := by
  decide

/-- Every type of the program has two different values. -/
example : ∃ x y : Ty.Den Prog.Δ Prog.roseF, x ≠ y := Ty.den_exists_ne _ _
example : ∃ x y : Ty.Den Prog.Δ Prog.t5, x ≠ y := Ty.den_exists_ne _ _

/-! ## The constructors: what the children are -/

/--
info: RoseVariantsTest.Prog.RoseL.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there.there.there.there.there.there) o0) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 1).there.there.there.there.there.there) o0
-/
#guard_msgs in
#leanscript_get_ctor RoseL.node

/--
info: RoseVariantsTest.Prog.RoseA.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there.there.there.there.there).array o0) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there.there.there.there.there) o0
-/
#guard_msgs in
#leanscript_get_ctor RoseA.node

/--
info: RoseVariantsTest.Prog.RoseF.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 o1 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.prim LeanPrimTy.nat) o0)
  (x1 : PExpr Prog.Δ Φ Γ ((Ty.prim LeanPrimTy.nat).fn (Ty.data (Ref.here 0).there.there.there.there)) o1) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 1).there.there.there.there) (o0.meet (o1.meet none))
-/
#guard_msgs in
#leanscript_get_ctor RoseF.node

/--
info: RoseVariantsTest.Prog.T5.node {Φ : KCtx Prog.ks} {Γ : UCtx Prog.ks} {o0 : Lvl}
  (x0 : PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 2).there.there.there.there.there.there.there).array o0) :
  PExpr Prog.Δ Φ Γ (Ty.data (Ref.here 0).there.there.there.there.there.there.there) o0
-/
#guard_msgs in
#leanscript_get_ctor T5.node

/-! ## `T5` -/

mutual
def T5.sum : T5 → Nat
  | .node cs => cs.foldl (fun acc p => acc + T5.sumP p) 0
def T5.sumP : Option T5 × Nat → Nat
  | (o, n) => T5.sumO o + n
def T5.sumO : Option T5 → Nat
  | none => 0
  | some t => t.sum
end

def t5v : T5 := .node #[(some (.node #[(none, 3)]), 4), (none, 5)]

#guard t5v.sum == 12

def t5SumT := #leanscript_to_term T5.sum
/-- An array literal of values that are not leaves is `PExpr.array_mk`. -/
def t5T : Term Prog.Δ 0 [] [] Prog.t5 [] none := #leanscript_to_term t5v

example : t5SumT.run t5T.run = (12 : Nat) := by kernel_rfl

/-! ## `RoseL`: a linked list of children -/

mutual
def RoseL.size : RoseL → Nat
  | .node cs => 1 + RoseL.sizeList cs
def RoseL.sizeList : List RoseL → Nat
  | [] => 0
  | r :: rs => r.size + RoseL.sizeList rs
end

def roseLv : RoseL := .node [.node [], .node [.node []]]

#guard roseLv.size == 4

def roseLSizeT := #leanscript_to_term RoseL.size
def roseLT : Term Prog.Δ 0 [] [] Prog.roseL [] none := #leanscript_to_term roseLv

example : roseLSizeT.run roseLT.run = (4 : Nat) := by kernel_rfl

/-! ## `RoseA`: an array of children -/

def RoseA.size : RoseA → Nat
  | .node cs => cs.foldl (fun acc c => acc + c.size) 1

def roseAv : RoseA := .node #[.node #[], .node #[.node #[]]]

#guard roseAv.size == 4

def roseASizeT := #leanscript_to_term RoseA.size
def roseAT : Term Prog.Δ 0 [] [] Prog.roseA [] none := #leanscript_to_term roseAv

example : roseASizeT.run roseAT.run = (4 : Nat) := by kernel_rfl

/-! ## `RoseF`: children as a function on `Fin m` -/

def RoseF.size : RoseF → Nat
  | .node m f => Fin.foldl m (fun acc i => acc + (f i).size) 1

def RoseF.depth : RoseF → Nat
  | .node m f => Fin.foldl m (fun acc i => max acc ((f i).depth + 1)) 0

def RoseF.arity : RoseF → Nat
  | .node m _ => m

def roseFv : RoseF := .node 2 (fun _ => .node 3 (fun _ => .node 0 Fin.elim0))

#guard roseFv.size == 9
#guard roseFv.depth == 2

def roseFSizeT := #leanscript_to_term RoseF.size
def roseFDepthT := #leanscript_to_term RoseF.depth
def roseFArityT := #leanscript_to_term RoseF.arity
/-- `fun _ => …` on `Fin 2` is `fun j => if j < 2 then some … else none`; `Fin.elim0` (on
    `Fin 0`) is `fun _ => none`. -/
def roseFT : Term Prog.Δ 0 [] [] Prog.roseF [] none := #leanscript_to_term roseFv

-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)
example : roseFArityT.run roseFT.run = (2 : Nat) := by kernel_rfl

def RoseF.firstArity₀ : RoseF → Nat
  | .node m f => if h : 0 < m then match f ⟨0, h⟩ with | .node k _ => k else 0

-- Reading a child `f ⟨0, h⟩` itself (not only the answer at it) needs a value for the
-- unreachable `none` branch: the `Inhabited` default of `RoseF`.
/--
error: LeanScript: the application
  a✝ ⟨0, h⟩
is read through a field `Fin m → _` (as `Nat → Option _`): below `m` it is `some`, but the language needs a value for `none`, and the type
  RoseF
has no `Inhabited` instance
-/
#guard_msgs in
example := #leanscript_to_term RoseF.firstArity₀

instance : Inhabited RoseF := ⟨.node 0 Fin.elim0⟩

def RoseF.firstArity : RoseF → Nat
  | .node m f => if h : 0 < m then match f ⟨0, h⟩ with | .node k _ => k else 0

def roseFFirstT := #leanscript_to_term RoseF.firstArity
example : roseFFirstT.run roseFT.run = (3 : Nat) := by kernel_rfl

/-- Rebuilding a node from its children. -/
def RoseF.mirror : RoseF → RoseF
  | .node m f => .node m (fun i => f ⟨m - 1 - i.val, by omega⟩)

def roseFMirrorT := #leanscript_to_term RoseF.mirror
example : roseFArityT.run (roseFMirrorT.run roseFT.run) = (2 : Nat) := by kernel_rfl
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)

/-- A fan of `n` leaves, built from a parameter. -/
def RoseF.fan (n : Nat) : RoseF := .node n (fun _ => .node 0 Fin.elim0)

def roseFFanT := #leanscript_to_term RoseF.fan
-- (moved to `Tests/Main.lean`: too slow for the kernel, run compiled)

/-! ## The parameterised rose trees -/

mutual
def RoseTreeL.sum : RoseTreeL Nat → Nat
  | .node a cs => a + RoseTreeL.sumList cs
def RoseTreeL.sumList : List (RoseTreeL Nat) → Nat
  | [] => 0
  | r :: rs => r.sum + RoseTreeL.sumList rs
end

def RoseTreeA.sum : RoseTreeA Nat → Nat
  | .node a cs => cs.foldl (fun acc c => acc + c.sum) a

def RoseTreeF.sum : RoseTreeF Nat → Nat
  | .node a m f => Fin.foldl m (fun acc i => acc + (f i).sum) a

def treeLv : RoseTreeL Nat := .node 1 [.node 10 [], .node 11 []]
def treeAv : RoseTreeA Nat := .node 1 #[.node 10 #[], .node 11 #[]]
def treeFv : RoseTreeF Nat := .node 1 2 (fun i => .node (i.val + 10) 0 Fin.elim0)

#guard treeLv.sum == 22 && treeAv.sum == 22 && treeFv.sum == 22

def treeLSumT := #leanscript_to_term RoseTreeL.sum
def treeASumT := #leanscript_to_term RoseTreeA.sum
def treeFSumT := #leanscript_to_term RoseTreeF.sum
def treeLT : Term Prog.Δ 0 [] [] Prog.treeL [] none := #leanscript_to_term treeLv
def treeAT : Term Prog.Δ 0 [] [] Prog.treeA [] none := #leanscript_to_term treeAv
def treeFT : Term Prog.Δ 0 [] [] Prog.treeF [] none := #leanscript_to_term treeFv

example : treeLSumT.run treeLT.run = (22 : Nat) := by kernel_rfl
example : treeASumT.run treeAT.run = (22 : Nat) := by kernel_rfl
example : treeFSumT.run treeFT.run = (22 : Nat) := by kernel_rfl

/-! ## The `Σ` form -/

def RoseS.size : RoseS → Nat
  | .node ⟨m, f⟩ => Fin.foldl m (fun acc i => acc + (f i).size) 1

def roseSv : RoseS := .node ⟨2, fun _ => .node ⟨0, Fin.elim0⟩⟩

#guard roseSv.size == 3

def roseSSizeT := #leanscript_to_term RoseS.size
def roseST : Term Prog.Δ 0 [] [] Prog.roseS [] none := #leanscript_to_term roseSv

example : roseSSizeT.run roseST.run = (3 : Nat) := by kernel_rfl

/-! ## Refusals: no, one or two values -/

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₁ where
  t := RoseTreeL Unit

/--
error: LeanScript: the type
  Empty
has no constructor (it has no value)
-/
#guard_msgs in
leanscript_signature Bad₂ where
  t := RoseTreeF Empty

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₃ where
  t := RoseTreeA Unit

/-- Children on a function from `Fin m` to a type of one value are refused too. -/
inductive UF where
  | node : (m : Nat) → (Fin m → Unit) → UF

/--
error: LeanScript: the type
  PUnit
has one constructor and no field (it has one value)
-/
#guard_msgs in
leanscript_signature Bad₄ where
  t := UF

/-- A recursive type with no finite value is still refused: here `Fin (m + 1)` is never
    empty, so every node has a child. -/
inductive Loop where
  | node : (m : Nat) → (Fin (m + 1) → Loop) → Loop

/--
error: LeanScript: these recursive types have no finite value (no grounding order): [Loop]
(an `Array` guards a recursive field, a function field `A → X` does not: every type of the language has values)
-/
#guard_msgs in
leanscript_signature Bad₅ where
  t := Loop

end RoseVariantsTest

end
