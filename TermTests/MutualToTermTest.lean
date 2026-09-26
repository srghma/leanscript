module

public import LeanScript.Two
public import LeanScript.Eval
public meta import LeanScript.ToTerm
public meta import LeanScript.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Mutual blocks, and members held inside an `Array` or a function

A member of a `mutual` block may be held inside an `Array` or a function
(`node (qs : Array Q)`, `node (f : Nat → K)`):

* `leanscript_signature` declares such a block (`Fld.array`, `Fld.fn` of a hole);
* `#leanscript_get_ctor` builds its values;
* `Term.data_rec` folds the whole block at once: in the branch of a member, every member
  held inside an array or a function is the pair of the subvalue and the answer at it;
* `#leanscript_to_term` translates a `mutual` group of recursive functions, one per member,
  to one `data_rec`: a call on a member held in a function field (`(f 0).sum`) is the answer
  next to the subvalue, and `Array.foldl` over an array field folds the pairs.

Each translation is run by the kernel (`kernel_rfl`); the Lean definitions are evaluated on the same values by
`#guard`.
-/

namespace MutualToTermTest

open LeanScript

-- A member (`Q`) inside an `Array` of the other member.
mutual
inductive G where
  | leaf : Nat → G
  | node : Array Q → G
inductive Q where
  | mk : G → Nat → Q
end

-- A member (`K`) inside a function field of the other member.
mutual
inductive H where
  | leaf : Nat → H
  | node : (Nat → K) → H
inductive K where
  | mk : H → String → K
end

mutual
inductive Even where
  | zero : Even
  | succ : Odd → Even
inductive Odd where
  | succ : Even → Odd
end

/-- A rose tree whose children are a nested `List`: `List Rose` is the second member. -/
inductive Rose where
  | node : Nat → List Rose → Rose

/-- A member inside an array of arrays. -/
inductive Grid where
  | cell : Nat → Grid
  | rows : Array (Array Grid) → Grid

leanscript_signature Prog where
  g := G
  q := Q
  h := H
  k := K
  even := Even
  rose := Rose
  grid := Grid

/-! ## The blocks -/

/-- `G`/`Q`: `G.node` holds an array of member `1` (`Q`), guarded; `Q.mk` holds member `0`. -/
example : Prog.block0 =
    .cons (.union (.two₁ (.fields (.one (.old .nat))) (.fields (.one (.array (.hole 1 (by decide)))))))
      (.cons (.record (.hole 0 (by decide)) (.one (.old .nat))) .nil) := rfl

/-- `H`/`K`: `H.node` holds a function from `Nat` to member `1` (`K`). -/
example : Prog.block1 =
    .cons (.union (.two₁ (.fields (.one (.old .nat))) (.fields (.one (.fn .nat (.hole 1 (by decide)))))))
      (.cons (.record (.hole 0 (by decide)) (.one (.old .string))) .nil) := rfl

/-- Every type of these blocks has two different values. -/
example : ∃ x y : Ty.Den Prog.Δ Prog.g, x ≠ y := Ty.den_exists_ne _ _
example : ∃ x y : Ty.Den Prog.Δ Prog.q, x ≠ y := Ty.den_exists_ne _ _
example : ∃ x y : Ty.Den Prog.Δ Prog.h, x ≠ y := Ty.den_exists_ne _ _
example : ∃ x y : Ty.Den Prog.Δ Prog.grid, x ≠ y := Ty.den_exists_ne _ _

/-! ## A member inside an `Array` of the other member -/

/-- `G.node #[Q.mk (G.leaf 3) 4, Q.mk (G.node #[]) 5]`. -/
def gT : Term Prog.Δ [] Prog.g :=
  (#leanscript_get_ctor G.node) (.array_mk
    (.cons ((#leanscript_get_ctor Q.mk) ((#leanscript_get_ctor G.leaf) (.lit .nat 3)) (.lit .nat 4))
    (.cons ((#leanscript_get_ctor Q.mk) ((#leanscript_get_ctor G.node) (.array_mk .nil)) (.lit .nat 5))
      .nil)))

mutual
def G.sum : G → Nat
  | .leaf n => n
  | .node qs => qs.foldl (fun acc q => acc + q.sum) 0
def Q.sum : Q → Nat
  | .mk g n => g.sum + n
end

#guard G.sum (.node #[.mk (.leaf 3) 4, .mk (.node #[]) 5]) == 12

def gSumT := #leanscript_to_term G.sum
def qSumT := #leanscript_to_term Q.sum

example : gSumT.run gT.run = (12 : Nat) := by kernel_rfl
example : qSumT.run ((#leanscript_get_ctor Q.mk) gT (.lit .nat 1)).run = (13 : Nat) := by kernel_rfl

-- The answer depends on the fold's result at every element, not only its sum.
mutual
def G.depth : G → Nat
  | .leaf _ => 0
  | .node qs => qs.foldl (fun acc q => max acc (q.depth + 1)) 0
def Q.depth : Q → Nat
  | .mk g _ => g.depth
end

def gDepthT := #leanscript_to_term G.depth
example : gDepthT.run gT.run = (1 : Nat) := by kernel_rfl

/-! ## A member inside a function field -/

/-- `H.node (fun n => K.mk (H.leaf n) "ab")`. -/
def hT : Term Prog.Δ [] Prog.h :=
  (#leanscript_get_ctor H.node)
    (.lam ((#leanscript_get_ctor K.mk) ((#leanscript_get_ctor H.leaf) (.bvar 0)) (.lit .string "ab")))

mutual
def H.sum : H → Nat
  | .leaf n => n
  | .node f => (f 0).sum + (f 1).sum
def K.sum : K → Nat
  | .mk h s => h.sum + s.length
end

#guard H.sum (.node fun n => .mk (.leaf n) "ab") == 5

def hSumT := #leanscript_to_term H.sum
example : hSumT.run hT.run = (5 : Nat) := by kernel_rfl

-- A value of the member held in the function is its subvalue (here passed on).
mutual
def H.first : H → Nat → Nat
  | .leaf n, m => n + m
  | .node f, m => (f m).first m
def K.first : K → Nat → Nat
  | .mk h _, m => h.first m
end

def hFirstT := #leanscript_to_term H.first
example : hFirstT.run hT.run (7 : Nat) = (14 : Nat) := by kernel_rfl

/-! ## A `mutual` block with members used directly -/

mutual
def Even.toNat : Even → Nat
  | .zero => 0
  | .succ o => o.toNat + 1
def Odd.toNat : Odd → Nat
  | .succ e => e.toNat + 1
end

def evenT := #leanscript_to_term Even.toNat
def oddT := #leanscript_to_term Odd.toNat

def two : Term Prog.Δ [] Prog.even :=
  (#leanscript_get_ctor Even.succ) ((#leanscript_get_ctor Odd.succ) (#leanscript_get_ctor Even.zero))

example : evenT.run two.run = (2 : Nat) := by kernel_rfl
example : oddT.run ((#leanscript_get_ctor Odd.succ) two).run = (3 : Nat) := by kernel_rfl

/-! ## Nested recursion: `Rose` and `List Rose` -/

mutual
def Rose.sum : Rose → Nat
  | .node n cs => n + Rose.sumList cs
def Rose.sumList : List Rose → Nat
  | [] => 0
  | r :: rs => r.sum + Rose.sumList rs
end

def roseT : Term Prog.Δ [] Prog.rose :=
  (#leanscript_get_ctor Rose.node) (.lit .nat 1)
    ((#leanscript_get_ctor List.cons (α := Rose))
      ((#leanscript_get_ctor Rose.node) (.lit .nat 2) (#leanscript_get_ctor List.nil (α := Rose)))
      (#leanscript_get_ctor List.nil (α := Rose)))

#guard Rose.sum (.node 1 [.node 2 []]) == 3

def roseSumT := #leanscript_to_term Rose.sum
example : roseSumT.run roseT.run = (3 : Nat) := by kernel_rfl

/-! ## A member inside an array of arrays -/

def Grid.sum : Grid → Nat
  | .cell n => n
  | .rows rs => rs.foldl (fun acc r => r.foldl (fun acc' g => acc' + g.sum) acc) 0
decreasing_by
  have h₁ := Array.sizeOf_lt_of_mem ‹r ∈ rs›
  have h₂ := Array.sizeOf_lt_of_mem ‹g ∈ r›
  simp only [Grid.rows.sizeOf_spec]
  omega

def gridT : Term Prog.Δ [] Prog.grid :=
  (#leanscript_get_ctor Grid.rows) (.array_mk
    (.cons (.array_mk (.cons ((#leanscript_get_ctor Grid.cell) (.lit .nat 1))
      (.cons ((#leanscript_get_ctor Grid.cell) (.lit .nat 2)) .nil)))
    (.cons (.array_mk (.cons ((#leanscript_get_ctor Grid.cell) (.lit .nat 4)) .nil)) .nil)))

#guard Grid.sum (.rows #[#[.cell 1, .cell 2], #[.cell 4]]) == 7

def gridSumT := #leanscript_to_term Grid.sum
example : gridSumT.run gridT.run = (7 : Nat) := by kernel_rfl

/-! ## Refusals -/

-- An array field holds the pairs of its subvalues and their answers: it can only be folded.
mutual
def G.count : G → Nat
  | .leaf _ => 1
  | .node qs => qs.size + qs.foldl (fun acc q => acc + q.count) 0
def Q.count : Q → Nat
  | .mk g _ => g.count
end

/--
error: LeanScript: the argument
  a✝
of `Array.size` is not a value of a leaf type (an extern takes and returns values of leaf types only)
-/
#guard_msgs in
example := #leanscript_to_term G.count

end MutualToTermTest

end
