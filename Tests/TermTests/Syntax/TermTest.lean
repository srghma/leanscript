module

public import LeanScript.Term.Build
public import LeanScript.Term.Extern.Shorthands
public import LeanScript.TermElab.Notation
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Terms over a datatype signature (`LeanScript.Term`)

Programs with the three datatype formers (`data_in`, `data_out`, `data_rec`), written in the
direct-style notation `[Term| …]` (normalised to the grammar of normal forms), evaluated by
`Term.run`, with the results checked by `rfl`.  The signature has two blocks: `List Nat`, then
a rose tree `Rose := node (List Nat) (Array Rose)` that stores an older `List Nat` in a field,
and whose fold calls the *older* block's fold.
-/

namespace TermTest

open LeanScript

/-! ## The signature -/

/-- `List Nat := nil | cons Nat List`. -/
def listBody : Mems [] 1 0 :=
  .cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil

/-- `Rose := node (List Nat) (Array Rose)`, over the block of `List Nat`. -/
def roseBody : Mems [0] 1 0 :=
  .cons (.record (.old (.data (.here 0))) (.one (.array (.hole 0 (by decide))))) .nil

/-- The program's signature: `List Nat`, then `Rose`. -/
def Δ : DSig [0, 0] := .cons (.cons .nil 0 listBody) 0 roseBody

/-- The block of `List Nat` (the older one). -/
abbrev listB : BRef [0, 0] := .there .here
/-- The block of `Rose` (the newest one). -/
abbrev roseB : BRef [0, 0] := .here

def listNat : Ty [0, 0] := .data (.there (.here 0))
def rose : Ty [0, 0] := .data (.here 0)

example : (Δ.block listB).unfold 0 = .union (.two .nullary (.fields (.cons .nat (.one listNat)))) :=
  rfl
example : (Δ.block roseB).unfold 0 = .record listNat (.one (.array rose)) := rfl

/-! ## Building values -/

section
variable {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]}

/-- A numeral. -/
def natT (n : Nat) : PExpr Δ Φ Γ .nat none := .lit .nat n

/-- `[]`, as a pure expression. -/
def nilT : PExpr Δ Φ Γ listNat none := .data_in listB 0 (.union_mk .two₁ .nil)

/-- `x :: xs`, as a pure expression. -/
def consT {o₁ o₂ : Lvl} (x : PExpr Δ Φ Γ .nat o₁) (xs : PExpr Δ Φ Γ listNat o₂) :
    PExpr Δ Φ Γ listNat (Lvl.meet o₁ (Lvl.meet o₂ none)) :=
  .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil)))

/-- `Nat.add`, the call of the extern `lean_nat_add`: a neutral expression, so at least one of
    its arguments is open. -/
def addT {o₁ o₂ : Lvl} {ℓ : Nat} (a : PExpr Δ Φ Γ .nat o₁) (b : PExpr Δ Φ Γ .nat o₂)
    (h : Lvl.meet o₁ (Lvl.meet o₂ none) = some ℓ := by rfl) : PExpr Δ Φ Γ .nat (some ℓ) :=
  PExpr.lean_nat_add a b h

/-- A node of a rose tree. -/
def nodeT {o₁ o₂ : Lvl} (xs : PExpr Δ Φ Γ listNat o₁) (cs : Elems Δ Φ Γ rose o₂) :
    PExpr Δ Φ Γ rose (Lvl.meet o₁ (Lvl.meet o₂ none)) :=
  .data_in roseB 0 (.record_mk (.cons xs (.cons (.array_mk cs) .nil)))

end

/-- Closed programs of type `τ` over `Δ`. -/
abbrev Prog (τ : Ty [0, 0]) : Type := Term Δ 0 [] [] τ [] none

/-! ## Folds -/

/-- `List.sum`, by the one fold of the block of `List Nat`.  The branch receives the body
    of `List Nat` whose hole is the pair `(tail, sum of the tail)`: the fields of `cons` are
    `n` (`#0`) and `(tail, s)` (`#1`); taken apart, `tail` is `#0`, `s` is `#1` and `n` is `#2`. -/
def sumT : Prog (.fn listNat .nat) :=
  [Term| fun _ => data_rec ‹listB› ‹fun _ => .nat›
    (match #0 with
      | · => 0
      | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #2 #1) 0 #0]

/-- `List.head?`, by one layer out. -/
def headT : Prog (.fn listNat (Ty.option .nat)) :=
  [Term| fun _ => match data_out ‹listB› 0 #0 with | · => union_mk 0 | (_, _) => union_mk 1 #0]

/-- The sum of every number in a rose tree: the branch calls a fold of the *older* block (the
    sum of a list, a closure shared by name) on the node's `List Nat`, and sums the answers of
    the children. -/
def roseSumT : Prog (.fn rose .nat) :=
  [Term| fun _ => data_rec ‹roseB› ‹fun _ => .nat›
    (let (_, _) := #0;
     let _ := (fun (_ : ‹listNat›) => data_rec ‹listB› ‹fun _ => .nat›
       (match #0 with
         | · => 0
         | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #2 #1) 0 #0);
     let _ := #0 #1;
     let _ := array_foldl #3 0 (let (_, _) := #0; extern ‹.lean_nat_add› #3 #1);
     extern ‹.lean_nat_add› #1 #0) 0 #0]

/-! ## Running them -/

def list123 : PExpr Δ [] [] listNat none :=
  consT (natT 1) (consT (natT 2) (consT (natT 3) nilT))

example : sumT.run list123.run = (6 : Nat) := by kernel_rfl
example : headT.run list123.run = (some 1 : Option Nat) := by kernel_rfl
example : headT.run nilT.run = (none : Option Nat) := by kernel_rfl

def tree : PExpr Δ [] [] rose none :=
  nodeT (consT (natT 1) nilT)
    (.cons (nodeT (consT (natT 10) (consT (natT 20) nilT)) .nil)
      (.cons (nodeT nilT .nil) .nil))

example : roseSumT.run tree.run = (31 : Nat) := by kernel_rfl

/-- Course-of-values recursion (`data_brec`, looking two levels down): the Fibonacci number of
    the length of a list, `f [] = 0`, `f [x] = 1`, `f (x :: y :: t) = f (y :: t) + f t`.  The
    branch of `cons` gets the window of depth `1` of the tail: the tail, the answer at it, and
    the tail's own body whose hole is the window of depth `0` (the pair of the tail's tail and
    the answer at it). -/
def fibLenT : Prog (.fn listNat .nat) :=
  [Term| fun _ => data_brec ‹listB› ‹fun _ => .nat› 1
    (match #0 with
      | · => 0
      | (_, _) =>
        let (_, _, _) := #1;
        match #2 with
          | · => 1
          | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #5 #1) 0 #0]

def list5 : PExpr Δ [] [] listNat none :=
  consT (natT 1) (consT (natT 2) (consT (natT 3) (consT (natT 4) (consT (natT 5) nilT))))

example : fibLenT.run nilT.run = (0 : Nat) := by kernel_rfl
example : fibLenT.run (consT (natT 7) nilT).run = (1 : Nat) := by kernel_rfl
example : fibLenT.run list123.run = (2 : Nat) := by kernel_rfl
example : fibLenT.run list5.run = (5 : Nat) := by kernel_rfl

/-- `nat_rec`: the triangular number `0 + 1 + … + (n - 1)`; the step sees the answer so far
    as `#0` and the predecessor as `#1`. -/
def triT : Prog (.fn .nat .nat) :=
  [Term| fun _ => nat_rec #0 0 (extern ‹.lean_nat_add› #0 #1)]

example : triT.run (5 : Nat) = (10 : Nat) := rfl

/-- An enum case analysis. -/
def enumT : Prog (.fn (.enum {}) .nat) :=
  [Term| fun _ => match #0 with | 0 => 0 | 1 => 10 | _ => 20]

example : enumT.run (2 : Fin _) = (20 : Nat) := rfl

/-- A join point: `join j x := x + 1; if b then jump j 1 else jump j 2`. -/
def joinT : Prog (.fn .bool .nat) :=
  [Term| fun _ => join _ (_ : Nat) := extern ‹.lean_nat_add› #0 1; if #0 then jump ^0 1 else jump ^0 2]

example : joinT.run true = (2 : Nat) := rfl
example : joinT.run false = (3 : Nat) := rfl

end TermTest

end
