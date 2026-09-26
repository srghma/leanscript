module

public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# Terms over a datatype signature (`LeanScript.Term`)

Programs written with the three datatype formers (`data_in`, `data_out`, `data_rec`),
evaluated by `Term.eval`, with the results checked by `rfl`.  The signature has two blocks:
`List Nat`, then a rose tree `Rose := node (List Nat) (Array Rose)` that stores an older
`List Nat` in a field, and whose fold calls the *older* block's fold.
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

/-- `x :: xs`, as a term. -/
def consT {Γ : Ctx [0, 0]} (x : Term Δ Γ .nat) (xs : Term Δ Γ listNat) : Term Δ Γ listNat :=
  .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil)))

/-- `[]`, as a term. -/
def nilT {Γ : Ctx [0, 0]} : Term Δ Γ listNat := .data_in listB 0 (.union_mk .two₁ .nil)

/-- A numeral. -/
def natT {Γ : Ctx [0, 0]} (n : Nat) : Term Δ Γ .nat := .lit .nat n

/-- `Nat.add`, as an extern. -/
def addT {Γ : Ctx [0, 0]} (a b : Term Δ Γ .nat) : Term Δ Γ .nat :=
  .extern (σs := [.nat, .nat]) "Nat.add" (fun v => Nat.add v.1 v.2.1) (.cons a (.cons b .nil))

/-- A node of a rose tree. -/
def nodeT {Γ : Ctx [0, 0]} (xs : Term Δ Γ listNat) (cs : Elems Δ Γ rose) : Term Δ Γ rose :=
  .data_in roseB 0 (.record_mk (.cons xs (.cons (.array_mk cs) .nil)))

/-! ## Folds -/

/-- `List.sum`, by the one fold of the block of `List Nat`.  The branch receives the body
    of `List Nat` whose hole is the pair `(tail, sum of the tail)`. -/
def sumT {Γ : Ctx [0, 0]} : Term Δ Γ (.fn listNat .nat) :=
  .lam (.data_rec listB (fun _ => .nat) (fun ⟨0, _⟩ =>
    .union_casesOn (.bvar 0)
      (.two (natT 0)
        -- the fields of `cons`: `n` (index 0), `(tail, s)` (index 1)
        (.record_casesOn (.bvar 1)
          -- `tail` (index 0), `s` (index 1), `n` (index 2)
          (addT (.bvar 2) (.bvar 1)))))
    0 (.bvar 0))

/-- `List.head?`, by one layer out. -/
def headT : Term Δ [] (.fn listNat (Ty.option .nat)) :=
  .lam (.union_casesOn (.data_out listB 0 (.bvar 0))
    (.two (.union_mk .two₁ .nil) (.union_mk .two₂ (.cons (.bvar 0) .nil))))

/-- The sum of every number in a rose tree: the branch calls the fold of the *older* block
    (`sumT`) on the node's `List Nat`, and sums the answers of the children. -/
def roseSumT : Term Δ [] (.fn rose .nat) :=
  .lam (.data_rec roseB (fun _ => .nat) (fun ⟨0, _⟩ =>
    -- the node: `(xs, children)`, each child paired with its answer
    .record_casesOn (.bvar 0)
      -- `xs` (index 0), `children` (index 1)
      (addT (.app sumT (.bvar 0))
        (.array_foldl (.bvar 1) (natT 0)
          -- the child (index 0), the accumulator (index 1)
          (.record_casesOn (.bvar 0)
            -- the subtree (index 0), its answer (index 1), …, the accumulator (index 3)
            (addT (.bvar 3) (.bvar 1))))))
    0 (.bvar 0))

/-! ## Running them -/

def list123 : Term Δ [] listNat := consT (natT 1) (consT (natT 2) (consT (natT 3) nilT))

example : (Term.app sumT list123).run = (6 : Nat) := rfl
example : (Term.app headT list123).run = (some 1 : Option Nat) := rfl
example : (Term.app headT nilT).run = (none : Option Nat) := rfl

def tree : Term Δ [] rose :=
  nodeT (consT (natT 1) nilT)
    (.cons (nodeT (consT (natT 10) (consT (natT 20) nilT)) .nil)
      (.cons (nodeT nilT .nil) .nil))

example : (Term.app roseSumT tree).run = (31 : Nat) := rfl

/-- Course-of-values recursion (`data_brec`, looking two levels down): the Fibonacci number of
    the length of a list, `f [] = 0`, `f [x] = 1`, `f (x :: y :: t) = f (y :: t) + f t`.  The
    branch of `cons` gets the window of depth `1` of the tail: the tail, the answer at it, and
    the tail's own body whose hole is the window of depth `0` (the pair of the tail's tail and
    the answer at it). -/
def fibLenT : Term Δ [] (.fn listNat .nat) :=
  .lam (.data_brec listB (fun _ => .nat) 1 (fun ⟨0, _⟩ =>
    .union_casesOn (.bvar 0)
      (.two (natT 0)
        -- the fields of `cons`: `x` (index 0), the window `w` of the tail (index 1)
        (.record_casesOn (.bvar 1)
          -- `t` (index 0), `f t` (index 1), the body of `t` (index 2)
          (.union_casesOn (.bvar 2)
            (.two (natT 1)
              -- `t = y :: t'`: `y` (index 0), the window of `t'` (index 1)
              (.record_casesOn (.bvar 1)
                -- `t'` (index 0), `f t'` (index 1), …, `f t` (index 5)
                (addT (.bvar 5) (.bvar 1))))))))
    0 (.bvar 0))

def list5 : Term Δ [] listNat :=
  consT (natT 1) (consT (natT 2) (consT (natT 3) (consT (natT 4) (consT (natT 5) nilT))))

example : (Term.app fibLenT nilT).run = (0 : Nat) := rfl
example : (Term.app fibLenT (consT (natT 7) nilT)).run = (1 : Nat) := rfl
example : (Term.app fibLenT list123).run = (2 : Nat) := rfl
example : (Term.app fibLenT list5).run = (5 : Nat) := rfl

/-- `nat_rec`: the triangular number `0 + 1 + … + (n - 1)`. -/
def triT : Term Δ [] (.fn .nat .nat) :=
  .lam (.nat_rec (.bvar 0) (natT 0) (addT (.bvar 0) (.bvar 1)))

example : (Term.app triT (natT 5)).run = (10 : Nat) := rfl

/-- `let` and an enum. -/
example : (Term.letE (Δ := Δ) (Γ := []) (.enum_mk {} 2)
    (.enum_casesOn (.bvar 0) (fun i => natT (i.val * 10)))).run = (20 : Nat) := rfl

end TermTest

end
