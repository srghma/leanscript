module

public import LeanScript.Term.Eval
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# Terms over a datatype signature (`LeanScript.Term`)

Programs written, in A-normal form, with the three datatype formers (`data_in`, `data_out`,
`data_rec`), evaluated by `Term.eval`, with the results checked by `rfl`.  The signature has two blocks:
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

/-- `x :: xs`, as a pure expression. -/
def consT {Γ : Ctx [0, 0]} (x : PExpr Δ Γ .nat) (xs : PExpr Δ Γ listNat) : PExpr Δ Γ listNat :=
  .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil)))

/-- `[]`, as a pure expression. -/
def nilT {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat := .data_in listB 0 (.union_mk .two₁ .nil)

/-- A numeral. -/
def natT {Γ : Ctx [0, 0]} (n : Nat) : PExpr Δ Γ .nat := .lit .nat n

/-- `Nat.add`, as an extern: a computation. -/
def addT {Γ : Ctx [0, 0]} (a b : PExpr Δ Γ .nat) : Comp Δ Γ .nat :=
  .extern (σs := [.nat, .nat]) "Nat.add" (fun v => Nat.add v.1 v.2) (.cons a (.cons b .nil))

/-- A node of a rose tree. -/
def nodeT {Γ : Ctx [0, 0]} (xs : PExpr Δ Γ listNat) (cs : Elems Δ Γ rose) : PExpr Δ Γ rose :=
  .data_in roseB 0 (.record_mk (.cons xs (.cons (.array_mk cs) .nil)))

/-- Apply a closed function (a computation) to an argument: `let f := fn; f a`. -/
def appT {σ τ : Ty [0, 0]} (fn : Comp Δ [] (.fn σ τ)) (a : PExpr Δ [.fn σ τ] σ) :
    Term Δ [] τ [] :=
  .letE fn (.ofComp (.app (.bvar 0) a))

/-! ## Folds -/

/-- `List.sum`, by the one fold of the block of `List Nat`.  The branch receives the body
    of `List Nat` whose hole is the pair `(tail, sum of the tail)`. -/
def sumT {Γ : Ctx [0, 0]} : Comp Δ Γ (.fn listNat .nat) :=
  .lam (.ofComp (.data_rec listB (fun _ => .nat) (fun ⟨0, _⟩ =>
    .union_casesOn (.bvar 0)
      (.two (.ret (natT 0))
        -- the fields of `cons`: `n` (index 0), `(tail, s)` (index 1)
        (.record_casesOn (.bvar 1)
          -- `tail` (index 0), `s` (index 1), `n` (index 2)
          (.ofComp (addT (.bvar 2) (.bvar 1))))))
    0 (.bvar 0)))

/-- `List.head?`, by one layer out. -/
def headT : Comp Δ [] (.fn listNat (Ty.option .nat)) :=
  .lam (.union_casesOn (.data_out listB 0 (.bvar 0))
    (.two (.ret (.union_mk .two₁ .nil)) (.ret (.union_mk .two₂ (.cons (.bvar 0) .nil)))))

/-- The sum of every number in a rose tree: the branch calls the fold of the *older* block
    (`sumT`) on the node's `List Nat`, and sums the answers of the children. -/
def roseSumT : Comp Δ [] (.fn rose .nat) :=
  .lam (.ofComp (.data_rec roseB (fun _ => .nat) (fun ⟨0, _⟩ =>
    -- the node: `(xs, children)`, each child paired with its answer
    .record_casesOn (.bvar 0)
      -- `xs` (index 0), `children` (index 1)
      (.letE sumT
        -- `sum` (index 0), `xs` (index 1), `children` (index 2)
        (.letE (.app (.bvar 0) (.bvar 1))
          -- `s` (index 0), …, `children` (index 3)
          (.letE (.array_foldl (.bvar 3) (natT 0)
              -- the child (index 0), the accumulator (index 1)
              (.record_casesOn (.bvar 0)
                -- the subtree (index 0), its answer (index 1), …, the accumulator (index 3)
                (.ofComp (addT (.bvar 3) (.bvar 1)))))
            -- the sum of the children (index 0), `s` (index 1)
            (.ofComp (addT (.bvar 1) (.bvar 0)))))))
    0 (.bvar 0)))

/-! ## Running them -/

def list123 {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat :=
  consT (natT 1) (consT (natT 2) (consT (natT 3) nilT))

example : (appT sumT list123).run = (6 : Nat) := by kernel_rfl
example : (appT headT list123).run = (some 1 : Option Nat) := rfl
example : (appT headT nilT).run = (none : Option Nat) := rfl

def tree {Γ : Ctx [0, 0]} : PExpr Δ Γ rose :=
  nodeT (consT (natT 1) nilT)
    (.cons (nodeT (consT (natT 10) (consT (natT 20) nilT)) .nil)
      (.cons (nodeT nilT .nil) .nil))

example : (appT roseSumT tree).run = (31 : Nat) := by kernel_rfl

/-- Course-of-values recursion (`data_brec`, looking two levels down): the Fibonacci number of
    the length of a list, `f [] = 0`, `f [x] = 1`, `f (x :: y :: t) = f (y :: t) + f t`.  The
    branch of `cons` gets the window of depth `1` of the tail: the tail, the answer at it, and
    the tail's own body whose hole is the window of depth `0` (the pair of the tail's tail and
    the answer at it). -/
def fibLenT : Comp Δ [] (.fn listNat .nat) :=
  .lam (.ofComp (.data_brec listB (fun _ => .nat) 1 (fun ⟨0, _⟩ =>
    .union_casesOn (.bvar 0)
      (.two (.ret (natT 0))
        -- the fields of `cons`: `x` (index 0), the window `w` of the tail (index 1)
        (.record_casesOn (.bvar 1)
          -- `t` (index 0), `f t` (index 1), the body of `t` (index 2)
          (.union_casesOn (.bvar 2)
            (.two (.ret (natT 1))
              -- `t = y :: t'`: `y` (index 0), the window of `t'` (index 1)
              (.record_casesOn (.bvar 1)
                -- `t'` (index 0), `f t'` (index 1), …, `f t` (index 5)
                (.ofComp (addT (.bvar 5) (.bvar 1)))))))))
    0 (.bvar 0)))

def list5 {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat :=
  consT (natT 1) (consT (natT 2) (consT (natT 3) (consT (natT 4) (consT (natT 5) nilT))))

example : (appT fibLenT nilT).run = (0 : Nat) := rfl
example : (appT fibLenT (consT (natT 7) nilT)).run = (1 : Nat) := rfl
example : (appT fibLenT list123).run = (2 : Nat) := by kernel_rfl
example : (appT fibLenT list5).run = (5 : Nat) := by kernel_rfl

/-- `nat_rec`: the triangular number `0 + 1 + … + (n - 1)`. -/
def triT : Comp Δ [] (.fn .nat .nat) :=
  .lam (.ofComp (.nat_rec (.bvar 0) (natT 0) (.ofComp (addT (.bvar 0) (.bvar 1)))))

example : (appT triT (natT 5)).run = (10 : Nat) := rfl

/-- `let` (of a shared pure expression) and an enum. -/
example : (Term.letE (Δ := Δ) (Γ := []) (.share (.enum_mk {} 2))
    (.enum_casesOn (.bvar 0) (fun i => .ret (natT (i.val * 10))))).run = (20 : Nat) := rfl

/-- A join point: `join j x := x + 1; if b then jump j 1 else jump j 2`, with `b := true`.
    (The condition is a variable: `if true then …` is an ι-redex, which the grammar rules
    out.) -/
example : (Term.join (Δ := Δ) (Γ := [.bool]) .nat (.ofComp (addT (.bvar 0) (natT 1)))
    (.ite (.bvar 0) (.jump .head (natT 1)) (.jump .head (natT 2))) : Term Δ [.bool] .nat []).eval (true : Bool)
      PUnit.unit = (2 : Nat) := rfl

end TermTest

end
