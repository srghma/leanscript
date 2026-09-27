module

public import LeanScript.TermElab.Notation
public import LeanScript.Term.Build
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `[Term| …]` notation (`LeanScript.TermElab.Notation`)

The programs of `TermTests.TermTest`, written in the notation (de Bruijn variables `#i`,
constructor names) in direct style and normalised to A-normal form, run by `Term.run` and
checked by `rfl` (`kernel_rfl` for the longer runs); checks that the notation builds the same
terms as the constructors of the three layers (`PExpr`, `Comp`, `Term`); how terms are printed back (`#guard_msgs`), and that the
printed form reads back as the same term.
-/

namespace TermNotationTest

open LeanScript

/-! ## The signature: `List Nat`, then `Rose := node (List Nat) (Array Rose)` -/

def listBody : Mems [] 1 0 :=
  .cons (.union (.two₁ .nullary (.fields (.cons (.old .nat) (.one (.hole 0 (by decide))))))) .nil
def roseBody : Mems [0] 1 0 :=
  .cons (.record (.old (.data (.here 0))) (.one (.array (.hole 0 (by decide))))) .nil
def Δ : DSig [0, 0] := .cons (.cons .nil 0 listBody) 0 roseBody

abbrev listB : BRef [0, 0] := .there .here
abbrev roseB : BRef [0, 0] := .here
abbrev listNat : Ty [0, 0] := [Ty| Data 1 0]
abbrev rose : Ty [0, 0] := [Ty| Data 0 0]

/-- `Nat.add`: the call of the extern `lean_nat_add` (an entry of the catalogue of externs) on
    two pure expressions, a pure (neutral) expression. -/
def addT {Γ : Ctx [0, 0]} (a b : PExpr Δ Γ .nat) : PExpr Δ Γ .nat :=
  [Term| extern ‹.lean_nat_add› ‹a› ‹b›]

/-! ## Building values -/

def consT {Γ : Ctx [0, 0]} (x : PExpr Δ Γ .nat) (xs : PExpr Δ Γ listNat) : PExpr Δ Γ listNat :=
  [Term| data_in ‹listB› 0 (union_mk 1 ‹x› ‹xs›)]
def nilT {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat := [Term| data_in ‹listB› 0 (union_mk 0)]
def nodeT {Γ : Ctx [0, 0]} (xs : PExpr Δ Γ listNat) (cs : Elems Δ Γ rose) : PExpr Δ Γ rose :=
  [Term| data_in ‹roseB› 0 (‹xs›, ‹.array_mk cs›)]

/-- The notation builds the same terms as the constructors. -/
example {Γ : Ctx [0, 0]} (x : PExpr Δ Γ .nat) (xs : PExpr Δ Γ listNat) :
    consT x xs = .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil))) := rfl
example {Γ : Ctx [0, 0]} : (nilT : PExpr Δ Γ listNat) = .data_in listB 0 (.union_mk .two₁ .nil) :=
  rfl
example : ([Term| (3, true, "a")] : PExpr Δ [] [Ty| Nat × Bool × String]) =
    .record_mk (.cons (.lit .nat 3) (.cons (.lit .bool true) (.cons (.lit .string "a") .nil))) :=
  rfl
/-- A pure expression in tail position is the answer of the statement. -/
example : ([Term| (3, true)] : Term Δ [] [Ty| Nat × Bool] []) =
    .ret (.record_mk (.cons (.lit .nat 3) (.cons (.lit .bool true) .nil))) := rfl
/-- A closure is a computation; the body of a curried function names its inner closure. -/
example : ([Term| fun _ _ => #1] : Comp Δ [] [Ty| Nat → Bool → Nat]) =
    .lam (.ofComp (.lam (.ret (.var (.tail .head))))) := rfl
/-- A free `#i` is a variable of the enclosing context. -/
example : ([Term| fun _ => ‹addT›(#0, #1)] : Comp Δ [.nat] [Ty| Nat → Nat]) =
    .lam (.ret (addT (.bvar 0) (.bvar 1))) := rfl
/-- A call of an extern is a pure expression: calls of externs nest, with no `let`. -/
example : ([Term| ‹addT›(‹addT›(#0, 1), 2)] : Term Δ [.nat] .nat []) =
    .ret (addT (addT (.bvar 0) (.lit .nat 1)) (.lit .nat 2)) := rfl
/-- A branch that is not in tail position gets a join point for the rest of the statement. -/
example : ([Term| ‹addT›(if #0 then 1 else 2, 10)] : Term Δ [.bool] .nat []) =
    .join .nat (.ret (addT (.bvar 0) (.lit .nat 10)))
      (.ite (.bvar 0) (.jump .head (.lit .nat 1)) (.jump .head (.lit .nat 2))) := rfl

/-! ## Folds -/

/-- `List.sum`: the branch of the fold receives (`#0`) the body of `List Nat` whose hole is
    the pair `(tail, sum of the tail)`. -/
def sumT {Γ : Ctx [0, 0]} : Comp Δ Γ [Ty| ‹listNat› → Nat] :=
  [Term| fun _ => data_rec ‹listB› ‹fun _ => .nat›
    (match #0 with
      | · => 0
      | (_, _) => let (_, _) := #1; ‹addT›(#2, #1))
    0 #0]

/-- `List.head?`, by one layer out. -/
def headT : Comp Δ [] [Ty| ‹listNat› → Option Nat] :=
  [Term| fun _ => match data_out ‹listB› 0 #0 with | · => union_mk 0 | (_, _) => union_mk 1 #0]

/-- The sum of every number in a rose tree: the branch calls the fold of the older block. -/
def roseSumT : Comp Δ [] [Ty| ‹rose› → Nat] :=
  [Term| fun _ => data_rec ‹roseB› ‹fun _ => .nat›
    (let (_, _) := #0;
      ‹addT›(‹sumT› #0, array_foldl #1 0 (let (_, _) := #0; ‹addT›(#3, #1))))
    0 #0]

/-- Course-of-values recursion: the Fibonacci number of the length of a list. -/
def fibLenT : Comp Δ [] [Ty| ‹listNat› → Nat] :=
  [Term| fun _ => data_brec ‹listB› ‹fun _ => .nat› 1
    (match #0 with
      | · => 0
      | (_, _) =>
        let (_, _, _) := #1;
        match #2 with
        | · => 1
        | (_, _) => let (_, _) := #1; ‹addT›(#5, #1))
    0 #0]

/-- Direct style is A-normalised: a computation inside an expression (the closure `sumT` and
    its application) is named by a `let`, in evaluation order. -/
example : ([Term| ‹addT›(‹sumT› ‹nilT›, 2)] : Term Δ [] .nat []) =
    .letE sumT (.letE (.app (.bvar 0) nilT) (.ret (addT (.bvar 0) (.lit .nat 2)))) := rfl

/-! ## Running them -/

def list123 {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat :=
  consT [Term| 1] (consT [Term| 2] (consT [Term| 3] nilT))
def list5 {Γ : Ctx [0, 0]} : PExpr Δ Γ listNat :=
  consT [Term| 1] (consT [Term| 2] (consT [Term| 3] (consT [Term| 4] (consT [Term| 5] nilT))))
def tree {Γ : Ctx [0, 0]} : PExpr Δ Γ rose :=
  nodeT (consT [Term| 1] nilT)
    (.cons (nodeT (consT [Term| 10] (consT [Term| 20] nilT)) .nil) (.cons (nodeT nilT .nil) .nil))

example : ([Term| ‹sumT› ‹list123›] : Term Δ [] .nat []).run = (6 : Nat) := by kernel_rfl
example : ([Term| ‹headT› ‹list123›] : Term Δ [] (.option .nat) []).run =
    (some 1 : Option Nat) := rfl
example : ([Term| ‹headT› ‹nilT›] : Term Δ [] (.option .nat) []).run = (none : Option Nat) := rfl
example : ([Term| ‹roseSumT› ‹tree›] : Term Δ [] .nat []).run = (31 : Nat) := by kernel_rfl
example : ([Term| ‹fibLenT› ‹list5›] : Term Δ [] .nat []).run = (5 : Nat) := by kernel_rfl

/-! ## The other forms -/

example : ([Term| let _ := 3; let _ := ‹addT›(#0, #0); ‹addT›(#1, #0)] : Term Δ [] .nat []).run =
    (9 : Nat) := rfl
example : ([Term| let _ : Nat → Nat := fun _ => ‹addT›(#0, 1); #0 (#0 1)] :
    Term Δ [] .nat []).run = (3 : Nat) := rfl
example : ([Term| (fun (_ : Nat) => #0) 4] : Term Δ [] .nat []).run = (4 : Nat) := rfl
example : ([Term| let _ := (fun _ => #0 : Nat → Nat); #0 4] : Term Δ [] .nat []).run =
    (4 : Nat) := rfl
example : ([Term| (fun _ => if #0 then "yes" else "no") true] : Term Δ [] .string []).run =
    "yes" := rfl
example : ([Term| array_foldl #[1, 2, 3, 4] 0 ‹addT›(#1, #0)] : Term Δ [] .nat []).run =
    (10 : Nat) := rfl
example : ([Term| nat_rec 5 0 ‹addT›(#0, 2)] : Term Δ [] .nat []).run = (10 : Nat) := rfl
example : ([Term| lit ‹.int› ‹-3›] : Term Δ [] .int []).run = (-3 : Int) := rfl
example : ([Term| 3] : Term Δ [] [Ty| UInt8] []).run = (3 : UInt8) := rfl
/-- A branch in the middle of a computation, and an explicit join point. -/
example : ([Term| ‹addT›(if false then 1 else 2, 10)] : Term Δ [] .nat []).run = (12 : Nat) := rfl
example : ([Term| join _ (_ : Nat) := ‹addT›(#0, 1); if true then jump ^0 1 else jump ^0 2] :
    Term Δ [] .nat []).run = (2 : Nat) := rfl

/-- Enums: `enum_mk i` builds constructor `i`, `match` with numeral patterns takes it apart
    (the last branch is the default). -/
def enumT : Comp Δ [] [Ty| Enum 4 → Nat] :=
  [Term| fun _ => match #0 with | 0 => 10 | 1 => 11 | _ => 12]
example : ([Term| ‹enumT› (enum_mk 1)] : Term Δ [] .nat []).run = (11 : Nat) := rfl
example : ([Term| ‹enumT› (enum_mk 3)] : Term Δ [] .nat []).run = (12 : Nat) := rfl

/-! ## Printing -/

/-- info: [Term| fun _ _ => #1] : Comp Δ [] [Ty| Nat → Bool → Nat] -/
#guard_msgs in #check (Comp.lam (.ofComp (.lam (.ret (.bvar 1)))) : Comp Δ [] [Ty| Nat → Bool → Nat])

/--
info: @[expose] def TermNotationTest.sumT : {Γ : Ctx [0, 0]} → Comp Δ Γ [Ty| ‹listNat› → Nat] :=
fun {Γ} =>
  [Term|
    fun _ =>
      data_rec ‹listB› ‹fun x => [Ty| Nat]›
            (match #0 with
               | · => 0
               | (_, _) => let (_, _) := #1; ‹addT›(#2, #1))
          0
        #0]
-/
#guard_msgs in #print sumT

/--
info: @[expose] def TermNotationTest.headT : Comp Δ [] [Ty| ‹listNat› → Option Nat] :=
[Term|
  fun _ =>
    match data_out ‹listB› 0 #0 with
     | · => union_mk 0
     | (_, _) => union_mk 1 #0]
-/
#guard_msgs in #print headT

/--
info: @[expose] def TermNotationTest.enumT : Comp Δ [] [Ty| Enum 4 → Nat] :=
[Term|
  fun _ =>
    match #0 with
     | 0 => 10
     | 1 => 11
     | _ => 12]
-/
#guard_msgs in #print enumT

/--
info: @[expose] def TermNotationTest.fibLenT : Comp Δ [] [Ty| ‹listNat› → Nat] :=
[Term|
  fun _ =>
    data_brec ‹listB› ‹fun x => [Ty| Nat]› 1
          (match #0 with
             | · => 0
             | (_, _) =>
              let (_, _, _) := #1;
                match #2 with
                 | · => 1
                 | (_, _) => let (_, _) := #1; ‹addT›(#5, #1))
        0
      #0]
-/
#guard_msgs in #print fibLenT

/-- The terms written with the constructors are printed in the notation too. -/
def roseSumC : Comp Δ [] (.fn rose .nat) :=
  .lam (.ofComp (.data_rec roseB (fun _ => .nat) (fun ⟨0, _⟩ =>
    .record_casesOn (.bvar 0)
      (.letE sumT
        (.letE (.app (.bvar 0) (.bvar 1))
          (.letE (.array_foldl (.bvar 3) (.lit .nat 0)
              (.record_casesOn (.bvar 0) (.ret (addT (.bvar 3) (.bvar 1)))))
            (.ret (addT (.bvar 1) (.bvar 0)))))))
    0 (.bvar 0)))

/--
info: @[expose] def TermNotationTest.roseSumC : Comp Δ [] [Ty| ‹rose› → Nat] :=
[Term|
  fun _ =>
    data_rec ‹roseB› ‹fun x => [Ty| Nat]›
          (let (_, _) := #0;
              let _ := ‹sumT›;
                let _ := #0 #1; let _ := array_foldl #3 0 (let (_, _) := #0; ‹addT›(#3, #1)); ‹addT›(#1, #0))
        0
      #0]
-/
#guard_msgs in #print roseSumC

/-- The printed form reads back as the same term (the Lean binder `x` renamed `_`). -/
example : roseSumC = [Term|
  fun _ =>
    data_rec ‹roseB› ‹fun _ => [Ty| Nat]›
          (let (_, _) := #0;
              let _ := ‹sumT›;
                let _ := #0 #1; let _ := array_foldl #3 0 (let (_, _) := #0; ‹addT›(#3, #1)); ‹addT›(#1, #0))
        0
      #0] := rfl
example : roseSumC = roseSumT := rfl

/-- A join point is printed as one. -/
def joinT : Term Δ [.bool] .nat [] := [Term| ‹addT›(if #0 then 1 else 2, 10)]
/--
info: @[expose] def TermNotationTest.joinT : Term Δ [[Ty| Bool]] [Ty| Nat] [] :=
[Term| join _ _ := ‹addT›(#0, 10); if #0 then jump ^0 1 else jump ^0 2]
-/
#guard_msgs in #print joinT

-- The notation can be turned off.
/-- info: Comp.lam (Term.ret (PExpr.bvar 0 ⋯)) : Comp Δ [] (Ty.nat.fn Ty.nat) -/
#guard_msgs in
set_option pp.leanscript false in #check (Comp.lam (.ret (.bvar 0)) : Comp Δ [] [Ty| Nat → Nat])

/-! ## Delays

`thunk_mk`/`lazy_mk` delay a value and `thunk_force`/`lazy_force` force it; all four run as
the identity.  The contents of a forced delay are not known from the type of the result, so the
argument of `thunk_force`/`lazy_force` is written with its type when nothing else fixes it. -/

/-- info: [Term| fun _ => thunk_mk (let _ := lazy_mk #0; lazy_force #0)] : Comp Δ [] [Ty| Nat → Thunk Nat] -/
#guard_msgs in #check ([Term| fun _ => thunk_mk (lazy_force (lazy_mk #0))] : Comp Δ [] [Ty| Nat → Thunk Nat])

example : ([Term| fun _ => thunk_mk (lazy_force (lazy_mk #0))] :
    Term DSig.nil [] [Ty| Nat → Thunk Nat] []).run (3 : Nat) = (3 : Nat) := rfl

example : ([Term| fun _ => thunk_force (#0 : Thunk Nat)] : Comp Δ [] [Ty| Thunk Nat → Nat]) =
    .lam (.ofComp (.thunk_force (τ := .prim .nat) (.var .head))) := rfl

/-! ## Refused forms -/

/-- error: `nat_rec` is used as `nat_rec n z s` -/
#guard_msgs in example : Term Δ [] .nat [] := [Term| nat_rec 5 0]

/-- error: `union_mk` is used as `union_mk i a₁ … aₙ` -/
#guard_msgs in example : PExpr Δ [] (.option .nat) := [Term| union_mk]

-- An identifier is never a variable, nor a Lean term.
/-- error: unknown constructor `x`: a variable is written `#i` and a Lean term `‹x›` -/
#guard_msgs in example : Comp Δ [] [Ty| Nat → Nat] := [Term| fun _ => x]

/-- error: expected a Lean term here: a number, a string or `‹term›` -/
#guard_msgs in example : PExpr Δ [] listNat := [Term| data_in listB 0 (union_mk 0)]

end TermNotationTest

end
