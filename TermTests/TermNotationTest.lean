module

public import LeanScript.TermNotation
public import LeanScript.Eval

@[expose] public section

set_option autoImplicit false

/-!
# The `[Term| …]` notation (`LeanScript.TermNotation`)

The programs of `TermTests.TermTest`, written with named variables, run by `Term.run` and
checked by `rfl`; checks that the notation builds the same terms as the constructors; how
terms are printed back (`#guard_msgs`), and that the printed form reads back as the same term.
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

/-- `Nat.add`, as an extern. -/
def addT {Γ : Ctx [0, 0]} (a b : Term Δ Γ .nat) : Term Δ Γ .nat :=
  [Term| extern "Nat.add" ‹fun v => Nat.add v.1 v.2.1› ‹a› ‹b›]

/-! ## Building values -/

def consT {Γ : Ctx [0, 0]} (x : Term Δ Γ .nat) (xs : Term Δ Γ listNat) : Term Δ Γ listNat :=
  [Term| roll listB 0 (inj 1 (x, xs))]
def nilT {Γ : Ctx [0, 0]} : Term Δ Γ listNat := [Term| roll listB 0 (inj 0)]
def nodeT {Γ : Ctx [0, 0]} (xs : Term Δ Γ listNat) (cs : Elems Δ Γ rose) : Term Δ Γ rose :=
  [Term| roll roseB 0 (xs, ‹.array_mk cs›)]

/-- The notation builds the same terms as the constructors. -/
example {Γ : Ctx [0, 0]} (x : Term Δ Γ .nat) (xs : Term Δ Γ listNat) :
    consT x xs = .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil))) := rfl
example {Γ : Ctx [0, 0]} : (nilT : Term Δ Γ listNat) = .data_in listB 0 (.union_mk .two₁ .nil) :=
  rfl
example : ([Term| fun x y => x] : Term Δ [] [Ty| Nat → Bool → Nat]) =
    .lam (.lam (.var (.tail .head))) := rfl
example : ([Term| (3, true, "a")] : Term Δ [] [Ty| Nat × Bool × String]) =
    .record_mk (.cons (.lit .nat 3) (.cons (.lit .bool true) (.cons (.lit .string "a") .nil))) :=
  rfl

/-! ## Folds -/

/-- `List.sum`: the branch of the fold receives the body of `List Nat` whose hole is the pair
    `(tail, sum of the tail)`. -/
def sumT {Γ : Ctx [0, 0]} : Term Δ Γ [Ty| listNat → Nat] :=
  [Term| fun xs => fold listB ‹fun _ => .nat› 0 xs (fun l =>
    match l with
    | · => 0
    | (n, p) => let (_, s) := p; ‹addT›(n, s))]

/-- `List.head?`, by one layer out. -/
def headT : Term Δ [] [Ty| listNat → Option Nat] :=
  [Term| fun xs => match unroll listB 0 xs with | · => inj 0 | (n, _) => inj 1 n]

/-- The sum of every number in a rose tree: the branch calls the fold of the older block. -/
def roseSumT : Term Δ [] [Ty| rose → Nat] :=
  [Term| fun t => fold roseB ‹fun _ => .nat› 0 t (fun node =>
    let (xs, children) := node;
    ‹addT›(‹sumT› xs, foldl (fun acc c => let (_, a) := c; ‹addT›(acc, a)) 0 children))]

/-- Course-of-values recursion: the Fibonacci number of the length of a list. -/
def fibLenT : Term Δ [] [Ty| listNat → Nat] :=
  [Term| fun xs => brec listB ‹fun _ => .nat› 1 0 xs (fun l =>
    match l with
    | · => 0
    | (_, w) =>
      let (_, ft, body) := w;
      match body with
      | · => 1
      | (_, w') => let (_, ft') := w'; ‹addT›(ft, ft'))]

/-! ## Running them -/

def list123 : Term Δ [] listNat := consT [Term| 1] (consT [Term| 2] (consT [Term| 3] nilT))
def list5 : Term Δ [] listNat :=
  consT [Term| 1] (consT [Term| 2] (consT [Term| 3] (consT [Term| 4] (consT [Term| 5] nilT))))
def tree : Term Δ [] rose :=
  nodeT (consT [Term| 1] nilT)
    (.cons (nodeT (consT [Term| 10] (consT [Term| 20] nilT)) .nil) (.cons (nodeT nilT .nil) .nil))

example : [Term| ‹sumT› ‹list123›].run = (6 : Nat) := rfl
example : [Term| ‹headT› ‹list123›].run = (some 1 : Option Nat) := rfl
example : [Term| ‹headT› ‹nilT›].run = (none : Option Nat) := rfl
example : [Term| ‹roseSumT› ‹tree›].run = (31 : Nat) := rfl
example : [Term| ‹fibLenT› ‹list5›].run = (5 : Nat) := rfl

/-! ## The other forms -/

example : ([Term| let x := 3; let y := ‹addT›(x, x); ‹addT›(x, y)] : Term Δ [] .nat).run = (9 : Nat) := rfl
example : ([Term| let f : Nat → Nat := fun x => ‹addT›(x, 1); f (f 1)] : Term Δ [] .nat).run = (3 : Nat) :=
  rfl
example : ([Term| (fun (x : Nat) => x) 4] : Term Δ [] .nat).run = (4 : Nat) := rfl
example : ([Term| let f := (fun x => x : Nat → Nat); f 4] : Term Δ [] .nat).run = (4 : Nat) := rfl
example : ([Term| (fun b => if b then "yes" else "no") true] : Term Δ [] .string).run = "yes" := rfl
example : ([Term| foldl (fun acc x => ‹addT›(acc, x)) 0 #[1, 2, 3, 4]] : Term Δ [] .nat).run = (10 : Nat) :=
  rfl
example : ([Term| natRec 5 0 (fun _ ih => ‹addT›(ih, 2))] : Term Δ [] .nat).run = (10 : Nat) := rfl
example : ([Term| lit ‹.int› ‹-3›] : Term Δ [] .int).run = (-3 : Int) := rfl
example : ([Term| 3] : Term Δ [] [Ty| UInt8]).run = (3 : UInt8) := rfl

/-- Enums: `enum i` builds constructor `i`, `match` with numeral patterns takes it apart (the
    last branch is the default). -/
def enumT : Term Δ [] [Ty| Enum 4 → Nat] :=
  [Term| fun e => match e with | 0 => 10 | 1 => 11 | _ => 12]
example : [Term| ‹enumT› (enum 1)].run = (11 : Nat) := rfl
example : [Term| ‹enumT› (enum 3)].run = (12 : Nat) := rfl

/-- `#i` is a variable of the enclosing context, by index. -/
example : ([Term| fun y => ‹addT›(#0, #1)] : Term Δ [.nat] [Ty| Nat → Nat]) =
    [Term| fun y => ‹addT›(y, #1)] := rfl

/-! ## Printing -/

/-- info: [Term| fun x₀ x₁ => x₀] : Term Δ [] [Ty| Nat → Bool → Nat] -/
#guard_msgs in #check (Term.lam (.lam (.bvar 1)) : Term Δ [] [Ty| Nat → Bool → Nat])

/--
info: @[expose] def TermNotationTest.sumT : {Γ : Ctx [0, 0]} → Term Δ Γ [Ty| listNat → Nat] :=
fun {Γ} =>
  [Term|
    fun x₀ =>
      fold listB ‹fun x => [Ty| Nat]› 0 x₀
        (fun x₁ =>
            match x₁ with
             | · => 0
             | (x₂, x₃) => let (x₄, x₅) := x₃; ‹addT›(x₂, x₅))]
-/
#guard_msgs in #print sumT

/--
info: @[expose] def TermNotationTest.headT : Term Δ [] [Ty| listNat → Option Nat] :=
[Term|
  fun x₀ =>
    match unroll listB 0 x₀ with
     | · => inj 0
     | (x₁, x₂) => inj 1 x₁]
-/
#guard_msgs in #print headT

/--
info: @[expose] def TermNotationTest.enumT : Term Δ [] [Ty| Enum 4 → Nat] :=
[Term|
  fun x₀ =>
    match x₀ with
     | 0 => 10
     | 1 => 11
     | _ => 12]
-/
#guard_msgs in #print enumT

/-- The terms written with the constructors are printed in the notation too. -/
def roseSumC : Term Δ [] (.fn rose .nat) :=
  .lam (.data_rec roseB (fun _ => .nat) (fun ⟨0, _⟩ =>
    .record_casesOn (.bvar 0)
      (addT (.app sumT (.bvar 0))
        (.array_foldl (.bvar 1) (.lit .nat 0)
          (.record_casesOn (.bvar 0) (addT (.bvar 3) (.bvar 1))))))
    0 (.bvar 0))

/--
info: @[expose] def TermNotationTest.roseSumC : Term Δ [] [Ty| rose → Nat] :=
[Term|
  fun x₀ =>
    fold roseB ‹fun x => [Ty| Nat]› 0 x₀
      (fun x₁ => let (x₂, x₃) := x₁; ‹addT›(sumT x₂, foldl (fun x₄ x₅ => let (x₆, x₇) := x₅; ‹addT›(x₄, x₇)) 0 x₃))]
-/
#guard_msgs in #print roseSumC

/-- The printed form reads back as the same term. -/
example : roseSumC = [Term|
  fun x₀ =>
    fold roseB ‹fun _ => [Ty| Nat]› 0 x₀
      (fun x₁ =>
        let (x₂, x₃) := x₁;
          ‹addT›(sumT x₂, foldl (fun x₄ x₅ => let (x₆, x₇) := x₅; ‹addT›(x₄, x₇)) 0 x₃))] := rfl
example : roseSumC = roseSumT := rfl

-- The notation can be turned off.
/-- info: (Term.bvar 0 ⋯).lam : Term Δ [] (Ty.nat.fn Ty.nat) -/
#guard_msgs in
set_option pp.leanscript false in #check (Term.lam (.bvar 0) : Term Δ [] [Ty| Nat → Nat])

/-! ## Refused forms -/

/-- error: `natRec` binds 2 name(s) here -/
#guard_msgs in example : Term Δ [] .nat := [Term| natRec 5 0 (fun ih => ih)]

/-- error: `inj` is used as `inj i`, `inj i a` or `inj i (a, b, …)` -/
#guard_msgs in example : Term Δ [] (.option .nat) := [Term| inj]

end TermNotationTest

end
