module

public import LeanScript.TermElab.Notation
public import LeanScript.Term.Build
public import LeanScript.Term.ExternShorthands
public meta import LeanScript.TacticElab.KernelRfl

@[expose] public section

set_option autoImplicit false

/-!
# The `[Term| …]` notation (`LeanScript.TermElab.Notation`)

Programs written in the notation (de Bruijn variables `#i`, constructor names) in direct style
and normalised to the grammar of normal forms, run by `Term.run` and checked by `rfl`
(`kernel_rfl` for the longer runs); checks that the notation builds the expected normal forms
(closures bound by `letV`, redexes on known values computed, calls with an open operand kept),
and the forms it refuses.
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

/-- Closed programs of type `τ`. -/
abbrev Prog (τ : Ty [0, 0]) : Type := Term Δ 0 [] [] τ [] none

/-- Statements with one unknown of type `σ`, at level `0`. -/
abbrev T1 (σ τ : Ty [0, 0]) : Type := Term Δ 0 [] [⟨σ, .many, 0⟩] τ [] (some 0)

/-- The innermost unknown. -/
abbrev x0 {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]} {τ : Ty [0, 0]} {ℓ : Nat} :
    PExpr Δ Φ (⟨τ, .many, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.head (by decide)))

/-- The unknown one binder further out. -/
abbrev x1 {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]} {τ : Ty [0, 0]} {ℓ : Nat} {b : UBinder [0, 0]} :
    PExpr Δ Φ (b :: ⟨τ, .many, ℓ⟩ :: Γ) τ (some ℓ) :=
  .neu (.var (.tail (.head (by decide))))

/-! ## Building values -/

section
variable {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]}

def nilT : PExpr Δ Φ Γ listNat none := [Term| data_in ‹listB› 0 (union_mk 0)]

-- [SKIPPED BY PROFILE_LAKE] /-- The notation builds the same closed values as the constructors. -/
-- [SKIPPED BY PROFILE_LAKE] example : (nilT : PExpr Δ Φ Γ listNat none) = .data_in listB 0 (.union_mk .two₁ .nil) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (3, true, "a")] : PExpr Δ Φ Γ [Ty| Nat × Bool × String] none) =
-- [SKIPPED BY PROFILE_LAKE]     .record_mk (.cons (.lit .nat 3) (.cons (.lit .bool true) (.cons (.lit .string "a") .nil))) :=
-- [SKIPPED BY PROFILE_LAKE]   rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| data_in ‹listB› 0 (union_mk 1 7 ‹nilT›)] : PExpr Δ Φ Γ listNat none) =
-- [SKIPPED BY PROFILE_LAKE]     .data_in listB 0 (.union_mk .two₂ (.cons (.lit .nat 7) (.cons nilT .nil))) := rfl

end

-- [SKIPPED BY PROFILE_LAKE] /-- A pure expression in tail position is the answer of the statement. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (3, true)] : Prog [Ty| Nat × Bool]) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (.record_mk (.cons (.lit .nat 3) (.cons (.lit .bool true) .nil))) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A closure is a known value, bound by `letV` and returned by name; the body of a curried
-- [SKIPPED BY PROFILE_LAKE]     function binds its inner closure, which is open (it mentions the outer parameter). -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| fun _ _ => #1] : Prog [Ty| Nat → Bool → Nat]) =
-- [SKIPPED BY PROFILE_LAKE]     .letV .many (.lam (u := .many) (.closed
-- [SKIPPED BY PROFILE_LAKE]       (.letV .many (.lam (u := .many) (.opened (.ret x1) (Nat.le_refl 1))) (.ret (.kvar .head)))))
-- [SKIPPED BY PROFILE_LAKE]       (.ret (.kvar .head)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A free `#i` is an unknown of the enclosing context: the closure is open. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| fun _ => extern ‹.lean_nat_add› #0 #1] : T1 .nat [Ty| Nat → Nat]) =
-- [SKIPPED BY PROFILE_LAKE]     .letV .many (.lam (u := .many) (.opened (.ret (PExpr.lean_nat_add x0 x1)) (Nat.le_refl 0)))
-- [SKIPPED BY PROFILE_LAKE]       (.ret (.kvar .head)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A call of an extern with an open argument is a neutral expression: calls nest, with no
-- [SKIPPED BY PROFILE_LAKE]     `let`. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| extern ‹.lean_nat_add› (extern ‹.lean_nat_add› #0 1) 2] : T1 .nat .nat) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (PExpr.lean_nat_add (PExpr.lean_nat_add x0 (.lit .nat 1)) (.lit .nat 2)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A call of an extern on closed arguments is computed. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| extern ‹.lean_nat_add› (extern ‹.lean_nat_add› 3 1) 2] : Prog .nat) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (.lit .nat 6) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- An `if` with pure branches in the middle of an expression is the pure conditional. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| extern ‹.lean_nat_add› (if #0 then 1 else 2) 10] : T1 .bool .nat) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (PExpr.lean_nat_add (.neu (.cond (.var (.head (by decide))) (.lit .nat 1) (.lit .nat 2)))
-- [SKIPPED BY PROFILE_LAKE]       (.lit .nat 10)) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- On a known condition, the branch is chosen. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| extern ‹.lean_nat_add› (if false then 1 else 2) 10] : Prog .nat) =
-- [SKIPPED BY PROFILE_LAKE]     .ret (.lit .nat 12) := rfl

/-! ## Folds -/

/-- `List.sum`: the branch of the fold receives (`#0`) the body of `List Nat` whose hole is
    the pair `(tail, sum of the tail)`. -/
def sumT : Prog [Ty| ‹listNat› → Nat] :=
  [Term| fun _ => data_rec ‹listB› ‹fun _ => .nat›
    (match #0 with
      | · => 0
      | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #2 #1)
    0 #0]

/-- `List.head?`, by one layer out. -/
def headT : Prog [Ty| ‹listNat› → Option Nat] :=
  [Term| fun _ => match data_out ‹listB› 0 #0 with | · => union_mk 0 | (_, _) => union_mk 1 #0]

/-- The sum of every number in a rose tree: the branch calls the fold of the older block (a
    closure, shared by name). -/
def roseSumT : Prog [Ty| ‹rose› → Nat] :=
  [Term| fun _ => data_rec ‹roseB› ‹fun _ => .nat›
    (let (_, _) := #0;
     let _ := (fun (_ : ‹listNat›) => data_rec ‹listB› ‹fun _ => .nat›
       (match #0 with
         | · => 0
         | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #2 #1) 0 #0);
     extern ‹.lean_nat_add› (#0 #1) (array_foldl #2 0 (let (_, _) := #0; extern ‹.lean_nat_add› #3 #1)))
    0 #0]

/-- Course-of-values recursion: the Fibonacci number of the length of a list. -/
def fibLenT : Prog [Ty| ‹listNat› → Nat] :=
  [Term| fun _ => data_brec ‹listB› ‹fun _ => .nat› 1
    (match #0 with
      | · => 0
      | (_, _) =>
        let (_, _, _) := #1;
        match #2 with
        | · => 1
        | (_, _) => let (_, _) := #1; extern ‹.lean_nat_add› #5 #1)
    0 #0]

/-! ## Running them -/

section
variable {Φ : KCtx [0, 0]} {Γ : UCtx [0, 0]}

def consT {o₁ o₂ : Lvl} (x : PExpr Δ Φ Γ .nat o₁) (xs : PExpr Δ Φ Γ listNat o₂) :
    PExpr Δ Φ Γ listNat (Lvl.meet o₁ (Lvl.meet o₂ none)) :=
  .data_in listB 0 (.union_mk .two₂ (.cons x (.cons xs .nil)))
def nodeT {o₁ o₂ : Lvl} (xs : PExpr Δ Φ Γ listNat o₁) (cs : Elems Δ Φ Γ rose o₂) :
    PExpr Δ Φ Γ rose (Lvl.meet o₁ (Lvl.meet o₂ none)) :=
  .data_in roseB 0 (.record_mk (.cons xs (.cons (.array_mk cs) .nil)))

def list123 : PExpr Δ Φ Γ listNat none :=
  consT [Term| 1] (consT [Term| 2] (consT [Term| 3] nilT))
def list5 : PExpr Δ Φ Γ listNat none :=
  consT [Term| 1] (consT [Term| 2] (consT [Term| 3] (consT [Term| 4] (consT [Term| 5] nilT))))
def tree : PExpr Δ Φ Γ rose none :=
  nodeT (consT [Term| 1] nilT)
    (.cons (nodeT (consT [Term| 10] (consT [Term| 20] nilT)) .nil) (.cons (nodeT nilT .nil) .nil))

end

-- [SKIPPED BY PROFILE_LAKE] example : sumT.run (list123 (Φ := []) (Γ := [])).run = (6 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : headT.run (list123 (Φ := []) (Γ := [])).run = (some 1 : Option Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : headT.run (nilT (Φ := []) (Γ := [])).run = (none : Option Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : roseSumT.run (tree (Φ := []) (Γ := [])).run = (31 : Nat) := by kernel_rfl
-- [SKIPPED BY PROFILE_LAKE] example : fibLenT.run (list5 (Φ := []) (Γ := [])).run = (5 : Nat) := by kernel_rfl

-- [SKIPPED BY PROFILE_LAKE] /-- A closed closure applied to a closed argument is β-reduced while normalising, and the case
-- [SKIPPED BY PROFILE_LAKE]     analysis of the literal list is computed: no call and no case analysis is left (the list
-- [SKIPPED BY PROFILE_LAKE]     literals are bound by `letV`, and are dead). -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (fun _ => match data_out ‹listB› 0 #0 with | · => union_mk 0 | (_, _) => union_mk 1 #0)
-- [SKIPPED BY PROFILE_LAKE]     (data_in ‹listB› 0 (union_mk 1 1 (data_in ‹listB› 0 (union_mk 0))))] : Prog (.option .nat)).run =
-- [SKIPPED BY PROFILE_LAKE]     (some 1 : Option Nat) := rfl

/-! ## The other forms -/

-- [SKIPPED BY PROFILE_LAKE] example : ([Term| let _ := 3; let _ := extern ‹.lean_nat_add› #0 #0; extern ‹.lean_nat_add› #1 #0] :
-- [SKIPPED BY PROFILE_LAKE]     Prog .nat) = .ret (.lit .nat 9) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| let _ : Nat → Nat := fun _ => extern ‹.lean_nat_add› #0 1; #0 (#0 1)] :
-- [SKIPPED BY PROFILE_LAKE]     Prog .nat).run = (3 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (fun (_ : Nat) => #0) 4] : Prog .nat) = .ret (.lit .nat 4) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (fun _ => if #0 then "yes" else "no") true] : Prog .string).run = "yes" := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| array_foldl #[1, 2, 3, 4] 0 (extern ‹.lean_nat_add› #1 #0)] : Prog .nat).run =
-- [SKIPPED BY PROFILE_LAKE]     (10 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| nat_rec 5 0 (extern ‹.lean_nat_add› #0 2)] : Prog .nat).run = (10 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| lit ‹.int› ‹-3›] : Prog .int).run = (-3 : Int) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| 3] : Prog [Ty| UInt8]).run = (3 : UInt8) := rfl

/-- A loop whose count is unknown is kept, as a computation bound by `letE`. -/
def twiceT : T1 .nat .nat := [Term| nat_rec #0 0 (extern ‹.lean_nat_add› #0 2)]

-- [SKIPPED BY PROFILE_LAKE] example : twiceT = .letE .many
-- [SKIPPED BY PROFILE_LAKE]     (.nat_rec (u₁ := .many) (u₂ := .many) x0 (.lit .nat 0)
-- [SKIPPED BY PROFILE_LAKE]       (.closed (.ret (PExpr.lean_nat_add x0 (.lit .nat 2)))) rfl) (.ret x0) := rfl

-- [SKIPPED BY PROFILE_LAKE] example : twiceT.eval PUnit.unit (5 : Nat) PUnit.unit = (10 : Nat) := rfl

/-- An explicit join point, on an unknown condition. -/
def joinT : Prog [Ty| Bool → Nat] :=
  [Term| fun _ => join _ (_ : Nat) := extern ‹.lean_nat_add› #0 1; if #0 then jump ^0 1 else jump ^0 2]
-- [SKIPPED BY PROFILE_LAKE] example : joinT.run true = (2 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : joinT.run false = (3 : Nat) := rfl

-- [SKIPPED BY PROFILE_LAKE] /-- On a known condition, the jump is inlined. -/
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| join _ (_ : Nat) := extern ‹.lean_nat_add› #0 1; if true then jump ^0 1 else jump ^0 2] :
-- [SKIPPED BY PROFILE_LAKE]     Prog .nat) = .ret (.lit .nat 2) := rfl

/-- Enums: `enum_mk i` builds constructor `i`, `match` with numeral patterns takes it apart
    (the last branch is the default). -/
def enumT : Prog [Ty| Enum 4 → Nat] :=
  [Term| fun _ => match #0 with | 0 => 10 | 1 => 11 | _ => 12]
-- [SKIPPED BY PROFILE_LAKE] example : enumT.run (1 : Fin 4) = (11 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : enumT.run (3 : Fin 4) = (12 : Nat) := rfl
-- [SKIPPED BY PROFILE_LAKE] example : ([Term| (fun (_ : Enum 4) => match #0 with | 0 => 10 | 1 => 11 | _ => 12) (enum_mk 1)] :
-- [SKIPPED BY PROFILE_LAKE]     Prog .nat) = .ret (.lit .nat 11) := rfl

/-! ## Delays

`thunk_mk`/`lazy_mk` delay a value and `thunk_force`/`lazy_force` force it; all four run as
the identity.  A delay is a known value; forcing an unknown one (or an open known one) is kept
as a computation. -/

-- [SKIPPED BY PROFILE_LAKE] example : ([Term| fun _ => thunk_force (#0 : Thunk Nat)] : Prog [Ty| Thunk Nat → Nat]) =
-- [SKIPPED BY PROFILE_LAKE]     .letV .many (.lam (u := .many) (.closed
-- [SKIPPED BY PROFILE_LAKE]       (.letE .many (.thunk_force (τ := .prim .nat) x0) (.ret x0))))
-- [SKIPPED BY PROFILE_LAKE]       (.ret (.kvar .head)) := rfl

/-! ## Refused forms -/

/-- error: `nat_rec` is used as `nat_rec n z s` -/
#guard_msgs in example : Prog .nat := [Term| nat_rec 5 0]

/-- error: `union_mk` is used as `union_mk i a₁ … aₙ` -/
#guard_msgs in example : PExpr Δ [] [] (.option .nat) none := [Term| union_mk]

-- An identifier is never a variable, nor a Lean term.
/-- error: unknown constructor `x`: a variable is written `#i` and a Lean term `‹x›` -/
#guard_msgs in example : Prog [Ty| Nat → Nat] := [Term| fun _ => x]

/-- error: expected a Lean term here: a number, a string or `‹term›` -/
#guard_msgs in example : PExpr Δ [] [] listNat none := [Term| data_in listB 0 (union_mk 0)]

end TermNotationTest

end
