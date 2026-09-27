import LeanScript.Term.Build
import LeanScript.Term.ExternShorthands
import LeanScript.TermElab.Notation
open LeanScript

def t6 : Term DSig.nil 0 [] [] (.fn (.option .nat) .nat) [] none :=
  [Term| fun (_ : Option Nat) => match #0 with | · => 0 | _ => #0]
example : t6.run (some (4 : Nat)) = (4 : Nat) := rfl

example : UCtx.annot (ks := []) 1 (Ctor.fields (Fields.one (Ty.prim LeanPrimTy.nat))).binds [] = [⟨.nat, .many, 1⟩] := rfl
