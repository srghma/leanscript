module

public import LeanScript.Expr.Term
public import LeanScript.Eval
public import LeanScript.FamilyRecFacts

@[expose] public section

set_option autoImplicit false

namespace TyTests.Scratch

open LeanScript

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

abbrev natT : TyWf := .prim .nat

def sigAdd : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"mul", natT ⇒ natT ⇒ natT⟩], by decide⟩

def addT {Γ : Ctx} (a b : Term sigAdd Γ natT) : Term sigAdd Γ natT :=
  .ap (.ap (.global .here) a) b

/-- Member `0`: the Peano naturals. -/
def memPe : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.familyMember 0).toTyWfIn, []⟩ []))

/-- Member `1`: a list of naturals. -/
def memLs : LeanFamMemberSchema (TyWfIn 2) :=
  .ctors (.skip (.here ⟨(Ty.prim .nat).toTyWfIn, [(Ty.familyMember 1).toTyWfIn]⟩ []))

def famPe : LeanMutualRecFamily (TyWfIn 2) := .selectedThenMore [] memPe memLs []
def famLs : LeanMutualRecFamily (TyWfIn 2) := .selectedLast memPe [] memLs

def peWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famPe) := by ty_wf
def lsWf : Ty.Wf (TyWf.mutualRecursiveFamilyTy famLs) := by ty_wf

def peTy : TyWf := .mutualRecursiveFamily famPe peWf
def lsTy : TyWf := .mutualRecursiveFamily famLs lsWf

example : famPe.members = [memPe, memLs] := rfl
example : famLs.members = [memPe, memLs] := rfl

abbrev succFields : List (TyWfIn 2) := [(Ty.familyMember 0).toTyWfIn]

abbrev pbind (τ : TyWf) : List (TyWfIn 2) → List TyWf := TyWf.famRecBinders famPe peWf τ

example (τ : TyWf) : pbind τ [] = [] := rfl
example (τ : TyWf) : pbind τ succFields = [peTy, τ] := rfl

end TyTests.Scratch
