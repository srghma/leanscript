import LeanScript.CtorFn
import LeanScript.Eval

open LeanScript

mutual
  inductive Process (α : Type) : Type 1 where
    | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat) : Process α
    | step (State : Type) (seed  : State) (trans : State → ProcessOption α State) : Process α
  inductive ProcessOption (α : Type) : Type → Type 1 where
    | none {State : Type} : ProcessOption α State
    | some {State : Type} (nextState : State) (value : α) (proc : Process α) : ProcessOption α State
end

namespace ProcessModel
abbrev natT : TyWf := .prim .nat
abbrev boolT : TyWf := .prim .bool
abbrev stringT : TyWf := .prim .string
def sig : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"append", stringT ⇒ stringT ⇒ stringT⟩], by decide⟩
def env : GlobalEnv sig.decls := (Nat.add, String.append, PUnit.unit)
def addT {Γ : Ctx} (a b : Term sig Γ natT) : Term sig Γ natT := .ap (.ap (.global .here) a) b
def appendT {Γ : Ctx} (a b : Term sig Γ stringT) : Term sig Γ stringT :=
  .ap (.ap (.global (.there .here)) a) b

abbrev optionTy (S P : TyWf) : TyWf := #leanscript_layout `ProcessOption `some natT S P
abbrev stepTy (S O : TyWf) : TyWf := #leanscript_layout `Process `step natT S O
abbrev haltTy (H : TyWf) : TyWf := #leanscript_layout `Process `halt natT H

abbrev mixedLeafTy : TyWf := haltTy boolT
abbrev mixedOpt2Ty : TyWf := optionTy stringT mixedLeafTy
abbrev mixedProc2Ty : TyWf := stepTy stringT mixedOpt2Ty
abbrev mixedOpt1Ty : TyWf := optionTy natT mixedProc2Ty
abbrev mixedTy : TyWf := stepTy natT mixedOpt1Ty

def mixedProcess_term : Term sig [] mixedTy :=
  #leanscript_ctor `Process `step natT natT mixedOpt1Ty (.nat_mk 0) (.lam
    (#leanscript_ctor `ProcessOption `some natT natT mixedProc2Ty
      (addT (.var (v♯0)) (.nat_mk 1)) (.nat_mk 42)
      (#leanscript_ctor `Process `step natT stringT mixedOpt2Ty (.string_mk "hello") (.lam
        (#leanscript_ctor `ProcessOption `some natT stringT mixedLeafTy
          (appendT (.var (v♯0)) (.string_mk "!")) (.nat_mk 99)
          (#leanscript_ctor `Process `halt natT boolT
            (.lam (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0)))))))))

local macro:max "run" t:term:max : term => `(Term.run (Sg := sig) env $t)

example : run mixedProcess_term =
    (0, fun n => ⟨⟨1, by decide⟩, (n + 1, 42,
      ("hello", fun s => ⟨⟨1, by decide⟩, (s ++ "!", 99,
        (fun b => match b with | true => 1 | false => 0), ())⟩, ()), ())⟩, ()) := rfl

inductive Shape3 | a | b | c
def s3 : Term sig [] (#leanscript_layout `Shape3 `b) := #leanscript_ctor `Shape3 `b
example : run s3 = ⟨1, by decide⟩ := rfl
def bt : Term sig [] boolT := #leanscript_ctor `Bool `true
example : run bt = true := rfl
def someT : Term sig [] (#leanscript_layout `Option `some natT) := #leanscript_ctor `Option `some natT (.nat_mk 3)
#check someT
example : (#leanscript_layout `Option `some natT) = tyWfOf (Option Nat) := rfl
def pairT := (#leanscript_ctor `Prod natT boolT (.nat_mk 3) (.bool_mk true) : Term sig [] _)
example : run pairT = (3, true, ()) := rfl
structure Wrap where
  val : Nat
  u : Unit
  p : val = val
def w : Term sig [] natT := #leanscript_ctor `Wrap (.nat_mk 5)
structure Fancy (S : Type) where
  o : Option S
  l : List S
  f : Unit → S → Array S
  n : Nat × S
#check #leanscript_ctor `Fancy
#print Fancy.mk.leanScriptCtor
mutual
  inductive Client (Req Resp : Type) : Type 1 where
    | stop (ServerState : Type) (get : ServerState -> Nat) : Client Req Resp
    | mk   (ClientState : Type) (seed : ClientState) (send : ClientState → Req × Server Req Resp) : Client Req Resp
  inductive Server (Req Resp : Type) : Type 1 where
    | stop (ClientState : Type) (get : ClientState -> Nat) : Server Req Resp
    | mk   (ServerState : Type) (seed : ServerState) (receive : ServerState → Req → Resp × Client Req Resp) : Server Req Resp
end
#check #leanscript_ctor `Client `mk
#check #leanscript_ctor `Server `mk
structure Keyed where
  State : Type
  Elem  : State → Type
  seed  : State
  get   : (s : State) → Elem s
#check #leanscript_ctor `Keyed
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
#check #leanscript_ctor `Vec `cons
structure Dep where
  n : Nat
  f : Fin n
#check #leanscript_ctor `Dep
end ProcessModel
