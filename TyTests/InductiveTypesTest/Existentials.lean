import TyTests.InductiveTypesTest.NestedRecursion
import LeanScript.Eval

/-!
# `deriving LeanScriptTyWf`: declarations with existentially typed fields

Part of the `deriving LeanScriptTyWf` suite that starts in `TyTests.InductiveTypesTest.Basic`; like it, this
file deliberately does not start with `module`.
-/

open LeanScript

-- 1. recursive tagged union with existential in both constructors and different

mutual
  inductive Process (α : Type) : Type 1 where
    | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat) : Process α
    | step (State : Type)
           (seed  : State)
           (trans : State → ProcessOption α State) : Process α
           -- same as `(trans : State → Option (State × α × Process α)) : Process α`

  inductive ProcessOption (α : Type) : Type → Type 1 where
    | none {State : Type} : ProcessOption α State
    | some {State : Type} (nextState : State)
                          (value : α)
                          (proc : Process α) : ProcessOption α State
end

/--
error: the type `Process` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Process, ProcessOption

-- TODO: we should be able to model using Term
def mixedProcess : Process Nat :=
  -- Top level: State is Nat
  Process.step Nat 0 (fun n =>
    -- We must return `ProcessOption Nat Nat`
    ProcessOption.some (n + 1) 42 (
      -- Next level: State is String
      Process.step String "hello" (fun s =>
        -- We must return `ProcessOption Nat String`
        ProcessOption.some (s ++ "!") 99 (
          -- Leaf level: a `Process Nat`
          Process.halt Bool (fun b => if b then 1 else 0)
        )
      )
    )
  )

def varyingProcess : Process Nat :=
  Process.step Nat 0 (fun n =>
    if n = 0 then
      ProcessOption.some 1 7 (Process.step Unit () (fun _ => ProcessOption.none))
    else
      ProcessOption.some 1 7 (Process.step Bool true (fun _ => ProcessOption.none)))

/-! ### `mixedProcess` and `varyingProcess`, as terms

Both values are closed, so every existential witness they use is known, and each value
is described with ordinary records, tagged unions and functions of the language. The
existential is simply replaced, at each constructor application, by the witness that
application uses:

* `Process.step S seed trans` is the record `{ seed : S, trans : S ⇒ … }`;
* `Process.halt H get` has one field, so it is that field, `H ⇒ nat`, as for any
  one-field constructor;
* `ProcessOption α S` has no existential of its own, so it is the tagged union
  `none | some (nextState : S) (value : α) (proc : …)` with Lean's tags (`none` = 0,
  `some` = 1);
* `Unit` is erased as everywhere in the language: a `Unit` field is dropped, and a
  `Unit →` binder is dropped;
* where values built with *different* witnesses meet (the two branches of the `if` in
  `varyingProcess`), each one is injected into a tagged union with one constructor per
  layout that occurs there.

So the type of the term is determined by the value, not by `Process Nat` alone. The one
free choice is the type of `proc` in a `ProcessOption` in which only `none` is ever built
(the inner transitions of `varyingProcess`): no process is ever stored there, so any
closed type works, and `nat` is used.

Arithmetic and string append are external to the language, so they are the two
declarations of the signature `ProcessModel.sig`. The `example`s at the end check, by
`rfl`, that each term evaluates to the Lean definition with the witnesses filled in.
-/

namespace ProcessModel

abbrev natT : TyWf := .prim .nat
abbrev boolT : TyWf := .prim .bool
abbrev stringT : TyWf := .prim .string

/-- The signature: `add : nat ⇒ nat ⇒ nat` (for `n + 1`) and
    `append : string ⇒ string ⇒ string` (for `s ++ "!"`). -/
def sig : Sig :=
  ⟨[⟨"add", natT ⇒ natT ⇒ natT⟩, ⟨"append", stringT ⇒ stringT ⇒ stringT⟩], by decide⟩

/-- The values of the declarations of `sig`. -/
def env : GlobalEnv sig.decls := (Nat.add, String.append, PUnit.unit)

/-- `a + b`. -/
def addT {Γ : Ctx} (a b : Term sig Γ natT) : Term sig Γ natT :=
  .ap (.ap (.global .here) a) b

/-- `a ++ b`. -/
def appendT {Γ : Ctx} (a b : Term sig Γ stringT) : Term sig Γ stringT :=
  .ap (.ap (.global (.there .here)) a) b

/-- `ProcessOption Nat S` whose `proc` field has type `P`:
    `none | some (nextState : S) (value : nat) (proc : P)`. -/
abbrev optionU (S P : TyWf) : LeanTaggedUnionSchema TyWf := .skip (.here ⟨S, [natT, P]⟩ [])
/-- The type of `optionU S P`. -/
abbrev optionTy (S P : TyWf) : TyWf := .taggedUnion (optionU S P)
/-- `Process.step S seed trans`, whose transition answers with `O`:
    the record `{ seed : S, trans : S ⇒ O }`. -/
abbrev stepR (S O : TyWf) : LeanRecordSchema TyWf := ⟨S, S ⇒ O, []⟩
/-- The type of `stepR S O`. -/
abbrev stepTy (S O : TyWf) : TyWf := .record (stepR S O)
/-- `Process.halt H get`: its one field, `get : H ⇒ nat`. -/
abbrev haltTy (H : TyWf) : TyWf := H ⇒ natT

/-! #### `mixedProcess` -/

/-- Leaf level: `Process.halt Bool _`. -/
abbrev mixedLeafTy : TyWf := haltTy boolT
/-- `ProcessOption Nat String`, holding the leaf. -/
abbrev mixedOpt2Ty : TyWf := optionTy stringT mixedLeafTy
/-- Next level: `Process.step String _ _`. -/
abbrev mixedProc2Ty : TyWf := stepTy stringT mixedOpt2Ty
/-- `ProcessOption Nat Nat`, holding the next level. -/
abbrev mixedOpt1Ty : TyWf := optionTy natT mixedProc2Ty
/-- Top level: `Process.step Nat _ _`. -/
abbrev mixedTy : TyWf := stepTy natT mixedOpt1Ty

/-- `mixedProcess`, as a term. -/
def mixedProcess_term : Term sig [] mixedTy :=
  -- Top level: State is Nat
  .record_mk (stepR natT mixedOpt1Ty) (.cons (.nat_mk 0) (.cons (.lam
    -- `ProcessOption.some (n + 1) 42 (…)`
    (.taggedUnion_mk (optionU natT mixedProc2Ty) 1 (fields :=
      .cons (addT (.var (v♯0)) (.nat_mk 1)) (.cons (.nat_mk 42) (.cons
        -- Next level: State is String
        (.record_mk (stepR stringT mixedOpt2Ty) (.cons (.string_mk "hello") (.cons (.lam
          -- `ProcessOption.some (s ++ "!") 99 (…)`
          (.taggedUnion_mk (optionU stringT mixedLeafTy) 1 (fields :=
            .cons (appendT (.var (v♯0)) (.string_mk "!")) (.cons (.nat_mk 99) (.cons
              -- Leaf level: `Process.halt Bool (fun b => if b then 1 else 0)`
              (.lam (.bool_casesOn (.var (v♯0)) (.nat_mk 1) (.nat_mk 0)))
            .nil)))))
        .nil)))
      .nil)))))
  .nil))

/-! #### `varyingProcess` -/

/-- `ProcessOption Nat Unit`: `nextState : Unit` is erased, and only `none` is ever built,
    so `proc` is `nat` (see above). -/
abbrev varyingOptUnitU : LeanTaggedUnionSchema TyWf := .skip (.here ⟨natT, [natT]⟩ [])
/-- The type of `varyingOptUnitU`. -/
abbrev varyingOptUnitTy : TyWf := .taggedUnion varyingOptUnitU
/-- `ProcessOption Nat Bool`, in which only `none` is ever built. -/
abbrev varyingOptBoolTy : TyWf := optionTy boolT natT
/-- The two processes the `if` chooses between, one constructor per layout:
    0. `Process.step Unit () trans`: `seed : Unit` is erased and so is the `Unit` binder of
       `trans`, which leaves the one field `ProcessOption Nat Unit`;
    1. `Process.step Bool true trans`: the fields `bool` and `bool ⇒ ProcessOption Nat Bool`. -/
abbrev varyingProcU : LeanTaggedUnionSchema TyWf :=
  .payloadFirst ⟨varyingOptUnitTy, []⟩ [boolT, boolT ⇒ varyingOptBoolTy] []
/-- The type of `varyingProcU`. -/
abbrev varyingProcTy : TyWf := .taggedUnion varyingProcU
/-- `ProcessOption Nat Nat`, holding one of the two processes. -/
abbrev varyingOptTy : TyWf := optionTy natT varyingProcTy
/-- Top level: `Process.step Nat _ _`. -/
abbrev varyingTy : TyWf := stepTy natT varyingOptTy

/-- `ProcessOption.some 1 7 p`. -/
def varyingSome {Γ : Ctx} (p : Term sig Γ varyingProcTy) : Term sig Γ varyingOptTy :=
  .taggedUnion_mk (optionU natT varyingProcTy) 1 (fields :=
    .cons (.nat_mk 1) (.cons (.nat_mk 7) (.cons p .nil)))

/-- `varyingProcess`, as a term.  `if n = 0 then … else …` is the case analysis on `n`. -/
def varyingProcess_term : Term sig [] varyingTy :=
  .record_mk (stepR natT varyingOptTy) (.cons (.nat_mk 0) (.cons (.lam
    (.nat_casesOn (.var (v♯0))
      -- `ProcessOption.some 1 7 (Process.step Unit () (fun _ => ProcessOption.none))`
      (varyingSome (.taggedUnion_mk varyingProcU 0 (fields :=
        .cons (.taggedUnion_mk varyingOptUnitU 0 (fields := .nil)) .nil)))
      -- `ProcessOption.some 1 7 (Process.step Bool true (fun _ => ProcessOption.none))`
      (varyingSome (.taggedUnion_mk varyingProcU 1 (fields :=
        .cons (.bool_mk true) (.cons (.lam
          (.taggedUnion_mk (optionU boolT natT) 0 (fields := .nil))) .nil))))))
  .nil))

/-! #### What they evaluate to -/

/-- Running a closed term of `sig`. -/
local macro:max "run" t:term:max : term => `(Term.run (Sg := sig) env $t)

/-- `mixedProcess`, with the witnesses `Nat`, `String` and `Bool` filled in. -/
example : run mixedProcess_term =
    (0, fun n => ⟨⟨1, by decide⟩, (n + 1, 42,
      ("hello", fun s => ⟨⟨1, by decide⟩, (s ++ "!", 99,
        (fun b => match b with | true => 1 | false => 0), ())⟩, ()), ())⟩, ()) := rfl

/-- `varyingProcess`, with the witnesses `Nat`, then `Unit` or `Bool`, filled in. -/
example : run varyingProcess_term =
    (0, fun n => match n with
      | 0 => ⟨⟨1, by decide⟩, (1, 7, ⟨⟨0, by decide⟩, (⟨⟨0, by decide⟩, ()⟩, ())⟩, ())⟩
      | _ + 1 => ⟨⟨1, by decide⟩, (1, 7,
          ⟨⟨1, by decide⟩, (true, fun _ => ⟨⟨0, by decide⟩, ()⟩, ())⟩, ())⟩, ()) := rfl

end ProcessModel

-- 2. recursive tagged union with existential in both constructors and different

inductive ProcessHaltIsOut (α : Type) : Type 1 where
  | halt (HaltedState : Type) (getOutOfHalt : HaltedState -> Nat)
  | step (State : Type) (seed : State)
         (emit : State → Option (State × α)) -- no recursion here
         (next : State → ProcessHaltIsOut α) -- no nesting here

/--
error: the type `ProcessHaltIsOut` has no `Ty`: existential typing is not yet supported, `HaltedState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for ProcessHaltIsOut

-- 3. recursive tagged union with existential in both constructors and different

mutual
  /-- A Client hides its `ClientState` and emits a request to a `Server`. -/
  inductive Client (Req Resp : Type) : Type 1 where
    | stop (ServerState : Type) (get : ServerState -> Nat) : Client Req Resp
    | mk   (ClientState : Type)
           (seed        : ClientState)
           (send        : ClientState → Req × Server Req Resp)
           : Client Req Resp

  /-- A Server hides its `ServerState`, processes a request,
      produces a response, and transitions to a `Client`. -/
  inductive Server (Req Resp : Type) : Type 1 where
    | stop (ClientState : Type) (get : ClientState -> Nat) : Server Req Resp
    | mk   (ServerState : Type)
           (seed        : ServerState)
           (receive     : ServerState → Req → Resp × Client Req Resp)
           : Server Req Resp
end

/--
error: the type `Client` has no `Ty`: existential typing is not yet supported, `ServerState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Client, Server

-- but this can
mutual
  /-- The twin of `Client`, at client states `C` and server states `S`. -/
  inductive ClientTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : C) (send : C → Req × ServerTwin C S Req Resp)

  /-- The twin of `Server`, at the same two choices. -/
  inductive ServerTwin (C S Req Resp : Type) : Type where
    | stop
    | mk (seed : S) (receive : S → Req → Resp × ClientTwin C S Req Resp)
end

deriving instance LeanScriptTyWf for ClientTwin, ServerTwin

/-- Hides two types: the state and an intermediate token type. -/
structure StreamPipeline (α : Type) (β : Type) where
  State : Type
  Inter : Type
  seed  : State
  feed  : State → α → State × Option Inter
  emit  : State → Inter → State × Option β

/--
error: the type `StreamPipeline` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for StreamPipeline

/-- Hides three types: the lexer's state, the syntax tree and the evaluator's environment. -/
structure CompilerEngine (α : Type) (β : Type) where
  LexState : Type
  AstType  : Type
  EvalEnv  : Type
  start    : LexState
  lex      : LexState → α → LexState
  parse    : LexState → AstType
  eval     : EvalEnv → AstType → β

-- as with `Unfold`: the refusal is pinned by the `deriving instance` below.

/--
error: the type `CompilerEngine` has no `Ty`: existential typing is not yet supported, `LexState` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for CompilerEngine

structure Keyed where
  State : Type
  Elem  : State → Type
  seed  : State
  get   : (s : State) → Elem s

/--
error: the type `Keyed` has no `Ty`: existential typing is not yet supported, `State` is an existential
-/
#guard_msgs in
deriving instance LeanScriptTyWf for Keyed

structure Layered (α : Type) where
  State : Type
  seed  : State
  subs  : List (Layered α)
  tag   : α
