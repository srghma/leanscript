import TyTests.InductiveTypesTest.NestedRecursion

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
