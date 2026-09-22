import Lean
import LeanScript.Term.Prims
import LeanScript.Term.Elab

/-!
# `#leanjs_compile_term_for`: a Lean `def`, as a `Term`

`LeanScript.Term.Elab` *reports* on what a Lean definition would compile to.  This
module does the compilation: for a declaration `f` it adds

```
f.leanTerm : Term Sig.empty [] [] <the Ty of f>
```

to the environment, and `f.leanTerm` is an ordinary value of `LeanScript.Expr.Term`, so
`LeanScript.Eval.Term.evalClosed` runs it and `decide +kernel` checks the answer against
the one Lean itself computes.

## What becomes what

| Lean | `Term` |
| :-- | :-- |
| a parameter | `Term.var`, at its de Bruijn index |
| `fun x => e` | `Term.lam` |
| `f a`, `f` a parameter | `Term.ap` |
| a closed scalar | `Term.lit` |
| an `@[extern]` constant applied to arguments | `Term.prim`, with the Lean function itself |
| any other constant | looked *through*: its body is compiled in its place |
| `if c then t else e`, `cond`, a `Bool` match | `Term.bool_elim` |
| a `match` on `Nat` | `Term.bool_elim` on `n == 0`, with `n - 1` bound by a `Term.letE` |
| `let x := v; b` | `Term.letE` |
| **a recursive call** | `Term.selfCall` |
| **the recursion itself** | `Term.fixAcc`, descending in `<` on a `Nat` argument |

Both kinds of terminating recursion Lean has — structural and well-founded — become
`Term.fixAcc`, which is what the header of `LeanScript.Expr` says: a structural
recursion is a descent in `<` at the structural measure of the argument recursed on, and
a well-founded one is a descent at the subject of its `termination_by`.  The compiler
recognises the case both kinds are written in here: the measure is a `Nat` **argument**
of the function.  `Term.fixAcc`'s accessibility field is then `LeanScript.accNatLt`,
which is a `def` and therefore reduces, so a generated term can be run by the kernel.

A recursive call whose subject does *not* descend answers with the `nodescend` field —
a fixed value of the result type — rather than looping; a faithful translation never
reaches it, which is exactly what Lean's own termination proof says.

## What is refused

The compiler answers with an error, and adds nothing to the environment, for a
declaration it cannot hold: one that is `partial`, `unsafe` or a partial fixpoint (a
`while` loop in a `do` block), one whose type mentions a shape the type translation has
no `Ty` for, one that recurses at something other than a `Nat` argument, and one that is
part of a `mutual` block.  That is a *refusal*, not a silent approximation: nothing that
is added to the environment is an approximation of anything.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace LeanScript.Term

open LeanScript LeanScript.Expr

/-! ## Rendering a `Ty` as syntax -/

/-- The name of the constructor of `LeanPrimTy` a terminal type is, for the types the
    compiler writes out. -/
def primTyIdent : LeanPrimTy → Option Name
  | .nat => some ``LeanPrimTy.nat
  | .int => some ``LeanPrimTy.int
  | .bool => some ``LeanPrimTy.bool
  | .char => some ``LeanPrimTy.char
  | .string => some ``LeanPrimTy.string
  | .uint8 => some ``LeanPrimTy.uint8
  | .uint16 => some ``LeanPrimTy.uint16
  | .uint32 => some ``LeanPrimTy.uint32
  | .uint64 => some ``LeanPrimTy.uint64
  | .int8 => some ``LeanPrimTy.int8
  | .int16 => some ``LeanPrimTy.int16
  | .int32 => some ``LeanPrimTy.int32
  | .int64 => some ``LeanPrimTy.int64
  | .float => some ``LeanPrimTy.float
  | .float32 => some ``LeanPrimTy.float32
  | .stringPosRaw => some ``LeanPrimTy.stringPosRaw
  | .substringRaw => some ``LeanPrimTy.substringRaw
  | .stringSlice => some ``LeanPrimTy.stringSlice
  | _ => none

/-- An `Int`, as the syntax that builds it. -/
def intSyntax : Int → MetaM (TSyntax `term)
  | .ofNat n => `((Int.ofNat $(quote n)))
  | .negSucc n => `((Int.negSucc $(quote n)))

mutual

/-- A payload type of a recursive declaration, as the syntax that builds it.  This is
    `tySyntax` one layer down: the same shapes, in `RTy`, and in addition `RTy.self`, an
    occurrence of the declaration the payload belongs to. -/
partial def rtySyntax : RTy → MetaM (TSyntax `term)
  | .self => do `(RTy.self)
  | .familyMember i => do `(RTy.familyMember $(quote i))
  | .prim p => do
      let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
      `(RTy.prim $(mkIdent n))
  | .fn a b => do `(RTy.fn $(← rtySyntax a) $(← rtySyntax b))
  | .primCovariant (.array a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.array $(← rtySyntax a)))
  | .primCovariant (.thunk a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.thunk $(← rtySyntax a)))
  | .primCovariant (.lazy a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.lazy $(← rtySyntax a)))
  | .enum s => do
      `(RTy.enum (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift)))
  | .record fs => do `(RTy.record $(← rtyRecordSchemaSyntax fs))
  | .taggedUnion l => do `(RTy.taggedUnion $(← rtyTuSchemaSyntax l))
  | _ => throwError "no syntax for a payload that is itself a recursive declaration"

/-- A list of payload types, as syntax. -/
partial def rtyListSyntax (τs : List RTy) : MetaM (TSyntax `term) := do
  let elems ← τs.toArray.mapM rtySyntax
  `([$(elems),*])

/-- The fields of each constructor of a union of payload types, as syntax. -/
partial def rtyListListSyntax (τss : List (List RTy)) : MetaM (TSyntax `term) := do
  let elems ← τss.toArray.mapM rtyListSyntax
  `([$(elems),*])

/-- The schema of a record of payload types, as syntax. -/
partial def rtyRecordSchemaSyntax (fs : LeanRecordSchema RTy) : MetaM (TSyntax `term) := do
  `(LeanRecordSchema.mk $(← rtySyntax fs.fst) $(← rtySyntax fs.snd)
      $(← rtyListSyntax fs.rest))

/-- A non-empty list of payload types, as syntax. -/
partial def rtyNeListSyntax (fs : NonEmpty.ListCorrectByConstruction.NonEmptyList RTy) :
    MetaM (TSyntax `term) := do
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
      $(← rtySyntax fs.head) $(← rtyListSyntax fs.tail))

/-- The constructors of a union of payload types from the first one that carries a
    field, as syntax. -/
partial def rtyCtorsWithPayloadSyntax : CtorsWithPayload RTy → MetaM (TSyntax `term)
  | .here fs rest => do
      `(CtorsWithPayload.here $(← rtyNeListSyntax fs) $(← rtyListListSyntax rest))
  | .skip r => do `(CtorsWithPayload.skip $(← rtyCtorsWithPayloadSyntax r))

/-- The schema of a tagged union of payload types, as syntax. -/
partial def rtyTuSchemaSyntax : LeanTaggedUnionSchema RTy → MetaM (TSyntax `term)
  | .payloadFirst fs next rest => do
      `(LeanTaggedUnionSchema.payloadFirst $(← rtyNeListSyntax fs) $(← rtyListSyntax next)
          $(← rtyListListSyntax rest))
  | .skip r => do `(LeanTaggedUnionSchema.skip $(← rtyCtorsWithPayloadSyntax r))

end

mutual

/-- A `Ty`, as the syntax that builds it — and, with it, the syntax of each of the
    schemas a datatype of the language is described by. -/
partial def tySyntax : Ty → MetaM (TSyntax `term)
  | .prim p => do
      let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
      `(Ty.prim $(mkIdent n))
  | .fn a b => do `(Ty.fn $(← tySyntax a) $(← tySyntax b))
  | .primCovariant (.array a) => do `(Ty.array $(← tySyntax a))
  | .primCovariant (.thunk a) => do `(Ty.thunk $(← tySyntax a))
  | .primCovariant (.lazy a) => do `(Ty.lazy $(← tySyntax a))
  | .enum s => do
      `(Ty.enum (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift)))
  | .record fs => do `(Ty.record $(← recordSchemaSyntax fs))
  | .taggedUnion l => do `(Ty.taggedUnion $(← tuSchemaSyntax l))
  | .recTaggedUnion l => do `(Ty.recTaggedUnion ⟨$(← rtyTuSchemaSyntax l.schema), by decide⟩)
  | .withComputedFields b cs => do
      `(Ty.withComputedFields $(← tySyntax b) $(← primTyNeListSyntax cs))
  | τ => throwError "no syntax for the type `{tyStr τ}`"

/-- The types of the values a declaration caches, as syntax. -/
partial def primTyNeListSyntax
    (cs : NonEmpty.ListCorrectByConstruction.NonEmptyList LeanPrimTy) :
    MetaM (TSyntax `term) := do
  let one (p : LeanPrimTy) : MetaM (TSyntax `term) := do
    let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
    `($(mkIdent n))
  let tail ← cs.tail.toArray.mapM one
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk $(← one cs.head) [$(tail),*])

/-- A list of `Ty`s, as syntax. -/
partial def tyListSyntax (τs : List Ty) : MetaM (TSyntax `term) := do
  let elems ← τs.toArray.mapM tySyntax
  `([$(elems),*])

/-- A list of lists of `Ty`s — the fields of each constructor of a union — as syntax. -/
partial def tyListListSyntax (τss : List (List Ty)) : MetaM (TSyntax `term) := do
  let elems ← τss.toArray.mapM tyListSyntax
  `([$(elems),*])

/-- The schema of a record, as syntax. -/
partial def recordSchemaSyntax (fs : LeanRecordSchema Ty) : MetaM (TSyntax `term) := do
  `(LeanRecordSchema.mk $(← tySyntax fs.fst) $(← tySyntax fs.snd) $(← tyListSyntax fs.rest))

/-- A non-empty list of `Ty`s — the fields of a constructor that has one — as syntax. -/
partial def neListSyntax (fs : NonEmpty.ListCorrectByConstruction.NonEmptyList Ty) :
    MetaM (TSyntax `term) := do
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
      $(← tySyntax fs.head) $(← tyListSyntax fs.tail))

/-- The constructors of a union from the first one that carries a field, as syntax. -/
partial def ctorsWithPayloadSyntax : CtorsWithPayload Ty → MetaM (TSyntax `term)
  | .here fs rest => do
      `(CtorsWithPayload.here $(← neListSyntax fs) $(← tyListListSyntax rest))
  | .skip r => do `(CtorsWithPayload.skip $(← ctorsWithPayloadSyntax r))

/-- The schema of a tagged union, as syntax. -/
partial def tuSchemaSyntax : LeanTaggedUnionSchema Ty → MetaM (TSyntax `term)
  | .payloadFirst fs next rest => do
      `(LeanTaggedUnionSchema.payloadFirst $(← neListSyntax fs) $(← tyListSyntax next)
          $(← tyListListSyntax rest))
  | .skip r => do `(LeanTaggedUnionSchema.skip $(← ctorsWithPayloadSyntax r))

end

/-- A value of a terminal type to answer with where the translation needs one it will
    never read: the `nodescend` field of a recursion. -/
def primDefault : LeanPrimTy → Option (TSyntax `term) → Option (TSyntax `term) := fun _ x => x

/-! ## The compiler -/

/-- A recursion in scope: which declaration it is, how many value arguments that
    declaration takes, and where the call goes.

    A member of a `mutual` block is **not** a recursion of its own: the whole block is
    one recursion, whose arguments are a **tag** saying which member is meant followed
    by a slot for every value argument of every member, and whose answer is the answer
    of the members — which is why a block whose members do not all answer with the same
    type is refused.  `slot` is what a member of such a block carries: its tag, where
    its own arguments start among the slots, and the whole merged argument list, so
    that a call of it can fill the slots of the other members with values nothing
    reads. -/
structure SelfRef where
  /-- The declaration called. -/
  name : Name
  /-- How many value arguments it takes. -/
  arity : Nat
  /-- The de Bruijn index of the recursion in `Ρ`. -/
  rvar : Nat
  /-- For a member of a `mutual` block: its tag, the offset of its slots, and the
      merged argument list of the block. -/
  slot : Option (Nat × Nat × List Ty) := none

/-- What the compiler knows while it walks a body. -/
structure CompCtx where
  /-- The variables in scope, innermost first, with the `Ty` each is bound at. -/
  vars : List (FVarId × Ty) := []
  /-- The recursions in scope. -/
  selves : List SelfRef := []
  /-- How far the compiler may look through definitions. -/
  fuel : Nat := 64

/-- What the compiler has produced so far: the Lean functions a `Term.prim` node and a
    `Term.lit` node hold are not syntax of the object language but values of Lean, and
    each of them is bound to an auxiliary definition of its own so that the generated
    term is a closed, readable expression. -/
structure CompState where
  /-- The declaration being compiled, which the auxiliary definitions are named after. -/
  root : Name
  /-- How many auxiliary definitions have been made. -/
  next : Nat := 0

/-- The compiler's monad. -/
abbrev CompM := ReaderT CompCtx (StateRefT CompState TermElabM)

/-- Bind a Lean value to an auxiliary definition of its own, and answer with its name.
    A generated term mentions the Lean functions it applies by name rather than holding
    them inline, so that it elaborates outside the compiler's own context. -/
def mkAuxValue (e : Expr) : CompM (TSyntax `term) := do
  let mut st ← get
  let mut name := Name.str st.root s!"aux{st.next}"
  -- a declaration that was compiled before has its auxiliary definitions already: take
  -- the next free name rather than clashing with them
  while (← getEnv).contains name do
    st := { st with next := st.next + 1 }
    name := Name.str st.root s!"aux{st.next}"
  set { st with next := st.next + 1 }
  let type ← inferType e
  let type ← instantiateMVars type
  let e ← instantiateMVars e
  addDecl (Declaration.defnDecl
    { name := name, levelParams := [], type := type, value := e,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })
  return mkIdent name

/-- The de Bruijn index of a variable, if it is one the compiler bound. -/
def lookupVar (fv : FVarId) : CompM (Option Nat) := do
  let vars := (← read).vars
  return vars.findIdx? (fun (g, _) => g == fv)

/-- Is this a type the translation erases — a proposition, a type, an instance or a
    one-value type? -/
def erasedBinder (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if (← whnf t).isSort then return true
  if ← isErasedType t then return true
  if (← isClass? t).isSome then return true
  return false

/-- The `Ty` of a Lean type, or an error naming why it has none. -/
def tyOf (t : Expr) : MetaM Ty := do
  match ← toTy t with
  | .ok τ => return τ
  | .erased => throwError "the type `{t}` carries no value"
  | .no r => throwError "the type `{t}` has no `Ty`: {r}"

/-- The constants the compiler applies as primitives even though they are not marked
    `@[extern]`: the ones whose Lean definition is a `Decidable` instance or a piece of
    core arithmetic that it is pointless to look through. -/
def primWhitelist : Std.HashSet Name :=
  Std.HashSet.ofList
    [``Nat.beq, ``Nat.ble, ``Nat.blt, ``Nat.decEq, ``Nat.decLt, ``Nat.decLe,
     ``Nat.succ, ``Nat.pred, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod,
     ``Nat.pow, ``Nat.min, ``Nat.max, ``Nat.land, ``Nat.lor, ``Nat.xor,
     ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.log2, ``Nat.gcd, ``Nat.toUInt8,
     ``Int.add, ``Int.sub, ``Int.mul, ``Int.ediv, ``Int.emod, ``Int.neg, ``Int.natAbs,
     ``Int.decEq, ``Int.decLt, ``Int.decLe, ``Int.toNat, ``Int.ofNat,
     ``Bool.not, ``Bool.and, ``Bool.or, ``Bool.xor, ``Bool.decEq,
     ``String.length, ``String.append, ``String.push, ``String.decEq,
     ``Array.append,
     ``Char.ofNat, ``Char.toNat, ``Char.val,
     ``decide]

/-- Is this constant one the compiler applies rather than looks through? -/
def isPrimConst (c : Name) : MetaM Bool := do
  let env ← getEnv
  if Lean.isExtern env c then return true
  if primWhitelist.contains c then return true
  match env.find? c with
  | some (.defnInfo _) => return false
  | some (.opaqueInfo _) => return true
  | _ => return false

/-- The members of the `mutual` block a declaration belongs to, in declaration order,
    or `none` if it is not part of one. -/
def mutualMembers (c : Name) : CoreM (Option (Array Name)) := do
  let env ← getEnv
  if let some info := Elab.Structural.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then return some info.declNames
  if let some info := Elab.WF.eqnInfoExt.find? env c then
    if info.declNames.size > 1 then return some info.declNames
  return none

/-- Is this declaration one of the recursive ones — so that its body has to be compiled
    into a `Term.fixAcc` rather than looked through? -/
def isRecursiveDecl (c : Name) : CoreM Bool := do
  match ← recursionKindOf c with
  | .structural _ | .wellFounded _ => return true
  | _ => return false

/-- The body a declaration is compiled from: for a recursive one, the right-hand side of
    its `eq_def` — which is written with the declaration itself in place of the
    recursion Lean elaborated it into — and for any other one, its value. -/
def bodyOf (c : Name) : MetaM Expr := do
  if ← isRecursiveDecl c then
    let some eqn ← getUnfoldEqnFor? c
      | throwError "`{c}` is recursive but has no `eq_def`"
    let some (.thmInfo ti) := (← getEnv).find? eqn
      | throwError "`{c}`'s `eq_def` is not a theorem"
    forallTelescope ti.type fun xs body => do
      let some (_, _, rhs) := body.eq?
        | throwError "`{c}`'s `eq_def` is not an equation"
      mkLambdaFVars xs rhs
  else
    let some (.defnInfo di) := (← getEnv).find? c
      | throwError "`{c}` is not a definition"
    return di.value

/-- The parameters of a declaration that carry a value, with their `Ty`s, and the `Ty`
    of what it answers with once they are all given. -/
def paramTys (c : Name) : MetaM (List Ty × Ty) := do
  let some ci := (← getEnv).find? c | throwError "unknown declaration `{c}`"
  forallTelescopeReducing ci.type fun xs body => do
    let mut ps : List Ty := []
    for x in xs do
      let t ← inferType x
      unless ← erasedBinder t do ps := ps ++ [← tyOf t]
    return (ps, ← tyOf body)

/-- The Lean types of the parameters of a declaration that carry a value. -/
def valueParamTypes (c : Name) : MetaM (Array Expr) := do
  let some ci := (← getEnv).find? c | throwError "unknown declaration `{c}`"
  forallTelescopeReducing ci.type fun xs _ => do
    let mut tys : Array Expr := #[]
    for x in xs do
      let t ← inferType x
      unless ← erasedBinder t do tys := tys.push t
    return tys

/-- Which value parameter a structural recursion descends on, if Lean recorded one and
    it is a `Nat`.  `recArgPos` counts *all* the parameters, the erased ones included, so
    it is translated into the numbering the object language uses. -/
def structuralNatArg? (c : Name) : MetaM (Option Nat) := do
  let some info := Elab.Structural.eqnInfoExt.find? (← getEnv) c | return none
  let some ci := (← getEnv).find? c | return none
  forallTelescopeReducing ci.type fun xs _ => do
    if h : info.recArgPos < xs.size then
      let recArg := xs[info.recArgPos]
      let mut idx := 0
      for x in xs do
        let t ← inferType x
        if ← erasedBinder t then continue
        if x == recArg then
          unless (← whnf t).isConstOf ``Nat do return none
          return some idx
        idx := idx + 1
      return none
    else return none

/-! ### Case splits on `Nat` and on `Bool` -/

/-- A recogniser for an eliminator of `Nat` or of `Bool`: the major premise, the branch
    for `0` / `false` and the branch for `n+1` / `true`, with the arguments the
    eliminator is applied to beyond the ones it needs appended to each branch. -/
structure ElimApp where
  /-- `true` for `Nat`, `false` for `Bool`. -/
  isNat : Bool
  /-- The value eliminated. -/
  major : Expr
  /-- The branch for `0` (`Nat`) or `false` (`Bool`). -/
  zero : Expr
  /-- The branch for `n+1` (a function of the predecessor) or `true`. -/
  succ : Expr
  /-- Arguments applied to the result of the elimination. -/
  extra : Array Expr

/-- Read an application of `Nat.rec`, `Nat.casesOn`, `Bool.rec` or `Bool.casesOn`. -/
def elimApp? (c : Name) (args : Array Expr) : Option ElimApp :=
  let mk (isNat : Bool) (major zero succ : Expr) (extra : Array Expr) :=
    some { isNat, major, zero, succ, extra }
  match c with
  | ``Nat.rec => if args.size ≥ 4 then
      mk true args[3]! args[1]! args[2]! (args.extract 4 args.size) else none
  | ``Nat.casesOn | ``Nat.recAux => if args.size ≥ 4 then
      (if c == ``Nat.recAux then
        mk true args[3]! args[1]! args[2]! (args.extract 4 args.size)
      else mk true args[1]! args[2]! args[3]! (args.extract 4 args.size)) else none
  | ``Bool.rec => if args.size ≥ 4 then
      mk false args[3]! args[1]! args[2]! (args.extract 4 args.size) else none
  | ``Bool.casesOn => if args.size ≥ 4 then
      mk false args[1]! args[2]! args[3]! (args.extract 4 args.size) else none
  | _ => none

/-- The arguments of a recursion, packed into the `PSigma` Lean's well-founded
    elaboration hands its measure. -/
def packPSigma : List Expr → MetaM (Option Expr)
  | [] => return none
  | [a] => return some a
  | a :: rest => do
      let some r ← packPSigma rest | return none
      -- the motive has to be given: inferring it from the two components would leave
      -- it a metavariable
      let α ← inferType a
      let β ← mkLambdaFVars #[a] (← inferType r)
      return some (← mkAppOptM ``PSigma.mk #[some α, some β, some a, some r])

/-- **The measure Lean's own termination proof descends at**, as a function of the value
    parameters of the declaration.

    A well-founded definition `f` is elaborated into a `f._unary` whose body applies
    `WellFounded.fix` at `InvImage r m`, where `m` is the measure — the transcription of
    the `termination_by` clause, or the one `GuessLex` found.  Reading it back out is
    what makes a compiled recursion *descend*: a measure the compiler guessed at instead
    would be a term that answers with its `nodescend` field rather than with what the
    Lean function answers with. -/
def wfMeasure? (c : Name) : MetaM (Option Expr) := do
  let env ← getEnv
  let some info := Elab.WF.eqnInfoExt.find? env c | return none
  let some uci := env.find? info.declNameNonRec | return none
  let some val := uci.value? | return none
  let some fci := env.find? c | return none
  -- the measure, abstracted over the parameters the recursion holds fixed
  let some (mAbs, k) ← lambdaTelescope val fun fixed body => do
      let some invImg := body.find? (fun e => e.isAppOfArity ``InvImage 4) | return none
      return some (← mkLambdaFVars fixed invImg.getAppArgs[3]!, fixed.size)
    | return none
  forallTelescopeReducing fci.type fun xs _ => do
    if xs.size < k then return none
    let some packed ← packPSigma (xs.extract k xs.size).toList | return none
    let body := mkApp (mkAppN mAbs (xs.extract 0 k)) packed
    unless ← isTypeCorrect body do return none
    -- the measure is a function of *every* parameter, and what the object language
    -- needs is a function of the ones that carry a value: a parameter it erases — a
    -- proof — is one the measure reads only until the case analysis it sits under is
    -- reduced away, and a measure that still reads one after that is not one this
    -- reads
    let mut valXs : Array Expr := #[]
    for x in xs do
      unless ← erasedBinder (← inferType x) do valXs := valXs.push x
    let f ← instantiateMVars (← mkLambdaFVars valXs body)
    unless f.hasFVar do return some f
    let body ← Meta.reduce body (skipTypes := true) (skipProofs := true)
    let f ← instantiateMVars (← mkLambdaFVars valXs body)
    if f.hasFVar then return none
    return some f

/-- The injection of a member of a `mutual` block into the sum Lean's own termination
    proof speaks about: member `j` of `n` is `PSum.inr` taken `j` times, and `PSum.inl`
    after that unless it is the last one. -/
partial def injectPSum (dom : Expr) (j n : Nat) (packed : Expr) : MetaM (Option Expr) := do
  if n ≤ 1 then return some packed
  let dom ← whnf dom
  unless dom.isAppOfArity ``PSum 2 do return none
  let a := dom.getAppArgs[0]!
  let b := dom.getAppArgs[1]!
  if j == 0 then
    return some (← mkAppOptM ``PSum.inl #[some a, some b, some packed])
  else
    let some inner ← injectPSum b (j - 1) (n - 1) packed | return none
    return some (← mkAppOptM ``PSum.inr #[some a, some b, some inner])

/-- **The measure of each member of a well-founded `mutual` block.**

    Lean elaborates the block into one function of the sum of the members' arguments,
    and its termination proof descends at one measure of that sum.  Reading it back out
    and composing it with the injection of each member is what gives the measure of that
    member, as a Lean function of the arguments that carry a value — exactly what the
    merged recursion needs, and not a guess. -/
def wfMutualMeasures (members : Array Name) : MetaM (Option (Array Expr)) := do
  let env ← getEnv
  let some info := Elab.WF.eqnInfoExt.find? env members[0]! | return none
  let some uci := env.find? info.declNameNonRec | return none
  let some val := uci.value? | return none
  let some (mAbs, k) ← lambdaTelescope val fun fixed body => do
      let some invImg := body.find? (fun e => e.isAppOfArity ``InvImage 4) | return none
      return some (← mkLambdaFVars fixed invImg.getAppArgs[3]!, fixed.size)
    | return none
  -- a block whose recursion holds a prefix of its arguments fixed is not one this reads
  unless k == 0 do return none
  let .forallE _ dom _ _ ← whnf (← inferType mAbs) | return none
  let mut out : Array Expr := #[]
  for j in [0:members.size] do
    let some ci := env.find? members[j]! | return none
    let r ← forallTelescopeReducing ci.type fun xs _ => do
      let some packed ← packPSigma xs.toList | return none
      let some injected ← injectPSum dom j members.size packed | return none
      let body := mkApp mAbs injected
      unless ← isTypeCorrect body do return none
      let mut valXs : Array Expr := #[]
      for x in xs do
        unless ← erasedBinder (← inferType x) do valXs := valXs.push x
      let f ← instantiateMVars (← mkLambdaFVars valXs body)
      unless f.hasFVar do return some f
      -- the measure of a member with an erased parameter — a proof — mentions that
      -- parameter only until the case analysis of the sum is reduced away
      let body ← Meta.reduce body (skipTypes := true) (skipProofs := true)
      let f ← instantiateMVars (← mkLambdaFVars valXs body)
      if f.hasFVar then return none
      return some f
    let some f := r | return none
    out := out.push f
  return some out

/-! ### Datatypes: a constructor, and the eliminator of a datatype -/

/-- The inductive type an eliminator belongs to, if the constant is one: `I.rec`,
    `I.recAux` or `I.casesOn`. -/
def elimInductive? (c : Name) : MetaM (Option Name) := do
  let .str pre s := c | return none
  unless s == "rec" || s == "recAux" || s == "casesOn" do return none
  match (← getEnv).find? pre with
  | some (.inductInfo _) => return some pre
  | _ => return none

/-- The `Ty` a field of a constructor of a recursive declaration has, with the
    declaration itself — `self` — put in place of an occurrence of it.  Only the two
    field shapes `Expr.RecFlds` covers are answered for: a terminal field and an
    occurrence of the declaration.  A declaration with any other field is refused. -/
def recFieldTy (self : Ty) : RTy → Option Ty
  | .self => some self
  | .prim p => some (.prim p)
  | _ => none

/-- The fields of each constructor of a datatype, as the `Ty` of the datatype records
    them: one entry per constructor, in declaration order. -/
def ctorFieldTys (τ : Ty) : Option (List (List Ty)) :=
  match τ with
  | .record fs => some [fs.toList]
  | .taggedUnion l => some l.toList
  | .enum s => some (List.replicate s.nOfConstructors [])
  | .prim .bool => some [[], []]
  | .recTaggedUnion l => l.schema.toList.mapM (fun fs => fs.mapM (recFieldTy (.recTaggedUnion l)))
  | _ => none

/-- The evidence `Expr.RecFlds` asks for, for one constructor of a recursive tagged
    union: which of its fields are terminal and which are an occurrence of the
    declaration, read off the `Ty` of each field — `self` being the declaration's own
    type.  Any other field shape is refused, exactly as `Expr.RecFlds` refuses it. -/
partial def recFldsSyntax : List Ty → MetaM (TSyntax `term)
  | [] => `(RecFlds.nil)
  | τ :: rest => do
      let restS ← recFldsSyntax rest
      match τ with
      | .prim _ => `(RecFlds.prim $restS)
      | .recTaggedUnion _ => `(RecFlds.self $restS)
      | _ =>
        throwError "a constructor of a recursive declaration with a field of type `{tyStr τ}`, which the object language has no description of"

/-- The branches of a dispatch on a recursive tagged union: one per constructor, each
    with the description of the fields it binds. -/
partial def recCasesSyntax : List (List Ty × TSyntax `term) → MetaM (TSyntax `term)
  | [] => `(RecCases.nil)
  | (fts, b) :: rest => do
      `(RecCases.cons $(← recFldsSyntax fts) $b $(← recCasesSyntax rest))

/-- How many of the fields of a constructor carry a value. -/
def valueFieldCount (ci : ConstructorVal) : MetaM Nat := do
  forallBoundedTelescope ci.type (some (ci.numParams + ci.numFields)) fun xs _ => do
    let fields := xs.extract ci.numParams xs.size
    let mut n := 0
    for x in fields do
      unless ← erasedBinder (← inferType x) do n := n + 1
    return n

/-- How many value fields a constructor has before its `i`-th field — the index the
    object language reads that field at, the erased ones having dropped out. -/
def valueFieldIndex (ci : ConstructorVal) (i : Nat) : MetaM (Option Nat) := do
  forallBoundedTelescope ci.type (some (ci.numParams + ci.numFields)) fun xs _ => do
    let fields := xs.extract ci.numParams xs.size
    let mut idx := 0
    for h : k in [0:fields.size] do
      let erased ← erasedBinder (← inferType fields[k])
      if k == i then return (if erased then none else some idx)
      unless erased do idx := idx + 1
    return none

/-- `Ty.den τ`, as a Lean type. -/
def denTypeOf (τ : Ty) : TermElabM Expr := do
  let τS ← tySyntax τ
  let τE ← Lean.Elab.Term.elabTerm τS (some (Lean.mkConst ``LeanScript.Ty))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  mkAppM ``LeanScript.Ty.den #[← instantiateMVars τE]

/-- Is the Lean function a primitive was built from one of exactly the type the node
    needs — a non-dependent function of the `Ty`s of its arguments, answering with the
    `Ty` of the node?  A Lean function whose parameters are *dependent* — a position in
    a string, whose type names the string — is not, and is compiled by
    `trPrimFallback` as one primitive of the variables it reads instead. -/
def primFnMatches (fnExpr : Expr) (valTys : Array Ty) (resTy : Ty) : TermElabM Bool := do
  let ty ← inferType fnExpr
  forallBoundedTelescope ty (some valTys.size) fun xs body => do
    if xs.size != valTys.size then return false
    let mut seen : Array FVarId := #[]
    for h : i in [0:valTys.size] do
      let d ← inferType xs[i]!
      if d.hasAnyFVar (fun f => seen.contains f) then return false
      unless ← isDefEq d (← denTypeOf valTys[i]) do return false
      seen := seen.push xs[i]!.fvarId!
    if body.hasAnyFVar (fun f => seen.contains f) then return false
    isDefEq body (← denTypeOf resTy)

/-! ### Bridging a Lean type and the denotation of its `Ty`

The `Ty` of a Lean type does not always denote *that* Lean type: a structure of one
field is erased to its field, and a structure of several is a tuple rather than the
structure.  A primitive is a Lean function written at the Lean types, and the node that
holds it takes a function of the denotations, so the two are bridged — in **both**
directions, since an argument travels one way and the answer the other. -/

/-- The fields of a constructor that carry a value, by their position among *all* of its
    fields, with the Lean type of each — at the parameters `params` the datatype is
    taken at, so that the types answered with mention nothing the caller cannot see.  A
    field whose type names an earlier field is refused: it has no bridge. -/
def valueFields (ci : ConstructorVal) (params : Array Expr) :
    MetaM (Array (Nat × Expr)) := do
  let ty ← instantiateForall ci.type (params.extract 0 ci.numParams)
  forallBoundedTelescope ty (some ci.numFields) fun xs _ => do
    let mut out : Array (Nat × Expr) := #[]
    let mut seen : Array FVarId := #[]
    for h : i in [0:xs.size] do
      let t ← inferType xs[i]
      if t.hasAnyFVar (fun f => seen.contains f) then
        throwError "`{ci.induct}` has a field whose type names an earlier field"
      seen := seen.push xs[i].fvarId!
      unless ← erasedBinder t do out := out.push (i, t)
    return out

/-- Is the Lean type `a` a `List` of a **terminal** type, whose `Ty` is `τ`?  The answer
    is the name of the constructor of `LeanPrimTy` the element type is, which is what
    `Ty.listOfList` and `Ty.listToList` — the two directions of the correspondence
    between a Lean list and a value of `Ty.list` — are taken at. -/
def listPrimElem? (τ : Ty) (a : Expr) : MetaM (Option Name) := do
  let aw ← whnf a
  unless aw.isAppOfArity ``List 1 do return none
  let some (.prim p) ← (do
      match ← toTy aw.getAppArgs[0]! with
      | .ok e => pure (some e)
      | _ => pure none) | return none
  unless Ty.beq τ (Ty.list (.prim p)) do return none
  return primTyIdent p

mutual

/-- A Lean function `Ty.den τ → A`. -/
partial def bridgeUp (τ : Ty) (a : Expr) : CompM Expr := do
  let den ← denTypeOf τ
  if ← isDefEq den a then
    return ← withLocalDeclD `x a fun x => mkLambdaFVars #[x] x
  match τ with
  | .fn d r =>
      -- a newtype whose field is a function is erased to the function, so a `Ty` that
      -- is an arrow answers a Lean type that is not one: the datatype builds it.
      match ← whnf a with
      | .forallE _ dom cod _ =>
        if cod.hasLooseBVars then throwError "a dependent function type has no bridge"
        let down ← bridgeDown d dom
        let up ← bridgeUp r cod
        withLocalDeclD `f den fun f =>
          withLocalDeclD `x dom fun x =>
            mkLambdaFVars #[f, x]
              (mkApp up (mkApp f (mkApp down x).headBeta)).headBeta
      | _ => bridgeUpData τ den a
  | .array d =>
      let elem ← whnf a
      if elem.isAppOfArity ``Array 1 then
        let up ← bridgeUp d elem.getAppArgs[0]!
        withLocalDeclD `v den fun v => do mkLambdaFVars #[v] (← mkAppM ``Array.map #[up, v])
      else bridgeUpData τ den a
  | .recTaggedUnion _ =>
      match ← listPrimElem? τ a with
      | some pn => return mkAppN (Lean.mkConst ``LeanScript.Ty.listToList) #[Lean.mkConst pn]
      | none => bridgeUpData τ den a
  | _ => bridgeUpData τ den a

/-- A Lean function `A → Ty.den τ`. -/
partial def bridgeDown (τ : Ty) (a : Expr) : CompM Expr := do
  let den ← denTypeOf τ
  if ← isDefEq den a then
    return ← withLocalDeclD `x a fun x => mkLambdaFVars #[x] x
  match τ with
  | .fn d r =>
      match ← whnf a with
      | .forallE _ dom cod _ =>
        if cod.hasLooseBVars then throwError "a dependent function type has no bridge"
        let up ← bridgeUp d dom
        let down ← bridgeDown r cod
        let denD ← denTypeOf d
        withLocalDeclD `g a fun g =>
          withLocalDeclD `y denD fun y =>
            mkLambdaFVars #[g, y]
              (mkApp down (mkApp g (mkApp up y).headBeta)).headBeta
      | _ => bridgeDownData τ den a
  | .array d =>
      let elem ← whnf a
      if elem.isAppOfArity ``Array 1 then
        let down ← bridgeDown d elem.getAppArgs[0]!
        withLocalDeclD `v a fun v => do mkLambdaFVars #[v] (← mkAppM ``Array.map #[down, v])
      else bridgeDownData τ den a
  | .recTaggedUnion _ =>
      match ← listPrimElem? τ a with
      | some pn => return mkAppN (Lean.mkConst ``LeanScript.Ty.listOfList) #[Lean.mkConst pn]
      | none => bridgeDownData τ den a
  | _ => bridgeDownData τ den a

/-- `Ty.den τ → A`, where `A` is a datatype the language holds as a newtype or a
    record: the fields are read out of the tuple and handed to the constructor. -/
partial def bridgeUpData (τ : Ty) (den a : Expr) : CompM Expr := do
  let aw ← whnf a
  let .const n us := aw.getAppFn
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let some (.inductInfo ind) := (← getEnv).find? n
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let [ctorName] := ind.ctors
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let ci ← getConstInfoCtor ctorName
  unless ci.numFields == (← valueFields ci aw.getAppArgs).size do
    throwError "`{n}` has a field the object language erases, so nothing builds one from its denotation"
  let flds ← valueFields ci aw.getAppArgs
  let ctor := mkAppN (Lean.mkConst ctorName us) (aw.getAppArgs.extract 0 ci.numParams)
  withLocalDeclD `y den fun y => do
    match τ, flds.size with
    | _, 1 =>
        let up ← bridgeUp τ flds[0]!.2
        mkLambdaFVars #[y] (mkApp ctor (mkApp up y).headBeta)
    | .record fs, _ =>
        let ftys := fs.toList.toArray
        unless ftys.size == flds.size do
          throwError "`{n}` has {flds.size} fields, and its record has {ftys.size}"
        let mut rest := y
        let mut args : Array Expr := #[]
        for (fty, _, lty) in (ftys.zip flds).map (fun (a, b) => (a, b.1, b.2)) do
          let up ← bridgeUp fty lty
          args := args.push (mkApp up (← mkAppM ``Prod.fst #[rest])).headBeta
          rest ← mkAppM ``Prod.snd #[rest]
        mkLambdaFVars #[y] (mkAppN ctor args)
    | _, _ => throwError "no bridge between `{a}` and the denotation of its `Ty`"

/-- `A → Ty.den τ`, where `A` is a datatype the language holds as a newtype or a
    record: the fields are read out of the value and put in a tuple. -/
partial def bridgeDownData (τ : Ty) (_den a : Expr) : CompM Expr := do
  let aw ← whnf a
  let .const n _ := aw.getAppFn
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let some (.inductInfo ind) := (← getEnv).find? n
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let [ctorName] := ind.ctors
    | throwError "no bridge between `{a}` and the denotation of its `Ty`"
  let ci ← getConstInfoCtor ctorName
  let flds ← valueFields ci aw.getAppArgs
  withLocalDeclD `x a fun x => do
    match τ, flds.size with
    | _, 1 =>
        let down ← bridgeDown τ flds[0]!.2
        mkLambdaFVars #[x] (mkApp down (Expr.proj n flds[0]!.1 x)).headBeta
    | .record fs, _ =>
        let ftys := fs.toList.toArray
        unless ftys.size == flds.size do
          throwError "`{n}` has {flds.size} fields, and its record has {ftys.size}"
        let mut out := Lean.mkConst ``PUnit.unit [Level.one]
        for (fty, raw, lty) in (ftys.zip flds).reverse.map (fun (a, b) => (a, b.1, b.2)) do
          let down ← bridgeDown fty lty
          out ← mkAppM ``Prod.mk #[(mkApp down (Expr.proj n raw x)).headBeta, out]
        mkLambdaFVars #[x] out
    | _, _ => throwError "no bridge between `{a}` and the denotation of its `Ty`"

end

/-- A Lean function of Lean types, as the function of the same arity between the
    denotations of the `Ty`s the node holds. -/
def bridgePrimFn (fnExpr : Expr) (valTys : List Ty) (resTy : Ty) : CompM Expr := do
  let tys := valTys.toArray
  let (doms, cod) ← forallBoundedTelescope (← inferType fnExpr) (some tys.size)
    fun xs body => do
      unless xs.size == tys.size do
        throwError "the primitive takes {xs.size} arguments, and the node has {tys.size}"
      let mut ds : Array Expr := #[]
      let mut seen : Array FVarId := #[]
      for x in xs do
        let d ← inferType x
        if d.hasAnyFVar (fun f => seen.contains f) then
          throwError "a dependent function has no bridge"
        ds := ds.push d
        seen := seen.push x.fvarId!
      if body.hasAnyFVar (fun f => seen.contains f) then
        throwError "a dependent function has no bridge"
      return (ds, body)
  let rec go (i : Nat) (ys args : Array Expr) : CompM Expr := do
    if h : i < tys.size then
      let up ← bridgeUp tys[i] doms[i]!
      let denTy ← denTypeOf tys[i]
      withLocalDeclD `y denTy fun y =>
        go (i + 1) (ys.push y) (args.push (mkApp up y).headBeta)
    else
      let down ← bridgeDown resTy cod
      mkLambdaFVars ys (mkApp down (mkAppN fnExpr args)).headBeta
  termination_by tys.size - i
  go 0 #[] #[]

/-! ### The translation itself -/

/-- The value-argument a structural recursion of Lean descends on, whatever its type:
    the index of that argument among the ones that carry a value. -/
def structuralArg? (c : Name) : MetaM (Option Nat) := do
  let some info := Elab.Structural.eqnInfoExt.find? (← getEnv) c | return none
  let some ci := (← getEnv).find? c | return none
  forallTelescopeReducing ci.type fun xs _ => do
    if h : info.recArgPos < xs.size then
      let recArg := xs[info.recArgPos]
      let mut idx := 0
      for x in xs do
        if ← erasedBinder (← inferType x) then continue
        if x == recArg then return some idx
        idx := idx + 1
      return none
    else return none

/-- The measure of a structural recursion over a **recursive declaration**: the number
    of constructor nodes of the argument recursed on (`Mu.size`).  Every field of a node
    has strictly fewer nodes than the node itself, so a recursive call on a field
    descends in `<` at this measure, which is what `Term.fixAcc` asks for. -/
def muSizeMeasure (c : Name) (ps : List Ty) (idx : Nat) : TermElabM Expr := do
  let tys ← ps.toArray.mapM denTypeOf
  let decls := tys.mapIdx fun i t => (Name.mkSimple s!"x{i}", fun (_ : Array Expr) => pure t)
  withLocalDeclsD decls fun xs => do
    let some x := xs[idx]?
      | throwError "`{c}` recurses at an argument the compiler cannot see"
    let t ← whnf (← inferType x)
    unless t.isAppOfArity ``Mu 2 do
      throwError "`{c}` recurses at an argument that is not a value of a recursive declaration"
    let args := t.getAppArgs
    mkLambdaFVars xs (← mkAppOptM ``Mu.size #[some args[0]!, some args[1]!, some x])

/-- Add a variable to the context. -/
def withVar {α} (fv : FVarId) (τ : Ty) (k : CompM α) : CompM α :=
  withReader (fun c => { c with vars := (fv, τ) :: c.vars }) k

mutual

/-- Compile a Lean expression into a term of the object language. -/
partial def trTerm (e0 : Expr) : CompM (TSyntax `term) := do
  let ctx ← read
  if ctx.fuel == 0 then throwError "the compiler ran out of fuel at `{e0}`"
  let e ← whnfCore e0
  -- a variable
  if let .fvar fv := e then
    if let some i ← lookupVar fv then
      return ← `(Term.var (v♯ $(quote i)))
    throwError "the local `{e}` is not a value of the object language"
  -- a closed scalar
  if !e.hasFVar then
    if let .ok (.prim p) ← toTy (← inferType e) then
      let some pn := primTyIdent p | throwError "no literal of type `{p.pretty}`"
      return ← `(Term.lit $(mkIdent pn) $(← mkAuxValue e))
  match e with
  | .lam _ t b _ =>
      if ← erasedBinder t then
        return ← withLocalDeclD `x t fun x => trTerm (b.instantiate1 x)
      let τ ← tyOf t
      return ← withLocalDeclD `x t fun x =>
        withVar x.fvarId! τ do
          let body ← trTerm (b.instantiate1 x)
          `(Term.lam $body)
  | .letE n t v b _ =>
      if ← erasedBinder t then
        return ← withLocalDeclD n t fun x => trTerm (b.instantiate1 x)
      let τ ← tyOf t
      let vS ← trTerm v
      return ← withLocalDeclD n t fun x =>
        withVar x.fvarId! τ do
          let bS ← trTerm (b.instantiate1 x)
          `(Term.letE $vS $bS)
  | .proj sName i st => return ← trProj sName i st
  | _ => pure ()
  -- an application, or a bare constant
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .fvar fv =>
      let some _ ← lookupVar fv | throwError "the local `{f}` is not a value of the object language"
      let mut out ← trTerm f
      for a in args do
        if ← erasedBinder (← inferType a) then continue
        out ← `(Term.ap $out $(← trTerm a))
      return out
  | .const c _ => trConstApp e c args
  | _ => throwError "the compiler has no rule for `{e}`"

/-- Compile an application of a constant. -/
partial def trConstApp (e : Expr) (c : Name) (args : Array Expr) :
    CompM (TSyntax `term) := do
  -- `if`, `cond`, and the eliminators that a `match` unfolds to
  if c == ``ite || c == ``dite then
    if args.size ≥ 5 then
      let condS ← trDecidable args[1]! args[2]!
      let thenS ← trBranch args[3]! (dep := c == ``dite)
      let elseS ← trBranch args[4]! (dep := c == ``dite)
      return ← applyExtra (← `(Term.bool_elim $condS $thenS $elseS)) (args.extract 5 args.size)
  if c == ``cond && args.size ≥ 4 then
    let condS ← trTerm args[1]!
    let thenS ← trTerm args[2]!
    let elseS ← trTerm args[3]!
    return ← applyExtra (← `(Term.bool_elim $condS $thenS $elseS)) (args.extract 4 args.size)
  if c == ``id && args.size ≥ 2 then
    return ← applyExtra (← trTerm args[1]!) (args.extract 2 args.size)
  -- a cast along an equation, which `match h : e with …` leaves in a body: proofs are
  -- irrelevant and the two sides of the equation are the same value, so what a cast
  -- answers with is what it was handed
  -- `Eq.mpr h b` answers with `b`, and anything further is an argument of it
  if c == ``Eq.mpr && args.size ≥ 4 then
    return ← applyExtra (← trTerm args[3]!) (args.extract 4 args.size)
  -- `@Eq.rec α a motive m b h` and `@Eq.ndrec α a motive m b h` answer with `m`; `b` is
  -- the other side of the equation and `h` is the proof, so neither is an argument the
  -- answer is applied to
  if (c == ``Eq.rec || c == ``Eq.ndrec) && args.size ≥ 4 then
    return ← applyExtra (← trTerm args[3]!) (args.extract 6 args.size)
  -- `Eq.ndrec_symm m h` is the same cast, with the value *before* the equation it is
  -- cast along; a branch of a `dite` that a `match` on a literal generates is this,
  -- applied to the value only, so the equation and its subject are dropped rather than
  -- handed on as arguments
  if c == ``Eq.ndrec_symm && args.size ≥ 4 then
    return ← applyExtra (← trTerm args[3]!) (args.extract 6 args.size)
  if c == ``Eq.casesOn && args.size ≥ 6 then
    return ← applyExtra (← trTerm args[5]!) (args.extract 6 args.size)
  if let some ea := elimApp? c args then
    return ← applyExtra (← trElim ea) ea.extra
  -- a recursive call
  if let some self := (← read).selves.find? (fun s => s.name == c) then
    let mut vals : Array Expr := #[]
    for a in args do
      unless ← erasedBinder (← inferType a) do vals := vals.push a
    if vals.size < self.arity then
      -- a recursive call that is handed on rather than made: η-expand it, so that what
      -- is handed on is a function of the object language whose body is the call
      return ← etaExpandTerm e
    let callArgs := vals.extract 0 self.arity
    let spine ← match self.slot with
      | none => trSpine callArgs.toList
      | some (tag, off, merged) => mutualSpine tag off merged callArgs
    let rvar ← rvarSyntax self.rvar
    return ← applyExtra (← `(Term.selfCall $rvar $spine)) (vals.extract self.arity vals.size)
  -- a matcher: look through it
  let env ← getEnv
  if Lean.Meta.isMatcherCore env c || (← Lean.isProjectionFn c)
      || Lean.Meta.isInstanceCore env c then
    return ← unfoldAndRetry e
  -- a constructor of a datatype, and the eliminator of one
  if let some (.ctorInfo ci) := (← getEnv).find? c then
    return ← trCtorApp e ci args
  if let some indName ← elimInductive? c then
    return ← trDataElim c indName args
  -- a primitive
  if ← isPrimConst c then
    return ← trPrimApp e c args
  -- a recursion of its own: compile it, and apply it
  if ← isRecursiveDecl c then
    let fnS ← compileFun c
    let mut out := fnS
    for a in args do
      if ← erasedBinder (← inferType a) then continue
      out ← `(Term.ap $out $(← trTerm a))
    return out
  -- anything else is looked through
  unfoldAndRetry e

/-- Field `i` of a value of a type the language holds as a **terminal** type: the
    terminal type has no fields of its own, so reading one is an ordinary primitive. -/
partial def trPrimField (sName : Name) (i : Nat) (st : Expr) : CompM (TSyntax `term) := do
  let stTyE ← inferType st
  let stTy ← tyOf stTyE
  let fnExpr ← withLocalDeclD `x stTyE fun x => mkLambdaFVars #[x] (Expr.proj sName i x)
  let resTy ← tyOf (← inferType (Expr.proj sName i st))
  let fnS ← mkAuxValue fnExpr
  let spine ← trSpine [st]
  mkPrimNode [stTy] resTy fnS spine

/-- A projection out of a structure: the eliminator of the record, followed by the
    variable the field it reads is bound to.  Where the structure is a newtype, whose
    wrapper the language erases, the projection *is* the value. -/
partial def trProj (sName : Name) (i : Nat) (st : Expr) : CompM (TSyntax `term) := do
  if (primOfName sName).isSome then
    return ← trPrimField sName i st
  let ind ← getConstInfoInduct sName
  let some ctorName := ind.ctors.head? | throwError "`{sName}` has no constructor"
  let ci ← getConstInfoCtor ctorName
  let some vi ← valueFieldIndex ci i
    | throwError "field {i} of `{sName}` carries no value the object language holds"
  let τ ← tyOf (← inferType st)
  match τ with
  | .record _ => do
      let stS ← trTerm st
      `(Term.record_elim $stS (Term.var (v♯ $(quote vi))))
  | _ =>
      if (← valueFieldCount ci) == 1 then trTerm st
      else throwError "the compiler has no rule for the projection of field {i} out of `{sName}`"

/-- An application of a constructor of a datatype: a record, an enum, a tagged union —
    or a newtype, whose wrapper the language erases. -/
partial def trCtorApp (e : Expr) (ci : ConstructorVal) (args : Array Expr) :
    CompM (TSyntax `term) := do
  let arity := ci.numParams + ci.numFields
  if args.size < arity then return ← etaExpandTerm e
  let base := mkAppN e.getAppFn (args.extract 0 arity)
  let extra := args.extract arity args.size
  -- the fields that carry a value
  let mut vals : Array Expr := #[]
  for a in args.extract ci.numParams arity do
    unless ← erasedBinder (← inferType a) do vals := vals.push a
  let ind ← getConstInfoInduct ci.induct
  -- a constructor of a type the language holds as a *terminal* type builds a value of
  -- that terminal type, so it is a primitive rather than a wrapper the language erases
  if (primOfName ci.induct).isSome then
    return ← trPrimApp e ci.name args
  let τ ← tyOf (← inferType base)
  -- an array, and the three delayed wrappers, are types of the language in their own
  -- right rather than the one-field structures Lean holds them in, so the constructor
  -- builds one with the Lean function that builds it
  if let .primCovariant _ := τ then
    return ← trPrimApp e ci.name args
  -- a newtype: one constructor of one value field, and the wrapper is erased
  if ind.ctors.length == 1 && vals.size == 1 then
    return ← applyExtra (← trTerm vals[0]!) extra
  match τ with
  | .record fs =>
      unless vals.size == fs.toList.length do
        throwError "`{ci.name}` carries {vals.size} values, and its record has {fs.toList.length} fields"
      let sp ← trSpine vals.toList
      applyExtra (← `(Term.record_mk $(← recordSchemaSyntax fs) $sp)) extra
  | .taggedUnion l =>
      let sp ← trSpine vals.toList
      applyExtra
        (← `(Term.taggedUnion_mk $(← tuSchemaSyntax l) $(quote ci.cidx) (by decide) $sp)) extra
  | .enum s =>
      applyExtra (← `(Term.enum_mk
        (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift))
        (Fin.mk $(quote ci.cidx) (by decide)))) extra
  | .prim .bool =>
      if ci.numFields == 0 then
        let b := if ci.cidx == 0 then Lean.mkConst ``Bool.false else Lean.mkConst ``Bool.true
        applyExtra (← `(Term.lit LeanPrimTy.bool $(← mkAuxValue b))) extra
      else trPrimApp e ci.name args
  | .prim _ => trPrimApp e ci.name args
  | .recTaggedUnion l =>
      let some ftys := ctorFieldTys τ
        | throwError "the compiler has no fields for the constructors of `{tyStr τ}`"
      let some fts := ftys[ci.cidx]?
        | throwError "`{ci.name}` is constructor {ci.cidx}, and `{tyStr τ}` has {ftys.length}"
      unless vals.size == fts.length do
        throwError "`{ci.name}` carries {vals.size} values, and its constructor has {fts.length} fields"
      let sp ← trSpine vals.toList
      let fldsS ← recFldsSyntax fts
      applyExtra (← `(Term.recTU_mk ⟨$(← rtyTuSchemaSyntax l.schema), by decide⟩
        $(quote ci.cidx) (by decide) $fldsS $sp)) extra
  | _ => throwError "the compiler has no rule for the constructor `{ci.name}` of type `{tyStr τ}`"

/-- A dispatch on a datatype: `I.rec`, `I.recAux` or `I.casesOn`, for an `I` the object
    language holds as a record, an enum, a tagged union or a newtype. -/
partial def trDataElim (c indName : Name) (args : Array Expr) : CompM (TSyntax `term) := do
  let ind ← getConstInfoInduct indName
  -- the eliminator of a one-constructor type the language holds as a terminal type
  -- binds that constructor's field, which is read by a primitive
  if (primOfName indName).isSome && indName != ``Bool then
    let p := ind.numParams
    unless args.size ≥ p + 3 do
      throwError "`{c}` is applied to fewer arguments than the dispatch needs"
    let isCases := c.getString! == "casesOn"
    let major := if isCases then args[p + 1]! else args[p + 2]!
    let minor := if isCases then args[p + 2]! else args[p + 1]!
    let extra := args.extract (p + 3) args.size
    let some ctorName := ind.ctors.head? | throwError "`{indName}` has no constructor"
    let ci ← getConstInfoCtor ctorName
    unless (← valueFieldCount ci) == 1 do
      throwError "the compiler has no dispatch on a value of the terminal type `{indName}`"
    let some vi ← valueFieldIndex ci 0
      | throwError "field 0 of `{indName}` carries no value the object language holds"
    let fldS ← trPrimField indName vi major
    let fldTy ← tyOf (← inferType (Expr.proj indName vi major))
    let bodyS ← trMinor minor [fldTy]
    return ← applyExtra (← `(Term.letE $fldS $bodyS)) extra
  if ind.all.length > 1 then
    throwError "`{indName}` is part of a `mutual` block, which the object language has no dispatch for"
  unless ind.numIndices == 0 do
    throwError "`{indName}` is an indexed family, which the object language has no dispatch for"
  let p := ind.numParams
  let n := ind.ctors.length
  let need := p + n + 2
  unless args.size ≥ need do
    throwError "`{c}` is applied to fewer arguments than the dispatch needs"
  let isCases := c.getString! == "casesOn"
  let major := if isCases then args[p + 1]! else args[p + 1 + n]!
  let minors := if isCases then args.extract (p + 2) (p + 2 + n) else args.extract (p + 1) (p + 1 + n)
  let extra := args.extract need args.size
  let τ ← tyOf (← inferType major)
  let majorS ← trTerm major
  match ctorFieldTys τ with
  | none =>
      -- a newtype: its one constructor binds the value itself
      unless n == 1 do
        throwError "the compiler has no dispatch on a value of type `{tyStr τ}`"
      let bodyS ← trMinor minors[0]! [τ]
      applyExtra (← `(Term.letE $majorS $bodyS)) extra
  | some ftys =>
      unless ftys.length == n do
        throwError "`{indName}` has {n} constructors, and its `Ty` has {ftys.length}"
      -- the recursor of a recursive datatype hands each branch one induction hypothesis
      -- per field that is an occurrence of the datatype; `casesOn` hands it none
      let ihCounts ←
        if isCases then pure (ftys.map (fun _ => 0))
        else ind.ctors.mapM fun cn => do
          let cinfo ← getConstInfoCtor cn
          forallBoundedTelescope cinfo.type (some (cinfo.numParams + cinfo.numFields))
            fun xs _ => do
              let fields := xs.extract cinfo.numParams xs.size
              let mut k := 0
              for x in fields do
                let t ← whnf (← inferType x)
                if t.getAppFn.constName? == some indName then k := k + 1
              return k
      let branches ← (minors.toList.zip (ftys.zip ihCounts)).mapM
        (fun (m, fts, nih) => trMinorIH m fts nih)
      match τ with
      | .record _ =>
          let some b0 := branches.head? | throwError "a record with no branch"
          applyExtra (← `(Term.record_elim $majorS $b0)) extra
      | .taggedUnion _ =>
          applyExtra (← `(Term.taggedUnion_elim $majorS $(← casesSyntax branches))) extra
      | .enum _ =>
          applyExtra (← `(Term.enum_elim $majorS $(← enumCasesSyntax branches))) extra
      | .recTaggedUnion _ =>
          applyExtra
            (← `(Term.recTU_elim $majorS $(← recCasesSyntax (ftys.zip branches)))) extra
      | .prim .bool =>
          match branches with
          | [bFalse, bTrue] => applyExtra (← `(Term.bool_elim $majorS $bTrue $bFalse)) extra
          | _ => throwError "a boolean dispatch with {branches.length} branches"
      | _ => throwError "the compiler has no dispatch on a value of type `{tyStr τ}`"

/-- One branch of a dispatch: a Lean function of the fields of its constructor, compiled
    with the fields that carry a value bound as the innermost variables — field `0` at de
    Bruijn index `0`, which is how `Cases` and `Term.record_elim` bind them. -/
partial def trMinor (minor : Expr) (fieldTys : List Ty) : CompM (TSyntax `term) := do
  trMinorIH minor fieldTys 0

/-- The branch of a dispatch, where the eliminator is the **recursor** of a recursive
    datatype and so hands the branch `nih` induction hypotheses after the fields.  The
    object language's dispatch takes a value one level apart and binds its fields only,
    so a branch that *reads* an induction hypothesis is a structural recursion rather
    than a dispatch, and is refused here: recursion is `Term.fixAcc`. -/
partial def trMinorIH (minor : Expr) (fieldTys : List Ty) (nih : Nat) :
    CompM (TSyntax `term) := do
  lambdaBoundedValueTelescope minor (fieldTys.length + nih) fun xs inner => do
    let flds := xs.extract 0 fieldTys.length
    let ihs := xs.extract fieldTys.length xs.size
    if inner.hasAnyFVar (fun f => ihs.contains f) then
      throwError "a branch that reads an induction hypothesis of the recursor: a recursion over a recursive declaration is `Term.fixAcc`, which the compiler builds for a recursive `def` and not for a use of the recursor itself"
    withReader (fun ctx => { ctx with vars := (flds.zip fieldTys.toArray).toList ++ ctx.vars })
      (trTerm inner)

/-- The branches of a dispatch on a tagged union. -/
partial def casesSyntax : List (TSyntax `term) → CompM (TSyntax `term)
  | [] => `(Cases.nil)
  | b :: rest => do `(Cases.cons $b $(← casesSyntax rest))

/-- The branches of a dispatch on an enum. -/
partial def enumCasesSyntax : List (TSyntax `term) → CompM (TSyntax `term)
  | [] => `(EnumCases.nil)
  | b :: rest => do `(EnumCases.cons $b $(← enumCasesSyntax rest))

/-- η-expand an expression of function type: `fun x => e x`.  This is what an
    under-applied recursive call becomes, since `Term.selfCall` takes its arguments all
    at once. -/
partial def etaExpandTerm (e : Expr) : CompM (TSyntax `term) := do
  let t ← whnf (← inferType e)
  let .forallE nm dom body bi := t
    | throwError "`{e}` is not applied to enough arguments, and is not a function"
  let _ := (body, bi)
  withLocalDeclD nm dom fun x => do
    let e' := mkApp e x
    if ← erasedBinder dom then
      trTerm e'
    else
      let τ ← tyOf dom
      withVar x.fvarId! τ do `(Term.lam $(← trTerm e'))

/-- Look through a definition and compile what is behind it: the head constant is
    replaced by its value, and the application is β-reduced. -/
partial def unfoldAndRetry (e : Expr) : CompM (TSyntax `term) := do
  let .const c lvls := e.getAppFn
    | throwError "the compiler cannot look through `{e.getAppFn}`"
  let some info := (← getEnv).find? c
    | throwError "unknown constant `{c}`"
  let some val := info.value?
    | throwError "the compiler cannot look through `{c}`, which has no definition"
  let e' := (val.instantiateLevelParams info.levelParams lvls).beta e.getAppArgs
  withReader (fun ctx => { ctx with fuel := ctx.fuel - 1 }) (trTerm e')

/-- Apply a compiled term to the arguments an elimination or a call was over-applied
    with. -/
partial def applyExtra (s : TSyntax `term) (extra : Array Expr) : CompM (TSyntax `term) := do
  let mut out := s
  for a in extra do
    if ← erasedBinder (← inferType a) then continue
    out ← `(Term.ap $out $(← trTerm a))
  return out

/-- The `Bool` a decidable proposition is: `decide c`, compiled as a primitive.

    A condition Lean wrote as the coercion of a `Bool` — `b = true`, which is what
    `if b then …` elaborates to — is that `Bool` itself, and is compiled as such rather
    than as a call of `Decidable.decide`: the decision of `b = true` reads `b`, and `b`
    may be an application of a function the object language holds in a variable, which
    no single primitive can stand for. -/
partial def trDecidable (prop inst : Expr) : CompM (TSyntax `term) := do
  if let some (α, lhs, rhs) := prop.eq? then
    if (← whnf α).isConstOf ``Bool then
      if (← whnfCore rhs).isConstOf ``Bool.true then return ← trTerm lhs
      if (← whnfCore lhs).isConstOf ``Bool.true then return ← trTerm rhs
  let d := mkApp2 (Lean.mkConst ``Decidable.decide) prop inst
  trPrimFallback d

/-- One branch of an `ite` or a `dite`: for a `dite` the branch is a function of the
    proof, which the object language does not have, so the binder is dropped. -/
partial def trBranch (b : Expr) (dep : Bool) : CompM (TSyntax `term) := do
  if !dep then return ← trTerm b
  match ← whnfCore b with
  | .lam n t body _ => withLocalDeclD n t fun x => trTerm (body.instantiate1 x)
  | b' => trTerm b'

/-- A case split on a `Nat` or on a `Bool`. -/
partial def trElim (ea : ElimApp) : CompM (TSyntax `term) := do
  let majorS ← trTerm ea.major
  if !ea.isNat then
    -- `Bool.rec f t b`: the branches are in the order `false`, `true`
    let falseS ← trTerm ea.zero
    let trueS ← trTerm ea.succ
    return ← `(Term.bool_elim $majorS $trueS $falseS)
  -- `Nat`: `n == 0` decides which branch, and the successor branch reads `n - 1`
  let zeroS ← trTerm ea.zero
  let isZero ← `(Term.prim [Ty.nat]
    (prim1 (σ₁ := Ty.nat) (τ := Ty.bool) (fun (n : Nat) => Nat.beq n 0))
    (Spine.cons $majorS Spine.nil))
  let pred ← `(Term.prim [Ty.nat]
    (prim1 (σ₁ := Ty.nat) (τ := Ty.nat) (fun (n : Nat) => n - 1))
    (Spine.cons $majorS Spine.nil))
  let succS ← match ← whnfCore ea.succ with
    | .lam n t body _ =>
        withLocalDeclD n t fun x =>
          withVar x.fvarId! (Ty.prim .nat) do
            let inner := body.instantiate1 x
            -- the induction hypothesis, if the eliminator is `Nat.rec`, is unused
            let inner ← match ← whnfCore inner with
              | .lam m s ib _ =>
                  if (← whnf s).isSort || !(ib.hasLooseBVars) then
                    pure (ib.instantiate1 (Lean.mkConst ``Unit.unit))
                  else withLocalDeclD m s fun _ => pure inner
              | _ => pure inner
            let bodyS ← trTerm inner
            `(Term.letE $pred $bodyS)
    | s => throwError "the successor branch `{s}` is not a function"
  `(Term.bool_elim $isZero $zeroS $succS)

/-- A `Term.prim` node: the Lean function `fnS` of the arguments `argTys`, answering
    with `resTy`, applied to the compiled arguments `spine`.  The type of the function is
    written out, because the node itself is often elaborated with no expected type (the
    first argument of a `Term.letE`, say). -/
partial def mkPrimNode (argTys : List Ty) (resTy : Ty) (fnS spine : TSyntax `term) :
    CompM (TSyntax `term) := do
  if argTys.length > 5 then
    throwError "a primitive of more than five arguments, which `Term.prim` has no packaging for"
  let packer := mkIdent (Name.str `LeanScript.Term s!"prim{argTys.length}")
  let tysS ← tyListSyntax argTys
  let resS ← tySyntax resTy
  let fn ← `(show Tup (Ty.denList $tysS) → Ty.den $resS from $packer $fnS)
  `(Term.prim $tysS $fn $spine)

/-- An application of a primitive: a total Lean function, applied to the values of the
    arguments the object language holds. -/
partial def trPrimApp (e : Expr) (c : Name) (args : Array Expr) : CompM (TSyntax `term) := do
  -- the value arguments, and the Lean function of them
  let mut valIdx : Array Nat := #[]
  let mut valTys : Array Ty := #[]
  for h : i in [0:args.size] do
    let t ← inferType args[i]
    unless ← erasedBinder t do
      valIdx := valIdx.push i
      valTys := valTys.push (← tyOf t)
  if valTys.size > 5 then
    throwError "`{c}` is applied to more than five values, which `Term.prim` has no packaging for"
  let resTy ← tyOf (← inferType e)
  -- build `fun x₁ … xₙ => c … xᵢ …`
  let fnExpr? ← try pure (some (← buildPrimFn e.getAppFn args valIdx)) catch _ => pure none
  let some fnExpr := fnExpr? | return ← trPrimFallback e
  unless ← primFnMatches fnExpr valTys resTy do
    -- the Lean types are not the denotations of their `Ty`s: bridge them, and fall
    -- back to one primitive of the variables the application reads if there is no
    -- bridge
    let bridged? ← try pure (some (← bridgePrimFn fnExpr valTys.toList resTy))
      catch _ => pure none
    let some bridged := bridged? | return ← trPrimFallback e
    if bridged.hasFVar then return ← trPrimFallback e
    let spine ← trSpine (valIdx.toList.map (fun i => args[i]!))
    return ← mkPrimNode valTys.toList resTy (← mkAuxValue bridged) spine
  if fnExpr.hasFVar then
    -- some argument the object language does not hold is read from the context: the
    -- whole application becomes one primitive of the variables it mentions
    return ← trPrimFallback e
  let fnS ← mkAuxValue fnExpr
  let spine ← trSpine (valIdx.toList.map (fun i => args[i]!))
  mkPrimNode valTys.toList resTy fnS spine

/-- The last resort: an expression of a type the object language holds, which mentions
    nothing but the variables in scope and total Lean constants, is **one** primitive —
    the Lean function of those variables — applied to them.

    A **proof** the expression reads — the in-range proof of an indexing operation, say —
    is not a variable of the object language, so it is discharged the way
    `buildPrimFn` discharges one: the primitive decides the proposition and answers with
    the default value of its type where it fails, which a faithful translation never
    reaches. -/
partial def trPrimFallback (e : Expr) : CompM (TSyntax `term) := do
  let ctx ← read
  for self in ctx.selves do
    if e.getUsedConstants.any (· == self.name) then
      throwError "the compiler has no rule for `{e}`, which contains a recursive call"
  let used := ctx.vars.filter (fun (fv, _) => (Expr.fvar fv).occurs e)
  let xs := (used.map (fun (fv, _) => Expr.fvar fv)).toArray
  let mut guards : List (Expr × Expr) := []
  for fv in (Lean.collectFVars {} e).fvarIds do
    if xs.any (fun x => x.fvarId! == fv) then continue
    let ty ← fv.getType
    if ← isProp ty then guards := (ty, Expr.fvar fv) :: guards
  let fnExpr ← mkLambdaFVars xs (← guardByDecisions e guards)
  if fnExpr.hasFVar then
    throwError "the compiler has no rule for `{e}`"
  let resTy ← tyOf (← inferType e)
  let argTys := used.map (fun (_, τ) => τ)
  let fnExpr ←
    if ← primFnMatches fnExpr argTys.toArray resTy then pure fnExpr
    else bridgePrimFn fnExpr argTys resTy
  let fnS ← mkAuxValue fnExpr
  let spine ← trSpine (xs.toList)
  mkPrimNode argTys resTy fnS spine

/-- Wrap a body in the decisions of the propositions the proof arguments of a primitive
    needed: the application is made where the proposition holds, and the default value
    of its type is answered with where it does not.  A faithful translation never takes
    the second branch — the proof the source had is what says so — and it is what makes
    the function total. -/
partial def guardByDecisions (body : Expr) : List (Expr × Expr) → CompM Expr
  | [] => return body
  | (prop, h) :: rest => do
      let .some dec ← trySynthInstance (← mkAppM ``Decidable #[prop])
        | throwError "the proposition `{prop}` a proof argument needs is not decidable"
      let ty ← inferType body
      let dflt ← defaultValueOf ty
      let thenFn ← mkLambdaFVars #[h] body
      let elseFn ← withLocalDeclD `hn (← mkAppM ``Not #[prop]) fun hn =>
        mkLambdaFVars #[hn] dflt
      guardByDecisions
        (← mkAppOptM ``dite #[some ty, some prop, some dec, some thenFn, some elseFn]) rest

/-- The default value of a Lean type, from its `Inhabited` instance. -/
partial def defaultValueOf (ty : Expr) : CompM Expr := do
  let .some inh ← trySynthInstance (← mkAppM ``Inhabited #[ty])
    | throwError "there is no default value of `{ty}`"
  mkAppOptM ``Inhabited.default #[some ty, some inh]

/-- `fun x₁ … xₙ => f a₁ … aₙ`, with the value arguments replaced by the bound
    variables.

    An argument the object language does **not** hold is not carried over but *rebuilt*
    at the type it has once the value arguments are the bound variables, which is what
    lets a primitive with a proof-carrying argument — `a[i]`, whose third argument is a
    proof that `i` is in range — become a Lean function of `a` and `i` alone.  An
    instance is synthesised, a one-value argument is that value, and a **proof** is
    discharged by `guardByDecisions`. -/
partial def buildPrimFn (f : Expr) (args : Array Expr) (valIdx : Array Nat) :
    CompM Expr := do
  let rec go (i : Nat) (ftype : Expr) (acc : Array Expr) (xs : Array Expr)
      (guards : List (Expr × Expr)) : CompM Expr := do
    if i == args.size then
      return ← mkLambdaFVars xs (← guardByDecisions (mkAppN f acc) guards)
    let .forallE nm dom rest _ ← whnf ftype
      | throwError "`{f}` is applied to more arguments than its type has"
    if valIdx.contains i then
      return ← withLocalDeclD nm dom fun x =>
        go (i + 1) (rest.instantiate1 x) (acc.push x) (xs.push x) guards
    -- an argument the object language does not hold: carry it over where its type has
    -- not moved under the bound variables, and rebuild it where it has
    let moved := xs.any (fun x => dom.containsFVar x.fvarId!)
    if !moved && !args[i]!.hasFVar then
      return ← go (i + 1) (rest.instantiate1 args[i]!) (acc.push args[i]!) xs guards
    if (← isClass? dom).isSome then
      let .some inst ← trySynthInstance dom
        | throwError "the instance `{dom}` a primitive needs cannot be synthesised"
      return ← go (i + 1) (rest.instantiate1 inst) (acc.push inst) xs guards
    if ← isProp dom then
      return ← withLocalDeclD nm dom fun h =>
        go (i + 1) (rest.instantiate1 h) (acc.push h) xs ((dom, h) :: guards)
    if ← isErasedType dom then
      let u ← defaultValueOf dom
      return ← go (i + 1) (rest.instantiate1 u) (acc.push u) xs guards
    throwError "an argument of type `{dom}` is not one the compiler rebuilds"
  go 0 (← inferType f) #[] #[] []

/-- A list of arguments, as a `Spine`. -/
partial def trSpine (args : List Expr) : CompM (TSyntax `term) := do
  match args with
  | [] => `(Spine.nil)
  | a :: rest => do
      let aS ← trTerm a
      let restS ← trSpine rest
      `(Spine.cons $aS $restS)

/-- The de Bruijn index of a recursion in scope, as syntax. -/
partial def rvarSyntax (i : Nat) : CompM (TSyntax `term) := do
  match i with
  | 0 => `(RVar.head)
  | n + 1 => do `(RVar.tail $(← rvarSyntax n))

/-- Bind one fresh local of each of the given Lean types, and run `k` with them. -/
partial def withFreshLocals {α} (tys : Array Expr) (k : Array Expr → CompM α) : CompM α := do
  let rec go (i : Nat) (acc : Array Expr) : CompM α := do
    if i == tys.size then k acc
    else withLocalDeclD `x tys[i]! fun x => go (i + 1) (acc.push x)
  go 0 #[]

/-- Hand a body the values of its parameters that carry one, introducing a local for
    each parameter that carries none — a proof, an instance, a type. -/
partial def withValueParams {α} (e : Expr) (vals : Array Expr) (k : Expr → CompM α) :
    CompM α := do
  let rec go (e : Expr) (i : Nat) : CompM α := do
    match ← whnfCore e with
    | .lam nm t b _ =>
        if ← erasedBinder t then
          withLocalDeclD nm t fun x => go (b.instantiate1 x) i
        else if i == vals.size then k (← whnfCore e)
        else go (b.instantiate1 vals[i]!) (i + 1)
    | e' =>
        if i == vals.size then k e'
        else
          let t ← whnf (← inferType e')
          let .forallE nm dom _ _ := t
            | throwError "the body of the declaration takes fewer arguments than its type"
          if ← erasedBinder dom then
            withLocalDeclD nm dom fun x => go (mkApp e' x) i
          else go (mkApp e' vals[i]!) (i + 1)
  go e 0

/-- The arguments of a call of one member of a `mutual` block, as the merged recursion
    takes them: the member's **tag**, then every slot — the caller's own arguments where
    they are the member's, and a value nothing reads everywhere else. -/
partial def mutualSpine (tag off : Nat) (merged : List Ty) (callArgs : Array Expr) :
    CompM (TSyntax `term) := do
  let margs := merged.toArray
  let mut elems : Array (TSyntax `term) := #[← `(Term.lit LeanPrimTy.nat $(quote tag))]
  for p in [1:margs.size] do
    if off ≤ p && p < off + callArgs.size then
      elems := elems.push (← trTerm callArgs[p - off]!)
    else
      let some τ := margs[p]? | throwError "a slot of the merged recursion is missing"
      elems := elems.push (← defaultTermOf τ)
  let mut out ← `(Spine.nil)
  for e in elems.reverse do out ← `(Spine.cons $e $out)
  return out

/-- **A `mutual` block, as one recursion.**

    The block's members all answer with the same type — a block whose members do not is
    refused — so the whole block is one function of a **tag** and of a slot for every
    value argument of every member: the body dispatches on the tag, a call of member `j`
    passes `j` and fills the other members' slots with values nothing reads, and the
    measure is the measure of whichever member the tag names.  `target` is the member
    the answer is the compilation of, which is that one function applied to its tag. -/
partial def compileMutual (members : Array Name) (target : Name) : CompM (TSyntax `term) := do
  let some tagIdx := members.findIdx? (· == target)
    | throwError "`{target}` is not a member of its own `mutual` block"
  -- the parameters of each member, and the answer they all share
  let mut psList : Array (List Ty) := #[]
  let mut leanTys : Array (Array Expr) := #[]
  let mut ret? : Option Ty := none
  for m in members do
    let (ps, r) ← paramTys m
    psList := psList.push ps
    leanTys := leanTys.push (← valueParamTypes m)
    match ret? with
    | none => ret? := some r
    | some r0 =>
        unless Ty.beq r0 r do
          throwError "the members of the `mutual` block of `{target}` do not all answer with the same type"
  let some ret := ret? | throwError "an empty `mutual` block"
  -- the merged argument list: the tag, then the slots of each member in turn
  let mut merged : List Ty := [Ty.prim .nat]
  let mut offs : Array Nat := #[]
  for ps in psList do
    offs := offs.push merged.length
    merged := merged ++ ps
  let allLeanTys := #[Lean.mkConst ``Nat] ++ leanTys.flatten
  let mergedS ← tyListSyntax merged
  -- a slot of the argument tuple, as syntax
  let slotOf (p : Nat) : CompM (TSyntax `term) := do
    let mut out ← `(as)
    for _ in [0:p] do out ← `($out |>.2)
    `($out |>.1)
  -- what each member descends at: the argument Lean's own structural recursion
  -- descends on, or — for a block Lean proved terminating with a measure — that
  -- measure, read out of the termination proof of the block
  let mut structArgs : Array Nat := #[]
  for j in [0:members.size] do
    if let some idx ← structuralNatArg? members[j]! then
      if (psList[j]!)[idx]? == some (Ty.prim .nat) then
        structArgs := structArgs.push idx
  let mut isLex := false
  let mut perMember : Array (TSyntax `term) := #[]
  if structArgs.size == members.size then
    for j in [0:members.size] do
      perMember := perMember.push (← slotOf (offs[j]! + structArgs[j]!))
  else
    let some ms ← wfMutualMeasures members
      | throwError "`{target}` is part of a `mutual` block whose measure the compiler could not read"
    let res ← forallTelescopeReducing (← inferType ms[0]!) fun _ b => whnf b
    if res.isConstOf ``Nat then
      isLex := false
    else if res.isAppOfArity ``Prod 2 && (← whnf res.getAppArgs[0]!).isConstOf ``Nat
        && (← whnf res.getAppArgs[1]!).isConstOf ``Nat then
      isLex := true
    else
      throwError "the measure of the `mutual` block of `{target}` answers with neither a `Nat` nor a pair of them"
    for j in [0:members.size] do
      let fnS ← mkAuxValue ms[j]!
      let mut app := fnS
      for i in [0:psList[j]!.length] do
        app ← `($app $(← slotOf (offs[j]! + i)))
      perMember := perMember.push app
  let mut subjBody := perMember[members.size - 1]!
  for j in [0:members.size - 1] do
    let j' := members.size - 2 - j
    let tagS ← slotOf 0
    subjBody ← `(cond (Nat.beq $tagS $(quote j')) $(perMember[j']!) $subjBody)
  let targetα : TSyntax `term ← if isLex then `(Nat × Nat) else `(Nat)
  let subj ← `(show Env $mergedS → $targetα from fun as => $subjBody)
  withFreshLocals allLeanTys fun locals => do
    -- the bodies, in the merged context: slot `p` is de Bruijn index `p`
    let selves := (List.range members.size).map fun j =>
      ({ name := members[j]!, arity := psList[j]!.length, rvar := 0,
         slot := some (j, offs[j]!, merged) } : SelfRef)
    let mergedVars := (locals.map (·.fvarId!)).zip merged.toArray
    let bodies ← withReader (fun ctx =>
        { ctx with
          vars := mergedVars.toList ++ ctx.vars,
          selves := selves ++ ctx.selves.map (fun s => { s with rvar := s.rvar + 1 }) }) do
      let mut out : Array (TSyntax `term) := #[]
      for j in [0:members.size] do
        let b ← bodyOf members[j]!
        let bs ← withValueParams b (locals.extract offs[j]! (offs[j]! + psList[j]!.length))
          fun inner => trTerm inner
        out := out.push bs
      pure out
    -- the dispatch on the tag
    let mut bodyS := bodies[members.size - 1]!
    for j in [0:members.size - 1] do
      let j' := members.size - 2 - j
      let cnd ← `(Term.prim [Ty.nat]
        (prim1 (σ₁ := Ty.nat) (τ := Ty.bool) (fun (n : Nat) => Nat.beq n $(quote j')))
        (Spine.cons (Term.var (v♯ 0)) Spine.nil))
      bodyS ← `(Term.bool_elim $cnd $(bodies[j']!) $bodyS)
    let ndS ← defaultTermOf ret
    let fixS ← if isLex then
        `(Term.fixAcc $mergedS NatLex NatLex.dec $subj (accLexOf $subj) Uncond $bodyS $ndS)
      else
        `(Term.fixAcc $mergedS NatLt NatLt.dec $subj (accOf $subj) Uncond $bodyS $ndS)
    -- the member asked for: the merged recursion, applied to its tag and its slots
    let m := psList[tagIdx]!.length
    let margs := merged.toArray
    let mut appS ← `(Term.var (v♯ $(quote m)))
    appS ← `(Term.ap $appS (Term.lit LeanPrimTy.nat $(quote tagIdx)))
    for p in [1:margs.size] do
      if offs[tagIdx]! ≤ p && p < offs[tagIdx]! + m then
        let i := p - offs[tagIdx]!
        appS ← `(Term.ap $appS (Term.var (v♯ $(quote (m - 1 - i)))))
      else
        let some τ := margs[p]? | throwError "a slot of the merged recursion is missing"
        appS ← `(Term.ap $appS $(← defaultTermOf τ))
    for _ in [0:m] do appS ← `(Term.lam $appS)
    `(Term.letE $fixS $appS)

/-- Compile a whole declaration into a term of type `Ty.arrows ps τ`, valid in any
    context: a recursion becomes a `Term.fixAcc`, and anything else a nest of
    `Term.lam`s. -/
partial def compileFun (c : Name) (measure? : Option Expr := none) : CompM (TSyntax `term) := do
  let kind ← recursionKindOf c
  unless kind.representable do
    throwError "`{c}` is {(kind.describe).1}, which `Term` has no constructor for"
  if measure?.isNone then
    if let some members ← mutualMembers c then
      return ← compileMutual members c
  if let .structural true := kind then throwError "`{c}` is part of a `mutual` block"
  if let .wellFounded true := kind then throwError "`{c}` is part of a `mutual` block"
  let (ps, resTy) ← paramTys c
  let body ← bodyOf c
  let isRec ← isRecursiveDecl c
  if !isRec then
    -- λ-abstract the value parameters, innermost binder last
    let rec goLam (e : Expr) (acc : List Ty) : CompM (TSyntax `term) := do
      match ← whnfCore e with
      | .lam n t b _ =>
          if ← erasedBinder t then
            withLocalDeclD n t fun x => goLam (b.instantiate1 x) acc
          else
            let τ ← tyOf t
            withLocalDeclD n t fun x =>
              withVar x.fvarId! τ do
                let inner ← goLam (b.instantiate1 x) (τ :: acc)
                `(Term.lam $inner)
      | e' => trTerm e'
    return ← goLam body []
  -- a recursion: what does it descend at?  A measure the command was given, else the
  -- argument Lean's own structural recursion descends on, else the measure Lean's own
  -- termination proof descends at.  There is no guess here: a measure that does not
  -- descend would make the compiled term answer with its `nodescend` field rather than
  -- with what the Lean function answers with, so a declaration whose measure cannot be
  -- read is refused.
  let (subj, isLex) ← match measure? with
    | some m => subjectOfMeasure c ps m
    | none =>
      match ← structuralNatArg? c with
      | some idx => do
          -- a structural recursion on a `Nat` descends at that argument itself, which
          -- `subjN` reads out of the argument tuple
          unless ps[idx]? == some (Ty.prim .nat) do
            throwError "`{c}` recurses at its argument number {idx}, which is not a `Nat` of the object language"
          unless idx ≤ 4 do
            throwError "`{c}` recurses at its argument number {idx}, and the compiler reads a subject out of the first five arguments only"
          let psS ← tyListSyntax ps
          let subjIdent := mkIdent (Name.str `LeanScript.Term s!"subj{idx}")
          pure ((← `(show Env $psS → Nat from $subjIdent)), false)
      | none =>
        -- a structural recursion over a recursive declaration descends at the number of
        -- constructor nodes of the argument it recurses on
        match ← structuralArg? c with
        | some idx =>
            match ps[idx]? with
            | some (.recTaggedUnion _) =>
                pure ((← mkSubject ps (← muSizeMeasure c ps idx) (← `(Nat))), false)
            | _ =>
              match ← wfMeasure? c with
              | some m => subjectOfMeasure c ps m
              | none =>
                throwError "`{c}` recurses, and the compiler could not read the measure its termination proof descends at; give one with `measure`"
        | none =>
          match ← wfMeasure? c with
          | some m => subjectOfMeasure c ps m
          | none =>
            throwError "`{c}` recurses, and the compiler could not read the measure its termination proof descends at; give one with `measure`"
  -- the body, with the parameters bound by `fixAcc` — parameter `0` is index `0`
  let bodyS ← lambdaBoundedValueTelescope body ps.length fun xs inner => do
    withReader (fun ctx =>
        { ctx with
          vars := (xs.zip ps.toArray).toList ++ ctx.vars,
          selves := { name := c, arity := ps.length, rvar := 0 } ::
            ctx.selves.map (fun s => { s with rvar := s.rvar + 1 }) }) do
      trTerm inner
  let psS ← tyListSyntax ps
  let ndS ← defaultTermOf resTy
  if isLex then
    `(Term.fixAcc $psS NatLex NatLex.dec $subj (accLexOf $subj) Uncond $bodyS $ndS)
  else
    `(Term.fixAcc $psS NatLt NatLt.dec $subj (accOf $subj) Uncond $bodyS $ndS)

/-- The subject of a recursion at a measure, and whether that measure descends
    lexicographically: a measure answers with a `Nat`, or with a pair of them, and with
    nothing else. -/
partial def subjectOfMeasure (c : Name) (ps : List Ty) (measure : Expr) :
    CompM (TSyntax `term × Bool) := do
  let mType ← whnf (← inferType measure)
  let res ← forallTelescopeReducing mType fun _ b => whnf b
  -- the two components of a pair are looked at only once the head really is `Prod`,
  -- since `getAppArgs` of anything else has none
  let isNatPair : MetaM Bool := do
    let args := res.getAppArgs
    unless res.isAppOf ``Prod && args.size == 2 do return false
    unless (← whnf args[0]!).isConstOf ``Nat do return false
    return (← whnf args[1]!).isConstOf ``Nat
  if res.isConstOf ``Nat then
    return ((← mkSubject ps measure (← `(Nat))), false)
  else if ← isNatPair then
    return ((← mkSubject ps measure (← `(Nat × Nat))), true)
  else
    let resStr := toString (← ppExpr res)
    throwError "the measure of `{c}` answers with `{resStr}`, and the compiler descends only in `<` on a `Nat` or lexicographically on a pair of them"

/-- The subject of a recursion: a `Nat`-valued Lean function of the arguments, as a
    function of the argument *tuple*, which is what `Term.fixAcc` takes. -/
partial def mkSubject (ps : List Ty) (measure : Expr) (target : TSyntax `term) :
    CompM (TSyntax `term) := do
  if ps.length > 10 then
    throwError "a recursion of more than ten arguments, which the compiler has no subject for"
  let packer := mkIdent (Name.str `LeanScript.Term s!"meas{ps.length}")
  let psS ← tyListSyntax ps
  let fnS ← mkAuxValue measure
  `(show Tup (Ty.denList $psS) → $target from $packer $fnS)

/-- Bind the value parameters of a body, in order, and run `k` with their `FVarId`s. -/
partial def lambdaBoundedValueTelescope {α} (e : Expr) (n : Nat)
    (k : Array FVarId → Expr → CompM α) : CompM α := do
  let rec go (e : Expr) (acc : Array FVarId) (k' : Array FVarId → Expr → CompM α) :
      CompM α := do
    if acc.size == n then return ← k' acc e
    match ← whnfCore e with
    | .lam nm t b _ =>
        if ← erasedBinder t then
          withLocalDeclD nm t fun x => go (b.instantiate1 x) acc k'
        else
          withLocalDeclD nm t fun x => go (b.instantiate1 x) (acc.push x.fvarId!) k'
    | e' =>
        if acc.size == n then k' acc e'
        else do
          -- the body is η-short of the type: apply it to one more argument
          let t ← whnf (← inferType e')
          let .forallE nm dom _ _ := t
            | throwError "the body of the declaration takes fewer arguments than its type"
          let erased ← erasedBinder dom
          withLocalDeclD nm dom fun x =>
            if erased then go (mkApp e' x) acc k'
            else go (mkApp e' x) (acc.push x.fvarId!) k'
  go e #[] k

/-- A value of a type to answer a recursive call that does not descend with.  It is
    never read by a faithful translation. -/
partial def defaultTermOf (τ : Ty) : CompM (TSyntax `term) := do
  match τ with
  | .prim p =>
      let some pn := primTyIdent p | throwError "no default value of type `{p.pretty}`"
      let lit : TSyntax `term ← match p with
        | .nat => `((0 : Nat))
        | .int => `((0 : Int))
        | .bool => `(false)
        | .char => `(('a' : Char))
        | .string => `(("" : String))
        | .uint8 => `((0 : UInt8))
        | .uint16 => `((0 : UInt16))
        | .uint32 => `((0 : UInt32))
        | .uint64 => `((0 : UInt64))
        | .int8 => `((0 : Int8))
        | .int16 => `((0 : Int16))
        | .int32 => `((0 : Int32))
        | .int64 => `((0 : Int64))
        | .float => `((0.0 : Float))
        | .float32 => `((0.0 : Float32))
        | .stringPosRaw => `((⟨0⟩ : String.Pos.Raw))
        | .substringRaw => `(("" : String).toSubstring)
        | .stringSlice => `(("" : String).toSlice)
        | _ => throwError "no default value of type `{p.pretty}`"
      `(Term.lit $(mkIdent pn) $lit)
  | .fn _ b => do `(Term.lam $(← defaultTermOf b))
  | .array a => do mkPrimNode [] (.array a) (← `((#[]))) (← `(Spine.nil))
  | .thunk b => do `(Term.thunkMk $(← defaultTermOf b))
  | .lazy b => do `(Term.lazyMk $(← defaultTermOf b))
  | .record fs => do
      let sp ← defaultSpineOf fs.toList
      `(Term.record_mk $(← recordSchemaSyntax fs) $sp)
  | .enum s => do
      `(Term.enum_mk (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift))
        (Fin.mk 0 (by decide)))
  | .taggedUnion l => do
      let some fs := l.toList.head? | throwError "a tagged union with no constructor"
      let sp ← defaultSpineOf fs
      `(Term.taggedUnion_mk $(← tuSchemaSyntax l) 0 (by decide) $sp)
  | .recTaggedUnion l => do
      -- a constructor with no occurrence of the declaration among its fields: one level
      -- is all a value built here is, so the recursion of the type is not entered
      let some ftys := ctorFieldTys (.recTaggedUnion l)
        | throwError "the compiler has no fields for the constructors of `{tyStr (.recTaggedUnion l)}`"
      let isBase (fs : List Ty) : Bool := fs.all fun
        | .prim _ => true
        | _ => false
      let some t := ftys.findIdx? isBase
        | throwError "every constructor of `{tyStr (.recTaggedUnion l)}` holds one of its own values, so the compiler has no value of it to stop a recursion with"
      let sp ← defaultSpineOf (ftys.getD t [])
      `(Term.recTU_mk ⟨$(← rtyTuSchemaSyntax l.schema), by decide⟩ $(quote t) (by decide)
        $(← recFldsSyntax (ftys.getD t [])) $sp)
  | τ => throwError "the compiler has no value of the type `{tyStr τ}` to stop a recursion with"

/-- The values of a list of types to stop a recursion with, as a `Spine`. -/
partial def defaultSpineOf : List Ty → CompM (TSyntax `term)
  | [] => `(Spine.nil)
  | τ :: rest => do `(Spine.cons $(← defaultTermOf τ) $(← defaultSpineOf rest))

end

/-! ## The command -/

/-- The empty signature: a compiled term names no global, because every definition it
    uses is either a primitive or looked through. -/
def emptySig : Sig := ⟨[], by decide⟩

/-- The Lean type a compiled declaration answers with: its own type, with the
    parameters that carry no value dropped. -/
def leanFnType (n : Name) : MetaM Expr := do
  let some ci := (← getEnv).find? n | throwError "unknown declaration `{n}`"
  forallTelescopeReducing ci.type fun xs body => do
    let mut tys : Array Expr := #[]
    for x in xs do
      let t ← inferType x
      unless ← erasedBinder t do tys := tys.push t
    if body.hasFVar then throwError "`{n}` has a dependent type"
    if tys.any (·.hasFVar) then throwError "`{n}` has a dependent type"
    return tys.foldr (fun a b => mkForall `x BinderInfo.default a b) body

/-- Compile one declaration: add `f.leanTerm`, and `f.leanFn` where the Lean type of
    the declaration really is the denotation of its `Ty`.  The answer says whether
    `f.leanFn` was added. -/
def compileDeclCore (n : Name) (measure? : Option (TSyntax `term)) : TermElabM Bool := do
  let (ps, resTy) ← paramTys n
  let fullTy := Ty.arrows ps resTy
  let tyS ← tySyntax fullTy
  let m? ← match measure? with
    | none => pure none
    | some mstx => do
        let tys ← valueParamTypes n
        let target ← mkFreshTypeMVar
        let expected := tys.foldr (fun a b => mkForall `x BinderInfo.default a b) target
        let m ← Lean.Elab.Term.elabTerm mstx (some expected)
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        pure (some (← instantiateMVars m))
  let termS ← ((compileFun n m?).run {}).run' { root := n ++ `leanTerm }
  -- the type of the compiled term, and the term itself
  let tyStx ← `(LeanScript.Expr.Term LeanScript.Term.emptySig [] [] $tyS)
  let termType ← Lean.Elab.Term.elabType tyStx
  let value ← Lean.Elab.Term.elabTerm termS (some termType)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasSorry then throwError "the compiled term of `{n}` did not elaborate"
  if value.hasExprMVar then throwError "the compiled term of `{n}` is not fully determined"
  let termType ← instantiateMVars termType
  let value ← Lean.Elab.Term.levelMVarToParam value
  let termType ← Lean.Elab.Term.levelMVarToParam termType
  let lvlState := collectLevelParams (collectLevelParams {} termType) value
  let levelParams := lvlState.params.toList
  addDecl (Declaration.defnDecl
    { name := n ++ `leanTerm, levelParams := levelParams, type := termType,
      value := value,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })
  -- `f.leanFn` is the generated term, run: an ordinary Lean function of the same type
  -- as `f` itself, which is what an `example` settled by `decide +kernel` compares
  -- against the answer Lean computes.
  let type ← leanFnType n
  let t := Lean.mkConst (n ++ `leanTerm) (levelParams.map Level.param)
  let targs := termType.getAppArgs
  unless targs.size == 4 do throwError "the compiled term has an unexpected type"
  let fnValue := mkAppN (Lean.mkConst `LeanScript.Term.evalClosed)
    #[targs[0]!, targs[3]!, Lean.mkConst ``PUnit.unit [1], t]
  -- the denotation of the `Ty` is not always the Lean type the declaration was
  -- written at: a one-field structure is erased to the type of its field, say.  Where
  -- the two differ the answer is **bridged** into the Lean type, so that `f.leanFn` is
  -- a function of exactly `f`'s own type and the two can be compared; and where there
  -- is no bridge only the term itself is added.
  if ← isDefEq (← inferType fnValue) type then
    addDecl (Declaration.defnDecl
      { name := n ++ `leanFn, levelParams := [], type := type, value := fnValue,
        hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })
    return true
  let bridged? ← try
      let up ← ((bridgeUp fullTy type).run {}).run' { root := n ++ `leanFn }
      let v ← instantiateMVars (mkApp up fnValue).headBeta
      if ← isDefEq (← inferType v) type then pure (some v) else pure none
    catch _ => pure none
  match bridged? with
  | some v =>
      addDecl (Declaration.defnDecl
        { name := n ++ `leanFn, levelParams := [], type := type, value := v,
          hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })
      return true
  | none => return false

/-- Compile one declaration, and add `f.leanTerm` to the environment.  `measure?` is the
    syntax of a `Nat`-valued Lean function of the value parameters of the declaration —
    or of a pair of them, for a recursion that descends lexicographically — which the
    recursion descends at; without one the compiler takes the argument Lean's own
    structural recursion descends on, and failing that the first `Nat` argument. -/
def compileDecl (n : Name) (measure? : Option (TSyntax `term) := none) :
    CommandElabM Bool := do
  if (← getEnv).contains (n ++ `leanTerm) then
    throwError "`{n}` has been compiled already"
  -- a declaration the compiler refuses is a *report*, so the error is answered with
  -- rather than thrown out of the elaboration, and nothing the attempt added stays
  let outcome : Except String Bool ← liftTermElabM <| Lean.Elab.Term.withoutErrToSorry do
    let env0 ← getEnv
    try
      let b ← compileDeclCore n measure?
      return Except.ok b
    catch e =>
      setEnv env0
      return Except.error (← e.toMessageData.toString)
  match outcome with
  | .ok b => return b
  | .error m => throwError m

/-- Compile a Lean definition into a `LeanScript.Expr.Term`, bound to `f.leanTerm`. -/
syntax (name := compileTermFor)
  "#leanjs_compile_term_for " ident (&" measure " term)? : command

@[command_elab compileTermFor]
def elabCompileTermFor : CommandElab := fun stx => do
  match stx with
  | `(#leanjs_compile_term_for $i:ident) => do
      let n ← liftCoreM (realizeGlobalConstNoOverload i)
      discard <| compileDecl n
  | `(#leanjs_compile_term_for $i:ident measure $m:term) => do
      let n ← liftCoreM (realizeGlobalConstNoOverload i)
      discard <| compileDecl n (some m)
  | _ => throwUnsupportedSyntax

/-! ## Compiling a whole module

`#leanjs_compile_term_for_all` applies the compiler to **every public function of the
file it appears in**, and says of each one whether it was compiled or, in a sentence,
why it was refused.  That is the companion of `#leanjs_generate_term_and_ctx_for_all`,
which only reports: this one actually adds the terms. -/

/-- Is this a declaration that answers with a type or a proposition — the auxiliary
    constructions of an inductive type, and anything else that is not a function of
    values? -/
def isTypeLevel (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return true
  -- a universe-polymorphic declaration speaks about types, which the object language
  -- has none of
  unless ci.levelParams.isEmpty do return true
  forallTelescopeReducing ci.type fun _ body => do
    if (← whnf body).isSort then return true
    if ← isProp body then return true
    return false

/-- Compile every public function of the file this command appears in, and report on
    each. -/
syntax (name := compileTermForAll) "#leanjs_compile_term_for_all" : command

/-- Is this a declaration the compiler itself added — `f.leanTerm`, `f.leanFn` or one of
    the auxiliary values a generated term holds its Lean functions in?  Those are not
    functions of the file, and compiling them again would only report on the compiler. -/
def isGenerated (n : Name) : Bool :=
  let rec go : Name → Bool
    | .str p s => s == "leanTerm" || s == "leanFn" || go p
    | .num p _ => go p
    | .anonymous => false
  go n

@[command_elab compileTermForAll]
def elabCompileTermForAll : CommandElab := fun _ => do
  let ns := (← liftCoreM publicFunctions).filter (fun n => !isGenerated n)
  if ns.isEmpty then
    logInfo "no public function in this module"
  let mut lines : Array String := #[]
  for n in ns do
    -- a declaration that answers with a type or a proposition is not a function of the
    -- object language at all, and saying so of each one would drown the report
    if ← liftTermElabM (isTypeLevel n) then continue
    if (← getEnv).contains (n ++ `leanTerm) then
      lines := lines.push s!"  compiled  {n}  (above, with a measure of its own)"
      continue
    let st ← get
    try
      let withFn ← compileDecl n
      lines := lines.push
        (if withFn then s!"  compiled  {n}" else
          s!"  compiled  {n}  (no leanFn: its Lean type is not the denotation of its Ty)")
    catch e =>
      -- put back what a failed attempt added, and say why it failed
      set st
      let msg := (← e.toMessageData.toString).replace "\n" " "
      let msg := if msg.length > 160 then (msg.take 160).toString ++ " ..." else msg
      lines := lines.push s!"  refused   {n}: {msg}"
  logInfo ("LeanTerms of this module\n" ++ "\n".intercalate lines.toList)


/-! ## The `Ty` of a Lean type

The type translation is useful on its own: `leanscript_ty% T` is the `LeanScript.Ty` of
the Lean type `T`, as a term, and `#leanjs_ty_for T` reports it.  Both refuse, with the
reason, a Lean type the language has no shape for. -/

/-- `leanscript_ty% T` elaborates to the `LeanScript.Ty` of the Lean type `T`. -/
syntax (name := leanscriptTyTerm) "leanscript_ty% " term : term

@[term_elab leanscriptTyTerm]
def elabLeanscriptTyTerm : TermElab := fun stx expectedType? => do
  match stx with
  | `(leanscript_ty% $t:term) => do
      let e ← elabType t
      let tau ← tyOf e
      elabTerm (← tySyntax tau) expectedType?
  | _ => throwUnsupportedSyntax

/-- `#leanjs_ty_for T` reports the `Ty` of the Lean type `T`. -/
syntax (name := tyForCmd) "#leanjs_ty_for " term : command

@[command_elab tyForCmd]
def elabTyForCmd : CommandElab := fun stx => do
  match stx with
  | `(#leanjs_ty_for $t:term) =>
      liftTermElabM do
        let e ← elabType t
        let nameS := toString (← Meta.ppExpr e)
        match ← toTy e with
        | .ok tau => logInfo s!"{nameS} : {tyStr tau}"
        | .erased => logInfo s!"{nameS} : - (a type the language erases: it carries no value)"
        | .no r => logInfo s!"{nameS} : - (no Ty: {r})"
  | _ => throwUnsupportedSyntax

/-! ## The schema of a Lean datatype, and the values it caches

`#leanjs_schema_for T` is `#leanjs_ty_for T` read as a *declaration*: which schema the
datatype has, and whether it is a plain schema or one that carries computed fields.  The
answer is decided, not declared — a declaration that caches values computed from itself
(`Lean.Name`, which stores its own `hash`) is recognised by the elaborator, and the types
of the cached values are read off the declaration, so a schema with computed fields is
reported wherever Lean has one. -/

/-- Which shape of `Ty` this is, by name. -/
def shapeKind : Ty → String
  | .prim _ => "terminal"
  | .fn _ _ => "function"
  | .primCovariant (.array _) => "array"
  | .primCovariant (.thunk _) => "thunk"
  | .primCovariant (.lazy _) => "lazy"
  | .enum _ => "LeanEnumSchema"
  | .record _ => "LeanRecordSchema"
  | .taggedUnion _ => "LeanTaggedUnionSchema"
  | .recTaggedUnion _ => "LeanTaggedUnionSchema (recursive)"
  | .recObject _ => "LeanRecordSchema (recursive)"
  | .recAlias _ => "RTy (recursive newtype)"
  | .mutualRecursiveFamily _ => "LeanMutualRecFamily"
  | .withComputedFields b _ => shapeKind b ++ " with computed fields"

/-- `#leanjs_schema_for T` reports the schema of the Lean datatype `T`, and the types of
    the values it caches if it has any. -/
syntax (name := schemaForCmd) "#leanjs_schema_for " term : command

@[command_elab schemaForCmd]
def elabSchemaForCmd : CommandElab := fun stx => do
  match stx with
  | `(#leanjs_schema_for $t:term) =>
      liftTermElabM do
        let e ← elabType t
        let nameS := toString (← Meta.ppExpr e)
        match ← toTy e with
        | .ok tau =>
            let (base, computed) :=
              match tau with
              | .withComputedFields b cs => (b, " ".intercalate (cs.toList.map (fun p : LeanPrimTy => p.pretty)))
              | _ => (tau, "-")
            logInfo s!"{nameS}\n  schema    : {shapeKind base}\n  \
              shape     : {tyStr base}\n  computed  : {computed}"
        | .erased =>
            logInfo s!"{nameS}\n  schema    : - (a type the language erases: it carries no value)"
        | .no r => logInfo s!"{nameS}\n  schema    : - (no Ty: {r})"
  | _ => throwUnsupportedSyntax

end LeanScript.Term
