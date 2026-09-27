module

public meta import LeanScript.TermElab.ToTerm.Basic

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: structurally terminating `while` loops

A `while c do body` loop in `Id` (`forIn Loop.mk init f`, whose step `f () s` is
`if c then … yield s' … else done s`) is not structurally recursive in Lean: `Lean.Loop.forIn`
is a `partial` definition.  The language has no fixpoint and no fuel, so the translator only
accepts a loop whose termination it **reads off the syntax**, and translates it to a
`Comp.nat_rec` that runs a number of steps bounded in advance.

The loop is accepted when its condition `c` bounds a mutable variable `x : Nat` of the state
and every `yield` of the body (every iteration that goes on) moves `x` towards the bound by a
literal step:

| the condition `c` has a conjunct   | every `yield` sets `x` to    | the steps (`nat_rec` count)    |
|------------------------------------|------------------------------|--------------------------------|
| `x > e`, `e < x`, `x ≠ 0`, `x != 0`, `k ≤ x` (`k ≥ 1`) | `x - k` (`k ≥ 1`), `x / k` (`k ≥ 2`), `x.pred` | `x₀ + 1`            |
| `x < b`, `b > x`                   | `x + k`, `k + x` (`k ≥ 1`), `x.succ` | `b₀ - x₀ + 1`          |
| `x ≤ b`, `b ≥ x`                   | the same                      | `b₀ + 1 - x₀ + 1`             |

where `x₀` and `b₀` are the values before the loop, and `b` does not change in the loop (it
does not mention the state, or it is a variable of the state that every `yield` passes
unchanged).  Every iteration that goes on then makes the measure (`x`, `b - x`,
`b + 1 - x`) strictly smaller, so the loop stops after at most `x₀` (`b₀ - x₀`, …) iterations
that go on, plus the last one: the bounded loop reaches the same final state.  Any other
`while` loop (`repeat`, a `continue` that skips the step, a step that is not a literal, a
bound the loop changes) is refused.
-/

open Lean Meta

namespace LeanScript.Gen

/-- A candidate reading of the condition of a `while` loop: `x` is positive (`pos`), or
    `x < b` (`lt … false`) / `x ≤ b` (`lt … true`). -/
inductive WGuard where
  | pos (x : Expr)
  | lt (x b : Expr) (le : Bool)
  deriving Inhabited, Repr, BEq, Hashable

/-- Replace every `let`/`have` by its value, everywhere. -/
def zetaAll (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => match e with
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- The arguments of the `ForInStep.yield`s of a step, outside the steps of nested loops. -/
partial def collectYields (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``ForInStep.yield 2 then acc.push e.appArg!
  else if e.isAppOf ``ForIn.forIn || e.isAppOf ``ForIn'.forIn' then
    -- a nested loop: its own `yield`s are not iterations of this one
    e.getAppArgs.pop.foldl (fun acc a => collectYields a acc) acc
  else match e with
    | .app f a => collectYields a (collectYields f acc)
    | .lam _ t b _ | .forallE _ t b _ => collectYields b (collectYields t acc)
    | .letE _ t v b _ => collectYields b (collectYields v (collectYields t acc))
    | .proj _ _ b => collectYields b acc
    | _ => acc

/-- The candidate readings of a condition (a proposition). -/
partial def guardCands (c : Expr) : MetaM (Array WGuard) := do
  let c := c.consumeMData
  let args := c.getAppArgs
  let lit (e : Expr) : MetaM (Option Nat) := natLit? e
  match c.getAppFn.constName?, args.size with
  | some ``And, 2 => return (← guardCands args[0]!) ++ (← guardCands args[1]!)
  | some ``Eq, 3 =>
      if args[2]!.consumeMData.isConstOf ``Bool.true then boolCands args[1]! else return #[]
  | some ``Ne, 3 => if (← lit args[2]!) == some 0 then return #[.pos args[1]!] else return #[]
  | some ``Not, 1 =>
      let p := args[0]!.consumeMData
      if p.isAppOfArity ``Eq 3 && (← lit (p.getArg! 2)) == some 0 then
        return #[.pos (p.getArg! 1)]
      return #[]
  | some ``LT.lt, 4 => return #[.pos args[3]!, .lt args[2]! args[3]! false]
  | some ``GT.gt, 4 => return #[.pos args[2]!, .lt args[3]! args[2]! false]
  | some ``LE.le, 4 => do
      let p := if ((← lit args[2]!).getD 0) ≥ 1 then #[WGuard.pos args[3]!] else #[]
      return p.push (.lt args[2]! args[3]! true)
  | some ``GE.ge, 4 => do
      let p := if ((← lit args[3]!).getD 0) ≥ 1 then #[WGuard.pos args[2]!] else #[]
      return p.push (.lt args[3]! args[2]! true)
  | _, _ => return #[]
where
  /-- The candidate readings of a Boolean condition. -/
  boolCands (b : Expr) : MetaM (Array WGuard) := do
    let b := b.consumeMData
    let args := b.getAppArgs
    match b.getAppFn.constName?, args.size with
    | some ``and, 2 => return (← boolCands args[0]!) ++ (← boolCands args[1]!)
    | some ``bne, 4 => if (← natLit? args[3]!) == some 0 then return #[.pos args[2]!] else return #[]
    | some ``not, 1 =>
        let p := args[0]!.consumeMData
        if p.isAppOfArity ``BEq.beq 4 && (← natLit? (p.getArg! 3)) == some 0 then
          return #[.pos (p.getArg! 2)]
        return #[]
    | some ``Decidable.decide, 2 => guardCands args[0]!
    | some ``Nat.blt, 2 => return #[.pos args[1]!, .lt args[0]! args[1]! false]
    | some ``Nat.ble, 2 => return #[.lt args[0]! args[1]! true]
    | _, _ => return #[]

/-- The path (`false`: first component, `true`: second) of a component of the state `r` of a
    loop (the mutable variables, a nest of pairs), when `x` is one. -/
partial def statePath? (r x : Expr) : Option (List Bool) :=
  let x := x.consumeMData
  if x == r then some []
  else if x.isAppOfArity ``Prod.fst 3 || x.isAppOfArity ``MProd.fst 3 then
    (statePath? r x.appArg!).map (· ++ [false])
  else if x.isAppOfArity ``Prod.snd 3 || x.isAppOfArity ``MProd.snd 3 then
    (statePath? r x.appArg!).map (· ++ [true])
  else match x with
    | .proj S i b =>
        if (S == ``Prod || S == ``MProd) && i < 2 then (statePath? r b).map (· ++ [i == 1])
        else none
    | _ => none

/-- The component at `path` of a state built syntactically by `Prod.mk`/`MProd.mk`. -/
def componentAt? (v : Expr) : List Bool → Option Expr
  | [] => some v
  | b :: p =>
    let v := v.consumeMData
    if v.isAppOfArity ``Prod.mk 4 || v.isAppOfArity ``MProd.mk 4 then
      componentAt? (if b then v.getArg! 3 else v.getArg! 2) p
    else none

/-- The component at `path` of the state `v`: syntactically when `v` is built by `Prod.mk`,
    else by projections. -/
def componentOf (v : Expr) : List Bool → MetaM Expr
  | [] => pure v
  | b :: p => do
    let v' := v.consumeMData
    if v'.isAppOfArity ``Prod.mk 4 || v'.isAppOfArity ``MProd.mk 4 then
      componentOf (if b then v'.getArg! 3 else v'.getArg! 2) p
    else
      let ty ← whnfR (← inferType v)
      let isM := ty.isAppOf ``MProd
      let f := if isM then (if b then ``MProd.snd else ``MProd.fst)
        else (if b then ``Prod.snd else ``Prod.fst)
      componentOf (← mkAppM f #[v]) p

/-- Is `e` syntactically the same expression as `x` (up to metadata and instances)? -/
def sameAs (e x : Expr) : MetaM Bool := do
  if e.hasLooseBVars then return false
  withReducible (isDefEq e x)

/-- Is `nx` (the new value of `x` in an iteration that goes on) strictly smaller than `x`,
    given `x > 0`: `x - k` (`k ≥ 1`), `x / k` (`k ≥ 2`), `x.pred`? -/
def decreases (nx x : Expr) : MetaM Bool := do
  let nx := nx.consumeMData
  if nx.hasLooseBVars then return false
  let args := nx.getAppArgs
  let litGe (e : Expr) (k : Nat) : MetaM Bool := do return ((← natLit? e).getD 0) ≥ k
  match nx.getAppFn.constName?, args.size with
  | some ``HSub.hSub, 6 => sameAs args[4]! x <&&> litGe args[5]! 1
  | some ``Nat.sub, 2 => sameAs args[0]! x <&&> litGe args[1]! 1
  | some ``HDiv.hDiv, 6 => sameAs args[4]! x <&&> litGe args[5]! 2
  | some ``Nat.div, 2 => sameAs args[0]! x <&&> litGe args[1]! 2
  | some ``Nat.pred, 1 => sameAs args[0]! x
  | _, _ => return false

/-- Is `nx` strictly larger than `x`: `x + k`, `k + x` (`k ≥ 1`), `x.succ`? -/
def increases (nx x : Expr) : MetaM Bool := do
  let nx := nx.consumeMData
  if nx.hasLooseBVars then return false
  let args := nx.getAppArgs
  let litGe (e : Expr) (k : Nat) : MetaM Bool := do return ((← natLit? e).getD 0) ≥ k
  match nx.getAppFn.constName?, args.size with
  | some ``HAdd.hAdd, 6 =>
      (sameAs args[4]! x <&&> litGe args[5]! 1) <||> (sameAs args[5]! x <&&> litGe args[4]! 1)
  | some ``Nat.add, 2 =>
      (sameAs args[0]! x <&&> litGe args[1]! 1) <||> (sameAs args[1]! x <&&> litGe args[0]! 1)
  | some ``Nat.succ, 1 => sameAs args[0]! x
  | _, _ => return false

/-- The number of steps of a bounded loop that computes the same final state as the `while`
    loop of state type `β`, initial state `init` and step `f` (`f () s : Id (ForInStep β)`),
    when the loop is structurally terminating in the sense of the module doc; `none`
    otherwise. -/
def whileBound? (β init f : Expr) : MetaM (Option Expr) := do
  withLocalDeclD `s β fun r => do
    let body ← zetaAll (← instantiateMVars (mkApp2 f (mkConst ``Unit.unit) r).headBeta)
    let body := body.consumeMData
    unless body.isAppOfArity ``ite 5 do return none
    let yieldsElse := collectYields (body.getArg! 4)
    unless yieldsElse.isEmpty do return none
    let yields := collectYields (body.getArg! 3)
    let nat := mkConst ``Nat
    for g in ← guardCands (body.getArg! 1) do
      match g with
      | .pos x =>
          unless ← isDefEq (← inferType x) nat do continue
          let some p := statePath? r x | continue
          let ok ← yields.allM fun v => do
            let some nx := componentAt? v p | return false
            decreases nx x
          unless ok do continue
          let x₀ ← componentOf init p
          return some (← mkAppM ``HAdd.hAdd #[x₀, mkNatLit 1])
      | .lt x b le =>
          unless ← isDefEq (← inferType x) nat do continue
          let some p := statePath? r x | continue
          -- the bound does not change in the loop
          let b₀? ← if !b.containsFVar r.fvarId! then pure (some b)
            else match statePath? r b with
              | some pb =>
                  if pb == p then pure none else
                  let same ← yields.allM fun v => do
                    let some nb := componentAt? v pb | return false
                    sameAs nb b
                  if same then some <$> componentOf init pb else pure none
              | none => pure none
          let some b₀ := b₀? | continue
          let ok ← yields.allM fun v => do
            let some nx := componentAt? v p | return false
            increases nx x
          unless ok do continue
          let x₀ ← componentOf init p
          let top ← if le then mkAppM ``HAdd.hAdd #[b₀, mkNatLit 1] else pure b₀
          return some (← mkAppM ``HAdd.hAdd #[← mkAppM ``HSub.hSub #[top, x₀], mkNatLit 1])
    return none

end LeanScript.Gen

end
