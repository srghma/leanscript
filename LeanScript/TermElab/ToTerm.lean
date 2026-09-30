module

public meta import LeanScript.TermElab.ToTerm.Expr
public meta import Lean.Meta.Eqns

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term f`: a Lean definition as a `LeanScript.Term`

`#leanscript_to_term f` is a term: the translation of the Lean definition `f` to a closed
`LeanScript.Term`, of type `Term Δ [] τ` where `τ` is `#leanscript_get_ty` of the type of `f`.
Written as a command, it shows the type of the translation.  The translation is generic in
the signature (`{ks} {Δ : DSig ks}`) unless it uses a declared datatype, in which case it is a
term over the current program (`leanscript_signature`).

The definition is read through its unfolding equation (`f.eq_def`), so a definition by
structural recursion is read with its recursive calls in place, and `match` is read through
the `casesOn` it is compiled to.  The translation is written in direct style: it builds a
source tree (`LeanScript.Anf.Src`) that `LeanScript.Anf` then normalises into a normal-form
`Term` (closures and data literals named by `Term.letV`, every call with an open operand named
by a `Term.letE`, redexes on known values computed, a branch that is not in tail position
written with a join point, `Branch.join`/`Term.jump`).  In the table, each construct is
given with the constructor it becomes:

| Lean | `Term` |
| :-- | :-- |
| a parameter, a `let`, a `fun` | `Neu.var` (de Bruijn), `Term.letE`/`Term.letV`, `Val.lam` |
| a closed value of a leaf type (a literal) | `PExpr.lit` |
| `if c then t else e`, `cond`, `dite` (the proof unused) | `Branch.ite` of `decide c` |
| a call of a library function that is the Lean function of an entry of the catalogue of externs (`LeanInitPureExtern`, looked up in `ToTerm.ExternTable`), or `decide` of a relation decided by one (`Nat.decLt`) | the call of that extern, `Neu.extern` (a neutral pure expression: `n * 2` is `lean_nat_mul n 2`), on the terms of its value arguments (not types, proofs or `()`; an `[Inhabited α]` argument is passed as its default value); the type arguments of the entry are found by unification |
| a call of any other library function | its definition unfolded (an instance method, `a + b` to `Nat.add a b`; a definition in terms of other functions), then translated; refused if it cannot be unfolded |
| a call that takes a proof mentioning a local (`a[i]'h`, `UInt16.ofNatLT n h` under `if h : …`) | the same extern, the proof erased: the evaluator of the extern decides the proposition on the values of the arguments (`if h : n < UInt16.size then UInt16.ofNatLT n h else default`), and `a[i]'h` is read as `Array.get!Internal` (`lean_array_get`, which takes the default of the element type); the `default` is never reached from a program that had to prove the proposition |
| an `if` (or a `match` on `Bool`) that is an operand, whose branches are pure expressions | the pure conditional `Neu.cond`, with no join point |
| a constructor | `#leanscript_get_ctor` of it (and so `data_in` for a recursive type) |
| a constructor of a wrapper of one value besides proofs (`⟨i, h⟩ : Fin c.n`, `Subtype.mk`), also when its parameters mention locals | that value |
| a projection applied to arguments (`c.data i` for a function field) | `Comp.app` |
| a proof parameter of a function that is not recursive (`(h : Safe n)`; in particular of the open definitions `leanscript` builds for well-founded recursion) | nothing: it is erased, like the proofs of the body that mention it |
| a parameter that only names an index of a later parameter's type (`{n}` in `Vec.sum {n} (v : Vec Nat n)`) | nothing: indices are erased, so it is not a parameter of the translation (and cannot be used as a value) |
| a type parameter that only names the index of a type-indexed family (`{α}` in `Nest.length {α} (n : Nest α)`) | nothing: it is fixed to the index the family is read at (`Nest.Elem Nat`: the one the program declares, or `#leanscript_to_term f (α := Nat)`), so a recursive call at `α × α` is a call on the tail |
| a field of type `α` of a type-indexed family (`a` in `Nest.cons {α} a r`) | in a constructor application, the value put in the element type (`(2, 3)` is `Nest.Elem.node (leaf 2) (leaf 3)`); in a case analysis at an index other than the one read at (`Nest Nat`), refused if used |
| a value of a quotient `Quot r` / `Quotient s` (read as its carrier): `Quot.mk r a`, `⟦a⟧` | the representative `a` |
| `Quot.lift f h q`, `Quot.liftOn`, `Quot.rec`, `Quot.recOn`, `Quot.hrecOn`, `Quot.recOnSubsingleton`, `Quotient.lift`, `Quotient.lift₂`, … | `f` of the representative (`Term.letE` of `q` unless it is a `Quot.mk`) |
| a decision on a quotient (`decide (p = q)` by an instance built with `Quot.recOnSubsingleton`) | the decision of the instance at the representatives; a decision by cases (`if c then isTrue _ else isFalse _`) is the decision of `c` |
| a cast along an equation (`Eq.ndrec`, `cast`, …, from the `match` of an inductive family) | the value cast |
| a case analysis (`match`, `casesOn`) | `#leanscript_get_cases`' shape: `ite`, `enum_casesOn`, `letE`, `record_casesOn`, `union_casesOn`; after `data_out` for a recursive type; `nat_rec` for `Nat` |
| a projection of a structure | `record_casesOn` (or the value itself, for one field) |
| structural recursion on a `Nat` parameter | `Comp.nat_rec` |
| a recursion whose recursive calls change other parameters (an accumulator: `loop f (b + 1) acc = loop f b (f acc)`), or leave out trailing ones (`hyperTCO n a`, partially applied) | the fold answers a function of those parameters (`nat_rec`/`data_rec` applied to their current values); a recursive call applies the answer to its arguments there |
| a recursive call applied to more arguments than the parameters (`ack2 m n` for `ack2 : Nat → (Nat → Nat)`) | `Comp.app` of the answer |
| a call of a helper definition (not from `Init`/`Std`/`Lean`: `ackInner (ack2 m)`, `hyperLoop (hyperTCO n a) b x`, `hyperBase n a`) | the helper's own translation (a closed term), applied to the terms of the arguments; a helper calling back the function translated is refused |
| `Id.run x`, `pure x`, `x >>= f` in `Id` (a `do` block) | `x`, `x`, `Term.letE` |
| `for i in [a:b:s] do …` in `Id` (`forIn`/`forIn'` over a `Std.Legacy.Range`) | `Comp.nat_rec` on the number of iterations `(b - a + s - 1) / s`, at `i = a + k * s`, whose answer is a `ForInStep`: a `done` (`break`, `return`) is kept to the end, and the loop is the value in the final step |
| `while c do …` in `Id` (`forIn` over `Lean.Loop`), when its termination is read off its syntax (`LeanScript.TermElab.ToTerm.While`: the condition bounds a `Nat` variable that every iteration that goes on moves towards the bound by a literal step) | the same loop of `x₀ + 1` (counting down) or `b₀ - x₀ + 1` (counting up to `b`) steps, with no fuel (`LeanScript.boundedLoop_stable`); any other `while` is refused |
| structural recursion on a parameter of a declared datatype, by one function or by a `mutual` group of functions (one per member of the block: `Even.toNat`/`Odd.toNat`, `Rose.sum`/`Rose.sumList`) | `Comp.data_rec` of the whole block, one branch per member (a member no function recurses on gets a constant branch) |
| a recursive call on a member held in a function field (`(f 0).sum` in the branch of `node f`) | the answer next to the subvalue (`record_casesOn` of the applied field) |
| `Array.foldl step z xs` (from `0` to `xs.size`) over any other array | `Comp.array_foldl`, the step binding the element and the accumulator |
| `Array.foldl step z qs` over a field `qs` that holds members in an `Array` (also `Array (Array Q)`, `Nat → Array Q`) | `Comp.array_foldl` over the pairs of the subvalues and their answers; in `step`, a recursive call on the element is its answer |
| an array literal `#[a, b, …]` of values that are not leaves (`#[(none, 3)] : Array (Option T5 × Nat)`) | `PExpr.array_mk` |
| `Fin.foldl n f z` | `Comp.nat_rec` on `n`, whose step at `k` is `f acc ⟨k, _⟩` |
| a value `a : Fin m → T` of a field read as `Nat → Option T` (`finOptArrow`: `RoseF.node m a`) | `fun j => if j < m then some (a ⟨j, _⟩) else none` (`fun _ => none` for `m = 0`) |
| `f i` for such a field `f` of an opened constructor | `f i` taken apart after `data_out`: `some x` is `x`, the unreachable `none` is the `Inhabited` default of `T` |
| a recursive call on `f i` for such a field | the answer at the member `Option T`: `some` of the answer at `f i` (the fold's branch at `Option T` is generated), `none` the `Inhabited` default of the answer type |
| the same, with recursive calls on subvalues up to four levels down (`f (y :: t)`, `f t` in the branch of `_ :: y :: t`) | `Comp.data_brec` of the smallest depth that reaches them (for members used directly only) |

A recursive definition must recurse directly on one of its parameters, at the top of its
body (`f x = match x with …`); the other parameters may change (the answer of the fold is
then a function of them); in a branch the
parameter recursed on is the constructor application it was matched against.  The functions
of a `mutual` group all take the same parameters, except the one recursed on, which is a
different member of the block for each.  The recursion may be compiled by Lean as structural
or as well-founded (`qs.foldl (fun acc q => acc + q.sum) 0` is well-founded): the translator
reads the unfolding equations, and checks itself that every recursive call is on a subvalue.
A field that holds members inside an `Array` or a function holds, in the branch, the pairs
of the subvalues and their answers, so it can only be folded, applied, or passed to a
recursive call.

Everything else is refused with an error, in particular a type with one value or none
(`Unit`, `Empty`, …: as a parameter, a `let`, a field or a value), a type of two values
other than `Bool` (such a type *is* `bool`), a parameter that is a type or an instance,
mutual recursion through a helper, a recursive call that is not on a subvalue, a pattern on a numeral other than
`0`/`n + 1`, a call of a library function that is not the Lean function of an extern and cannot be
unfolded (`List.length`), and a call returning a quotient that does
not compute to `Quot.mk` (the language would need a representative).
-/

open Lean Meta Elab Term

namespace LeanScript.Gen

/-- The values of the parameters of a definition (its locals `xs`) that are the type index of
    a later parameter's type-indexed family (`α` in `Nest.size {α} (n : Nest α)`): the index
    the family is read at (`Nest.Elem Nat`), for the index given by name (`(α := Nat)`) or,
    when not given, the only one at which the program declares the family. -/
def typeIndexValues (f : Name) (xs : Array Expr) (idxParams : Array Nat)
    (named : Array (Ident × Lean.Term)) (prog? : Option ProgInfo) :
    TermElabM (Array (Option Expr)) := do
  let mut out : Array (Option Expr) := Array.replicate xs.size none
  let mut used : Array Name := #[]
  for i in idxParams do
    let x := xs[i]!
    unless (← whnf (← inferType x)).isSort do continue
    let n ← x.fvarId!.getUserName
    -- the binder's name in the type of `f` (the unfolding equation may rename it)
    let n' ← forallTelescope (← getConstInfo f).type fun ys _ =>
      if h : i < ys.size then ys[i].fvarId!.getUserName else pure n
    let shown := if n'.hasMacroScopes then n else n'
    -- the family it is the index of
    let mut fam? : Option (InductiveVal × Array Expr) := none
    for j in [i + 1:xs.size] do
      let t ← whnf (← instantiateMVars (← inferType xs[j]!))
      let some (c, _) := t.getAppFn.const? | continue
      let some (.inductInfo ind) := (← getEnv).find? c | continue
      unless ← typeIndexed ind do continue
      if t.getAppNumArgs == ind.numParams + 1 && t.appArg! == x then
        fam? := some (ind, t.getAppArgs[:ind.numParams].toArray)
        break
    let some (ind, ps) := fam? | fail m!"the parameter `{n}` of `{f}` is a type"
    if ps.any (·.hasFVar) then
      fail m!"the parameters of `{ind.name}` in the type of `{f}` are not closed"
    let v ← match named.find? (fun a => a.1.getId == n || a.1.getId == n') with
      | some (a, stx) =>
        used := used.push a.getId
        let T ← elabType stx
        synthesizeSyntheticMVarsNoPostponing
        pure (← normType (mkAppN (mkConst ind.name) (ps.push (← instantiateMVars T)))).appArg!
      | none =>
        let cands := (prog?.map (·.members.flatten) |>.getD #[]).filter fun m =>
          m.isAppOfArity ind.name (ind.numParams + 1) && m.getAppArgs[:ind.numParams].toArray == ps
        match cands with
        | #[m] => pure m.appArg!
        | _ => fail m!"`{f}` is generic in the type index `{shown}` of `{ind.name}`: give the index \
            as `#leanscript_to_term {f} ({shown} := …)`"
    out := out.set! i (some v)
  for (a, _) in named do
    unless used.contains a.getId do fail m!"`{f}` has no type index named `{a.getId}`"
  return out

/-- Instantiate the binders of a `∀` at the positions given a value. -/
partial def instBinders (e : Expr) (vals : Array (Option Expr)) : Expr :=
  go e 0
where
  go (e : Expr) (i : Nat) : Expr :=
    match e with
    | .forallE n d b bi =>
      match vals[i]?.join with
      | some v => go (b.instantiate1 v) (i + 1)
      | none => .forallE n d (go b (i + 1)) bi
    | e => e

/-- The translation of the definition `f`, elaborated against `expected?`; `named` gives the
    type indices it is generic in (`(α := Nat)`). -/
def translateDef (f : Name) (expected? : Option Expr) (named : Array (Ident × Lean.Term) := #[]) :
    TermElabM Expr := do
  let info ← getConstInfo f
  unless info.levelParams.isEmpty do fail m!"`{f}` is universe polymorphic"
  let some eqn ← getUnfoldEqnFor? f (nonRec := true)
    | fail m!"`{f}` is not a definition that can be unfolded"
  let prog? ← currentProg?
  let eqTy ← inferType (mkConst eqn)
  -- a type index a parameter's family is generic in is fixed first
  let (idxParams, vals) ← forallTelescope eqTy fun xs _ => do
    let idxParams ← indexParams xs
    return (idxParams, ← typeIndexValues f xs idxParams named prog?)
  let eqTy := instBinders eqTy vals
  let stx ← forallTelescope eqTy fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | fail m!"unexpected unfolding equation of `{f}`"
    let params := lhs.getAppArgs
    let given := (List.range params.size).toArray.filter (vals[·]!.isNone) |>.map (params[·]!)
    unless given == xs do
      fail m!"unexpected unfolding equation of `{f}`"
    let group ← mutualGroup f
    let recursive := group.any fun g => (rhs.find? (·.isConstOf g)).isSome
    let kept := (List.range params.size).toArray.filter (!idxParams.contains ·) |>.map (params[·]!)
    -- a parameter `_ : Unit` is a lazy delay of the rest of the function: no variable
    let units ← kept.mapM fun x => do isUnitType (← inferType x)
    if recursive && units.any id then
      fail m!"`{f}` is recursive and has a parameter of type `Unit`"
    -- a proof parameter of a function that is not recursive is erased (the proofs of its
    -- body, which alone can mention it, are erased too)
    let proofs ← if recursive then pure (kept.map fun _ => false) else kept.mapM fun x => isProof x
    let slotted := (List.range kept.size).toArray.filter (fun i => !units[i]! && !proofs[i]!)
      |>.map (kept[·]!)
    let dataKept := (List.range kept.size).toArray.filter (!proofs[·]!) |>.map (kept[·]!)
    let L : Loc := { slots := slotted.map (some ·.fvarId!), fns := if recursive then group else #[],
                     fn := f,
                     params, idxParams, prog?, c := prog?.map (·.members.size) |>.getD 0 }
    let go (L : Loc) : TM (Anf.Src × Lean.Term) := do
      for x in kept do
        if ← isUnitType (← inferType x) then continue
        if !recursive && (← isProof x) then continue
        if ← isType x then fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is a type"
        if (← isClass? (← inferType x)).isSome then
          fail m!"the parameter `{← x.fvarId!.getUserName}` of `{f}` is an instance"
        discard <| cirOf L (← inferType x)
      let mut body ← tr L rhs
      for i in (List.range kept.size).reverse do
        if proofs[i]! then continue
        if units[i]! then
          let rest ← mkForallFVars (kept[i+1:].toArray.filter (dataKept.contains ·)) (← inferType lhs)
          body ← delayCoerceTy L rest (← mkForallFVars #[kept[i]!] rest) body
        else body := Anf.Src.lam (some (← tyStx L (← inferType kept[i]!))) body
      -- the type of the translation: the parameters kept, then the result (an index
      -- parameter only occurs in indices, which are erased)
      let ty ← if idxParams.isEmpty && !proofs.any id then pure info.type
        else mkForallFVars dataKept (← inferType lhs)
      return (body, ← tyStx L ty)
    -- the depth of the course-of-values recursion: the first that works
    let mut res? := none
    let mut err? : Option Exception := none
    for d in [0:4] do
      if d > 0 && !recursive then break
      try
        res? := some (← (go { L with depth := d }).run { st := St.ofProg #[] prog? })
        break
      catch e => if err?.isNone then err? := some e
    let some ((src, ty), s) := res? | throw err?.get!
    -- the direct-style source, normalised to an A-normal statement
    let body ← src.toTerm
    match prog?, s.usesData with
    | some p, true => `(($body : LeanScript.Term $(mkIdent (p.name ++ `Δ)) 0 [] [] $ty [] none))
    | _, _ =>
      let d? ← match expected? with
        | some t =>
          let t ← whnfR (← instantiateMVars t)
          if t.isAppOfArity ``LeanScript.Term 8 then pure (some t.getAppArgs[1]!) else pure none
        | none => pure none
      match d? with
      | some d => `(($body : LeanScript.Term $(← exprToSyntax d) 0 [] [] $ty [] none))
      | none =>
        let ks := mkIdent `ks
        let d := mkIdent `Δ
        `(fun {$ks : List Nat} {$d : LeanScript.DSig $ks} =>
            ($body : LeanScript.Term $d 0 [] [] $ty [] none))
  let v ← elabTerm stx expected?
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars v

/-- `#leanscript_to_term f`: the translation of the Lean definition `f` to a closed
    `LeanScript.Term`. -/
syntax:max (name := leanscriptToTerm)
  "#leanscript_to_term " ident (ppSpace leanscriptNamedArg)* : term

/-- `#leanscript_to_term f`, as a command: show the type of the translation. -/
syntax (name := leanscriptToTermCmd)
  "#leanscript_to_term " ident (ppSpace leanscriptNamedArg)* : command

def resolveDef (id : Ident) : TermElabM Name :=
  try realizeGlobalConstNoOverloadWithInfo id
  catch _ => fail m!"unknown constant `{id.getId}`"

@[term_elab leanscriptToTerm]
def elabToTerm : TermElab := fun stx expected? => do
  translateDef (← resolveDef ⟨stx[1]⟩) expected? (namedArgs stx[2])

@[command_elab leanscriptToTermCmd]
def elabToTermCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let v ← translateDef (← resolveDef ⟨stx[1]⟩) none (namedArgs stx[2])
  logInfo m!"{stx[1]} : {← inferType v}"

end LeanScript.Gen

end
