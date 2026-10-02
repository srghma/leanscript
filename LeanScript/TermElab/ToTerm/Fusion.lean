module

public meta import LeanScript.TermElab.ToTerm.Basic

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_to_term`: inlining combinators, and fusing a `foldr` into an array

Rewrites of Lean expressions that the expression translator (`LeanScript.TermElab.ToTerm.Expr`)
makes before it translates them.  They remove the values the language cannot write: a
structure of a polymorphic function (a Church-encoded fold, `structure Fold α where run :
{r : Type} → (α → r → r) → r → r`, of type `Type 1`), and a list built by `List.cons` that
is converted to an array at once.  `Tests/SnapshotsPBOPure/Fusion01.lean` is the example.

* **Inlining at the head** (`headNorm`): the head of an expression is reduced as far as
  helper definitions of the program allow: a helper that is not recursive (`mapF`,
  `filterMapF`, `fromArray`, `toArray`, …) is unfolded, a projection of a constructor
  application (`(Fold.mk g).run` is `g`, also when the structure is a call of a helper that
  unfolds to a constructor application) is the field, `flip`, `Function.comp`, `id` and
  `Function.const` are unfolded, and β-redexes are reduced.  The translator uses it when a
  helper cannot be translated on its own (its type is a type parameter, a structure in `Type
  1`, …: `trApp`) and on a projection whose structure is not a constructor application.

* **`foldr`/`toArray` fusion** (`fuseToArrayFoldr?`): `List.toArray (Array.foldr f [] xs)`,
  where `f a acc` only puts elements in front of `acc` (`b :: acc`, `acc`, or a choice of
  these by `if`/`match`/`let`, with `acc` used nowhere else), is
  `Array.foldl (fun acc' a => f' a acc') #[] xs`, where `f'` pushes the same elements, in the
  same order, onto the array `acc'` (`acc'.push b`, `acc'`).  Both build the array of the
  elements that `f` puts in front, `xs` read from the left: `foldr` puts the elements of the
  last element of `xs` in front first, and the list is read from its head.  The fold over the
  array is a loop of the language (`Comp.array_foldl`), the push is in place (the
  accumulator is owned), and no list is built.

* **Strings** (`stringRewrite?`): `s.startsWith p` for a string pattern `p` is the extern
  `String.Internal.isPrefixOf p s`, and `(s.drop n).toString` (`String.Slice.toString` of
  `String.drop`) is the extern `String.Internal.drop s n` (and `dropEnd`/`dropRight` likewise):
  the slice of the new string API is a leaf of the language with no operations, while these
  externs are its old functions on strings, with the same value.

None of this is checked by Lean (the translator is not verified); the differential checks of
`leanscript --check` compare the JavaScript with Lean.
-/

open Lean Meta Elab Term

namespace LeanScript.Gen

/-- Is `c` a definition of the program (not of the library) that is not recursive, so that it
    can be unfolded where it is used? -/
def isInlinableHelper (c : Name) : MetaM Bool := do
  if ← isLibraryDecl c then return false
  let env ← getEnv
  let some (.defnInfo info) := env.find? c | return false
  if (Elab.Structural.eqnInfoExt.find? env c).isSome then return false
  if (Elab.WF.eqnInfoExt.find? env c).isSome then return false
  if (info.value.find? (·.isConstOf c)).isSome then return false
  -- a match compiled to an auxiliary definition is translated as a match, not unfolded here
  if ← isMatcher c then return false
  return true

/-- The library combinators unfolded at the head by `headNorm`. -/
def headInlineLib : List Name := [``flip, ``Function.comp, ``id, ``Function.const]

/-- Is `c` the projection function of a field of a structure that is not a class? -/
def isStructProjFn (c : Name) : MetaM Bool := do
  match ← getProjectionFnInfo? c with
  | some info => return !info.fromClass
  | none => return false

/-- The expression `e` with its head reduced as far as helpers of the program allow (see the
    module doc): helpers unfolded, projections of constructor applications reduced, the
    combinators of `headInlineLib` unfolded, β-redexes reduced. -/
partial def headNorm (e : Expr) : MetaM Expr := do
  let e ← whnfCore (← instantiateMVars e)
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .proj _ i s =>
    let s' ← headNorm s
    if let .const c _ := s'.getAppFn then
      if let some (.ctorInfo cinfo) := (← getEnv).find? c then
        if s'.getAppNumArgs == cinfo.numParams + cinfo.numFields then
          return ← headNorm (mkAppN s'.getAppArgs[cinfo.numParams + i]! args)
    return e
  | .const c _ =>
    if (← isInlinableHelper c) || headInlineLib.contains c || (← isStructProjFn c) then
      if let some e' ← unfoldDefinition? e then return ← headNorm e'
    return e
  | _ => return e

/-- A projection `s.i a₁ …` whose structure `s` reduces by `headNorm` to a constructor
    application: the field applied to the arguments, its head reduced; `none` otherwise. -/
def projByInlining? (e : Expr) : MetaM (Option Expr) := do
  unless e.getAppFn.isProj do return none
  let e' ← headNorm e
  if e'.getAppFn.isProj then return none
  return some e'

/-! ## `foldr`/`toArray` fusion -/

/-- The body `e : List β` of the step of a `foldr` with accumulator `acc`, rewritten to push
    the elements it puts in front of `acc` onto the array `accE : Array β` (see the module
    doc); `none` when `e` is not of that shape. -/
partial def pushOnto (acc : Expr) (β : Expr) (accE : Expr) (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  if e == acc then return some accE
  if !e.containsFVar acc.fvarId! then return none
  let arrTy ← mkAppM ``Array #[β]
  match e with
  | .mdata _ b => pushOnto acc β accE b
  | .letE n t v b _ =>
    if v.containsFVar acc.fvarId! then return none
    withLetDecl n t v fun x => do
      let some b' ← pushOnto acc β accE (b.instantiate1 x) | return none
      return some (← mkLetFVars #[x] b')
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if e.isAppOfArity ``List.cons 3 then
      let x := args[1]!
      if x.containsFVar acc.fvarId! then return none
      return ← pushOnto acc β (← mkAppM ``Array.push #[accE, x]) args[2]!
    if e.isAppOfArity ``ite 5 then
      if args[1]!.containsFVar acc.fvarId! then return none
      let some t ← pushOnto acc β accE args[3]! | return none
      let some f ← pushOnto acc β accE args[4]! | return none
      return some (mkAppN (mkConst ``ite fn.constLevels!) #[arrTy, args[1]!, args[2]!, t, f])
    if e.isAppOfArity ``cond 4 then
      if args[1]!.containsFVar acc.fvarId! then return none
      let some t ← pushOnto acc β accE args[2]! | return none
      let some f ← pushOnto acc β accE args[3]! | return none
      return some (mkAppN (mkConst ``cond fn.constLevels!) #[arrTy, args[1]!, t, f])
    if e.isAppOfArity ``dite 5 then
      if args[1]!.containsFVar acc.fvarId! then return none
      let br (k : Expr) : MetaM (Option Expr) := do
        let .lam n d b bi := k | return none
        withLocalDecl n bi d fun h => do
          let some b' ← pushOnto acc β accE (b.instantiate1 h) | return none
          return some (← mkLambdaFVars #[h] b')
      let some t ← br args[3]! | return none
      let some f ← br args[4]! | return none
      return some (mkAppN (mkConst ``dite fn.constLevels!) #[arrTy, args[1]!, args[2]!, t, f])
    if let some m ← matchMatcherApp? e then
      unless m.remaining.isEmpty do return none
      if m.discrs.any (·.containsFVar acc.fvarId!) then return none
      if m.params.any (·.containsFVar acc.fvarId!) then return none
      -- a motive that does not depend on the discriminants: `fun _ => List β`
      let some motive' ← lambdaTelescope m.motive fun xs b => do
          if xs.size != m.discrs.size then return none
          if b.hasAnyFVar (xs.contains <| .fvar ·) then return none
          return some (← mkLambdaFVars xs arrTy)
        | return none
      let mut alts : Array Expr := #[]
      for alt in m.alts do
        let some alt' ← lambdaTelescope alt fun ys b => do
            let some b' ← pushOnto acc β accE b | return none
            return some (← mkLambdaFVars ys b')
          | return none
        alts := alts.push alt'
      return some { m with motive := motive', alts }.toExpr
    return none

/-- `List.toArray l` for `l = Array.foldr f [] xs` (from `xs.size` down to `0`, after
    `headNorm`) whose step only puts elements in front of its accumulator: the
    `Array.foldl` that pushes them (see the module doc). -/
def fuseToArrayFoldr? (l : Expr) : MetaM (Option Expr) := do
  let l ← headNorm l
  unless l.isAppOfArity ``Array.foldr 7 do return none
  let args := l.getAppArgs
  let α := args[0]!
  let f := args[2]!
  let xs := args[4]!
  unless (← whnfR args[3]!).isAppOf ``List.nil do return none
  let lt ← whnf (← inferType l)
  unless lt.isAppOfArity ``List 1 do return none
  let β := lt.appArg!
  unless ← isDefEq args[5]! (← mkAppM ``Array.size #[xs]) do return none
  unless (← Meta.evalNat args[6]!) == some 0 do return none
  let arrTy ← mkAppM ``Array #[β]
  let listTy ← mkAppM ``List #[β]
  withLocalDeclD `acc arrTy fun acc' => withLocalDeclD `a α fun a =>
    withLocalDeclD `acc listTy fun acc => do
      let body ← Core.betaReduce (mkApp2 f a acc)
      let some body' ← pushOnto acc β acc' body | return none
      let step ← mkLambdaFVars #[acc', a] body'
      let init ← mkAppOptM ``Array.empty #[β]
      let size ← mkAppM ``Array.size #[xs]
      return some (← mkAppOptM ``Array.foldl
        #[α, arrTy, step, init, xs, some (mkNatLit 0), some size])

/-! ## Strings -/

/-- The externs of the old string API for the functions of the new one that go through a
    slice, a leaf of the language (see the module doc). -/
def stringRewrite? (e : Expr) : MetaM (Option Expr) := do
  let e ← instantiateMVars e
  let args := e.getAppArgs
  -- `s.startsWith p` for a string `p`
  if e.isAppOfArity ``String.startsWith 4 then
    if ← isDefEq args[0]! (mkConst ``String) then
      return some (mkApp2 (mkConst ``String.Internal.isPrefixOf) args[2]! args[1]!)
  -- `(s.drop n).toString`, `(s.dropEnd n).toString`
  if e.isAppOfArity ``String.Slice.toString 1 then
    let sl ← instantiateMVars args[0]!
    if sl.isAppOfArity ``String.drop 2 then
      return some (mkApp2 (mkConst ``String.Internal.drop) sl.appFn!.appArg! sl.appArg!)
    if sl.isAppOfArity ``String.dropEnd 2 then
      return some (mkApp2 (mkConst ``String.Internal.dropRight) sl.appFn!.appArg! sl.appArg!)
  return none

end LeanScript.Gen

end
