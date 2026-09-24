module

public meta import LeanScript.ToTerm.TransRec

@[expose] public section

meta section

/-!
# The translation: structural recursion

`transBrecOn`, the clause of the translation for a structural recursion as Lean compiled
it.  Like the clauses of `LeanScript.ToTerm.TransRec`, it takes the translation itself as
its first argument `trans`.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-- A structural recursion as Lean compiled it: `Nat.brecOn` or `List.brecOn`.

    The branch of a `brecOn` is given the **history** of the recursion — the value of the
    function at every smaller argument — and the grammar's folds give it the value at the
    immediate predecessor only.  So the history is reduced away here: the branch is
    instantiated at the two constructors of its type, with the head of the history
    replaced by a variable standing for the value at the predecessor, and what is left is
    the pair of branches of `Nat.rec` / `List.rec`, which
    `LeanScript.ToTerm.transRecCore` turns into `nat_rec` / `recTaggedUnion_rec` (or the
    case analysis, when the branch does not use that value).

    On a `Nat` the depth is not fixed at one.  If the branch at `n + 1` reads more of the
    history than its head, the depths `1, 2, …` are tried in turn: at depth `k` the
    branch is instantiated at `n + k + 1` with the `k + 1` nearest entries of the history
    replaced by variables, and the first depth at which nothing of the history is left is
    the depth of the `nat_rec` that is built — with the answers below it, the branch at
    `0, …, k`, as its base values.  A recursion that reads the history at an argument
    that is not a fixed number of steps back is refused. -/
def transBrecOn (trans : TransFn) (c : TCtx) (e : Expr) (n : Name) (lvls : List Level)
    (args : Array Expr) : MetaM Expr := do
  let isNat := n == ``Nat.brecOn
  let mIdx := if isNat then 0 else 1
  let arity := mIdx + 3
  if args.size < arity then
    return ← trans c (← etaExpand e)
  let motive ← whnf args[mIdx]!
  unless motive.isLambda do
    throwError "`#leanscript_to_term`: the motive of {n} is not a function"
  let major := args[mIdx + 1]!
  let brecF := args[mIdx + 2]!
  let τLean ← lambdaBoundedTelescope motive 1 fun xs body => do
    let body ← whnf body
    if body.containsFVar xs[0]!.fvarId! then
      throwError "`#leanscript_to_term`: {n} is used with a dependent motive, which the \
        language has no eliminator for"
    return body
  let τ ← tyOfType τLean
  let brecFTy ← inferType brecF
  -- the type of the history at a given argument
  let historyTy (t : Expr) : MetaM Expr := do
    return (← whnf (← instantiateForall brecFTy #[t])).bindingDomain!
  -- the branch at a constructor, with the head of the history read as `ih`
  let branchAt (scrutinee : Expr) (ih? : Option Expr) : MetaM Expr := do
    let ht ← historyTy scrutinee
    withLocalDeclD `history ht fun hist => do
      let body ← reduceBrecBodyDeep (mkApp2 brecF scrutinee hist)
      let body := match ih? with
        | some ih => substHistoryHead body hist.fvarId! ih
        | none => body
      if body.containsFVar hist.fvarId! then
        throwError "`#leanscript_to_term`: this recursion reads the value of the \
          function at an argument that is not the immediate predecessor, and the \
          grammar's folds descend one step at a time"
      return body
  -- what to do with the arguments a saturated `brecOn` is applied to on top of its own
  let finish (core : Expr) : MetaM Expr := do
    let extra := args.extract arity args.size
    if extra.isEmpty then return core
    applyArgs trans c core (mkAppN (mkConst n lvls) (args.extract 0 arity)) extra
  if isNat then
    -- one step first: that is `Nat.rec`, and `transRecCore` may still turn it into the
    -- case analysis when the branch does not use the value of the fold
    let depth0? : Option (Array Expr) ←
      try
        let z ← branchAt (mkConst ``Nat.zero) none
        let s ← withLocalDeclD `n (mkConst ``Nat) fun nv =>
          withLocalDeclD `ih τLean fun ih => do
            let body ← branchAt (mkApp (mkConst ``Nat.succ) nv) (some ih)
            mkLambdaFVars #[nv, ih] body
        pure (some #[z, s])
      catch _ => pure none
    if let some minors := depth0? then
      let some (.recInfo ri) := (← getEnv).find? ``Nat.rec
        | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
      return ← finish (← transRecCore trans c ri τ minors major)
    -- more than one step: the branch at `n + k + 1`, with the `k + 1` nearest answers
    -- read out of the history and bound as `ih₀, …, ihₖ` — nearest first
    let stepAt (k : Nat) : MetaM Expr :=
      withLocalDeclD `n (mkConst ``Nat) fun nv => do
        let mut scrutE := nv
        for _ in [0:k + 1] do scrutE := mkApp (mkConst ``Nat.succ) scrutE
        let ihDecls : Array (Name × (Array Expr → MetaM Expr)) :=
          (Array.range (k + 1)).map fun i =>
            (Name.mkSimple s!"ih{i}", fun _ => pure τLean)
        withLocalDeclsD ihDecls fun ihs => do
          let ht ← historyTy scrutE
          withLocalDeclD `history ht fun hist => do
            let body ← reduceBrecBodyDeep (mkApp2 brecF scrutE hist)
            let body := substHistory body hist.fvarId! ihs
            if body.containsFVar hist.fvarId! then
              throwError "`#leanscript_to_term`: this recursion reads the value of the \
                function at an argument that is not one of its {k + 1} nearest \
                predecessors"
            mkLambdaFVars (#[nv] ++ ihs) body
    let mut found : Option (Nat × Expr) := none
    for k in [1:maxNatRecDepth + 1] do
      if found.isNone then
        found ← try pure (some (k, ← stepAt k)) catch _ => pure none
    let some (k, s) := found
      | throwError "`#leanscript_to_term`: this recursion does not descend by a fixed \
          number of steps — the fold of a natural number the grammar has gives its branch \
          the answers at the `k + 1` nearest predecessors, so a call at an argument such \
          as `n / 2` has no term"
    -- the answers below the depth: the branch at `0, …, k`, each one allowed to read the
    -- answers already known
    let mut baseVals : Array Expr := #[]
    for j in [0:k + 1] do
      let mut jE : Expr := mkConst ``Nat.zero
      for _ in [0:j] do jE := mkApp (mkConst ``Nat.succ) jE
      let ht ← historyTy jE
      let v ← withLocalDeclD `history ht fun hist => do
        let body ← reduceBrecBodyDeep (mkApp2 brecF jE hist)
        let body := substHistory body hist.fvarId! baseVals.reverse
        if body.containsFVar hist.fvarId! then
          throwError "`#leanscript_to_term`: the answer at {j} reads the value of the \
            function at an argument the fold has not computed yet"
        pure body
      baseVals := baseVals.push v
    let scrutT ← trans c major
    let natTy ← tyOfType (mkConst ``Nat)
    -- the base values are written nearest first: `(f k, …, f 1, f 0)`
    let baseTerms ← baseVals.reverse.mapM fun v => trans c v
    let base := mkNatRecBase c τ baseTerms
    let core ← lambdaBoundedTelescope s (k + 2) fun xs body => do
      let c' := c.pushFields
        (#[(xs[0]!.fvarId!, natTy)] ++ (xs.extract 1 xs.size).map fun x => (x.fvarId!, τ))
      return mkAppN (mkConst ``LeanScript.Term.nat_rec)
        #[c.sg, c.gamma, τ, mkNatLit k, scrutT, base, ← trans c' body]
    return ← finish core
  let minors ←
    do
      let α := args[0]!
      let listTy := mkApp (mkConst ``List [← getDecLevel α]) α
      let nil := mkApp (mkConst ``List.nil [← getDecLevel α]) α
      let z ← branchAt nil none
      let s ← withLocalDeclD `head α fun hd =>
        withLocalDeclD `tail listTy fun tl =>
          withLocalDeclD `ih τLean fun ih => do
            let cons := mkApp3 (mkConst ``List.cons [← getDecLevel α]) α hd tl
            let body ← branchAt cons (some ih)
            mkLambdaFVars #[hd, tl, ih] body
      pure #[z, s]
  let some (.recInfo ri) := (← getEnv).find? ``List.rec
    | throwError "`#leanscript_to_term`: internal: no recursor for {n}"
  finish (← transRecCore trans c ri τ minors major)

end LeanScript.ToTerm

end

end
