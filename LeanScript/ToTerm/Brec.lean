module

public meta import LeanScript.ToTerm.Match

@[expose] public section

meta section

/-!
# The compiled form of a structural recursion

Reducing a `brecOn` body far enough to see the branch it takes, and reading the values of
the recursion at the previous arguments out of the history it is given.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The compiled form of a structural recursion

Lean compiles a structurally recursive definition into `X.brecOn`, which hands the branch
the whole **history** of the recursion — the value of the function at every smaller
argument — while the grammar's folds hand the branch a fixed number of the nearest
answers (`LeanScript.Term.nat_rec k`, `LeanScript.Term.recTaggedUnion_rec`).  So a
`brecOn` is translated by *reducing the history away*: the branch is instantiated at a
history whose nearest entries are variables standing for those answers, and the
translation succeeds exactly when nothing else of the history is read. -/

/-- Reduce an application far enough to see the branch it takes: beta, `match`, `casesOn`
    and the auxiliary the compiler names `_f`, and **nothing else** — a call the
    translation has to see is left standing. -/
def isBrecAux (n : Name) : Bool :=
  let s := n.getString!
  s == "_f" || s.startsWith "match_" || s == "casesOn" || s == "brecOn" || s == "_unary"

/-- `whnfCore`, unfolding the auxiliaries of a compiled recursion on the way. -/
partial def reduceBrecBody (e : Expr) : MetaM Expr := do
  let e ← whnfCore e
  match e.getAppFn with
  | .const n _ =>
      if isBrecAux n then
        match ← withTransparency .all (unfoldDefinition? e) with
        | some e' => reduceBrecBody e'
        | none => return e
      else return e
  | _ => return e

/-- `reduceBrecBody`, continued **under the binders** the branch opens.  A recursion that
    takes more than one argument is compiled with the later arguments in the motive, so
    its branch is a function and the `match` that reads the history sits under a lambda;
    reducing there is what lets an accumulator-passing loop be seen as a fold. -/
partial def reduceBrecBodyDeep (e : Expr) : MetaM Expr := do
  let e ← reduceBrecBody e
  match e with
  | .lam .. =>
      lambdaBoundedTelescope e 1 fun xs b => do
        mkLambdaFVars xs (← reduceBrecBodyDeep b)
  | _ => return e

/-- How deep a recursion on a natural number the translation looks for: `fib` descends
    two steps, the hexanacci numbers six, and a definition that descends more steps than
    this is refused rather than searched for indefinitely. -/
def maxNatRecDepth : Nat := 16

/-- One component of a `PProd`, however it is written: `(0, x)` for the first component
    of `x` and `(1, x)` for the second, whether it is a projection or an application of
    `PProd.fst` / `PProd.snd`. -/
def pprodProj? (e : Expr) : Option (Nat × Expr) :=
  match e.consumeMData with
  | .proj ``PProd i x => some (i, x)
  | e' =>
      match e'.getAppFnArgs with
      | (``PProd.fst, #[_, _, x]) => some (0, x)
      | (``PProd.snd, #[_, _, x]) => some (1, x)
      | _ => none

/-- The history `i` steps back: `hist` itself is `0`, and `t.2` is one step further than
    `t`, since `below (n + 1)` is `motive n ×' below n`. -/
partial def histTail? (hist : FVarId) (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .fvar f => if f == hist then some 0 else none
  | e' =>
      match pprodProj? e' with
      | some (1, x) => (histTail? hist x).map (· + 1)
      | _ => none

/-- Which entry of the history does this expression read?  `hist.1` is the value at the
    immediate predecessor, `hist.2.1` the value one step further back, and so on. -/
def histEntry? (hist : FVarId) (e : Expr) : Option Nat :=
  match pprodProj? e with
  | some (0, x) => histTail? hist x
  | _ => none

/-- Read the values of the recursion at the nearest predecessors out of the history:
    entry `i` becomes `ihs[i]`.  Whatever still mentions the history afterwards is a read
    the fold that is being built cannot serve. -/
def substHistory (e : Expr) (hist : FVarId) (ihs : Array Expr) : Expr :=
  e.replace fun s =>
    match histEntry? hist s with
    | some i => ihs[i]?
    | none => none

/-- Read the value of the recursion at the immediate predecessor out of the history:
    `history.1` becomes the variable that stands for it.  Whatever is left of the history
    afterwards is a deeper call, which a one-step fold cannot express. -/
def substHistoryHead (e : Expr) (hist : FVarId) (ih : Expr) : Expr :=
  substHistory e hist #[ih]

end LeanScript.ToTerm

end

end
