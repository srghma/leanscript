module

public meta import LeanScript.ToTerm.Trans
public import LeanScript.CtorFn

@[expose] public section

meta section

/-!
# The elaborator

`#leanscript_to_term`, and the two commands that report on and empty its cache.  This is
the module to import to use the translation.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The elaborator -/

/-- The empty signature, as an expression. -/
def emptySigE : Expr :=
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``LeanScript.GlobalDecl)
  mkApp2 (mkConst ``LeanScript.Sig.mk) nil
    (mkApp2 (mkConst ``rfl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- The signature and the context the expected type asks for. -/
def sigAndCtxOf? (expected? : Option Expr) : MetaM (Expr × Expr) := do
  match expected? with
  | none => return (emptySigE, nilCtxE)
  | some t =>
    match (← whnf (← instantiateMVars t)).getAppFnArgs with
    | (``LeanScript.Term, #[sg, γ, _, _, _]) => return (sg, γ)
    | _ => return (emptySigE, nilCtxE)

/-- Translate `e` — the value of a definition, or an expression written out. -/
def translate (sg base : Expr) (e : Expr) : MetaM Expr := do
  let globals ← parseSig sg
  let c : TCtx := { sg := sg, globals := globals, base := base }
  match e with
  | .const n lvls =>
      checkConst n
      let info ← getConstInfo n
      let some val := info.value?
        | throwError "`#leanscript_to_term`: `{n}` has no definition to translate"
      transClosedCached trans c (val.instantiateLevelParams info.levelParams lvls)
  | _ => trans c e

/-- `#leanscript_to_term e`: the `LeanScript.Term` that means what the Lean definition
    `e` means.  See this module's header.

    The signature the translation resolves top-level names against is the one of the
    expected type; `#leanscript_to_term (sig := s) e` names it instead, which is what
    lets the type of the translation be *inferred* rather than written out. -/
syntax (name := leanscriptToTerm) "#leanscript_to_term " ("(" &"sig" " := " term ")")?
  term : term

@[term_elab leanscriptToTerm]
def elabLeanscriptToTerm : TermElab := fun stx expected? => do
  let sigStx := stx[1]
  let arg := stx[2]
  let e ← instantiateMVars (← elabTerm arg none)
  let (sgOfExpected, base) ← sigAndCtxOf? expected?
  let sg ← if sigStx.isNone then pure sgOfExpected else
    instantiateMVars (← elabTerm sigStx[3] (mkConst ``LeanScript.Sig))
  let t ← translate sg base e
  match expected? with
  | some ty => Term.ensureHasType ty t
  | none => return t

/-! ## Optimizing a term written by hand

The grammar rejects a redex written by hand: `.extern (.lean_string_data__String_toList
"ab")` does not elaborate, because the value of the call can be written as a term (the
list `['a', 'b']`), and `Term.extern` demands `TyWf.quotable τ = false`.  A constructor
of an inductive can only *check* a side condition; it cannot replace itself by the value.
`#leanscript_optimize t` is the smart constructor that does: `t` is written with the
constructors of the grammar as usual, the side conditions it does not meet are set
aside, and the term is rebuilt from the leaves up through the translation's own
constructor (`mkNode`), which reduces every redex it meets — an extern on values is its
value, a closed computation is its value, a β-redex is reduced, … — and proves the side
conditions of what is left.  If something other than a side condition is wrong with `t`
(or a redex is left that nothing reduces), the errors of `t` are reported as usual. -/

/-- Rebuild the term `t` bottom-up through `mkNode`: the indices and the proofs about them
    are dropped and recomputed, and every node that is a redex is reduced. -/
partial def optimizeTerm (t : Expr) : MetaM Expr := do
  let t ← instantiateMVars t
  let fn := t.getAppFn
  let some ctor := fn.constName? | return t
  let some (.ctorInfo ci) := (← getEnv).find? ctor | return t
  unless isGrammarFamily ci.induct do return t
  let args := t.getAppArgs
  unless args.size == ci.numParams + ci.numFields do return t
  let info ← ctorInfo ctor
  let mut out := args.extract 0 ci.numParams
  for i in [0:info.roles.size] do
    let a := args[ci.numParams + i]!
    match info.roles[i]! with
    | .index | .indexProof => pure ()
    | .child => out := out.push (← optimizeTerm a)
    | _ => out := out.push a
  mkNode ctor out

/-- `#leanscript_optimize t`: the term `t`, written with the constructors of the grammar,
    with its redexes reduced.  See the section header. -/
syntax (name := leanscriptOptimize) "#leanscript_optimize " term : term

/-- The expected type with its grade vector and head left open: reducing a redex changes
    both (an extern that answers with a list is a computation; its value is a literal). -/
def openIndices (expected? : Option Expr) : MetaM (Option Expr) := do
  let some t := expected? | return none
  match (← whnf (← instantiateMVars t)).getAppFnArgs with
  | (``LeanScript.Term, #[sg, γ, _, τ, _]) =>
      let u ← mkFreshExprMVar (mkApp (mkConst ``LeanScript.Usage) γ)
      let k ← mkFreshExprMVar (mkConst ``LeanScript.Head)
      return some (mkAppN (mkConst ``LeanScript.Term) #[sg, γ, u, τ, k])
  | _ => return expected?

@[term_elab leanscriptOptimize]
def elabLeanscriptOptimize : TermElab := fun stx expected? => do
  let before ← Core.getMessageLog
  let e ← withSynthesize (elabTerm stx[1] (← openIndices expected?))
  let e ← instantiateMVars e
  let written ← Core.getMessageLog
  -- the side conditions `t` does not meet are rebuilt, so their errors are set aside
  Core.setMessageLog before
  let t ← try
      let t ← instantiateMVars (← optimizeTerm e)
      unless t.hasSorry || t.hasExprMVar do Meta.check t
      pure t
    catch ex =>
      Core.setMessageLog written
      throw ex
  if t.hasSorry || t.hasExprMVar then
    -- something other than a side condition is wrong: report `t` as written
    Core.setMessageLog written
    return e
  match expected? with
  | some ty => Term.ensureHasType ty t
  | none => return t

/-- `#leanscript_to_term_cache_stats`: how many definitions the translation cache holds,
    how often one was reused, and how often two definitions turned out to have the same
    shape and were merged into one tree. -/
syntax (name := toTermCacheStats) "#leanscript_to_term_cache_stats" : command

@[command_elab toTermCacheStats]
def elabToTermCacheStats : Command.CommandElab := fun _ => do
  let st ← cacheRef.get
  logInfo m!"entries: {st.entries.size}, hits: {st.hits}, shape merges: {st.shared}"

/-- `#leanscript_to_term_cache_clear`: empty the translation cache. -/
syntax (name := toTermCacheClear) "#leanscript_to_term_cache_clear" : command

@[command_elab toTermCacheClear]
def elabToTermCacheClear : Command.CommandElab := fun _ => cacheRef.set {}

end LeanScript.ToTerm

end

end
