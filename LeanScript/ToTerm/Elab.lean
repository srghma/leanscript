module

public meta import LeanScript.ToTerm.Trans

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
    | (``LeanScript.Term, #[sg, γ, _]) => return (sg, γ)
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
      transClosedCached c (val.instantiateLevelParams info.levelParams lvls)
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
  | some ty => ensureHasType ty t
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
