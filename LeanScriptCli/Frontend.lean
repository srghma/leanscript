import Lean
import LeanScript.TermElab.ToTerm
import LeanScript.Term.Syntax.Packed

/-!
# The front end of the `leanscript` tool: from a Lean file to closed `Term`s

`elabFile` elaborates a Lean file with the Lean front end (as `lean` does), importing, on
top of the file's own imports, the modules the translator needs.  An import the search path
cannot find is left out, with a warning, so an old file whose header names modules that no
longer exist still elaborates as far as it can.

`candidates` lists the definitions of the file the tool tries to translate: the public,
non-auxiliary, non-`partial`, computable definitions of values (not of types or
propositions), in the order of the file: structurally recursive ones and ones defined by
well-founded recursion alike.

A function defined by well-founded recursion (or a member of a `mutual` block, or a function
calling such functions) is translated through its **open definition** (`openDef`): the
right-hand side of its unfolding equation with every call of such a function `g` made a
call of a new parameter `g_rec`.  That definition is not recursive, so the translator reads it
like any other; the function is its fixed point (its unfolding equation), which is how the
JavaScript runs it (`LeanScriptCli.RecCalls`).

`translate` runs the translator (`LeanScript.Gen.translateDef`, the elaborator behind
`#leanscript_to_term`) on a definition, which reads its `Expr` (its unfolding equation, not
LCNF or IR, which have lost the types), computes the closed values of leaf type it embeds
(`reduceLits`), and **evaluates** the elaborated `Term` expression to a run-time value
(`Lean.Meta.evalExpr`), packed as a `LeanScript.ClosedTerm`.
-/

open Lean Elab Meta

namespace LeanScript.Cli

/-- The modules the translator needs in the environment of the file. -/
def extraImports : Array Import :=
  #[{ module := `LeanScript.TermElab.ToTerm, isMeta := true },
    { module := `LeanScript.Term.Syntax.Packed, isMeta := true },
    { module := `LeanScript.Term.Build, isMeta := true }]

/-- Set up the search path: `LEAN_PATH` (as set by `lake env`) if present, and the build
    directories of the project the executable belongs to. -/
def initPath : IO Unit := do
  let app ← IO.appPath
  -- `<root>/.lake/build/bin/leanscript`
  let root := (app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)).getD "."
  let mut sp : SearchPath := [root / ".lake" / "build" / "lib" / "lean"]
  let pkgDir := root / ".lake" / "packages"
  if ← pkgDir.isDir then
    for d in ← pkgDir.readDir do
      sp := sp ++ [d.path / ".lake" / "build" / "lib" / "lean"]
  initSearchPath (← findSysroot) sp

/-- The project root the executable belongs to. -/
def projectRoot : IO System.FilePath := do
  let app ← IO.appPath
  return (app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)).getD "."

/-- Does the search path have an `.olean` for the module? -/
def oleanExists (m : Name) : IO Bool := do
  let sp ← searchPathRef.get
  match ← sp.findWithExt "olean" m with
  | some p => p.pathExists
  | none => return false

/-- The result of elaborating a file. -/
structure Elaborated where
  /-- The environment after the last command. -/
  env : Environment
  /-- The messages (errors of the file included: they do not stop the tool). -/
  messages : MessageLog
  /-- The input context (for positions). -/
  inputCtx : Parser.InputContext
  /-- The imports of the header that could not be found. -/
  missing : Array Name

/-- The name the main module of an elaborated file gets. -/
def mainModuleName : Name := `LeanScriptInput

/-- Elaborate a Lean file. -/
def elabFile (file : System.FilePath) : IO Elaborated := do
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let imports := headerToImports header
  let mut kept : Array Import := #[]
  let mut missing : Array Name := #[]
  for i in imports do
    if ← oleanExists i.module then kept := kept.push { i with isMeta := true }
    else missing := missing.push i.module
  unless kept.any (·.module == `Init) do kept := #[{ module := `Init }] ++ kept
  let (env, messages) ← processHeaderCore (header.raw.getPos?.getD 0) (kept ++ extraImports)
    false {} messages inputCtx (trustLevel := 1024) (mainModule := mainModuleName)
  let cmdState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState cmdState
  return { env := s.commandState.env, messages := s.commandState.messages, inputCtx, missing }

/-- Run a `TermElabM` action in the environment of an elaborated file. -/
def runTermElab {α : Type} (el : Elaborated) (x : TermElabM α) (heartbeats : Nat := 0) :
    IO α := do
  let ctx : Core.Context := { fileName := el.inputCtx.fileName, fileMap := el.inputCtx.fileMap,
                              maxHeartbeats := heartbeats, options := {} }
  let st : Core.State := { env := el.env }
  let (a, _) ← (x.run'.run'.toIO ctx st)
  return a

/-- Why a definition of the file is not translated. -/
inductive Skip where
  /-- Not a candidate at all (auxiliary, private, a type, …): not reported. -/
  | silent
  /-- A candidate that is refused, with the reason. -/
  | refused (why : String)

/-- Does `e` mention a constant satisfying `p`? -/
def mentions (e : Expr) (p : Name → Bool) : Bool :=
  (e.find? fun | .const n _ => p n | _ => false).isSome

/-- Is `n` a definition of the file the tool should try to translate? -/
def classify (n : Name) (ci : ConstantInfo) : MetaM (Option Skip) := do
  let env ← getEnv
  if isPrivateName n || n.isInternalDetail || n.hasMacroScopes then return some .silent
  -- a `partial def f` is an opaque constant implemented by `f._unsafe_rec`.  (A definition
  -- by structural or well-founded recursion has an `_unsafe_rec` companion too, used by the
  -- compiler, but is a `defnInfo`: it is not partial.)
  if let .opaqueInfo _ := ci then
    if env.contains (n ++ `_unsafe_rec) then return some (.refused "a `partial` definition")
  let .defnInfo d := ci | return some .silent
  if isAuxRecursor env n || isNoConfusion env n || isMatcherCore env n then return some .silent
  if (← isInstance n) then return some .silent
  if (env.getProjectionFnInfo? n).isSome then return some .silent
  -- the auxiliary definitions Lean generates next to a definition
  let auxComponent (s : String) : Bool :=
    ["eq_def", "induct", "below", "brecOn", "binductionOn", "sizeOf_spec", "mutual_induct",
      "fun_cases", "_sunfold", "_unsafe_rec", "ctorIdx", "toCtorIdx", "ctorElim",
      "ctorElimType"].contains s || s.startsWith "eq_" || s.startsWith "proof_" ||
      s.startsWith "match_" || s.startsWith "_" || s.startsWith "brecOn_" ||
      s.startsWith "below_"
  if n.components.any (fun c => match c with | .str _ s => auxComponent s | _ => false) then
    return some .silent
  -- a definition of a type or of a proposition carries no value
  let isData ← forallTelescope d.type fun _ r => do
    let r ← whnf r
    if r.isSort then return false
    return !(← isProp r)
  unless isData do return some .silent
  if d.value.hasSorry then
    return some (.refused "the definition does not elaborate (it contains errors or `sorry`)")
  if mentions d.type (fun c => [``IO.RealWorld, ``EStateM, ``ST, ``EST, ``EIO, ``BaseIO,
      ``IO].contains c) then
    return some (.refused "an `IO`/`ST` action: the language has no side effects")
  if isNoncomputable env n then return some (.refused "a `noncomputable` definition")
  -- a definition by well-founded recursion is a candidate too: it is translated as the fixed
  -- point of its body (`openDef`)
  return none

/-- Is `n` defined by well-founded recursion (`WellFounded.fix`, directly or through the
    `f._unary` / `f._mutual` definition Lean packs the recursion in)? -/
def isWellFounded (n : Name) : MetaM Bool := do
  let env ← getEnv
  if (Elab.WF.eqnInfoExt.find? env n).isSome then return true
  let .defnInfo d ← getConstInfo n | return false
  return mentions d.value (fun c => c == ``WellFounded.fix || c == ``WellFounded.Nat.fix ||
      c == n ++ `_unary || c == n ++ `_mutual)

/-- The functions of the recursive group `n` belongs to (itself alone if it is not part of
    a `mutual` block). -/
def recGroup (n : Name) : MetaM (Array Name) := do
  let env ← getEnv
  if let some i := Elab.Structural.eqnInfoExt.find? env n then return i.declNames
  if let some i := Elab.WF.eqnInfoExt.find? env n then return i.declNames
  return #[n]

/-- The right-hand side of the unfolding equation of `n` (`n.eq_def`), under its parameters. -/
def withUnfoldRhs {α : Type} (n : Name) (k : Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  let some eqn ← getUnfoldEqnFor? n (nonRec := true)
    | throwError "`{n}` is not a definition that can be unfolded"
  let lvls := (← getConstInfo n).levelParams.map mkLevelParam
  forallTelescope (← inferType (mkConst eqn lvls)) fun xs eq => do
    let some (_, lhs, rhs) := eq.eq? | throwError "unexpected unfolding equation of `{n}`"
    k xs lhs rhs

/-- The constants of `among` the unfolding equation of `n` calls, in the order of `among`. -/
def unfoldRefs (n : Name) (among : Array Name) : MetaM (Array Name) :=
  withUnfoldRhs n fun _ _ rhs => return among.filter fun g => mentions rhs (· == g)

/-- The name of the parameter that stands for the function `g` in an open definition. -/
def recParamName (g : Name) : Name :=
  .mkSimple ("_".intercalate (g.components.map fun c => c.toString (escape := false)) ++ "_rec")

/-- The value of `c` at the universe levels `us`, when `c` is a theorem whose statement
    mentions one of the functions `refs`: an auxiliary proof Lean abstracted out of a
    definition (`f._proof_3 : … f (n + 1) …`), which the open definition must inline to see
    the calls of `f` in it (otherwise the statement of the proof, still about `f`, no longer
    matches the place it is used at, now about `f_rec`). -/
def inlinableProof? (refs : Array Name) (c : Name) (us : List Level) : MetaM (Option Expr) := do
  let some (.thmInfo t) := (← getEnv).find? c | return none
  unless mentions t.type (refs.contains ·) do return none
  return some (t.value.instantiateLevelParams t.levelParams us)

/-- Replace the calls of the functions `refs` by calls of the parameters standing for them
    (`selfs`, each with the positions of the proof parameters it drops): `g a h b` becomes
    `g_rec a b` when `h` is a proof.  An auxiliary proof about the functions `refs` is inlined
    first (`inlinableProof?`). -/
partial def replaceRecCalls (refs : Array Name) (selfs : Array (Expr × Array Bool)) (e : Expr) :
    MetaM Expr := do
  let find? (c : Name) := (refs.findIdx? (· == c)).map (selfs[·]!)
  match e with
  | .app .. =>
    let f := e.getAppFn
    if let .const c us := f then
      if let some v ← inlinableProof? refs c us then
        return ← replaceRecCalls refs selfs (mkAppN v e.getAppArgs).headBeta
    let args ← e.getAppArgs.mapM (replaceRecCalls refs selfs)
    match f with
    | .const c _ =>
      match find? c with
      | some (x, isPf) =>
        if isPf.isEmpty then return mkAppN x args
        if args.size < isPf.size then
          throwError "`{c}` is applied to fewer arguments than its parameters, whose proofs \
            cannot be erased"
        let kept := (List.range args.size).toArray.filter (fun i => !(isPf[i]?.getD false)) |>.map (args[·]!)
        return mkAppN x kept
      | none => return mkAppN f args
    | _ => return mkAppN (← replaceRecCalls refs selfs f) args
  | .const c us =>
    if let some v ← inlinableProof? refs c us then
      return ← replaceRecCalls refs selfs v
    match find? c with
    | some (x, isPf) =>
      if isPf.isEmpty then return x
      throwError "`{c}` is used as a value, but it takes proofs, which cannot be erased"
    | none => return e
  | .lam _ t b _ => return e.updateLambdaE! (← replaceRecCalls refs selfs t) (← replaceRecCalls refs selfs b)
  | .forallE _ t b _ => return e.updateForallE! (← replaceRecCalls refs selfs t) (← replaceRecCalls refs selfs b)
  | .letE n t v b nd =>
    return .letE n (← replaceRecCalls refs selfs t) (← replaceRecCalls refs selfs v)
      (← replaceRecCalls refs selfs b) nd
  | .mdata _ b => return e.updateMData! (← replaceRecCalls refs selfs b)
  | .proj _ _ b => return e.updateProj! (← replaceRecCalls refs selfs b)
  | _ => return e

/-- The name of the open definition of `n`. -/
def openDefName (n : Name) : Name := n ++ `leanscript_open

/-- **The open definition** of `n`, abstracted over the recursive functions `refs`: the
    right-hand side of the unfolding equation of `n` (`n x = body`), in which every call of a
    function `g` of `refs` (`n` itself, the other members of its `mutual` block, other
    functions of the file defined by well-founded recursion) is a call of a new first
    parameter `g_rec`:

    `n.leanscript_open g₁_rec … gₖ_rec x = body[gᵢ := gᵢ_rec]`

    It is not recursive, so the translator reads it like any other definition; `n` is its
    fixed point, `n = n.leanscript_open g₁ … gₖ` (the unfolding equation), which is how the
    JavaScript runs it: the exported function `n` passes the exported functions `gᵢ`
    themselves for the `gᵢ_rec`.  Nothing about termination is needed at run time: the
    calls are exactly those Lean makes. -/
def openDef (n : Name) (refs : Array Name) : MetaM Name := do
  let info ← getConstInfo n
  unless info.levelParams.isEmpty do throwError "`{n}` is universe polymorphic"
  -- the type of `g_rec`: the type of `g` without its proof parameters, when no later type
  -- depends on them (the translation erases proofs, and a function value cannot take one)
  let recTys ← refs.mapM fun g => do
    let gi ← getConstInfo g
    unless gi.levelParams.isEmpty do throwError "`{g}` is universe polymorphic"
    forallTelescope gi.type fun ys r => do
      let isPf ← ys.mapM fun y => do isProp (← inferType y)
      let kept := (List.range ys.size).toArray.filter (!isPf[·]!) |>.map (ys[·]!)
      let t ← mkForallFVars kept r
      if isPf.any id && !t.hasFVar then return (t, isPf) else return (gi.type, #[])
  let (ty, val) ← withUnfoldRhs n fun xs lhs rhs => do
    let decls := (refs.zip recTys).map fun (g, t, _) =>
      (recParamName g, fun (_ : Array Expr) => pure t)
    withLocalDeclsD decls fun selfs => do
      let rhs' ← replaceRecCalls refs (selfs.zip (recTys.map (·.2))) rhs
      return (← mkForallFVars (selfs ++ xs) (← inferType lhs), ← mkLambdaFVars (selfs ++ xs) rhs')
  let name := openDefName n
  let decl := Declaration.defnDecl { name, levelParams := [], type := ty, value := val,
                                     hints := .regular 0, safety := .safe }
  -- (the kernel checks it: a proof of the body that relies on the definition of a function it
  -- now calls through `g_rec` makes the open definition, and the function, refused)
  addDecl decl
  -- its unfolding equation is generated on demand
  enableRealizationsForConst name
  return name

/-- The candidates of the file, in the order of the file, and the refused ones with the
    reason. -/
def candidates (el : Elaborated) : IO (Array Name × Array (Name × String)) := runTermElab el do
  let env ← getEnv
  let mut locals : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.map₂.toList do
    locals := locals.push (n, ci)
  let mut withPos : Array (Nat × Name) := #[]
  let mut refused : Array (Nat × Name × String) := #[]
  for (n, ci) in locals do
    let pos := match ← findDeclarationRanges? n with
      | some r => r.range.pos.line * 100000 + r.range.pos.column
      | none => 0
    match ← classify n ci with
    | none => withPos := withPos.push (pos, n)
    | some .silent => pure ()
    | some (.refused why) => refused := refused.push (pos, n, why)
  let sortedOk := withPos.qsort (fun a b => a.1 < b.1)
  let sortedRefused := refused.qsort (fun a b => a.1 < b.1)
  return (sortedOk.map (·.2), sortedRefused.map (·.2))

/-- The names of the parameters of a definition that the translation keeps (not types,
    instances, propositions or `Unit`), sanitised later by the printer. -/
def paramNames (n : Name) : MetaM (List String) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let t ← inferType x
      if (← isType x) || (← isProp t) || (← isClass? t).isSome then continue
      if (← whnf t).isConstOf ``Unit || (← whnf t).isConstOf ``PUnit then continue
      out := out.push (← x.fvarId!.getUserName).eraseMacroScopes.toString
    return out.toList

/-- Is `e` a value the tool can evaluate at once: literals and constructors (of values;
    types and proofs are skipped), and primitives implemented natively (`@[extern]`,
    `opaque`) applied to such values. -/
partial def isValueLike (e : Expr) : MetaM Bool := do
  match e with
  | .lit _ => return true
  | .mdata _ e => isValueLike e
  | _ =>
    let env ← getEnv
    let some (c, _) := e.getAppFn.const? | return false
    let ok := match env.find? c with
      | some (.ctorInfo _) => true
      | some (.opaqueInfo _) => true
      | _ => isExtern env c
    unless ok do return false
    for a in e.getAppArgs do
      if (← isProof a) || (← isType a) then continue
      if (← inferType a).isSort then continue
      unless ← isValueLike a do return false
    return true

/-- Compute the closed values of leaf type a translation embeds (`PExpr.lit p v`, where the
    translator put a closed Lean term such as `3 + 4` or `ack 2 3`), so that evaluating the
    translation is cheap: each value is normalised with a bounded budget, and a value that
    does not normalise to literals and constructors is refused rather than computed. -/
def reduceLits (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``LeanScript.PExpr.lit 6 then
      let v := e.appArg!
      if ← isValueLike v then return .done e
      let v' ← tryCatchRuntimeEx
          (withTheReader Core.Context (fun c => { c with maxHeartbeats := 200 * 1000 }) do
            withCurrHeartbeats do
              Meta.reduce v (skipTypes := true) (skipProofs := true))
          (fun _ =>
            throwError "the closed value `{v}` could not be computed at compile time")
      -- a normal form that is still stuck on a `partial` or `opaque` function is not a value
      let env ← getEnv
      let stuck := mentions v' fun c => env.contains (c ++ `_unsafe_rec) ||
        (match env.find? c with
         | some (.opaqueInfo _) => !isExtern env c
         | some (.axiomInfo _) => true
         | _ => false)
      if stuck then
        throwError "the closed value `{v}` could not be computed at compile time \
          (it normalises to `{v'}`)"
      return .done (mkApp e.appFn! v')
    return .continue)

/-- Translate a definition to a closed `Term` value. -/
unsafe def translate (n : Name) : TermElabM ClosedTerm := do
  modifyThe Core.State fun st => { st with messages := {} }
  -- a `List` is the built-in list (an immutable JavaScript array): the tool has no signature
  -- that could declare it as a datatype
  let v ← withOptions (·.setBool LeanScript.Gen.builtinListOption true) do
    LeanScript.Gen.translateDef n none
  Term.synthesizeSyntheticMVarsNoPostponing
  let v ← instantiateMVars v
  -- the translator reports some failures as logged errors rather than exceptions
  let msgs := (← getThe Core.State).messages
  if msgs.hasErrors then
    let firstErr := msgs.toList.find? (·.severity == .error)
    let txt ← match firstErr with
      | some m => m.data.toString
      | none => pure "an error"
    throwError "{txt}"
  if v.hasMVar then
    throwError "the translation has unresolved parts (metavariables)"
  -- a translation generic in the signature is `fun {ks} {Δ} => t`
  let ty ← whnfR (← inferType v)
  let v := if ty.isAppOf ``LeanScript.Term then v
    else (mkAppN v #[mkApp (mkConst ``List.nil [.zero]) (mkConst ``Nat),
      mkConst ``LeanScript.DSig.nil]).headBeta
  let ty ← whnfR (← inferType v)
  unless ty.isAppOfArity ``LeanScript.Term 8 do
    throwError "unexpected type of the translation: {ty}"
  let v ← reduceLits v
  let as := ty.getAppArgs
  let packed := mkAppN (mkConst ``LeanScript.ClosedTerm.mk) #[as[0]!, as[1]!, as[5]!, as[7]!, v]
  evalExpr LeanScript.ClosedTerm (mkConst ``LeanScript.ClosedTerm) packed

/-- The type of a definition, as Lean prints it. -/
def typeString (n : Name) : MetaM String := do
  return toString (← ppExpr (← getConstInfo n).type)

end LeanScript.Cli
