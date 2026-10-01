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

/-- The name the main module of an elaborated file gets: the name of the file
    (`CasePartial` for `Tests/CasePartial.lean`, which is what `panic!` writes in its message,
    `PANIC at test1 CasePartial:5:9: …`), or `LeanScriptInput` when it has none. -/
def mainModuleName (file : System.FilePath) : Name :=
  match file.fileStem with
  | some s => if s.isEmpty then `LeanScriptInput else Name.mkSimple s
  | none => `LeanScriptInput

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
    false {} messages inputCtx (trustLevel := 1024) (mainModule := mainModuleName file)
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
  -- the parser of a notation (`infixl`, `notation`, `syntax`): part of the syntax of the file,
  -- not of its program
  if d.type.isConstOf ``Lean.ParserDescr || d.type.isConstOf ``Lean.TrailingParserDescr then
    return some .silent
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
    instances, propositions or `Unit`), sanitised later by the printer: the binders of the
    leading `fun`s of its value, then those of its type (unfolded: `test4 (f : F) : F` for
    `F := ∀ {α β γ}, α → β → γ` takes `f` and then the parameters of `F`).  When the definition
    was translated through its generalisation over `Unit` (`Gen.unitGenName`, declared by the
    translation), the names are the generalisation's, whose `Unit`s are parameters. -/
def paramNames (n : Name) : MetaM (List String) := do
  let g := LeanScript.Gen.unitGenName n
  let n := if (← getEnv).contains g then g else n
  let ci ← getConstInfo n
  let keep (x : Expr) : MetaM Bool := do
    let t ← inferType x
    if (← isType x) || (← isProp t) || (← isClass? t).isSome then return false
    if (← whnf t).isConstOf ``Unit || (← whnf t).isConstOf ``PUnit then return false
    return true
  -- a binder written by the user, or `none` for one Lean made up (`x✝` of a `match`)
  let name? (x : Expr) : MetaM (Option String) := do
    let n ← x.fvarId!.getUserName
    return if n.hasMacroScopes then none else some n.toString
  let name (x : Expr) : MetaM String := do
    return (← x.fvarId!.getUserName).eraseMacroScopes.toString
  let fromType (T : Expr) : MetaM (Array (Option String)) :=
    forallTelescopeReducing T fun ys _ => do
      let mut out := #[]
      for y in ys do if ← keep y then out := out.push (← name? y)
      return out
  -- the names of the type, used where the value's `fun`s give none written by the user
  let tyNames ← forallTelescopeReducing ci.type fun ys _ => do
    let mut out := #[]
    for y in ys do if ← keep y then out := out.push (← name y)
    return out
  let valNames ← match ci.value? with
    | some v =>
      lambdaTelescope v fun xs body => do
        let mut out := #[]
        for x in xs do if ← keep x then out := out.push (← name? x)
        return out ++ (← fromType (← inferType body))
    | none => pure #[]
  let n := max tyNames.size valNames.size
  return (List.range n).map fun i => (valNames[i]?.join).getD (tyNames[i]?.getD s!"p{i}")

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
def reduceLits (e : Expr) (nativeFloat : Expr → MetaM (Option Expr) := fun _ => pure none) :
    MetaM Expr :=
  Meta.transform e (post := fun e => do
    if e.isAppOfArity ``LeanScript.PExpr.lit 6 then
      let v := e.appArg!
      if ← isValueLike v then return .done e
      -- a closed float (`HashableFloat.normalize (1.5 + 1.0)`): computed natively, to its bits
      -- (reducing the float model symbolically is far too slow); refused when it is `NaN` or
      -- `-0.0`, which the language's floats do not have (`checkFloatLit`)
      if v.isAppOfArity ``HashableFloat.normalize 1 || v.isAppOfArity ``HashableFloat32.normalize 1 then
        if let some a' ← nativeFloat v.appArg! then
          return .done (mkApp e.appFn! (mkApp v.appFn! a'))
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

/-- A closed float (`Float` or `Float32`), computed natively: `Float.ofBits b` (`Float32.ofBits b`)
    for its bits `b`.  Refused when it is `NaN` or `-0.0`: the language's floats
    (`HashableFloat`) have neither, and normalising it to `0.0` would change the program. -/
unsafe def checkFloatLit (a : Expr) : MetaM (Option Expr) := do
  let ty ← whnf (← inferType a)
  let refuse (what : String) : MetaM (Option Expr) :=
    throwError "the closed float `{a}` is {what}, which the language's floats \
      (`HashableFloat`) cannot represent"
  if ty.isConstOf ``Float then
    let f ← evalExpr Float (mkConst ``Float) a
    if f.isNaN then return ← refuse "NaN"
    if f.toBits == 0x8000000000000000 then return ← refuse "-0.0"
    return some (mkApp (mkConst ``Float.ofBits) (toExpr f.toBits))
  else if ty.isConstOf ``Float32 then
    let f ← evalExpr Float32 (mkConst ``Float32) a
    if f.isNaN then return ← refuse "NaN"
    if f.toBits == 0x80000000 then return ← refuse "-0.0"
    return some (mkApp (mkConst ``Float32.ofBits) (toExpr f.toBits))
  else return none

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
  let v ← reduceLits v checkFloatLit
  let as := ty.getAppArgs
  let packed := mkAppN (mkConst ``LeanScript.ClosedTerm.mk) #[as[0]!, as[1]!, as[5]!, as[7]!, v]
  evalExpr LeanScript.ClosedTerm (mkConst ``LeanScript.ClosedTerm) packed

/-! ## The recursive types of a file, declared on their own

`Term` refers to a recursive type by its name in the signature of the program
(`leanscript_signature`).  A file written for Lean only declares none, so the tool declares one
itself (`autoSignature`): the program `LeanScriptAutoSig` of every recursive inductive type the
candidates mention (in their types or their bodies) at closed arguments. -/

/-- The name of the program the tool declares for the recursive types of a file. -/
def autoSigName : Name := `LeanScriptAutoSig

/-- The closed applications of recursive inductive types in `e` (`Expr`, `Tree Nat`): the types
    the translation of a definition mentioning `e` must find in the signature. -/
partial def recTypeApps (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let isRecInd (c : Name) : Bool := match env.find? c with
    | some (.inductInfo i) => (i.isRec || i.all.length > 1 || i.numNested > 0) &&
        ![``Nat, ``List, ``Array, ``Lean.Name, ``String, ``Int].contains c
    | _ => false
  let mut acc : Array Expr := #[]
  let mut seen : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[e]
  while h : todo.size > 0 do
    let x := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains x then continue
    seen := seen.insert x
    match x with
    | .app .. =>
      if let .const c _ := x.getAppFn then
        if isRecInd c && !x.hasLooseBVars && !x.hasFVar && !x.hasMVar then
          if let some (.inductInfo i) := env.find? c then
            if x.getAppNumArgs == i.numParams + i.numIndices then acc := acc.push x
      todo := todo.push x.appFn! |>.push x.appArg!
    | .const c _ =>
      if isRecInd c then
        if let some (.inductInfo i) := env.find? c then
          if i.numParams + i.numIndices == 0 then acc := acc.push x
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return acc

/-- Run a command in the environment of an elaborated file; the new environment, or `none`
    when the command fails. -/
def runCommandElab (el : Elaborated) (opts : Options) (x : Command.CommandElabM Unit) :
    IO (Option Environment) := do
  let ctx : Command.Context := { fileName := el.inputCtx.fileName, fileMap := el.inputCtx.fileMap,
                                 snap? := none, cancelTk? := none }
  let st := Command.mkState el.env {} opts
  match ← (x ctx |>.run st).toBaseIO with
  | .ok ((), st') => return if st'.messages.hasErrors then none else some st'.env
  | .error _ => return none

/-- Declare the program of the recursive types the candidates `cands` mention
    (`autoSigName`), and make it the current one, unless the file declares a program itself.
    A type the signature refuses is left out (the translation of a definition using it then
    reports why). -/
def autoSignature (el : Elaborated) (cands : Array Name) : IO Elaborated := do
  -- a file that declares its own program is translated against it
  let own ← runTermElab el (return (← LeanScript.Gen.currentProg?).isSome)
  if own then return el
  let opts := ({} : Options).setBool LeanScript.Gen.builtinListOption true
  let tys ← runTermElab el (withOptions (fun _ => opts) do
    let mut out : Array Expr := #[]
    for n in cands do
      let ci ← getConstInfo n
      let mut es := (← recTypeApps ci.type)
      if let some v := ci.value? then es := es ++ (← recTypeApps v)
      for t in es do
        let t ← try LeanScript.Gen.normType t catch _ => continue
        unless out.contains t do out := out.push t
    return out)
  if tys.isEmpty then return el
  let declare (ts : Array Expr) : IO (Option Environment) :=
    runCommandElab el opts do
      let names := (List.range ts.size).toArray.map fun i => Name.mkSimple s!"t{i}"
      LeanScript.Gen.declareProgram (mkIdent autoSigName) names ts
  if let some env ← declare tys then return { el with env }
  -- some type is refused: keep the ones the signature accepts on their own
  let mut kept : Array Expr := #[]
  for t in tys do
    if (← declare #[t]).isSome then kept := kept.push t
  if kept.isEmpty then return el
  match ← declare kept with
  | some env => return { el with env }
  | none => return el

/-- The type of a definition, as Lean prints it. -/
def typeString (n : Name) : MetaM String := do
  return toString (← ppExpr (← getConstInfo n).type)

end LeanScript.Cli
