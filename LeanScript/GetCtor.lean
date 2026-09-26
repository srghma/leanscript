module

public meta import LeanScript.Signature

@[expose] public section

meta section

set_option autoImplicit false

/-!
# `#leanscript_get_ty`, `#leanscript_get_ctor` and `#leanscript_get_cases`

The constructor API of the language (designed in §2.6 of
`proposals/NominalTyProposal.md`).  All
three are term elaborators backed by the cache (`LeanScript.Gen.Cache`): the definition is
generated the first time and reused afterwards, here and in importing modules.  Written as a
command, each shows what it generated.

* `#leanscript_get_ty T` — the `Ty` of a closed Lean type `T`.  A structural type (no
  declared datatype in it) is generic in the signature, `{ks : List Nat} → Ty ks`; a type that
  mentions a recursive datatype is a `Ty Prog.ks` of the current program `Prog`
  (`leanscript_signature`), where the datatype is its name `.data r`.

* `#leanscript_get_ctor c (x := T)…` — the constructor function of the Lean constructor `c`
  (`#leanscript_get_ctor I` names the only constructor of `I`).  Its arguments, in order:

  | Lean binder | argument |
  | :-- | :-- |
  | a type parameter given as a named argument `(α := T)` | none: fixed when generated, and part of the cache key |
  | a type parameter not given (`α : Type`) | an explicit `(α : Ty ks)` |
  | any other parameter | must be given as a named argument |
  | a value field | a `Term Δ Γ τ`, `τ` its translated type |
  | a proof or instance field | none (erased) |

  The result is a `Term Δ Γ τ` where `τ` is `#leanscript_get_ty` of the constructor's type:

  * one constructor with one field: the field itself (the wrapper is erased);
  * one constructor with two or more fields: `Term.record_mk`;
  * two field-less constructors: a literal of the leaf `bool`, `false` for the first and
    `true` for the second (`Bool.false`/`Bool.true` themselves, and every other type of two
    points: two points are only ever `bool`);
  * three or more field-less constructors: `Term.enum_mk` (`Ordering` numbers from `-1`);
  * otherwise `Term.union_mk` at the constructor's position;
  * for a **recursive** type (a member of a block of the current program), `Term.data_in` of
    the above: the translator never builds `data_in` for a Lean constructor itself.

  Like `#leanscript_get_ty`, the function is generic in the signature
  (`{ks} {Δ : DSig ks} {Γ : Ctx ks}`) unless a declared datatype occurs in it; then it is
  specialised to the current program (`{Γ : Ctx Prog.ks}`, terms over `Prog.Δ`).

  A type parameter a recursive layout depends on must be given
  (`#leanscript_get_ctor List.cons (α := Nat)`): every instance of a recursive type is its
  own member of the signature.

* `#leanscript_get_cases I (x := T)…` — the dual: the case analysis of the Lean inductive
  type `I` (a constructor name denotes its type).  Its arguments are the type variables, the
  answer type `{τ}`, the scrutinee, and one branch per constructor, `on_c`, whose context
  binds the constructor's fields in front of `Γ` (the first field innermost).  The body is
  `Term.union_casesOn` / `Term.record_casesOn` / `Term.letE` (a single field) /
  `Term.enum_casesOn` / `Term.ite` (`Bool`), preceded by `Term.data_out` for a recursive
  type, so the translator never builds `data_out` for a Lean `casesOn` itself.
-/

open Lean Meta Elab Term

namespace LeanScript.Gen

/-! ## Syntax -/

/-- A named parameter of `#leanscript_get_ctor`: `(α := Nat)`. -/
syntax leanscriptNamedArg := atomic("(" ident " := ") term ")"

/-- `#leanscript_get_ty T`: the `Ty` of the closed Lean type `T`. -/
syntax:max (name := leanscriptGetTy) "#leanscript_get_ty " term:max : term

/-- `#leanscript_get_ctor c (α := T)…`: the constructor function of the Lean constructor
    `c`. -/
syntax:max (name := leanscriptGetCtor)
  "#leanscript_get_ctor " ident (ppSpace leanscriptNamedArg)* : term

/-- `#leanscript_get_cases I (α := T)…`: the case analysis of the Lean inductive type `I`. -/
syntax:max (name := leanscriptGetCases)
  "#leanscript_get_cases " ident (ppSpace leanscriptNamedArg)* : term

/-- `#leanscript_get_cases I …`, as a command: show the generated case analysis. -/
syntax (name := leanscriptGetCasesCmd)
  "#leanscript_get_cases " ident (ppSpace leanscriptNamedArg)* : command

/-- `#leanscript_get_ty T`, as a command: show the generated type. -/
syntax (name := leanscriptGetTyCmd) "#leanscript_get_ty " term:max : command

/-- `#leanscript_get_ctor c …`, as a command: show the generated constructor function. -/
syntax (name := leanscriptGetCtorCmd)
  "#leanscript_get_ctor " ident (ppSpace leanscriptNamedArg)* : command

/-! ## Types -/

/-- The name a type is known by, for naming generated definitions. -/
def headName (e : Expr) : Name :=
  match e.getAppFn.constName? with
  | some c => c
  | none => `Fn

/-- The generated definition of `#leanscript_get_ty T`, generating it if needed. -/
def ensureTy (T : Expr) : TermElabM Name := do
  let T ← normType T
  if T.hasFVar || T.hasMVar then fail m!"the type{indentExpr T}\nis not closed"
  let prog? : Option ProgInfo ← currentProg?
  let cir ← (do
      discover T
      discard <| declareBlocks false (prog?.map ProgInfo.name)
      toCIR T).run' (St.ofProg #[] prog?)
  let prog? := if cir.hasData then prog? else none
  let key : GenKey := { kind := "ty", args := #[some T], prog := prog?.map ProgInfo.name }
  if let some d ← cached? key then return d
  let decl ← match prog? with
    | some p => freshDeclName p.name (p.name ++ `ty ++ headName T)
    | none => freshDeclName (headName T) (headName T ++ `leanScriptTy)
  let tyStx ← cir.stx (prog?.map (fun p : ProgInfo => p.members.size) |>.getD 0) #[]
  match prog? with
  | some p =>
    emitDef decl (← `(LeanScript.Ty $(mkIdent (p.name ++ `ks)))) tyStx
  | none =>
    let ks := mkIdent `ks
    emitDef decl (← `(∀ {$ks : List Nat}, LeanScript.Ty $ks)) (← `(fun {$ks} => $tyStx))
  addEntry (.gen key decl)
  return decl

/-! ## Constructors -/

/-- The constructor a name denotes: a constructor, or an inductive type with exactly one. -/
def resolveCtor (id : Ident) : TermElabM Name := do
  let n ← try realizeGlobalConstNoOverloadWithInfo id
    catch _ => fail m!"unknown constant `{id.getId}`"
  match (← getEnv).find? n with
  | some (.ctorInfo _) => return n
  | some (.inductInfo ind) =>
    match ind.ctors with
    | [c] => return c
    | cs => fail m!"`{n}` has {cs.length} constructors; name the one you mean"
  | _ => fail m!"`{n}` is not a constructor"

/-- Instantiate the parameters of a constructor's type: the named ones with their values,
    the other type parameters with fresh type variables.  `k` receives the parameters, the
    cache key's view of them, and the type variables. -/
partial def withParams {α : Type} (ctor : Name) (numParams : Nat) (ty : Expr)
    (named : Array (Ident × Lean.Term))
    (k : Array Expr → Array (Option Expr) → Array Expr → TermElabM α) : TermElabM α :=
  go 0 ty #[] #[] #[] (named.map (·.1.getId))
where
  go (i : Nat) (ty : Expr) (ps : Array Expr) (key : Array (Option Expr)) (vars : Array Expr)
      (unused : Array Name) : TermElabM α := do
    if i = numParams then
      unless unused.isEmpty do
        fail m!"`{ctor}` has no parameter named {unused.toList}"
      return ← k ps key vars
    let .forallE n d b _ ← whnf ty | fail m!"`{ctor}` has fewer parameters than expected"
    if let some (_, v) := named.find? (·.1.getId == n) then
      let v ← elabTermEnsuringType v d
      synthesizeSyntheticMVarsNoPostponing
      let v ← instantiateMVars v
      let v ← if ← isType v then normType v else pure v
      go (i + 1) (b.instantiate1 v) (ps.push v) (key.push (some v)) vars (unused.erase n)
    else if (← whnf d).isSort then
      unless ← isDefEq d (mkSort Level.one) do
        fail m!"the parameter `{n}` of `{ctor}` is not a `Type`; give it as `({n} := …)`"
      withLocalDeclD n (mkSort Level.one) fun x =>
        go (i + 1) (b.instantiate1 x) (ps.push x) (key.push none) (vars.push x) unused
    else
      fail m!"the parameter `{n}` of `{ctor}` is not a type; give it as `({n} := …)`"

/-- What an inductive instance translates to. -/
structure TypePlan where
  /-- Its constructors: their names and the types of their fields. -/
  ctors : Array (Name × Array CIR)
  /-- The type it is. -/
  layout : CIR
  /-- `(block, member)` when it is a member of a declared block. -/
  data? : Option (Nat × Nat)
  /-- `(constructors, shift)` when it is an enum. -/
  enum? : Option (Nat × Int)
  /-- Is it `Bool` (or another type of two field-less constructors), the leaf whose
      constructors are the literals `false` and `true`? -/
  isBool : Bool := false

/-- Does a plan name a declared datatype anywhere (then it is specialised to the program)? -/
def TypePlan.concrete (p : TypePlan) : Bool :=
  p.layout.hasData || p.ctors.any (·.2.any CIR.hasData)

/-- Translate the inductive instance `T` and its constructors. -/
def planType (T : Expr) (prog? : Option ProgInfo) : M TypePlan := do
  discover T
  let ctors ← match ← classify T with
    | .node n => readCtors n
    | _ => pure #[]
  for (_, fs) in ctors do
    for f in fs do discover f
  discard <| declareBlocks false (prog?.map ProgInfo.name)
  match ← classify T with
  | .prim _ =>
    if T.isConstOf ``Bool then
      return { ctors := #[(``Bool.false, #[]), (``Bool.true, #[])], layout := ← toCIR T,
               data? := none, enum? := none, isBool := true }
    fail m!"`{T}` is a leaf of the language: its values are literals, not constructor \
      applications"
  | .node n =>
    let i := (← get).index[n]!
    let ctors ← ctors.mapM fun (c, fs) => return (c, ← fs.mapM toCIR)
    match ← kindOf i with
    | .recursive b j => return { ctors, layout := .data b j, data? := some (b, j), enum? := none }
    | .structural =>
      let layout ← toCIR n
      let enum? := match layout with | .enum m s => some (m, s) | _ => none
      -- two field-less constructors are the leaf `bool`: the first is `false`
      let isBool := ctors.size = 2 && ctors.all (·.2.isEmpty)
      return { ctors, layout, data? := none, enum?, isBool }
  | _ => fail m!"`{T}` is a built-in type former, which has no constructors of its own"

/-- The last two components of a constructor's name (`Tree.node`), which name its
    function under a program (`Prog.Tree.node`). -/
def shortName (ctor : Name) : Name :=
  match ctor with
  | .str (.str _ i) c => .str (.str .anonymous i) c
  | n => n

/-- A name for a type variable that does not clash with the implicit arguments. -/
def varIdent (n : Name) : Ident :=
  let n := n.eraseMacroScopes
  if n == `ks || n == `Δ || n == `Γ then mkIdent (n.appendAfter "'") else mkIdent n

/-- The instance of the inductive type `ind` given by the named parameters, the other type
    parameters being type variables.  `k` receives the instance, the cache key's view of the
    parameters, and the type variables. -/
def withInstance {α : Type} (ind : Name) (named : Array (Ident × Lean.Term))
    (k : Expr → Array (Option Expr) → Array Expr → TermElabM α) : TermElabM α := do
  let info ← getConstInfoInduct ind
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty := info.type.instantiateLevelParams info.levelParams us
  withParams ind info.numParams ty named fun ps key vars => do
    for u in us do
      if (← instantiateLevelMVars u).hasMVar then discard <| isLevelDefEq u Level.zero
    let us ← us.mapM instantiateLevelMVars
    k (← normType (mkAppN (mkConst ind us) ps)) key vars

/-- How a generated function is set up: its signature arguments, the program it is
    specialised to, and the names it uses. -/
structure Frame where
  /-- The program, when the function names a declared datatype. -/
  prog? : Option ProgInfo
  /-- The number of blocks visible (those of the program). -/
  c : Nat
  /-- The type variables. -/
  varIds : Array Ident
  /-- `ks` and `Δ`: the program's, or the function's own implicit arguments. -/
  ksT : Lean.Term
  dT : Lean.Term

/-- The frame of a function generated from a plan. -/
def mkFrame (plan : TypePlan) (prog? : Option ProgInfo) (vars : Array Expr) : TermElabM Frame := do
  let prog? := if plan.concrete then prog? else none
  let varIds ← vars.mapM fun x => return varIdent (← x.fvarId!.getUserName)
  let (ksT, dT) : Lean.Term × Lean.Term := match prog? with
    | some p => (mkIdent (p.name ++ `ks), mkIdent (p.name ++ `Δ))
    | none => (mkIdent `ks, mkIdent `Δ)
  return { prog?, c := prog?.map (fun p : ProgInfo => p.members.size) |>.getD 0, varIds, ksT, dT }

/-- Close a generated function: `fty`/`fn` take the type variables, then (in front) the
    context `{Γ}`, and when generic `{ks} {Δ}`. -/
def Frame.close (F : Frame) (fty fn : Lean.Term) : TermElabM (Lean.Term × Lean.Term) := do
  let mut fty := fty
  let mut fn := fn
  for v in F.varIds.reverse do
    fty ← `(($v : LeanScript.Ty $(F.ksT)) → $fty)
    fn ← `(fun $v => $fn)
  let gam := mkIdent `Γ
  fty ← `(∀ {$gam : LeanScript.Ctx $(F.ksT)}, $fty)
  fn ← `(fun {$gam} => $fn)
  if F.prog?.isNone then
    let ks := mkIdent `ks
    let d := mkIdent `Δ
    fty ← `(∀ {$ks : List Nat} {$d : LeanScript.DSig $ks}, $fty)
    fn ← `(fun {$ks} {$d} => $fn)
  return (fty, fn)

/-- The name of a generated definition: under the program when specialised to one. -/
def Frame.declName (F : Frame) (key short : Name) (suffix : Name) : TermElabM Name :=
  match F.prog? with
  | some p => freshDeclName p.name (p.name ++ short ++ suffix)
  | none => freshDeclName key (key ++ suffix)

/-- The generated definition of `#leanscript_get_ctor c (named…)`, generating it if
    needed. -/
def ensureCtor (id : Ident) (named : Array (Ident × Lean.Term)) : TermElabM Name := do
  let ctor ← resolveCtor id
  let cinfo ← getConstInfoCtor ctor
  withInstance cinfo.induct named fun T key vars => do
    let prog? : Option ProgInfo ← currentProg?
    let plan ← (planType T prog?).run' (St.ofProg (vars.map (·.fvarId!)) prog?)
    let F ← mkFrame plan prog? vars
    let gkey : GenKey := { kind := "ctor", name := ctor, args := key, prog := F.prog?.map ProgInfo.name }
    if let some d ← cached? gkey then return d
    let some pos := plan.ctors.findIdx? (·.1 == ctor)
      | fail m!"`{ctor}` is not a constructor of{indentExpr T}"
    let fields := plan.ctors[pos]!.2
    let decl ← F.declName ctor (shortName ctor) (if F.prog?.isSome then .anonymous else `leanScriptCtor)
    let argIds : Array Ident := (Array.range fields.size).map fun q => mkIdent (.mkSimple s!"x{q}")
    let gam := mkIdent `Γ
    -- the body
    let args : List Lean.Term := argIds.toList.map fun a => ⟨a.raw⟩
    let payload ← if plan.isBool then
        if pos == 1 then `(LeanScript.Term.lit LeanPrimTy.bool rfl true)
        else `(LeanScript.Term.lit LeanPrimTy.bool rfl false)
      else ctorBodyStx plan.ctors.size pos plan.enum? args
    let body ← match plan.data? with
      | some (b, j) => `(LeanScript.Term.data_in $(← brefStx F.c b) $(quote j) $payload)
      | none => pure payload
    -- the type and the function
    let mut fty ← `(LeanScript.Term $(F.dT) $gam $(← plan.layout.stx F.c F.varIds))
    let mut fn := body
    for q in (List.range fields.size).reverse do
      fty ← `(($(argIds[q]!) : LeanScript.Term $(F.dT) $gam
        $(← fields[q]!.stx F.c F.varIds)) → $fty)
      fn ← `(fun $(argIds[q]!) => $fn)
    let (fty', fn') ← F.close fty fn
    emitDef decl fty' fn'
    addEntry (.gen gkey decl)
    return decl

/-! ## Case analysis -/

/-- The inductive type a name denotes (a constructor names its type). -/
def resolveInductive (id : Ident) : TermElabM Name := do
  let n ← try realizeGlobalConstNoOverloadWithInfo id
    catch _ => fail m!"unknown constant `{id.getId}`"
  match (← getEnv).find? n with
  | some (.inductInfo _) => return n
  | some (.ctorInfo c) => return c.induct
  | _ => fail m!"`{n}` is not an inductive type"

/-- The case analysis of a value of `layout`, whose (unfolded) type has the constructors
    `ctors`: one branch per constructor, which binds the constructor's fields. -/
def casesBodyStx (plan : TypePlan) (scrut : Lean.Term) (bs : Array Lean.Term) :
    MetaM Lean.Term := do
  let m := plan.ctors.size
  if plan.isBool then
    `(LeanScript.Term.ite $scrut $(bs[1]!) $(bs[0]!))
  else if plan.enum?.isSome then
    let i := mkIdent `i
    let mut sel := bs[m - 1]!
    for p in (List.range (m - 1)).reverse do
      sel ← `(if ($i).val = $(quote p) then $(bs[p]!) else $sel)
    `(LeanScript.Term.enum_casesOn $scrut (fun $i => $sel))
  else if m = 1 then
    if plan.ctors[0]!.2.size = 1 then `(LeanScript.Term.letE $scrut $(bs[0]!))
    else `(LeanScript.Term.record_casesOn $scrut $(bs[0]!))
  else
    let mut br ← `(LeanScript.Branches.two $(bs[m - 2]!) $(bs[m - 1]!))
    for p in (List.range (m - 2)).reverse do
      br ← `(LeanScript.Branches.cons $(bs[p]!) $br)
    `(LeanScript.Term.union_casesOn $scrut $br)

/-- The generated definition of `#leanscript_get_cases I (named…)`, generating it if
    needed. -/
def ensureCases (id : Ident) (named : Array (Ident × Lean.Term)) : TermElabM Name := do
  let ind ← resolveInductive id
  withInstance ind named fun T key vars => do
    let prog? : Option ProgInfo ← currentProg?
    let plan ← (planType T prog?).run' (St.ofProg (vars.map (·.fvarId!)) prog?)
    let F ← mkFrame plan prog? vars
    let gkey : GenKey := { kind := "cases", name := ind, args := key, prog := F.prog?.map ProgInfo.name }
    if let some d ← cached? gkey then return d
    let decl ← F.declName ind (.mkSimple ind.getString!) (if F.prog?.isSome then `cases else `leanScriptCases)
    let gam := mkIdent `Γ
    let tau := mkIdent `τ
    let x := mkIdent `scrut
    let brIds : Array Ident := plan.ctors.map fun (c, _) =>
      mkIdent (.mkSimple ("on_" ++ c.getString!))
    let scrut ← match plan.data? with
      | some (b, j) => `(LeanScript.Term.data_out $(← brefStx F.c b) $(quote j) $x)
      | none => pure x
    let body ← casesBodyStx plan scrut (brIds.map fun b => ⟨b.raw⟩)
    let mut fty ← `(LeanScript.Term $(F.dT) $gam $tau)
    let mut fn := body
    for p in (List.range plan.ctors.size).reverse do
      let mut ctx : Lean.Term := gam
      for f in plan.ctors[p]!.2.reverse do
        ctx ← `($(← f.stx F.c F.varIds) :: $ctx)
      fty ← `(($(brIds[p]!) : LeanScript.Term $(F.dT) $ctx $tau) → $fty)
      fn ← `(fun $(brIds[p]!) => $fn)
    fty ← `(($x : LeanScript.Term $(F.dT) $gam $(← plan.layout.stx F.c F.varIds)) → $fty)
    fn ← `(fun $x => $fn)
    fty ← `(∀ {$tau : LeanScript.Ty $(F.ksT)}, $fty)
    fn ← `(fun {$tau} => $fn)
    let (fty', fn') ← F.close fty fn
    emitDef decl fty' fn'
    addEntry (.gen gkey decl)
    return decl

/-- The named arguments of the syntax. -/
def namedArgs (stx : Syntax) : Array (Ident × Lean.Term) :=
  stx.getArgs.map fun a => (⟨a[1]⟩, ⟨a[3]⟩)

/-! ## Elaborators -/

@[term_elab leanscriptGetTy]
def elabGetTy : TermElab := fun stx expected? => do
  let T ← elabType stx[1]
  synthesizeSyntheticMVarsNoPostponing
  let d ← ensureTy T
  elabTerm (mkCIdentFrom stx d) expected?

@[term_elab leanscriptGetCtor]
def elabGetCtor : TermElab := fun stx expected? => do
  let d ← ensureCtor ⟨stx[1]⟩ (namedArgs stx[2])
  elabTerm (mkCIdentFrom stx d) expected?

@[term_elab leanscriptGetCases]
def elabGetCases : TermElab := fun stx expected? => do
  let d ← ensureCases ⟨stx[1]⟩ (namedArgs stx[2])
  elabTerm (mkCIdentFrom stx d) expected?

@[command_elab leanscriptGetTyCmd]
def elabGetTyCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let T ← elabType stx[1]
  synthesizeSyntheticMVarsNoPostponing
  let d ← ensureTy T
  let some v := (← getEnv).find? d |>.bind (·.value?) | return
  logInfo m!"{MessageData.signature d} :={indentExpr v}"

@[command_elab leanscriptGetCtorCmd]
def elabGetCtorCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let d ← ensureCtor ⟨stx[1]⟩ (namedArgs stx[2])
  logInfo (MessageData.signature d)

@[command_elab leanscriptGetCasesCmd]
def elabGetCasesCmd : Command.CommandElab := fun stx => Command.liftTermElabM do
  let d ← ensureCases ⟨stx[1]⟩ (namedArgs stx[2])
  logInfo (MessageData.signature d)

end LeanScript.Gen

end
