module

public meta import LeanScript.ToTerm.ObjectExpr
public meta import LeanScript.Eval.Quote

@[expose] public section

meta section

/-!
# Building optimized terms

`LeanScript.Term` is optimized by construction: a constructor that could form a redex
carries a proof that it does not, stated in terms of the two indices every term carries
(its grade vector `LeanScript.Usage` and its root `LeanScript.Head`).  So the translation
cannot build a term node by node as a raw tree and hope: every node it builds must come
with its indices and, where the grammar asks for one, a proof that it is not a redex.

This module is where that happens.  `mkNode ctor args` is the one way the translation
builds a node of any family of the grammar's `mutual` block:

* it takes the arguments of the constructor **without** its indices and without the
  proofs about them — exactly the arguments the constructor had before the grammar was
  indexed — and reads the indices off the types of the subterms;
* when the node would be a redex, it does not build it: it **reduces** it, and builds
  what the redex reduces to instead.  A β-redex becomes a `let`; a `let` whose bound
  expression is a variable, a `fun` or a literal, or whose variable is used fewer than
  twice, is inlined; a dispatch on a literal or on a constructor takes its branch, with
  the fields bound; a forced delay is what it delays; an extern called on literals and
  closed values is **computed** — `Extern.eval` is run (compiled) on their values — and
  replaced by its value, written as a term (`LeanScript.Ty.quote`), when its result type
  is `LeanScript.TyWf.quotable`, and by `Term.extern` of it otherwise;
* otherwise it builds the node, with the proofs written by `decide`.

Inlining is a **substitution**, and a substitution can create new redexes (a variable
replaced by a `fun` in the function position of an application), so the substitution
rebuilds every node it passes through with `mkNode` again: what comes out is normal.  This
terminates because the language is total — it has no fixpoint, and the folds
(`nat_rec`, `array_rec`, `…_rec`) are never unrolled.

The substitution is generic: it reads, from the type of each constructor, which of its
arguments are the context, the indices, the subterms (and in which context each subterm
is written) and the proofs about the indices, so it walks every family of the grammar
without a clause per constructor.
-/

open Lean Meta

namespace LeanScript.ToTerm

/-! ## The families of the grammar, and what each argument of a constructor is -/

/-- The inductive families of the grammar's `mutual` block. -/
def grammarFamilies : Array Name := #[``LeanScript.Term, ``LeanScript.Terms,
  ``LeanScript.ArrayRecBases, ``LeanScript.Spine, ``LeanScript.TaggedUnionCases,
  ``LeanScript.CtorsWithPayloadCases, ``LeanScript.TaggedUnionCasesRest,
  ``LeanScript.TaggedUnionSomeCases, ``LeanScript.EnumCases, ``LeanScript.EnumSomeCases,
  ``LeanScript.TaggedUnionFoldCases, ``LeanScript.CtorsWithPayloadFoldCases,
  ``LeanScript.TaggedUnionFoldCasesRest, ``LeanScript.FoldKBranch,
  ``LeanScript.TaggedUnionFoldKCases, ``LeanScript.CtorsWithPayloadFoldKCases,
  ``LeanScript.TaggedUnionFoldKCasesRest, ``LeanScript.FamilyMemberValue,
  ``LeanScript.FamilyMemberCases, ``LeanScript.FamilyMemberSomeCases,
  ``LeanScript.FamilyMemberFoldCases, ``LeanScript.FamilyFoldCases,
  ``LeanScript.FamilyFoldKBranch, ``LeanScript.FamilyMemberFoldKCases,
  ``LeanScript.FamilyTaggedUnionFoldKCases, ``LeanScript.FamilyCtorsWithPayloadFoldKCases,
  ``LeanScript.FamilyTaggedUnionFoldKCasesRest, ``LeanScript.FamilyFoldKCases]

/-- Is this one of the grammar's families? -/
def isGrammarFamily (n : Name) : Bool := grammarFamilies.contains n

/-- What one argument of a constructor of the grammar is. -/
inductive Role where
  /-- the context `Γ` the node is written in -/
  | ctx
  /-- an index computed from the subterms: a grade vector, a head, a list of heads -/
  | index
  /-- a proof about the indices: that the node is not a redex -/
  | indexProof
  /-- a subterm, of one of the grammar's families -/
  | child
  /-- the variable of `Term.var` -/
  | var
  /-- anything else: a type, a schema, the payload of a literal, a proof about them -/
  | static
  deriving Inhabited, BEq, Repr

/-- What the arguments of a constructor are. -/
structure CtorInfo where
  /-- The constructor. -/
  ctor : Name
  /-- Its family. -/
  family : Name
  /-- The role of each of its fields (the arguments after the parameter `Sg`). -/
  roles : Array Role
  /-- The name of each of its fields. -/
  names : Array Name
  /-- For each field that is an index: the field of a subterm whose type carries it, and
      the position of it among the arguments of that type. -/
  indexSrc : Array (Option (Nat × Nat))
  deriving Inhabited

/-- The constructors analysed so far. -/
initialize ctorInfoRef : IO.Ref (Std.HashMap Name CtorInfo) ← IO.mkRef {}

/-- Is this the type of an index: a grade vector, a head or a list of heads? -/
def isIndexType (ty : Expr) : Bool :=
  ty.getAppFn.isConstOf ``LeanScript.Usage || ty.isConstOf ``LeanScript.Head ||
    (ty.isAppOfArity ``List 1 && ty.appArg!.isConstOf ``LeanScript.Head)

/-- The position, among all the arguments of a family (its parameter included), of the
    context `Γ`: the first argument of type `Ctx`. -/
def ctxPosOf (fam : Name) : MetaM Nat := do
  let ind ← getConstInfoInduct fam
  forallTelescopeReducing ind.type fun ys _ => do
    for i in [0:ys.size] do
      let t ← inferType ys[i]!
      if t.isConstOf ``LeanScript.Ctx ||
          (t.isAppOfArity ``List 1 && t.appArg!.isConstOf ``LeanScript.TyWf) then
        return i
    throwError "`#leanscript_to_term`: internal: {fam} has no context"

/-- What the arguments of the constructor `ctor` are, read off its type. -/
def ctorInfo (ctor : Name) : MetaM CtorInfo := do
  if let some i := (← ctorInfoRef.get)[ctor]? then return i
  let ci ← getConstInfoCtor ctor
  let gpos ← ctxPosOf ci.induct
  let info ← forallTelescope ci.type fun xs res => do
    let fields := xs.extract ci.numParams xs.size
    let ctxFv := res.getAppArgs[gpos]!
    let mut roles : Array Role := #[]
    let mut names : Array Name := #[]
    let mut idxFvs : Array Expr := #[]
    for x in fields do
      let ty ← inferType x
      names := names.push (← x.fvarId!.getUserName)
      if x == ctxFv then
        roles := roles.push .ctx
      else if isIndexType ty then
        roles := roles.push .index; idxFvs := idxFvs.push x
      else if ty.getAppFn.constName?.any isGrammarFamily then
        roles := roles.push .child
      else if ty.getAppFn.isConstOf ``LeanScript.DeBruijnProj then
        roles := roles.push .var
      else if (← isProp ty) && idxFvs.any (fun v => ty.containsFVar v.fvarId!) then
        roles := roles.push .indexProof
      else
        roles := roles.push .static
    let mut src : Array (Option (Nat × Nat)) := #[]
    for i in [0:fields.size] do
      if roles[i]! != .index then src := src.push none; continue
      let mut found := none
      for j in [0:fields.size] do
        if roles[j]! != .child then continue
        let args := (← inferType fields[j]!).getAppArgs
        if let some p := args.findIdx? (· == fields[i]!) then
          found := some (j, p); break
      src := src.push found
    return { ctor, family := ci.induct, roles, names, indexSrc := src : CtorInfo }
  ctorInfoRef.modify (·.insert ctor info)
  return info

/-! ## Reading a built term -/

/-- The type of a built node, as an application of its family. -/
def famTypeOf (t : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType t)
  if ty.getAppFn.constName?.any isGrammarFamily then return ty
  let ty ← whnfR ty
  if ty.getAppFn.constName?.any isGrammarFamily then return ty
  whnf ty

/-- The signature, context, grade vector, type and head of a term. -/
def termParts (t : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
  match (← famTypeOf t).getAppFnArgs with
  | (``LeanScript.Term, #[sg, γ, u, τ, k]) => return (sg, γ, u, τ, k)
  | _ => throwError "`#leanscript_to_term`: internal: not a term of the language: {t}"

/-- The type of a term. -/
def termTyOf (t : Expr) : MetaM Expr := do
  let (_, _, _, τ, _) ← termParts t
  instantiateMVars τ

/-- The head of a term: the name of the `LeanScript.Head` constructor its root is. -/
def headOf (t : Expr) : MetaM Name := do
  let (_, _, _, _, k) ← termParts t
  let k ← whnf k
  let some n := k.constName? | throwError "`#leanscript_to_term`: internal: no head: {k}"
  return n

/-- The node a term is, with any application of a cached translation or of a reducible
    constructor function unfolded until a constructor of the grammar is at the root. -/
def exposeNode (t : Expr) : MetaM Expr := do
  let isNode (e : Expr) : MetaM Bool := do
    let some n := e.getAppFn.constName? | return false
    match (← getEnv).find? n with
    | some (.ctorInfo ci) => return isGrammarFamily ci.induct
    | _ => return false
  let t := t.consumeMData.headBeta
  if ← isNode t then return t
  let t' ← whnfR t
  if ← isNode t' then return t'
  let t' ← whnf t
  if ← isNode t' then return t'
  throwError "`#leanscript_to_term`: internal: not a node of the grammar: {t}"

/-- The value of a closed natural-number expression. -/
partial def natValue (e : Expr) : MetaM Nat := do
  if let some n ← evalNat (← instantiateMVars e) then return n
  let e' ← whnf e
  if let some n ← evalNat e' then return n
  match e'.getAppFnArgs with
  | (``Nat.succ, #[m]) => return (← natValue m) + 1
  | (``Nat.zero, _) => return 0
  | _ => throwError "`#leanscript_to_term`: internal: not a number: {e}"

/-- The elements of a list expression, by weak head normalisation. -/
partial def listElems (e : Expr) : MetaM (List Expr) := do
  match (← whnf e).getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, a, as]) => return a :: (← listElems as)
  | _ => throwError "`#leanscript_to_term`: internal: not a list: {e}"

/-- The de Bruijn index a variable expression denotes. -/
partial def varIndex (x : Expr) : MetaM Nat := do
  let x := x.consumeMData
  match x.getAppFnArgs with
  | (``LeanScript.DeBruijnProj.head, _) => return 0
  | (``LeanScript.DeBruijnProj.tail, #[_, _, _, _, _, _, v]) => return (← varIndex v) + 1
  | _ =>
      let x' ← whnfR x
      if x' == x then
        let x'' ← whnf x
        if x'' == x then throwError "`#leanscript_to_term`: internal: not a variable: {x}"
        varIndex x''
      else varIndex x'

/-! ## Grades, evaluated

The grade of a variable in a grade vector, computed by following the definitions of
`LeanScript.Usage`: this is what `Term.letE` asks about its body. -/

/-- The grade of the variable of de Bruijn index `i` in the grade vector `u`. -/
partial def gradeOf (u : Expr) (i : Nat) : MetaM Nat := do
  let u := u.consumeMData
  match u.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← gradeOf a i) + (← gradeOf b i)
  | (``LeanScript.Usage.add, #[_, a, b]) => return (← gradeOf a i) + (← gradeOf b i)
  | (``OfNat.ofNat, _) => return 0
  | (``Zero.zero, _) => return 0
  | (``LeanScript.Usage.zero, _) => return 0
  | (``LeanScript.Usage.single, #[_, _, x]) => return if (← varIndex x) == i then 1 else 0
  | (``LeanScript.Usage.tail, #[_, _, v]) => gradeOf v (i + 1)
  | (``LeanScript.Usage.cons, #[_, _, k, v]) =>
      if i == 0 then natValue k else gradeOf v (i - 1)
  | (``LeanScript.Usage.smul, #[_, k, v]) => return (← natValue k) * (← gradeOf v i)
  | (``LeanScript.Usage.letU, #[_, _, a, b]) =>
      return (← gradeOf b 0) * (← gradeOf a i) + (← gradeOf b (i + 1))
  | (``LeanScript.Usage.drop, #[_, δ, v]) => gradeOf v (i + (← listElems δ).length)
  | (``LeanScript.Usage.dropN, #[_, _, n, v]) => gradeOf v (i + (← natValue n))
  | _ =>
      let u' ← whnfCore u
      if u' == u then throwError "`#leanscript_to_term`: internal: not a grade vector: {u}"
      gradeOf u' i

/-- How many times a term uses the variable of de Bruijn index `i`. -/
def usesOf (t : Expr) (i : Nat) : MetaM Nat := do
  let (_, _, u, _, _) ← termParts t
  gradeOf (← instantiateMVars u) i

/-! ## Variables -/

/-- The `i`-th cell of a context: the type there and the context after it. -/
partial def ctxCell (γ : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  match (← whnf γ).getAppFnArgs with
  | (``List.cons, #[_, t, rest]) => if i == 0 then return (t, rest) else ctxCell rest (i - 1)
  | _ => throwError "`#leanscript_to_term`: internal: variable {i} out of range of {γ}"

/-- The variable of de Bruijn index `i` of the context `γ`, and its type. -/
partial def mkVarIdx (γ : Expr) (i : Nat) : MetaM (Expr × Expr) := do
  let (t, rest) ← ctxCell γ 0
  if i == 0 then
    return (mkAppN (mkConst ``LeanScript.DeBruijnProj.head) #[tyE, tyE, idTyE, t, rest], t)
  let (v, b) ← mkVarIdx rest (i - 1)
  return (mkAppN (mkConst ``LeanScript.DeBruijnProj.tail) #[tyE, tyE, idTyE, t, rest, b, v], b)

/-- The term that reads the variable of de Bruijn index `i` of the context `γ`. -/
def mkVarTerm (sg γ : Expr) (i : Nat) : MetaM Expr := do
  let (x, τ) ← mkVarIdx γ i
  return mkAppN (mkConst ``LeanScript.Term.var) #[sg, γ, τ, x]

/-! ## Building a node -/

/-- A proof of a decidable proposition about closed indices, by `decide`. -/
def proveByDecide (p : Expr) : MetaM Expr := do
  mkDecideProof (← instantiateMVars p)

/-- Build the node `ctor` from its arguments **without** indices — the parameter `Sg` and
    then every field that is not an index or a proof about the indices, in order — reading
    the indices off the subterms and proving the side conditions by `decide`.  No check
    that the node is not a redex is made here: that is `mkNode`. -/
def buildNode (ctor : Name) (args : Array Expr) : MetaM Expr := do
  let info ← ctorInfo ctor
  let ci ← getConstInfoCtor ctor
  -- place the given arguments
  let mut vals : Array (Option Expr) := #[]
  let mut k := ci.numParams
  for r in info.roles do
    if r == .index || r == .indexProof then vals := vals.push none
    else
      let some a := args[k]? | throwError "`#leanscript_to_term`: internal: too few \
        arguments for {ctor}: {args}"
      vals := vals.push (some a); k := k + 1
  unless k == args.size do
    throwError "`#leanscript_to_term`: internal: too many arguments for {ctor}: {args}"
  -- the indices, off the subterms
  for i in [0:info.roles.size] do
    if info.roles[i]! == .index then
      let some (j, p) := info.indexSrc[i]!
        | throwError "`#leanscript_to_term`: internal: no source for an index of {ctor}"
      let some c := vals[j]! | throwError "`#leanscript_to_term`: internal: {ctor}"
      let cty ← famTypeOf c
      let some v := cty.getAppArgs[p]?
        | throwError "`#leanscript_to_term`: internal: {ctor}: {cty}"
      vals := vals.set! i (some (← instantiateMVars v))
  -- the proofs, now that their types are known
  let params := args.extract 0 ci.numParams
  let mut cur ← instantiateForall ci.type params
  let mut out := params
  for i in [0:info.roles.size] do
    let cur' ← whnf cur
    let .forallE _ d b _ := cur'
      | throwError "`#leanscript_to_term`: internal: {ctor} has too few arguments"
    let v ← match vals[i]! with
      | some v => pure v
      | none => proveByDecide d
    out := out.push v
    cur := b.instantiate1 v
  return mkAppN (mkConst ctor) out

/-! ## Substitution

`mapVars t γ d ρ` rebuilds `t` in the context `γ` (the new context of `t`'s root), where
`d` is the number of binders between the node being rebuilt and the root of the
substitution: a variable below `d` is bound inside and stays, and a variable `d + j` is
replaced by `ρ j` — another variable of the root's new context, or a term written there,
which is then shifted by `d`. -/

/-- What a variable of the root is replaced by. -/
inductive Image where
  /-- the variable of this de Bruijn index of the root's new context -/
  | var (j : Nat)
  /-- a term written in the root's new context -/
  | term (t : Expr)
  deriving Inhabited

/-- How many binders a context puts in front of `base`: the cells of `γ` until `base`. -/
partial def bindersBefore (γ base : Expr) (fuel : Nat := 100000) : MetaM Nat := do
  if fuel == 0 then throwError "`#leanscript_to_term`: internal: context {γ} is not over {base}"
  if γ == base then return 0
  let γ' ← whnf γ
  if γ' == base then return 0
  match γ'.getAppFnArgs with
  | (``List.cons, #[_, _, rest]) => return (← bindersBefore rest base (fuel - 1)) + 1
  | _ =>
      if ← isDefEq γ' base then return 0
      throwError "`#leanscript_to_term`: internal: context {γ} is not over {base}"

/-! ## Values, and externs called on them -/

/-- Is this head (the name of a `LeanScript.Head` constructor) a constructor applied to
    its fields, closed or not (`LeanScript.Head.isCtor`)? -/
def isCtorHead (k : Name) : Bool := k == ``LeanScript.Head.ctor || k == ``LeanScript.Head.val

/-- Is this head a literal or a closed value (`LeanScript.Head.isValue`)? -/
def isValueHead (k : Name) : Bool := k == ``LeanScript.Head.lit || k == ``LeanScript.Head.val

/-- Is the type `τ` quotable (`LeanScript.TyWf.quotable`): must an extern on values that
    answers with it be replaced by its value? -/
def isQuotable (τ : Expr) : MetaM Bool := do
  let b ← whnf (mkApp (mkConst ``LeanScript.TyWf.quotable) τ)
  if b.isConstOf ``Bool.true then return true
  if b.isConstOf ``Bool.false then return false
  throwError "`#leanscript_to_term`: internal: cannot decide whether {τ} is quotable"

/-- Run a closed expression of type `Option LeanScript.Quoted` (compiled). -/
def evalQuoted (e : Expr) : MetaM (Option LeanScript.Quoted) := do
  let ty := mkApp (mkConst ``Option [0]) (mkConst ``LeanScript.Quoted)
  unsafe evalExpr (Option LeanScript.Quoted) ty e

/-- Run a closed expression of type `Option (Option LeanScript.Quoted)` (compiled). -/
def evalQuotedChecked (e : Expr) : MetaM (Option (Option LeanScript.Quoted)) := do
  let ty := mkApp (mkConst ``Option [0])
    (mkApp (mkConst ``Option [0]) (mkConst ``LeanScript.Quoted))
  unsafe evalExpr (Option (Option LeanScript.Quoted)) ty e

/-- Run a closed boolean expression (compiled). -/
def evalBool (e : Expr) : MetaM Bool :=
  unsafe evalExpr Bool (mkConst ``Bool) e

/-- The value of an extern on values whose result type `τ` is quotable, as the term that
    denotes it: `Extern.eval` is run (compiled), and its value read back
    (`LeanScript.Extern.quote`). -/
def quoteExtern (τ e : Expr) : MetaM LeanScript.Quoted := do
  match ← evalQuoted (mkApp2 (mkConst ``LeanScript.Extern.quote) τ e) with
  | some q => return q
  | none => throwError "`#leanscript_to_term`: internal: the value of {e} cannot be written"

mutual

/-- The node `ctor` from its arguments without indices: reduced, if it is a redex; built
    as it stands otherwise.  **The** constructor of the translation. -/
partial def mkNode (ctor : Name) (args : Array Expr) : MetaM Expr := do
  if let some t ← reduceRedex? ctor args then return t
  buildNode ctor args

/-- Rebuild `t` in the new context `γ`; see this section's header. -/
partial def mapVars (t : Expr) (γ : Expr) (d : Nat) (ρ : Nat → MetaM Image) : MetaM Expr := do
  let t ← exposeNode t
  let .const ctor _ := t.getAppFn | unreachable!
  let args := t.getAppArgs
  let ci ← getConstInfoCtor ctor
  let sg := args[0]!
  if ctor == ``LeanScript.Term.var then
    let i ← varIndex args[3]!
    if i < d then return ← mkVarTerm sg γ i
    match ← ρ (i - d) with
    | .var j => return ← mkVarTerm sg γ (j + d)
    | .term u => return ← if d == 0 then pure u else shiftBy u γ d
  let info ← ctorInfo ctor
  -- walk the telescope with the old arguments, the context replaced
  let params := args.extract 0 ci.numParams
  let mut cur ← instantiateForall ci.type params
  let mut newArgs := params
  for i in [0:info.roles.size] do
    let old := args[ci.numParams + i]!
    let cur' ← whnf cur
    let .forallE _ dom b _ := cur'
      | throwError "`#leanscript_to_term`: internal: {ctor} has too few arguments"
    let v ← match info.roles[i]! with
      | .ctx => pure γ
      | .child =>
          -- the context this subterm is written in, and how many binders it adds
          let γc := (← famTypeOf' dom).2
          let n ← bindersBefore γc γ
          mapVars old γc (d + n) ρ
      | _ => pure old
    match info.roles[i]! with
    | .index | .indexProof => pure ()
    | _ => newArgs := newArgs.push v
    cur := b.instantiate1 (if info.roles[i]! == .ctx then γ else
      if info.roles[i]! == .child then v else old)
  mkNode ctor newArgs

/-- The context argument of a family type, and the type itself. -/
partial def famTypeOf' (ty : Expr) : MetaM (Expr × Expr) := do
  let ty ← instantiateMVars ty
  let ty ← if ty.getAppFn.constName?.any isGrammarFamily then pure ty else whnf ty
  let some fam := ty.getAppFn.constName? | throwError "`#leanscript_to_term`: internal: {ty}"
  let p ← ctxPosOf fam
  return (ty, ty.getAppArgs[p]!)

/-- Weaken `t` (written in the context `γ` minus its `d` innermost binders) into `γ`. -/
partial def shiftBy (t : Expr) (γ : Expr) (d : Nat) : MetaM Expr :=
  mapVars t γ 0 fun j => pure (.var (j + d))

/-- `b[a/0]`: `b` is written in `σ :: γ`, `a` in `γ`; the result is written in `γ`. -/
partial def subst0 (b a γ : Expr) : MetaM Expr :=
  mapVars b γ 0 fun j => pure (if j == 0 then .term a else .var (j - 1))

/-- Bind the terms `es` (all written in `γ`) as the innermost variables of `body`, the
    first of them at de Bruijn index `0`: a `let` for each, which `mkNode` inlines where
    the grammar asks it to. -/
partial def bindMany (sg γ : Expr) (body : Expr) (es : Array Expr) : MetaM Expr := do
  if es.isEmpty then
    -- the body's context is `[] ++ γ`, or `γ` itself: rebuild it in `γ`
    return ← mapVars body γ 0 fun j => pure (.var j)
  let n := es.size
  let eLast := es[n - 1]!
  let σ ← termTyOf eLast
  let γ' := consCtxE σ γ
  let mut rest : Array Expr := #[]
  for e in es.extract 0 (n - 1) do
    rest := rest.push (← shiftBy e γ' 1)
  let body' ← bindMany sg γ' body rest
  let τ ← termTyOf body'
  mkNode ``LeanScript.Term.letE #[sg, γ, σ, τ, eLast, body']

/-- The terms of a spine, in order. -/
partial def spineElems (sp : Expr) : MetaM (Array Expr) := do
  let sp ← exposeNode sp
  match sp.getAppFnArgs with
  | (``LeanScript.Spine.nil, _) => return #[]
  | (``LeanScript.Spine.cons, args) => return #[args[args.size - 2]!] ++
      (← spineElems args[args.size - 1]!)
  | _ => throwError "`#leanscript_to_term`: internal: not a spine: {sp}"

/-- The argument of a node that the constructor's type names `n`. -/
partial def argNamed (ctor : Name) (args : Array Expr) (n : String) : MetaM Expr := do
  let info ← ctorInfo ctor
  let ci ← getConstInfoCtor ctor
  let mut k := ci.numParams
  for i in [0:info.roles.size] do
    let r := info.roles[i]!
    if r == .index || r == .indexProof then continue
    if info.names[i]!.eraseMacroScopes.toString == n then return args[k]!
    k := k + 1
  throwError "`#leanscript_to_term`: internal: {ctor} has no argument {n}"

/-- The last argument of an exposed node: the payload of a literal, the subterm of a
    delay or of a one-field form. -/
partial def lastArg (t : Expr) : MetaM Expr := do
  let t ← exposeNode t
  return t.getAppArgs.back!

/-- The branch of the tagged-union dispatch `cases` for constructor `t`. -/
partial def tuBranch (cases : Expr) (t : Nat) : MetaM Expr := do
  let cases ← exposeNode cases
  let args := cases.getAppArgs
  match cases.getAppFn.constName!, t with
  | ``LeanScript.TaggedUnionCases.payloadFirst, 0 => return args[args.size - 3]!
  | ``LeanScript.TaggedUnionCases.payloadFirst, 1 => return args[args.size - 2]!
  | ``LeanScript.TaggedUnionCases.payloadFirst, n + 2 => tuBranch args.back! n
  | ``LeanScript.TaggedUnionCases.skip, 0 => return args[args.size - 2]!
  | ``LeanScript.TaggedUnionCases.skip, n + 1 => tuBranch args.back! n
  | ``LeanScript.CtorsWithPayloadCases.here, 0 => return args[args.size - 2]!
  | ``LeanScript.CtorsWithPayloadCases.here, n + 1 => tuBranch args.back! n
  | ``LeanScript.CtorsWithPayloadCases.skip, 0 => return args[args.size - 2]!
  | ``LeanScript.CtorsWithPayloadCases.skip, n + 1 => tuBranch args.back! n
  | ``LeanScript.TaggedUnionCasesRest.cons, 0 => return args[args.size - 2]!
  | ``LeanScript.TaggedUnionCasesRest.cons, n + 1 => tuBranch args.back! n
  | c, _ => throwError "`#leanscript_to_term`: internal: no branch {t} in {c}"

/-- The branch of the partial dispatch `cases` for constructor `t`, if it has one. -/
partial def tuSomeBranch? (cases : Expr) (t : Nat) : MetaM (Option Expr) := do
  let cases ← exposeNode cases
  let c := cases.getAppFn.constName!
  let t' ← natValue (← argNamed c cases.getAppArgs "t")
  let branch ← argNamed c cases.getAppArgs "branch"
  if t' == t then return some branch
  if c == ``LeanScript.TaggedUnionSomeCases.cons then
    tuSomeBranch? (← argNamed c cases.getAppArgs "rest") t
  else return none

/-- The branch of the enum dispatch `cases` for constructor `i`. -/
partial def enumBranch (cases : Expr) (i : Nat) : MetaM Expr := do
  let cases ← exposeNode cases
  let args := cases.getAppArgs
  match cases.getAppFn.constName!, i with
  | ``LeanScript.EnumCases.three, j =>
      match j with
      | 0 => return args[args.size - 3]!
      | 1 => return args[args.size - 2]!
      | _ => return args[args.size - 1]!
  | ``LeanScript.EnumCases.cons, 0 => return args[args.size - 2]!
  | ``LeanScript.EnumCases.cons, n + 1 => enumBranch args.back! n
  | c, _ => throwError "`#leanscript_to_term`: internal: no branch {i} in {c}"

/-- The branch of the partial enum dispatch `cases` for constructor `i`, if it has one. -/
partial def enumSomeBranch? (cases : Expr) (i : Nat) : MetaM (Option Expr) := do
  let cases ← exposeNode cases
  let c := cases.getAppFn.constName!
  let j ← natValue (mkApp2 (mkConst ``Fin.val) (← inferFinBound (← argNamed c cases.getAppArgs "i"))
    (← argNamed c cases.getAppArgs "i"))
  let branch ← argNamed c cases.getAppArgs "branch"
  if j == i then return some branch
  if c == ``LeanScript.EnumSomeCases.cons then
    enumSomeBranch? (← argNamed c cases.getAppArgs "rest") i
  else return none

/-- The bound `n` of an element of `Fin n`. -/
partial def inferFinBound (i : Expr) : MetaM Expr := do
  match (← whnf (← inferType i)).getAppFnArgs with
  | (``Fin, #[n]) => return n
  | _ => throwError "`#leanscript_to_term`: internal: not a `Fin`: {i}"

/-- The value of an element of a `Fin`. -/
partial def finValue (i : Expr) : MetaM Nat := do
  natValue (mkApp2 (mkConst ``Fin.val) (← inferFinBound i) i)

/-- The field literal of a primitive `casesOn` taken on the literal `lit`: the terms its
    branch binds, innermost first. -/
partial def primFields (ctor : Name) (sg γ lit : Expr) : MetaM (Array Expr) := do
  let v ← lastArg lit
  let mk (c : Name) (payload : Expr) : MetaM Expr := buildNode c #[sg, γ, payload]
  let bv (w : Nat) (fn : Name) : MetaM Expr := do
    let prf ← proveByDecide (← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit w])
    buildNode ``LeanScript.Term.bitvec_mk #[sg, γ, mkNatLit w, prf, mkApp (mkConst fn) v]
  match ctor with
  | ``LeanScript.Term.uint8_casesOn => return #[← bv 8 ``UInt8.toBitVec]
  | ``LeanScript.Term.uint16_casesOn => return #[← bv 16 ``UInt16.toBitVec]
  | ``LeanScript.Term.uint32_casesOn => return #[← bv 32 ``UInt32.toBitVec]
  | ``LeanScript.Term.uint64_casesOn => return #[← bv 64 ``UInt64.toBitVec]
  | ``LeanScript.Term.int8_casesOn =>
      return #[← mk ``LeanScript.Term.uint8_mk (mkApp (mkConst ``Int8.toUInt8) v)]
  | ``LeanScript.Term.int16_casesOn =>
      return #[← mk ``LeanScript.Term.uint16_mk (mkApp (mkConst ``Int16.toUInt16) v)]
  | ``LeanScript.Term.int32_casesOn =>
      return #[← mk ``LeanScript.Term.uint32_mk (mkApp (mkConst ``Int32.toUInt32) v)]
  | ``LeanScript.Term.int64_casesOn =>
      return #[← mk ``LeanScript.Term.uint64_mk (mkApp (mkConst ``Int64.toUInt64) v)]
  | ``LeanScript.Term.char_casesOn =>
      return #[← mk ``LeanScript.Term.uint32_mk (mkApp (mkConst ``Char.val) v)]
  | ``LeanScript.Term.stringPosRaw_casesOn =>
      return #[← mk ``LeanScript.Term.nat_mk (mkApp (mkConst ``String.Pos.Raw.byteIdx) v)]
  | ``LeanScript.Term.stringPos_casesOn =>
      return #[← mk ``LeanScript.Term.stringPosRaw_mk (← mkAppM ``String.Pos.offset #[v])]
  | ``LeanScript.Term.substringRaw_casesOn =>
      return #[← mk ``LeanScript.Term.string_mk (mkApp (mkConst ``Substring.Raw.str) v),
        ← mk ``LeanScript.Term.stringPosRaw_mk (mkApp (mkConst ``Substring.Raw.startPos) v),
        ← mk ``LeanScript.Term.stringPosRaw_mk (mkApp (mkConst ``Substring.Raw.stopPos) v)]
  | ``LeanScript.Term.float_casesOn =>
      return #[← mk ``LeanScript.Term.floatModel_mk (mkApp (mkConst ``Float.toModel) v)]
  | ``LeanScript.Term.float32_casesOn =>
      return #[← mk ``LeanScript.Term.float32Model_mk (mkApp (mkConst ``Float32.toModel) v)]
  | ``LeanScript.Term.floatModel_casesOn =>
      return #[← mk ``LeanScript.Term.uint64_mk (mkApp (mkConst ``Float.Model.toBits) v)]
  | ``LeanScript.Term.float32Model_casesOn =>
      return #[← mk ``LeanScript.Term.uint32_mk (mkApp (mkConst ``Float32.Model.toBits) v)]
  | _ => throwError "`#leanscript_to_term`: internal: {ctor} is not a primitive dispatch"

/-- The elements of an array, in order. -/
partial def termsElems (ts : Expr) : MetaM (Array Expr) := do
  let ts ← exposeNode ts
  match ts.getAppFnArgs with
  | (``LeanScript.Terms.nil, _) => return #[]
  | (``LeanScript.Terms.cons, args) => return #[args[args.size - 2]!] ++
      (← termsElems args[args.size - 1]!)
  | _ => throwError "`#leanscript_to_term`: internal: not the elements of an array: {ts}"

/-- The value of a term that is a literal or a closed value, as an expression of its
    denotation: the payload of a literal, the Lean array of the values of an array's
    elements, and the value a delay stands for. -/
partial def valueDen (t : Expr) : MetaM Expr := do
  let n ← exposeNode t
  match n.getAppFn.constName! with
  | ``LeanScript.Term.array_mk =>
      let σ := n.getAppArgs[2]!
      let ty := mkApp (mkConst ``LeanScript.TyWf.Den) σ
      let ds ← (← termsElems (← lastArg n)).mapM valueDen
      return mkApp2 (mkConst ``List.toArray [0]) ty (← mkListLit ty ds.toList)
  | ``LeanScript.Term.thunk_mk | ``LeanScript.Term.lazy_mk => valueDen (← lastArg n)
  | _ => lastArg n

/-- The values of a spine of literals and closed values, as the nested pairs
    `TyWf.DenList` is. -/
partial def valueDens (sp : Expr) : MetaM Expr := do
  let es ← spineElems sp
  let mut acc := mkConst ``PUnit.unit [Level.one]
  for e in es.reverse do
    acc ← mkAppM ``Prod.mk #[← valueDen e, acc]
  return acc

/-- The term that denotes a computed value of type `τ`, from its description. -/
partial def quotedTerm (sg γ τ : Expr) : LeanScript.Quoted → MetaM Expr
  | .lit c p => return mkAppN (mkConst c) #[sg, γ, p]
  | .bitvec w p => do
      let wE := mkNatLit w
      let h ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit 0, wE])
      return mkAppN (mkConst ``LeanScript.Term.bitvec_mk) #[sg, γ, wE, h, p]
  | .enum i => do
      let s ← mkFreshExprMVar (mkConst ``LeanScript.LeanEnumSchema)
      unless ← isDefEq τ (mkApp (mkConst ``LeanScript.TyWf.enum) s) do
        throwError "`#leanscript_to_term`: internal: {τ} is not an enum"
      let s ← instantiateMVars s
      let n := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      let h ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, n])
      return mkAppN (mkConst ``LeanScript.Term.enum_mk)
        #[sg, γ, s, mkApp3 (mkConst ``Fin.mk) n (mkNatLit i) h]
  | .array xs => do
      let σ ← mkFreshExprMVar tyE
      unless ← isDefEq τ (mkApp (mkConst ``LeanScript.TyWf.array) σ) do
        throwError "`#leanscript_to_term`: internal: {τ} is not an array type"
      let σ ← instantiateMVars σ
      let mut ts ← mkNode ``LeanScript.Terms.nil #[sg, γ, σ]
      for x in xs.reverse do
        ts ← mkNode ``LeanScript.Terms.cons #[sg, γ, σ, ← quotedTerm sg γ σ x, ts]
      mkNode ``LeanScript.Term.array_mk #[sg, γ, σ, ts]
  | .delay lazy x => do
      let σ ← mkFreshExprMVar tyE
      let former := if lazy then ``LeanScript.TyWf.lazy else ``LeanScript.TyWf.thunk
      unless ← isDefEq τ (mkApp (mkConst former) σ) do
        throwError "`#leanscript_to_term`: internal: {τ} is not a delay"
      let σ ← instantiateMVars σ
      let ctor := if lazy then ``LeanScript.Term.lazy_mk else ``LeanScript.Term.thunk_mk
      mkNode ctor #[sg, γ, σ, ← quotedTerm sg γ σ x]

/-- The extern `e` (an entry of the catalogue applied to values) of result type `τ`, as a
    term: its value when that can be written (`LeanScript.TyWf.quotable`), and
    `Term.extern e` otherwise. -/
partial def mkExternNode (sg γ τ e : Expr) : MetaM Expr := do
  if ← isQuotable τ then
    return ← quotedTerm sg γ τ (← quoteExtern τ e)
  let h ← mkDecideProof (← mkEq (mkApp (mkConst ``LeanScript.TyWf.quotable) τ)
    (mkConst ``Bool.false))
  buildNode ``LeanScript.Term.extern #[sg, γ, τ, e, h]

/-- If the node `ctor args` is a redex, what it reduces to. -/
partial def reduceRedex? (ctor : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let arg (n : String) : MetaM Expr := argNamed ctor args n
  let sg := args[0]!
  match ctor with
  | ``LeanScript.Term.ap =>
      let f ← arg "f"
      unless (← headOf f) == ``LeanScript.Head.lam do return none
      let body ← lastArg f
      let a ← arg "a"
      let γ ← arg "Γ"
      let σ ← termTyOf a
      let τ ← termTyOf body
      some <$> mkNode ``LeanScript.Term.letE #[sg, γ, σ, τ, a, body]
  | ``LeanScript.Term.letE =>
      let e ← arg "e"
      let b ← arg "b"
      let k ← headOf e
      if (k == ``LeanScript.Head.comp || isCtorHead k) && (← usesOf b 0) ≥ 2 then
        return none
      some <$> subst0 b e (← arg "Γ")
  | ``LeanScript.Term.bool_casesOn =>
      let c ← arg "c"
      unless (← headOf c) == ``LeanScript.Head.lit do return none
      let v ← whnf (← lastArg c)
      if v.isConstOf ``Bool.true then some <$> rebase (← arg "t") (← arg "Γ")
      else if v.isConstOf ``Bool.false then some <$> rebase (← arg "e") (← arg "Γ")
      else throwError "`#leanscript_to_term`: internal: not a boolean: {v}"
  | ``LeanScript.Term.nat_casesOn =>
      let n ← arg "n"
      unless (← headOf n) == ``LeanScript.Head.lit do return none
      let γ ← arg "Γ"
      let v ← natValue (← lastArg n)
      if v == 0 then return some (← rebase (← arg "z") γ)
      let pred ← buildNode ``LeanScript.Term.nat_mk #[sg, γ, mkNatLit (v - 1)]
      some <$> subst0 (← arg "s") pred γ
  | ``LeanScript.Term.int_casesOn =>
      let i ← arg "i"
      unless (← headOf i) == ``LeanScript.Head.lit do return none
      let γ ← arg "Γ"
      let v ← whnf (← lastArg i)
      match v.getAppFnArgs with
      | (``Int.ofNat, #[m]) =>
          some <$> subst0 (← arg "ofNat") (← buildNode ``LeanScript.Term.nat_mk #[sg, γ, m]) γ
      | (``Int.negSucc, #[m]) =>
          some <$> subst0 (← arg "negSucc") (← buildNode ``LeanScript.Term.nat_mk #[sg, γ, m]) γ
      | _ => throwError "`#leanscript_to_term`: internal: not an integer: {v}"
  | ``LeanScript.Term.uint8_casesOn | ``LeanScript.Term.uint16_casesOn
  | ``LeanScript.Term.uint32_casesOn | ``LeanScript.Term.uint64_casesOn
  | ``LeanScript.Term.int8_casesOn | ``LeanScript.Term.int16_casesOn
  | ``LeanScript.Term.int32_casesOn | ``LeanScript.Term.int64_casesOn
  | ``LeanScript.Term.char_casesOn | ``LeanScript.Term.stringPosRaw_casesOn
  | ``LeanScript.Term.stringPos_casesOn | ``LeanScript.Term.substringRaw_casesOn
  | ``LeanScript.Term.float_casesOn | ``LeanScript.Term.float32_casesOn
  | ``LeanScript.Term.floatModel_casesOn | ``LeanScript.Term.float32Model_casesOn =>
      let x ← arg "x"
      unless (← headOf x) == ``LeanScript.Head.lit do return none
      let γ ← arg "Γ"
      some <$> bindMany sg γ (← arg "b") (← primFields ctor sg γ x)
  | ``LeanScript.Term.lazy_force | ``LeanScript.Term.thunk_force =>
      let e ← arg "e"
      unless isCtorHead (← headOf e) do return none
      some <$> lastArg e
  | ``LeanScript.Term.array_casesOn =>
      let a ← arg "a"
      unless isCtorHead (← headOf a) do return none
      let γ ← arg "Γ"
      let ts ← exposeNode (← lastArg a)
      match ts.getAppFnArgs with
      | (``LeanScript.Terms.nil, _) => some <$> rebase (← arg "z") γ
      | (``LeanScript.Terms.cons, targs) =>
          let hd := targs[targs.size - 2]!
          let tl := targs[targs.size - 1]!
          let tlArr ← mkNode ``LeanScript.Term.array_mk #[sg, γ, ← arg "σ", tl]
          some <$> bindMany sg γ (← arg "s") #[hd, tlArr]
      | _ => throwError "`#leanscript_to_term`: internal: not the elements of an array: {ts}"
  | ``LeanScript.Term.enum_casesOn =>
      let e ← arg "e"
      unless (← headOf e) == ``LeanScript.Head.lit do return none
      let i ← finValue (← lastArg e)
      some <$> rebase (← enumBranch (← arg "cases") i) (← arg "Γ")
  | ``LeanScript.Term.enum_casesOnWithDefault =>
      let e ← arg "e"
      unless (← headOf e) == ``LeanScript.Head.lit do return none
      let i ← finValue (← lastArg e)
      match ← enumSomeBranch? (← arg "cases") i with
      | some b => some <$> rebase b (← arg "Γ")
      | none => some <$> rebase (← arg "dflt") (← arg "Γ")
  | ``LeanScript.Term.record_casesOn =>
      let r ← arg "r"
      unless isCtorHead (← headOf r) do return none
      let γ ← arg "Γ"
      some <$> bindMany sg γ (← arg "body") (← spineElems (← lastArg r))
  | ``LeanScript.Term.recObject_casesOn =>
      let x ← arg "x"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      some <$> bindMany sg γ (← arg "body") (← spineElems (← lastArg x))
  | ``LeanScript.Term.recAlias_casesOn =>
      let x ← arg "x"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      some <$> bindMany sg γ (← arg "body") #[← lastArg x]
  | ``LeanScript.Term.taggedUnion_casesOn | ``LeanScript.Term.recTaggedUnion_casesOn =>
      let x ← arg "x"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      let xn ← exposeNode x
      let t ← natValue (← argNamed xn.getAppFn.constName! xn.getAppArgs "t")
      some <$> bindMany sg γ (← tuBranch (← arg "cases") t) (← spineElems (← lastArg x))
  | ``LeanScript.Term.taggedUnion_casesOnWithDefault
  | ``LeanScript.Term.recTaggedUnion_casesOnWithDefault =>
      let x ← arg "v"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      let xn ← exposeNode x
      let t ← natValue (← argNamed xn.getAppFn.constName! xn.getAppArgs "t")
      match ← tuSomeBranch? (← arg "cases") t with
      | some b => some <$> bindMany sg γ b (← spineElems (← lastArg x))
      | none => some <$> rebase (← arg "dflt") γ
  | ``LeanScript.Term.mutualRecursiveFamily_casesOn =>
      let x ← arg "x"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      let value ← exposeNode (← lastArg x)
      let cases ← exposeNode (← arg "cases")
      match value.getAppFn.constName!, cases.getAppFn.constName! with
      | ``LeanScript.FamilyMemberValue.ctors, ``LeanScript.FamilyMemberCases.ctors =>
          let t ← natValue (← argNamed ``LeanScript.FamilyMemberValue.ctors value.getAppArgs "t")
          some <$> bindMany sg γ (← tuBranch (← lastArg cases) t)
            (← spineElems (← lastArg value))
      | ``LeanScript.FamilyMemberValue.record, ``LeanScript.FamilyMemberCases.record =>
          some <$> bindMany sg γ (← lastArg cases) (← spineElems (← lastArg value))
      | ``LeanScript.FamilyMemberValue.alias, ``LeanScript.FamilyMemberCases.alias =>
          some <$> bindMany sg γ (← lastArg cases) #[← lastArg value]
      | a, b => throwError "`#leanscript_to_term`: internal: {a} dispatched by {b}"
  | ``LeanScript.Term.mutualRecursiveFamily_casesOnWithDefault =>
      let x ← arg "x"
      unless isCtorHead (← headOf x) do return none
      let γ ← arg "Γ"
      let value ← exposeNode (← lastArg x)
      let cases ← exposeNode (← arg "cases")
      let t ← natValue (← argNamed ``LeanScript.FamilyMemberValue.ctors value.getAppArgs "t")
      match ← tuSomeBranch? (← argNamed cases.getAppFn.constName! cases.getAppArgs "cases") t with
      | some b => some <$> bindMany sg γ b (← spineElems (← lastArg value))
      | none => some <$> rebase (← arg "dflt") γ
  | ``LeanScript.Term.extern =>
      -- an extern on values whose value can be written: the value
      let τ ← arg "τ"
      unless ← isQuotable τ do return none
      some <$> quotedTerm sg (← arg "Γ") τ (← quoteExtern τ (← arg "e"))
  | ``LeanScript.Term.externCall =>
      let sp ← arg "args"
      unless ← allValues sp do return none
      let call ← arg "call"
      let e := (mkApp call (← valueDens sp)).headBeta
      some <$> mkExternNode sg (← arg "Γ") (← arg "τ") e
  | ``LeanScript.Term.externCallChecked =>
      let sp ← arg "args"
      unless ← allValues sp do return none
      let call ← arg "call"
      let τ ← arg "τ"
      let γ ← arg "Γ"
      let opt := (mkApp call (← valueDens sp)).headBeta
      if ← isQuotable τ then
        -- decided and computed at once, compiled
        match ← evalQuotedChecked (mkApp2 (mkConst ``LeanScript.Extern.quoteChecked) τ opt) with
        | some (some q) => return some (← quotedTerm sg γ τ q)
        | some none => throwError "`#leanscript_to_term`: internal: the value of {opt} \
            cannot be written"
        | none => return some (← rebase (← arg "fallback") γ)
      let r ← whnf opt
      match r.getAppFnArgs with
      | (``Option.some, #[_, e]) => some <$> mkExternNode sg γ τ e
      | (``Option.none, _) => some <$> rebase (← arg "fallback") γ
      | _ =>
          -- the decision does not unfold here: run it, and take the entry out of the option
          unless ← evalBool (← mkAppM ``Option.isSome #[opt]) do
            return some (← rebase (← arg "fallback") γ)
          let h ← mkDecideProof (← mkEq (← mkAppM ``Option.isSome #[opt]) (mkConst ``Bool.true))
          some <$> mkExternNode sg γ τ (← mkAppM ``Option.get #[opt, h])
  | _ => return none

/-- Is every term of this spine a literal or a closed value? -/
partial def allValues (sp : Expr) : MetaM Bool := do
  for e in ← spineElems sp do
    unless isValueHead (← headOf e) do return false
  return true

/-- A subterm written in a context defeq to `γ` (a branch that binds nothing), rebuilt in
    `γ` itself. -/
partial def rebase (t γ : Expr) : MetaM Expr := do
  let (_, γt, _, _, _) ← termParts t
  if γt == γ then return t
  mapVars t γ 0 fun j => pure (.var j)

end

end LeanScript.ToTerm

end

end
