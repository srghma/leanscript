module

public meta import LeanScript.ToTerm.ObjectExpr
public meta import LeanScript.ToTerm.TyView
public meta import LeanScript.Eval.Quote
public meta import LeanScript.Eval

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
  twice, is inlined — a use under a `fun`, in a fold's branch or in a `lazy` counts as
  many (`LeanScript.Usage.many`), so inlining never moves a computation to where it
  would run more often; a `let` in the function position of an application, in the
  bound expression of another `let` (of a `fun`) or in a scrutinee (of a constructor)
  is floated out first, since a `let` has the head of its body and hides the redex; a dispatch on a literal or on a constructor takes its branch, with
  the fields bound; a forced delay is what it delays; an extern called on literals and
  closed values is **computed** — `Extern.eval` is run (compiled) on their values — and
  replaced by its value, written as a term (`LeanScript.Ty.quote`), when its result type
  is `LeanScript.TyWf.quotable`, and by `Term.extern` of it otherwise; an application of
  a dispatch one of whose branches is a `fun` (`LeanScript.Head.caseIntro`) is moved into
  the branches (`pushArg`: the argument is bound by a `let` first unless it is a variable
  or a literal), and so is a force of a dispatch one of whose branches is a delay
  (`mapBranches`); a fold (`nat_rec`, `array_rec`) whose branch reads none of its
  answers is written as the nested case analysis it is (`natRecCasesAt`,
  `arrayRecCasesAt`), and a depth-`0` fold whose branch is the answer it is given is its
  base value; a dispatch on a value with one constructor (a record, a newtype, a primitive
  wrapper) whose branch reads none of the fields is its branch (`oneCtorUnused?`);
  a dispatch on a dispatch whose branches are all known (literals, constructors, values,
  or such dispatches — `LeanScript.Head.caseCtor`) is pushed into the branches of the
  inner one, where it reduces (case-of-case, `caseOfCase?`); `if c then true else false`
  is `c`; and a **closed computation** — one that reads no variable and no top-level
  declaration, at a type whose values can be written as terms
  (`LeanScript.Head.closedComp`) — is **run** where the term is written (`Term.eval`,
  compiled) and replaced by its value (`closedValue?`): `sumTo 5` is `10`, and
  `fun x => x + sumTo 4` is `fun x => x + 6`;
* beyond what the grammar rejects, it also η-reduces `fun x => f x` to `f` (when `f` does
  not read `x`), and turns a depth-`0` fold at a function type whose step is a tail call
  on a new accumulator — `go (k + 1) a = go k (F k a)` — into a fold at the
  accumulator's type, one closure instead of one per step (`accLoop?`);
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
  let some n := k.getAppFn.constName? | throwError "`#leanscript_to_term`: internal: no head: {k}"
  return n

/-- The value of a boolean literal, read off its head (`LeanScript.Head.bool`); `none` for
    any other term. -/
def boolHeadOf? (t : Expr) : MetaM (Option Bool) := do
  let (_, _, _, _, k) ← termParts t
  let k ← whnf k
  let (``LeanScript.Head.bool, #[b]) := k.getAppFnArgs | return none
  let b ← whnf b
  if b.isConstOf ``Bool.true then return some true
  if b.isConstOf ``Bool.false then return some false
  return none

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
  | (``LeanScript.Usage.global, _) => return 0
  | (``LeanScript.Usage.single, #[_, _, x]) => return if (← varIndex x) == i then 1 else 0
  | (``LeanScript.Usage.tail, #[_, _, v]) => gradeOf v (i + 1)
  | (``LeanScript.Usage.cons, #[_, _, k, v]) =>
      if i == 0 then natValue k else gradeOf v (i - 1)
  | (``LeanScript.Usage.smul, #[_, k, v]) => return (← natValue k) * (← gradeOf v i)
  | (``LeanScript.Usage.many, #[_, v]) => return 2 * (← gradeOf v i)
  | (``LeanScript.Usage.letU, #[_, _, a, b]) =>
      return (← gradeOf b 0) * (← gradeOf a i) + (← gradeOf b (i + 1))
  | (``LeanScript.Usage.drop, #[_, δ, v]) => gradeOf v (i + (← listElems δ).length)
  | (``LeanScript.Usage.dropN, #[_, _, n, v]) => gradeOf v (i + (← natValue n))
  | _ =>
      let u' ← whnfCore u
      if u' == u then throwError "`#leanscript_to_term`: internal: not a grade vector: {u}"
      gradeOf u' i

/-- The number of uses of free names in the grade vector `u` (`LeanScript.Usage.free`),
    computed by following the definitions of `LeanScript.Usage`, as `gradeOf` does: a term
    is closed when it is `0`. -/
partial def freeOf (u : Expr) : MetaM Nat := do
  let u := u.consumeMData
  match u.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← freeOf a) + (← freeOf b)
  | (``LeanScript.Usage.add, #[_, a, b]) => return (← freeOf a) + (← freeOf b)
  | (``OfNat.ofNat, _) => return 0
  | (``Zero.zero, _) => return 0
  | (``LeanScript.Usage.zero, _) => return 0
  | (``LeanScript.Usage.global, _) => return 1
  | (``LeanScript.Usage.single, _) => return 1
  | (``LeanScript.Usage.tail, #[_, _, v]) => return (← freeOf v) - (← gradeOf v 0)
  | (``LeanScript.Usage.cons, #[_, _, k, v]) => return (← natValue k) + (← freeOf v)
  | (``LeanScript.Usage.smul, #[_, k, v]) => return (← natValue k) * (← freeOf v)
  | (``LeanScript.Usage.many, #[_, v]) => return 2 * (← freeOf v)
  | (``LeanScript.Usage.letU, #[_, _, a, b]) =>
      let h ← gradeOf b 0
      return h * (← freeOf a) + ((← freeOf b) - h)
  | (``LeanScript.Usage.drop, #[_, δ, v]) => dropFree v (← listElems δ).length
  | (``LeanScript.Usage.dropN, #[_, _, n, v]) => dropFree v (← natValue n)
  | _ =>
      let u' ← whnfCore u
      if u' == u then throwError "`#leanscript_to_term`: internal: not a grade vector: {u}"
      freeOf u'
where
  /-- `freeOf` of `v` with its `n` innermost variables forgotten. -/
  dropFree (v : Expr) (n : Nat) : MetaM Nat := do
    let mut f ← freeOf v
    for i in [0:n] do f := f - (← gradeOf v i)
    return f

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

/-- A stand-in proof of `p`, for a node that is only **run**, never kept: `unsafeCast` of
    the unit.  The code that runs it erases proofs, so the stand-in is never looked at. -/
def placeholderProof (p : Expr) : MetaM Expr := do
  let lvl ← getLevel p
  return mkApp3 (mkConst ``unsafeCast [levelOne, lvl]) (mkConst ``PUnit [levelOne]) p
    (mkConst ``PUnit.unit [levelOne])

/-- `buildNode`; with `placeholder`, the proof `hClosed` (that the node is not a closed
    computation) is not proved but stood in for (`placeholderProof`): the node is then only
    fit to be run, by `closedValue?`. -/
def buildNodeCore (ctor : Name) (args : Array Expr) (placeholder : Bool) : MetaM Expr := do
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
      | none =>
          if placeholder && info.names[i]!.eraseMacroScopes == `hClosed then
            placeholderProof d
          else proveByDecide d
    out := out.push v
    cur := b.instantiate1 v
  return mkAppN (mkConst ctor) out

/-- Build the node `ctor` from its arguments **without** indices — the parameter `Sg` and
    then every field that is not an index or a proof about the indices, in order — reading
    the indices off the subterms and proving the side conditions by `decide`.  No check
    that the node is not a redex is made here: that is `mkNode`. -/
def buildNode (ctor : Name) (args : Array Expr) : MetaM Expr :=
  buildNodeCore ctor args false

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

/-- The context `γ`, whose `n` innermost cells are written as a list computation (the
    fields of a branch, `fields.toList ++ Γ`), with those cells written out:
    `σ₀ :: … :: σₙ₋₁ :: Γ`. -/
partial def ctxCells (γ : Expr) : Nat → MetaM Expr
  | 0 => pure γ
  | n + 1 => do
      let γ' ← whnf γ
      match γ'.getAppFnArgs with
      | (``List.cons, #[α, σ, rest]) => return mkApp3 γ'.getAppFn α σ (← ctxCells rest n)
      | _ => throwError "`#leanscript_to_term`: internal: context {γ} has fewer than {n + 1} cells"

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

/-- Is this head a `fun`, or a dispatch that may answer with one
    (`LeanScript.Head.isFunLike`)? -/
def isFunLikeHead (k : Name) : Bool :=
  k == ``LeanScript.Head.lam || k == ``LeanScript.Head.caseIntro

/-- Is this head a literal — a boolean one (`LeanScript.Head.bool`) or another? -/
def isLitHead (k : Name) : Bool := k == ``LeanScript.Head.lit || k == ``LeanScript.Head.bool

/-- Is this head a literal or a closed value (`LeanScript.Head.isValue`)? -/
def isValueHead (k : Name) : Bool := isLitHead k || k == ``LeanScript.Head.val

/-- `LeanScript.Head.isKnown`, on the name of a head: a literal, a constructor, a closed
    value, or a dispatch that answers with one of those in every branch. -/
def isKnownHead (k : Name) : Bool :=
  isValueHead k || k == ``LeanScript.Head.ctor || k == ``LeanScript.Head.caseCtor

/-- `LeanScript.Head.isComp`, on the name of a head: a computation — an application, a
    fold, an extern, a force or a dispatch. -/
def isCompHead (k : Name) : Bool :=
  k == ``LeanScript.Head.comp || k == ``LeanScript.Head.caseIntro ||
    k == ``LeanScript.Head.caseCtor

/-- A dispatch that may answer with an introduction form: `Head.caseIntro` or
    `Head.caseCtor`. -/
def isCaseHead (k : Name) : Bool :=
  k == ``LeanScript.Head.caseIntro || k == ``LeanScript.Head.caseCtor

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

/-! ## Floating a `let` out

A `let` has the head of its body (`Term.letE`), so a node whose function, bound expression
or scrutinee is a `let` of a `fun` or of a constructor is a redex behind the `let`.  It is
rewritten `N[let x = e; b] ↦ let x = e; N[b]` — the rest of `N` weakened past `x` — and
the node `N[b]` is then reduced as any other. -/

/-- The scrutinee of a dispatch on a primitive type or an enum.  It is a literal or a
    variable or a computation, and never a `let` of a literal — but it may be a `let` of a
    dispatch of literals (`Head.caseCtor`), which floats out of it before the dispatch is
    taken case-of-case. -/
def primScrutinee? : Name → Option String
  | ``LeanScript.Term.bool_casesOn => some "c"
  | ``LeanScript.Term.nat_casesOn => some "n"
  | ``LeanScript.Term.int_casesOn => some "i"
  | ``LeanScript.Term.enum_casesOn | ``LeanScript.Term.enum_casesOnWithDefault => some "e"
  | ``LeanScript.Term.uint8_casesOn | ``LeanScript.Term.uint16_casesOn
  | ``LeanScript.Term.uint32_casesOn | ``LeanScript.Term.uint64_casesOn
  | ``LeanScript.Term.int8_casesOn | ``LeanScript.Term.int16_casesOn
  | ``LeanScript.Term.int32_casesOn | ``LeanScript.Term.int64_casesOn
  | ``LeanScript.Term.char_casesOn | ``LeanScript.Term.stringPosRaw_casesOn
  | ``LeanScript.Term.stringPos_casesOn | ``LeanScript.Term.substringRaw_casesOn
  | ``LeanScript.Term.float_casesOn | ``LeanScript.Term.float32_casesOn
  | ``LeanScript.Term.floatModel_casesOn | ``LeanScript.Term.float32Model_casesOn => some "x"
  | _ => none

/-- The argument of a node whose root the grammar checks, when a `let` there must float
    out: the function of an application, the bound expression of a `let`, the scrutinee
    of a force or of a dispatch.  (An extern checks for a literal or a closed value, and a
    `let` is never one.) -/
def scrutineeArg? : Name → Option String
  | ``LeanScript.Term.ap => some "f"
  | ``LeanScript.Term.letE => some "e"
  | ``LeanScript.Term.lazy_force | ``LeanScript.Term.thunk_force => some "e"
  | ``LeanScript.Term.array_casesOn => some "a"
  | ``LeanScript.Term.record_casesOn => some "r"
  | ``LeanScript.Term.recObject_casesOn | ``LeanScript.Term.recAlias_casesOn
  | ``LeanScript.Term.taggedUnion_casesOn | ``LeanScript.Term.recTaggedUnion_casesOn
  | ``LeanScript.Term.mutualRecursiveFamily_casesOn
  | ``LeanScript.Term.mutualRecursiveFamily_casesOnWithDefault => some "x"
  | ``LeanScript.Term.taggedUnion_casesOnWithDefault
  | ``LeanScript.Term.recTaggedUnion_casesOnWithDefault => some "v"
  | ctor => primScrutinee? ctor

/-- The scrutinee of a **dispatch** (not of an application, a `let` or a force): what
    case-of-case looks at. -/
def dispatchScrutinee? (ctor : Name) : Option String :=
  if ctor == ``LeanScript.Term.ap || ctor == ``LeanScript.Term.letE ||
      ctor == ``LeanScript.Term.lazy_force || ctor == ``LeanScript.Term.thunk_force then none
  else scrutineeArg? ctor

/-- The field named `n` of an exposed node (all of its arguments, indices included). -/
def fieldNamed (t : Expr) (n : String) : MetaM Expr := do
  let ctor := t.getAppFn.constName!
  let info ← ctorInfo ctor
  let ci ← getConstInfoCtor ctor
  for i in [0:info.names.size] do
    if info.names[i]!.eraseMacroScopes.toString == n then
      return t.getAppArgs[ci.numParams + i]!
  throwError "`#leanscript_to_term`: internal: {ctor} has no field {n}"

mutual

/-- The node `ctor` from its arguments without indices: reduced, if it is a redex; built
    as it stands otherwise.  **The** constructor of the translation. -/
partial def mkNode (ctor : Name) (args : Array Expr) : MetaM Expr := do
  if let some t ← floatLet? ctor args then return t
  if let some t ← caseOfCase? ctor args then return t
  if let some t ← reduceRedex? ctor args then return t
  if let some t ← closedValue? ctor args then return t
  buildNode ctor args

/-- **Case-of-case.**  A dispatch on a dispatch that answers with a known constructor in
    every branch (`LeanScript.Head.caseCtor`) is moved into the inner branches:
    `match (match s with | p => Cᵖ) with | q => bᵍ` is `match s with | p => match Cᵖ with
    | q => bᵍ`, and each copy of the outer dispatch then meets a constructor and reduces to
    one of its branches.  The rest of the outer node is weakened past the variables each
    inner branch binds. -/
partial def caseOfCase? (ctor : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let some sName := dispatchScrutinee? ctor | return none
  let s ← argNamed ctor args sName
  unless (← headOf s) == ``LeanScript.Head.caseCtor do return none
  let τs ← termTyOf s
  let τ ← argNamed ctor args "τ"
  some <$> mapBranches s τs τ fun γc n b => do
    -- the context of the branch, as a list of cells (`fields.toList ++ Γ` unfolded), so
    -- that the contexts of the outer node's branches are seen to be over it
    rebuildPast ctor args (← ctxCells γc n) sName b n

/-- If the node `ctor args` hides a redex behind a `let` (see the section header), the
    `let` floated out of it. -/
partial def floatLet? (ctor : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let some sName := scrutineeArg? ctor | return none
  let s ← argNamed ctor args sName
  let sn ← exposeNode s
  unless sn.getAppFn.isConstOf ``LeanScript.Term.letE do return none
  let k ← headOf s
  let floats :=
    if ctor == ``LeanScript.Term.ap then isFunLikeHead k
    else if ctor == ``LeanScript.Term.letE then k == ``LeanScript.Head.lam
    else if ctor == ``LeanScript.Term.thunk_force || ctor == ``LeanScript.Term.lazy_force then
      isCtorHead k || isCaseHead k
    else isKnownHead k
  unless floats do return none
  let e ← fieldNamed sn "e"
  let b ← fieldNamed sn "b"
  let γ ← argNamed ctor args "Γ"
  let σ ← termTyOf e
  let inner ← rebuildPast ctor args (consCtxE σ γ) sName b
  some <$> mkNode ``LeanScript.Term.letE #[args[0]!, γ, σ, ← termTyOf inner, e, inner]

/-- The node `ctor args` (arguments without indices) rebuilt in the context `γ'`, which
    has `m` more variables, innermost, than the node's (one, by default): the argument
    named `sName` is replaced by `b` (already written in `γ'`) and every other subterm is
    weakened. -/
partial def rebuildPast (ctor : Name) (args : Array Expr) (γ' : Expr) (sName : String)
    (b : Expr) (m : Nat := 1) : MetaM Expr := do
  let info ← ctorInfo ctor
  let ci ← getConstInfoCtor ctor
  let params := args.extract 0 ci.numParams
  let mut cur ← instantiateForall ci.type params
  let mut newArgs := params
  let mut k := ci.numParams
  for i in [0:info.roles.size] do
    let cur' ← whnf cur
    let .forallE _ dom body _ := cur'
      | throwError "`#leanscript_to_term`: internal: {ctor} has too few arguments"
    let r := info.roles[i]!
    if r == .index || r == .indexProof then
      -- the contexts of the subterms do not depend on the indices
      cur := body.instantiate1 (← mkFreshExprMVar dom)
      continue
    let old := args[k]!
    k := k + 1
    let v ← match r with
      | .ctx => pure γ'
      | .child =>
          if info.names[i]!.eraseMacroScopes.toString == sName then pure b
          else
            let γc := (← famTypeOf' dom).2
            let n ← bindersBefore γc γ'
            mapVars old γc n fun j => pure (.var (j + m))
      | _ => pure old
    newArgs := newArgs.push v
    cur := body.instantiate1 v
  mkNode ctor newArgs

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
  | ``LeanScript.Term.record_mk =>
      -- the fields, as the nested pairs the record denotes
      valueDens n.getAppArgs.back!
  | ``LeanScript.Term.taggedUnion_mk =>
      let a := n.getAppArgs
      mkAppOptM ``LeanScript.TyWf.DenTU.mk
        #[some a[2]!, some a[3]!, some a[4]!, some (← valueDens a.back!)]
  | ``LeanScript.Term.recTaggedUnion_mk =>
      let a := n.getAppArgs
      let unf := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) a[2]! a[3]!
      let node ← mkAppOptM ``LeanScript.TyWf.DenTU.mk
        #[some unf, some a[4]!, some a[5]!, some (← valueDens a.back!)]
      return mkApp3 (mkConst ``LeanScript.TyWf.DenRec.mk) a[2]! a[3]! node
  | _ => lastArg n

/-- The values of a spine of literals and closed values, as the nested pairs
    `TyWf.DenList` is. -/
partial def valueDens (sp : Expr) : MetaM Expr := do
  let es ← spineElems sp
  let mut acc := mkConst ``PUnit.unit [Level.one]
  for e in es.reverse do
    acc ← mkAppM ``Prod.mk #[← valueDen e, acc]
  return acc

/-- The checked position at byte index `i` into the string `s` (an expression), with its
    validity proved by `decide`. -/
partial def quotePosE (s : Expr) (i : Nat) : MetaM Expr := do
  let raw := mkApp (mkConst ``String.Pos.Raw.mk) (mkNatLit i)
  let valid ← mkDecideProof (mkApp2 (mkConst ``String.Pos.Raw.IsValid) s raw)
  return mkApp3 (mkConst ``String.Pos.mk) s raw valid

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
  | .stringPos i => do
      let .prim p ← tyView τ
        | throwError "`#leanscript_to_term`: internal: {τ} is not a string position"
      let some s := (← whnf p).getAppFnArgs |> fun
          | (``LeanScript.LeanPrimTy.stringPos, #[s]) => some s
          | _ => none
        | throwError "`#leanscript_to_term`: internal: {τ} is not a string position"
      return mkAppN (mkConst ``LeanScript.Term.stringPos_mk) #[sg, γ, s, ← quotePosE s i]
  | .stringSlice str i j => do
      let s := toExpr str
      let pi ← quotePosE s i
      let pj ← quotePosE s j
      let le ← mkDecideProof (← mkAppM ``LE.le #[pi, pj])
      let v := mkAppN (mkConst ``String.Slice.mk) #[s, pi, pj, le]
      return mkAppN (mkConst ``LeanScript.Term.stringSlice_mk) #[sg, γ, v]
  | .floatModel single bits => do
      let (bitsE, toBV, model, spec, ctor) := if single then
          (toExpr (UInt32.ofNat bits), ``UInt32.toBitVec, ``Float32.Model.mk,
            ``Float.Model.Format.binary32, ``LeanScript.Term.float32Model_mk)
        else
          (toExpr (UInt64.ofNat bits), ``UInt64.toBitVec, ``Float.Model.mk,
            ``Float.Model.Format.binary64, ``LeanScript.Term.floatModel_mk)
      -- `Valid` is a structure with one field, an implication of decidable equations about
      -- the bits, so it is proved by `decide`
      let validMk := mkApp2 (mkConst ``Float.Model.Format.Valid.mk) (mkConst spec)
        (mkApp (mkConst toBV) bitsE)
      let .forallE _ d _ _ ← whnf (← inferType validMk)
        | throwError "`#leanscript_to_term`: internal: unexpected `Float.Model.Format.Valid`"
      let m := mkApp2 (mkConst model) bitsE (mkApp validMk (← mkDecideProof d))
      return mkAppN (mkConst ctor) #[sg, γ, m]
  | .ctor t xs => do
      match ← tyView τ with
      | .record fs =>
          let spine ← quotedSpine sg γ (← recordFieldTys fs) xs
          mkNode ``LeanScript.Term.record_mk #[sg, γ, fs, spine]
      | .taggedUnion l =>
          let some fieldTys := (← taggedUnionCtorTys l)[t]?
            | throwError "`#leanscript_to_term`: internal: {τ} has no constructor {t}"
          let spine ← quotedSpine sg γ fieldTys xs
          let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
          let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit t, lenE])
          mkNode ``LeanScript.Term.taggedUnion_mk #[sg, γ, l, mkNatLit t, prf, spine]
      | .recTaggedUnion l hwf =>
          let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf
          let some fieldTys := (← taggedUnionCtorTys (← reduceTy unfE))[t]?
            | throwError "`#leanscript_to_term`: internal: {τ} has no constructor {t}"
          let spine ← quotedSpine sg γ fieldTys xs
          let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
          let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit t, lenE])
          mkNode ``LeanScript.Term.recTaggedUnion_mk #[sg, γ, l, hwf, mkNatLit t, prf, spine]
      | _ => throwError "`#leanscript_to_term`: internal: {τ} has no constructors"

/-- The spine of the terms that denote the computed values `xs`, of the types `tys`. -/
partial def quotedSpine (sg γ : Expr) (tys : List Expr) (xs : List LeanScript.Quoted) :
    MetaM Expr := do
  unless tys.length == xs.length do
    throwError "`#leanscript_to_term`: internal: {xs.length} values for {tys.length} fields"
  let tysA := tys.toArray
  let xsA := xs.toArray
  let mut sp ← mkNode ``LeanScript.Spine.nil #[sg, γ]
  for i in [0:xsA.size] do
    let j := xsA.size - 1 - i
    let t ← quotedTerm sg γ tysA[j]! xsA[j]!
    sp ← mkNode ``LeanScript.Spine.cons #[sg, γ, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- The extern `e` (an entry of the catalogue applied to values) of result type `τ`, as a
    term: its value when that can be written (`LeanScript.TyWf.quotable`), and
    `Term.extern e` otherwise. -/
partial def mkExternNode (sg γ τ e : Expr) : MetaM Expr := do
  if ← isQuotable τ then
    return ← quotedTerm sg γ τ (← quoteExtern τ e)
  let h ← mkDecideProof (← mkEq (mkApp (mkConst ``LeanScript.TyWf.quotable) τ)
    (mkConst ``Bool.false))
  buildNode ``LeanScript.Term.extern #[sg, γ, τ, e, h]

/-- **A closed computation is its value.**  If the node `ctor args` is a computation that
    reads no variable and no top-level declaration, at a type whose values can be written
    as terms (`LeanScript.Head.closedComp`, which the grammar's `hClosed` rejects), its
    value: the node is built with a stand-in for `hClosed` (`buildNodeCore`), run —
    `Term.eval`, compiled, with stand-ins for the environments it never reads — and its
    value written back as a term (`LeanScript.TyWf.quote`).  So `sumTo 5`, a fold on the
    literal `5`, is the literal `10`. -/
partial def closedValue? (ctor : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let info ← ctorInfo ctor
  unless info.names.any (·.eraseMacroScopes == `hClosed) do return none
  let t ← buildNodeCore ctor args true
  let (sg, γ, u, τ, _) ← termParts t
  unless (← freeOf (← instantiateMVars u)) == 0 do return none
  unless isCompHead (← headOf t) do return none
  unless ← isQuotable τ do return none
  -- the model gives these no value, so a term that builds one cannot be run
  for n in [``LeanScript.Term.recObject_mk, ``LeanScript.Term.recAlias_mk,
      ``LeanScript.Term.mutualRecursiveFamily_mk] do
    if (t.find? (·.isConstOf n)).isSome then
      throwError "`#leanscript_to_term`: a closed computation builds a value of a recursive \
        record, newtype or mutual family, which has no value to write: {t}"
  -- the term reads no declaration, so it is run against the empty signature
  let noDecls := mkApp (mkConst ``List.nil [0]) (mkConst ``LeanScript.GlobalDecl)
  let emptySig := mkApp2 (mkConst ``LeanScript.Sig.mk) noDecls
    (← mkDecideProof (← mkEq (mkApp (mkConst ``LeanScript.declNamesUnique) noDecls)
      (mkConst ``Bool.true)))
  let sgE ← instantiateMVars sg
  let t0 := (← instantiateMVars t).replace fun x => if x == sgE then some emptySig else none
  let gE := mkConst ``PUnit.unit [levelOne]
  let envE ← placeholderProof (mkApp (mkConst ``LeanScript.Env) γ)
  let hE ← placeholderProof (← mkAppM ``LeanScript.Term.NoRecMk #[t0])
  let v ← mkAppOptM ``LeanScript.Term.eval
    #[some emptySig, some gE, none, none, none, none, some t0, some envE, some hE]
  let e ← instantiateMVars (mkApp2 (mkConst ``LeanScript.TyWf.quote) τ v)
  -- the context the translation writes under is a local (`fun Γ => …`); the term reads
  -- none of it, so it is run in the empty context
  let ctxTy := mkConst ``LeanScript.Ctx
  let mut e := e
  for fv in (collectFVars {} e).fvarIds do
    if ← isDefEq (← fv.getType) ctxTy then
      e := e.replaceFVarId fv (mkApp (mkConst ``List.nil [0]) (mkConst ``LeanScript.TyWf))
  if e.hasFVar then
    throwError "`#leanscript_to_term`: internal: a closed computation mentions a local: {e}"
  let ty := mkApp (mkConst ``Option [0]) (mkConst ``LeanScript.Quoted)
  let some q ← unsafe evalExpr (Option LeanScript.Quoted) ty e (safety := .unsafe) (checkMeta := false)
    | throwError "`#leanscript_to_term`: internal: the value of {t} cannot be written"
  some <$> quotedTerm sg γ τ q

/-- If the node `ctor args` is a redex, what it reduces to. -/
partial def reduceRedex? (ctor : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let arg (n : String) : MetaM Expr := argNamed ctor args n
  let sg := args[0]!
  match ctor with
  | ``LeanScript.Term.lam =>
      -- η: `fun x => f x`, where `f` does not read `x`, is `f`.  (The grammar does not
      -- reject this `fun`: telling `f x` from `f y` would take a head that depends on the
      -- head of the argument, which a term written in a generic context cannot decide.)
      let b ← exposeNode args.back!
      unless b.getAppFn.isConstOf ``LeanScript.Term.ap do return none
      let a ← exposeNode (← fieldNamed b "a")
      unless a.getAppFn.isConstOf ``LeanScript.Term.var do return none
      unless (← varIndex a.getAppArgs.back!) == 0 do return none
      let f ← fieldNamed b "f"
      unless (← usesOf f 0) == 0 do return none
      some <$> mapVars f (← arg "Γ") 0 fun j => do
        if j == 0 then throwError "`#leanscript_to_term`: internal: η on a function that \
          reads its parameter"
        pure (.var (j - 1))
  | ``LeanScript.Term.ap =>
      let f ← arg "f"
      let kf ← headOf f
      if kf == ``LeanScript.Head.caseIntro then
        return some (← pushArg sg (← arg "Γ") (← arg "σ") (← arg "τ") f (← arg "a"))
      unless kf == ``LeanScript.Head.lam do return none
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
      if (k == ``LeanScript.Head.comp || isCtorHead k || isCaseHead k) &&
          (← usesOf b 0) ≥ 2 then
        return none
      some <$> subst0 b e (← arg "Γ")
  | ``LeanScript.Term.bool_casesOn =>
      let c ← arg "c"
      if (← boolHeadOf? (← arg "t")) == some true && (← boolHeadOf? (← arg "e")) == some false then
        -- `if c then true else false` is `c`
        return some c
      unless isLitHead (← headOf c) do return none
      let v ← whnf (← lastArg c)
      if v.isConstOf ``Bool.true then some <$> rebase (← arg "t") (← arg "Γ")
      else if v.isConstOf ``Bool.false then some <$> rebase (← arg "e") (← arg "Γ")
      else throwError "`#leanscript_to_term`: internal: not a boolean: {v}"
  | ``LeanScript.Term.nat_casesOn =>
      let n ← arg "n"
      unless isLitHead (← headOf n) do return none
      let γ ← arg "Γ"
      let v ← natValue (← lastArg n)
      if v == 0 then return some (← rebase (← arg "z") γ)
      let pred ← buildNode ``LeanScript.Term.nat_mk #[sg, γ, mkNatLit (v - 1)]
      some <$> subst0 (← arg "s") pred γ
  | ``LeanScript.Term.int_casesOn =>
      let i ← arg "i"
      unless isLitHead (← headOf i) do return none
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
      let γ ← arg "Γ"
      let b ← arg "b"
      if isLitHead (← headOf x) then
        return some (← bindMany sg γ b (← primFields ctor sg γ x))
      -- a branch that reads none of the fields: the value need not be taken apart
      oneCtorUnused? b γ
  | ``LeanScript.Term.lazy_force | ``LeanScript.Term.thunk_force =>
      let e ← arg "e"
      let ke ← headOf e
      if isCaseHead ke then
        -- a force of a dispatch one of whose branches is a delay: force each branch
        let τ ← arg "τ"
        let τd ← termTyOf e
        return some (← mapBranches e τd τ fun γc _ b => mkNode ctor #[sg, γc, τ, b])
      unless isCtorHead ke do return none
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
      unless isLitHead (← headOf e) do return none
      let i ← finValue (← lastArg e)
      some <$> rebase (← enumBranch (← arg "cases") i) (← arg "Γ")
  | ``LeanScript.Term.enum_casesOnWithDefault =>
      let e ← arg "e"
      unless isLitHead (← headOf e) do return none
      let i ← finValue (← lastArg e)
      match ← enumSomeBranch? (← arg "cases") i with
      | some b => some <$> rebase b (← arg "Γ")
      | none => some <$> rebase (← arg "dflt") (← arg "Γ")
  | ``LeanScript.Term.record_casesOn =>
      let r ← arg "r"
      let γ ← arg "Γ"
      unless isCtorHead (← headOf r) do return ← oneCtorUnused? (← arg "body") γ
      some <$> bindMany sg γ (← arg "body") (← spineElems (← lastArg r))
  | ``LeanScript.Term.recObject_casesOn =>
      let x ← arg "x"
      let γ ← arg "Γ"
      unless isCtorHead (← headOf x) do return ← oneCtorUnused? (← arg "body") γ
      some <$> bindMany sg γ (← arg "body") (← spineElems (← lastArg x))
  | ``LeanScript.Term.recAlias_casesOn =>
      let x ← arg "x"
      let γ ← arg "Γ"
      unless isCtorHead (← headOf x) do return ← oneCtorUnused? (← arg "body") γ
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
  | ``LeanScript.Term.nat_rec =>
      -- a fold whose branch reads none of its answers is a case analysis
      let k ← natValue (← arg "k")
      let branch ← arg "branch"
      if (← answersRead branch 1 (k + 1)) > 0 then
        -- a one-step fold whose branch is the answer it is given: the base, at every `n`
        if k == 0 && (← headOf branch) == ``LeanScript.Head.var then
          return some (← rebase (← spineElems (← arg "base"))[0]! (← arg "Γ"))
        -- a fold at a function type whose step calls the answer at once, with new
        -- arguments: a loop over those arguments
        return ← accLoop? args
      let (_, γb, _, _, _) ← termParts branch
      let natTy := (← ctxCell γb 0).1
      some <$> natRecCasesAt sg (← arg "τ") natTy k 0 (← arg "Γ") (← arg "n")
        (← spineElems (← arg "base")) branch
  | ``LeanScript.Term.array_rec =>
      let k ← natValue (← arg "k")
      let branch ← arg "branch"
      if (← answersRead branch 2 (k + 1)) > 0 then
        -- a one-step fold whose branch is the answer it is given: the base, at every array
        if k == 0 && (← headOf branch) == ``LeanScript.Head.var then
          return some (← rebase (← arrayRecBasesElems (← arg "bases"))[0]! (← arg "Γ"))
        return none
      let (_, γb, _, _, _) ← termParts branch
      let arrTy := (← ctxCell γb 1).1
      some <$> arrayRecCasesAt sg (← arg "σ") arrTy (← arg "τ") k 0 (← arg "Γ") (← arg "a")
        (← arrayRecBasesElems (← arg "bases")) branch
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

/-- `(match … with | p => fᵖ) a`, where the dispatch `f` has a `fun` in some branch
    (`LeanScript.Head.caseIntro`): the application moved into the branches,
    `match … with | p => fᵖ a`, where it meets the `fun` and is reduced.  An argument that
    is not a variable or a literal is bound by a `let` first, so it is written once;
    `mkNode` then inlines it where the grammar asks (into the one branch that reads it,
    say, since the branches of a dispatch run at most once between them). -/
partial def pushArg (sg γ σ τ f a : Expr) : MetaM Expr := do
  let ka ← headOf a
  if ka == ``LeanScript.Head.var || isLitHead ka then
    let τf ← termTyOf f
    return ← mapBranches f τf τ fun γc n b => do
      let a' ← if n == 0 then rebase a γc else shiftBy a γc n
      mkNode ``LeanScript.Term.ap #[sg, γc, σ, τ, b, a']
  let γ' := consCtxE σ γ
  let f' ← shiftBy f γ' 1
  let body ← mkNode ``LeanScript.Term.ap #[sg, γ', σ, τ, f', ← mkVarTerm sg γ' 0]
  mkNode ``LeanScript.Term.letE #[sg, γ, σ, τ, a, body]

/-- Rebuild the dispatch `t` (a node of `Term` whose root is a dispatch, or a node of one
    of the families of branches it holds), whose branches answer with the type `τ`, with
    every branch `b` replaced by `k γc n b` — `γc` is the context `b` is written in and `n`
    the number of variables the branch binds — which answers with `τ'`.  What the
    dispatch is taken on, and every other argument, is kept. -/
partial def mapBranches (t τ τ' : Expr) (k : Expr → Nat → Expr → MetaM Expr) :
    MetaM Expr := do
  let t ← exposeNode t
  let .const ctor _ := t.getAppFn | unreachable!
  let args := t.getAppArgs
  let ci ← getConstInfoCtor ctor
  let info ← ctorInfo ctor
  let mut γ := mkConst ``Unit
  for i in [0:info.roles.size] do
    if info.roles[i]! == .ctx then γ := args[ci.numParams + i]!
  -- which fields are branches: the subterms whose type is written with the node's own `τ`
  let branch ← forallTelescope ci.type fun xs _ => do
    let fields := xs.extract ci.numParams xs.size
    let some j := info.names.findIdx? (·.eraseMacroScopes.toString == "τ")
      | throwError "`#leanscript_to_term`: internal: {ctor} has no result type"
    let τv := fields[j]!
    fields.mapM fun x => do
      let ty ← inferType x
      return ty.getAppFn.constName?.any isGrammarFamily && ty.getAppArgs.contains τv
  let mut newArgs := args.extract 0 ci.numParams
  for i in [0:info.roles.size] do
    let old := args[ci.numParams + i]!
    match info.roles[i]! with
    | .index | .indexProof => continue
    | .child =>
        let (fty, γc) ← famTypeOf' (← inferType old)
        if !branch[i]! then newArgs := newArgs.push old
        else if fty.getAppFn.isConstOf ``LeanScript.Term then
          let n ← bindersBefore γc γ
          newArgs := newArgs.push (← k γc n old)
        else
          newArgs := newArgs.push (← mapBranches old τ τ' k)
    | _ =>
        if info.names[i]!.eraseMacroScopes.toString == "τ" then newArgs := newArgs.push τ'
        else newArgs := newArgs.push old
  mkNode ctor newArgs

/-- How many times the term `b` reads the `n` variables of de Bruijn indices `start`,
    `start + 1`, …: the answers a fold's branch is given. -/
partial def answersRead (b : Expr) (start n : Nat) : MetaM Nat := do
  let mut total := 0
  for j in [start:start + n] do total := total + (← usesOf b j)
  return total

/-- `nat_rec k n base branch`, whose branch reads none of its answers, as the case analysis
    it is: `k + 1` nested `nat_casesOn`, the one at level `j` (in the context `γj`, which
    binds the `j` predecessors taken so far in front of the fold's context) answering
    `base` at `j` for zero, and the innermost handing its predecessor — the `n` of the
    branch — to the branch. -/
partial def natRecCasesAt (sg τ natTy : Expr) (k j : Nat) (γj n : Expr) (base : Array Expr)
    (branch : Expr) : MetaM Expr := do
  if j == k + 1 then
    -- the branch binds its predecessor, then the `k + 1` answers it never reads
    return ← mapVars branch γj 0 fun i => pure (.var (if i == 0 then 0 else i - 1))
  let scrut ← if j == 0 then pure n else mkVarTerm sg γj 0
  -- `base` holds the answers at `k, …, 0`, nearest first
  let z ← if j == 0 then rebase base[k]! γj else shiftBy base[k - j]! γj j
  let s ← natRecCasesAt sg τ natTy k (j + 1) (consCtxE natTy γj) n base branch
  mkNode ``LeanScript.Term.nat_casesOn #[sg, γj, τ, scrut, z, s]

/-- The answers of an `ArrayRecBases`, for the lists of `0, 1, …, k` elements: the one for
    `j` elements is written with those elements bound, the last at index `0`. -/
partial def arrayRecBasesElems (b : Expr) : MetaM (Array Expr) := do
  let b ← exposeNode b
  match b.getAppFnArgs with
  | (``LeanScript.ArrayRecBases.nil, args) => return #[args.back!]
  | (``LeanScript.ArrayRecBases.cons, args) =>
      return #[args[args.size - 2]!] ++ (← arrayRecBasesElems args.back!)
  | _ => throwError "`#leanscript_to_term`: internal: not the bases of a fold: {b}"

/-- `array_rec k a bases branch`, whose branch reads none of its answers, as the case
    analysis it is: `k + 1` nested `array_casesOn`, the one at level `j` (in the context
    `γj`, which binds the element and the rest taken at each level so far, the latest at
    indices `0` and `1`) answering the base for `j` elements when the rest is empty, and
    the innermost handing the first element and the first rest — the head and the tail
    of the branch — to the branch. -/
partial def arrayRecCasesAt (sg σ arrTy τ : Expr) (k j : Nat) (γj a : Expr)
    (bases : Array Expr) (branch : Expr) : MetaM Expr := do
  if j == k + 1 then
    -- the branch binds the head, the tail, then the `k + 1` answers it never reads
    return ← mapVars branch γj 0 fun i => pure (.var
      (if i == 0 then 2 * k else if i == 1 then 2 * k + 1 else i + k - 1))
  let scrut ← if j == 0 then pure a else mkVarTerm sg γj 1
  let z ← if j == 0 then rebase bases[0]! γj else
    mapVars bases[j]! γj 0 fun i => pure (.var (if i < j then 2 * i else i + j))
  let γ' := consCtxE σ (consCtxE arrTy γj)
  let s ← arrayRecCasesAt sg σ arrTy τ k (j + 1) γ' a bases branch
  mkNode ``LeanScript.Term.array_casesOn #[sg, γj, σ, τ, scrut, z, s]

/-- The one branch `b` of a dispatch on a value with one constructor (a record, a newtype,
    a primitive wrapper), written in the context `γ` with the fields bound in front: if it
    reads none of the fields, the dispatch is not needed — the language is pure and
    total — and it is the branch, rebuilt in `γ`; otherwise `none`. -/
partial def oneCtorUnused? (b γ : Expr) : MetaM (Option Expr) := do
  let (_, γb, _, _, _) ← termParts b
  let n ← bindersBefore γb γ
  if (← answersRead b 0 n) > 0 then return none
  some <$> mapVars b γ 0 fun j => do
    if j < n then throwError "`#leanscript_to_term`: internal: field {j} is read"
    pure (.var (j - n))

/-- Is every term of this spine a literal or a closed value? -/
partial def allValues (sp : Expr) : MetaM Bool := do
  for e in ← spineElems sp do
    unless isValueHead (← headOf e) do return false
  return true

/-- `x - y`, for two terms of type `Nat` written in `γ`: `Term.externCall` of
    `LeanScript.natSubCall` (computed at once when both are literals). -/
partial def natSubTerm (sg γ x y : Expr) : MetaM Expr := do
  let natTy ← termTyOf x
  let tyNil := mkApp (mkConst ``List.nil [Level.zero]) tyE
  let sp ← mkNode ``LeanScript.Spine.cons
    #[sg, γ, natTy, tyNil, y, ← mkNode ``LeanScript.Spine.nil #[sg, γ]]
  let sp ← mkNode ``LeanScript.Spine.cons #[sg, γ, natTy, consCtxE natTy tyNil, x, sp]
  mkNode ``LeanScript.Term.externCall
    #[sg, γ, consCtxE natTy (consCtxE natTy tyNil), natTy, sp, mkConst ``LeanScript.natSubCall]

/-- **An accumulator-passing recursion, as a loop.**  The node is the one-step fold
    `nat_rec n (fun a => B) (fun k ih => fun a => ih F)` at a function type `σ ⇒ ρ`, whose
    step calls the answer at the predecessor at once, on a new accumulator `F` (which does
    not read `ih` otherwise) — the shape of a tail-recursive loop, `go (k + 1) a = go k F`,
    `go 0 a = B`.  Folded as it stands, it builds `n` closures, one per step, and a call
    runs them nested `n` deep.  But `go n a₀ = B[F(0, F(1, … F(n - 1, a₀)))]`: the
    accumulator is updated at `k = n - 1`, then `n - 2`, …, then `0`.  So it is
    `fun a => let p = n - 1; B[nat_rec n a (fun j s => F[s/a, (p - j)/k])]` — a fold at
    `σ`, which carries the accumulator itself, and one closure.  (The countdown `p - j` is
    written only when `F` reads `k`; a counter that is not a variable is bound by a `let`
    first, so it is computed once.) -/
partial def accLoop? (args : Array Expr) : MetaM (Option Expr) := do
  let arg (n : String) : MetaM Expr := argNamed ``LeanScript.Term.nat_rec args n
  let sg := args[0]!
  unless (← natValue (← arg "k")) == 0 do return none
  let γ ← arg "Γ"
  let n ← arg "n"
  let some base0 := (← spineElems (← arg "base"))[0]? | return none
  let baseN ← exposeNode base0
  unless baseN.getAppFn.isConstOf ``LeanScript.Term.lam do return none
  let branch ← arg "branch"
  let branchN ← exposeNode branch
  unless branchN.getAppFn.isConstOf ``LeanScript.Term.lam do return none
  let sN ← exposeNode branchN.getAppArgs.back!
  unless sN.getAppFn.isConstOf ``LeanScript.Term.ap do return none
  let ihN ← exposeNode (← fieldNamed sN "f")
  unless ihN.getAppFn.isConstOf ``LeanScript.Term.var do return none
  unless (← varIndex ihN.getAppArgs.back!) == 2 do return none
  let F ← fieldNamed sN "a"
  unless (← usesOf F 2) == 0 do return none
  let natTy ← termTyOf n
  -- a counter that is a computation: bound first, and the fold taken again on its name
  let kn ← headOf n
  unless kn == ``LeanScript.Head.var || isLitHead kn do
    let γ' := consCtxE natTy γ
    let inner ← rebuildPast ``LeanScript.Term.nat_rec args γ' "n" (← mkVarTerm sg γ' 0)
    return some (← mkNode ``LeanScript.Term.letE #[sg, γ, natTy, ← termTyOf inner, n, inner])
  let B := baseN.getAppArgs.back!
  let (_, γB, _, ρ, _) ← termParts B
  let σ := (← ctxCell γB 0).1
  -- the contexts: `a`; then `p`, `a`; then `j`, `s`, `p`, `a` (innermost first)
  let γa := consCtxE σ γ
  let γp := consCtxE natTy γa
  let γb := consCtxE natTy (consCtxE σ γp)
  let one ← buildNode ``LeanScript.Term.nat_mk #[sg, γa, mkNatLit 1]
  let p ← natSubTerm sg γa (← shiftBy n γa 1) one
  -- the step, on the accumulator `s`, at `k = p - j`
  -- (`k` bound by a `let`, which `mkNode` inlines unless `F` reads it twice)
  let γk := consCtxE natTy γb
  let F' ← mapVars F γk 0 fun i => do
    if i == 0 then return .var 2
    if i == 1 then return .var 0
    if i == 2 then throwError "`#leanscript_to_term`: internal: a loop step that reads its \
      answer"
    return .var (i + 2)
  let kTerm ← natSubTerm sg γb (← mkVarTerm sg γb 2) (← mkVarTerm sg γb 0)
  let step ← mkNode ``LeanScript.Term.letE #[sg, γb, natTy, σ, kTerm, F']
  let tyNil := mkApp (mkConst ``List.nil [Level.zero]) tyE
  let base ← mkNode ``LeanScript.Spine.cons
    #[sg, γp, σ, tyNil, ← mkVarTerm sg γp 1, ← mkNode ``LeanScript.Spine.nil #[sg, γp]]
  let fold ← mkNode ``LeanScript.Term.nat_rec
    #[sg, γp, σ, mkNatLit 0, ← shiftBy n γp 2, base, step]
  -- `B`, whose accumulator is the answer of the loop
  let B' ← mapVars B (consCtxE σ γp) 0 fun i => pure (.var (if i == 0 then 0 else i + 2))
  let body ← mkNode ``LeanScript.Term.letE #[sg, γp, σ, ρ, fold, B']
  let body ← mkNode ``LeanScript.Term.letE #[sg, γa, natTy, ρ, p, body]
  some <$> mkNode ``LeanScript.Term.lam #[sg, γ, σ, ρ, body]

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
