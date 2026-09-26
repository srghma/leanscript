module

public import LeanScript.Term
public meta import Lean.Elab.Command
public meta import Lean.Meta.Constructions.CasesOn

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Reading Lean types

The first stage shared by `leanscript_signature`, `#leanscript_get_ty` and
`#leanscript_get_ctor`: a Lean type is normalised (`normType`), its head is classified
(`classify`: a leaf, `→`, `Array`, `Thunk`, a type variable, or an inductive instance), and
the fields of an inductive instance's constructors are read (`readCtors`), with the fields
the language erases (proofs and instances) dropped.  A field whose type depends on an earlier
field is read through its erasure (`eraseDeps`): `Fin n → Nat` is `Nat → Nat`.  An inductive
family is read with its indices erased (`normType`, `erasedFields`): `Vec α n` is `Vec α`, a
linked list whose `cons` has no length field.  A family indexed by a *type* that recurses at
other indices (`Nest.cons : α → Nest (α × α) → Nest α`) is read at one index through a
generated element type (`canonIndex`, `ensureElem`): `Nest τ` is a list of `Nest.Elem B`.
A quotient `Quot r` (`Quotient s`) is read as its carrier (`quotCarrier?`): a value of it is
one of its representatives.

A *type variable* is a local `α : Type`: `#leanscript_get_ctor Option.some` reads `Option α`
with `α` a local, and `α` becomes an argument `(α : Ty ks)` of the generated function.
-/

open Lean Meta Elab

namespace LeanScript.Gen

/-- Every error of the generators starts with this. -/
def errPrefix : String := "LeanScript"

/-- Throw an error of the generators. -/
def fail {α : Type} (msg : MessageData) : MetaM α :=
  throwError m!"{errPrefix}: {msg}"

/-- The head of a (normalised) type. -/
inductive Head where
  /-- A leaf, given by the `LeanPrimTy` that names it. -/
  | prim (p : Lean.Term)
  /-- A non-dependent function type. -/
  | fn (a b : Expr)
  /-- `Array a`. -/
  | array (a : Expr)
  /-- A type variable (a local `α : Type`). -/
  | var (x : FVarId)
  /-- An instance of an inductive type. -/
  | node (e : Expr)

/-- Is a field of this type erased: a proof or an instance?  (A `Unit` field is **not**
    erased: `Unit` has one value, so it has no type in the language, and a constructor with
    such a field is refused like every other unit-like type.  Two values are `Bool`, never
    `Option Unit`.) -/
def isErasedField (bi : BinderInfo) (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if bi.isInstImplicit then return true
  return (← isClass? t).isSome

/-- The inductive family (with indices, valued in `Type`) a type is a full application of:
    its information, universe levels, parameters and indices. -/
def familyApp? (e : Expr) : MetaM (Option (InductiveVal × List Level × Array Expr × Array Expr)) := do
  let some (c, us) := e.getAppFn.const? | return none
  let some (.inductInfo info) := (← getEnv).find? c | return none
  let args := e.getAppArgs
  unless info.numIndices > 0 && args.size == info.numParams + info.numIndices do return none
  if ← isProp e then return none
  return some (info, us, args[:info.numParams].toArray, args[info.numParams:].toArray)

/-! ## Families indexed by a type (`Nest : Type → Type 1`)

A family whose index is a *type* recurses at other indices (`Nest.cons : α → Nest (α × α) →
Nest α`): its instances `Nest Nat`, `Nest (Nat × Nat)`, … are infinitely many, so they cannot
each be a member of a (finite) block.  Like the value indices of `Vec α n`, the type index is
erased, but through an *element type* that holds a value of every index reached:

```
inductive Nest.Elem (α : Type) : Type where
  | leaf : α → Nest.Elem α
  | node : Nest.Elem α → Nest.Elem α → Nest.Elem α   -- from the index `α × α`
```

generated once (`ensureElem`), with one `node` per recursive index `σ(α) ≠ α` (a structure
`σ(α)`, such as `α × α`, is flattened into its fields).  `Nest τ` is then read as the
datatype `Nest (Nest.Elem B)`, where the *base* `B` is `τ` with the recursive indices peeled
off (`canonIndex`: `Nat × Nat` peels to `Nat`), and a field of type `α` holds an
`Nest.Elem B`: `Nest Nat` is `nil | cons (Nest.Elem Nat) Nest`, a list whose `k`-th element is
a tree (in Lean, a perfect tree of depth `k`).  A family whose type index only recurses at
itself needs no element type: `F τ` is read with `α := τ`. -/

/-- Is the inductive a family with an index that is a type? -/
def typeIndexed (info : InductiveVal) : MetaM Bool := do
  if info.numIndices == 0 then return false
  forallTelescopeReducing info.type fun xs _ =>
    xs[info.numParams:].toArray.anyM fun x => return (← whnf (← inferType x)).isSort

/-- The applications of the constant `c` to `arity` arguments inside `e`. -/
partial def appsOf (c : Name) (arity : Nat) (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.getAppFn.isConstOf c && e.getAppNumArgs == arity then acc.push e else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc

/-- The position, among the fields of a constructor of a type-indexed family, of the field
    that its result's index is (`α` in `Nest.cons {α} a r : Nest α`). -/
def indexField (info : InductiveVal) (ctor : Name) : MetaM Nat := do
  let cinfo ← getConstInfoCtor ctor
  forallTelescopeReducing cinfo.type fun xs res => do
    let idx := (← whnf res).getAppArgs[info.numParams]!
    let some p := xs[info.numParams:].toArray.idxOf? idx
      | throwError m!"LeanScript: the constructor `{ctor}` of the type-indexed family \
          `{info.name}` builds a value at the index{indentExpr idx}\nwhich is not a variable: \
          only families whose constructors are generic in the index are supported"
    return p

/-- A type-indexed family, checked (one index, of type `Type`, no universe parameters, every
    constructor generic in the index), and the indices `fun ps α => σ` at which it recurses
    (`fun α => α × α` for `Nest`). -/
def typeFamilySteps (info : InductiveVal) : MetaM (Array Expr) := do
  let bad {α : Type} (why : MessageData) : MetaM α :=
    throwError m!"LeanScript: the family `{info.name}` is indexed by a type, and {why}"
  unless info.levelParams.isEmpty do bad m!"is universe polymorphic"
  unless info.numIndices == 1 do bad m!"has {info.numIndices} indices: only one type index is \
    supported"
  forallTelescopeReducing info.type fun xs _ => do
    unless ← isDefEq (← inferType xs[info.numParams]!) (mkSort Level.one) do
      bad m!"its index is not a `Type`"
  let mut steps : Array Expr := #[]
  for ctor in info.ctors do
    let p ← indexField info ctor
    let cinfo ← getConstInfoCtor ctor
    steps ← forallTelescopeReducing cinfo.type fun xs _ => do
      let ps := xs[:info.numParams].toArray
      let a := xs[info.numParams + p]!
      let mut steps := steps
      for x in xs[info.numParams:] do
        if x == a then continue
        for occ in appsOf info.name (info.numParams + 1) (← instantiateMVars (← inferType x)) do
          let σ := occ.getAppArgs[info.numParams]!
          if σ == a || !σ.containsFVar a.fvarId! then continue
          if σ.hasLooseBVars || (appsOf info.name (info.numParams + 1) σ).size > 0 ||
              xs.any (fun y => y != a && !ps.contains y && σ.containsFVar y.fvarId!) then
            bad m!"the constructor `{ctor}` recurses at the index{indentExpr σ}\nwhich is not a \
              type built from the index alone"
          let st ← mkLambdaFVars (ps.push a) σ
          unless steps.contains st do steps := steps.push st
      return steps
  return steps

/-- The fields of a constructor of the element type for the recursive index `s` (a type
    mentioning the local `α`): the fields of `s` when it is a structure (`α × α` gives `α`
    and `α`), with the structure's name; otherwise `s` itself. -/
def stepFields (s : Expr) : MetaM (Option Name × Array Expr) := do
  let s ← whnf s
  let some (c, us) := s.getAppFn.const? | return (none, #[s])
  unless isStructure (← getEnv) c do return (none, #[s])
  let info ← getConstInfoInduct c
  unless info.numIndices == 0 && !info.isRec && s.getAppNumArgs == info.numParams do
    return (none, #[s])
  let cinfo ← getConstInfoCtor info.ctors[0]!
  let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) s.getAppArgs
  forallTelescopeReducing ty fun ys _ => do
    let mut out := #[]
    for y in ys do
      let d ← y.fvarId!.getDecl
      if (← isProp d.type) || d.binderInfo.isInstImplicit ||
          ys.any (d.type.containsFVar ·.fvarId!) then
        return (none, #[s])
      out := out.push d.type
    return if out.isEmpty then (none, #[s]) else (some c, out)

/-- The name of the element type of a type-indexed family. -/
def elemName (info : InductiveVal) : Name := info.name ++ `Elem

/-- The element type of a type-indexed family with the recursive indices `steps` (non-empty),
    declared if it does not exist yet: `leaf : α → Elem α` and one `node` (`node0`, `node1`,
    … when there are several) per recursive index. -/
def ensureElem (info : InductiveVal) (steps : Array Expr) : MetaM Name := do
  let n := elemName info
  if let some c := (← getEnv).find? n then
    unless c matches .inductInfo _ do
      throwError m!"LeanScript: `{n}` is already declared, and is not the element type of the \
        type-indexed family `{info.name}`"
    return n
  let decl ← forallBoundedTelescope info.type info.numParams fun ps _ => do
    withLocalDeclD `α (mkSort Level.one) fun α => do
      let self := mkAppN (mkConst n) (ps.push α)
      let leaf : Constructor :=
        { name := n ++ `leaf, type := ← mkForallFVars (ps.push α) (← mkArrow α self) }
      let mut ctors := #[leaf]
      for k in [0:steps.size] do
        let (_, fs) ← stepFields ((steps[k]!).beta (ps.push α))
        let mut ty := self
        for f in fs.reverse do ty ← mkArrow (f.replaceFVar α self) ty
        let nm := if steps.size = 1 then `node else .mkSimple s!"node{k}"
        ctors := ctors.push { name := n ++ nm, type := ← mkForallFVars (ps.push α) ty }
      let ty ← mkForallFVars ps (.forallE `α (mkSort Level.one) (mkSort Level.one) .default)
      -- the parameters of the constructors are implicit, as in a declared `inductive`
      let rec implicit : Nat → Expr → Expr
        | k + 1, .forallE x d b _ => .forallE x d (implicit k b) .implicit
        | _, e => e
      let cs := ctors.map fun c => { c with type := implicit (info.numParams + 1) c.type }
      return Declaration.inductDecl [] (info.numParams + 1)
        [{ name := n, type := ty, ctors := cs.toList }] false
  try addDecl decl
  catch e => throwError m!"LeanScript: the element type `{n}` of the type-indexed family \
    `{info.name}` is not a valid inductive type: {e.toMessageData}"
  compileDecls #[n]
  mkCasesOn n
  return n

/-- One peeling step: `τ` is the recursive index `st` at `σ`. -/
def matchStep (ps : Array Expr) (st τ : Expr) : MetaM (Option Expr) :=
  withNewMCtxDepth do
    let m ← mkFreshExprMVar (mkSort Level.one)
    unless ← withReducible (isDefEq τ (st.beta (ps.push m))) do return none
    let r ← instantiateMVars m
    return if r.hasMVar then none else some r

/-- The index of the datatype that `I ps τ` is read as: `Elem ps B`, where `B` is `τ` with the
    recursive indices peeled off (`Nat × Nat` peels to `Nat`), or `τ` itself when the family
    recurses only at its index. -/
def canonIndex (info : InductiveVal) (ps : Array Expr) (τ : Expr) : MetaM Expr := do
  let steps ← typeFamilySteps info
  if steps.isEmpty then return τ
  let n ← ensureElem info steps
  let mut τ := τ
  for _ in [0:10000] do
    if τ.isAppOf n then return τ
    let mut next := none
    for st in steps do
      if let some σ ← matchStep ps st τ then
        next := some σ
        break
    let some σ := next | break
    τ := σ
  return mkAppN (mkConst n) (ps.push τ)

/-- For a value `a : τ` of a field of type `α` at the index `τ` of a type-indexed family whose
    datatype has the index `Elem ps B`: the same value in `Elem ps B` (`(2, 3)` at `Nat × Nat`
    is `node (leaf 2) (leaf 3)` over `Nat`), as a Lean expression. -/
partial def injectElem (info : InductiveVal) (ps : Array Expr) (τ a : Expr) : MetaM Expr := do
  let steps ← typeFamilySteps info
  if steps.isEmpty then return a
  let n ← ensureElem info steps
  if (← whnf τ).isAppOf n then return a
  for k in [0:steps.size] do
    let st := steps[k]!
    let some σ ← matchStep ps st τ | continue
    let nm := if steps.size = 1 then `node else .mkSimple s!"node{k}"
    let node := mkAppN (mkConst (n ++ nm)) (ps.push (← canonIndex info ps σ).appArg!)
    -- the fields as `stepFields` splits them: `some true` for a field of type `α` (injected
    -- in turn), `some false` for one that does not mention `α`
    let (str?, kinds) ← withLocalDeclD `α (mkSort Level.one) fun α => do
      let (str?, fs) ← stepFields (st.beta (ps.push α))
      return (str?, fs.map fun f => if f == α then some true
        else if f.containsFVar α.fvarId! then none else some false)
    let vals ← match str? with
      | none => pure #[a]
      | some c =>
        let ctor := getStructureCtor (← getEnv) c
        let a' ← whnfR a
        if a'.isAppOfArity ctor.name (ctor.numParams + ctor.numFields) then
          pure a'.getAppArgs[ctor.numParams:].toArray
        else pure ((List.range kinds.size).toArray.map fun j => mkProj c j a)
    let mut args := #[]
    for j in [0:kinds.size] do
      match kinds[j]! with
      | some true => args := args.push (← injectElem info ps σ vals[j]!)
      | some false => args := args.push vals[j]!
      | none =>
        throwError m!"LeanScript: the value{indentExpr a}\nat the index{indentExpr τ}\nof \
          `{info.name}` cannot be put in `{n}`: the index `{st}` holds the index other than \
          as a field of its own"
    return mkAppN node args
  return mkAppN (mkConst (n ++ `leaf)) (ps.push τ |>.push a)

/-- Which fields of a constructor (the locals `xs`, after its parameters; `res` its result
    type) are erased: the proofs and instances (`isErasedField`), and, for a constructor of an
    inductive family, the fields that only name an index: a field `x` that occurs in the
    indices of the result type and is itself an index of the type of a field kept.  In
    `Vec.cons {n} (a : α) (v : Vec α n) : Vec α (n + 1)`, `n` is the index of `v`: the
    language erases the indices of a family (`Vec α n` is the datatype `Vec α` of every
    length, a linked list), and `n` is recovered from `v` (its length), so it is not a
    field.  A field of an ordinary structure is never erased this way (`Matrix.rows` stays,
    even though `cells : Vec _ rows` mentions it). -/
def erasedFields (xs : Array Expr) (res : Expr) : MetaM (Array Bool) := do
  let base ← xs.mapM fun x => do
    let d ← x.fvarId!.getDecl
    isErasedField d.binderInfo d.type
  -- the field that is the index of a type-indexed family (`α` in `Nest.cons {α} a r`) is
  -- erased: the family is read at one index (`canonIndex`)
  if let some (info, _, _, resIdx) ← familyApp? (← whnf res) then
    if ← typeIndexed info then
      return (xs.zip base).map fun (x, e) => e || resIdx.contains x
  let some (_, _, _, resIdx) ← familyApp? (← whnf res) | return base
  let mut det : Array FVarId := #[]
  for (y, e) in xs.zip base do
    if e then continue
    if let some (_, _, _, is) ← familyApp? (← whnf (← inferType y)) then
      for i in is do
        if i.isFVar then det := det.push i.fvarId!
  return (xs.zip base).map fun (x, e) =>
    e || (det.contains x.fvarId! && resIdx.any (·.containsFVar x.fvarId!))

/-- The erased-field mask of a constructor at the given parameters (`erasedFields`). -/
def ctorErasedMask (ctor : Name) (us : List Level) (params : Array Expr) : MetaM (Array Bool) := do
  let cinfo ← getConstInfoCtor ctor
  let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
  forallTelescopeReducing ty fun xs res => erasedFields xs res

/-- An instance of an inductive family at *closed* indices (`Vec Nat 0`) is checked before its
    indices are erased: when only field-less constructors can build a value at these indices,
    it has no value, one, or two, and is refused like every other such type. -/
def checkClosedIndices (e : Expr) (info : InductiveVal) (us : List Level)
    (params indices : Array Expr) : MetaM Unit := do
  let mut matching : Array Name := #[]
  let mut allNullary := true
  for ctor in info.ctors do
    let cinfo ← getConstInfoCtor ctor
    let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    let ok ← withoutModifyingState do
      let (_, _, res) ← forallMetaTelescopeReducing ty
      let ris := (← whnf res).getAppArgs[info.numParams:].toArray
      (ris.zip indices).allM fun (a, b) => isDefEq a b
    if ok then
      matching := matching.push ctor
      if (← ctorErasedMask ctor us params).any (!·) then allNullary := false
  unless allNullary do return
  match matching.size with
  | 0 => throwError m!"{errPrefix}: the type{indentExpr e}\nhas no value (no constructor \
      builds a value at these indices)"
  | 1 => throwError m!"{errPrefix}: the type{indentExpr e}\nhas one value (only \
      `{matching[0]!}` builds a value at these indices, and it has no field)"
  | 2 => throwError m!"{errPrefix}: the type{indentExpr e}\nhas two values (only \
      field-less constructors build a value at these indices): two points are only ever \
      `Bool`"
  | _ => return

/-- The carrier `α` of a quotient type `@Quot α r` (in head normal form: `Quotient s` is
    `Quot Setoid.r`).  The language has no quotients: a quotient is read as its carrier, a
    value of it as one of its representatives.  This is faithful for the functions Lean can
    write on a quotient (`Quot.lift f h q` is `f` of any representative of `q`, and `h` says
    that the result does not depend on which), but the carrier may have more values than the
    quotient (`Quot (· % 2 = · % 2)` on `Nat` has two values, it is read as `Nat`). -/
def quotCarrier? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Quot 2 then some e.appFn!.appArg! else none

/-- Normalise a type: head normal form, type arguments normalised.  The indices of an
    inductive family are erased: `Vec α n` is normalised to `Vec α` (the datatype of vectors
    of every length), after a check that at closed indices it has at least three values
    (`checkClosedIndices`).  With `check := false` the check is skipped: the type of a
    subterm (`Vec.nil : Vec Nat 0` inside `Vec.cons 2 Vec.nil`) is only the datatype its value
    belongs to, the erased `Vec Nat`; declared types (of fields, parameters, `let`s, results)
    are checked. -/
partial def normType (e : Expr) (check : Bool := true) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e with
  | .forallE n a b bi =>
    if b.hasLooseBVars then return e
    return .forallE n (← normType a check) (← normType b check) bi
  | _ =>
    let fn := e.getAppFn
    -- a quotient is read as its carrier: `Quot r` (and `Quotient s`, which unfolds to it) is
    -- the type of the representatives, and a value is a representative (`quotCarrier?`)
    if let some α := quotCarrier? e then return ← normType α check
    if fn.isConst then
      if let some (info, us, params, indices) ← familyApp? e then
        if ← typeIndexed info then
          let params ← params.mapM (normArg check)
          let τ ← normType indices[0]! check
          return mkAppN fn (params.push (← canonIndex info params τ))
        if check && !indices.any (fun i => i.hasFVar || i.hasMVar) then
          checkClosedIndices e info us params indices
        return mkAppN fn (← params.mapM (normArg check))
      return mkAppN fn (← e.getAppArgs.mapM (normArg check))
    return e
where
  /-- A type argument is normalised (also an erased family, `Vec Nat`); a value is kept. -/
  normArg (check : Bool) (a : Expr) : MetaM Expr := do
    if (← isType a) || (← isErasedFamily a) then normType a check else pure a
  /-- Is `a` an inductive family with its indices erased (`Vec Nat`)? -/
  isErasedFamily (a : Expr) : MetaM Bool := do
    let some (c, _) := a.getAppFn.const? | return false
    let some (.inductInfo info) := (← getEnv).find? c | return false
    return info.numIndices > 0 && a.getAppNumArgs == info.numParams

/-- A natural number literal, if the expression evaluates to one. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.nat? then return some n
  if let some n := e.rawNatLit? then return some n
  let e' ← whnf e
  if let some n := e'.rawNatLit? then return some n
  evalNat e

/-- The head of a (normalised) type. -/
def classify (e : Expr) : MetaM Head := do
  if let .forallE _ a b _ := e then
    if b.hasLooseBVars then fail m!"dependent function type{indentExpr e}"
    return .fn a b
  if e.isFVar then
    if (← whnf (← inferType e)) == mkSort Level.one then return .var e.fvarId!
    fail m!"the type{indentExpr e}\nis a local that is not a type variable"
  let some (c, _) := e.getAppFn.const? | fail m!"not a type former application{indentExpr e}"
  let args := e.getAppArgs
  let p (s : Lean.Term) : MetaM Head := return .prim s
  match c, args.size with
  | ``Bool, 0 => p (← `(LeanPrimTy.bool))
  | ``Nat, 0 => p (← `(LeanPrimTy.nat))
  | ``Int, 0 => p (← `(LeanPrimTy.int))
  | ``UInt8, 0 => p (← `(LeanPrimTy.uint8))
  | ``UInt16, 0 => p (← `(LeanPrimTy.uint16))
  | ``UInt32, 0 => p (← `(LeanPrimTy.uint32))
  | ``UInt64, 0 => p (← `(LeanPrimTy.uint64))
  | ``Int8, 0 => p (← `(LeanPrimTy.int8))
  | ``Int16, 0 => p (← `(LeanPrimTy.int16))
  | ``Int32, 0 => p (← `(LeanPrimTy.int32))
  | ``Int64, 0 => p (← `(LeanPrimTy.int64))
  | ``Char, 0 => p (← `(LeanPrimTy.char))
  | ``String, 0 => p (← `(LeanPrimTy.string))
  | ``String.Pos.Raw, 0 => p (← `(LeanPrimTy.stringPosRaw))
  | ``Substring.Raw, 0 => p (← `(LeanPrimTy.substringRaw))
  | ``String.Slice, 0 => p (← `(LeanPrimTy.stringSlice))
  | ``Float, 0 => p (← `(LeanPrimTy.float))
  | ``Float32, 0 => p (← `(LeanPrimTy.float32))
  | ``Float.Model, 0 => p (← `(LeanPrimTy.floatModel))
  | ``Float32.Model, 0 => p (← `(LeanPrimTy.float32Model))
  | ``BitVec, 1 =>
    let some n ← natLit? args[0]! | fail m!"the width of{indentExpr e}\nis not a numeral"
    if n = 0 then fail m!"`BitVec 0` has one value"
    if n = 1 then fail m!"`BitVec 1` has two values: two points are only ever `Bool`"
    p (← `(LeanPrimTy.bitvec $(quote n)))
  | ``String.Pos, 1 =>
    let some s := (match (← whnf args[0]!) with | .lit (.strVal s) => some s | _ => none)
      | fail m!"the string of{indentExpr e}\nis not a literal"
    if s = "" then fail m!"`String.Pos \"\"` has one value"
    if s.length = 1 then
      fail m!"`String.Pos {repr s}` has two values: two points are only ever `Bool`"
    p (← `(LeanPrimTy.stringPos $(quote s)))
  | ``Fin, 1 =>
    -- `Fin n` is a wrapper of its `Nat` value (the bound is a proof, erased), so it is `nat`;
    -- but a *numeral* bound of `0`, `1` or `2` makes it a type of no, one or two values
    if let some n ← natLit? args[0]! then
      if n = 0 then fail m!"`Fin 0` has no value"
      if n = 1 then fail m!"`Fin 1` has one value"
      if n = 2 then fail m!"`Fin 2` has two values: two points are only ever `Bool`"
    return .node e
  | ``Array, 1 => return .array args[0]!
  | ``Thunk, 1 =>
    fail m!"`Thunk` is not a type of the language: a delay denotes the value it stands for, \
      so `Thunk Bool` would be a second type of two values{indentExpr e}"
  | _, _ =>
    unless ((← getEnv).find? c).any (·.isInductive) do
      fail m!"`{c}` is not an inductive type{indentExpr e}"
    return .node e

/-- The built-in table of enum numberings: the number the first constructor prints as.
    `Ordering` prints as `-1, 0, 1`. -/
def enumShift (c : Name) : Int :=
  if c == ``Ordering then -1 else 0

/-- Does the type `e` mention, directly or through the constructors of the inductive types it
    mentions (transitively, by constant), one of the inductive types `targets`?  Used to tell
    whether a field `Fin m → T` of a constructor of `targets` is on a recursive cycle. -/
partial def reachesInductive (targets : Array Name) (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let isInd (c : Name) : Bool := (env.find? c).any (·.isInductive)
  let mut todo : Array Name := e.getUsedConstants.filter isInd
  let mut seen : NameSet := {}
  while h : 0 < todo.size do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if targets.contains c then return true
    if seen.contains c then continue
    seen := seen.insert c
    let some (.inductInfo info) := env.find? c | continue
    for ctor in info.ctors do
      let some cinfo := env.find? ctor | continue
      for d in cinfo.type.getUsedConstants do
        if isInd d && !seen.contains d then todo := todo.push d
  return false

/-- Is the field arrow `a → b` of the constructor `ctor` (whose fields are the locals `deps`)
    read as `Nat → Option b`?  That is the case when its domain is `Fin m` for a bound `m`
    that is an earlier field (so it may be `0`; a bound such as `m + 1` is never `0`, and
    `Fin (m + 1) → Loop` keeps the plain erasure, under which a recursive type whose every node
    has a child has no value, as in Lean), and its codomain is on a recursive
    cycle through the constructor's own type (`node : (m : Nat) → (Fin m → Rose) → Rose`).
    Erased to `Nat → Rose`, such a field would have no base value (every value of `Nat → Rose`
    needs a `Rose` already), so the type would have no finite value in the language; with
    `Option`, the children are `some` below `m` and `none` from `m` on, and `m = 0` is a
    value (`fun _ => none`).  A codomain that is not on such a cycle keeps the plain erasure
    (`Chunk.data : Fin n → Nat` is `Nat → Nat`). -/
def finOptArrow (ctor : Name) (deps : Array Expr) (a b : Expr) : MetaM Bool := do
  let a ← whnf a
  unless a.isAppOfArity ``Fin 1 && deps.contains a.appArg! do return false
  let some (.ctorInfo cinfo) := (← getEnv).find? ctor | return false
  let some (.inductInfo info) := (← getEnv).find? cinfo.induct | return false
  reachesInductive info.all.toArray b

mutual

/-- The erasure of a field type `t` that depends on the locals `deps` (the earlier fields of
    the constructor, and the arguments of the dependent arrows around `t`).  The language has
    no dependent types, so such a dependency is erased, when it only goes through:

    * the domain or codomain of an arrow (`Fin n → Nat` is `Nat → Nat`); a dependent arrow
      `(i : Fin 3) → Fin (i + 1)` is erased to a plain one, `Nat → Nat`;
    * a type argument (`Array (Fin n)`, `Option (Fin n)`, `Fin n × Nat` are `Array Nat`, …);
    * an inductive type with one constructor of one relevant field, whose other fields are
      proofs: the type is that field (`Fin n` is `Nat`, `Vector α n` is `Array α`,
      `{x : Nat // x < n}` is `Nat`, `BitVec n` is `Nat`), as the translation of such a
      wrapper always is.

    Anything else (a value argument of an inductive type with several fields or constructors,
    a type computed from the value, `cond b Nat Bool`, …) is refused.  The erasure never
    mentions `deps`; `ctor` is the constructor, named by the errors.  A type that mentions no local of `deps` and no dependent arrow is only
    normalised. -/
partial def eraseDeps (ctor : Name) (deps : Array Expr) (t : Expr) : MetaM Expr := do
  let t ← normType t
  let mentions (e : Expr) : Bool := deps.any fun d => e.containsFVar d.fvarId!
  match t with
  | .forallE n a b bi =>
    let a' ← eraseDeps ctor deps a
    -- `Fin m → T` on a recursive cycle is `Nat → Option T` (`finOptArrow`)
    let opt ← finOptArrow ctor deps a b
    let wrap (b' : Expr) : MetaM Expr := if opt then mkAppM ``Option #[b'] else pure b'
    if !b.hasLooseBVars then return .forallE n a' (← wrap (← eraseDeps ctor deps b)) bi
    withLocalDecl n bi a fun x => do
      let b' ← wrap (← eraseDeps ctor (deps.push x) (b.instantiate1 x))
      return .forallE n a' (b'.abstract #[x]) bi
  | _ =>
    unless mentions t do return t
    let refuse {α : Type} : MetaM α :=
      fail m!"a field of the constructor `{ctor}` has the type{indentExpr t}\nwhich depends on the value of an earlier field (or of the \
        argument of a dependent arrow) in a way that cannot be erased: only arrows, type \
        arguments, and inductive types with one constructor of one field besides proofs \
        (`Fin n`, `Vector α n`, `\{x // p x}`) are erased to a non-dependent type"
    let some (c, us) := t.getAppFn.const? | refuse
    let args := t.getAppArgs
    if c == ``Array && args.size == 1 then
      return mkApp (.const c us) (← eraseDeps ctor deps args[0]!)
    let some (.inductInfo info) := (← getEnv).find? c | refuse
    unless args.size = info.numParams do refuse
    -- the dependency is only in type arguments: erase them
    let valueDep ← args.anyM fun a => return mentions a && !(← isType a)
    unless valueDep do
      return mkAppN (.const c us) (← args.mapM fun a => do
        if mentions a then eraseDeps ctor deps a else pure a)
    -- a wrapper of one relevant field: the field
    unless info.ctors.length == 1 do refuse
    let ctors ← readCtors t
    let some (_, fs) := ctors[0]? | refuse
    unless fs.size == 1 do refuse
    eraseDeps ctor deps fs[0]!

/-- The constructors of an inductive instance: their names and their relevant fields, in
    declaration order.  The instance may mention type variables.  A field whose type depends
    on an earlier field is read through its erasure (`eraseDeps`): `data : Fin n → Nat` is a
    field of type `Nat → Nat`. -/
partial def readCtors (e : Expr) : MetaM (Array (Name × Array Expr)) := do
  let some (c, us) := e.getAppFn.const? | fail m!"not an inductive instance{indentExpr e}"
  let info ← getConstInfoInduct c
  -- an inductive family is read with its indices erased (`Vec α`, see `normType`)
  let params := e.getAppArgs[:info.numParams].toArray
  unless params.size = info.numParams do
    fail m!"`{c}` is not fully applied{indentExpr e}"
  -- a type-indexed family is read at its (canonical) index: the constructors' index field is
  -- that index
  let idxVal? ← if ← typeIndexed info then pure (e.getAppArgs[info.numParams]?) else pure none
  info.ctors.toArray.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    forallTelescopeReducing ty fun xs res => do
      let erased ← erasedFields xs res
      let resIdx := (← whnf res).getAppArgs[info.numParams]?
      let mut fields : Array Expr := #[]
      for (x, er) in xs.zip erased do
        let decl ← x.fvarId!.getDecl
        let t := match idxVal?, resIdx with
          | some v, some (.fvar a) => decl.type.replaceFVarId a v
          | _, _ => decl.type
        if er then continue
        if (← whnf t).isSort then
          fail m!"the constructor `{ctor}` has a field whose value is a type \
            (existential typing is not supported)"
        let t' ← eraseDeps ctor xs t
        if xs.any (fun d => t'.containsFVar d.fvarId!) then
          fail m!"a field of the constructor `{ctor}` has a type that depends on an earlier \
            field{indentExpr t}"
        fields := fields.push t'
      return (ctor, fields)

end

/-- The inductive instances a type mentions directly. -/
partial def occurrences (e : Expr) : MetaM (Array Expr) := do
  match ← classify e with
  | .prim _ | .var _ => return #[]
  | .fn a b => return (← occurrences a) ++ (← occurrences b)
  | .array a => occurrences a
  | .node n => return #[n]

end LeanScript.Gen

end
