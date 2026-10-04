module

public import LeanScript.GenElab.Read.Nest
public meta import Lean.Elab.Command
public meta import Lean.Meta.Constructions.CasesOn

@[expose] public section

meta section

set_option autoImplicit false

/-!
# Reading Lean types

The first stage shared by `leanscript_signature`, `#leanscript_get_ty` and
`#leanscript_get_ctor`: a Lean type is normalised (`normType`), its head is classified
(`classify`: a leaf, `→`, `Array`, a delay `Thunk τ` / `Unit → τ`, a type variable, or an
inductive instance), and
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
    isErasedCtorField d.binderInfo d.type
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

/-- `Nat`, the stand-in for a type parameter (`## Polymorphism`). -/
def tyParamStandIn : Expr := mkConst ``Nat

/-- Is `T` (in weak head normal form) the sort `Type`, the type of a type parameter? -/
def isTypeSort (T : Expr) : MetaM Bool := do
  match ← whnf T with
  | .sort l => return l.normalize == Level.one
  | _ => return false

/-- The stand-in for a parameter of type `T`: `Nat` when `T` is `Type`, and `fun _ … => Nat`
    when `T` is the kind of a type constructor (`f : Type → Type` in
    `fold {f : Type → Type} [Foldable f]`).  A type constructor is erased like a type: the body
    has no instance to look into a value of `f α` with (an instance of a class on `f`, such as
    `Foldable f`, only passes it on), so reading every `f α` as the stand-in `Nat` translates
    every instance once the types are erased. -/
partial def typeStandIn? (T : Expr) : MetaM (Option Expr) := do
  if ← isTypeSort T then return some tyParamStandIn
  match ← whnf T with
  | .forallE n d b bi =>
    if b.hasLooseBVars then return none
    unless (← typeStandIn? d).isSome do return none
    let some b' ← typeStandIn? b | return none
    return some (.lam n d b' bi)
  | _ => return none

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

/-- Is the type `Unit` (or `PUnit`), the domain of a delay `Unit → τ`? -/
def isUnitType (a : Expr) : MetaM Bool := do
  let a ← whnfR a
  return a.isConstOf ``Unit || a.isAppOfArity ``PUnit 0 || a.getAppFn.isConstOf ``PUnit

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
partial def eraseDeps (ctor : Name) (deps : Array Expr) (t : Expr) (tyBinders : Bool := false) :
    MetaM Expr := do
  let t ← normType t
  let mentions (e : Expr) : Bool := deps.any fun d => e.containsFVar d.fvarId!
  match t with
  | .forallE n a b bi =>
    -- a field of a polymorphic type (`foldMap : {α m : Type} → [Monoid m] → (α → m) → f α → m`
    -- of a class): read at the stand-ins (`## Polymorphism` of `ToTerm`), like a type
    -- parameter; a use of the field passes the stand-ins (`appArgs`)
    if tyBinders && b.hasLooseBVars then
      if let some v ← typeStandIn? a then
        return ← eraseDeps ctor deps (← Core.betaReduce (b.instantiate1 v)) tyBinders
    let eraseDeps (ctor : Name) (deps : Array Expr) (t : Expr) : MetaM Expr :=
      eraseDeps ctor deps t tyBinders
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
        let t' ← eraseDeps ctor xs t (tyBinders := true)
        if xs.any (fun d => t'.containsFVar d.fvarId!) then
          fail m!"a field of the constructor `{ctor}` has a type that depends on an earlier \
            field{indentExpr t}"
        fields := fields.push t'
      return (ctor, fields)

end

/-- The applications of constants in a closed type (`Html`, `RoseTree Nat`, `Prod Html Nat`,
    …), outermost first. -/
partial def constApps (e : Expr) : Array Expr :=
  match e with
  | .app .. =>
    let rest := e.getAppArgs.foldl (fun acc a => acc ++ constApps a) #[]
    if e.getAppFn.isConst then #[e] ++ rest else rest
  | .const .. => #[e]
  | .forallE _ a b _ => constApps a ++ constApps b
  | .mdata _ b => constApps b
  | _ => #[]

/-- Is the list type `L = List T` a field type of a constructor of a nested inductive type
    that `T` mentions (`Html.elem : String → List Html → Html`, `RoseTree.node : α →
    List (RoseTree α) → …` at `List (RoseTree Nat)`, `Obj.mk : List (String × Obj) → Obj` at
    `List (String × Obj)`)?  Such a list is part of the recursion of that type, and a recursive
    occurrence cannot sit inside the built-in list (`Ty.list`): under `builtinListOption` it is
    then still read as a datatype (`nil | cons T L`), a member of the block of that type,
    everywhere the program mentions it (the reading of a type does not depend on where it
    occurs). -/
def listNestedInElem (T L : Expr) : MetaM Bool := do
  for I in constApps T do
    let some (c, us) := I.getAppFn.const? | continue
    let some (.inductInfo info) := (← getEnv).find? c | continue
    unless info.numNested > 0 && info.numIndices == 0 do continue
    let args := I.getAppArgs
    unless args.size == info.numParams do continue
    if I.hasLooseBVars then continue
    let found ← info.ctors.anyM fun ctor => do
      let cty ← instantiateForall ((← getConstInfo ctor).instantiateTypeLevelParams us) args
      forallTelescopeReducing cty fun xs _ => xs.anyM fun x => do
        let t ← instantiateMVars (← inferType x)
        return (t.find? (· == L)).isSome
    if found then return true
  return false

/-- The head of a (normalised) type. -/
partial def classify (e : Expr) : MetaM Head := do
  if let .forallE _ a b _ := e then
    if b.hasLooseBVars then
      -- a dependency that only goes through what the translation erases (the predicate of a
      -- subtype, the bound of a `Fin`, a type argument: `(n : Nat) → {m // m ≥ n - 10}` is
      -- `Nat → Nat`) is erased (`eraseDeps`); any other one is refused
      let e' ← try eraseDeps .anonymous #[] e
        catch _ => fail m!"dependent function type{indentExpr e}"
      if let .forallE _ _ b' _ := e' then
        unless b'.hasLooseBVars do return ← classify e'
      fail m!"dependent function type{indentExpr e}"
    -- `Unit → b` is a delay of `b` (`Unit` itself has one value, so it is no type)
    if ← isUnitType a then return .lazy b
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
  | ``HashableFloat, 0 => p (← `(LeanPrimTy.float))
  | ``HashableFloat32, 0 => p (← `(LeanPrimTy.float32))
  | ``Float.Model, 0 => p (← `(LeanPrimTy.floatModel))
  | ``Float32.Model, 0 => p (← `(LeanPrimTy.float32Model))
  | ``Lean.Name, 0 => return .leanName
  | ``BitVec, 1 =>
    let some n ← natLit? args[0]! | fail m!"the width of{indentExpr e}\nis not a numeral"
    if n = 0 then fail m!"`BitVec 0` has one value"
    if n = 1 then fail m!"`BitVec 1` has two values: two points are only ever `Bool`"
    -- the proof of `2 ≤ n` as a term, not the default `by decide`: a pending tactic block is a
    -- metavariable unification cannot assign, so the type would not unify with the `bitvec n`
    -- of an extern's signature
    p (← `(LeanPrimTy.bitvec $(quote n) (Nat.le_of_ble_eq_true rfl)))
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
  | ``List, 1 =>
    if ← useBuiltinList then
      unless ← listNestedInElem args[0]! e do return .list args[0]!
    return .node e
  | ``Thunk, 1 => return .thunk args[0]!
  | ``Std.HashMap, 4 =>
    -- a hash map with string keys (and `String`'s own instances) is the built-in `Ty.strMap`
    -- (a JavaScript object); any other hash map is read as the structure it is
    if (← whnf args[0]!).isConstOf ``String then
      let beq ← synthInstance (← mkAppM ``BEq #[mkConst ``String])
      let hash ← synthInstance (← mkAppM ``Hashable #[mkConst ``String])
      unless (← withReducibleAndInstances (isDefEq args[2]! beq)) &&
          (← withReducibleAndInstances (isDefEq args[3]! hash)) do
        fail m!"the hash map{indentExpr e}\nhas string keys compared or hashed by instances \
          other than `String`'s own: only those are the keys of a JavaScript object"
      return .strMap args[1]!
    return .node e
  | _, _ =>
    unless ((← getEnv).find? c).any (·.isInductive) do
      fail m!"`{c}` is not an inductive type{indentExpr e}"
    return .node e

/-- The inductive instances a type mentions directly. -/
partial def occurrences (e : Expr) : MetaM (Array Expr) := do
  match ← classify e with
  | .prim _ | .leanName | .var _ => return #[]
  | .fn a b => return (← occurrences a) ++ (← occurrences b)
  | .array a | .list a | .strMap a | .thunk a | .lazy a => occurrences a
  | .node n => return #[n]

end LeanScript.Gen

end
