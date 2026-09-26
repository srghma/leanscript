module

public import LeanScript.Term
public meta import Lean.Elab.Command

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
field is read through its erasure (`eraseDeps`): `Fin n → Nat` is `Nat → Nat`.

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

/-- Normalise a type: head normal form, type arguments normalised. -/
partial def normType (e : Expr) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e with
  | .forallE n a b bi =>
    if b.hasLooseBVars then return e
    return .forallE n (← normType a) (← normType b) bi
  | _ =>
    let fn := e.getAppFn
    if fn.isConst then
      let args ← e.getAppArgs.mapM fun a => do
        if (← isType a) then normType a else pure a
      return mkAppN fn args
    return e

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

/-- Is a field of this type erased: a proof or an instance?  (A `Unit` field is **not**
    erased: `Unit` has one value, so it has no type in the language, and a constructor with
    such a field is refused like every other unit-like type.  Two values are `Bool`, never
    `Option Unit`.) -/
def isErasedField (bi : BinderInfo) (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if bi.isInstImplicit then return true
  return (← isClass? t).isSome

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
    if !b.hasLooseBVars then return .forallE n a' (← eraseDeps ctor deps b) bi
    withLocalDecl n bi a fun x => do
      let b' ← eraseDeps ctor (deps.push x) (b.instantiate1 x)
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
    unless info.numIndices = 0 && args.size = info.numParams do refuse
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
  if info.numIndices ≠ 0 then
    fail m!"`{c}` is an inductive family with indices, which is not supported{indentExpr e}"
  let params := e.getAppArgs
  unless params.size = info.numParams do
    fail m!"`{c}` is not fully applied{indentExpr e}"
  info.ctors.toArray.mapM fun ctor => do
    let cinfo ← getConstInfoCtor ctor
    let ty ← instantiateForall (cinfo.instantiateTypeLevelParams us) params
    forallTelescopeReducing ty fun xs _ => do
      let mut fields : Array Expr := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let t := decl.type
        if ← isErasedField decl.binderInfo t then continue
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
