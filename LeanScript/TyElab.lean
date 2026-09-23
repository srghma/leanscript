open Lean Meta Elab Command

namespace LeanScript

/-! ## Rendering a `Ty` -/

mutual

/-- A one-line rendering of a type of the term language, as an s-expression. -/
partial def tyStr : Ty → String
  | .prim p => p.pretty
  | .fn a b => "(fn " ++ tyStr a ++ " " ++ tyStr b ++ ")"
  | .primCovariant (.array a) => "(array " ++ tyStr a ++ ")"
  -- | .primCovariant (.task a) => "(task " ++ tyStr a ++ ")"
  -- | .primCovariant (.promise a) => "(promise " ++ tyStr a ++ ")"
  | .primCovariant (.thunk a) => "(thunk " ++ tyStr a ++ ")"
  | .primCovariant (.lazy a) => "(lazy " ++ tyStr a ++ ")"
  | .enum e => "(enum " ++ toString e.nOfConstructors ++ " from " ++ toString e.shift ++ ")"
  | .record fs => "(record" ++ String.join ((fs.toList).map (fun a => " " ++ tyStr a)) ++ ")"
  | .taggedUnion tu =>
      "(taggedUnion" ++ String.join ((tu.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map tyStr) ++ "]")) ++ ")"
  | .recTaggedUnion l =>
      "(recTaggedUnion" ++ String.join ((l.schema.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recObject fs =>
      "(recObject" ++ String.join ((fs.fields.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .recAlias b => "(recAlias " ++ rtyStr b.body ++ ")"
  | .mutualRecursiveFamily _ => "(mutualRecursiveFamily …)"
  | .withComputedFields b cs =>
      "(withComputedFields " ++ tyStr b ++ " [" ++
        " ".intercalate (cs.toList.map (·.pretty)) ++ "])"

/-- A one-line rendering of a type *inside* a recursive declaration. -/
partial def rtyStr : RTy → String
  | .self => "self"
  | .familyMember i => "(familyMember " ++ toString i ++ ")"
  | .prim p => p.pretty
  | .fn a b => "(fn " ++ rtyStr a ++ " " ++ rtyStr b ++ ")"
  | .primCovariant (.array a) => "(array " ++ rtyStr a ++ ")"
  -- | .primCovariant (.task a) => "(task " ++ rtyStr a ++ ")"
  -- | .primCovariant (.promise a) => "(promise " ++ rtyStr a ++ ")"
  | .primCovariant (.thunk a) => "(thunk " ++ rtyStr a ++ ")"
  | .primCovariant (.lazy a) => "(lazy " ++ rtyStr a ++ ")"
  | .enum e => "(enum " ++ toString e.nOfConstructors ++ " from " ++ toString e.shift ++ ")"
  | .record fs => "(record" ++ String.join ((fs.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .taggedUnion tu =>
      "(taggedUnion" ++ String.join ((tu.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recTaggedUnion l =>
      "(recTaggedUnion" ++ String.join ((l.toList).map (fun fs =>
        " [" ++ " ".intercalate (fs.map rtyStr) ++ "]")) ++ ")"
  | .recObject fs => "(recObject" ++ String.join ((fs.toList).map (fun a => " " ++ rtyStr a)) ++ ")"
  | .recAlias b => "(recAlias " ++ rtyStr b ++ ")"
  | .mutualRecursiveFamily _ => "(mutualRecursiveFamily …)"
  | .withComputedFields b cs =>
      "(withComputedFields " ++ rtyStr b ++ " [" ++
        " ".intercalate (cs.toList.map (·.pretty)) ++ "])"

end

/-! ## Translating a Lean type into a `Ty`

The translation is the one the table in `LeanScript.Ty`'s module doc-comment describes.
It answers `none` for a type the language has no shape for — a type variable, a `Prop`
other than in an erased position, a monad, a dependent function type, a structure with a
field whose type has no `Ty`. -/

/-- The terminal types, by the name of the Lean type. -/
def primOfName : Name → Option LeanPrimTy
  | ``Nat => some .nat
  | ``Int => some .int
  | ``Bool => some .bool
  | ``Char => some .char
  | ``String => some .string
  | ``UInt8 => some .uint8
  | ``UInt16 => some .uint16
  | ``UInt32 => some .uint32
  | ``UInt64 => some .uint64
  | ``Int8 => some .int8
  | ``Int16 => some .int16
  | ``Int32 => some .int32
  | ``Int64 => some .int64
  | ``Float => some .float
  | ``Float32 => some .float32
  | ``String.Pos.Raw => some .stringPosRaw
  | ``Substring.Raw => some .substringRaw
  | ``String.Slice => some .stringSlice
  | _ => none

/-- Is this a type the language erases — a proposition, or a one-value type? -/
def isErasedType (e : Expr) : MetaM Bool := do
  if (← isProp e) then return true
  let e ← whnf e
  match e.getAppFn with
  | .const n _ => return n == ``Unit || n == ``PUnit
  | _ => return false

/-- The result of translating a Lean type. -/
inductive TyResult where
  /-- A type of the language. -/
  | ok (τ : Ty)
  /-- A type the language erases: it carries no value. -/
  | erased
  /-- No shape of the language describes it, for this reason. -/
  | no (reason : String)
  deriving Inhabited

/-- Does the constant `n` occur in this type? -/
def occursIn (n : Name) (e : Expr) : MetaM Bool := do
  return (← instantiateMVars e).find? (fun s => s.isConstOf n) |>.isSome

/-! ### The values a declaration caches

A Lean declaration may cache a value **computed from itself** — `Lean.Name` stores its
own `hash`, declared `@[computed_field]`.  Lean records that by building a second
inductive, `T._impl`, whose constructors carry the cached values ahead of the fields, so
the types of the cached values are read off it and no declaration has to be named here.
`Ty.withComputedFields` is where they land. -/

/-- The terminal types of the values the declaration `n` caches, in declaration order:
    `.inl none` when it caches nothing, and `.inr` with a reason when it caches a value
    of a type that is not terminal, which `Ty.withComputedFields` has no room for. -/
def computedFieldPrimTys (n : Name) :
    MetaM (Sum (Option (NonEmpty.ListCorrectByConstruction.NonEmptyList LeanPrimTy)) String) := do
  let env ← getEnv
  -- no `T._impl`: the declaration has no computed field at all
  let some (.inductInfo _) := env.find? (n ++ `_impl) | return .inl none
  let some (.inductInfo ind) := env.find? n | return .inl none
  for c in ind.ctors do
    let ci ← getConstInfoCtor c
    -- a constructor with no field stores no cached value, so it says nothing about them
    if ci.numFields == 0 then continue
    let some (.ctorInfo cimpl) := env.find? (c ++ `_impl)
      | return .inr s!"`{n}` caches values in a way this translation cannot read"
    let k := cimpl.numFields - ci.numFields
    if k == 0 then return .inl none
    return ← forallTelescopeReducing cimpl.type fun xs _ => do
      let mut tys : List LeanPrimTy := []
      for x in xs[ind.numParams:ind.numParams + k] do
        let t ← whnf (← inferType x)
        let some p := t.getAppFn.constName?.bind primOfName
          | return .inr s!"`{n}` caches a value of a type that is not terminal"
        tys := tys ++ [p]
      match tys with
      | [] => return .inl none
      | t :: ts => return .inl (some ⟨t, ts⟩)
  -- every constructor is field-less, so the cached values are nowhere to be read
  return .inr s!"`{n}` caches values and has no constructor with a field to read them from"

mutual

/-- The `Ty` of a Lean type, if it has one.

    `depth` bounds the recursion: a type whose translation needs more than `depth`
    nested datatypes is refused rather than diverging. -/
partial def toTy (e : Expr) (depth : Nat := 8) : MetaM TyResult := do
  if depth == 0 then return .no "nested too deeply"
  let e ← whnf e
  if (← isProp e) then return .erased
  if e.isSort then return .no "a type or a proposition, which carries no value"
  if e.isForall then
    -- the parameters that carry a value, in order; the erased ones (the proofs) drop
    -- out, and what is left has to be non-dependent
    return ← forallTelescopeReducing e fun xs body => do
      let mut doms : List Ty := []
      let mut kept : Array FVarId := #[]
      for x in xs do
        let d ← inferType x
        if ← isErasedType d then continue
        if d.hasAnyFVar (fun f => kept.contains f) then
          return .no "a dependent function type"
        match ← toTy d (depth - 1) with
        | .ok a => doms := doms ++ [a]; kept := kept.push x.fvarId!
        | .erased => pure ()
        | .no r => return .no r
      if body.hasAnyFVar (fun f => kept.contains f) then
        return .no "a dependent function type"
      match ← toTy body (depth - 1) with
      | .ok r => return .ok (doms.foldr Ty.fn r)
      | .erased => return .no "a function answering with an erased type"
      | .no r => return .no r
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const n _ := f | return .no "not a constant type"
  if let some p := primOfName n then return .ok (.prim p)
  if n == ``Unit || n == ``PUnit then return .erased
  if n == ``Array && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.array a)
    | .erased => return .no "an array of an erased type"
    | .no r => return .no r
  if n == ``List && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (Ty.list a)
    | .erased => return .no "a list of an erased type"
    | .no r => return .no r
  if n == ``Thunk && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.thunk a)
    | .erased => return .no "a thunk of an erased type"
    | .no r => return .no r
  if n == ``Option && args.size == 1 then
    match ← toTy args[0]! (depth - 1) with
    | .ok a => return .ok (.option a)
    | .erased => return .no "an option of an erased type"
    | .no r => return .no r
  if n == ``Prod && args.size == 2 then
    match ← toTy args[0]! (depth - 1), ← toTy args[1]! (depth - 1) with
    | .ok a, .ok b => return .ok (.prod a b)
    | .no r, _ => return .no r
    | _, .no r => return .no r
    | _, _ => return .no "a pair with an erased component"
  -- a user-declared inductive
  let env ← getEnv
  let some (.inductInfo ind) := env.find? n | return .no s!"no shape for `{n}`"
  if ind.all.length > 1 then return .no s!"`{n}` is part of a mutual block"
  -- a recursive declaration: its `Ty` is `Ty.recTaggedUnion`, whose fields are
  -- *descriptions* rather than types, so an occurrence of the declaration among them is
  -- `RTy.self`
  if ind.isRec then
    unless ind.numIndices == 0 do
      return .no s!"`{n}` is an indexed family, which the recursive shapes have no room for"
    unless ind.numParams == 0 do
      return .no s!"`{n}` is a recursive declaration with parameters, which the recursive shapes have no room for"
    let mut ctorRTys : List (List RTy) := []
    for c in ind.ctors do
      let cinfo ← getConstInfoCtor c
      let fields : Sum (List RTy) String ← forallTelescopeReducing cinfo.type fun xs _ => do
        let mut fs : List RTy := []
        for x in xs do
          match ← toRTyField n (← inferType x) depth with
          | .inl (some a) => fs := fs ++ [a]
          | .inl none => pure ()
          | .inr r => return Sum.inr r
        return Sum.inl fs
      match fields with
      | .inr r => return .no r
      | .inl fs => ctorRTys := ctorRTys ++ [fs]
    let some sch := LeanTaggedUnionSchema.ofList? ctorRTys
      | return .no s!"`{n}` is a recursive declaration the tagged-union schema refuses"
    if h : RTy.Wf (.recTaggedUnion sch) then
      return ← withComputedFieldsOf n (.recTaggedUnion ⟨sch, h⟩)
    else
      return .no s!"`{n}` is a recursive declaration with no well-formed shape (it does not mention itself, or it has no value at all)"
  -- the fields of each constructor, with the parameters instantiated
  let mut ctorTys : List (List Ty) := []
  for c in ind.ctors do
    let cinfo ← getConstInfoCtor c
    let cty ← instantiateForall cinfo.type (args.extract 0 ind.numParams)
    let fields : Sum (List Ty) String ← forallTelescopeReducing cty fun xs _ => do
      let mut fs : List Ty := []
      for x in xs do
        match ← toTy (← inferType x) (depth - 1) with
        | .ok a => fs := fs ++ [a]
        | .erased => pure ()
        | .no r => return Sum.inr r
      return Sum.inl fs
    match fields with
    | .inr r => return .no r
    | .inl fs => ctorTys := ctorTys ++ [fs]
  match ctorTys with
  | [] => return .no s!"`{n}` has no constructors"
  | [[]] => return .erased
  | [[a]] => return ← withComputedFieldsOf n a  -- a newtype: the wrapper is erased
  | [fs] =>
      match LeanRecordSchema.ofList? fs with
      | some sch => return ← withComputedFieldsOf n (.record sch)
      | none => return .no "a record of fewer than two fields"
  | _ =>
      if ctorTys.all (·.isEmpty) then
        match Ty.enumOrBool? ctorTys.length 0 with
        | some τ => return ← withComputedFieldsOf n τ
        | none => return .no "an enum of fewer than two constructors"
      else
        match LeanTaggedUnionSchema.ofList? ctorTys with
        | some sch => return ← withComputedFieldsOf n (.taggedUnion sch)
        | none => return .no "a tagged union the schema refuses"

/-- The `Ty` of the declaration `n`, whose shape is `τ`, with the types of the values it
    caches attached — `Ty.withComputedFields` — when it caches any. -/
partial def withComputedFieldsOf (n : Name) (τ : Ty) : MetaM TyResult := do
  match ← computedFieldPrimTys n with
  | .inr r => return .no r
  | .inl none => return .ok τ
  | .inl (some cs) => return .ok (.withComputedFields τ cs)

/-- One field of a constructor of the recursive declaration `n`, as a payload type: an
    occurrence of `n` itself is `RTy.self`, an array whose elements mention `n` is an
    array of payload types, and anything else is a closed `Ty` read as a payload.  The
    answer is `.inr` with a reason when the field has no shape, and `.inl none` when the
    field is erased. -/
partial def toRTyField (n : Name) (t0 : Expr) (depth : Nat) :
    MetaM (Sum (Option RTy) String) := do
  if depth == 0 then return .inr "nested too deeply"
  let t ← whnf t0
  if t.getAppFn.constName? == some n then return .inl (some (RTy.self))
  -- an array of fields: the elements may themselves mention the declaration
  if t.isAppOfArity ``Array 1 then
    let a := t.appArg!
    if (← occursIn n a) then
      match ← toRTyField n a (depth - 1) with
      | .inl (some r) => return .inl (some (.primCovariant (.array r)))
      | .inl none => return .inr "an array of an erased type"
      | .inr r => return .inr r
  match ← toTy t (depth - 1) with
  | .ok a => return .inl (some (Ty.toRTy a))
  | .erased => return .inl none
  | .no r => return .inr r

/-! ## Rendering a `Ty` as syntax -/

/-- The name of the constructor of `LeanPrimTy` a terminal type is, for the types the
    compiler writes out. -/
def primTyIdent : LeanPrimTy → Option Name
  | .nat => some ``LeanPrimTy.nat
  | .int => some ``LeanPrimTy.int
  | .bool => some ``LeanPrimTy.bool
  | .char => some ``LeanPrimTy.char
  | .string => some ``LeanPrimTy.string
  | .uint8 => some ``LeanPrimTy.uint8
  | .uint16 => some ``LeanPrimTy.uint16
  | .uint32 => some ``LeanPrimTy.uint32
  | .uint64 => some ``LeanPrimTy.uint64
  | .int8 => some ``LeanPrimTy.int8
  | .int16 => some ``LeanPrimTy.int16
  | .int32 => some ``LeanPrimTy.int32
  | .int64 => some ``LeanPrimTy.int64
  | .float => some ``LeanPrimTy.float
  | .float32 => some ``LeanPrimTy.float32
  | .stringPosRaw => some ``LeanPrimTy.stringPosRaw
  | .substringRaw => some ``LeanPrimTy.substringRaw
  | .stringSlice => some ``LeanPrimTy.stringSlice
  | _ => none

/-- An `Int`, as the syntax that builds it. -/
def intSyntax : Int → MetaM (TSyntax `term)
  | .ofNat n => `((Int.ofNat $(quote n)))
  | .negSucc n => `((Int.negSucc $(quote n)))

mutual

/-- A payload type of a recursive declaration, as the syntax that builds it.  This is
    `tySyntax` one layer down: the same shapes, in `RTy`, and in addition `RTy.self`, an
    occurrence of the declaration the payload belongs to. -/
partial def rtySyntax : RTy → MetaM (TSyntax `term)
  | .self => do `(RTy.self)
  | .familyMember i => do `(RTy.familyMember $(quote i))
  | .prim p => do
      let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
      `(RTy.prim $(mkIdent n))
  | .fn a b => do `(RTy.fn $(← rtySyntax a) $(← rtySyntax b))
  | .primCovariant (.array a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.array $(← rtySyntax a)))
  | .primCovariant (.thunk a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.thunk $(← rtySyntax a)))
  | .primCovariant (.lazy a) => do
      `(RTy.primCovariant (LeanPrimTyCovariant.lazy $(← rtySyntax a)))
  | .enum s => do
      `(RTy.enum (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift)))
  | .record fs => do `(RTy.record $(← rtyRecordSchemaSyntax fs))
  | .taggedUnion l => do `(RTy.taggedUnion $(← rtyTuSchemaSyntax l))
  | _ => throwError "no syntax for a payload that is itself a recursive declaration"

/-- A list of payload types, as syntax. -/
partial def rtyListSyntax (τs : List RTy) : MetaM (TSyntax `term) := do
  let elems ← τs.toArray.mapM rtySyntax
  `([$(elems),*])

/-- The fields of each constructor of a union of payload types, as syntax. -/
partial def rtyListListSyntax (τss : List (List RTy)) : MetaM (TSyntax `term) := do
  let elems ← τss.toArray.mapM rtyListSyntax
  `([$(elems),*])

/-- The schema of a record of payload types, as syntax. -/
partial def rtyRecordSchemaSyntax (fs : LeanRecordSchema RTy) : MetaM (TSyntax `term) := do
  `(LeanRecordSchema.mk $(← rtySyntax fs.fst) $(← rtySyntax fs.snd)
      $(← rtyListSyntax fs.rest))

/-- A non-empty list of payload types, as syntax. -/
partial def rtyNeListSyntax (fs : NonEmpty.ListCorrectByConstruction.NonEmptyList RTy) :
    MetaM (TSyntax `term) := do
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
      $(← rtySyntax fs.head) $(← rtyListSyntax fs.tail))

/-- The constructors of a union of payload types from the first one that carries a
    field, as syntax. -/
partial def rtyCtorsWithPayloadSyntax : CtorsWithPayload RTy → MetaM (TSyntax `term)
  | .here fs rest => do
      `(CtorsWithPayload.here $(← rtyNeListSyntax fs) $(← rtyListListSyntax rest))
  | .skip r => do `(CtorsWithPayload.skip $(← rtyCtorsWithPayloadSyntax r))

/-- The schema of a tagged union of payload types, as syntax. -/
partial def rtyTuSchemaSyntax : LeanTaggedUnionSchema RTy → MetaM (TSyntax `term)
  | .payloadFirst fs next rest => do
      `(LeanTaggedUnionSchema.payloadFirst $(← rtyNeListSyntax fs) $(← rtyListSyntax next)
          $(← rtyListListSyntax rest))
  | .skip r => do `(LeanTaggedUnionSchema.skip $(← rtyCtorsWithPayloadSyntax r))

end

mutual

/-- A `Ty`, as the syntax that builds it — and, with it, the syntax of each of the
    schemas a datatype of the language is described by. -/
partial def tySyntax : Ty → MetaM (TSyntax `term)
  | .prim p => do
      let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
      `(Ty.prim $(mkIdent n))
  | .fn a b => do `(Ty.fn $(← tySyntax a) $(← tySyntax b))
  | .primCovariant (.array a) => do `(Ty.array $(← tySyntax a))
  | .primCovariant (.thunk a) => do `(Ty.thunk $(← tySyntax a))
  | .primCovariant (.lazy a) => do `(Ty.lazy $(← tySyntax a))
  | .enum s => do
      `(Ty.enum (LeanEnumSchema.mk $(quote s.extraConstructors) $(← intSyntax s.shift)))
  | .record fs => do `(Ty.record $(← recordSchemaSyntax fs))
  | .taggedUnion l => do `(Ty.taggedUnion $(← tuSchemaSyntax l))
  | .recTaggedUnion l => do `(Ty.recTaggedUnion ⟨$(← rtyTuSchemaSyntax l.schema), by decide⟩)
  | .withComputedFields b cs => do
      `(Ty.withComputedFields $(← tySyntax b) $(← primTyNeListSyntax cs))
  | τ => throwError "no syntax for the type `{tyStr τ}`"

/-- The types of the values a declaration caches, as syntax. -/
partial def primTyNeListSyntax
    (cs : NonEmpty.ListCorrectByConstruction.NonEmptyList LeanPrimTy) :
    MetaM (TSyntax `term) := do
  let one (p : LeanPrimTy) : MetaM (TSyntax `term) := do
    let some n := primTyIdent p | throwError "no syntax for the terminal type `{p.pretty}`"
    `($(mkIdent n))
  let tail ← cs.tail.toArray.mapM one
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk $(← one cs.head) [$(tail),*])

/-- A list of `Ty`s, as syntax. -/
partial def tyListSyntax (τs : List Ty) : MetaM (TSyntax `term) := do
  let elems ← τs.toArray.mapM tySyntax
  `([$(elems),*])

/-- A list of lists of `Ty`s — the fields of each constructor of a union — as syntax. -/
partial def tyListListSyntax (τss : List (List Ty)) : MetaM (TSyntax `term) := do
  let elems ← τss.toArray.mapM tyListSyntax
  `([$(elems),*])

/-- The schema of a record, as syntax. -/
partial def recordSchemaSyntax (fs : LeanRecordSchema Ty) : MetaM (TSyntax `term) := do
  `(LeanRecordSchema.mk $(← tySyntax fs.fst) $(← tySyntax fs.snd) $(← tyListSyntax fs.rest))

/-- A non-empty list of `Ty`s — the fields of a constructor that has one — as syntax. -/
partial def neListSyntax (fs : NonEmpty.ListCorrectByConstruction.NonEmptyList Ty) :
    MetaM (TSyntax `term) := do
  `(NonEmpty.ListCorrectByConstruction.NonEmptyList.mk
      $(← tySyntax fs.head) $(← tyListSyntax fs.tail))

/-- The constructors of a union from the first one that carries a field, as syntax. -/
partial def ctorsWithPayloadSyntax : CtorsWithPayload Ty → MetaM (TSyntax `term)
  | .here fs rest => do
      `(CtorsWithPayload.here $(← neListSyntax fs) $(← tyListListSyntax rest))
  | .skip r => do `(CtorsWithPayload.skip $(← ctorsWithPayloadSyntax r))

/-- The schema of a tagged union, as syntax. -/
partial def tuSchemaSyntax : LeanTaggedUnionSchema Ty → MetaM (TSyntax `term)
  | .payloadFirst fs next rest => do
      `(LeanTaggedUnionSchema.payloadFirst $(← neListSyntax fs) $(← tyListSyntax next)
          $(← tyListListSyntax rest))
  | .skip r => do `(LeanTaggedUnionSchema.skip $(← ctorsWithPayloadSyntax r))

end

/-- A value of a terminal type to answer with where the translation needs one it will
    never read: the `nodescend` field of a recursion. -/
def primDefault : LeanPrimTy → Option (TSyntax `term) → Option (TSyntax `term) := fun _ x => x

/-- Is this a type the translation erases — a proposition, a type, an instance or a
    one-value type? -/
def erasedBinder (t : Expr) : MetaM Bool := do
  if ← isProp t then return true
  if (← whnf t).isSort then return true
  if ← isErasedType t then return true
  if (← isClass? t).isSome then return true
  return false

/-- The `Ty` of a Lean type, or an error naming why it has none. -/
def tyOf (t : Expr) : MetaM Ty := do
  match ← toTy t with
  | .ok τ => return τ
  | .erased => throwError "the type `{t}` carries no value"
  | .no r => throwError "the type `{t}` has no `Ty`: {r}"

/-- `Ty.den τ`, as a Lean type. -/
def denTypeOf (τ : Ty) : TermElabM Expr := do
  let τS ← tySyntax τ
  let τE ← Lean.Elab.Term.elabTerm τS (some (Lean.mkConst ``LeanScript.Ty))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  mkAppM ``LeanScript.Ty.den #[← instantiateMVars τE]
