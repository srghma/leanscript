module

public meta import LeanScript.ToTerm.TransBrec
public meta import LeanScript.ToTerm.TransRecObject
public meta import LeanScript.ToTerm.TransRecUnion
public meta import LeanScript.ToTerm.TransRecFamily
public meta import LeanScript.ToTerm.TransRecCases
public meta import LeanScript.ToTerm.Extern
public meta import LeanScript.ToTerm.Cache
public meta import LeanScript.ToTerm.Existential
public meta import LeanScript.ToTerm.ForIn
public meta import LeanScript.ToTerm.While

@[expose] public section

meta section

/-!
# The translation: introduction forms

The clause of the translation for an application of a constructor, and for a list or an
array written out.  Like the clauses of `LeanScript.ToTerm.TransRec`, they are written
outside the `mutual` block of `LeanScript.ToTerm.Trans`, and are passed the translation
`trans` (and its checking mode `transCheck`) as arguments.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm
/-- A list, or an array, written out: every element of it at once. -/
def transListLit (trans : TransFn) (c : TCtx) (e : Expr) : MetaM Expr := do
  let ty ← tyOfTerm e
  let .array σ ← tyView ty
    | throwError "`#leanscript_to_term`: {e} is not an array"
  let mut elems : Array Expr := #[]
  let mut cur := e
  repeat
    match cur.getAppFnArgs with
    | (``List.nil, _) => break
    | (``List.cons, #[_, a, as]) => elems := elems.push a; cur := as
    | (``List.toArray, #[_, l]) => cur := l
    | (``Array.mk, #[_, l]) => cur := l
    | _ =>
        throwError "`#leanscript_to_term`: the grammar builds an array from all of its \
          elements at once, so only a list written out can be translated; {cur} is not \
          one"
  let mut ts := mkAppN (mkConst `LeanScript.Terms.nil) #[c.sg, c.gamma, σ]
  for i in [0:elems.size] do
    let a := elems[elems.size - 1 - i]!
    ts := mkAppN (mkConst `LeanScript.Terms.cons) #[c.sg, c.gamma, σ, ← trans c a, ts]
  return mkAppN (mkConst `LeanScript.Term.array_mk) #[c.sg, c.gamma, σ, ts]

/-- A spine of arguments at the given trees. -/
def mkSpine (trans : TransFn) (c : TCtx) (tys : List Expr) (vals : Array Expr) : MetaM Expr := do
  unless tys.length == vals.size do
    throwError "`#leanscript_to_term`: this constructor carries {vals.size} values but \
      its tree has {tys.length} fields"
  let mut sp := mkAppN (mkConst `LeanScript.Spine.nil) #[c.sg, c.gamma]
  let tysA := tys.toArray
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    let t ← trans c vals[j]!
    sp := mkAppN (mkConst `LeanScript.Spine.cons)
      #[c.sg, c.gamma, tysA[j]!, mkTyListE (tys.drop (j + 1)), t, sp]
  return sp

/-- An application of a constructor: it is built in place. -/
def transCtorApp (trans : TransFn)
    (transCheck : TCtx → Expr → Expr → MetaM Expr) (c : TCtx) (e : Expr) (ci : ConstructorVal)
    (args : Array Expr) : MetaM Expr := do
  if args.size < ci.numParams + ci.numFields then
    return ← trans c (← etaExpand e)
  if ci.induct == ``Array then
    return ← transListLit trans c e
  -- a value of a datatype with existentials: its constructor function
  if ← usesCtorFn e ci then
    return ← ctorFnApp trans transCheck c ci args none
  let ty ← tyOfTerm e
  let fields ← ctorValueArgs ci args
  -- a delay
  if let .thunk σ ← tyView ty then
    let some body := fields[0]?
      | throwError "`#leanscript_to_term`: a thunk needs its body"
    let inner := (mkApp body (mkConst ``Unit.unit)).headBeta
    return mkAppN (mkConst `LeanScript.Term.thunk_mk)
      #[c.sg, c.gamma, σ, ← trans c inner]
  -- a one-field wrapper is its field (a type with one constructor: a constructor of a
  -- union whose one field is the union itself, `succ n`, is not a wrapper)
  if h : fields.size = 1 then
    let indInfo ← getConstInfoInduct ci.induct
    let fty ← tyOfTerm fields[0]
    if indInfo.ctors.length == 1 && fty == ty then return ← trans c fields[0]
  match ← tyView ty with
  | .record fs =>
      let fieldTys ← recordFieldTys fs
      let spine ← mkSpine trans c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.record_mk) #[c.sg, c.gamma, fs, spine]
  | .taggedUnion l =>
      let ctys ← taggedUnionCtorTys l
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine trans c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.taggedUnion_mk)
        #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
  | .recTaggedUnion l hwf =>
      -- the fields of a value are the payload **unfolded**: a field that is an
      -- occurrence of the union is a value of the union again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recTaggedUnionUnfold) l hwf
      let ctys ← taggedUnionCtorTys (← reduceTy unfE)
      let some fieldTys := ctys[ci.cidx]?
        | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
            {ci.cidx}"
      let spine ← mkSpine trans c fieldTys fields
      let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE unfE
      let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
      return mkAppN (mkConst `LeanScript.Term.recTaggedUnion_mk)
        #[c.sg, c.gamma, l, hwf, mkNatLit ci.cidx, prf, spine]
  | .recObject fs hwf =>
      -- the fields of a value are the record's fields **unfolded**: an occurrence of the
      -- record inside a field is a value of the record again
      let unfE := mkApp2 (mkConst ``LeanScript.TyWf.recObjectUnfold) fs hwf
      let fieldTys ← recordFieldTys (← reduceTy unfE)
      let spine ← mkSpine trans c fieldTys fields
      return mkAppN (mkConst `LeanScript.Term.recObject_mk) #[c.sg, c.gamma, fs, hwf, spine]
  | .recAlias b hwf =>
      let indInfo ← getConstInfoInduct ci.induct
      if indInfo.ctors.length > 1 then
        -- a declaration of several constructors with an occurrence of itself inside
        -- another type: its body is the union of its constructors, **unfolded**
        let unfE ← reduceTy (mkApp2 (mkConst ``LeanScript.TyWf.recAliasUnfold) b hwf)
        let .taggedUnion l ← tyView unfE
          | throwError "`#leanscript_to_term`: internal: the body of {ci.induct} is not a \
              tagged union"
        let ctys ← taggedUnionCtorTys l
        let some fieldTys := ctys[ci.cidx]?
          | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no constructor \
              {ci.cidx}"
        let spine ← mkSpine trans c fieldTys fields
        let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
        let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
        let body := mkAppN (mkConst `LeanScript.Term.taggedUnion_mk)
          #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
        return mkAppN (mkConst `LeanScript.Term.recAlias_mk) #[c.sg, c.gamma, b, hwf, body]
      -- the one field of a value is the body **unfolded**: an occurrence of the newtype
      -- inside it is a value of the newtype again
      let some v := fields[0]?
        | throwError "`#leanscript_to_term`: a value of the recursive newtype \
            {ci.induct} needs its body"
      unless fields.size == 1 do
        throwError "`#leanscript_to_term`: the constructor of the recursive newtype \
          {ci.induct} has {fields.size} fields"
      return mkAppN (mkConst `LeanScript.Term.recAlias_mk)
        #[c.sg, c.gamma, b, hwf, ← trans c v]
  | .mutualRecursiveFamily nE f hwf =>
      -- a value of the member the family selects, with its fields **unfolded** in the
      -- scope of the whole family: an occurrence of a member is a value of that member
      let curE := mkApp2 (mkConst ``LeanScript.LeanMutualRecFamily.current)
        (tyWfInE ((← natOfExpr nE) + 2)) f
      let unfE ← reduceTy (mkAppN (mkConst ``LeanScript.LeanFamMemberSchema.map)
        #[tyWfInE ((← natOfExpr nE) + 2), tyE,
          mkApp3 (mkConst ``LeanScript.TyWfIn.unfoldFam) nE f hwf, curE])
      let value ← match unfE.getAppFnArgs with
        | (``LeanScript.LeanFamMemberSchema.ctors, #[_, l]) =>
            let ctys ← taggedUnionCtorTys l
            let some fieldTys := ctys[ci.cidx]?
              | throwError "`#leanscript_to_term`: the tree of {ci.induct} has no \
                  constructor {ci.cidx}"
            let spine ← mkSpine trans c fieldTys fields
            let lenE := mkApp2 (mkConst ``LeanScript.LeanTaggedUnionSchema.length) tyE l
            let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit ci.cidx, lenE])
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.ctors)
              #[c.sg, c.gamma, l, mkNatLit ci.cidx, prf, spine]
        | (``LeanScript.LeanFamMemberSchema.record, #[_, fs]) =>
            let spine ← mkSpine trans c (← recordFieldTys fs) fields
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.record)
              #[c.sg, c.gamma, fs, spine]
        | (``LeanScript.LeanFamMemberSchema.alias, #[_, b]) =>
            let some v := fields[0]?
              | throwError "`#leanscript_to_term`: a value of {ci.induct} needs its body"
            pure <| mkAppN (mkConst `LeanScript.FamilyMemberValue.alias)
              #[c.sg, c.gamma, b, ← trans c v]
        | _ => throwError "`#leanscript_to_term`: internal: the member of the family \
            {ci.induct} has no shape: {unfE}"
      return mkAppN (mkConst `LeanScript.Term.mutualRecursiveFamily_mk)
        #[c.sg, c.gamma, nE, f, hwf, value]
  | .enum s =>
      let nE := mkApp (mkConst ``LeanScript.LeanEnumSchema.nOfConstructors) s
      return mkAppN (mkConst `LeanScript.Term.enum_mk)
        #[c.sg, c.gamma, s, ← mkFinLit nE ci.cidx]
  | .prim _ =>
      if ← isBoolTy ty then
        return mkAppN (mkConst `LeanScript.Term.bool_mk)
          #[c.sg, c.gamma, toExpr (ci.cidx == 1)]
      throwError "`#leanscript_to_term`: {ci.name} builds a value of a terminal type, \
        which has no constructor in the language; write it as a literal"
  | _ =>
      throwError "`#leanscript_to_term`: the tree of {ci.induct} has no introduction \
        form in the grammar"


end LeanScript.ToTerm

end

end
