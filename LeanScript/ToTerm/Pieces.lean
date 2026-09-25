module

public meta import LeanScript.ToTerm.Cache

@[expose] public section

meta section

/-!
# Literals, and small pieces of the object language

The introduction form of a Lean literal, and the small constructions — lists of trees,
the fields of a schema, a `Fin` literal, an unfolding step — the translation uses
throughout.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## Literals -/

/-- The introduction form of a literal of this Lean type. -/
def litCtorFor : Name → Option Name
  | ``Bool => some ``LeanScript.Term.bool_mk
  | ``Nat => some ``LeanScript.Term.nat_mk
  | ``Int => some ``LeanScript.Term.int_mk
  | ``String => some ``LeanScript.Term.string_mk
  | ``Char => some ``LeanScript.Term.char_mk
  | ``UInt8 => some ``LeanScript.Term.uint8_mk
  | ``UInt16 => some ``LeanScript.Term.uint16_mk
  | ``UInt32 => some ``LeanScript.Term.uint32_mk
  | ``UInt64 => some ``LeanScript.Term.uint64_mk
  | ``Int8 => some ``LeanScript.Term.int8_mk
  | ``Int16 => some ``LeanScript.Term.int16_mk
  | ``Int32 => some ``LeanScript.Term.int32_mk
  | ``Int64 => some ``LeanScript.Term.int64_mk
  | ``Float => some ``LeanScript.Term.float_mk
  | ``Float32 => some ``LeanScript.Term.float32_mk
  | _ => none

/-- Is this expression a literal — a numeral, a string, a character, a boolean, or a
    sign in front of one?  A literal is carried into the term as it stands; anything
    else is translated. -/
partial def isLitLike (e : Expr) : Bool :=
  match e with
  | .lit _ => true
  | .mdata _ b => isLitLike b
  | .const n _ => n == ``Bool.true || n == ``Bool.false
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => isLitLike n
    | (``OfScientific.ofScientific, _) => true
    | (``Neg.neg, #[_, _, a]) => isLitLike a
    | (``Int.ofNat, #[a]) => isLitLike a
    | (``Int.negSucc, #[a]) => isLitLike a
    | (``Char.ofNat, #[a]) => isLitLike a
    | (``Char.ofNatAux, #[a, _]) => isLitLike a
    | _ => false

/-! ## Small pieces of the object language -/

/-- The pieces of the schema of a list: the `CtorsWithPayload` after the field-less
    `nil`, the fields of `cons` and the constructors after it (there are none).  The
    schema is `listSchemaE`, so this is where the element type is read off. -/
def listSchemaParts (l : Expr) : MetaM (Expr × Expr × Expr) := do
  let cp ← match (← whnf l).getAppFnArgs with
    | (``LeanScript.LeanTaggedUnionSchema.skip, #[_, cp]) => pure (← whnf cp)
    | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"
  match cp.getAppFnArgs with
  | (``LeanScript.CtorsWithPayload.here, #[_, fields, rest]) => return (cp, fields, rest)
  | _ => throwError "`#leanscript_to_term`: not the schema of a list: {l}"

/-- A member of `Fin n`, with the bound proved by computation. -/
def mkFinLit (n : Expr) (i : Nat) : MetaM Expr := do
  let prf ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, n])
  return mkAppN (mkConst ``Fin.mk) #[n, mkNatLit i, prf]

/-- Unfold the head of an application: a matcher, a `casesOn`, or any definition. -/
def unfoldHere? (e : Expr) : MetaM (Option Expr) := do
  if let some e' ← delta? e then return some e'
  withTransparency .all (unfoldDefinition? e)

/-- The arguments of a constructor that carry a value. -/
partial def ctorValueArgs (ci : ConstructorVal) (args : Array Expr) :
    MetaM (Array Expr) := do
  let fieldArgs := args.extract ci.numParams args.size
  forallBoundedTelescope (← instantiateForall ci.type (args.extract 0 ci.numParams))
      (some ci.numFields) fun xs _ => do
    let mut out := #[]
    for h : i in [0:fieldArgs.size] do
      if ← LeanScript.Deriving.erasedBinder (← inferType xs[i]!) then continue
      out := out.push fieldArgs[i]
    return out

/-- The base values of a fold, already translated, as a `Spine` at `k` copies of `τ` —
    the type `LeanScript.Term.nat_rec` asks its base values at. -/
partial def mkNatRecBase (c : TCtx) (τ : Expr) (vals : Array Expr) : MetaM Expr := do
  let mut sp := (← mkNode ``LeanScript.Spine.nil #[c.sg, c.gamma])
  let mut tys : List Expr := []
  for i in [0:vals.size] do
    let j := vals.size - 1 - i
    sp := (← mkNode ``LeanScript.Spine.consT
      #[c.sg, c.gamma, τ, mkTyListE tys, vals[j]!, sp])
    tys := τ :: tys
  return sp

end LeanScript.ToTerm

end

end
