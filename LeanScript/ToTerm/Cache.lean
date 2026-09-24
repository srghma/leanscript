module

public meta import LeanScript.ToTerm.Ctx

@[expose] public section

meta section

/-!
# The cache, and what may be translated at all

The cache of translated definitions, which survives between calls, and the tests that
refuse a constant the language has no total value for.
-/

open Lean Meta Elab Term

namespace LeanScript.ToTerm

/-! ## The cache of translated definitions -/

/-- One definition that has been translated: the value it was translated from, and the
    translation, as a function of the context it is used in. -/
structure CacheEntry where
  /-- The signature it was translated against. -/
  sg : Expr
  /-- The closed Lean value that was translated. -/
  src : Expr
  /-- The translation: `fun (Γ : Ctx) => …`. -/
  fn : Expr
  /-- The hash of the translation, for the shape lookup. -/
  hash : UInt64
  deriving Inhabited, BEq, Repr

/-- What the cache holds, and what it has done. -/
structure CacheState where
  /-- The definitions translated so far. -/
  entries : Array CacheEntry := #[]
  /-- How often a definition was found already translated. -/
  hits : Nat := 0
  /-- How often a *new* definition turned out to have the shape of one already
      translated, and was replaced by it. -/
  shared : Nat := 0
  deriving Inhabited, BEq, Repr

/-- The cache of translated definitions.  It survives between calls of
    `#leanscript_to_term`, so a function called from two definitions is translated
    once. -/
initialize cacheRef : IO.Ref CacheState ← IO.mkRef {}

/-! ## What may be translated at all -/

/-- Is this constant part of a well-founded recursion — the fixpoint operator, its
    companions, or a recursion on an accessibility proof? -/
def isWfRecursion (n : Name) : Bool :=
  n.components.any (fun p => p == `WellFounded || p == `WellFoundedRecursion) ||
    n == ``Acc.rec || n == ``invImage

/-- Is this the fixpoint a `partial_fixpoint` definition is built from? -/
def isPartialFixpoint (n : Name) : Bool :=
  n.getString! == "fix" && n.getPrefix == `Lean.Order

/-- Is this the compiled form of a structural recursion — `X.brecOn`, `X.binductionOn`,
    the `below` motive, or the unsafe companion of a `partial` definition?

    `Nat.brecOn` and `List.brecOn` are **not** among them: those two are the compiled form
    of a recursion over the two types the grammar has a fold for, and
    `LeanScript.ToTerm.transBrecOn` turns them into that fold. -/
def isCompiledRecursion (n : Name) : Bool :=
  if n == ``Nat.brecOn || n == ``List.brecOn then false else
  let s := n.getString!
  s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
    s == "_unsafe_rec"

/-- Refuse a constant the language has no total value for. -/
def checkConst (n : Name) : MetaM Unit := do
  if isPartialFixpoint n then
    throwError "`#leanscript_to_term`: a partial fixpoint ({n}) is not supported: the \
      grammar has no fixpoint that does not descend"
  if isWfRecursion n then
    throwError "`#leanscript_to_term`: well-founded recursion ({n}) is not supported — \
      the only folds the translation produces are `nat_rec` and `recTaggedUnion_rec`, so \
      write the recursion as `Nat.rec` or `List.rec` with a non-dependent motive"
  if isCompiledRecursion n then
    throwError "`#leanscript_to_term`: {n} is the compiled form of a recursion the \
      grammar cannot express — write the recursion as `Nat.rec` or `List.rec` with a \
      non-dependent motive, which are `nat_rec` and `recTaggedUnion_rec`"
  match ← getConstInfo n with
  | .defnInfo d =>
      if d.safety == .partial then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      if d.safety == .unsafe then
        throwError "`#leanscript_to_term`: `{n}` is `unsafe`"
  | .opaqueInfo _ =>
      if ((← getEnv).find? (n ++ `_unsafe_rec)).isSome then
        throwError "`#leanscript_to_term`: `{n}` is `partial`, and a `partial` \
          definition has no value the grammar can express"
      throwError "`#leanscript_to_term`: `{n}` is opaque, so there is nothing to \
        translate"
  | .axiomInfo _ =>
      throwError "`#leanscript_to_term`: `{n}` is an axiom, so there is nothing to \
        translate"
  | _ => pure ()

/-- Is a call of this constant inlined?  A constructor and a projection always are, and
    so is anything the author marked inlinable or reducible. -/
def isInlinable (n : Name) : MetaM Bool := do
  if (← getEnv).find? n matches some (.ctorInfo _) then return true
  if (← getProjectionFnInfo? n).isSome then return true
  if ← Lean.isReducible n then return true
  let env ← getEnv
  return Compiler.hasInlineAttribute env n
    || Compiler.hasMacroInlineAttribute env n
    || Compiler.hasInlineIfReduceAttribute env n

end LeanScript.ToTerm

end

end
