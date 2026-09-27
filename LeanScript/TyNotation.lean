module

public import LeanScript.Ty
public meta import Lean.PrettyPrinter.Delaborator.Builtins

@[expose] public section

set_option autoImplicit false

/-!
# `[Ty| …]`: a notation for closed types, and its pretty-printer

`[Ty| τ]` elaborates the surface syntax `τ` to a `LeanScript.Ty ks` (the signature `ks` is
left to unification), and every `Ty` built from its constructors is printed back in the same
notation (`set_option pp.leanscript false` turns that off).

| surface syntax                 | `Ty`                                               |
|--------------------------------|----------------------------------------------------|
| `Bool`, `Nat`, `Int`, `String`, `Char`, `UInt8` … `UInt64`, `Int8` … `Int64`, `Float`, `Float32`, `Float.Model`, `Float32.Model`, `String.Pos.Raw`, `Substring.Raw`, `String.Slice` | `.prim p` |
| `BitVec 32`, `String.Pos "ab"` | `.prim (.bitvec 32)`, `.prim (.stringPos "ab")`    |
| `σ → τ`                        | `.fn σ τ` (right associative)                      |
| `Array τ`                      | `.array τ`                                         |
| `Option τ`                     | `Ty.option τ` (`⟪· \| τ⟫`)                         |
| `σ ⊕ τ`                        | `Ty.sum σ τ` (`⟪σ \| τ⟫`, right associative)       |
| `τ₁ × τ₂ × … × τₙ`             | `.record τ₁ (.cons τ₂ … (.one τₙ))`                |
| `⟪c₁ \| c₂ \| … \| cₙ⟫`          | `.union …`: `cᵢ` is `·` (no fields) or `τ, …, τ`   |
| `Enum n`, `Enum n k`           | `.enum` of `n ≥ 3` constructors, numbered from `k` |
| `Data b j`                     | `.data r`: member `j` of block `b` (`0` newest)    |
| `‹t›`, or an identifier        | the Lean term `t : Ty ks`                          |

A chain `τ₁ × τ₂ × τ₃` is **one** record of three fields; parentheses make a field that is
itself a record: `τ₁ × (τ₂ × τ₃)` is a record of two fields.
-/

namespace LeanScript

/-- The surface syntax of a closed type (`[Ty| …]`). -/
declare_syntax_cat lsty
/-- A constructor of a union type: `·` (no fields) or its fields. -/
declare_syntax_cat lsctor

/-- A leaf, or a Lean term of type `Ty ks`. -/
syntax:max ident : lsty
/-- A number (an argument of `BitVec`, `Enum` or `Data`). -/
syntax:max (name := lstyNum) num : lsty
/-- A string (the argument of `String.Pos`). -/
syntax:max str : lsty
/-- A negative number (the numbering of an `Enum`). -/
syntax:max "-" num : lsty
/-- A Lean term. -/
syntax (name := lstyAntiquot) "‹" term "›" : lsty
syntax "(" lsty ")" : lsty
/-- A type former applied: `Array τ`, `Option τ`, `BitVec n`, `String.Pos s`, `Enum n`,
    `Data b j`. -/
syntax:40 ident (ppSpace lsty:max)+ : lsty
/-- A record. -/
syntax:35 lsty:36 " × " lsty:35 : lsty
/-- A binary union of two one-field constructors. -/
syntax:30 lsty:31 " ⊕ " lsty:30 : lsty
/-- A function type. -/
syntax:25 lsty:26 " → " lsty:25 : lsty
syntax "·" : lsctor
syntax (name := lsctorFields) lsty,+ : lsctor
/-- A union: two or more constructors. -/
syntax "⟪" sepBy1(lsctor, " | ") "⟫" : lsty

/-- `[Ty| τ]`: the closed type written in the surface syntax `τ` (see the module doc). -/
syntax:max "[Ty| " lsty "]" : term

end LeanScript

meta section

/-- Print `LeanScript.Ty`s (and `LeanScript.Term`s) in the `[Ty| …]` (`[Term| …]`) notation. -/
register_option pp.leanscript : Bool := {
  defValue := true
  descr := "print LeanScript types and terms in the `[Ty| …]` and `[Term| …]` notations"
}

namespace LeanScript.Notation

open Lean

/-! ## Elaboration -/

/-- The leaves written as a plain name. -/
def primNames : List (Name × Name) :=
  [(`Bool, ``LeanPrimTy.bool), (`Nat, ``LeanPrimTy.nat), (`Int, ``LeanPrimTy.int),
   (`UInt8, ``LeanPrimTy.uint8), (`UInt16, ``LeanPrimTy.uint16),
   (`UInt32, ``LeanPrimTy.uint32), (`UInt64, ``LeanPrimTy.uint64),
   (`Int8, ``LeanPrimTy.int8), (`Int16, ``LeanPrimTy.int16),
   (`Int32, ``LeanPrimTy.int32), (`Int64, ``LeanPrimTy.int64),
   (`Char, ``LeanPrimTy.char), (`String, ``LeanPrimTy.string),
   (`String.Pos.Raw, ``LeanPrimTy.stringPosRaw), (`Substring.Raw, ``LeanPrimTy.substringRaw),
   (`String.Slice, ``LeanPrimTy.stringSlice), (`Float, ``LeanPrimTy.float),
   (`Float32, ``LeanPrimTy.float32), (`Float.Model, ``LeanPrimTy.floatModel),
   (`Float32.Model, ``LeanPrimTy.float32Model)]

/-- A Lean term given as an argument of a type former: a number, a string or `‹t›`. -/
partial def lstyArg : TSyntax `lsty → MacroM Term
  | `(lsty| $n:num) => pure n
  | `(lsty| $s:str) => pure s
  | `(lsty| -$n:num) => `(-$n)
  | `(lsty| ‹$t›) => pure t
  | `(lsty| ($t)) => lstyArg t
  | t => Macro.throwErrorAt t "expected a number, a string or `‹term›`"

/-- The name `Ref` of member `j` of block `b` (`0` is the newest block). -/
def mkRef (b : Nat) (j : Term) : MacroM Term := do
  let mut r ← `(LeanScript.Ref.here $j)
  for _ in [0:b] do
    r ← `(LeanScript.Ref.there $r)
  return r

/-- The fields of a nonempty list of terms of `Ty`: `.one` at the end, `.cons` before. -/
def mkFields : List Term → MacroM Term
  | [] => Macro.throwError "a record needs at least one field"
  | [t] => `(LeanScript.Fields.one $t)
  | t :: ts => do `(LeanScript.Fields.cons $t $(← mkFields ts))

/-- Two or more constructors: `.two` of the last two, `.cons` before. -/
def mkCtors : List Term → MacroM Term
  | [c, d] => `(LeanScript.Ctors.two $c $d)
  | c :: cs@(_ :: _ :: _) => do `(LeanScript.Ctors.cons $c $(← mkCtors cs))
  | _ => Macro.throwError "a union needs at least two constructors"

/-- The fields after the first of a chain `τ₁ × τ₂ × … × τₙ` (a parenthesized record ends
    the chain: it is one field). -/
partial def recordFields : TSyntax `lsty → List (TSyntax `lsty)
  | `(lsty| $a × $b) => a :: recordFields b
  | t => [t]

/-- `Enum n k`: `n ≥ 3` constructors numbered from `k`. -/
def enumOf (n : TSyntax `lsty) (k : Term) : MacroM Term := do
  match n with
  | `(lsty| $n:num) =>
      if n.getNat < 3 then
        Macro.throwErrorAt n "an enum has at least three constructors \
          (two field-less constructors are `Bool`)"
      `(LeanScript.Ty.enum (LeanScript.LeanEnumSchema.mk $(quote (n.getNat - 3)) $k))
  | n => do `(LeanScript.Ty.enum (LeanScript.LeanEnumSchema.mk ($(← lstyArg n) - 3) $k))

mutual

/-- The `Ty` a surface type denotes. -/
partial def elabLsty : TSyntax `lsty → MacroM Term
  | `(lsty| ‹$t›) => pure t
  | `(lsty| ($t)) => elabLsty t
  | `(lsty| $a → $b) => do `(LeanScript.Ty.fn $(← elabLsty a) $(← elabLsty b))
  | `(lsty| $a ⊕ $b) => do `(LeanScript.Ty.sum $(← elabLsty a) $(← elabLsty b))
  | `(lsty| $a × $b) => do
      let fs ← (recordFields b).mapM elabLsty
      `(LeanScript.Ty.record $(← elabLsty a) $(← mkFields fs))
  | `(lsty| ⟪$cs|*⟫) => do
      let cs ← cs.getElems.toList.mapM elabCtor
      `(LeanScript.Ty.union $(← mkCtors cs))
  | `(lsty| $id:ident) => do
      match primNames.lookup id.getId.eraseMacroScopes with
      | some p =>
        match p with
        | ``LeanPrimTy.bool => `(LeanScript.Ty.bool)
        | ``LeanPrimTy.nat => `(LeanScript.Ty.nat)
        | ``LeanPrimTy.int => `(LeanScript.Ty.int)
        | ``LeanPrimTy.string => `(LeanScript.Ty.string)
        | _ => `(LeanScript.Ty.prim $(mkIdentFrom id p) rfl)
      | none => pure id
  | `(lsty| $id:ident $args*) => do
      let f := id.getId.eraseMacroScopes
      match f, args.toList with
      | `Array, [t] => do `(LeanScript.Ty.array $(← elabLsty t))
      | `Option, [t] => do `(LeanScript.Ty.option $(← elabLsty t))
      | `BitVec, [n] => do `(LeanScript.Ty.prim (LeanScript.LeanPrimTy.bitvec $(← lstyArg n)) rfl)
      | `String.Pos, [s] => do
          `(LeanScript.Ty.prim (LeanScript.LeanPrimTy.stringPos $(← lstyArg s)) rfl)
      | `Enum, [n] =>
          if n.raw.isOfKind ``lstyAntiquot then do `(LeanScript.Ty.enum $(← lstyArg n))
          else enumOf n (← `(0))
      | `Enum, [n, k] => do enumOf n (← lstyArg k)
      | `Data, [r] => do `(LeanScript.Ty.data $(← lstyArg r))
      | `Data, [b, j] => do
          let `(lsty| $b:num) := b | Macro.throwErrorAt b "expected a block number"
          `(LeanScript.Ty.data $(← mkRef b.getNat (← lstyArg j)))
      | _, _ => Macro.throwErrorAt id s!"unknown type former `{f}` with {args.size} \
          argument(s): expected `Array τ`, `Option τ`, `BitVec n`, `String.Pos s`, `Enum n`, \
          `Enum n k` or `Data b j`"
  | `(lsty| $n:num) => Macro.throwErrorAt n "a number is not a type"
  | `(lsty| $s:str) => Macro.throwErrorAt s "a string is not a type"
  | t => Macro.throwErrorAt t "unsupported type syntax"

/-- A constructor of a union. -/
partial def elabCtor : TSyntax `lsctor → MacroM Term
  | `(lsctor| ·) => `(LeanScript.Ctor.nullary)
  | c => do
      unless c.raw.isOfKind ``lsctorFields do Macro.throwErrorAt c "unsupported constructor syntax"
      let ts : Array (TSyntax `lsty) := c.raw[0].getSepArgs.map (⟨·⟩)
      `(LeanScript.Ctor.fields $(← mkFields (← ts.toList.mapM elabLsty)))

end

macro_rules
  | `([Ty| $t]) => elabLsty t

/-! ## Pretty-printing -/

open PrettyPrinter Delaborator SubExpr

/-- Is the `[Ty| …]`/`[Term| …]` notation used for printing? -/
def ppNotation : DelabM Bool := do
  return (← getOptions).getBool `pp.leanscript true && !(← getPPOption getPPExplicit)

/-- A natural number literal. -/
def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg!.consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- An integer literal: `n` or `-n`. -/
def intLit? (e : Expr) : Option Int :=
  match natLit? e with
  | some n => some n
  | none =>
    if e.isAppOfArity ``Neg.neg 3 then (natLit? e.appArg!).map (- ·) else none

/-- A surface type with its precedence. -/
abbrev PSyn := TSyntax `lsty × Nat

/-- The precedence of an atom. -/
def atomPrec : Nat := 1024

/-- Parenthesize `s` when its precedence is below `req`. -/
def paren (req : Nat) : PSyn → DelabM (TSyntax `lsty)
  | (s, p) => if p < req then `(lsty| ($s)) else pure s

/-- A number, as a surface argument. -/
def numArg (n : Nat) : TSyntax `lsty := ⟨Syntax.node .none ``LeanScript.lstyNum #[Syntax.mkNumLit (toString n)]⟩

/-- A Lean term embedded in a surface type. -/
def embedTy : DelabM PSyn := do
  let s ← delab
  -- an identifier is printed as it is, unless it would be read as a leaf
  if let `($id:ident) := s then
    unless (primNames.lookup id.getId).isSome do
      return (← `(lsty| $id:ident), atomPrec)
  return (← `(lsty| ‹$s›), atomPrec)

/-- Member `j` of block `b`, if `e` is such a literal name. -/
partial def refLit? (e : Expr) : Option (Nat × Nat) :=
  if e.isAppOfArity ``Ref.here 3 then (natLit? e.appArg!).map (0, ·)
  else if e.isAppOfArity ``Ref.there 3 then (refLit? e.appArg!).map fun (b, j) => (b + 1, j)
  else none

/-- A leaf. -/
def delabPrim : DelabM PSyn := do
  let p := (← getExpr).consumeMData
  if let some c := p.constName? then
    if let some (n, _) := primNames.find? (·.2 == c) then
      return (← `(lsty| $(mkIdent n):ident), atomPrec)
  if p.isAppOfArity ``LeanPrimTy.bitvec 2 then
    let n ← match natLit? (p.getArg! 0) with
      | some n => pure (numArg n)
      | none => withNaryArg 0 do `(lsty| ‹$(← delab)›)
    return (← `(lsty| $(mkIdent `BitVec):ident $n), 40)
  if p.isAppOfArity ``LeanPrimTy.stringPos 1 then
    let s ← match p.appArg!.consumeMData with
      | .lit (.strVal s) => `(lsty| $(Syntax.mkStrLit s):str)
      | _ => withNaryArg 0 do `(lsty| ‹$(← delab)›)
    return (← `(lsty| $(mkIdent `String.Pos):ident $s), 40)
  failure

mutual

/-- The current expression, a `Ty`, as a surface type; `root` is whether it is the whole
    printed type (then an expression that is not in the notation fails, instead of being
    embedded as `‹…›`). -/
partial def delabLsty (root : Bool) : DelabM PSyn := do
  let e := (← getExpr).consumeMData
  let other : DelabM PSyn := if root then failure else embedTy
  let some c := e.getAppFn.constName? | other
  let n := e.getAppNumArgs
  let r : DelabM PSyn := do
    match c, n with
    | ``Ty.prim, 3 => withNaryArg 1 delabPrim
    | ``Ty.bool, 1 => return (← `(lsty| $(mkIdent `Bool):ident), atomPrec)
    | ``Ty.nat, 1 => return (← `(lsty| $(mkIdent `Nat):ident), atomPrec)
    | ``Ty.int, 1 => return (← `(lsty| $(mkIdent `Int):ident), atomPrec)
    | ``Ty.string, 1 => return (← `(lsty| $(mkIdent `String):ident), atomPrec)
    | ``Ty.fn, 3 => do
        let a ← paren 26 (← withNaryArg 1 (delabLsty false))
        let b ← paren 25 (← withNaryArg 2 (delabLsty false))
        return (← `(lsty| $a → $b), 25)
    | ``Ty.array, 2 => do
        let t ← paren atomPrec (← withNaryArg 1 (delabLsty false))
        return (← `(lsty| $(mkIdent `Array):ident $t), 40)
    | ``Ty.option, 2 => do
        let t ← paren atomPrec (← withNaryArg 1 (delabLsty false))
        return (← `(lsty| $(mkIdent `Option):ident $t), 40)
    | ``Ty.sum, 3 => mkSum (← withNaryArg 1 (delabLsty false)) (← withNaryArg 2 (delabLsty false))
    | ``Ty.pair, 3 => mkRecord [← withNaryArg 1 (delabLsty false), ← withNaryArg 2 (delabLsty false)]
    | ``Ty.record, 3 => do
        let t ← withNaryArg 1 (delabLsty false)
        mkRecord (t :: (← withNaryArg 2 delabFields))
    | ``Ty.union, 4 => do
        match ← withNaryArg 2 delabCtors with
        | [none, some [t]] => return (← `(lsty| $(mkIdent `Option):ident $(← paren atomPrec t)), 40)
        | [some [a], some [b]] => mkSum a b
        | cs => do
            let cs ← cs.toArray.mapM fun
              | none => `(lsctor| ·)
              | some fs => do
                  let fs ← fs.toArray.mapM fun f => pure f.1
                  pure ⟨Syntax.node .none ``LeanScript.lsctorFields
                    #[Syntax.mkSep (fs.map (·.raw)) (mkAtom ",")]⟩
            return (← `(lsty| ⟪$cs|*⟫), atomPrec)
    | ``Ty.enum, 2 => do
        let s := e.appArg!.consumeMData
        if s.isAppOfArity ``LeanEnumSchema.mk 2 then
          if let (some x, some k) := (natLit? (s.getArg! 0), intLit? (s.getArg! 1)) then
            let n := numArg (x + 3)
            if k == 0 then return (← `(lsty| $(mkIdent `Enum):ident $n), 40)
            let k : TSyntax `lsty ← if k < 0
              then `(lsty| -$(Syntax.mkNumLit (toString k.natAbs)):num) else pure (numArg k.toNat)
            return (← `(lsty| $(mkIdent `Enum):ident $n $k), 40)
        let s ← withNaryArg 1 delab
        return (← `(lsty| $(mkIdent `Enum):ident ‹$s›), 40)
    | ``Ty.data, 2 => do
        match refLit? e.appArg!.consumeMData with
        | some (b, j) => return (← `(lsty| $(mkIdent `Data):ident $(numArg b) $(numArg j)), 40)
        | none =>
          let r ← withNaryArg 1 delab
          return (← `(lsty| $(mkIdent `Data):ident ‹$r›), 40)
    | _, _ => failure
  r <|> other

/-- The fields of a record. -/
partial def delabFields : DelabM (List PSyn) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Fields.one 2 then
    return [← withNaryArg 1 (delabLsty false)]
  else if e.isAppOfArity ``Fields.cons 3 then
    return (← withNaryArg 1 (delabLsty false)) :: (← withNaryArg 2 delabFields)
  else failure

/-- A constructor of a union: `none` when it has no fields. -/
partial def delabCtor : DelabM (Option (List PSyn)) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Ctor.nullary 1 then return none
  else if e.isAppOfArity ``Ctor.fields 2 then return some (← withNaryArg 1 delabFields)
  else failure

/-- The constructors of a union. -/
partial def delabCtors : DelabM (List (Option (List PSyn))) := do
  let e := (← getExpr).consumeMData
  if e.isAppOfArity ``Ctors.two 5 then
    return [← withNaryArg 3 delabCtor, ← withNaryArg 4 delabCtor]
  else if e.isAppOfArity ``Ctors.cons 5 then
    return (← withNaryArg 3 delabCtor) :: (← withNaryArg 4 delabCtors)
  else failure

/-- `a ⊕ b`. -/
partial def mkSum (a b : PSyn) : DelabM PSyn := do
  return (← `(lsty| $(← paren 31 a) ⊕ $(← paren 30 b)), 30)

/-- `f₁ × … × fₙ` (`n ≥ 2`). -/
partial def mkRecord : List PSyn → DelabM PSyn
  | [a, b] => do return (← `(lsty| $(← paren 36 a) × $(← paren 36 b)), 35)
  | a :: fs@(_ :: _ :: _) => do
      let (r, _) ← mkRecord fs
      return (← `(lsty| $(← paren 36 a) × $r), 35)
  | _ => failure

end

open PrettyPrinter.Parenthesizer in
/-- Parentheses in the surface syntax of types, where the precedences require them. -/
@[category_parenthesizer lsty]
def lsty.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `lsty true (fun stx => Unhygienic.run `(lsty| ($(⟨stx⟩)))) prec <|
    parenthesizeCategoryCore `lsty prec

/-- Print a `Ty` in the `[Ty| …]` notation. -/
def delabTy : Delab := do
  unless ← ppNotation do failure
  let (s, _) ← delabLsty true
  `([Ty| $s])

@[delab app.LeanScript.Ty.prim] def delabTyPrim : Delab := delabTy
@[delab app.LeanScript.Ty.fn] def delabTyFn : Delab := delabTy
@[delab app.LeanScript.Ty.array] def delabTyArray : Delab := delabTy
@[delab app.LeanScript.Ty.enum] def delabTyEnum : Delab := delabTy
@[delab app.LeanScript.Ty.record] def delabTyRecord : Delab := delabTy
@[delab app.LeanScript.Ty.union] def delabTyUnion : Delab := delabTy
@[delab app.LeanScript.Ty.data] def delabTyData : Delab := delabTy
@[delab app.LeanScript.Ty.bool] def delabTyBool : Delab := delabTy
@[delab app.LeanScript.Ty.nat] def delabTyNat : Delab := delabTy
@[delab app.LeanScript.Ty.int] def delabTyInt : Delab := delabTy
@[delab app.LeanScript.Ty.string] def delabTyString : Delab := delabTy
@[delab app.LeanScript.Ty.option] def delabTyOption : Delab := delabTy
@[delab app.LeanScript.Ty.sum] def delabTySum : Delab := delabTy
@[delab app.LeanScript.Ty.pair] def delabTyPair : Delab := delabTy

end LeanScript.Notation

end
