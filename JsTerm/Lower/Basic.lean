module

public import JsTerm.Ty.Lower
public import JsTerm.Ty.Canon
public import JsTerm.Lower.Extern
public import JsTerm.Lower.Tail
public import LeanScript.Term.Syntax.Packed
public import LeanScript.Term.Ownership.Walk

@[expose] public section

set_option autoImplicit false

/-!
# The support of the conversion from `Term`

The pieces of `termToJs` (`JsTerm.Lower.FromTerm`) that are not the recursion over `Term`
itself: the literals (`primLit`), the conversion monad (`ConvM`), where a variable of `Term`
lives in JavaScript (`Ref`, `Names`), the casts between equal types, and the builders of the
JavaScript shapes the conversion emits (bindings, patterns, records, unions, loop bodies).
-/

namespace MoreJs

variable {S : JsSig}

open LeanScript

/-! ## The signature of a function -/

/-- The blocks of a signature, newest first. -/
def _root_.LeanScript.DSig.brefs : {ks : List Nat} → DSig ks → List (BRef ks)
  | [], .nil => []
  | _ :: _, .cons Δ _ _ => .here :: Δ.brefs.map .there

/-- The signature of the JavaScript of a program over the datatypes `Δ`: declaration
    `refIndex r` is the layout of one layer of the datatype `r`, its unfolded body lowered
    (`lowerTy cfg (unfold r)`: an anonymous record or union — or the one field of a datatype
    of one constructor of one field — whose recursive positions are `obj (decl i) []`).  With
    canonical ids (`cfg.declCanon`), the row of a datatype is at its canonical id. -/
def jsSigOf (cfg : JsConfig) {ks : List Nat} (Δ : DSig ks) : JsSig :=
  let rows : List (Nat × JsTy) := Δ.brefs.flatMap fun b =>
    (List.finRange ((Δ.block b).k + 1)).map fun j =>
      let i := refIndex ((Δ.block b).ref j)
      (cfg.declCanon.getD i i, lowerTy cfg ((Δ.block b).unfold j))
  let n := blocksSize ks
  { decls := (Array.range n).map fun i =>
      ((rows.find? (·.1 == i)).map (·.2)).getD (.obj (.decl i) []) }

/-- The configuration `cfg` with the canonical ids of the datatypes of `Δ` (`canonDecls` of
    their bodies, lowered with every datatype its own). -/
def withCanonDecls (cfg : JsConfig) {ks : List Nat} (Δ : DSig ks) : JsConfig :=
  let cfg₀ := { cfg with declCanon := #[] }
  { cfg with declCanon := canonDecls (jsSigOf cfg₀ Δ).decls }

/-! ## Literals -/

/-- The start of the error of a literal that does not fit in its representation (a `Nat`
    above `2^53 - 1` as a `uint53`): an error of the whole translation, which stops
    `leanscript` (with a failure), unlike a construct not converted yet. -/
def literalTooBigPrefix : String := "literal too big: "

/-- Is the error of the conversion a literal too big for its representation? -/
def isLiteralTooBig (e : String) : Bool := e.startsWith literalTooBigPrefix

/-- A literal of a leaf type, at the representation the configuration gives it. -/
def primLit (cfg : JsConfig) : (p : LeanPrimTy) → p.denote → Except String (Σ t, JsLit t)
  | .bool, b => pure ⟨_, .bool b⟩
  | .nat, n => natLit "Nat" (lowerScalarPrim cfg .nat) n
  | .int, n => intLit "Int" (lowerScalarPrim cfg .int) n
  | .bitvec w h, v =>
    match lowerScalarPrim cfg (.bitvec w h) with
    | .bitvec_small w' h₁ h₂ => pure ⟨.bitvec_small w' h₁ h₂, .bitvec_small v.toNat⟩
    | .bigint_bitvec_big w' h' => pure ⟨_, .bigint_bitvec_big (n := w') (h := h') v.toNat⟩
    | .int53_bitvec_big w' h' =>
      if hv : v.toNat ≤ maxSafe then pure ⟨_, .int53_bitvec_big (n := w') (h := h') v.toNat hv⟩
      else throw (tooBig s!"BitVec {w}" v.toNat)
    | _ => throw "internal: the representation of a bit vector"
  | .uint8, v => pure ⟨_, .uint8 v⟩
  | .uint16, v => pure ⟨_, .uint16 v⟩
  | .uint32, v => pure ⟨_, .uint32 v⟩
  | .uint64, v => natLit "UInt64" (lowerScalarPrim cfg .uint64) v.toNat
  | .int8, v => pure ⟨_, .int8 v⟩
  | .int16, v => pure ⟨_, .int16 v⟩
  | .int32, v => pure ⟨_, .int32 v⟩
  | .int64, v => intLit "Int64" (lowerScalarPrim cfg .int64) v.toInt
  | .char, c => pure ⟨_, .string (String.singleton c)⟩
  | .string, s => pure ⟨_, .string s⟩
  | .stringPos _ _, p => uint53Lit "String.Pos" p.offset.byteIdx
  | .stringPosRaw, p => uint53Lit "String.Pos.Raw" p.byteIdx
  | .substringRaw, s => pure ⟨_, .substring s.str s.startPos.byteIdx s.stopPos.byteIdx⟩
  | .stringSlice, s =>
    pure ⟨_, .stringSlice s.str s.startInclusive.offset.byteIdx s.endExclusive.offset.byteIdx⟩
  | .float, f => pure ⟨_, .float f.toFloat⟩
  | .float32, f => pure ⟨_, .float32 f.toFloat32⟩
  | .floatModel, m => pure ⟨_, .float (Float.ofModel m)⟩
  | .float32Model, m => pure ⟨_, .float32 (Float32.ofModel m)⟩
where
  tooBig (what : String) (n : Int) : String :=
    literalTooBigPrefix ++
      s!"the {what} literal {n} does not fit in a JavaScript number (use the bigint representation)"
  natLit (what : String) (t : JsTerminalTy) (n : Nat) : Except String (Σ t, JsLit t) :=
    match t with
    | .bigint_nat => pure ⟨_, .bigint_nat n⟩
    | _ => uint53Lit what n
  uint53Lit (what : String) (n : Nat) : Except String (Σ t, JsLit t) :=
    if h : n ≤ maxSafe then pure ⟨_, .uint53 n h⟩ else throw (tooBig what n)
  intLit (what : String) (t : JsTerminalTy) (n : Int) : Except String (Σ t, JsLit t) :=
    match t with
    | .bigint_int => pure ⟨_, .bigint_int n⟩
    | _ => if h : n.natAbs ≤ maxSafe then pure ⟨_, .int53 n h⟩ else throw (tooBig what n)

/-! ## The conversion -/

/-- The conversion monad. -/
abbrev ConvM := Except String

/-- Where a variable of `Term` lives in JavaScript: a constant or a mutable variable, by its de
    Bruijn *level* (its position counting from the outside of the function), or nowhere (a
    field annotated unused, which is never read). -/
inductive Ref where
  | c (lvl : Nat)
  | m (lvl : Nat)
  | none
  /-- A partial application: the function `base` (a constant) and the arguments passed so far,
      constants, with their types (the function takes more). -/
  | pap (base : Ref) (args : List (Ref × JsTy))
  /-- The position of the constructor held by `base`, an enum of `n` constructors from `shift`
      (`JsExpr.enumIndex`): a natural number that is not stored anywhere, but read from the enum
      (`base` itself for a `number` and `shift = 0`) wherever it is used. -/
  | enumIdx (base : Ref) (n : Nat) (shift : Int)
  /-- A record whose fields are not stored together but each in its own variable, `fs` (the
      variables of a loop that keeps a record in one variable per field, `cTailLoop`): taking
      it apart reads the variables; reading it whole builds the record `{ _1: f₁, … }`, which
      is refused (an error) when `strict` (in the step of the loop, where it would build a
      record at every iteration). -/
  | fields (fs : List Ref) (strict : Bool)
  /-- A value of a union known to be its constructor `tag`, whose fields are `fs` (the layer a
      branch of a fold runs on, `JsTerm.Lower.DataRec`): a case analysis of it takes the arm
      `tag` without a test (`cBranchAt`); reading it whole builds `{ tag: tag, _1: f₁, … }`. -/
  | ctor (tag : Nat) (fs : List Ref)
  /-- A call not made yet, `f(args)` answering a value of type `ret` (the answer of a fold at
      a subvalue, `JsTerm.Lower.DataRec`): made where it is read, or bound to a constant
      where the pair holding it is taken apart (`bindCalls`). -/
  | call (f : Ref) (args : List (Ref × JsTy)) (ret : JsTy)
  deriving Inhabited

/-- A variable of JavaScript as the facts on sizes name it: a mutable variable or not, and its
    de Bruijn *level* (`Ref.c`, `Ref.m`), which does not change under binders. -/
abbrev VarKey := Bool × Nat

/-- What the tests around the part of a statement being converted say of the sizes of arrays
    held in variables (`JsTerm.Lower.Bounds`).  A fact is about the value a variable of `Term`
    has; the JavaScript variable holding it keeps that value everywhere below the test that
    established it (a constant is never reassigned; a mutable variable of a loop is only
    assigned at the end of an iteration, from values computed before, `loopNext`). -/
structure BoundFacts where
  /-- `(a, k)`: the array in the variable `a` has at least `k` elements. -/
  minSize : List (VarKey × Nat) := []
  /-- `(i, a)`: the natural number in the variable `i` is smaller than the size of the array in
      the variable `a`. -/
  idxLt : List (VarKey × VarKey) := []
  deriving Inhabited

/-- What a case analysis on a value says of it, in one of its arms: the constant of level `src`
    (of JavaScript type `ty`) holds the constructor `tag`, whose fields are in `fields` (`.none`
    for a field the arm does not bind).  A constructor expression of the same constructor on the
    same fields is that value (`knownCtorLvl?`): it is not built again. -/
structure CtorFact where
  src : Nat
  ty : JsTy
  tag : Nat
  fields : List Ref
  deriving Inhabited

/-- The JavaScript variables of the two contexts of variables of a statement: the unknowns `Γ`
    and the known values `Φ`, innermost first. -/
structure Names where
  /-- The unknowns (`Γ`). -/
  u : List Ref := []
  /-- The known values (`Φ`). -/
  k : List Ref := []
  /-- Which unknowns and known values are owned (`LeanScript.Own.Env`, in the same order). -/
  own : Own.Env := {}
  /-- The context of ownership of the part of a statement being converted (an update of an
      array in it is done in place when `Own.updateInPlace` says so). -/
  cx : Own.Ctx := default
  /-- The constants of the versions of each local function with versions, by its number
      (`Own.FnOwn.id`), in the order of its versions (`.none` for a version not generated). -/
  fns : List (Nat × List Ref) := []
  /-- May the loop being converted have an owning closure as its accumulator
      (`Own.fnAllow`)? -/
  allowFn : Bool := true
  /-- The level of the constant of the accumulator `acc` of the tail loop being converted, when
      the loop keeps a record in one variable per field (`Ref.fields`): a record literal passed
      to `acc` has its fields bound one by one, so that the next iteration assigns them to the
      variables instead of building the record. -/
  flatAcc : Option Nat := none
  /-- What the enclosing tests say of the sizes of arrays (`JsTerm.Lower.Bounds`): an access
      known to be in bounds is written `a[i]` (`JsExpr.index`). -/
  bounds : BoundFacts := {}
  /-- What the enclosing case analyses say of the values they take apart (`CtorFact`). -/
  ctors : List CtorFact := []
  deriving Inhabited

/-- The same update of an array, done in place (`JsOpImported.toMutable?`: `…_immutable` becomes
    `…_mutable`); any other expression itself.  Only used where `Own.updateInPlace` says that
    nothing else refers to the array. -/
def JsExpr.inPlace {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → JsExpr S C M τ
  | .imported op args =>
    match op.toMutable? with
    | some ⟨_, op'⟩ => .imported op' args
    | none => .imported op args
  | e => e

/-- A copy of an array: `[...a]`, or `Uint8Array.of(...a)` for a typed array (`none` at a type
    that is not an array). -/
def JsExpr.copyArray? {C M : List JsTy} {A : JsTy} (e : JsExpr S C M A) :
    Option (JsExpr S C M A) :=
  match JsArrayLayout.of? A with
  | some ⟨_, l⟩ => some (.array_mk l (.spread e .nil))
  | none => none

/-- The same update of an array, done in place on a copy of the array
    (`…_mutable([...a], …)`): its answer is a new array even where the `…_immutable` operation
    would answer its argument itself (`Own.copyThenUpdate`). -/
def JsExpr.updateOnCopy? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option (JsExpr S C M τ)
  | .imported op (.cons a rest) =>
    match op.toMutable?, a.copyArray? with
    | some ⟨_, op'⟩, some a' => some (.imported op' (.cons a' rest))
    | _, _ => none
  | _ => none

/-- An expression at another type, when the two types are equal (they always are: a failure is
    an error of the backend). -/
def castE {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) (τ' : JsTy) : ConvM (JsExpr S C M τ') :=
  if h : τ = τ' then pure (h ▸ e) else
    throw s!"internal: the JavaScript type {τ} is not {τ'}"

/-- Arguments at other types, when the types are equal. -/
def castArgs {C M σs : List JsTy} (as : JsArgs S C M σs) (σs' : List JsTy) :
    ConvM (JsArgs S C M σs') :=
  if h : σs = σs' then pure (h ▸ as) else
    throw s!"internal: the JavaScript types {σs} are not {σs'}"

/-- The parts of an array literal at another element type, when the types are equal. -/
def castParts {C M : List JsTy} {A E : JsTy} (ps : JsParts S C M A E) (E' : JsTy) :
    ConvM (JsParts S C M A E') :=
  if h : E = E' then pure (h ▸ ps) else
    throw s!"internal: the JavaScript type {E} is not {E'}"

/-- The levels of the constants `ts` bound on top of `C` (the first one outermost). -/
def paramRefs (C ts : List JsTy) : List (Ref × JsTy) :=
  ts.zipIdx.map fun (t, i) => (.c (C.length + i), t)

/-! ## Appends as literals -/

/-- The parts of one literal followed by the parts of another. -/
def JsParts.append {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → JsParts S C M A E →
    JsParts S C M A E
  | .nil, qs => qs
  | .elem e ps, qs => .elem e (ps.append qs)
  | .spread a ps, qs => .spread a (ps.append qs)

/-- The parts `e` brings to an array (or array-layout list) literal of type `A`: the parts of
    `e` when it is a literal itself (`[...[x, ...a], y]` is `[x, ...a, y]`), otherwise the spread
    `...e`. -/
def JsExpr.spliceParts {C M : List JsTy} {A : JsTy} (E : JsTy) :
    JsExpr S C M A → ConvM (JsParts S C M A E)
  | .array_mk _ ps => castParts ps E
  | .list_mk ps => castParts ps E
  | e => pure (.spread e .nil)

/-- `a ++ b` (`Array.append`, `List.append` at the array layout) as one literal, `[...a, ...b]`,
    in which an operand that is a literal itself (an array literal, or an append already written
    as one) is spliced: a chain of appends is one literal whatever the nesting, and its literal
    operands are merged (`#["a"] ++ (xs ++ #["b"])` is `["a", ...xs, "b"]`).  `none` when the
    arguments are not two arrays (or two array-layout lists) of type `τ`. -/
def appendLit? {C M σs : List JsTy} {τ : JsTy} (as : JsArgs S C M σs) :
    ConvM (Option (JsExpr S C M τ)) :=
  match σs, as with
  | [_, _], .cons a (.cons b .nil) => do
    match JsArrayLayout.of? τ with
    | some ⟨E, l⟩ =>
      let pa ← (← castE a τ).spliceParts E
      let pb ← (← castE b τ).spliceParts E
      return some (.array_mk l (pa.append pb))
    | none =>
      match τ with
      | .list α =>
        let pa ← (← castE a (.list α)).spliceParts α
        let pb ← (← castE b (.list α)).spliceParts α
        return some (← castE (.list_mk (pa.append pb)) τ)
      | _ => return none
  | _, _ => return none

/-- Is the expression an array (or array-layout list) literal? -/
def JsExpr.isArrayLit {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .array_mk _ _ => true
  | .list_mk _ => true
  | _ => false

/-- Is the first of the arguments an array (or array-layout list) literal? -/
def JsArgs.firstIsArrayLit {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .cons a _ => a.isArrayLit
  | .nil => false

mutual
/-- The JavaScript value of a `Ref`, in the contexts `C` and `M`, at the type `τ`: a variable,
    or the closure of a partial application (`(y) => f(a, y)`). -/
partial def Ref.get {C M : List JsTy} (r : Ref) (τ : JsTy) : ConvM (JsExpr S C M τ) :=
  match r with
  | .c l => match JsMem.ofIndex? C (C.length - 1 - l) τ with
    | some x => pure (.cvar x)
    | _ => throw s!"internal: no constant of type {τ} at level {l}"
  | .m l => match JsMem.ofIndex? M (M.length - 1 - l) τ with
    | some x => pure (.mvar x)
    | _ => throw s!"internal: no mutable variable of type {τ} at level {l}"
  | .none => pure (.unreachable τ)
  | .pap base args => match τ with
    | .fn ds c => do
      let body ← papCall base (args ++ paramRefs C ds) c (C := pushAll ds C) (M := M)
      return .lam (ds.map fun _ => "y") (.ret body)
    | _ => throw s!"internal: a partial application at the type {τ}"
  | .enumIdx base n shift => match JsNatTy.of? τ with
    | some nt => return .enumIndex nt (← base.get (.enum n shift))
    | none => throw s!"internal: the position of a constructor at the type {τ}"
  | .fields fs strict => do
    if strict then throw "tail loop: a record kept in the variables of the loop is read whole"
    match τ with
    | .obj id args =>
      let ts := S.fieldsOf id args
      if fs.length != ts.length then throw "internal: the fields of a record kept in variables"
      let as : JsArgs S C M ts ← castArgs (← refArgs (fs.zip ts)) ts
      castE (JsExpr.record_mk (id := id) (args := args) as) τ
    | _ => throw s!"internal: a record kept in variables at the type {τ}"
  | .ctor tag fs => match τ with
    | .obj id args => do
      let some ts := (S.ctorsOf id args)[tag]? | throw "internal: a known constructor"
      if fs.length != ts.length then throw "internal: the fields of a known constructor"
      let as ← refArgs (C := C) (M := M) (fs.zip ts)
      match JsMem.ofIndex? (S.ctorsOf id args) tag ((fs.zip ts).map (·.2)) with
      | some m => pure (.union_mk m as)
      | none => throw "internal: the fields of a known constructor"
    | _ => throw s!"internal: a known constructor at the type {τ}"
  | .call f args ret => do castE (← papCall f args ret) τ

/-- The call of `base` on all its arguments `args`, answering a value of type `c`. -/
partial def papCall {C M : List JsTy} (base : Ref) (args : List (Ref × JsTy)) (c : JsTy) :
    ConvM (JsExpr S C M c) := do
  return .app (← base.get (.fn (args.map (·.2)) c)) (← refArgs args)

/-- The values of `Ref`s, as arguments. -/
partial def refArgs {C M : List JsTy} : (as : List (Ref × JsTy)) → ConvM (JsArgs S C M (as.map (·.2)))
  | [] => pure .nil
  | (r, t) :: as => return .cons (← r.get t) (← refArgs as)
end

/-- Can a value of the type hold an array that an update in place could change (a generic or
    typed array, anywhere in it, the declared datatypes `S` unfolded)?  A value of any other
    type is never changed once built, so it can be shared instead of built again. -/
partial def JsTy.hasMutable (S : JsSig) (seen : List Nat := []) : JsTy → Bool
  | .array _ | .typedArray _ => true
  | .terminal _ | .enum .. | .fn .. => false
  | .list e | .thunk e => e.hasMutable S seen
  | .obj (.decl i) args =>
    args.any (·.hasMutable S seen) || (!seen.contains i && (S.body i).hasMutable S (i :: seen))
  | .obj _ args => args.any (·.hasMutable S seen)

/-- The level of the constant that already holds the constructor `tag` of type `ty` on the
    fields held by the constants of levels `args`, by the facts `facts` of the enclosing case
    analyses (`CtorFact`); never for a type that can hold an array (`JsTy.hasMutable`). -/
def knownCtorLvl? (facts : List CtorFact) (tag : Nat) (args : List (Option Nat)) (ty : JsTy) :
    Option Nat :=
  if ty.hasMutable S then none else
  (facts.find? fun f => f.tag == tag && f.ty == ty && f.fields.length == args.length &&
    (f.fields.zip args).all fun (r, a) => match r, a with
      | .c l, some l' => l == l'
      | _, _ => false).map (·.src)

/-- The refs `rs` with every call not made yet (`Ref.call`) that `used` says is read bound to a
    constant first (`const x = f(a);`), for `rest`; a call that is not read is dropped (it
    would compute nothing anybody reads: the language is pure and total). -/
partial def bindCalls {C M J : List JsTy} {k : JsEnd} (rs : List Ref) (used : List Bool)
    (rest : List Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J k)) : ConvM (JsBlock S C M J k) :=
  match rs with
  | [] => rest [] C
  | r :: rs' =>
    match r, used.headD true with
    | .call f as t, true => do
      let e ← papCall (C := C) (M := M) f as t
      return .const "x" e (← bindCalls (C := t :: C) rs' used.tail fun rs'' C' =>
        rest (.c C.length :: rs'') C')
    | .call _ _ _, false => bindCalls rs' used.tail fun rs'' C' => rest (.none :: rs'') C'
    | _, _ => bindCalls rs' used.tail fun rs'' C' => rest (r :: rs'') C'

/-- `e` as a constant, for `k`: `e` itself when it is a constant already, else `const x = e;`
    and the rest. -/
def bindConst {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (e : JsExpr S C M τ)
    (rest : Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J k)) : ConvM (JsBlock S C M J k) :=
  match e with
  | .cvar x => rest (.c (C.length - 1 - x.index)) C
  | e => return .const "x" e (← rest (.c C.length) (τ :: C))

/-- A pattern over the fields `ts` keeping the ones `keep` says, and where each field lives
    once the pattern has bound them in the constants `C`. -/
def mkSel : (ts : List JsTy) → List Bool → (C : List JsTy) → (Σ us, JsSel ts us) × List Ref
  | [], _, _ => (⟨[], .nil⟩, [])
  | t :: ts, b :: bs, C =>
    if b then
      let (⟨us, s⟩, rs) := mkSel ts bs (t :: C)
      (⟨t :: us, .keep "f" s⟩, .c C.length :: rs)
    else
      let (⟨us, s⟩, rs) := mkSel ts bs C
      (⟨us, .skip s⟩, .none :: rs)
  | t :: ts, [], C =>
    let (⟨us, s⟩, rs) := mkSel ts [] (t :: C)
    (⟨t :: us, .keep "f" s⟩, .c C.length :: rs)

/-- Which fields a pattern binds: every field not annotated unused. -/
def usedFields (us : List Usage01ω) : List Bool := us.map fun | .zero => false | _ => true

/-- The position of a constructor in a union. -/
def ctorIxIndex {ks : List Nat} : {bs : List Bool} → {b : Bool} → {cs : Ctors ks bs} →
    {c : Ctor ks b} → CtorIx cs c → Nat
  | _, _, _, _, .two₁ => 0
  | _, _, _, _, .two₂ => 1
  | _, _, _, _, .head => 0
  | _, _, _, _, .tail ix => ctorIxIndex ix + 1

/-- The error for the constructs not converted yet. -/
def notYet {α : Type} : ConvM α :=
  throw "the course-of-values recursion of depth 1 or more over a declared datatype is not converted to JavaScript yet"

/-- The number of declaration a type names, when it is a declared datatype. -/
def declOf? : JsTy → Option Nat
  | .obj (.decl i) [] => some i
  | _ => none

/-- One layer into a declared datatype (`JsExpr.fold`): `e`, a value of the body, at the type
    `τ` of the datatype. -/
def foldE {C M : List JsTy} {σ : JsTy} (e : JsExpr S C M σ) (τ : JsTy) : ConvM (JsExpr S C M τ) :=
  match declOf? τ with
  | some i => do castE (.fold i (← castE e (S.body i))) τ
  | none => throw s!"internal: a layer into the type {τ}"

/-- One layer out of a declared datatype (`JsExpr.unfold`), at the type `τ` of its body. -/
def unfoldE {C M : List JsTy} {σ : JsTy} (e : JsExpr S C M σ) (τ : JsTy) : ConvM (JsExpr S C M τ) :=
  match declOf? σ with
  | some i => do castE (.unfold i (← castE e (.obj (.decl i) []))) τ
  | none => throw s!"internal: a layer out of the type {σ}"

/-- A block at another type of result, when the types are equal. -/
def castRet {C M J : List JsTy} {τ : JsTy} (b : JsBlock S C M J (.ret τ)) (τ' : JsTy) :
    ConvM (JsBlock S C M J (.ret τ')) :=
  if h : τ = τ' then pure (h ▸ b) else
    throw s!"internal: the JavaScript type {τ} is not {τ'}"

/-- The arms of a case analysis on a union at other constructors, when they are equal. -/
def castArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (a : JsUnionArms S C M J k cs)
    (cs' : List (List JsTy)) : ConvM (JsUnionArms S C M J k cs') :=
  if h : cs = cs' then pure (h ▸ a) else
    throw s!"internal: the constructors {cs} are not {cs'}"

/-- A record literal of type `τ` (an object type) of the fields `as`. -/
def recordLit {C M σs : List JsTy} (as : JsArgs S C M σs) (τ : JsTy) : ConvM (JsExpr S C M τ) :=
  match τ with
  | .obj id args => do return .record_mk (← castArgs as (S.fieldsOf id args))
  | τ => throw s!"internal: a record literal of type {τ}"

/-- A list literal of type `L` (a list type) of the parts `ps`: `[e₀, …]` at the array layout
    (`JsTy.list`), the cons cells `{ tag: 1, _1: e₀, _2: … { tag: 0 } }` at the tagged layout
    (the prelude's `consList`, `ListRepr.taggedUnion`). -/
def listLit {C M : List JsTy} {α : JsTy} (ps : JsParts S C M (.list α) α) (L : JsTy) :
    ConvM (JsExpr S C M L) :=
  if L.isConsList then castE ps.toConsList L else castE (.list_mk ps) L

/-- `e()`: the value of a delay (a function of no parameter) of type `r`. -/
def forceLazy {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) (r : JsTy) : ConvM (JsExpr S C M r) :=
  match τ, e with
  | .fn [] _, e => castE (.app e .nil) r
  | τ, _ => throw s!"internal: forcing a value of type {τ}"

/-- The constructor of position `i` of the object type `τ`, of the fields `as`. -/
def unionMk {C M σs : List JsTy} (τ : JsTy) (i : Nat) (as : JsArgs S C M σs) : ConvM (JsExpr S C M τ) :=
  match τ with
  | .obj id args => match JsMem.ofIndex? (S.ctorsOf id args) i σs with
    | some m => pure (.union_mk m as)
    | none => throw "internal: the fields of a constructor"
  | τ => throw s!"internal: a constructor of type {τ}"

/-- A case analysis on `e`, a value of a union type, by the arms `arms`. -/
def unionCasesAny {C M J : List JsTy} {k : JsEnd} {σ : JsTy} {cs : List (List JsTy)}
    (e : JsExpr S C M σ) (arms : JsUnionArms S C M J k cs) : ConvM (JsBlock S C M J k) :=
  match σ, e with
  | .obj id args, e => do return .unionCases e (← castArms arms (S.ctorsOf id args))
  | σ, _ => throw s!"internal: a case analysis on a value of type {σ}"

/-- Where the function of a call lives, when it is a variable. -/
def pexprRef? {ks : List Nat} {Δ : DSig ks} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (f : PExpr Δ Φ Γ τ o) (n : Names) : Option Ref :=
  match f with
  | .neu (.var x) => some (n.u.getD x.index .none)
  | .kvar x => some (n.k.getD x.index .none)
  | _ => none

/-- The string `s` of the first `String.Pos s` among the types of the arguments of an extern, if
    any: the operation takes it as its first argument. -/
def stringPosArg? {ks : List Nat} : List (Ty ks) → Option String
  | [] => none
  | Ty.prim (.stringPos s _) :: _ => some s
  | _ :: ts => stringPosArg? ts

/-- The body of a loop at another element type, when the types are equal. -/
def castBodyElem {C M : List JsTy} {α E : JsTy} {k : JsEnd} (b : JsBlock S (α :: E :: C) M [] k)
    (E'' : JsTy) : ConvM (JsBlock S (α :: E'' :: C) M [] k) :=
  if h : E = E'' then pure (h ▸ b) else
    throw s!"internal: the JavaScript type {E} is not {E''}"

/-- `const { … } = e;` (for the fields `used` says) and the rest, which `rest` builds from where
    the fields live; just the rest when the pattern binds nothing. -/
def destructureAny {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (e : JsExpr S C M τ) (used : List Bool)
    (rest : List Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J k)) : ConvM (JsBlock S C M J k) :=
  match τ, e with
  | .obj id args, e => do
    let (⟨us, sel⟩, refs) := mkSel (S.fieldsOf id args) used C
    match us, sel with
    | [], _ => rest refs C
    | u :: us', sel => return .destructure e sel (← rest refs (pushAll (u :: us') C))
  | τ, _ => throw s!"internal: taking apart a value of type {τ}"


/-- The expressions `es` as the arguments of types `σs`, when their types are those. -/
def argsOfList? {C M : List JsTy} :
    List ((σ : JsTy) × JsExpr S C M σ) → (σs : List JsTy) → Option (JsArgs S C M σs)
  | [], [] => some .nil
  | ⟨σ, e⟩ :: es, σ' :: σs =>
    if h : σ = σ' then (JsArgs.cons (h ▸ e) ·) <$> argsOfList? es σs else none
  | _, _ => none

/-- The body of a loop whose accumulator is the mutable variable `acc`, the body reading the
    accumulator as its innermost constant: the body starts with a `const` copy of `acc` (a
    closure built by the body captures the value of this iteration, not the variable the loop
    reassigns), and every `return e` becomes `acc = e;`. -/
def loopBody {C M : List JsTy} {α E : JsTy} (acc : JsMem M α)
    (body : JsBlock S (α :: E :: C) M [] (.ret α)) : JsBlock S (E :: C) M [] .loop :=
  .const "a" (.mvar acc) (body.retToNext acc)

end MoreJs

end
