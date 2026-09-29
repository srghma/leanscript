module

public import JsTerm.Ty.Lower
public import JsTerm.Lower.Extern
public import JsTerm.Passes.Simplify
public import LeanScript.Term.Syntax.Packed

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

open LeanScript

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
  deriving Inhabited

/-- The JavaScript variables of the two contexts of variables of a statement: the unknowns `Γ`
    and the known values `Φ`, innermost first. -/
structure Names where
  /-- The unknowns (`Γ`). -/
  u : List Ref := []
  /-- The known values (`Φ`). -/
  k : List Ref := []
  deriving Inhabited

/-- An expression at another type, when the two types are equal (they always are: a failure is
    an error of the backend). -/
def castE {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) (τ' : JsTy) : ConvM (JsExpr C M τ') :=
  if h : τ = τ' then pure (h ▸ e) else
    throw s!"internal: the JavaScript type {τ} is not {τ'}"

/-- Arguments at other types, when the types are equal. -/
def castArgs {C M σs : List JsTy} (as : JsArgs C M σs) (σs' : List JsTy) :
    ConvM (JsArgs C M σs') :=
  if h : σs = σs' then pure (h ▸ as) else
    throw s!"internal: the JavaScript types {σs} are not {σs'}"

/-- The parts of an array literal at another element type, when the types are equal. -/
def castParts {C M : List JsTy} {A E : JsTy} (ps : JsParts C M A E) (E' : JsTy) :
    ConvM (JsParts C M A E') :=
  if h : E = E' then pure (h ▸ ps) else
    throw s!"internal: the JavaScript type {E} is not {E'}"

/-- The levels of the constants `ts` bound on top of `C` (the first one outermost). -/
def paramRefs (C ts : List JsTy) : List (Ref × JsTy) :=
  ts.zipIdx.map fun (t, i) => (.c (C.length + i), t)

mutual
/-- The JavaScript value of a `Ref`, in the contexts `C` and `M`, at the type `τ`: a variable,
    or the closure of a partial application (`(y) => f(a, y)`). -/
partial def Ref.get {C M : List JsTy} (r : Ref) (τ : JsTy) : ConvM (JsExpr C M τ) :=
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

/-- The call of `base` on all its arguments `args`, answering a value of type `c`. -/
partial def papCall {C M : List JsTy} (base : Ref) (args : List (Ref × JsTy)) (c : JsTy) :
    ConvM (JsExpr C M c) := do
  return .app (← base.get (.fn (args.map (·.2)) c)) (← refArgs args)

/-- The values of `Ref`s, as arguments. -/
partial def refArgs {C M : List JsTy} : (as : List (Ref × JsTy)) → ConvM (JsArgs C M (as.map (·.2)))
  | [] => pure .nil
  | (r, t) :: as => return .cons (← r.get t) (← refArgs as)
end

/-- `e` as a constant, for `k`: `e` itself when it is a constant already, else `const x = e;`
    and the rest. -/
def bindConst {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (e : JsExpr C M τ)
    (rest : Ref → (C' : List JsTy) → ConvM (JsBlock C' M J k)) : ConvM (JsBlock C M J k) :=
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
  throw "the recursors of declared datatypes are not converted to JavaScript yet"

/-- A block at another type of result, when the types are equal. -/
def castRet {C M J : List JsTy} {τ : JsTy} (b : JsBlock C M J (.ret τ)) (τ' : JsTy) :
    ConvM (JsBlock C M J (.ret τ')) :=
  if h : τ = τ' then pure (h ▸ b) else
    throw s!"internal: the JavaScript type {τ} is not {τ'}"

/-- The arms of a case analysis on a union at other constructors, when they are equal. -/
def castArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (a : JsUnionArms C M J k cs)
    (cs' : List (List JsTy)) : ConvM (JsUnionArms C M J k cs') :=
  if h : cs = cs' then pure (h ▸ a) else
    throw s!"internal: the constructors {cs} are not {cs'}"

/-- A record literal of type `τ` (a record type) of the fields `as`. -/
def recordLit {C M σs : List JsTy} (as : JsArgs C M σs) (τ : JsTy) : ConvM (JsExpr C M τ) :=
  match τ with
  | .record f₁ f₂ fs => do return .record_mk (← castArgs as (f₁ :: f₂ :: fs))
  | τ => throw s!"internal: a record literal of type {τ}"

/-- A list literal of type `L` (a list type) of the parts `ps`: `[e₀, …]` at the array layout
    (`JsTy.list`), the cons cells `{ tag: 1, _1: e₀, _2: … { tag: 0 } }` at the tagged layout
    (`JsTy.consList`, `ListRepr.taggedUnion`). -/
def listLit {C M : List JsTy} {α : JsTy} (ps : JsParts C M (.list α) α) (L : JsTy) :
    ConvM (JsExpr C M L) :=
  if L.isConsList then castE ps.toConsList L else castE (.list_mk ps) L

/-- `e()`: the value of a delay (a function of no parameter) of type `r`. -/
def forceLazy {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) (r : JsTy) : ConvM (JsExpr C M r) :=
  match τ, e with
  | .fn [] _, e => castE (.app e .nil) r
  | τ, _ => throw s!"internal: forcing a value of type {τ}"

/-- The constructor of position `i` of the union type `τ`, of the fields `as`. -/
def unionMk {C M σs : List JsTy} (τ : JsTy) (i : Nat) (as : JsArgs C M σs) : ConvM (JsExpr C M τ) :=
  match τ with
  | .union c₀ c₁ cs => match JsMem.ofIndex? (c₀ :: c₁ :: cs) i σs with
    | some m => pure (.union_mk m as)
    | none => throw "internal: the fields of a constructor"
  | τ => throw s!"internal: a constructor of type {τ}"

/-- A case analysis on `e`, a value of a union type, by the arms `arms`. -/
def unionCasesAny {C M J : List JsTy} {k : JsEnd} {σ : JsTy} {cs : List (List JsTy)}
    (e : JsExpr C M σ) (arms : JsUnionArms C M J k cs) : ConvM (JsBlock C M J k) :=
  match σ, e with
  | .union c₀ c₁ cs', e => do return .unionCases e (← castArms arms (c₀ :: c₁ :: cs'))
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
def castBodyElem {C M : List JsTy} {α E : JsTy} {k : JsEnd} (b : JsBlock (α :: E :: C) M [] k)
    (E'' : JsTy) : ConvM (JsBlock (α :: E'' :: C) M [] k) :=
  if h : E = E'' then pure (h ▸ b) else
    throw s!"internal: the JavaScript type {E} is not {E''}"

/-- Is the body of an array fold, whose accumulator is its innermost constant and element the
    one around it, the push of the element onto the accumulator
    (`return array__lean_array_push(acc, e);`)? -/
def isPushStep {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → Bool
  | .ret (.imported op (.cons a (.cons b .nil))) =>
    op.name == "array__lean_array_push_immutable" && cvarIndex? a == some 0 &&
      cvarIndex? b == some 1
  | _ => false
where
  cvarIndex? {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Option Nat
    | .cvar x => some x.index
    | _ => none

/-- `const { … } = e;` (for the fields `used` says) and the rest, which `rest` builds from where
    the fields live; just the rest when the pattern binds nothing. -/
def destructureAny {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (e : JsExpr C M τ) (used : List Bool)
    (rest : List Ref → (C' : List JsTy) → ConvM (JsBlock C' M J k)) : ConvM (JsBlock C M J k) :=
  match τ, e with
  | .record f₁ f₂ fs, e => do
    let (⟨us, sel⟩, refs) := mkSel (f₁ :: f₂ :: fs) used C
    match us, sel with
    | [], _ => rest refs C
    | u :: us', sel => return .destructure e sel (← rest refs (pushAll (u :: us') C))
  | τ, _ => throw s!"internal: taking apart a value of type {τ}"


/-- `[...z, ...arr]` on a generic array (none on a typed array). -/
def appendLit {C M : List JsTy} {A E : JsTy} (l : JsArrayLayout A E) (z arr : JsExpr C M A) :
    Option (JsExpr C M A) :=
  match A, E, l, z, arr with
  | _, _, .generic _, z, arr => some (.array_mk (.generic _) (.spread z (.spread arr .nil)))
  | _, _, .typed .., _, _ => none

/-- The body of a loop whose accumulator is the mutable variable `acc`, the body reading the
    accumulator as its innermost constant: every `return e` becomes `acc = e;`.  When the body
    builds a closure, the constant is a `const` copy of `acc` made at the start of the
    iteration (a closure must capture the value of this iteration, not the variable the loop
    reassigns); otherwise the body reads `acc` itself. -/
def loopBody {C M : List JsTy} {α E : JsTy} (acc : JsMem M α)
    (body : JsBlock (α :: E :: C) M [] (.ret α)) : JsBlock (E :: C) M [] .loop :=
  if body.occs.any (·.inClosure) then
    .const "a" (.mvar acc) (body.retToNext acc)
  else
    (body.subst (JsSubst.inst (.mvar acc))).retToNext acc

end MoreJs

end
