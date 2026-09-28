module

public import JsTerm.Extern
public import JsTerm.Simplify
public import JsTerm.InPlace
public import LeanScript.Term.Syntax.Packed

@[expose] public section

set_option autoImplicit false

/-!
# From `Term` to the JavaScript grammar

`termToJs cfg t` converts a closed normal-form statement (`LeanScript.Term`) into a
JavaScript function (`MoreJs.JsFun`), at the configuration `cfg`.  The conversion is
syntax-directed and type-directed: a `Term` of type `τ` becomes a `JsTerm` of type
`lowerTy cfg τ`, and each construct of `Term` has one JavaScript shape:

| `Term` | JavaScript |
| --- | --- |
| an unknown, a known value (de Bruijn) | a constant (`const`, a parameter, a field) or a mutable variable (the accumulator of a loop), by its de Bruijn index in its own context; join points stay de Bruijn indexed |
| `PExpr.lit` | a literal at the configured representation (`12n` or `12`); a literal that does not fit in a `number` is refused |
| `record_mk`, `union_mk ix`, `array_mk`, `list_mk` | `{ _1: f₁, … }`, `{ tag: ix, _1: f₁, … }`, `[e₀, …]` or `Uint8Array.of(…)`, `[e₀, …]` |
| `enum_mk i` | the number `shift + i` |
| `Neu.cond` | `c ? a : b` |
| `Neu.extern` | the operation of the extern at these types (`MoreJs.lowerExtern`) |
| `Val.lam` | `(x) => { … }` |
| `Val.thunk_mk`, `Val.lazy_mk` | `thunk__lean_mk_thunk(() => { … })`, `() => { … }` |
| `Term.ret`, `Term.jump j v` | `return e;`, a jump to the join point `j` |
| `Term.letV`, `Term.letE` | `const k = v;`, `const x = c;` |
| `Term.record_casesOn` | `const { _1: f₁, _3: f₃ } = r;` (unused fields skipped) |
| `Branch.ite`, `enum_casesOn`, `union_casesOn` | `if`/`else`, and case analyses |
| `Branch.join` | a join point (`JsBlock.join`) |
| `Comp.app f a`, `Comp.share n` | `f(a)`, `n` |
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }`; when the step ignores the accumulator (a case analysis `0` / `k + 1`), only the last iteration (`JsBlock.lastIter`) |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }`; a fold pushing every element (`Array.append z a`) on generic arrays is `[...z, ...a]` |
| `Comp.thunk_force`, `Comp.lazy_force` | `thunk__lean_thunk_get_own(t)`, `t()` |

A literal of an unbounded type at a `number` representation (a `Nat` as a `uint53`) that does
not fit in a safe integer is an error of the conversion: `leanscript` reports it and exits.

A top-level term of the shape `val k := fun x => …; ret k` (a curried function, as every
translation of a Lean function is) is *uncurried*: its parameters become the parameters of
the exported function, as far as the lambdas go.  Function values passed as arguments or
returned stay curried (one argument at a time).

The recursors of declared datatypes (`data_in`, `data_out`, `data_rec`, `data_brec`) are not
converted yet: a term using one is refused with an error.
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

/-- The JavaScript variable of a `Ref`, in the contexts `C` and `M`, at the type `τ`. -/
def Ref.get {C M : List JsTy} (r : Ref) (τ : JsTy) : ConvM (JsExpr C M τ) :=
  match r with
  | .c l => match JsMem.ofIndex? C (C.length - 1 - l) τ with
    | some x => pure (.cvar x)
    | _ => throw s!"internal: no constant of type {τ} at level {l}"
  | .m l => match JsMem.ofIndex? M (M.length - 1 - l) τ with
    | some x => pure (.mvar x)
    | _ => throw s!"internal: no mutable variable of type {τ} at level {l}"
  | .none => pure (.unimplemented "an unused field" τ)

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
    op.name == "array__lean_array_push" && cvarIndex? a == some 0 && cvarIndex? b == some 1
  | _ => false
where
  cvarIndex? {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Option Nat
    | .cvar x => some x.index
    | _ => none

/-- `const { … } = e;` and the rest, or just the rest when the pattern binds nothing. -/
def destructureOrSkip {C M J ts : List JsTy} {k : JsEnd} :
    {us : List JsTy} → JsExpr C M (.record ts) → JsSel ts us → JsBlock (pushAll us C) M J k →
    JsBlock C M J k
  | [], _, _, rest => rest
  | _ :: _, e, sel, rest => .destructure e sel rest

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

section
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

mutual

/-- A neutral expression. -/
partial def cNeu {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (e : Neu Δ Φ Γ τ ℓ) (n : Names) (C M : List JsTy) : ConvM (JsExpr C M (lowerTy cfg τ)) :=
  match e with
  | .var x => (n.u.getD x.index .none).get _
  | .data_out _ _ _ => notYet
  | .cond c a b => do
    let ce ← castE (← cNeu c n C M) (.terminal .bool)
    return .cond ce (← cPExpr a n C M) (← cPExpr b n C M)
  | Neu.extern e args _ => do
    let as ← cArgs args n C M
    return lowerExtern (externName e) as

/-- A pure expression. -/
partial def cPExpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr C M (lowerTy cfg τ)) :=
  match e with
  | .neu e => cNeu e n C M
  | .kvar k => (n.k.getD k.index .none).get _
  | .lit p v => do
    let ⟨_, l⟩ ← primLit cfg p v
    castE (.lit l) _
  | .enum_mk s i => pure (.enum_mk s.nOfConstructors s.shift i)
  | .record_mk args => do castE (.record_mk (← cArgs args n C M)) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | PExpr.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | PExpr.list_mk (t := t) es => do
    castE (.list_mk (← cElems (A := .list (lowerTy cfg t)) es n C M)) _
  | .data_in _ _ _ => notYet

/-- Arguments. -/
partial def cArgs {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M : List JsTy) :
    ConvM (JsArgs C M (σs.map (lowerTy cfg))) :=
  match as with
  | .nil => pure .nil
  | .cons a as => return .cons (← cPExpr a n C M) (← cArgs as n C M)

/-- Elements of an array or list literal of type `A`. -/
partial def cElems {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} {A : JsTy}
    (es : Elems Δ Φ Γ t o) (n : Names) (C M : List JsTy) :
    ConvM (JsParts C M A (lowerTy cfg t)) :=
  match es with
  | .nil => pure .nil
  | .cons a as => return .elem (← cPExpr a n C M) (← cElems as n C M)

/-- A constructor of a union: `{ tag: i, _1: … }`. -/
partial def unionLit {C M : List JsTy} {bs : List Bool} {b : Bool} [UnionShape bs]
    (cs : Ctors ks bs) (c : Ctor ks b) (ix : CtorIx cs c) {σs : List JsTy} (as : JsArgs C M σs) :
    ConvM (JsExpr C M (lowerTy cfg (Ty.union (d := true) cs))) :=
  match JsMem.ofIndex? (lowerCtors cfg cs) (ctorIxIndex ix) σs with
  | some m => castE (.union_mk m as) _
  | none => throw "internal: the fields of a constructor"

/-- An array literal: `[e₀, …]`, or `Uint8Array.of(…)` for a typed array. -/
partial def arrayLit {C M : List JsTy} (t : Ty ks)
    (ps : JsParts C M (lowerTy cfg (Ty.array (d := true) t)) (lowerTy cfg t)) :
    ConvM (JsExpr C M (lowerTy cfg (Ty.array (d := true) t))) := do
  let A' := lowerTy cfg (Ty.array (d := true) t)
  match JsArrayLayout.of? A' with
  | some ⟨E, l⟩ =>
    return .array_mk l (← castParts ps E)
  | none => throw "internal: the layout of an array"

/-- A value of known shape. -/
partial def cVal {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr C M (lowerTy cfg τ)) :=
  match v with
  | Val.lam (σ := σ) b => do
    let body ← cBody b n (lowerTy cfg σ :: C) M [.c C.length]
    return .lam "x" body
  | Val.thunk_mk (τ := t) b => do
    let body ← cBody b n C M []
    let lz ← castE (.lazy_mk body) (.lazy (lowerTy cfg t))
    return lowerExtern "lean_mk_thunk" (.cons lz .nil)
  | Val.lazy_mk b => do castE (.lazy_mk (← cBody b n C M [])) _
  | .record_mk args => do castE (.record_mk (← cArgs args n C M)) _
  | Val.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | Val.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | Val.list_mk (t := t) es => do
    castE (.list_mk (← cElems (A := .list (lowerTy cfg t)) es n C M)) _
  | .data_in _ _ _ => notYet

/-- The body of a closure, a delay or a loop, whose parameters live at `xs` (innermost first;
    `C` already holds them): a block ending in `return`. -/
partial def cBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (xs : List Ref) :
    ConvM (JsBlock C M [] (.ret (lowerTy cfg τ))) :=
  match b with
  | .closed t => cTerm t { n with u := xs } C M []
  | .opened t _ => cTerm t { n with u := xs ++ n.u } C M []

/-- A computation, followed by the block `k` builds from where its result lives. -/
partial def cComp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (c : Comp Δ d Φ Γ τ ℓ) (n : Names) (C M J : List JsTy) {e : JsEnd}
    (k : Ref → (C' M' : List JsTy) → ConvM (JsBlock C' M' J e)) : ConvM (JsBlock C M J e) :=
  match c with
  | .app f a _ => do
    let fe ← cPExpr f n C M
    let ae ← cPExpr a n C M
    return .const "x" (.app fe ae) (← k (.c C.length) _ M)
  | .share e => do
    let ee ← cNeu e n C M
    return .const "x" ee (← k (.c C.length) _ M)
  | Comp.nat_rec (τ := ρ) cnt z s _ => do
    let N := lowerTy cfg (Ty.nat : Ty ks)
    let some nt := JsNatTy.of? N | throw "internal: the representation of a Nat"
    let α := lowerTy cfg ρ
    let cntE ← cPExpr cnt n C M
    let zE ← cPExpr z n C M
    let accLvl := M.length
    let M' := α :: M
    let acc : JsMem M' α := .zero
    -- the body: the counter, then the accumulator it reads
    let body ← cBody s n (α :: N :: C) M' [.c (C.length + 1), .c C.length]
    let rest ← k (.m accLvl) C M'
    if body.mentions ⟨false, 0⟩ then
      return .letMut "acc" zE (.forRange "i" nt cntE.wkM (loopBody acc body) rest)
    else
      -- a step that ignores the accumulator (a case analysis `0` / `k + 1` read as a
      -- recursion): only the last iteration counts, `i = n - 1`, so no loop
      let drop : JsRenM Option (α :: N :: C) (N :: C) := fun {τ} x =>
        match τ, x with
        | _, .zero => Option.none
        | _, .succ x => some x
      match body.renameM drop (fun x => some x) with
      | some body' =>
        return .letMut "acc" zE (.lastIter "i" nt cntE.wkM (body'.retToNext acc) rest)
      | none => return .letMut "acc" zE (.forRange "i" nt cntE.wkM (loopBody acc body) rest)
  | Comp.array_foldl (t := t) (ρ := ρ) arr z s _ => do
    let A := lowerTy cfg (Ty.array (d := true) t)
    let α := lowerTy cfg ρ
    let arrE ← cPExpr arr n C M
    let zE ← cPExpr z n C M
    let some ⟨E, l⟩ := JsArrayLayout.of? A | throw "internal: the layout of an array"
    let M' := α :: M
    let body ← cBody s n (α :: lowerTy cfg t :: C) M' [.c C.length, .c (C.length + 1)]
    let body ← castBodyElem body E
    -- `Array.append z arr` (a fold pushing every element onto the accumulator) on generic
    -- arrays is the array literal `[...z, ...arr]`
    if isPushStep body && α == A then
      if let some lit := appendLit l (← castE zE A) arrE then
        return .const "x" (← castE lit α) (← k (.c C.length) _ M)
    let rest ← k (.m M.length) C M'
    return .letMut "acc" zE (.forOf "e" l arrE.wkM (loopBody .zero body) rest)
  | .data_rec _ _ _ _ _ _ _ => notYet
  | .data_brec _ _ _ _ _ _ _ _ => notYet
  | Comp.thunk_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e : JsExpr C M (lowerTy cfg t.relax) := lowerExtern "lean_thunk_get_own" (.cons pe .nil)
    return .const "x" e (← k (.c C.length) _ M)
  | Comp.lazy_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e ← castE (.lazy_force pe) (lowerTy cfg t.relax)
    return .const "x" e (← k (.c C.length) _ M)

/-- A statement: a block every path of which ends in a `return` (or a jump). -/
partial def cTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock C M J (.ret (lowerTy cfg τ))) :=
  match t with
  | .ret p => return .ret (← cPExpr p n C M)
  | Term.letV (σ := σ) _ v t => do
    let ve ← cVal v n C M
    return .const "k" ve (← cTerm t { n with k := .c C.length :: n.k } (lowerTy cfg σ :: C) M J)
  | .letE _ c t => cComp c n C M J fun x C' M' => cTerm t { n with u := x :: n.u } C' M' J
  | Term.record_casesOn (t := tt) (fs := fs) us e t => do
    let ee ← cNeu e n C M
    let ts := lowerTy cfg tt :: lowerFields cfg fs
    let (⟨us', sel⟩, refs) := mkSel ts (usedFields us) C
    let rest ← cTerm t { n with u := refs ++ n.u } (pushAll us' C) M J
    return destructureOrSkip ee sel rest
  | .branch b => cBranch b n C M J
  | Term.jump (σ := σ) j p => do
    let pe ← cPExpr p n C M
    match JsMem.ofIndex? J j.index (lowerTy cfg σ) with
    | some jm => return .jump jm pe
    | none => throw "internal: a join point"

/-- A branch in tail position. -/
partial def cBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    (b : Branch Δ d Φ Γ τ js ℓ) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock C M J (.ret (lowerTy cfg τ))) :=
  match b with
  | .ite c t e => do
    let ce ← castE (← cNeu c n C M) (.terminal .bool)
    return .ite ce (← cTerm t n C M J) (← cTerm e n C M J)
  | Branch.enum_casesOn (s := s) c bs => do
    let ce ← cNeu c n C M
    let k := s.nOfConstructors
    let rec arms (m start : Nat) : ConvM (JsEnumArms C M J (.ret (lowerTy cfg τ)) m) :=
      match m with
      | 0 => pure .nil
      | m + 1 => do
        if h : start < k then
          return .cons (← cTerm (bs ⟨start, h⟩) n C M J) (← arms m (start + 1))
        else throw "internal: an arm of a case analysis"
    return .enumCases ce (← arms k 0)
  | Branch.union_casesOn e brs => do
    let ee ← cNeu e n C M
    return .unionCases ee (← cBranches brs n C M J)
  | Branch.join σ _ _ body br => do
    let σ' := lowerTy cfg σ
    let block ← cBranch br n C M (σ' :: J)
    let rest ← cTerm body { n with u := .c C.length :: n.u } (σ' :: C) M J
    return .join "x" block rest

/-- The arms of a union's case analysis: each binds the fields it uses
    (`const { _1: f₁, _2: f₂ } = s;`) and continues. -/
partial def cBranches {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) (n : Names) (C M J : List JsTy) :
    ConvM (JsUnionArms C M J (.ret (lowerTy cfg τ)) (lowerCtors cfg cs)) :=
  match brs with
  | Branches.two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂ => do
    let (⟨u₁, s₁⟩, r₁) := mkSel (lowerCtor cfg c₁) (usedFields us₁) C
    let (⟨u₂, s₂⟩, r₂) := mkSel (lowerCtor cfg c₂) (usedFields us₂) C
    let a₁ ← cTerm b₁ { n with u := r₁ ++ n.u } (pushAll u₁ C) M J
    let a₂ ← cTerm b₂ { n with u := r₂ ++ n.u } (pushAll u₂ C) M J
    return .cons s₁ a₁ (.cons s₂ a₂ .nil)
  | Branches.cons (c := c) us b rest => do
    let (⟨u, s⟩, r) := mkSel (lowerCtor cfg c) (usedFields us) C
    let a ← cTerm b { n with u := r ++ n.u } (pushAll u C) M J
    return .cons s a (← cBranches rest n C M J)

end

end

/-! ## Whole functions -/

section
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

/-- A function whose parameters `ps` are bound (as constants) on top of `C`, and its body. -/
abbrev Peeled (C : List JsTy) : Type :=
  (ps : List (String × JsTy)) × (r : JsTy) × JsBlock (pushAll (ps.map (·.2)) C) [] [] (.ret r)

mutual
/-- Convert a top-level statement, uncurrying the chain of lambdas at its head: `val k := fun
    x => (val k' := fun y => b; ret k'); ret k` becomes the parameters `x, y` and the body
    `b`, as long as the shape repeats (so `export const f = (x, y) => …` instead of
    `(x) => (y) => …`).  `names` are the preferred names of the parameters (the Lean binder
    names). -/
partial def peelFun {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ [] o) (n : Names) (C : List JsTy) (names : List String) :
    ConvM (Peeled C) :=
  let whole : ConvM (Peeled C) := do
    return ⟨[], lowerTy cfg τ, ← cTerm cfg t n C [] []⟩
  match t with
  | .letV _ v (.ret (.kvar k)) =>
    if k.index != 0 then whole else
    match v with
    | Val.lam (σ := σ) b => do
      let ⟨ps, r, body⟩ ← peelBody b n (lowerTy cfg σ :: C) (names.drop 1)
      return ⟨(names.headD "p", lowerTy cfg σ) :: ps, r, body⟩
    | _ => whole
  | _ => whole

/-- `peelFun` inside the body of a lambda (whose parameter is bound in `C`, as a constant). -/
partial def peelBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C : List JsTy) (rest : List String) :
    ConvM (Peeled C) :=
  let x : Ref := .c (C.length - 1)
  match b with
  | .closed t' => peelFun t' { n with u := [x] } C rest
  | .opened t' _ => peelFun t' { n with u := x :: n.u } C rest
end

end

/-- Convert a closed program into an exported JavaScript function named `name`
    (`export const name = (params) => …`).  `paramNames` are the preferred names of its
    parameters.  The body is cleaned up (`peephole`, `inlineArrays`), and the arrays nothing
    else refers to are updated in place (`inPlace`). -/
def termToJs (cfg : JsConfig) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) : Except String JsFun := do
  let ⟨ps, ret, body⟩ ← peelFun cfg ct.term {} [] paramNames
  let body := peephole (inlineArrays (peephole body))
  let body := inPlace body
  return { name, leanName, params := ps, ret, body }

end MoreJs

end
