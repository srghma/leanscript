module

public import JsTerm.Extern
public import JsTerm.InPlace
public import LeanScript.Term.Syntax.Packed

@[expose] public section

set_option autoImplicit false

/-!
# From `Term` to the JavaScript grammar

`termToJs cfg t` converts a closed normal-form statement (`LeanScript.Term`) into a
JavaScript function (`MoreJs.JsFun`), at the configuration `cfg`.  The conversion is
syntax-directed; each construct of `Term` has one JavaScript shape:

| `Term` | JavaScript |
| --- | --- |
| an unknown, a known value (de Bruijn) | a named `const` (`x$1`, `k$2`, …); join points stay de Bruijn indexed |
| `PExpr.lit` | a literal at the configured layout (`12n` or `12`); a literal that does not fit in a `number` is refused |
| `record_mk`, `union_mk ix`, `array_mk`, `list_mk` | `{ _1: f₁, … }`, `{ tag: ix, _1: f₁, … }`, `[e₀, …]` or `Uint8Array.of(…)`, `[e₀, …]` |
| `enum_mk i` | the number `shift + i` |
| `Neu.cond` | `c ? a : b` |
| `Neu.extern` | an operator or a call of a runtime function (`MoreJs.lowerExtern`) |
| `Val.lam` | `(x) => { … }` |
| `Val.thunk_mk`, `Val.lazy_mk` | `$lean_mk_thunk(() => { … })`, `() => { … }` |
| `Term.ret`, `Term.jump j v` | `return e;`, `jump j e` (`x = e; break L;`, `L` and `x` the label and the variable of the join point) |
| `Term.letV`, `Term.letE` | `const k = v;`, `const x = c;` |
| `Term.record_casesOn` | `const { _1: f₁, _3: f₃ } = r;` (unused fields skipped) |
| `Branch.ite`, `enum_casesOn`, `union_casesOn` | `if`/`else if` chains (on `s.tag` for a union) |
| `Branch.join` | `let x; join x { branch }` (the labelled block `L: { … }`) followed by the body of the join point |
| `Comp.app f a`, `Comp.share n` | `f(a)`, `n` |
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }`; when the step ignores the accumulator (a case analysis `0` / `k + 1`), `let acc = z; if (0n < n) { const i = n - 1n; …; acc = …; }` |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }`; a fold pushing every element (`Array.append z a`) on generic arrays is `[...z, ...a]` |
| `Comp.thunk_force`, `Comp.lazy_force` | `$lean_thunk_get_own(t)`, `t()` |

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

/-- The largest safe integer of a `number`. -/
def maxSafe : Nat := 2 ^ 53 - 1

/-- An unbounded natural number at the layout `t`: a `BigInt`, or a `number` if it fits. -/
def natLit (what : String) (t : JsTerm) (n : Nat) : Except String JsExpr :=
  if t.isBigInt then pure (.lit (.bigint n))
  else if n ≤ maxSafe then pure (.lit (.int n))
  else throw s!"the {what} literal {n} does not fit in a JavaScript number (use the bigint representation)"

/-- An unbounded integer at the layout `t`. -/
def intLit (what : String) (t : JsTerm) (n : Int) : Except String JsExpr :=
  if t.isBigInt then pure (.lit (.bigint n))
  else if n.natAbs ≤ maxSafe then pure (.lit (.int n))
  else throw s!"the {what} literal {n} does not fit in a JavaScript number (use the bigint representation)"

/-- A literal of a leaf type, at the layout the configuration gives it. -/
def primLit (cfg : JsConfig) : (p : LeanPrimTy) → p.denote → Except String JsExpr
  | .bool, b => pure (.lit (.bool b))
  | .nat, n => natLit "Nat" (lowerScalarPrim cfg .nat) n
  | .int, n => intLit "Int" (lowerScalarPrim cfg .int) n
  | .bitvec w h, v => natLit s!"BitVec {w}" (lowerScalarPrim cfg (.bitvec w h)) v.toNat
  | .uint8, v => pure (.lit (.int v.toNat))
  | .uint16, v => pure (.lit (.int v.toNat))
  | .uint32, v => pure (.lit (.int v.toNat))
  | .uint64, v => natLit "UInt64" (lowerScalarPrim cfg .uint64) v.toNat
  | .int8, v => pure (.lit (.int v.toInt))
  | .int16, v => pure (.lit (.int v.toInt))
  | .int32, v => pure (.lit (.int v.toInt))
  | .int64, v => intLit "Int64" (lowerScalarPrim cfg .int64) v.toInt
  | .char, c => pure (.lit (.str (String.singleton c)))
  | .string, s => pure (.lit (.str s))
  | .stringPos _ _, p => pure (.lit (.int p.offset.byteIdx))
  | .stringPosRaw, p => pure (.lit (.int p.byteIdx))
  | .substringRaw, s =>
    pure (.array [.lit (.str s.str), .lit (.int s.startPos.byteIdx), .lit (.int s.stopPos.byteIdx)])
  | .stringSlice, s =>
    pure (.array [.lit (.str s.str), .lit (.int s.startInclusive.offset.byteIdx),
      .lit (.int s.endExclusive.offset.byteIdx)])
  | .float, f => pure (.lit (.number f.toFloat))
  | .float32, f => pure (.lit (.number f.toFloat32.toFloat))
  | .floatModel, m => pure (.lit (.number (Float.ofModel m)))
  | .float32Model, m => pure (.lit (.number (Float32.ofModel m).toFloat))

/-! ## The conversion -/

/-- The state of the conversion: the counter of fresh names and the runtime functions used
    so far. -/
structure ConvState where
  /-- The next fresh name. -/
  next : Nat := 1
  /-- The runtime functions the program calls, each once, in order of first use. -/
  imports : Array RtFn := #[]

/-- The conversion monad. -/
abbrev ConvM := StateT ConvState (Except String)

/-- The JavaScript names of the three contexts of a statement, innermost first. -/
structure Names where
  /-- The unknowns (`Γ`). -/
  u : List String := []
  /-- The known values (`Φ`). -/
  k : List String := []
  deriving Inhabited

/-- A fresh JavaScript name. -/
def fresh (pfx : String) : ConvM String :=
  modifyGet fun s => (s!"{pfx}${s.next}", { s with next := s.next + 1 })

/-- Record a runtime function the program calls (each once). -/
def addImport (acc : Array RtFn) (f : RtFn) : Array RtFn :=
  if acc.contains f then acc else acc.push f

/-- Record runtime functions the program calls (each once). -/
def useRt (fs : List RtFn) : ConvM Unit :=
  modify fun s => { s with imports := fs.foldl addImport s.imports }

/-- `Thunk.mk`, in the runtime. -/
def mkThunkFn : RtFn := { file := .nonConfigurable, name := "$lean_mk_thunk" }

/-- `Thunk.get`, in the runtime. -/
def thunkGetFn : RtFn := { file := .nonConfigurable, name := "$lean_thunk_get_own" }

/-- Lift an error. -/
def liftExcept {α : Type} (x : Except String α) : ConvM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- Turn the tail `return e` of every path into `acc = e` (the body of a loop). -/
partial def retToAssign (acc : String) : List JsStmt → List JsStmt
  | [] => []
  | s :: ss =>
    let s' := match s with
      | .ret e => .assign acc e
      | .ite c t e => .ite c (retToAssign acc t) (retToAssign acc e)
      | s => s
    s' :: retToAssign acc ss

/-- Does a statement contain a join point (outside of the arrows)? -/
partial def JsStmt.hasJoin : JsStmt → Bool
  | .join .. => true
  | .ite _ t e => t.any JsStmt.hasJoin || e.any JsStmt.hasJoin
  | _ => false

/-- Turn the tail `return e` of every path into a jump to the join point of de Bruijn index
    `d` (seen from the statements): the statements become the block of a join point. -/
partial def retToJump (d : Nat) : List JsStmt → List JsStmt
  | [] => []
  | s :: ss =>
    let s' := match s with
      | .ret e => .jump d e
      | .ite c t e => .ite c (retToJump d t) (retToJump d e)
      | .join x b => .join x (retToJump (d + 1) b)
      | s => s
    s' :: retToJump d ss

/-- The body of a loop iteration assigning the accumulator `acc` instead of returning: each
    `return e` becomes `acc = e`.  When the body has join points (whose blocks are followed by
    more statements), it becomes the block of a join point of variable `acc` instead, and each
    `return e` a jump out of it (`acc = e; break L;`). -/
def retToAcc (acc : String) (body : List JsStmt) : List JsStmt :=
  if body.any JsStmt.hasJoin then [.join acc (retToJump 0 body)] else retToAssign acc body

mutual
/-- Does a statement build a closure (which could capture a variable the loop reassigns)? -/
partial def JsStmt.hasArrow : JsStmt → Bool
  | .const _ e | .assign _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e
  | .expr e => e.hasArrow
  | .setMember o _ e => o.hasArrow || e.hasArrow
  | .setAt o i e => o.hasArrow || i.hasArrow || e.hasArrow
  | .letMut _ e => e.any JsExpr.hasArrow
  | .ite c t e => c.hasArrow || t.any JsStmt.hasArrow || e.any JsStmt.hasArrow
  | .forRange _ _ n b => n.hasArrow || b.any JsStmt.hasArrow
  | .forOf _ xs b | .while xs b => xs.hasArrow || b.any JsStmt.hasArrow
  | .join _ b => b.any JsStmt.hasArrow
  | .throw _ _ => false
/-- Does an expression build a closure? -/
partial def JsExpr.hasArrow : JsExpr → Bool
  | .arrow .. => true
  | .bin _ a b => a.hasArrow || b.hasArrow
  | .un _ a => a.hasArrow
  | .call f as => f.hasArrow || as.any JsExpr.hasArrow
  | .helper _ as | .array as | .typedArray _ as => as.any JsExpr.hasArrow
  | .index e _ | .member e _ | .spread e => e.hasArrow
  | .cond c a b => c.hasArrow || a.hasArrow || b.hasArrow
  | .object fs => fs.any (·.2.hasArrow)
  | .at e i => e.hasArrow || i.hasArrow
  | .new c as => c.hasArrow || as.any JsExpr.hasArrow
  | _ => false
end

/-- Rename a variable in statements that do not rebind it (the names of the conversion are
    all distinct). -/
partial def renameStmts (x y : String) (ss : List JsStmt) : List JsStmt :=
  ss.map go
where
  goE : JsExpr → JsExpr
    | .var z => .var (if z == x then y else z)
    | .bin op a b => .bin op (goE a) (goE b)
    | .un op a => .un op (goE a)
    | .helper n as => .helper n (as.map goE)
    | .call f as => .call (goE f) (as.map goE)
    | .arrow ps b => .arrow ps (b.map go)
    | .array es => .array (es.map goE)
    | .typedArray c es => .typedArray c (es.map goE)
    | .index e i => .index (goE e) i
    | .member e m => .member (goE e) m
    | .cond c a b => .cond (goE c) (goE a) (goE b)
    | .object fs => .object (fs.map fun (k, e) => (k, goE e))
    | .at e i => .at (goE e) (goE i)
    | .new c as => .new (goE c) (as.map goE)
    | .spread e => .spread (goE e)
    | e => e
  go : JsStmt → JsStmt
    | .const z e => .const z (goE e)
    | .letMut z e => .letMut z (e.map goE)
    | .assign z e => .assign (if z == x then y else z) (goE e)
    | .destructure zs e => .destructure zs (goE e)
    | .destructureObj zs e => .destructureObj zs (goE e)
    | .setMember o m e => .setMember (goE o) m (goE e)
    | .setAt o i e => .setAt (goE o) (goE i) (goE e)
    | .expr e => .expr (goE e)
    | .while c b => .while (goE c) (b.map go)
    | .ret e => .ret (goE e)
    | .ite c t e => .ite (goE c) (t.map go) (e.map go)
    | .forRange i big n b => .forRange i big (goE n) (b.map go)
    | .forOf z xs b => .forOf z (goE xs) (b.map go)
    | .throw k m => .throw k m
    | .join z b => .join (if z == x then y else z) (b.map go)
    | .jump j e => .jump j (goE e)

/-- The body of a loop whose accumulator is the mutable `acc`, the body reading it as
    `accIn`: every `return e` becomes `acc = e`.  When the body builds a closure, `accIn` is
    a `const` copy of `acc` made at the start of the iteration (a closure must capture the
    value of this iteration, not the variable the loop reassigns); otherwise the body reads
    `acc` itself. -/
def loopBody (acc accIn : String) (body : List JsStmt) : List JsStmt :=
  if body.any JsStmt.hasArrow then
    .const accIn (.var acc) :: retToAcc acc body
  else
    retToAcc acc (renameStmts accIn acc body)

mutual
/-- Does a statement mention the variable `x`? -/
partial def JsStmt.mentions (x : String) : JsStmt → Bool
  | .const _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e | .expr e =>
    e.mentions x
  | .setMember o _ e => o.mentions x || e.mentions x
  | .setAt o i e => o.mentions x || i.mentions x || e.mentions x
  | .while c b => c.mentions x || b.any (·.mentions x)
  | .letMut _ e => e.any (·.mentions x)
  | .assign y e => y == x || e.mentions x
  | .join y b => y == x || b.any (·.mentions x)
  | .ite c t e => c.mentions x || t.any (·.mentions x) || e.any (·.mentions x)
  | .forRange _ _ n b => n.mentions x || b.any (·.mentions x)
  | .forOf _ xs b => xs.mentions x || b.any (·.mentions x)
  | .throw _ _ => false
/-- Does an expression mention the variable `x`? -/
partial def JsExpr.mentions (x : String) : JsExpr → Bool
  | .var y => y == x
  | .arrow _ b => b.any (·.mentions x)
  | .bin _ a b => a.mentions x || b.mentions x
  | .un _ a => a.mentions x
  | .call f as => f.mentions x || as.any (·.mentions x)
  | .helper _ as | .array as | .typedArray _ as => as.any (·.mentions x)
  | .index e _ | .member e _ | .spread e => e.mentions x
  | .cond c a b => c.mentions x || a.mentions x || b.mentions x
  | .object fs => fs.any (·.2.mentions x)
  | .at e i => e.mentions x || i.mentions x
  | .new c as => c.mentions x || as.any (·.mentions x)
  | .lit _ => false
end

/-- An expression that can be repeated without recomputing anything. -/
def JsExpr.isAtom : JsExpr → Bool
  | .var _ | .lit _ => true
  | _ => false

/-- Is the body of an array fold, whose element is `e` and accumulator `acc`, the push of the
    element onto the accumulator (`return lean_array_push(acc, e);`)? -/
def isPushStep (acc e : String) : List JsStmt → Bool
  | [.ret (.helper h [.var a, .var x])] => h == "$lean_array_push" && a == acc && x == e
  | _ => false

/-- The name of field `i` (from `0`) of a record or a constructor: `_1`, `_2`, …. -/
def fieldKey (i : Nat) : String := s!"_{i + 1}"

/-- A record: `{ _1: e₁, _2: e₂, … }`. -/
def recordObj (es : List JsExpr) : JsExpr :=
  .object (es.zipIdx.map fun (e, i) => (fieldKey i, e))

/-- The constructor of position `tag` (from `0`) of a union: `{ tag, _1: e₁, … }`. -/
def unionObj (tag : Nat) (es : List JsExpr) : JsExpr :=
  .object (("tag", .lit (.int tag)) :: es.zipIdx.map fun (e, i) => (fieldKey i, e))

/-- The properties an object pattern takes out, for the binders of a record's (or a
    constructor's) fields, `none` for a field not used. -/
def fieldBinds (bs : List (Option String)) : List (String × String) :=
  bs.zipIdx.filterMap fun (b, i) => b.map fun x => (fieldKey i, x)

/-- The type of member `j` of a union's constructor list, as a list of field types. -/
def ctorsBinds {ks : List Nat} : {bs : List Bool} → Ctors ks bs → List (List (Ty ks))
  | _, .two a b => [a.binds, b.binds]
  | _, .cons c cs => c.binds :: ctorsBinds cs

/-- The position of a constructor in a union. -/
def ctorIxIndex {ks : List Nat} : {bs : List Bool} → {b : Bool} → {cs : Ctors ks bs} →
    {c : Ctor ks b} → CtorIx cs c → Nat
  | _, _, _, _, .two₁ => 0
  | _, _, _, _, .two₂ => 1
  | _, _, _, _, .head => 0
  | _, _, _, _, .tail ix => ctorIxIndex ix + 1

section
variable (cfg : JsConfig) (rt : Runtime) {ks : List Nat} {Δ : DSig ks}

/-- The knob of the configuration that decides how a value of this type is represented, if
    one does. -/
def knobOfTy {ks : List Nat} {d : Bool} : Ty ks d → Option RtKnob
  | .prim p => (JsConfig.knobOfPrim? p).bind RtKnob.ofName?
  | _ => none

/-- Names for the fields a pattern binds, `none` for the ones annotated unused. -/
def fieldBinders (tys : List (Ty ks)) (us : List Usage01ω) :
    ConvM (List (Option String) × List String) := do
  let mut bs := #[]
  let mut names := #[]
  for i in [0:tys.length] do
    let x ← fresh "f"
    names := names.push x
    let used := match us[i]? with
      | some .zero => false
      | _ => true
    bs := bs.push (if used then some x else none)
  return (bs.toList, names.toList)

mutual

/-- A neutral expression. -/
partial def cNeu {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Neu Δ Φ Γ τ ℓ → Names → ConvM JsExpr
  | .var x, n => pure (.var (n.u.getD x.index "undefined$"))
  | .data_out _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"
  | .cond c a b, n => do return .cond (← cNeu c n) (← cPExpr a n) (← cPExpr b n)
  | Neu.extern (σs := σs) e args _, n => do
    let as ← cArgs args n
    let (ex, fs) := lowerExtern rt (externName e) (σs.map (lowerTy cfg)) (lowerTy cfg τ)
      (knobOfTy τ) as
    useRt fs
    return ex

/-- A pure expression. -/
partial def cPExpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    PExpr Δ Φ Γ τ o → Names → ConvM JsExpr
  | .neu e, n => cNeu e n
  | .kvar k, n => pure (.var (n.k.getD k.index "undefined$"))
  | .lit p v, _ => liftExcept (primLit cfg p v)
  | .enum_mk s i, _ => pure (.lit (.int (s.shift + i.val)))
  | .record_mk args, n => return recordObj (← cArgs args n)
  | .union_mk ix args, n => return unionObj (ctorIxIndex ix) (← cArgs args n)
  | PExpr.array_mk (t := t) es, n => do
    let es ← cElems es n
    match typedCtor? (lowerTy cfg (Ty.array t : Ty ks)) with
    | some c => return .typedArray c es
    | none => return .array es
  | .list_mk es, n => return .array (← cElems es n)
  | .data_in _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"

/-- Arguments. -/
partial def cArgs {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl} :
    Args Δ Φ Γ σs o → Names → ConvM (List JsExpr)
  | .nil, _ => pure []
  | .cons a as, n => return (← cPExpr a n) :: (← cArgs as n)

/-- Elements of an array or list literal. -/
partial def cElems {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} :
    Elems Δ Φ Γ t o → Names → ConvM (List JsExpr)
  | .nil, _ => pure []
  | .cons a as, n => return (← cPExpr a n) :: (← cElems as n)

/-- A value of known shape. -/
partial def cVal {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Val Δ d Φ Γ τ o → Names → ConvM JsExpr
  | .lam b, n => do
    let x ← fresh "x"
    return .arrow [x] (← cBody b n [x])
  | .thunk_mk b, n => do
    useRt [mkThunkFn]
    return .helper mkThunkFn.name [.arrow [] (← cBody b n [])]
  | .lazy_mk b, n => return .arrow [] (← cBody b n [])
  | .record_mk args, n => return recordObj (← cArgs args n)
  | .union_mk ix args, n => return unionObj (ctorIxIndex ix) (← cArgs args n)
  | Val.array_mk (t := t) es, n => do
    let es ← cElems es n
    match typedCtor? (lowerTy cfg (Ty.array t : Ty ks)) with
    | some c => return .typedArray c es
    | none => return .array es
  | .list_mk es, n => return .array (← cElems es n)
  | .data_in _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"

/-- The body of a closure, a delay or a loop, whose parameters are named `bs` (innermost
    first): statements ending in `return`. -/
partial def cBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Body Δ d Φ Γ bs τ o → Names → List String → ConvM (List JsStmt)
  | .closed t, n, xs => cTerm t { u := xs, k := n.k }
  | .opened t _, n, xs => cTerm t { u := xs ++ n.u, k := n.k }

/-- A computation whose result is named `x`: the statements that compute it, and the name
    it can be referred to by. -/
partial def cComp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ τ ℓ → Names → ConvM (List JsStmt × String)
  | .app f a _, n => do
    let x ← fresh "x"
    return ([.const x (.call (← cPExpr f n) [← cPExpr a n])], x)
  | .share e, n => do
    let x ← fresh "x"
    return ([.const x (← cNeu e n)], x)
  | .nat_rec cnt z s _, n => do
    let acc ← fresh "acc"
    let i ← fresh "i"
    let cntE ← cPExpr cnt n
    let (pre, cntE) ← if cntE.isAtom then pure ([], cntE) else do
      let c ← fresh "n"
      pure ([JsStmt.const c cntE], JsExpr.var c)
    let zE ← cPExpr z n
    let accIn ← fresh "a"
    let body ← cBody s n [accIn, i]
    let big := (lowerTy cfg (Ty.nat : Ty ks)).isBigInt
    if body.any (·.mentions accIn) then
      return (pre ++ [.letMut acc (some zE), .forRange i big cntE (loopBody acc accIn body)], acc)
    else
      -- a step that ignores the accumulator (a case analysis `0` / `k + 1` read as a
      -- recursion): only the last iteration counts, `i = n - 1`, so no loop
      let lit (k : Nat) : JsExpr := .lit (if big then .bigint k else .int k)
      let lt : JsBinOp := if big then .bigint .lt else .num .lt
      let sub : JsBinOp := if big then .bigint .sub else .num .sub
      return (pre ++ [.letMut acc (some zE),
        .ite (.bin lt (lit 0) cntE) (.const i (.bin sub cntE (lit 1)) :: retToAcc acc body) []],
        acc)
  | Comp.array_foldl (ρ := ρ) arr z s _, n => do
    let acc ← fresh "acc"
    let e ← fresh "e"
    let arrE ← cPExpr arr n
    let zE ← cPExpr z n
    let accIn ← fresh "a"
    let saved ← get
    let body ← cBody s n [e, accIn]
    -- `Array.append z arr` (a fold pushing every element onto the accumulator) on generic
    -- arrays is the array literal `[...z, ...arr]`
    if isPushStep accIn e body && (lowerTy cfg ρ matches .genericArray _) then
      set saved
      let x ← fresh "x"
      return ([.const x (.array [.spread zE, .spread arrE])], x)
    return ([.letMut acc (some zE), .forOf e arrE (loopBody acc accIn body)], acc)
  | .data_rec _ _ _ _ _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"
  | .data_brec _ _ _ _ _ _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"
  | .thunk_force p, n => do
    let x ← fresh "x"
    useRt [thunkGetFn]
    return ([.const x (.helper thunkGetFn.name [← cPExpr p n])], x)
  | .lazy_force p, n => do
    let x ← fresh "x"
    return ([.const x (.call (← cPExpr p n) [])], x)

/-- A statement: JavaScript statements every path of which ends in a `return`. -/
partial def cTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Term Δ d Φ Γ τ js o → Names → ConvM (List JsStmt)
  | .ret p, n => return [.ret (← cPExpr p n)]
  | Term.letV _ v t, n => do
    let k ← fresh "k"
    let ve ← cVal v n
    return .const k ve :: (← cTerm t { n with k := k :: n.k })
  | .letE _ c t, n => do
    let (ss, x) ← cComp c n
    return ss ++ (← cTerm t { n with u := x :: n.u })
  | Term.record_casesOn (t := tt) (fs := fs) us e t, n => do
    let (bs, xs) ← fieldBinders (tt :: fs.toList) us
    let ee ← cNeu e n
    let rest ← cTerm t { n with u := xs ++ n.u }
    let binds := fieldBinds bs
    return if binds.isEmpty then rest else .destructureObj binds ee :: rest
  | .branch b, n => cBranch b n
  | .jump j p, n => return [.jump j.index (← cPExpr p n)]

/-- A branch in tail position. -/
partial def cBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
    Branch Δ d Φ Γ τ js ℓ → Names → ConvM (List JsStmt)
  | .ite c t e, n => return [.ite (← cNeu c n) (← cTerm t n) (← cTerm e n)]
  | Branch.enum_casesOn (s := s) c bs, n => do
    let ce ← cNeu c n
    let (pre, ce) ← if ce.isAtom then pure ([], ce) else do
      let x ← fresh "s"
      pure ([JsStmt.const x ce], JsExpr.var x)
    let k := s.nOfConstructors
    let mut out : List JsStmt := []
    for i' in [0:k] do
      let i := k - 1 - i'
      if h : i < k then
        let body ← cTerm (bs ⟨i, h⟩) n
        if i == k - 1 then out := body
        else out := [.ite (.bin .strictEq ce (.lit (.int (s.shift + i)))) body out]
    return pre ++ out
  | Branch.union_casesOn (cs := cs) e brs, n => do
    let ee ← cNeu e n
    let (pre, ee) ← if ee.isAtom then pure ([], ee) else do
      let x ← fresh "s"
      pure ([JsStmt.const x ee], JsExpr.var x)
    let arms ← cBranches brs n ee
    let k := arms.length
    let mut out : List JsStmt := []
    for (i, body) in ((List.range k).zip arms).reverse do
      if i == k - 1 then out := body
      else out := [.ite (.bin .strictEq (.member ee "tag") (.lit (.int i))) body out]
    let _ := ctorsBinds cs
    return pre ++ out
  | Branch.join _ _ _ body br, n => do
    let x ← fresh "x"
    let block ← cBranch br n
    let bodyS ← cTerm body { n with u := x :: n.u }
    return [.letMut x none, .join x block] ++ bodyS

/-- The arms of a union's case analysis on `scrut`: each takes the fields apart
    (`const { _1: f₁, _2: f₂ } = scrut;`) and continues. -/
partial def cBranches {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Branches Δ d Φ Γ cs τ js o → Names → JsExpr → ConvM (List (List JsStmt))
  | Branches.two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂, n, scrut => do
    let a₁ ← arm c₁.binds us₁ (fun n' => cTerm b₁ n') n scrut
    let a₂ ← arm c₂.binds us₂ (fun n' => cTerm b₂ n') n scrut
    return [a₁, a₂]
  | Branches.cons (c := c) us b rest, n, scrut => do
    let a ← arm c.binds us (fun n' => cTerm b n') n scrut
    return a :: (← cBranches rest n scrut)
where
  /-- One arm: bind the fields (`const { _1: f, _3: h } = scrut;`), then the body. -/
  arm (tys : List (Ty ks)) (us : List Usage01ω) (k : Names → ConvM (List JsStmt)) (n : Names)
      (scrut : JsExpr) : ConvM (List JsStmt) := do
    if tys.isEmpty then return ← k n
    let (bs, xs) ← fieldBinders tys us
    let body ← k { n with u := xs ++ n.u }
    let binds := fieldBinds bs
    if binds.isEmpty then return body
    return .destructureObj binds scrut :: body

end

end

/-! ## Peephole clean-up -/

mutual
/-- Clean up a block:

* `const x = e; return x;` is `return e;`, and `const x = e; jump j x;` is `jump j e;`;
* a join point whose block only jumps to it, `let x; L: { x = e; break L; }`, is
  `const x = e;`, and one whose block is `if (c) { x = a; break L; } else { x = b; break L; }`
  is `const x = c ? a : b;` (the jumps of index `0` are the jumps to it). -/
partial def peepholeStmts : List JsStmt → List JsStmt
  | [] => []
  | [.const x e, .ret (.var y)] => if x == y then [.ret (peepholeExpr e)]
      else [.const x (peepholeExpr e), .ret (.var y)]
  | [.const x e, .jump j (.var y)] => if x == y then [.jump j (peepholeExpr e)]
      else [.const x (peepholeExpr e), .jump j (.var y)]
  | .letMut x none :: .join x' block :: rest =>
    if x == x' then
      match peepholeStmts block with
      | [.jump 0 e] => peepholeStmts (.const x e :: rest)
      | [.ite c [.jump 0 a] [.jump 0 b]] => peepholeStmts (.const x (.cond c a b) :: rest)
      | block' => .letMut x none :: .join x block' :: peepholeStmts rest
    else .letMut x none :: peepholeStmt (.join x' block) :: peepholeStmts rest
  | s :: ss => peepholeStmt s :: peepholeStmts ss

/-- Clean up the blocks of a statement. -/
partial def peepholeStmt : JsStmt → JsStmt
  | .const x e => .const x (peepholeExpr e)
  | .letMut x e => .letMut x (e.map peepholeExpr)
  | .assign x e => .assign x (peepholeExpr e)
  | .destructure xs e => .destructure xs (peepholeExpr e)
  | .destructureObj xs e => .destructureObj xs (peepholeExpr e)
  | .setMember o m e => .setMember (peepholeExpr o) m (peepholeExpr e)
  | .setAt o i e => .setAt (peepholeExpr o) (peepholeExpr i) (peepholeExpr e)
  | .expr e => .expr (peepholeExpr e)
  | .while c body => .while (peepholeExpr c) (peepholeStmts body)
  | .ret e => .ret (peepholeExpr e)
  | .ite c t e => .ite (peepholeExpr c) (peepholeStmts t) (peepholeStmts e)
  | .forRange i big n body => .forRange i big (peepholeExpr n) (peepholeStmts body)
  | .forOf x xs body => .forOf x (peepholeExpr xs) (peepholeStmts body)
  | .throw k m => .throw k m
  | .join x block => .join x (peepholeStmts block)
  | .jump j e => .jump j (peepholeExpr e)

/-- Clean up the arrows inside an expression. -/
partial def peepholeExpr : JsExpr → JsExpr
  | .arrow ps body => .arrow ps (peepholeStmts body)
  | .bin op a b => .bin op (peepholeExpr a) (peepholeExpr b)
  | .un op a => .un op (peepholeExpr a)
  | .helper n as => .helper n (as.map peepholeExpr)
  | .call f as => .call (peepholeExpr f) (as.map peepholeExpr)
  | .array es => .array (es.map peepholeExpr)
  | .typedArray c es => .typedArray c (es.map peepholeExpr)
  | .index e i => .index (peepholeExpr e) i
  | .member e m => .member (peepholeExpr e) m
  | .cond c a b => .cond (peepholeExpr c) (peepholeExpr a) (peepholeExpr b)
  | .object fs => .object (fs.map fun (k, e) => (k, peepholeExpr e))
  | .at e i => .at (peepholeExpr e) (peepholeExpr i)
  | .new c as => .new (peepholeExpr c) (as.map peepholeExpr)
  | .spread e => .spread (peepholeExpr e)
  | e => e
end

/-! ## Array literals: flattening and inlining

The appends of generic arrays are array literals of spreads (`[...a, ...b]`), so a chain of
appends is nested literals.  Two rewrites turn it into one literal:

* a spread of an array literal is its elements: `[x, ...[y, ...z]]` is `[x, y, ...z]`;
* `const x = [ … ];` used exactly once afterwards, not inside a loop or a closure (where it
  would be evaluated more than once), is inlined into that use.  The elements of such a
  literal (literals, variables, spreads of those) have no effect and cannot fail, so moving
  it is safe as long as none of its variables is reassigned in between.
-/

/-- A literal, a variable, or an array literal of such (spread or not): an expression that
    has no effect, cannot fail and is cheap. -/
partial def JsExpr.isMovable : JsExpr → Bool
  | .var _ | .lit _ => true
  | .array es => es.all JsExpr.isMovable
  | .spread e => e.isMovable
  | _ => false

/-- The variables of a movable expression. -/
partial def JsExpr.movableVars : JsExpr → List String
  | .var x => [x]
  | .array es => es.flatMap JsExpr.movableVars
  | .spread e => e.movableVars
  | _ => []

mutual
/-- Rewrite every expression of a statement bottom-up with `f`. -/
partial def JsStmt.mapE (f : JsExpr → JsExpr) : JsStmt → JsStmt
  | .const x e => .const x (e.mapE f)
  | .letMut x e => .letMut x (e.map (·.mapE f))
  | .assign x e => .assign x (e.mapE f)
  | .destructure xs e => .destructure xs (e.mapE f)
  | .destructureObj xs e => .destructureObj xs (e.mapE f)
  | .setMember o m e => .setMember (o.mapE f) m (e.mapE f)
  | .setAt o i e => .setAt (o.mapE f) (i.mapE f) (e.mapE f)
  | .expr e => .expr (e.mapE f)
  | .while c b => .while (c.mapE f) (b.map (·.mapE f))
  | .ret e => .ret (e.mapE f)
  | .ite c t e => .ite (c.mapE f) (t.map (·.mapE f)) (e.map (·.mapE f))
  | .forRange i big n b => .forRange i big (n.mapE f) (b.map (·.mapE f))
  | .forOf x xs b => .forOf x (xs.mapE f) (b.map (·.mapE f))
  | .throw k m => .throw k m
  | .join x b => .join x (b.map (·.mapE f))
  | .jump j e => .jump j (e.mapE f)
/-- Rewrite an expression bottom-up with `f`. -/
partial def JsExpr.mapE (f : JsExpr → JsExpr) : JsExpr → JsExpr
  | .bin op a b => f (.bin op (a.mapE f) (b.mapE f))
  | .un op a => f (.un op (a.mapE f))
  | .helper n as => f (.helper n (as.map (·.mapE f)))
  | .call g as => f (.call (g.mapE f) (as.map (·.mapE f)))
  | .arrow ps b => f (.arrow ps (b.map (·.mapE f)))
  | .array es => f (.array (es.map (·.mapE f)))
  | .typedArray c es => f (.typedArray c (es.map (·.mapE f)))
  | .index e i => f (.index (e.mapE f) i)
  | .member e m => f (.member (e.mapE f) m)
  | .cond c a b => f (.cond (c.mapE f) (a.mapE f) (b.mapE f))
  | .object fs => f (.object (fs.map fun (k, e) => (k, e.mapE f)))
  | .at e i => f (.at (e.mapE f) (i.mapE f))
  | .new c as => f (.new (c.mapE f) (as.map (·.mapE f)))
  | .spread e => f (.spread (e.mapE f))
  | e => f e
end

/-- One step of flattening: the spreads of array literals inside an array literal are
    replaced by their elements. -/
def flattenStep : JsExpr → JsExpr
  | .array es => .array (es.flatMap fun
      | .spread (.array es') => es'
      | e => [e])
  | e => e

/-- The sum of two counts of mentions (`JsStmt.uses`). -/
def usesAdd (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)

/-- The count of mentions inside a loop or a closure: every one is evaluated again. -/
def usesAgain (a : Nat × Nat) : Nat × Nat := (a.1, a.1)

mutual
/-- How often a statement mentions the variable `x`: all the mentions, and the mentions that
    are evaluated more than once (in the body of a loop, or of a closure). -/
partial def JsStmt.uses (x : String) : JsStmt → Nat × Nat
  | .const _ e | .assign _ e | .destructure _ e | .destructureObj _ e | .ret e | .jump _ e
  | .expr e => e.uses x
  | .letMut _ e => (e.map (·.uses x)).getD (0, 0)
  | .setMember o _ e => usesAdd (o.uses x) (e.uses x)
  | .setAt o i e => usesAdd (usesAdd (o.uses x) (i.uses x)) (e.uses x)
  | .while c b => usesAgain (usesAdd (c.uses x) (usesAll x b))
  | .ite c t e => usesAdd (c.uses x) (usesAdd (usesAll x t) (usesAll x e))
  | .forRange _ _ n b => usesAdd (n.uses x) (usesAgain (usesAll x b))
  | .forOf _ xs b => usesAdd (xs.uses x) (usesAgain (usesAll x b))
  | .throw _ _ => (0, 0)
  | .join _ b => usesAll x b
/-- How often an expression mentions the variable `x` (see `JsStmt.uses`). -/
partial def JsExpr.uses (x : String) : JsExpr → Nat × Nat
  | .var y => if y == x then (1, 0) else (0, 0)
  | .lit _ => (0, 0)
  | .arrow _ b => usesAgain (usesAll x b)
  | .bin _ a b | .at a b => usesAdd (a.uses x) (b.uses x)
  | .un _ a | .index a _ | .member a _ | .spread a => a.uses x
  | .call f as => as.foldl (fun acc a => usesAdd acc (a.uses x)) (f.uses x)
  | .helper _ as | .array as | .typedArray _ as =>
    as.foldl (fun acc a => usesAdd acc (a.uses x)) (0, 0)
  | .new c as => as.foldl (fun acc a => usesAdd acc (a.uses x)) (c.uses x)
  | .cond c a b => usesAdd (c.uses x) (usesAdd (a.uses x) (b.uses x))
  | .object fs => fs.foldl (fun acc (_, e) => usesAdd acc (e.uses x)) (0, 0)
/-- `JsStmt.uses` of a block. -/
partial def usesAll (x : String) (ss : List JsStmt) : Nat × Nat :=
  ss.foldl (fun acc s => usesAdd acc (s.uses x)) (0, 0)
end

/-- Does a statement (re)assign the variable `x`? -/
partial def JsStmt.assigns (x : String) : JsStmt → Bool
  | .assign y _ | .letMut y _ => y == x
  | .join y b => y == x || b.any (·.assigns x)
  | .while _ b | .forRange _ _ _ b | .forOf _ _ b => b.any (·.assigns x)
  | .ite _ t e => t.any (·.assigns x) || e.any (·.assigns x)
  | _ => false

/-- Inline the array literals of a block used once (see above), and flatten. -/
partial def inlineArrays : List JsStmt → List JsStmt
  | [] => []
  | .const x e :: rest =>
    let e := e.mapE flattenStep
    let (all, again) := usesAll x rest
    if (e matches .array _) && e.isMovable && all == 1 && again == 0 &&
        e.movableVars.all (fun y => !rest.any (·.assigns y)) then
      inlineArrays (rest.map (JsStmt.mapE (fun
        | .var y => if y == x then e else .var y
        | e' => flattenStep e')))
    else .const x e :: inlineArrays rest
  | s :: rest => inner s :: inlineArrays rest
where
  /-- Inline inside the blocks of a statement. -/
  inner : JsStmt → JsStmt
    | .while c b => .while c (inlineArrays b)
    | .ite c t e => .ite c (inlineArrays t) (inlineArrays e)
    | .forRange i big n b => .forRange i big n (inlineArrays b)
    | .forOf x xs b => .forOf x xs (inlineArrays b)
    | .join x b => .join x (inlineArrays b)
    | s => s.mapE flattenStep

/-! ## Whole functions -/

section
variable (cfg : JsConfig) (rt : Runtime) {ks : List Nat} {Δ : DSig ks}

mutual
/-- Convert a top-level statement, uncurrying the chain of lambdas at its head: `val k := fun
    x => (val k' := fun y => b; ret k'); ret k` becomes the parameters `x, y` and the body
    `b`, as long as the shape repeats (so `export const f = (x, y) => …` instead of
    `(x) => (y) => …`).  `names` are the preferred names of the parameters (the Lean binder
    names). -/
partial def peelFun {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Term Δ d Φ Γ τ js o → Names → List String → ConvM (List (String × JsTerm) × List JsStmt)
  | t@(.letV _ v (.ret (.kvar k))), n, names =>
    if k.index != 0 then do return ([], ← cTerm cfg rt t n) else
    match v with
    | Val.lam (σ := σ) b => do
      let x ← match names with
        | nm :: _ => pure nm
        | [] => fresh "p"
      let rest := names.drop 1
      let (ps, body) ← peelBody b x n rest
      return ((x, lowerTy cfg σ) :: ps, body)
    | _ => do return ([], ← cTerm cfg rt t n)
  | t, n, _ => do return ([], ← cTerm cfg rt t n)

/-- `peelFun` inside the body of a lambda whose parameter is named `x`. -/
partial def peelBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Body Δ d Φ Γ bs τ o → String → Names → List String →
      ConvM (List (String × JsTerm) × List JsStmt)
  | .closed t', x, n, rest => peelFun t' { u := [x], k := n.k } rest
  | .opened t' _, x, n, rest => peelFun t' { u := [x] ++ n.u, k := n.k } rest
end

/-- The result type after peeling `k` arrows. -/
def peelTy : Nat → JsTerm → JsTerm
  | k + 1, .fn _ b => peelTy k b
  | _, t => t

end

/-- Convert a closed program into an exported JavaScript function named `name`
    (`export const name = (params) => …`), with the runtime functions it calls (those `rt`
    exports).  `paramNames` are the preferred names of its parameters.  The arrays nothing
    else refers to are updated in place (`inPlaceStmts`), when the runtime has the functions
    that do it. -/
def termToJs (cfg : JsConfig) (rt : Runtime) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) : Except String (JsFun × List RtFn) := do
  let ((ps, body), st) ← (peelFun cfg rt ct.term {} paramNames).run {}
  let ret := peelTy ps.length (lowerTy cfg ct.τ)
  let body := peepholeStmts (inlineArrays (peepholeStmts body))
  let inPlaceOk := ["$lean_array_push_inplace", "$lean_array_set_inplace",
    "$lean_array_swap_inplace", "$lean_array_pop_inplace"].all (rt.has .nonConfigurable)
  let body := if inPlaceOk then inPlaceStmts body else body
  -- the runtime functions the body calls now (an in-place version instead of a copying one)
  let called := calledHelpers body
  let imports := st.imports.toList.filter (called.contains ·.name) ++
    (called.filter (·.endsWith "_inplace")).map fun n => { file := .nonConfigurable, name := n }
  return ({ name, leanName, params := ps.map (·.1), paramTys := ps.map (·.2), ret, body },
    imports)

end MoreJs

end
