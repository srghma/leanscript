module

public import JsTerm.Extern
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
| an unknown, a known value (de Bruijn) | a named `const` (`x$1`, `k$2`, …) |
| `PExpr.lit` | a literal at the configured layout (`12n` or `12`); a literal that does not fit in a `number` is refused |
| `record_mk`, `union_mk ix`, `array_mk`, `list_mk` | `[f₀, …]`, `[tag, f₀, …]`, `[e₀, …]` or `Uint8Array.of(…)`, `[e₀, …]` |
| `enum_mk i` | the number `shift + i` |
| `Neu.cond` | `c ? a : b` |
| `Neu.extern` | an operator or a runtime helper (`MoreJs.lowerExtern`) |
| `Val.lam` | `(x) => { … }` |
| `Val.thunk_mk`, `Val.lazy_mk` | `$thunk(() => { … })`, `() => { … }` |
| `Term.ret`, `Term.jump j v` | `return e;`, `return j(v);` |
| `Term.letV`, `Term.letE` | `const k = v;`, `const x = c;` |
| `Term.record_casesOn` | `const [f₀, , f₂] = r;` (unused fields skipped) |
| `Branch.ite`, `enum_casesOn`, `union_casesOn` | `if`/`else if` chains |
| `Branch.join` | `const j = (x) => { … };` in front of the branch |
| `Comp.app f a`, `Comp.share n` | `f(a)`, `n` |
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }`; when the step ignores the accumulator (a case analysis `0` / `k + 1`), `let acc = z; if (0n < n) { const i = n - 1n; …; acc = …; }` |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }` |
| `Comp.thunk_force`, `Comp.lazy_force` | `$force(t)`, `t()` |

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

/-- A float, exactly: `± m * 2 ^ e` read off its IEEE bits. -/
def floatLit (f : Float) : JsLit :=
  let bits : Nat := f.toBits.toNat
  let neg : Bool := (bits / 2 ^ 63) % 2 == 1
  let ex : Nat := (bits / 2 ^ 52) % 2 ^ 11
  let frac : Nat := bits % 2 ^ 52
  if ex == 2047 then
    if frac != 0 then .special "NaN" else .special (if neg then "-Infinity" else "Infinity")
  else
    let (m, e) : Nat × Int := if ex == 0 then (frac, -1074) else (frac + 2 ^ 52, (ex : Int) - 1075)
    let m : Int := if neg then -(m : Int) else m
    if m == 0 then .int 0 else .float m e

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
  | .float, f => pure (.lit (floatLit f.toFloat))
  | .float32, f => pure (.lit (floatLit f.toFloat32.toFloat))
  | .floatModel, _ => throw "a `Float.Model` literal has no JavaScript representation"
  | .float32Model, _ => throw "a `Float32.Model` literal has no JavaScript representation"

/-! ## The conversion -/

/-- The state of the conversion: the counter of fresh names and the helpers used so far. -/
structure ConvState where
  /-- The next fresh name. -/
  next : Nat := 1
  /-- The runtime helpers the program calls, each once, in order of first use. -/
  helpers : Array JsHelper := #[]

/-- The conversion monad. -/
abbrev ConvM := StateT ConvState (Except String)

/-- The JavaScript names of the three contexts of a statement, innermost first. -/
structure Names where
  /-- The unknowns (`Γ`). -/
  u : List String := []
  /-- The known values (`Φ`). -/
  k : List String := []
  /-- The join points (`js`). -/
  j : List String := []
  deriving Inhabited

/-- A fresh JavaScript name. -/
def fresh (pfx : String) : ConvM String :=
  modifyGet fun s => (s!"{pfx}${s.next}", { s with next := s.next + 1 })

/-- Record helpers the program calls (each once). -/
def addHelper (acc : Array JsHelper) (h : JsHelper) : Array JsHelper :=
  if acc.any (fun x => x.name == h.name) then acc else acc.push h

/-- Record helpers the program calls (each once). -/
def useHelpers (hs : List JsHelper) : ConvM Unit :=
  modify fun s => { s with helpers := hs.foldl addHelper s.helpers }

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

mutual
/-- Does a statement build a closure (which could capture a variable the loop reassigns)? -/
partial def JsStmt.hasArrow : JsStmt → Bool
  | .const _ _ e | .letMut _ _ e | .assign _ e | .destructure _ e | .ret e => e.hasArrow
  | .ite c t e => c.hasArrow || t.any JsStmt.hasArrow || e.any JsStmt.hasArrow
  | .forRange _ _ n b => n.hasArrow || b.any JsStmt.hasArrow
  | .forOf _ xs b => xs.hasArrow || b.any JsStmt.hasArrow
  | .throw _ => false
/-- Does an expression build a closure? -/
partial def JsExpr.hasArrow : JsExpr → Bool
  | .arrow .. => true
  | .bin _ a b => a.hasArrow || b.hasArrow
  | .un _ a => a.hasArrow
  | .call f as => f.hasArrow || as.any JsExpr.hasArrow
  | .helper _ as | .array as | .typedArray _ as => as.any JsExpr.hasArrow
  | .index e _ | .member e _ => e.hasArrow
  | .cond c a b => c.hasArrow || a.hasArrow || b.hasArrow
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
    | e => e
  go : JsStmt → JsStmt
    | .const z ty e => .const z ty (goE e)
    | .letMut z ty e => .letMut z ty (goE e)
    | .assign z e => .assign (if z == x then y else z) (goE e)
    | .destructure zs e => .destructure zs (goE e)
    | .ret e => .ret (goE e)
    | .ite c t e => .ite (goE c) (t.map go) (e.map go)
    | .forRange i big n b => .forRange i big (goE n) (b.map go)
    | .forOf z xs b => .forOf z (goE xs) (b.map go)
    | .throw m => .throw m

/-- The body of a loop whose accumulator is the mutable `acc`, the body reading it as
    `accIn`: every `return e` becomes `acc = e`.  When the body builds a closure, `accIn` is
    a `const` copy of `acc` made at the start of the iteration (a closure must capture the
    value of this iteration, not the variable the loop reassigns); otherwise the body reads
    `acc` itself. -/
def loopBody (acc accIn : String) (ty : JsTerm) (body : List JsStmt) : List JsStmt :=
  if body.any JsStmt.hasArrow then
    .const accIn ty (.var acc) :: retToAssign acc body
  else
    retToAssign acc (renameStmts accIn acc body)

mutual
/-- Does a statement mention the variable `x`? -/
partial def JsStmt.mentions (x : String) : JsStmt → Bool
  | .const _ _ e | .letMut _ _ e | .destructure _ e | .ret e => e.mentions x
  | .assign y e => y == x || e.mentions x
  | .ite c t e => c.mentions x || t.any (·.mentions x) || e.any (·.mentions x)
  | .forRange _ _ n b => n.mentions x || b.any (·.mentions x)
  | .forOf _ xs b => xs.mentions x || b.any (·.mentions x)
  | .throw _ => false
/-- Does an expression mention the variable `x`? -/
partial def JsExpr.mentions (x : String) : JsExpr → Bool
  | .var y => y == x
  | .arrow _ b => b.any (·.mentions x)
  | .bin _ a b => a.mentions x || b.mentions x
  | .un _ a => a.mentions x
  | .call f as => f.mentions x || as.any (·.mentions x)
  | .helper _ as | .array as | .typedArray _ as => as.any (·.mentions x)
  | .index e _ | .member e _ => e.mentions x
  | .cond c a b => c.mentions x || a.mentions x || b.mentions x
  | .lit _ => false
end

/-- An expression that can be repeated without recomputing anything. -/
def JsExpr.isAtom : JsExpr → Bool
  | .var _ | .lit _ => true
  | _ => false

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
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

/-- Names for the fields a pattern binds, `none` for the ones annotated unused. -/
def fieldBinders (tys : List (Ty ks)) (us : List Usage01ω) :
    ConvM (List (Option (String × JsTerm)) × List String) := do
  let mut bs := #[]
  let mut names := #[]
  for i in [0:tys.length] do
    let x ← fresh "f"
    names := names.push x
    let used := match us[i]? with
      | some .zero => false
      | _ => true
    bs := bs.push (if used then some (x, lowerTy cfg tys[i]!) else none)
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
    let (ex, hs) := lowerExtern (externName e) (σs.map (lowerTy cfg)) (lowerTy cfg τ) as
    useHelpers hs
    return ex

/-- A pure expression. -/
partial def cPExpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl} :
    PExpr Δ Φ Γ τ o → Names → ConvM JsExpr
  | .neu e, n => cNeu e n
  | .kvar k, n => pure (.var (n.k.getD k.index "undefined$"))
  | .lit p v, _ => liftExcept (primLit cfg p v)
  | .enum_mk s i, _ => pure (.lit (.int (s.shift + i.val)))
  | .record_mk args, n => return .array (← cArgs args n)
  | .union_mk ix args, n => return .array (.lit (.int (ctorIxIndex ix)) :: (← cArgs args n))
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
    useHelpers [thunkHelper]
    return .helper "$thunk" [.arrow [] (← cBody b n [])]
  | .lazy_mk b, n => return .arrow [] (← cBody b n [])
  | .record_mk args, n => return .array (← cArgs args n)
  | .union_mk ix args, n => return .array (.lit (.int (ctorIxIndex ix)) :: (← cArgs args n))
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
  | .closed t, n, xs => cTerm t { u := xs, k := n.k, j := [] }
  | .opened t _, n, xs => cTerm t { u := xs ++ n.u, k := n.k, j := [] }

/-- A computation whose result is named `x`: the statements that compute it, and the name
    it can be referred to by. -/
partial def cComp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat} :
    Comp Δ d Φ Γ τ ℓ → Names → ConvM (List JsStmt × String)
  | .app f a _, n => do
    let x ← fresh "x"
    return ([.const x (lowerTy cfg τ) (.call (← cPExpr f n) [← cPExpr a n])], x)
  | .share e, n => do
    let x ← fresh "x"
    return ([.const x (lowerTy cfg τ) (← cNeu e n)], x)
  | .nat_rec cnt z s _, n => do
    let acc ← fresh "acc"
    let i ← fresh "i"
    let cntE ← cPExpr cnt n
    let (pre, cntE) ← if cntE.isAtom then pure ([], cntE) else do
      let c ← fresh "n"
      pure ([JsStmt.const c (lowerTy cfg (Ty.nat : Ty ks)) cntE], JsExpr.var c)
    let zE ← cPExpr z n
    let accIn ← fresh "a"
    let body ← cBody s n [accIn, i]
    let big := (lowerTy cfg (Ty.nat : Ty ks)).isBigInt
    if body.any (·.mentions accIn) then
      return (pre ++ [.letMut acc (lowerTy cfg τ) zE,
        .forRange i big cntE (loopBody acc accIn (lowerTy cfg τ) body)], acc)
    else
      -- a step that ignores the accumulator (a case analysis `0` / `k + 1` read as a
      -- recursion): only the last iteration counts, `i = n - 1`, so no loop
      let lit (k : Nat) : JsExpr := .lit (if big then .bigint k else .int k)
      return (pre ++ [.letMut acc (lowerTy cfg τ) zE,
        .ite (.bin .lt (lit 0) cntE)
          (.const i (lowerTy cfg (Ty.nat : Ty ks)) (.bin .sub cntE (lit 1)) :: retToAssign acc body)
          []], acc)
  | .array_foldl arr z s _, n => do
    let acc ← fresh "acc"
    let e ← fresh "e"
    let arrE ← cPExpr arr n
    let zE ← cPExpr z n
    let accIn ← fresh "a"
    let body ← cBody s n [e, accIn]
    return ([.letMut acc (lowerTy cfg τ) zE,
      .forOf e arrE (loopBody acc accIn (lowerTy cfg τ) body)], acc)
  | .data_rec _ _ _ _ _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"
  | .data_brec _ _ _ _ _ _ _ _, _ => throw "the recursors of declared datatypes are not converted to JavaScript yet"
  | .thunk_force p, n => do
    let x ← fresh "x"
    useHelpers [forceHelper]
    return ([.const x (lowerTy cfg τ) (.helper "$force" [← cPExpr p n])], x)
  | .lazy_force p, n => do
    let x ← fresh "x"
    return ([.const x (lowerTy cfg τ) (.call (← cPExpr p n) [])], x)

/-- A statement: JavaScript statements every path of which ends in a `return`. -/
partial def cTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Term Δ d Φ Γ τ js o → Names → ConvM (List JsStmt)
  | .ret p, n => return [.ret (← cPExpr p n)]
  | Term.letV (σ := σ) _ v t, n => do
    let k ← fresh "k"
    let ve ← cVal v n
    return .const k (lowerTy cfg σ) ve :: (← cTerm t { n with k := k :: n.k })
  | .letE _ c t, n => do
    let (ss, x) ← cComp c n
    return ss ++ (← cTerm t { n with u := x :: n.u })
  | Term.record_casesOn (t := tt) (fs := fs) us e t, n => do
    let (bs, xs) ← fieldBinders cfg (tt :: fs.toList) us
    let ee ← cNeu e n
    return .destructure bs ee :: (← cTerm t { n with u := xs ++ n.u })
  | .branch b, n => cBranch b n
  | .jump j p, n => return [.ret (.call (.var (n.j.getD j.index "undefined$")) [← cPExpr p n])]

/-- A branch in tail position. -/
partial def cBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat} :
    Branch Δ d Φ Γ τ js ℓ → Names → ConvM (List JsStmt)
  | .ite c t e, n => return [.ite (← cNeu c n) (← cTerm t n) (← cTerm e n)]
  | Branch.enum_casesOn (s := s) c bs, n => do
    let ce ← cNeu c n
    let (pre, ce) ← if ce.isAtom then pure ([], ce) else do
      let x ← fresh "s"
      pure ([JsStmt.const x (.enum s.nOfConstructors s.shift) ce], JsExpr.var x)
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
      pure ([JsStmt.const x (lowerTy cfg (Ty.union cs : Ty ks)) ee], JsExpr.var x)
    let arms ← cBranches brs n ee
    let k := arms.length
    let mut out : List JsStmt := []
    for (i, body) in ((List.range k).zip arms).reverse do
      if i == k - 1 then out := body
      else out := [.ite (.bin .strictEq (.index ee 0) (.lit (.int i))) body out]
    let _ := ctorsBinds cs
    return pre ++ out
  | Branch.join σ _ _ body br, n => do
    let j ← fresh "j"
    let x ← fresh "x"
    let bodyS ← cTerm body { n with u := x :: n.u }
    let rest ← cBranch br { n with j := j :: n.j }
    return .const j (.fn (lowerTy cfg σ) (lowerTy cfg τ)) (.arrow [x] bodyS) :: rest

/-- The arms of a union's case analysis on `scrut`: each takes the fields apart
    (`const [, f₀, f₁] = scrut;`) and continues. -/
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
  /-- One arm: bind the fields, then the body. -/
  arm (tys : List (Ty ks)) (us : List Usage01ω) (k : Names → ConvM (List JsStmt)) (n : Names)
      (scrut : JsExpr) : ConvM (List JsStmt) := do
    if tys.isEmpty then return ← k n
    let (bs, xs) ← fieldBinders cfg tys us
    let body ← k { n with u := xs ++ n.u }
    if bs.all Option.isNone then return body
    return .destructure (none :: bs) scrut :: body

end

end

/-! ## Peephole clean-up -/

mutual
/-- `const x = e; return x;` is `return e;`, inside every block. -/
partial def peepholeStmts : List JsStmt → List JsStmt
  | [] => []
  | [.const x ty e, .ret (.var y)] => if x == y then [.ret (peepholeExpr e)]
      else [.const x ty (peepholeExpr e), .ret (.var y)]
  | s :: ss => peepholeStmt s :: peepholeStmts ss

/-- Clean up the blocks of a statement. -/
partial def peepholeStmt : JsStmt → JsStmt
  | .const x ty e => .const x ty (peepholeExpr e)
  | .letMut x ty e => .letMut x ty (peepholeExpr e)
  | .assign x e => .assign x (peepholeExpr e)
  | .destructure xs e => .destructure xs (peepholeExpr e)
  | .ret e => .ret (peepholeExpr e)
  | .ite c t e => .ite (peepholeExpr c) (peepholeStmts t) (peepholeStmts e)
  | .forRange i big n body => .forRange i big (peepholeExpr n) (peepholeStmts body)
  | .forOf x xs body => .forOf x (peepholeExpr xs) (peepholeStmts body)
  | .throw m => .throw m

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
  | e => e
end

/-! ## Whole functions -/

section
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

mutual
/-- Convert a top-level statement, uncurrying the lambdas at its head: `val k := fun x => b;
    ret k` becomes a parameter `x` and the body `b`, as long as the shape repeats.  `names`
    are the preferred names of the parameters (the Lean binder names). -/
partial def peelFun {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl} :
    Term Δ d Φ Γ τ js o → Names → List String → ConvM (List (String × JsTerm) × List JsStmt)
  | t@(.letV _ v (.ret (.kvar k))), n, names =>
    if k.index != 0 then do return ([], ← cTerm cfg t n) else
    match v with
    | Val.lam (σ := σ) b => do
      let x ← match names with
        | nm :: _ => pure nm
        | [] => fresh "p"
      let rest := names.drop 1
      let (ps, body) ← peelBody b x n rest
      return ((x, lowerTy cfg σ) :: ps, body)
    | _ => do return ([], ← cTerm cfg t n)
  | t, n, _ => do return ([], ← cTerm cfg t n)

/-- `peelFun` inside the body of a lambda whose parameter is named `x`. -/
partial def peelBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl} :
    Body Δ d Φ Γ bs τ o → String → Names → List String →
      ConvM (List (String × JsTerm) × List JsStmt)
  | .closed t', x, n, rest => peelFun t' { u := [x], k := n.k, j := [] } rest
  | .opened t' _, x, n, rest => peelFun t' { u := [x] ++ n.u, k := n.k, j := [] } rest
end

/-- The result type after peeling `k` arrows. -/
def peelTy : Nat → JsTerm → JsTerm
  | k + 1, .fn _ b => peelTy k b
  | _, t => t

end

/-- Convert a closed program into an exported JavaScript function named `name`, with the
    runtime helpers it needs.  `paramNames` are the preferred names of its parameters. -/
def termToJs (cfg : JsConfig) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) : Except String (JsFun × List JsHelper) := do
  let ((ps, body), st) ← (peelFun cfg ct.term {} paramNames).run {}
  let ret := peelTy ps.length (lowerTy cfg ct.τ)
  return ({ name, leanName, params := ps, ret, body := peepholeStmts body }, st.helpers.toList)

end MoreJs

end
