module

public import JsTerm.Lower.DataRec

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
| `record_mk`, `union_mk ix`, `array_mk`, `list_mk` | `{ _1: f₁, … }`, `{ tag: ix, _1: f₁, … }`, `[e₀, …]` or `Uint8Array.of(…)`, `[e₀, …]` (`listRepr = stdListToJsArray`) or `{ tag: 1, _1: e₀, _2: … { tag: 0 } }` (`listRepr = taggedUnion`) |
| `enum_mk i` | the number `shift + i` |
| `Neu.cond` | `c ? a : b` |
| `Neu.extern` | the operation of the extern at these types (`MoreJs.lowerExtern`) |
| `Val.lam` | `(x, y) => { … }`, of all the parameters of its type (uncurried) |
| `Val.thunk_mk`, `Val.lazy_mk` | `thunk__lean_mk_thunk(() => { … })`, `() => { … }` |
| `Term.ret`, `Term.jump j v` | `return e;`, a jump to the join point `j` |
| `Term.letV`, `Term.letE` | `const k = v;`, `const x = c;` |
| `Term.record_casesOn` | `const { _1: f₁, _3: f₃ } = r;` (unused fields skipped) |
| `Branch.ite`, `enum_casesOn`, `union_casesOn` | `if`/`else`, and case analyses |
| `Branch.join` | a join point (`JsBlock.join`) |
| `Comp.app f a`, `Comp.share n` | `f(a, b)` once every parameter is passed (a partial application is a closure), `n` |
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }` |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }`; a fold pushing every element (`Array.append z a`) on generic arrays is `[...z, ...a]` |
| `Comp.thunk_force`, `Comp.lazy_force` | `thunk__lean_thunk_get_own(t)`, `t()` |
| `PExpr.data_in`, `Neu.data_out` | the value itself (`JsExpr.fold`, `JsExpr.unfold`) |
| `Comp.data_rec` | `const go0 = (v) => { …; return branch₀; }; …; const x = go_j(e);` |

An extern with no operation at the types of a call is an error of the conversion
(`lowerExtern`).

A literal of an unbounded type at a `number` representation (a `Nat` as a `uint53`) that does
not fit in a safe integer is an error of the conversion: `leanscript` reports it and exits.

## Functions are uncurried

The layout of a Lean arrow `A → B → C` is the JavaScript function of two parameters
(`lowerTy`: `JsTy.fn [A, B] C`), wherever it appears: an exported function, a closure, a
parameter or a field of function type.  So:

* a lambda takes **all** the parameters of its type at once: the chain `fun x => (val k :=
  fun y => b; ret k)` is `(x, y) => b`; when the body of a lambda is not the next lambda of the
  chain (it computes the function first), it is applied to the remaining parameters
  (`(x, y) => { …; const f = …; return f(y); }`) — the parameters are passed later than the
  Lean code passes them, which changes nothing, since the conversion of a computation never has
  an effect but a throw;
* a call passes all the parameters at once.  A call of fewer (`let g := f a; let r := g b`)
  is not a call yet: the conversion remembers the function and the arguments passed so far
  (`Ref.pap`, all of them constants), and the call `f(a, b)` happens once the last parameter
  is passed; a partial application used as a value (passed, returned, stored) is the closure
  `(y) => f(a, y)`;
* the exported function takes all the parameters of its type, named by the Lean binders.

## Declared datatypes

A value of a declared datatype has the type `obj (decl i) []` (its stable number, `refIndex`):
`data_in` and `data_out` are the casts `JsExpr.fold` and `JsExpr.unfold` (nothing at run time).
The fold `data_rec` (and the course-of-values fold `data_brec` at depth `0`, the same fold) is
one local function per member of the block, mutually recursive (`JsBlock.funs`), each mapping
one layer and running the member's branch on it (`JsTerm.Lower.DataRec`).  A course-of-values
fold of depth `1` or more is not converted yet: a term using one is refused with an error.

The literals, the conversion monad and the builders of the shapes are in `JsTerm.Lower.Basic`.
-/

namespace MoreJs

variable {S : JsSig}

open LeanScript

/-- The constant of the version of the local function `fi` a call giving up the arguments `off`
    calls (`Own.FnOwn.chosen`), when it is generated. -/
def fnVersionRef? (n : Names) (fi : Own.FnOwn) (off : List Bool) : Option Ref :=
  match (n.fns.lookup fi.id).bind (·[(fi.chosen off).1]?) with
  | some r@(.c _) => some r
  | _ => none

/-- The values of `Ref`s as arguments, those `copies` says copied (`[...a]`). -/
def refArgsCopy {C M : List JsTy} :
    (as : List (Ref × JsTy)) → List Bool → ConvM (JsArgs S C M (as.map (·.2)))
  | [], _ => pure .nil
  | (r, t) :: as, cs => do
    let e ← r.get t
    let e ← if cs.headD false then
        match e.copyArray? with
        | some e' => pure e'
        | none => throw "internal: a copy of an argument that is not an array"
      else pure e
    return .cons e (← refArgsCopy as cs.tail)

/-- The change of the environment of the body of a loop whose accumulator (the parameter `idx`)
    is an owning closure (`Own.AccMode.ownFn`, `Own.Env.withAccFn`). -/
def accEnv {ks : List Nat} (mode : Own.AccMode) (idx fid : Nat) (ρ : Ty ks) : Own.Env → Own.Env :=
  match mode with
  | .ownFn m r => Own.Env.withAccFn idx (Own.mustFn fid ρ m r) m r
  | _ => fun e => e

section
variable (cfg : JsConfig) {ks : List Nat} {Δ : DSig ks}

/-- The operands of a chain of `List.append`s (`lean_list_append`), whatever its nesting, in
    order: `(a ++ b) ++ (c ++ d)` has the operands `a, b, c, d`. -/
partial def listAppendLeaves {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {o : Lvl} →
    PExpr Δ Φ Γ τ o → List ((τ' : Ty ks) × (o' : Lvl) × PExpr Δ Φ Γ τ' o')
  | _, _, p@(.neu (Neu.extern e (.cons a (.cons b .nil)) _)) =>
    if externName e == "lean_list_append" then listAppendLeaves a ++ listAppendLeaves b
    else [⟨_, _, p⟩]
  | _, _, p => [⟨_, _, p⟩]

mutual

/-- A neutral expression. -/
partial def cNeu {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (e : Neu Δ Φ Γ τ ℓ) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .var x => (n.u.getD x.index .none).get _
  | Neu.data_out b j e => do unfoldE (← cNeu e n C M) (lowerTy cfg ((Δ.block b).unfold j))
  | .cond c a b => do
    let ce ← castE (← cNeu c n C M) (.terminal .bool)
    return .cond ce (← cPExpr a n C M) (← cPExpr b n C M)
  | Neu.extern (σs := σs) (τ := τ) e args h => do
    let nm := externName e
    -- `l ++ l'` on cons cells: the whole chain of appends, built from its end (`cConsAppend`)
    if nm == "lean_list_append" && (lowerTy cfg τ).isConsList then
      return ← cConsAppend (listAppendLeaves (.neu (Neu.extern e args h))) n C M _
    let as ← cArgs args n C M
    let r ← match stringPosArg? σs with
      | some s => lowerExtern nm (.cons (.lit (.string s)) as)
      | none => lowerExtern nm as
    -- an update of an array nothing else refers to is done in place; `set!` and
    -- `swapIfInBounds` otherwise update a copy in place (their answer is then always new).
    -- An append onto an array literal is better written as one literal (below).
    if Own.updateInPlace n.cx nm args && !(nm == "lean_array_append" && as.firstIsArrayLit) then
      return r.inPlace
    else if Own.copyThenUpdate nm then
      match r.updateOnCopy? with
      | some r' => return r'
      | none => throw s!"internal: the update {nm} on a copy"
    -- `a ++ b` on arrays (and on lists at the array layout) is the literal `[...a, ...b]`, in
    -- which the literal operands, and the appends already written as literals, are spliced
    else if nm == "lean_array_append" || nm == "lean_list_append" then
      return (← appendLit? as).getD r
    else return r

/-- A chain of appends of lists of cons cells (`ListRepr.taggedUnion`), given by its operands
    (`listAppendLeaves`), at the type `L`: built from its end, so that the last operand is shared,
    not copied, a literal operand is its cells put in front of the rest
    (`{ tag: 1, _1: "a", _2: rest }`), and any other operand is copied in front of the rest
    (`consList__lean_list_append(xs, rest)`).  `(a ++ b) ++ c` is written `a ++ (b ++ c)`, which
    copies the cells of `a` once instead of twice (`List.append` is associative). -/
partial def cConsAppend {Φ : KCtx ks} {Γ : UCtx ks}
    (leaves : List ((τ' : Ty ks) × (o' : Lvl) × PExpr Δ Φ Γ τ' o')) (n : Names)
    (C M : List JsTy) (L : JsTy) : ConvM (JsExpr S C M L) := do
  match L with
  | .obj .consList [α] =>
    match leaves.reverse with
    | [] => throw "internal: an append of no list"
    | ⟨_, _, last⟩ :: before =>
      let mut acc : JsExpr S C M (.consList α) ← castE (← cPExpr last n C M) _
      for ⟨_, _, leaf⟩ in before do
        let whole : ConvM (JsExpr S C M (.consList α)) := do
          let e ← castE (← cPExpr leaf n C M) (.consList α)
          lowerExtern "lean_list_append" (.cons e (.cons acc .nil))
        acc ← match ← cConsLitFront? leaf n C M α acc with
          | some r => pure r
          | none => whole
      castE acc L
  | L => throw s!"internal: an append of lists of type {L}"

/-- A list literal put in front of `rest` as its cells (`{ tag: 1, _1: e₀, _2: rest }`); `none`
    when the expression is not a list literal of plain elements. -/
partial def cConsLitFront? {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) (α : JsTy)
    (rest : JsExpr S C M (.consList α)) : ConvM (Option (JsExpr S C M (.consList α))) :=
  match e with
  | PExpr.list_mk (t := t) es => do
    let ps : JsParts S C M (.list (lowerTy cfg t)) (lowerTy cfg t) ← cElems es n C M
    match ps.elems? with
    | some xs => do
      let xs ← xs.mapM (castE · α)
      pure (some (xs.foldr JsExpr.consCons rest))
    | none => pure none
  | _ => pure none

/-- A pure expression. -/
partial def cPExpr {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .neu e => cNeu e n C M
  | .kvar k => (n.k.getD k.index .none).get _
  | .lit p v => do
    let ⟨_, l⟩ ← primLit cfg p v
    castE (.lit l) _
  | .enum_mk s i => pure (.enum_mk s.nOfConstructors s.shift i)
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | PExpr.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | PExpr.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
  | PExpr.data_in b j e => do
    foldE (← cPExpr e n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))

/-- A pure expression whose value is made owned by copying arrays (`Own.PExpr.copyable`): its
    owned parts as they are, each other array copied (`[...a]`). -/
partial def cPExprOwned {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (n : Names) (C M : List JsTy) : ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  if Own.PExpr.owned n.cx e then cPExpr e n C M else
  match e with
  | .record_mk args => do recordLit (← cArgsOwned args n C M) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgsOwned args n C M)
  | PExpr.data_in b j e => do
    foldE (← cPExprOwned e n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))
  | e => do
    match (← cPExpr e n C M).copyArray? with
    | some c => pure c
    | none => throw "internal: a copy of a value that is not an array"

/-- `cPExprOwned` of arguments. -/
partial def cArgsOwned {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M : List JsTy) :
    ConvM (JsArgs S C M (σs.map (lowerTy cfg))) :=
  match as with
  | .nil => pure .nil
  | .cons a as => return .cons (← cPExprOwned a n C M) (← cArgsOwned as n C M)

/-- Arguments. -/
partial def cArgs {Φ : KCtx ks} {Γ : UCtx ks} {σs : List (Ty ks)} {o : Lvl}
    (as : Args Δ Φ Γ σs o) (n : Names) (C M : List JsTy) :
    ConvM (JsArgs S C M (σs.map (lowerTy cfg))) :=
  match as with
  | .nil => pure .nil
  | .cons a as => return .cons (← cPExpr a n C M) (← cArgs as n C M)

/-- Elements of an array or list literal of type `A`. -/
partial def cElems {Φ : KCtx ks} {Γ : UCtx ks} {t : Ty ks} {o : Lvl} {A : JsTy}
    (es : Elems Δ Φ Γ t o) (n : Names) (C M : List JsTy) :
    ConvM (JsParts S C M A (lowerTy cfg t)) :=
  match es with
  | .nil => pure .nil
  | .cons a as => return .elem (← cPExpr a n C M) (← cElems as n C M)

/-- A constructor of a union: `{ tag: i, _1: … }`. -/
partial def unionLit {C M : List JsTy} {bs : List Bool} {b : Bool} [UnionShape bs]
    (cs : Ctors ks bs) (c : Ctor ks b) (ix : CtorIx cs c) {σs : List JsTy} (as : JsArgs S C M σs) :
    ConvM (JsExpr S C M (lowerTy cfg (Ty.union (d := true) cs))) :=
  unionMk _ (ctorIxIndex ix) as

/-- An array literal: `[e₀, …]`, or `Uint8Array.of(…)` for a typed array. -/
partial def arrayLit {C M : List JsTy} (t : Ty ks)
    (ps : JsParts S C M (lowerTy cfg (Ty.array (d := true) t)) (lowerTy cfg t)) :
    ConvM (JsExpr S C M (lowerTy cfg (Ty.array (d := true) t))) := do
  let A' := lowerTy cfg (Ty.array (d := true) t)
  match JsArrayLayout.of? A' with
  | some ⟨E, l⟩ =>
    return .array_mk l (← castParts ps E)
  | none => throw "internal: the layout of an array"

/-- A value of known shape. -/
partial def cVal {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (v : Val Δ d Φ Γ τ o) (n : Names) (C M : List JsTy) (fl : List Bool := []) :
    ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match v with
  | Val.lam (σ := σ) (τ := ρ) b => do
    match lowerTy cfg (Ty.fn (d := true) σ ρ) with
    | .fn (d₀ :: ds) c =>
      -- all the parameters of the type at once
      let ps := paramRefs C (d₀ :: ds)
      -- a closure owns the parameters `fl` says (a version of a local function, `Own.lamPlan`)
      -- and borrows the others; nothing from outside is owned in it (it may run later, or many
      -- times)
      let body ← cApplyBody b { n with own := n.own.none } (pushAll (d₀ :: ds) C) M
        (ps.map (·.1)) (ps.zipIdx.map fun (_, i) => fl.getD i false) c
      castE (.lam ((d₀ :: ds).map fun _ => "x") body) _
    | _ => throw "internal: the type of a lambda"
  | Val.thunk_mk (τ := t) b => do
    let body ← cBody b n C M [] []
    let lz : JsExpr S C M (.fn [] (lowerTy cfg t.relax)) := .lam (σs := []) [] body
    lowerExtern "lean_mk_thunk" (.cons lz .nil)
  | Val.lazy_mk b => do castE (.lam (σs := []) [] (← cBody b n C M [] [])) _
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | Val.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | Val.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | Val.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
  | Val.data_in b j e => do
    foldE (← cPExpr e n C M) (lowerTy cfg (Ty.data (d := true) ((Δ.block b).ref j)))

/-- A statement that answers a function, applied to the parameters `ps` (bound in `C`, the
    first one outermost), answering a value of type `r`: the chain of lambdas `val k := fun x =>
    …; ret k` takes the parameters one after the other; any other statement computes the
    function (a block computing it into a join point), which is then called on the parameters
    left (`f(y)`).  `fl` says which of the parameters are owned (`Own.Term.walkApplied`). -/
partial def cApplyTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ [] o) (n : Names) (C M : List JsTy) (ps : List Ref) (fl : List Bool)
    (r : JsTy) :
    ConvM (JsBlock S C M [] (.ret r)) :=
  let whole : ConvM (JsBlock S C M [] (.ret r)) := do
    let blk ← cTerm t n C M []
    if h : lowerTy cfg τ = r then return h ▸ blk else
    match lowerTy cfg τ with
    | .fn ds c =>
      if ds.length != ps.length then throw "internal: the parameters of a function" else
      let call ← papCall (.c C.length) ((ps.zip ds).map fun (p, t) => (p, t)) c
        (C := lowerTy cfg τ :: C) (M := M)
      castRet ((JsBlock.join "f" ((blk.retToJump (k := .ret c)))
        ((JsBlock.ret call)))) r
    | _ => throw "internal: applying a value that is not a function"
  if ps.isEmpty then whole else
  match t with
  | .letV _ v (.ret (.kvar k)) =>
    if k.index != 0 then whole else
    match v with
    | Val.lam b => cApplyBody b n C M ps fl r
    | _ => whole
  | _ => whole

/-- The body of a lambda applied to the parameters `ps` (its own parameter first), owned or not
    (`fl`). -/
partial def cApplyBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (ps : List Ref) (fl : List Bool)
    (r : JsTy) : ConvM (JsBlock S C M [] (.ret r)) :=
  match ps with
  | [] => throw "internal: a lambda without a parameter"
  | p :: ps' =>
    let f := fl.headD false
    match b with
    | .closed t =>
      cApplyTerm t { n with u := [p], own := n.own.closedBody [f] } C M ps' fl.tail r
    | .opened t _ =>
      cApplyTerm t { n with u := p :: n.u, own := n.own.pushU [f] } C M ps' fl.tail r

/-- The body of a closure, a delay or a loop, whose parameters live at `xs` (innermost first;
    `C` already holds them) and are owned or not (`fl`; nothing from outside is owned in the
    body): a block ending in `return`. -/
partial def cBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (xs : List Ref) (fl : List Bool)
    (mod : Own.Env → Own.Env := id) : ConvM (JsBlock S C M [] (.ret (lowerTy cfg τ))) :=
  match b with
  | .closed t => cTerm t { n with u := xs, own := mod (n.own.body true fl) } C M []
  | .opened t _ => cTerm t { n with u := xs ++ n.u, own := mod (n.own.body false fl) } C M []

/-- The initial value of a loop whose accumulator is an owning closure owning `m`
    (`Own.AccMode.ownFn`): a local function is given by its version owning the most of `m`. -/
partial def cPExprFn {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (e : PExpr Δ Φ Γ τ o) (m : List Bool) (n : Names) (C M : List JsTy) :
    ConvM (JsExpr S C M (lowerTy cfg τ)) :=
  match e with
  | .kvar x => match n.own.kf.getD x.index none with
    | some fi => match fnVersionRef? n fi m with
      | some r => r.get _
      | none => cPExpr e n C M
    | none => cPExpr e n C M
  | e => cPExpr e n C M

/-- A computation, followed by the block `k` builds from where its result lives. -/
partial def cComp {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (c : Comp Δ d Φ Γ τ ℓ) (n : Names) (C M J : List JsTy) {e : JsEnd}
    (k : Ref → (C' M' : List JsTy) → ConvM (JsBlock S C' M' J e)) : ConvM (JsBlock S C M J e) :=
  match c with
  | Comp.app (σ := σ) (τ := τ) f a _ => do
    -- the function, as a constant (or the partial application it is)
    let withF (rest : Ref → (C' : List JsTy) → ConvM (JsBlock S C' M J e)) :
        ConvM (JsBlock S C M J e) := do
      match pexprRef? f n with
      | some r@(.c _) | some r@(.pap ..) | some r@.none => rest r C
      | _ => return (← bindConst (← cPExpr f n C M) rest)
    withF fun fr C₁ => do
      return (← bindConst (← cPExpr a n C₁ M) fun ar C₂ => do
        let (base, args) := match fr with
          | .pap b as => (b, as)
          | r => (r, [])
        let args := args ++ [(ar, lowerTy cfg σ)]
        if τ.isFn then
          -- a partial application: the call waits for the other parameters
          k (.pap base args) C₂ M
        else
          -- a local function with versions: the version owning the most arguments the caller
          -- gives up (`Own.FnOwn.choose`, as `Own.Comp.cost` decides it)
          let (base, copies) := match Own.appOffer n.cx f a with
            | some (fi, off) =>
              ((fnVersionRef? n fi off).getD base, fi.copyMask off)
            | none => (base, [])
          -- an owning closure copies the arguments it owns that the caller keeps
          let call : JsExpr S C₂ M (lowerTy cfg τ) :=
            .app (← base.get (.fn (args.map (·.2)) (lowerTy cfg τ))) (← refArgsCopy args copies)
          return (JsBlock.const "x" call (← k (.c C₂.length) _ M)))
  | .share e => do
    let ee ← cNeu e n C M
    return (JsBlock.const "x" ee (← k (.c C.length) _ M))
  | Comp.nat_rec (τ := ρ) cnt z s _ => do
    let N := lowerTy cfg (Ty.nat : Ty ks)
    let some nt := JsNatTy.of? N | throw "internal: the representation of a Nat"
    let α := lowerTy cfg ρ
    let cntE ← cPExpr cnt n C M
    -- the body owns its accumulator when every iteration hands the next an owned value (the
    -- initial value copied first if it is not owned, when that saves copies in the body)
    let mode := Own.natRecAcc n.cx z s n.allowFn
    let zE ← match mode with
      | .copy => cPExprOwned z n C M
      | .ownFn m _ => cPExprFn z m n C M
      | _ => cPExpr z n C M
    let accLvl := M.length
    let M' := α :: M
    let acc : JsMem M' α := .zero
    -- the body: the counter, then the accumulator it reads
    let body ← cBody s n (α :: N :: C) M' [.c (C.length + 1), .c C.length] [mode.owns, false]
      (accEnv mode 0 (Own.accFnId d n.cx.env) ρ)
    let rest ← k (.m accLvl) C M'
    return JsBlock.letMut "acc" zE (JsBlock.forRange "i" nt cntE.wkM (loopBody acc body) rest)
  | Comp.array_foldl (t := t) (ρ := ρ) arr z s _ => do
    let A := lowerTy cfg (Ty.array (d := true) t)
    let α := lowerTy cfg ρ
    let arrE ← cPExpr arr n C M
    let mode := Own.foldlAcc n.cx z s n.allowFn
    let zE ← match mode with
      | .copy => cPExprOwned z n C M
      | .ownFn m _ => cPExprFn z m n C M
      | _ => cPExpr z n C M
    let some ⟨E, l⟩ := JsArrayLayout.of? A | throw "internal: the layout of an array"
    let M' := α :: M
    let body ← cBody s n (α :: lowerTy cfg t :: C) M' [.c C.length, .c (C.length + 1)]
      [false, mode.owns] (accEnv mode 1 (Own.accFnId d n.cx.env) ρ)
    let body ← castBodyElem body E
    let rest ← k (.m M.length) C M'
    return (JsBlock.letMut "acc" zE
      ((JsBlock.forOf "e" l arrE.wkM ((loopBody .zero body)) rest)))
  | Comp.data_rec (b := b) ρ _ branches j e _ =>
    let B := Δ.block b
    -- the answers at the holes of a layer are owned when every branch answers an owned value
    let f := if Own.dataRecOwns n.cx b ρ branches then Own.Env.withHoles (Own.recHoles b ρ)
      else fun e => e
    dataFold B ρ (fun i => Ty.pair (.data (B.ref i)) (ρ i))
      (fun i x C' => cBody (branches i) n C' M [x] [false] f) j e
  | Comp.data_brec (b := b) ρ 0 _ branches j e _ =>
    -- depth `0`: the windows are the pairs of `data_rec`
    let B := Δ.block b
    dataFold B ρ (fun i => B.win ρ 0 i) (fun i x C' => cBody (branches i) n C' M [x] [false]) j e
  | .data_brec _ _ (_ + 1) _ _ _ _ _ => notYet
  | Comp.thunk_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e : JsExpr S C M (lowerTy cfg t.relax) ← lowerExtern "lean_thunk_get_own" (.cons pe .nil)
    return (JsBlock.const "x" e (← k (.c C.length) _ M))
  | Comp.lazy_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e ← forceLazy pe (lowerTy cfg t.relax)
    return (JsBlock.const "x" e (← k (.c C.length) _ M))
where
  /-- The fold over the block `B` answering `ρ`, whose branch `i` (`branch i`) runs on the layer
      of member `i` with every hole `i'` filled by `σt i'`, applied to `e`, a value of member
      `j` (`recFuns`): `const go0 = (v) => …; …; const x = go_j(e);` and the rest. -/
  dataFold {oe : Lvl} (B : Δ.Block) (ρ : Fin (B.k + 1) → Ty ks) (σt : Fin (B.k + 1) → Ty ks)
      (branch : (i : Fin (B.k + 1)) → Ref → (C' : List JsTy) →
        ConvM (JsBlock S C' M [] (.ret (lowerTy cfg (ρ i)))))
      (j : Fin (B.k + 1)) (sub : PExpr Δ Φ Γ (.data (B.ref j)) oe) : ConvM (JsBlock S C M J e) := do
    let members : Fin (B.k + 1) → Σ g, Decl B.ks' (B.k + 1) g :=
      fun i => (B.bs.decl? i.val).getD ⟨0, default⟩
    let T : Fin (B.k + 1) → JsTy := fun i => lowerTy cfg (Ty.data (d := true) (B.ref i))
    let R : Fin (B.k + 1) → JsTy := fun i => lowerTy cfg (ρ i)
    recFuns cfg B.old (fun i => .data (B.ref i)) σt members T R branch fun C' => do
      let ee ← castE (← cPExpr sub n C' M) (T j)
      let call : JsExpr S C' M (R j) :=
        .app (← (Ref.c (C.length + j.val)).get (.fn [T j] (R j))) (.cons ee .nil)
      return .const "x" call (← k (.c C'.length) (R j :: C') M)

/-- A statement: a block every path of which ends in a `return` (or a jump). -/
partial def cTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ js o) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  match t with
  | .ret p => do
    let (cx, _) := n.own.stmt (fun v => Own.PExpr.occ v p) (fun _ => false)
    match n.own.retFn with
    | some (m, _) => return (JsBlock.ret (← cPExprFn p m { n with cx } C M))
    | none => return (JsBlock.ret (← cPExpr p { n with cx } C M))
  | Term.letV uk v t => cLetV uk v t n C M J
  | .letE _ c t =>
    let (cx, env') := n.own.stmt (fun w => Own.Comp.occ w c)
      (fun w => (Own.Term.occ (w.upU 1) t).n > 0)
    let allow := Own.fnAllow cx env' c t
    let fr := (Own.Comp.fnResult cx c allow).or (Own.papInfo cx c (Own.Term.occ (.u 0) t)).1
    let own := env'.pushUF (Own.Comp.owned cx c allow) fr
    cComp c { n with cx, allowFn := allow } C M J fun x C' M' =>
      cTerm t { n with u := x :: n.u, own } C' M' J
  | Term.record_casesOn (t := t₀) (fs := fs) us e t => do
    let m := (t₀ :: fs.toList).length
    let (cx, env') := n.own.stmt (fun w => Own.Neu.occ w e)
      (fun w => (Own.Term.occ (w.upU m) t).n > 0)
    let (bs, hs) := Own.recordFields cx t₀ fs e
    let own := env'.pushUH bs hs
    let ee ← cNeu e { n with cx } C M
    return (← destructureAny ee (usedFields us) fun refs C' =>
      cTerm t { n with u := refs ++ n.u, own } C' M J)
  | .branch b => cBranch b n C M J
  | Term.jump (σ := σ) j p => do
    let (cx, _) := n.own.stmt (fun v => Own.PExpr.occ v p) (fun _ => false)
    let pe ← cPExpr p { n with cx } C M
    match JsMem.ofIndex? J j.index (lowerTy cfg σ) with
    | some jm => return (JsBlock.jump jm pe)
    | none => throw "internal: a join point"

/-- `val k := v; t`.  A local function gets one constant per version generated
    (`Own.lamPlan`); any other value one constant. -/
partial def cLetV {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {σ τ : Ty ks} {js : JCtx ks} {o o' : Lvl}
    (uk : Usage1ω) (v : Val Δ d Φ Γ σ o) (t : Term Δ d (⟨σ, uk, o, true⟩ :: Φ) Γ τ js o')
    (n : Names) (C M J : List JsTy) : ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  let ce := n.own.stmt (fun w => Own.Val.occ w v) (fun w => (Own.Term.occ (w.upK 1) t).n > 0)
  let cx := ce.1
  let env' := ce.2
  match v, t with
  | Val.lam (σ := σ₁) (τ := τ₁) b, t =>
    let plan := Own.lamPlan uk cx env' b t
    let own := env'.pushKF true (some plan.info)
    let F := lowerTy cfg (Ty.fn (d := true) σ₁ τ₁)
    let rec versions (vs : List (Own.FnVer × Bool)) (C' : List JsTy) (refs : List Ref) :
        ConvM (JsBlock S C' M J (.ret (lowerTy cfg τ))) :=
      match vs with
      | [] =>
        let refs := refs.reverse
        let n' : Names := { n with k := refs.headD Ref.none :: n.k, own := own }
        cTerm t { n' with fns := (plan.info.id, refs) :: n.fns } C' M J
      | (ver, e) :: vs => do
        if !e then versions vs C' (.none :: refs) else
        let ve ← cVal (Val.lam b) { n with cx } C' M ver.mask
        return JsBlock.const (if ver.mask.any (·) then "k_mut" else "k") ve
          (← versions vs (F :: C') (.c C'.length :: refs))
    versions (plan.info.vers.zip plan.emit) C []
  | v, t => do
    let ve ← cVal v { n with cx } C M
    return (JsBlock.const "k" ve
      (← cTerm t { n with k := .c C.length :: n.k, own := env'.pushK (Own.Val.owned cx v) }
        (lowerTy cfg σ :: C) M J))

/-- A branch in tail position. -/
partial def cBranch {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks} {ℓ : Nat}
    (b : Branch Δ d Φ Γ τ js ℓ) (n : Names) (C M J : List JsTy) :
    ConvM (JsBlock S C M J (.ret (lowerTy cfg τ))) :=
  match b with
  | .ite c t e => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w c)
      (fun w => (Own.Term.occ w t).n > 0 || (Own.Term.occ w e).n > 0)
    let ce ← castE (← cNeu c { n with cx } C M) (.terminal .bool)
    return (JsBlock.ite ce (← cTerm t { n with own } C M J) (← cTerm e { n with own } C M J))
  | Branch.enum_casesOn (s := s) c bs => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w c)
      (fun w => (List.finRange _).any fun j => (Own.Term.occ w (bs j)).n > 0)
    let ce ← cNeu c { n with cx } C M
    let n := { n with own }
    let k := s.nOfConstructors
    let rec arms (m start : Nat) : ConvM (JsEnumArms S C M J (.ret (lowerTy cfg τ)) m) :=
      match m with
      | 0 => pure .nil
      | m + 1 => do
        if h : start < k then
          return .cons (← cTerm (bs ⟨start, h⟩) n C M J) (← arms m (start + 1))
        else throw "internal: an arm of a case analysis"
    return (JsBlock.enumCases ce (← arms k 0))
  | Branch.union_casesOn e brs => do
    let (cx, own) := n.own.stmt (fun w => Own.Neu.occ w e)
      (fun w => (Own.Branches.occ w brs).n > 0)
    let ee ← cNeu e { n with cx } C M
    return (← unionCasesAny ee
      (← cBranches brs { n with own } (Own.Neu.owned cx e) (Own.Neu.partOwned cx e) C M J))
  | Branch.join σ _ _ body br => do
    let σ' := lowerTy cfg σ
    let envBr := Own.joinBranchEnv n.own body
    let block ← cBranch br { n with own := envBr } C M (σ' :: J)
    -- the join point owns its parameter when every jump passes an owned value
    let own := (Own.joinBodyEnv n.own br).pushU [Own.joinParam σ envBr br]
    let rest ← cTerm body { n with u := .c C.length :: n.u, own } (σ' :: C) M J
    return (JsBlock.join "x" block rest)

/-- The arms of a union's case analysis: each binds the fields it uses
    (`const { _1: f₁, _2: f₂ } = s;`), owned or not (`ow`), and continues. -/
partial def cBranches {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {bs : List Bool} {cs : Ctors ks bs}
    {τ : Ty ks} {js : JCtx ks} {o : Lvl}
    (brs : Branches Δ d Φ Γ cs τ js o) (n : Names) (ow ph : Bool) (C M J : List JsTy) :
    ConvM (JsUnionArms S C M J (.ret (lowerTy cfg τ)) (lowerCtors cfg cs)) :=
  match brs with
  | Branches.two (c₁ := c₁) (c₂ := c₂) us₁ us₂ b₁ b₂ => do
    let (⟨u₁, s₁⟩, r₁) := mkSel (lowerCtor cfg c₁) (usedFields us₁) C
    let (⟨u₂, s₂⟩, r₂) := mkSel (lowerCtor cfg c₂) (usedFields us₂) C
    let own₁ := n.own.pushUH (Own.fieldsOwned c₁.binds.length ow)
      (Own.fieldsOwned c₁.binds.length ph)
    let own₂ := n.own.pushUH (Own.fieldsOwned c₂.binds.length ow)
      (Own.fieldsOwned c₂.binds.length ph)
    let a₁ ← cTerm b₁ { n with u := r₁ ++ n.u, own := own₁ } (pushAll u₁ C) M J
    let a₂ ← cTerm b₂ { n with u := r₂ ++ n.u, own := own₂ } (pushAll u₂ C) M J
    return .cons s₁ a₁ (.cons s₂ a₂ .nil)
  | Branches.cons (c := c) us b rest => do
    let (⟨u, s⟩, r) := mkSel (lowerCtor cfg c) (usedFields us) C
    let own := n.own.pushUH (Own.fieldsOwned c.binds.length ow) (Own.fieldsOwned c.binds.length ph)
    let a ← cTerm b { n with u := r ++ n.u, own } (pushAll u C) M J
    return .cons s a (← cBranches rest n ow ph C M J)

end

end

/-! ## Whole functions -/

/-- Convert a closed program into an exported JavaScript function named `name`
    (`export const name = (params) => …`), of all the parameters of its type (none when it is
    not a function).  `paramNames` are the preferred names of its parameters.  `owned` says
    which parameters the function owns (`OwnVersion.owned`; none by default): it may update
    those in place.  The conversion is the whole translation: the finished function is not
    rewritten afterwards (every optimisation is done on `Term`, before, by `Term.optimize`,
    and the updates done in place are decided on `Term`, by `LeanScript.Term.Ownership`). -/
def termToJs (cfg : JsConfig) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) (owned : List Bool := []) : Except String JsFun := do
  -- datatypes of equal layouts share one object id (`canonDecls`)
  let cfg := withCanonDecls cfg ct.Δ
  let τ := lowerTy cfg ct.τ
  let (ds, ret) := match τ with
    | .fn ds c => (ds, c)
    | t => ([], t)
  let ps : List (String × JsTy) := ds.zipIdx.map fun (t, i) => (paramNames.getD i s!"p{i}", t)
  let sig := jsSigOf cfg ct.Δ
  let fl := ds.zipIdx.map fun (_, i) => owned.getD i false
  let body ← cApplyTerm (S := sig) cfg ct.term {} (pushAll ds []) [] ((paramRefs [] ds).map (·.1))
    fl ret
  let body ← if h : pushAll ds [] = pushAll (ps.map (·.2)) [] then pure (h ▸ body) else
    throw "internal: the parameters of a function"
  return { name, leanName, sig, params := ps, ret, body }

end MoreJs

end
