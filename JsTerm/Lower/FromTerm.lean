module

public import JsTerm.Lower.Basic
public import JsTerm.Passes.InPlace
public import JsTerm.Passes.Cleanup
public import JsTerm.Passes.Contify

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
| `Comp.nat_rec n z s` | `let acc = z; for (let i = 0n; i < n; i++) { …; acc = …; }`; when the step ignores the accumulator (a case analysis `0` / `k + 1`), only the last iteration (`JsBlock.lastIter`) |
| `Comp.array_foldl a z s` | `let acc = z; for (const e of a) { …; acc = …; }`; a fold pushing every element (`Array.append z a`) on generic arrays is `[...z, ...a]` |
| `Comp.thunk_force`, `Comp.lazy_force` | `thunk__lean_thunk_get_own(t)`, `t()` |

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

The recursors of declared datatypes (`data_in`, `data_out`, `data_rec`, `data_brec`) are not
converted yet: a term using one is refused with an error.

The literals, the conversion monad and the builders of the shapes are in `JsTerm.Lower.Basic`.
-/

namespace MoreJs

open LeanScript

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
  | Neu.extern (σs := σs) e args _ => do
    let as ← cArgs args n C M
    match stringPosArg? σs with
    | some s => lowerExtern (externName e) (.cons (.lit (.string s)) as)
    | none => lowerExtern (externName e) as

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
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | PExpr.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | PExpr.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | PExpr.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
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
  unionMk _ (ctorIxIndex ix) as

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
  | Val.lam (σ := σ) (τ := ρ) b => do
    match lowerTy cfg (Ty.fn (d := true) σ ρ) with
    | .fn (d₀ :: ds) c =>
      -- all the parameters of the type at once
      let ps := paramRefs C (d₀ :: ds)
      let body ← cApplyBody b n (pushAll (d₀ :: ds) C) M (ps.map (·.1)) c
      castE (.lam ((d₀ :: ds).map fun _ => "x") body) _
    | _ => throw "internal: the type of a lambda"
  | Val.thunk_mk (τ := t) b => do
    let body ← cBody b n C M []
    let lz : JsExpr C M (.fn [] (lowerTy cfg t.relax)) := .lam (σs := []) [] body
    lowerExtern "lean_mk_thunk" (.cons lz .nil)
  | Val.lazy_mk b => do castE (.lam (σs := []) [] (← cBody b n C M [])) _
  | .record_mk args => do recordLit (← cArgs args n C M) _
  | Val.union_mk (cs := cs) (c := c) ix args => do unionLit cs c ix (← cArgs args n C M)
  | Val.array_mk (t := t) es => do arrayLit t (← cElems (A := lowerTy cfg (Ty.array (d := true) t)) es n C M)
  | Val.list_mk (t := t) es => do
    listLit (← cElems (A := .list (lowerTy cfg t)) es n C M) _
  | .data_in _ _ _ => notYet

/-- A statement that answers a function, applied to the parameters `ps` (bound in `C`, the
    first one outermost), answering a value of type `r`: the chain of lambdas `val k := fun x =>
    …; ret k` takes the parameters one after the other; any other statement computes the
    function (a block computing it into a join point), which is then called on the parameters
    left (`f(y)`). -/
partial def cApplyTerm {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {o : Lvl}
    (t : Term Δ d Φ Γ τ [] o) (n : Names) (C M : List JsTy) (ps : List Ref) (r : JsTy) :
    ConvM (JsBlock C M [] (.ret r)) :=
  let whole : ConvM (JsBlock C M [] (.ret r)) := do
    let blk ← cTerm t n C M []
    if h : lowerTy cfg τ = r then return h ▸ blk else
    match lowerTy cfg τ with
    | .fn ds c =>
      if ds.length != ps.length then throw "internal: the parameters of a function" else
      let call ← papCall (.c C.length) ((ps.zip ds).map fun (p, t) => (p, t)) c
        (C := lowerTy cfg τ :: C) (M := M)
      castRet (.join "f" (blk.retToJump (k := .ret c)) (.ret call)) r
    | _ => throw "internal: applying a value that is not a function"
  if ps.isEmpty then whole else
  match t with
  | .letV _ v (.ret (.kvar k)) =>
    if k.index != 0 then whole else
    match v with
    | Val.lam b => cApplyBody b n C M ps r
    | _ => whole
  | _ => whole

/-- The body of a lambda applied to the parameters `ps` (its own parameter first). -/
partial def cApplyBody {d : Nat} {Φ : KCtx ks} {Γ bs : UCtx ks} {τ : Ty ks} {o : Lvl}
    (b : Body Δ d Φ Γ bs τ o) (n : Names) (C M : List JsTy) (ps : List Ref) (r : JsTy) :
    ConvM (JsBlock C M [] (.ret r)) :=
  match ps with
  | [] => throw "internal: a lambda without a parameter"
  | p :: ps' => match b with
    | .closed t => cApplyTerm t { n with u := [p] } C M ps' r
    | .opened t _ => cApplyTerm t { n with u := p :: n.u } C M ps' r

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
  | Comp.app (σ := σ) (τ := τ) f a _ => do
    -- the function, as a constant (or the partial application it is)
    let withF (rest : Ref → (C' : List JsTy) → ConvM (JsBlock C' M J e)) :
        ConvM (JsBlock C M J e) := do
      match pexprRef? f n with
      | some r@(.c _) | some r@(.pap ..) => rest r C
      | _ => bindConst (← cPExpr f n C M) rest
    withF fun fr C₁ => do
      bindConst (← cPExpr a n C₁ M) fun ar C₂ => do
        let (base, args) := match fr with
          | .pap b as => (b, as)
          | r => (r, [])
        let args := args ++ [(ar, lowerTy cfg σ)]
        if τ.isFn then
          -- a partial application: the call waits for the other parameters
          k (.pap base args) C₂ M
        else
          let call ← papCall base args (lowerTy cfg τ) (C := C₂) (M := M)
          return .const "x" call (← k (.c C₂.length) _ M)
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
    let e : JsExpr C M (lowerTy cfg t.relax) ← lowerExtern "lean_thunk_get_own" (.cons pe .nil)
    return .const "x" e (← k (.c C.length) _ M)
  | Comp.lazy_force (τ := t) p => do
    let pe ← cPExpr p n C M
    let e ← forceLazy pe (lowerTy cfg t.relax)
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
  | Term.record_casesOn us e t => do
    let ee ← cNeu e n C M
    destructureAny ee (usedFields us) fun refs C' => cTerm t { n with u := refs ++ n.u } C' M J
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
    unionCasesAny ee (← cBranches brs n C M J)
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

/-- Convert a closed program into an exported JavaScript function named `name`
    (`export const name = (params) => …`), of all the parameters of its type (none when it is
    not a function).  `paramNames` are the preferred names of its parameters.  The body is
    cleaned up (`cleanup`, `peephole`, `inlineArrays`), and the arrays nothing else refers to are updated
    in place (`inPlace`). -/
def termToJs (cfg : JsConfig) (name leanName : String) (paramNames : List String)
    (ct : ClosedTerm) : Except String JsFun := do
  let τ := lowerTy cfg ct.τ
  let (ds, ret) := match τ with
    | .fn ds c => (ds, c)
    | t => ([], t)
  let ps : List (String × JsTy) := ds.zipIdx.map fun (t, i) => (paramNames.getD i s!"p{i}", t)
  let body ← cApplyTerm cfg ct.term {} (pushAll ds []) [] ((paramRefs [] ds).map (·.1)) ret
  let body ← if h : pushAll ds [] = pushAll (ps.map (·.2)) [] then pure (h ▸ body) else
    throw "internal: the parameters of a function"
  let body := peephole (inlineArrays (peephole (cleanup body)))
  let body := peephole (cleanup body)
  let body := tidy body
  let body := inPlace body
  return { name, leanName, params := ps, ret, body }

end MoreJs

end
