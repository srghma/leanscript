module

public import LeanScript.TermElab.Anf.Emit

@[expose] public section

meta section

set_option autoImplicit false

/-!
# The normaliser: from direct-style source trees to the syntax of normal-form `Term`s

`LeanScript.Term` is a grammar of **normal forms**: every redex that can be computed has been,
a known value is never taken apart, called or forced, and every call has an open operand.  It
is convenient to *write* a term in direct style (`f (if c then g x else 0) + 1`), so the
notation `[Term| …]` (`LeanScript.TermElab.Notation`), the translator `#leanscript_to_term`
(`LeanScript.TermElab.ToTerm`) build a direct-style source tree `Src` (whose variables are de
Bruijn indices of the source), and this module normalises it into the syntax of a `Term`.

The normaliser is a **normaliser by evaluation**, in continuation-passing style.  A source tree
is evaluated to a *semantic value* `Sem`:

* an unknown (a variable of the output, or of the enclosing context) or a neutral expression
  built on one (`data_out`, `cond`, a call of an extern with an open argument);
* a value of known shape: a literal, a record, a constructor of a union, an array or list
  literal, `data_in`, a closure or a delay (with its environment and its source body), or the
  application of a constructor function (`#leanscript_get_ctor`).

A known value is reduced as soon as it is eliminated: `data_out` of `data_in`, a case analysis
of a constructor or a literal, a call of a **closed** closure on a **closed** argument
(β-reduction: the body is evaluated with the argument), the force of a closed delay, a fold
over a closed count or array literal with a closed body (unrolled), a call of an extern on
closed arguments (`PExpr.externLit`).  What cannot be reduced is emitted, in evaluation order:

* a closure or a delay is bound by `Term.letV` (so it is shared by name, `PExpr.kvar`); its
  body is normalised on its own, one level deeper, and is `Body.closed` exactly when it
  mentions nothing bound outside of it (the level of what the body mentions is tracked, so the
  choice is exact);
* a computation with an open operand (a call, a fold, a force) is bound by `Term.letE`;
* a source `let` of a compound neutral expression is `Comp.share`d; of a data literal, bound by
  `Term.letV` (still known, so later case analyses are reduced);
* a branch on a neutral value in tail position gets the continuation in each branch; anywhere
  else it is the pure conditional `Neu.cond` when it is an `if` whose branches are pure, and
  otherwise gets a **join point** for the rest of the computation.  A join point is only
  allowed in front of a branch (`Branch.join`), so join points are kept *pending* until the
  next branch, where they are placed; a pending join point that is jumped to in straight-line
  code is inlined instead (it is jumped to only there).

Every binder is annotated `many` (`Usage1ω.many`, `Usage01ω.many`): the annotations are sound
and a later pass (`Term.dce`) can make them exact.

Variables are resolved to indices only when rendered: a semantic value names an output
variable by its *position* (the number of binders of its context outside it), so it stays
valid under the binders the normaliser adds.  A variable of the enclosing context (free in the
source) is an unknown, and is taken to be open.
-/

open Lean Meta Elab Term

namespace LeanScript.Anf

/-! ## The normaliser -/

mutual

/-- Normalise the operands `ss` in order, then continue with their values. -/
partial def values (ss : List Src) (sc : Scope) (p : Pos)
    (k : List Sem → Pos → TermElabM Out) : TermElabM Out :=
  match ss with
  | [] => k [] p
  | s :: ss => value s sc p fun v p => values ss sc p fun vs p => k (v :: vs) p

/-- Bind a value by a source `let`: in place when trivial, a compound neutral expression
    shared (`Comp.share`), a data literal bound by `letV`. -/
partial def bindSem (s : Sem) (p : Pos) (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if s.trivial then return ← k s p
  if s.isNeutral then
    return ← emitComp (← `(LeanScript.Comp.share $(← renderNeu s p.core false)))
      (← openLv s.lv "a shared expression") p k
  let (s', ty?) := match s with
    | .ascribe s ty => (s.strip, some ty)
    | s => (s, none)
  let c := p.core
  let asc (v : Lean.Term) : TermElabM Lean.Term := match ty? with
    | some ty => `(($v : LeanScript.Val _ _ _ _ $ty _))
    | none => pure v
  match s' with
  | .record fs _ =>
      let vs ← asc (← `(LeanScript.Val.record_mk $(← argsStx (← fs.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .record fs (some kr)) p k
  | .union pos ix fs _ =>
      let vs ← asc (← `(LeanScript.Val.union_mk $ix $(← argsStx (← fs.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .union pos ix fs (some kr)) p k
  | .array es _ =>
      let vs ← asc (← `(LeanScript.Val.array_mk $(← elemsStx (← es.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .array es (some kr)) p k
  | .list es _ =>
      let vs ← asc (← `(LeanScript.Val.list_mk $(← elemsStx (← es.toList.mapM (render · c false)))))
      emitVal vs s.lv (fun kr => .list es (some kr)) p k
  | .dataIn b j e _ =>
      let vs ← asc (← `(LeanScript.Val.data_in $b $j $(← render e c false)))
      emitVal vs s.lv (fun kr => .dataIn b j e (some kr)) p k
  | _ => k s p

/-- Bind values in order (`bindSem`). -/
partial def bindSems (ss : List Sem) (p : Pos) (k : List Sem → Pos → TermElabM Out) :
    TermElabM Out :=
  match ss with
  | [] => k [] p
  | s :: ss => bindSem s p fun s p => bindSems ss p fun ss p => k (s :: ss) p

/-- The body of a closure, a delay or a fold, binding `n` unknowns: normalised one level
    deeper, and `Body.closed` exactly when it mentions nothing bound outside of it.  Returns
    the syntax of the `Body` and its level. -/
partial def mkBody (n : Nat) (body : Src) (sc : Scope) (p : Pos) : TermElabM (Lean.Term × Lvl) := do
  let c := p.core
  let inner : Core := { du := c.du + n, dk := c.dk, jd := 0, depth := c.depth + 1, placed := [] }
  let sc' : Scope := { vars := unknowns n c.du (c.depth + 1) ++ sc.vars, joins := [] }
  let o ← stmt body sc' { core := inner } .ret
  match o.lv with
  | some m =>
      if m ≤ c.depth then return (← `(LeanScript.Body.opened (d := $(quote c.depth)) (ls_relvl% $(o.stx)) (by ls_lvl)), some m)
      else return (← `(LeanScript.Body.closed (d := $(quote c.depth)) $(o.stx)), none)
  | none => return (← `(LeanScript.Body.closed (d := $(quote c.depth)) $(o.stx)), none)

/-- Apply the value `f` to `a`: β-reduce a closed closure on a closed argument, else call it. -/
partial def apply (f a : Sem) (p : Pos) (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if let .clo env _ body kr := f.strip then
    if kr.lv.isNone && a.lv.isNone then
      return ← value body { vars := a :: env } p k
  let ℓ ← match lmeet f.lv a.lv with
    | some ℓ => pure ℓ
    | none => throwError "cannot call a closed function that is not a closure while normalising"
  emitComp (← `(LeanScript.Comp.app $(← render f p.core false) $(← render a p.core false) rfl)) ℓ p k

/-- A statement in the middle of a computation: a pending join point for the continuation
    `k`, and the statement jumping to it. -/
partial def reify (ty? : Option Lean.Term) (run : Pos → Kont → TermElabM Out) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  let id ← mkFreshId
  let saved := p.pend
  let pj : Pend := { id, ty?, k := fun s c => k s { core := c, pend := saved } }
  run { p with pend := pj :: p.pend } (.jump id)

/-- Normalise `s` to a value, and continue with it. -/
partial def value (s : Src) (sc : Scope) (p : Pos) (k : Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  match s with
  | .var i => k (sc.var i) p
  | .lit stx v => k (.lit stx v) p
  | .enumMk i stx => k (.enum i stx) p
  | .record args => values args.toList sc p fun fs p => k (.record fs.toArray none) p
  | .union pos ix args => values args.toList sc p fun fs p => k (.union pos ix fs.toArray none) p
  | .array es => values es.toList sc p fun fs p => k (.array fs.toArray none) p
  | .list es => values es.toList sc p fun fs p => k (.list fs.toArray none) p
  | .dataIn b j e => value e sc p fun v p => k (.dataIn b j v none) p
  | .ctor f args shape => (values args.toList sc p fun fs p => do
      match shape with
      | some { kind := .wrap, data? := none } => k fs[0]! p
      | _ => k (.ctor f fs.toArray shape) p)
  | .embed stx => k (.embed stx) p
  | .dataOut b j e => value e sc p fun v p => do k (← dataOutSem b j v) p
  | .cond c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => value a sc p k
      | some _ => value b sc p k
      | none =>
        needNeutral cv "the condition of `cond`"
        values [a, b] sc p fun vs p => k (.cond cv vs[0]! vs[1]!) p)
  | .extern e args => values args.toList sc p fun fs p => do k (← externSem e fs.toArray) p
  | .ascribe s ty => value s sc p fun v p => k (.ascribe v ty) p
  | .app f a => (do
      -- `(fun x₁ … xₙ => b) a₁ … aₖ` (`k ≤ n`) is `let x₁ := a₁; …`: no closure is built
      let (hd, as) := Src.spine s
      if as.length ≤ Src.lams hd then
        values as sc p fun avs p => do
          let (tys, body) := Src.peel hd as.length
          let avs := (avs.zip tys).map fun (a, ty?) => match ty? with
            | some ty => Sem.ascribe a ty
            | none => a
          bindSems avs p fun avs p => value body (sc.pushAll avs.reverse) p k
      else
        value f sc p fun fv p => value a sc p fun av p => apply fv av p k)
  | .lam ty? body => (do
      let (bs, o) ← mkBody 1 body sc p
      let vs ← match ty? with
        | some τ => `(LeanScript.Val.lam (σ := $τ) (u := .many) $bs)
        | none => `(LeanScript.Val.lam (u := .many) $bs)
      emitVal vs o (fun kr => .clo sc.vars ty? body kr) p k)
  | .delayMk lazy τ? body => (do
      let (bs, o) ← mkBody 0 body sc p
      let vs ← match lazy, τ? with
        | false, some τ => `(LeanScript.Val.thunk_mk (τ := $τ) $bs)
        | false, none => `(LeanScript.Val.thunk_mk $bs)
        | true, some τ => `(LeanScript.Val.lazy_mk (τ := $τ) $bs)
        | true, none => `(LeanScript.Val.lazy_mk $bs)
      emitVal vs o (fun kr => .delay lazy τ? sc.vars body kr) p k)
  | .force lazy τ? e => (value e sc p fun v p => do
      if let .delay _ _ env body kr := v.strip then
        if kr.lv.isNone then return ← value body { vars := env } p k
      let ℓ ← match v.lv with
        | some ℓ => pure ℓ
        | none => throwError "cannot force a closed delay of unknown shape while normalising"
      let e ← `(ls_relvl% $(← render v p.core false))
      let cs ← match lazy, τ? with
        | false, some τ => `(LeanScript.Comp.thunk_force (τ := $τ) $e)
        | false, none => `(LeanScript.Comp.thunk_force $e)
        | true, some τ => `(LeanScript.Comp.lazy_force (τ := $τ) $e)
        | true, none => `(LeanScript.Comp.lazy_force $e)
      emitComp cs ℓ p k)
  | .natRec τ? n z st => (values [n, z] sc p fun vs p => do
      let nv := vs[0]!
      let zv := vs[1]!
      let (bs, o) ← mkBody 2 st sc p
      match lmeet (lmeet nv.lv zv.lv) o with
      | none =>
        let some N ← nv.natVal?
          | throwError "cannot unroll a closed `nat_rec` whose count is not known while normalising"
        unrollNat st sc N 0 zv p k
      | some ℓ =>
        let c := p.core
        let cs ← match τ? with
          | some τ => `(LeanScript.Comp.nat_rec (τ := $τ) (u₁ := .many) (u₂ := .many)
              $(← render nv c false) $(← render zv c false) $bs rfl)
          | none => `(LeanScript.Comp.nat_rec (u₁ := .many) (u₂ := .many)
              $(← render nv c false) $(← render zv c false) $bs rfl)
        emitComp cs ℓ p k)
  | .arrayFoldl a z st => (values [a, z] sc p fun vs p => do
      let av := vs[0]!
      let zv := vs[1]!
      let (bs, o) ← mkBody 2 st sc p
      match lmeet (lmeet av.lv zv.lv) o with
      | none =>
        let .array es _ := av.strip
          | throwError "cannot unroll a closed `array_foldl` over an array of unknown shape"
        unrollArray st sc es.toList zv p k
      | some ℓ =>
        let c := p.core
        emitComp (← `(LeanScript.Comp.array_foldl (u₁ := .many) (u₂ := .many)
          $(← render av c false) $(← render zv c false) $bs rfl)) ℓ p k)
  | .dataRec Δ? b ρ k? brs j e => (value e sc p fun ev p => do
      let bodies ← brs.mapM fun br => mkBody 1 br sc p
      let o := bodies.foldl (fun o (_, o') => lmeet o o') ev.lv
      let some ℓ := o
        | throwError "cannot compute a closed fold of a datatype while normalising"
      let c := p.core
      let pairs ← bodies.mapM fun (bs, _) => `(⟨_, $bs⟩)
      let pats ← (List.range pairs.size).toArray.mapM fun i => `(⟨$(quote i), _⟩)
      let brFun ← `(fun $[| $pats => $pairs]*)
      let ev' ← render ev c false
      let cs ← match Δ?, k? with
        | some Δ, none => `(LeanScript.Comp.dataRecS (Δ := $Δ) $b $ρ (fun _ => .many) $brFun $j $ev' rfl)
        | none, none => `(LeanScript.Comp.dataRecS $b $ρ (fun _ => .many) $brFun $j $ev' rfl)
        | some Δ, some kk =>
            `(LeanScript.Comp.dataBrecS (Δ := $Δ) $b $ρ $kk (fun _ => .many) $brFun $j $ev' rfl)
        | none, some kk => `(LeanScript.Comp.dataBrecS $b $ρ $kk (fun _ => .many) $brFun $j $ev' rfl)
      emitComp cs ℓ p k)
  | .letE v b => value v sc p fun vv p => bindSem vv p fun vv p => value b (sc.push vv) p k
  | .recordCases scrut n body => (value scrut sc p fun sv p =>
      takeApart sv n p fun fs p => value body (sc.pushAll fs) p k)
  | .ite ty? c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => value a sc p k
      | some _ => value b sc p k
      | none =>
        needNeutral cv "the condition of `if`"
        match ← pureSem? a sc, ← pureSem? b sc with
        | some av, some bv =>
            let r := Sem.cond cv av bv
            k (match ty? with | some ty => .ascribe r ty | none => r) p
        | _, _ => reify ty? (fun p K => branchOn cv s sc p K) p k)
  | .enumCases ty? scrut pats brs => (value scrut sc p fun sv p => do
      match enumSel pats sv with
      | some i => value brs[i]! sc p k
      | none => reify ty? (fun p K => branchOn sv s sc p K) p k)
  | .unionCases ty? scrut brs => (value scrut sc p fun sv p => do
      match unionSel (brs.map (·.1)) sv with
      | some (i, fs) => bindSems fs.toList p fun fs p => value brs[i]!.2 (sc.pushAll fs) p k
      | none => reify ty? (fun p K => branchOn sv s sc p K) p k)
  | .join ty? .. => reify ty? (fun p K => stmt s sc p K) p k
  | .jump .. => stmt s sc p .ret

/-- Unroll a closed `nat_rec` from `i` to `N`. -/
partial def unrollNat (st : Src) (sc : Scope) (N i : Nat) (acc : Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out := do
  if i ≥ N then k acc p
  else
    let pred := Sem.lit (← `(LeanScript.PExpr.lit LeanScript.LeanPrimTy.nat $(quote i))) (.nat i)
    value st (sc.pushAll [acc, pred]) p fun acc p => unrollNat st sc N (i + 1) acc p k

/-- Unroll a closed `array_foldl` over the elements `es`. -/
partial def unrollArray (st : Src) (sc : Scope) (es : List Sem) (acc : Sem) (p : Pos)
    (k : Sem → Pos → TermElabM Out) : TermElabM Out :=
  match es with
  | [] => k acc p
  | e :: es => value st (sc.pushAll [e, acc]) p fun acc p => unrollArray st sc es acc p k

/-- Take a value apart as a record of `n` fields: its fields when it is a known record, else
    `Term.record_casesOn` of a neutral value. -/
partial def takeApart (sv : Sem) (n : Nat) (p : Pos) (k : List Sem → Pos → TermElabM Out) :
    TermElabM Out := do
  if let some fs := recordSel n sv then
    return ← bindSems fs.toList p k
  needNeutral sv "the scrutinee of a record"
  let c := p.core
  let ns ← renderNeu sv c false
  let r ← k (unknowns n c.du c.depth) { p with core := { c with du := c.du + n } }
  return { stx := ← `(LeanScript.Term.record_casesOn (d := $(quote c.depth)) [] $ns $(r.stx)),
           lv := lmeet sv.lv r.lv }

/-- The value of a pure source tree, when it needs no computation, binding or branch (other
    than pure conditionals). -/
partial def pureSem? (s : Src) (sc : Scope) : TermElabM (Option Sem) := do
  try
    let all (ss : Array Src) : TermElabM (Option (Array Sem)) := do
      let mut out := #[]
      for s in ss do
        let some v ← pureSem? s sc | return none
        out := out.push v
      return some out
    match s with
    | .var i => return some (sc.var i)
    | .lit stx v => return some (.lit stx v)
    | .enumMk i stx => return some (.enum i stx)
    | .embed stx => return some (.embed stx)
    | .record args => return (← all args).map (.record · none)
    | .union pos ix args => return (← all args).map (.union pos ix · none)
    | .array es => return (← all es).map (.array · none)
    | .list es => return (← all es).map (.list · none)
    | .dataIn b j e => return (← pureSem? e sc).map (.dataIn b j · none)
    | .ctor f args shape => (return (← all args).map fun fs =>
        (match shape with
         | some { kind := .wrap, data? := none } => fs[0]!
         | _ => .ctor f fs shape))
    | .dataOut b j e => (do
        let some v ← pureSem? e sc | return none
        return some (← dataOutSem b j v))
    | .cond c a b | .ite _ c a b => (do
        let some cv ← pureSem? c sc | return none
        match ← iteSel cv with
        | some 0 => pureSem? a sc
        | some _ => pureSem? b sc
        | none =>
          unless cv.isNeutral do return none
          let some av ← pureSem? a sc | return none
          let some bv ← pureSem? b sc | return none
          let r := Sem.cond cv av bv
          match s with
          | .ite (some ty) .. => return some (.ascribe r ty)
          | _ => return some r)
    | .extern e args => (do
        let some fs ← all args | return none
        return some (← externSem e fs))
    | .ascribe s ty => return (← pureSem? s sc).map (.ascribe · ty)
    | _ => return none
  catch _ => return none

/-- A branch on the value `sv` (the scrutinee of `s`, not a known value), in tail position:
    the pending join points are placed in front of it, and each branch goes to `K`. -/
partial def branchOn (sv : Sem) (s : Src) (sc : Scope) (p : Pos) (K : Kont) : TermElabM Out := do
  needNeutral sv "the scrutinee of a branch"
  placeJoins p fun c => do
    let p' : Pos := { core := c }
    let ns ← renderNeu sv c false
    match s with
    | .ite _ _ a b =>
        let ta ← stmt a sc p' K
        let tb ← stmt b sc p' K
        return { stx := ← `(LeanScript.Branch.ite $ns $(ta.stx) $(tb.stx)),
                 lv := lmeet sv.lv (lmeet ta.lv tb.lv) }
    | .enumCases _ _ pats brs =>
        let outs ← brs.mapM fun b => stmt b sc p' K
        -- the branch of each constructor up to the largest one named; the default past it
        let dflt := outs[outs.size - 1]!
        let top := pats.foldl (fun m q => match q with | some i => max m (i + 1) | none => m) 0
        let listed ← (List.range top).toArray.mapM fun i => do
          let o := outs[enumSel pats (.enum (some i) default) |>.getD (outs.size - 1)]!
          `(⟨_, $(o.stx)⟩)
        let lv := outs.foldl (fun o r => lmeet o r.lv) sv.lv
        return { stx := ← `(LeanScript.Branch.enumList $ns [$listed,*] ⟨_, $(dflt.stx)⟩), lv }
    | .unionCases _ _ brs =>
        let outs ← brs.mapM fun (n, b) =>
          stmt b (sc.pushAll (unknowns n c.du c.depth)) { core := { c with du := c.du + n } } K
        let lv := outs.foldl (fun o r => lmeet o r.lv) sv.lv
        return { stx := ← `(LeanScript.Branch.union_casesOn $ns
                   $(← branchesStx c.depth (outs.map (·.stx)).toList)), lv }
    | _ => throwError "internal error of the normaliser: not a branch"

/-- Normalise `s` to a statement whose value goes to `K`. -/
partial def stmt (s : Src) (sc : Scope) (p : Pos) (K : Kont) : TermElabM Out := do
  if let .fn f := K then return ← value s sc p f
  match s with
  | .letE v b => value v sc p fun vv p => bindSem vv p fun vv p => stmt b (sc.push vv) p K
  | .recordCases scrut n body => (value scrut sc p fun sv p =>
      takeApart sv n p fun fs p => stmt body (sc.pushAll fs) p K)
  | .ite _ c a b => (value c sc p fun cv p => do
      match ← iteSel cv with
      | some 0 => stmt a sc p K
      | some _ => stmt b sc p K
      | none => branchOn cv s sc p K)
  | .enumCases _ scrut pats brs => (value scrut sc p fun sv p => do
      match enumSel pats sv with
      | some i => stmt brs[i]! sc p K
      | none => branchOn sv s sc p K)
  | .unionCases _ scrut brs => (value scrut sc p fun sv p => do
      match unionSel (brs.map (·.1)) sv with
      | some (i, fs) => bindSems fs.toList p fun fs p => stmt brs[i]!.2 (sc.pushAll fs) p K
      | none => branchOn sv s sc p K)
  | .join ty? body main => (do
      let id ← mkFreshId
      let saved := p.pend
      let pj : Pend := { id, ty?, k := fun v c => stmt body (sc.push v) { core := c, pend := saved } K }
      stmt main { sc with joins := id :: sc.joins } { p with pend := pj :: p.pend } K)
  | .jump j arg => (value arg sc p fun v p => do
      let some id := sc.joins[j]? | throwError "unknown join point ^{j}"
      jumpTo id v p)
  | _ => value s sc p K.apply

end

/-! ## Entry points -/

/-- The syntax of the statement (`Term`) that a source tree denotes. -/
def Src.toTerm (s : Src) : TermElabM Lean.Term := do
  `(ls_relvl% $((← stmt s {} {} .ret).stx))

/-- The syntax of the pure expression (`PExpr`) that a source tree denotes; fails when it needs
    a computation, a binding or a branch. -/
def Src.toPExpr (s : Src) : TermElabM Lean.Term := do
  let o ← value s {} {} fun v p => do
    unless p.core.du == 0 && p.core.dk == 0 do
      throwError "this term is not a pure expression: it makes a call, binds or branches"
    return { stx := ← render v p.core false, lv := v.lv }
  `(ls_relvl% $(o.stx))

/-- The syntax of the neutral expression (`Neu`) that a source tree denotes. -/
def Src.toNeu (s : Src) : TermElabM Lean.Term := do
  let o ← value s {} {} fun v p => do
    unless p.core.du == 0 && p.core.dk == 0 && v.isNeutral do
      throwError "this term is not a neutral pure expression: it makes a call, binds, \
        branches, or is a literal or a constructor"
    return { stx := ← renderNeu v p.core false, lv := v.lv }
  `(ls_relvl% $(o.stx))

end LeanScript.Anf

end
