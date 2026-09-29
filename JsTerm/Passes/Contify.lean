module

public import JsTerm.Passes.Tco
public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Local functions as join points, assignments moved up, literals moved down

The last clean-ups of `JsTerm` that the conversion runs on the body of each function (not
proved: `JsTerm` has no semantics; checked by the snapshots):

* **local functions called in tail position** (`contifyNode`): `const k = (x) => { B };` (or
  `const k = () => (x) => { B };`, the join points of `do` notation, which take a `Unit` first)
  whose every use is a tail call of the same form — `return k(e);`, or `acc = k(e);` at the end
  of an iteration — is a join point: the calls jump to it with `e`, and `B` runs after, its
  `return v` being the same form (`return v;`, `acc = v;` and the end of the iteration).  No
  closure is allocated, and no call is made;
* **assignments moved up** (`hoistAssignNode`): `const y = e; acc = x;` is `acc = x; const y = e;`
  when `e` does not read `acc` (and no closure reads a mutable variable), so that a value
  computed for `acc` is assigned right after it is computed, and then written in place
  (`acc = f(acc);`, `inlineOnce`);
* **constants used once, right away** (`inlineOnceNode` of `JsTerm.Passes.Cleanup`, here only
  when no closure reads or assigns a mutable variable), so that `const f = k(); return f(e);`
  is a call `return k()(e);` that can be contified;
* **record and union literals used once** (`inlineLitNode`): `const x = { … };` read once, not
  in a loop or a closure, is written where it is read (its parts have no effect, cannot throw,
  and read no mutable variable assigned in between), so that an accumulator starting from it
  can be unboxed.

`tidy` runs these and the passes of `JsTerm.Passes.Unbox` bottom-up, with the clean-ups of
`JsTerm.Passes.Cleanup` between the rounds, until nothing changes.
-/

namespace MoreJs

/-! ## Local functions called in tail position -/

/-- A closure of one parameter `σ` answering a `ρ`, as a body over the constants around it
    (`thunk`: it is a `() => (x) => …`). -/
structure LamInfo (C M : List JsTy) where
  thunk : Bool
  σ : JsTy
  ρ : JsTy
  body : JsBlock (σ :: C) M [] (.ret ρ)

/-- The closure an expression is, when it is `(x) => { … }` or `() => (x) => { … }`. -/
def JsExpr.lamInfo? {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Option (LamInfo C M)
  | .lam (σs := [σ]) (τ := ρ) _ B => some ⟨false, σ, ρ, B⟩
  | .lam (σs := []) _ (.ret (.lam (σs := [σ]) (τ := ρ) _ B)) => some ⟨true, σ, ρ, B⟩
  | _ => none

/-- The argument of a call `k(e)` (or `k()(e)` when `thunk`) of the constant `k` of index `d`,
    when `e` does not mention `k`. -/
def JsExpr.callOf? {C M : List JsTy} {τ : JsTy} (d : Nat) (thunk : Bool) :
    JsExpr C M τ → Option ((σ : JsTy) × JsExpr C M σ)
  | .app (σs := [σ]) f (.cons e .nil) =>
    let isK : Bool := if thunk then
        (match f with
         | .app (.cvar x) .nil => x.index == d
         | _ => false)
      else
        (match f with
         | .cvar x => x.index == d
         | _ => false)
    if isK && !e.mentions ⟨false, d⟩ then some ⟨σ, e⟩ else none
  | _ => none

/-- How the calls of a contified function are used: returned, or assigned to the mutable
    variable of index `m` (where the walk starts) at the end of an iteration. -/
inductive TailForm where
  | ret
  | assign (m : Nat)

/-- What `JsBlock.contify` knows: the index of the function `k` among the constants, how many
    mutable variables it went under, the form of the calls, whether the function is a
    `() => (x) => …`, and the type of its parameter. -/
structure Contify where
  d : Nat
  dm : Nat
  form : TailForm
  thunk : Bool
  σ : JsTy

/-- The jump of a call `k(e)`, when it is one (and the argument has the type of the
    parameter). -/
def Contify.jumpOf? (u : Contify) {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (j : JsMem J u.σ)
    (e : JsExpr C M τ) : Option (JsBlock C M J k) :=
  match e.callOf? u.d u.thunk with
  | some ⟨σ', a⟩ => if h : σ' = u.σ then some (.jump j (h ▸ a)) else none
  | none => none

mutual
/-- The block with the calls of `k` replaced by jumps to the new join point `nj` (the other
    join points renamed by `jr`); `none` if `k` is used otherwise. -/
partial def JsBlock.contify (u : Contify) {C M J J' : List JsTy} {k : JsEnd} (jr : JsJRen J J')
    (nj : JsMem J' u.σ) : JsBlock C M J k → Option (JsBlock C M J' k)
  | .ret e =>
    match u.form with
    | .ret =>
      match u.jumpOf? nj e with
      | some b => some b
      | none => if e.mentions ⟨false, u.d⟩ then none else some (.ret e)
    | .assign _ => if e.mentions ⟨false, u.d⟩ then none else some (.ret e)
  | .assign x e .next =>
    let direct : Option (JsBlock C M J' .loop) := match u.form with
      | .assign m => if x.index == m + u.dm then u.jumpOf? nj e else none
      | .ret => none
    match direct with
    | some b => some b
    | none => if e.mentions ⟨false, u.d⟩ then none else some (.assign x e .next)
  | .next => some .next
  | .throw msg => some (.throw msg)
  | .jump j e => if e.mentions ⟨false, u.d⟩ then none else return .jump (← jr j) e
  | .const x e rest =>
    if e.mentions ⟨false, u.d⟩ then none else
    .const x e <$> rest.contify { u with d := u.d + 1 } jr nj
  | .letMut x e rest =>
    if e.mentions ⟨false, u.d⟩ then none else
    .letMut x e <$> rest.contify { u with dm := u.dm + 1 } jr nj
  | .assign x e rest =>
    if e.mentions ⟨false, u.d⟩ then none else .assign x e <$> rest.contify u jr nj
  | .destructure (us := us) e sel rest =>
    if e.mentions ⟨false, u.d⟩ then none else
    .destructure e sel <$> rest.contify { u with d := u.d + us.length } jr nj
  | .ite c t e =>
    if c.mentions ⟨false, u.d⟩ then none else
    return .ite c (← t.contify u jr nj) (← e.contify u jr nj)
  | .enumCases e arms =>
    if e.mentions ⟨false, u.d⟩ then none else .enumCases e <$> arms.contify u jr nj
  | .unionCases e arms =>
    if e.mentions ⟨false, u.d⟩ then none else .unionCases e <$> arms.contify u jr nj
  | .join x b rest =>
    return .join x (← b.contify u jr.lift nj.succ) (← rest.contify { u with d := u.d + 1 } jr nj)
  | .forRange x nt n b rest =>
    if n.mentions ⟨false, u.d⟩ || b.mentions ⟨false, u.d + 1⟩ then none else
    .forRange x nt n b <$> rest.contify u jr nj
  | .lastIter x nt n b rest =>
    if n.mentions ⟨false, u.d⟩ || b.mentions ⟨false, u.d + 1⟩ then none else
    .lastIter x nt n b <$> rest.contify u jr nj
  | .forOf x l xs b rest =>
    if xs.mentions ⟨false, u.d⟩ || b.mentions ⟨false, u.d + 1⟩ then none else
    .forOf x l xs b <$> rest.contify u jr nj
/-- `contify` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.contify (u : Contify) {C M J J' : List JsTy} {k : JsEnd} {n : Nat}
    (jr : JsJRen J J') (nj : JsMem J' u.σ) : JsEnumArms C M J k n → Option (JsEnumArms C M J' k n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.contify u jr nj) (← rest.contify u jr nj)
/-- `contify` in the arms of a case analysis on a union. -/
partial def JsUnionArms.contify (u : Contify) {C M J J' : List JsTy} {k : JsEnd}
    {cs : List (List JsTy)} (jr : JsJRen J J') (nj : JsMem J' u.σ) :
    JsUnionArms C M J k cs → Option (JsUnionArms C M J' k cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.contify { u with d := u.d + us.length } jr nj) (← rest.contify u jr nj)
end

mutual
/-- The mutable variable a call of the constant `d` is first assigned to at the end of an
    iteration (`x = k(e);`), by its index where the walk started. -/
partial def JsBlock.tailAssign? {C M J : List JsTy} {k : JsEnd} (d dm : Nat) (thunk : Bool) :
    JsBlock C M J k → Option Nat
  | .assign x e .next =>
    if (e.callOf? d thunk).isSome && x.index ≥ dm then some (x.index - dm) else none
  | .const _ _ rest => rest.tailAssign? (d + 1) dm thunk
  | .letMut _ _ rest => rest.tailAssign? d (dm + 1) thunk
  | .assign _ _ rest | .forRange _ _ _ _ rest | .lastIter _ _ _ _ rest | .forOf _ _ _ _ rest =>
    rest.tailAssign? d dm thunk
  | .destructure (us := us) _ _ rest => rest.tailAssign? (d + us.length) dm thunk
  | .ite _ t e => (t.tailAssign? d dm thunk).orElse fun _ => e.tailAssign? d dm thunk
  | .join _ b rest => (b.tailAssign? d dm thunk).orElse fun _ => rest.tailAssign? (d + 1) dm thunk
  | .unionCases _ arms => arms.tailAssign? d dm thunk
  | _ => none
/-- `tailAssign?` of the first arm that has one. -/
partial def JsUnionArms.tailAssign? {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (d dm : Nat) (thunk : Bool) : JsUnionArms C M J k cs → Option Nat
  | .nil => none
  | .cons (us := us) _ b rest =>
    (b.tailAssign? (d + us.length) dm thunk).orElse fun _ => rest.tailAssign? d dm thunk
end

/-- A block that jumps to no join point, under any join points. -/
def JsBlock.anyJ {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M [] k) : Option (JsBlock C M J k) :=
  b.renameJ (fun {_} (x : JsMem [] _) => nomatch x)

/-- `const k = (x) => { B }; rest` where `rest` only calls `k` in tail position: `rest` jumping
    to a join point whose body is `B` (see above). -/
def contifyNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const h e rest) =>
    match e.lamInfo? with
    | none => b
    | some ⟨thunk, σ, ρ, B⟩ =>
      if !rest.mentions ⟨false, 0⟩ then b else
      let build (form : TailForm) (B' : JsBlock (σ :: C) M J k) : Option (JsBlock C M J k) := do
        let u : Contify := { d := 0, dm := 0, form, thunk, σ }
        let rest' ← rest.contify u (fun x => some (.succ x)) (.zero : JsMem (σ :: J) σ)
        let rest'' ← rest'.renameM JsRen.strengthen (fun x => some x)
        return .join h rest'' B'
      let viaRet : Option (JsBlock C M J k) :=
        if hk : k = .ret ρ then do
          let B' ← (hk ▸ B : JsBlock (σ :: C) M [] k).anyJ
          build .ret B'
        else none
      match viaRet with
      | some r => r
      | none =>
        if hk : k = .loop then
          match rest.tailAssign? 0 0 thunk with
          | some m =>
            match JsMem.ofIndex? M m ρ with
            | some acc =>
              match (hk ▸ B.retToNext acc : JsBlock (σ :: C) M [] k).anyJ with
              | some B' => (build (.assign m) B').getD b
              | none => b
            | none => b
          | none => b
        else b
  | b => b

/-! ## Assignments moved up -/

/-- `const y = e; acc = x;` (`x` bound before `y`) is `acc = x; const y = e;` when `e` does not
    mention `acc` (and no closure reads a mutable variable, `noCapture`). -/
def hoistAssignNode (noCapture : Bool) {C M J : List JsTy} {k : JsEnd} :
    JsBlock C M J k → JsBlock C M J k
  | b@(.const h e (.assign m (.cvar (.succ x)) rest)) =>
    if noCapture && !e.mentions ⟨true, m.index⟩ then .assign m (.cvar x) (.const h e rest) else b
  | b => b

/-! ## Record and union literals used once -/

/-- A record or union literal whose parts have no effect and cannot throw. -/
def JsExpr.isMovableLit {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : Bool :=
  match e with
  | .record_mk _ | .union_mk .. => e.discardable
  | _ => false

/-- `const x = { … }; rest` with `x` read once in `rest`, not in a loop or a closure, and no
    mutable variable of the literal assigned in `rest`: `rest` with the literal for `x`. -/
def inlineLitNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if !e.isMovableLit then b else
    let occs := rest.occs
    let uses := occs.filter (·.is ⟨false, 0⟩)
    let stable := e.occs.all fun o => !o.isMut || !occs.any fun r => r.write && r.is ⟨true, o.idx⟩
    if uses.size == 1 && !uses.any (·.again) && stable then rest.subst (JsSubst.inst e) else b
  | b => b

/-! ## Calls of known functions, returned -/

/-- `return ((x) => { B })(a);` with atoms for arguments: `B` with the arguments for the
    parameters (its `return`s return from the function). -/
def retBetaNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.ret (.app (.lam _ B) args)) =>
    if args.allAtoms then ((B.subst (JsSubst.params args)).anyJ).getD b else b
  | b => b

/-! ## All of them -/

/-- One step of the passes of this file and of `JsTerm.Passes.Unbox`, on a block whose parts
    are done already. -/
def tidyStep (noCapture : Bool) {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) :
    JsBlock C M J k :=
  let b := if noCapture then inlineOnceNode b else b
  let b := retBetaNode b
  let b := inlineLitNode (contifyNode b)
  let b := scalarNode (unboxNode b)
  let b := flattenJoinNode b
  let b := copyMutNode b
  let b := deadConstNode b
  let b := coalesceNode noCapture b
  let b := hoistAssignNode noCapture b
  tcoNode noCapture b

/-- The passes of this file and of `JsTerm.Passes.Unbox`, everywhere, then the clean-ups
    (`cleanup`, `peephole`), until nothing changes (at most `fuel` rounds). -/
def tidy {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) (fuel : Nat := 6) :
    JsBlock C M J k :=
  let noCapture := !b.capturesMut
  go noCapture fuel b (b.pretty "")
where
  /-- The rounds. -/
  go (noCapture : Bool) : Nat → JsBlock C M J k → String → JsBlock C M J k
    | 0, b, _ => b
    | n + 1, b, s =>
      let b' := peephole (cleanup (b.mapBU betaRw ⟨fun _ _ _ _ b => tidyStep noCapture b⟩))
      let s' := b'.pretty ""
      if s' == s then b' else go noCapture n b' s'

end MoreJs

end
