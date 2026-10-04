module

public import JsTerm.Lower.Tail

@[expose] public section

set_option autoImplicit false

/-!
# Loops over a `Bool` tag, unrolled

The functions of a `mutual` group of two functions recursing on a `Nat` (`testEven`/`testOdd`)
are each converted to the same counting-down loop over the whole group, whose first mutable
variable is a `Bool` *tag* saying which function the iteration runs (`JsTerm.Lower.FromTerm`,
`cTailLoop`):

```js
let p$1 = true; let p$2 = b._1; let p$3 = b._2; let j = n;
while (true) {
  if (j === 0) { return { _1: p$2, _2: p$3 }; }
  j--;
  if (p$1) { …; p$1 = false; p$2 = …; p$3 = …; } else { …; p$1 = true; p$2 = …; p$3 = …; }
}
```

Two rewrites of `JsTerm` remove the tag (a JavaScript-level fact: the tag is a mutable variable
of a loop, which `Term` does not have):

* **Unrolling** (`JsBlock.unrollTags?`): when every iteration that starts in the state `s₀` (the
  initial value of the tag) either ends the loop or goes on in a state that, one iteration
  later, is `s₀` again, the loop runs the two iterations in one step, the second one after a
  test of the counter in the middle of the step (`JsBlock.tick`); the tag is then always `s₀`
  at the start of a step, and is dropped:

  ```js
  while (true) {
    if (j === 0) { return …; }  j--;  (the arm of `true`)
    if (j === 0) { return …; }  j--;  (the arm of `false`)
  }
  ```

  The last assignments of the first iteration, of constants, are put off to the end of the
  second one (`JsPend`, `JsBlock.delay`): the second iteration and the base case in the middle
  read the constants themselves, so the step assigns each variable once
  (`const x = p$2 + 1; const y = p$1 + 2; if (j === 0) { return { _1: x, _2: y }; } j--;
  p$1 = y + 3; p$2 = x + 4;`).  A base case reading the tag reads the state it runs in.

* **Peeling** (`JsBlock.peelTop`): the other function of the pair runs one iteration of its own
  state, then calls the first function (whose loop starts in the state it goes on in), with
  arguments rebuilt from the variables of the loop (`TagInv`: the first function's variables
  must be initialised from its parameters, directly or field by field):

  ```js
  export const testOdd = (n, b) => {
    if (n === 0) { return b; }
    return testEven(n - 1, { _1: b._2 + 3, _2: b._1 + 4 });
  };
  ```

  The iteration run outside the loop has no mutable variable: each is replaced by its value
  (`JsBlock.peelB`), the test of the counter is a case analysis on its value
  (`JsBlock.natCase`), and a record literal of all the fields of a record of leaves taken
  apart is that record (`etaRecord`: `return b;`).

Both rewrites keep what each function computes: the unrolled loop runs the same iterations in
the same order (the tag it no longer tests has the value the test would have found), and the
peeled function runs the first iteration of its loop, then the loop of the other function from
the state that iteration reached, which (the two loops being the same code, up to the initial
tag) is the rest of its own loop.  Each rewrite gives up (`none`) on any shape it does not
recognise, and the loop is then printed as it is.
-/

namespace MoreJs

variable {S : JsSig}

/-! ## Helpers -/

/-- The value of a boolean literal. -/
def JsExpr.boolLit? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option Bool
  | .lit (.bool b) => some b
  | _ => none

/-- The renaming of `C` into `pushAll us C` (under the variables of a pattern). -/
def wkUnderAll {C : List JsTy} : (us : List JsTy) → JsRenM Id C (pushAll us C)
  | [] => fun x => x
  | _ :: us => fun x => wkUnderAll us (JsMem.succ x)

/-- `rest` is `return x;` of the constant `x` just bound (of type `τ`): then `τ = R`. -/
def JsBlock.retC0Eq? {C M J : List JsTy} {τ R : JsTy} :
    JsBlock S (τ :: C) M J (.ret R) → Option (PLift (τ = R))
  | .ret (.cvar .zero) => some ⟨rfl⟩
  | _ => none

/-- The renaming dropping the innermost variable (`none` for it). -/
def dropMut0Ren {M : List JsTy} {τ : JsTy} : JsRenM Option (τ :: M) M := fun x =>
  match x with
  | .zero => none
  | .succ y => some y

/-- Drop the innermost mutable variable, when the block does not mention it. -/
def JsBlock.dropMut0? {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (b : JsBlock S C (τ :: M) J k) :
    Option (JsBlock S C M J k) :=
  b.renameM (fun x => some x) dropMut0Ren

/-- A substitution of the variables `M` (constants or mutable variables) by expressions over
    the constants `C'` and the mutable variables `M'` (none by default). -/
abbrev JsMutSub (S : JsSig) (M C' : List JsTy) (M' : List JsTy := []) : Type :=
  ∀ {τ : JsTy}, JsMem M τ → JsExpr S C' M' τ

namespace JsMutSub

variable {M' : List JsTy}

/-- No variable. -/
def empty {C' : List JsTy} : JsMutSub S [] C' M' := fun {_} (y : JsMem [] _) => nomatch y

/-- The constants as themselves. -/
def ident {C : List JsTy} : JsMutSub S C C M' := fun y => .cvar y

/-- The mutable variables as themselves. -/
def identM {C M : List JsTy} : JsMutSub S M C M := fun y => .mvar y

/-- One more variable, of value `e`. -/
def push {M C' : List JsTy} {σ : JsTy} (sm : JsMutSub S M C' M') (e : JsExpr S C' M' σ) :
    JsMutSub S (σ :: M) C' M' := fun y =>
  match y with
  | .zero => e
  | .succ z => sm z

/-- The variable `x` of value `v` from now on. -/
def set {M C' : List JsTy} {σ : JsTy} (sm : JsMutSub S M C' M') (x : JsMem M σ)
    (v : JsExpr S C' M' σ) : JsMutSub S M C' M' := fun {τ} y =>
  if h : τ = σ then (if y.index == x.index then h ▸ v else sm y) else sm y

/-- The values renamed (moved to more constants). -/
def ren {M C' C'' : List JsTy} (r : JsRenM Id C' C'') (sm : JsMutSub S M C' M') :
    JsMutSub S M C'' M' :=
  fun y => Id.run ((sm y).renameM r JsRen.id)

/-- Under a new constant. -/
def wkC {M C' : List JsTy} {σ : JsTy} (sm : JsMutSub S M C' M') : JsMutSub S M (σ :: C') M' :=
  sm.ren JsRen.succ

/-- Under the variables of a pattern. -/
def wkAll {M C' : List JsTy} (us : List JsTy) (sm : JsMutSub S M C' M') :
    JsMutSub S M (pushAll us C') M' :=
  sm.ren (wkUnderAll us)

/-- Under a new constant, bound on both sides (to itself). -/
def lift {M C' : List JsTy} {σ : JsTy} (sm : JsMutSub S M C' M') :
    JsMutSub S (σ :: M) (σ :: C') M' :=
  push (wkC sm) (.cvar .zero)

/-- Under the variables of a pattern, bound on both sides (to themselves). -/
def liftAll {M C' : List JsTy} : (us : List JsTy) → JsMutSub S M C' M' →
    JsMutSub S (pushAll us M) (pushAll us C') M'
  | [], sm => sm
  | _ :: us, sm => liftAll us (lift sm)

end JsMutSub

mutual
/-- The expression, its constants replaced by their values `sc` and its mutable variables by
    their values `sm` (`none` for a closure, which would read the variables when it is
    called). -/
partial def JsExpr.substMut {C M C' M' : List JsTy} (sc : JsMutSub S C C' M')
    (sm : JsMutSub S M C' M') {τ : JsTy} : JsExpr S C M τ → Option (JsExpr S C' M' τ)
  | .cvar x => some (sc x)
  | .mvar x => some (sm x)
  | .lit l => some (.lit l)
  | .imported op as => .imported op <$> as.substMut sc sm
  | .inlined op as => .inlined op <$> as.substMut sc sm
  | .unreachable t => some (.unreachable t)
  | .app f as => return .app (← f.substMut sc sm) (← as.substMut sc sm)
  | .lam .. => none
  | .record_mk fs => .record_mk <$> fs.substMut sc sm
  | .union_mk ix as => .union_mk ix <$> as.substMut sc sm
  | .enum_mk n s i => some (.enum_mk n s i)
  | .enumIndex nt e => .enumIndex nt <$> e.substMut sc sm
  | .enumEq a b => return .enumEq (← a.substMut sc sm) (← b.substMut sc sm)
  | .boolCmp op a b => return .boolCmp op (← a.substMut sc sm) (← b.substMut sc sm)
  | .index l nt a i => return .index l nt (← a.substMut sc sm) (← i.substMut sc sm)
  | .indexOr l nt a i d =>
    return .indexOr l nt (← a.substMut sc sm) (← i.substMut sc sm) (← d.substMut sc sm)
  | .array_mk l ps => .array_mk l <$> ps.substMut sc sm
  | .list_mk ps => .list_mk <$> ps.substMut sc sm
  | .cond c a b => return .cond (← c.substMut sc sm) (← a.substMut sc sm) (← b.substMut sc sm)
  | .listOp op as => .listOp op <$> as.substMut sc sm
  | .fold i e => .fold i <$> e.substMut sc sm
  | .unfold i e => .unfold i <$> e.substMut sc sm
  | .global n => some (.global n)
/-- `substMut` of arguments. -/
partial def JsArgs.substMut {C M C' M' : List JsTy} (sc : JsMutSub S C C' M')
    (sm : JsMutSub S M C' M') {σs : List JsTy} : JsArgs S C M σs → Option (JsArgs S C' M' σs)
  | .nil => some .nil
  | .cons a as => return .cons (← a.substMut sc sm) (← as.substMut sc sm)
/-- `substMut` of the parts of an array literal. -/
partial def JsParts.substMut {C M C' M' : List JsTy} (sc : JsMutSub S C C' M')
    (sm : JsMutSub S M C' M') {A E : JsTy} : JsParts S C M A E → Option (JsParts S C' M' A E)
  | .nil => some .nil
  | .elem e rest => return .elem (← e.substMut sc sm) (← rest.substMut sc sm)
  | .spread a rest => return .spread (← a.substMut sc sm) (← rest.substMut sc sm)
end

/-! ## Assignments put off -/

/-- Mutable variables given a new value that is not assigned yet: the assignments put off, of
    values that no assignment changes (constants and literals). -/
abbrev JsPend (S : JsSig) (C M : List JsTy) : Type :=
  List ((σ : JsTy) × JsMem M σ × JsExpr S C M σ)

namespace JsPend

/-- Under a new constant. -/
def wkC {C M : List JsTy} {σ : JsTy} (p : JsPend S C M) : JsPend S (σ :: C) M :=
  p.map fun ⟨τ, x, e⟩ => ⟨τ, x, e.wkC⟩

/-- Under the variables of a pattern. -/
def wkAll {C M : List JsTy} (us : List JsTy) (p : JsPend S C M) : JsPend S (pushAll us C) M :=
  p.map fun ⟨τ, x, e⟩ => ⟨τ, x, Id.run (e.renameM (wkUnderAll us) JsRen.id)⟩

/-- The value of each mutable variable: its new value if it has one, else itself. -/
def sub {C M : List JsTy} (p : JsPend S C M) : JsMutSub S M C M := fun {τ} y =>
  match p.find? (·.2.1.index == y.index) with
  | some ⟨σ, _, e⟩ => if h : σ = τ then h ▸ e else .mvar y
  | none => .mvar y

/-- Without the variable `x` (assigned now). -/
def drop {C M : List JsTy} {σ : JsTy} (p : JsPend S C M) (x : JsMem M σ) : JsPend S C M :=
  p.filter (·.2.1.index != x.index)

/-- The assignments put off, then the block. -/
def flush {C M J : List JsTy} {k : JsEnd} (p : JsPend S C M) (b : JsBlock S C M J k) :
    JsBlock S C M J k :=
  p.foldr (fun ⟨_, x, e⟩ b => .assign x e b) b

end JsPend

/-- Is the expression a constant or a literal (a value no assignment changes)? -/
def JsExpr.isConstAtom {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .lit _ | .enum_mk .. => true
  | _ => false

/-- Is the block assignments, then the end of the iteration? -/
def JsBlock.assignsNext {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Bool
  | .next => true
  | .assign _ _ r => r.assignsNext
  | _ => false

mutual
/-- The block (in the body of a loop) run after the assignments put off `p`: every read of such
    a variable reads its new value, an assignment of one ends its putting off, and the end of the
    iteration does the assignments still put off first (`none` on a statement it does not
    handle). -/
partial def JsBlock.delay {C M J : List JsTy} (p : JsPend S C M) :
    JsBlock S C M J .loop → Option (JsBlock S C M J .loop)
  | .next => some (p.flush .next)
  | .jump j e => return .jump j (← e.substMut JsMutSub.ident p.sub)
  | .throw m => some (.throw m)
  | .const x e rest => return .const x (← e.substMut JsMutSub.ident p.sub) (← rest.delay p.wkC)
  | .destructure (us := us) e sel rest =>
    return .destructure (← e.substMut JsMutSub.ident p.sub) sel (← rest.delay (p.wkAll us))
  | .assign x e rest =>
    return .assign x (← e.substMut JsMutSub.ident p.sub) (← rest.delay (p.drop x))
  | .ite c t e =>
    return .ite (← c.substMut JsMutSub.ident p.sub) (← t.delay p) (← e.delay p)
  | .enumCases e arms => return .enumCases (← e.substMut JsMutSub.ident p.sub) (← arms.delay p)
  | .unionCases e arms => return .unionCases (← e.substMut JsMutSub.ident p.sub) (← arms.delay p)
  | .tick nt j b rest => return .tick nt j (← b.delay p) (← rest.delay p)
  | _ => none
/-- `delay` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.delay {C M J : List JsTy} {n : Nat} (p : JsPend S C M) :
    JsEnumArms S C M J .loop n → Option (JsEnumArms S C M J .loop n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.delay p) (← rest.delay p)
/-- `delay` in the arms of a case analysis on a union. -/
partial def JsUnionArms.delay {C M J : List JsTy} {cs : List (List JsTy)} (p : JsPend S C M) :
    JsUnionArms S C M J .loop cs → Option (JsUnionArms S C M J .loop cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest => return .cons sel (← b.delay (p.wkAll us)) (← rest.delay p)
end

/-! ## Unrolling -/

/-- The renaming dropping the innermost constant (`none` for it). -/
def dropC0Ren {C : List JsTy} {τ : JsTy} : JsRenM Option (τ :: C) C := fun x =>
  match x with
  | .zero => none
  | .succ y => some y

mutual
/-- The block (the arm of an iteration of a loop, over the constants `C`, which extend the
    constants `C0` of the loop by `ren`) with every assignment of the tag (the mutable variable
    of index `tag`, assigned only boolean literals, or constants holding one: `lits`, by their
    levels) dropped, and every end of the iteration replaced by `kont` of the value the tag
    then has (`cur`: its value so far) and of the assignments put off (`pend`: the assignments
    of constants and literals just before the end of the iteration).  A constant holding a
    boolean literal that is no longer read is dropped. -/
partial def JsBlock.thenNext {C0 C M J : List JsTy} (tag : Nat) (cur : Bool) (lits : List (Nat × Bool))
    (pend : JsPend S C M) (ren : JsRenM Id C0 C)
    (kont : {C' : List JsTy} → JsRenM Id C0 C' → Bool → JsPend S C' M →
      Option (JsBlock S C' M J .loop)) :
    JsBlock S C M J .loop → Option (JsBlock S C M J .loop)
  | .next => kont ren cur pend
  | .jump j e => some (pend.flush (.jump j e))
  | .throw m => some (.throw m)
  | .const x e rest => do
    let lits' := match e.boolLit? with
      | some b => (C.length, b) :: lits
      | none => lits
    let r ← rest.thenNext tag cur lits' pend.wkC (fun v => JsMem.succ (ren v)) kont
    if e.boolLit?.isSome && !r.mentions ⟨false, 0⟩ then r.renameM dropC0Ren (fun y => some y)
    else some (.const x e r)
  | .destructure (us := us) e sel rest =>
    (.destructure e sel ·) <$>
      rest.thenNext tag cur lits (pend.wkAll us) (fun v => wkUnderAll us (ren v)) kont
  | .assign x e rest =>
    if x.index == tag then do
      let c ← e.boolLit? <|> (match e with
        | .cvar v => lits.lookup (C.length - 1 - v.index)
        | _ => none)
      rest.thenNext tag c lits pend ren kont
    else if rest.assignsNext then do
      -- one of the last assignments of the iteration: put off when its value is a constant or
      -- a literal (it reads the new values of those put off before)
      let e' ← e.substMut JsMutSub.ident pend.sub
      if e'.isConstAtom then rest.thenNext tag cur lits (pend.drop x ++ [⟨_, x, e'⟩]) ren kont
      else (.assign x e' ·) <$> rest.thenNext tag cur lits (pend.drop x) ren kont
    else (.assign x e ·) <$> rest.thenNext tag cur lits pend ren kont
  | .ite c t e =>
    return .ite c (← t.thenNext tag cur lits pend ren kont) (← e.thenNext tag cur lits pend ren kont)
  | .enumCases e arms => (.enumCases e ·) <$> arms.thenNext tag cur lits pend ren kont
  | .unionCases e arms => (.unionCases e ·) <$> arms.thenNext tag cur lits pend ren kont
  | .tick nt j b rest =>
    return .tick nt j (← b.thenNext tag cur lits pend ren kont)
      (← rest.thenNext tag cur lits pend ren kont)
  | .natCase x nt n z s =>
    return .natCase x nt n (← z.thenNext tag cur lits pend ren kont)
      (← s.thenNext tag cur lits pend.wkC (fun v => JsMem.succ (ren v)) kont)
  | _ => none
/-- `thenNext` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.thenNext {C0 C M J : List JsTy} {n : Nat} (tag : Nat) (cur : Bool)
    (lits : List (Nat × Bool)) (pend : JsPend S C M) (ren : JsRenM Id C0 C)
    (kont : {C' : List JsTy} → JsRenM Id C0 C' → Bool → JsPend S C' M →
      Option (JsBlock S C' M J .loop)) :
    JsEnumArms S C M J .loop n → Option (JsEnumArms S C M J .loop n)
  | .nil => some .nil
  | .cons b rest =>
    return .cons (← b.thenNext tag cur lits pend ren kont)
      (← rest.thenNext tag cur lits pend ren kont)
/-- `thenNext` in the arms of a case analysis on a union. -/
partial def JsUnionArms.thenNext {C0 C M J : List JsTy} {cs : List (List JsTy)} (tag : Nat)
    (cur : Bool) (lits : List (Nat × Bool)) (pend : JsPend S C M) (ren : JsRenM Id C0 C)
    (kont : {C' : List JsTy} → JsRenM Id C0 C' → Bool → JsPend S C' M →
      Option (JsBlock S C' M J .loop)) :
    JsUnionArms S C M J .loop cs → Option (JsUnionArms S C M J .loop cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel
      (← b.thenNext tag cur lits (pend.wkAll us) (fun v => wkUnderAll us (ren v)) kont)
      (← rest.thenNext tag cur lits pend ren kont)
end

/-- The step `if (tag) { a } else { b }` of a counting-down loop (the tag, of index `t` among
    the mutable variables of the step, read nowhere else and assigned only literals): the arms. -/
def JsBlock.tagArms? {C M J : List JsTy} (t : Nat) :
    JsBlock S C M J .loop → Option (JsBlock S C M J .loop × JsBlock S C M J .loop)
  | .ite (.mvar v) a b =>
    let onlyWrites (blk : JsBlock S C M J .loop) : Bool :=
      blk.occs.all fun o => !(o.isMut && o.idx == t) || (o.write && !o.again && !o.inClosure)
    if v.index == t && onlyWrites a && onlyWrites b then some (a, b) else none
  | _ => none

/-- The block, whose mutable variable of index `tag` is the tag of the counting-down loop that
    follows (after constants, patterns and more mutable variables), with the loop unrolled
    for the initial state `s0` of the tag, and the tag never assigned. -/
partial def JsBlock.unrollAt {C M J : List JsTy} {k : JsEnd} (tag : Nat) (s0 : Bool) :
    JsBlock S C M J k → Option (JsBlock S C M J k)
  | .const x e rest => do
    if e.mentions ⟨true, tag⟩ then none
    (.const x e ·) <$> rest.unrollAt tag s0
  | .destructure e sel rest => do
    if e.mentions ⟨true, tag⟩ then none
    (.destructure e sel ·) <$> rest.unrollAt tag s0
  | .letMut x e rest => do
    if e.mentions ⟨true, tag⟩ then none
    (.letMut x e ·) <$> rest.unrollAt (tag + 1) s0
  | .countdown (N := N) x nt n base step rest => do
    -- the tag, under the counter
    let t := tag + 1
    if n.mentions ⟨true, tag⟩ || rest.mentions ⟨true, tag⟩ then none
    let (a, b) ← step.tagArms? t
    -- the base case reads the tag as the state it runs in: `s0` at the start of a step, the
    -- state of the second iteration in the middle
    let tagM ← JsMem.ofIndex? (N :: M) t (.terminal .bool)
    let base0 ← base.delay [⟨_, tagM, .lit (.bool s0)⟩]
    let arm (s : Bool) := if s then a else b
    let step' ← (arm s0).thenNext t s0 [] [] JsRen.id fun ren c pend =>
      if c == s0 then some (pend.flush .next)
      else do
        -- the second iteration, after a test of the counter: the variables the first one
        -- assigned last are read as their new values (the assignments put off to its end)
        let base' ← (Id.run (base.renameM ren JsRen.id)).delay
          (pend ++ [⟨_, tagM, .lit (.bool c)⟩])
        let arm' := Id.run ((arm c).renameM ren JsRen.id)
        let rest' ← arm'.thenNext t c [] [] JsRen.id fun _ c' pend' =>
          if c' == s0 then some (pend'.flush .next) else none
        some (.tick nt .zero base' (← rest'.delay pend))
    some (.countdown x nt n base0 step' rest)
  | _ => none

/-- The block (the body of a function) with its loop over a `Bool` tag unrolled (the tag the
    first mutable variable, initialised to a literal, of the statements before the loop), or
    `none` when it has no such loop or the loop cannot be unrolled. -/
partial def JsBlock.unrollTags? {C M J : List JsTy} {k : JsEnd} :
    JsBlock S C M J k → Option (JsBlock S C M J k)
  | .letMut _ e rest => do
    let b0 ← e.boolLit?
    let r ← rest.unrollAt 0 b0
    r.dropMut0?
  | .const x e rest => (.const x e ·) <$> rest.unrollTags?
  | .destructure e sel rest => (.destructure e sel ·) <$> rest.unrollTags?
  | _ => none

/-! ## Peeling -/

/-- Bind a value for the rest: the value itself when it is an atom (it can be repeated), else
    a new constant `const x = e;` holding it. -/
def bindAtom {C' : List JsTy} {σ R : JsTy} (hint : String) (e : JsExpr S C' [] σ)
    (k : (C2 : List JsTy) → JsRenM Id C' C2 → JsExpr S C2 [] σ → Option (JsBlock S C2 [] [] (.ret R))) :
    Option (JsBlock S C' [] [] (.ret R)) :=
  if e.isAtom then k C' JsRen.id e
  else (.const hint e ·) <$> k (σ :: C') JsRen.succ (.cvar .zero)

mutual
/-- One iteration of a loop (the step or the base case, over the mutable variables `M` of the
    loop) run once, outside the loop, as the end of a function: the constants and the mutable
    variables are replaced by their values (`sc`, `sm`; a constant or an assignment whose value
    is not an atom is a new constant), the exit of the loop (the jump to its join point)
    returns the value, a test of the counter (`tick`) is a case analysis on its value, and the
    end of the iteration is `onNext` of the values of the variables then. -/
partial def JsBlock.peelB {C M C' : List JsTy} {R : JsTy} (sc : JsMutSub S C C') (sm : JsMutSub S M C')
    (onNext : {C'' : List JsTy} → JsMutSub S M C'' → Option (JsBlock S C'' [] [] (.ret R))) :
    JsBlock S C M [R] .loop → Option (JsBlock S C' [] [] (.ret R))
  | .next => onNext sm
  | .jump j e => match j with
    | .zero => do return .ret (← e.substMut sc sm)
    | .succ m => nomatch m
  | .throw m => some (.throw m)
  | .const x e rest => do
    let e' ← e.substMut sc sm
    if e'.isAtom then rest.peelB (sc.push e') sm onNext
    else (.const x e' ·) <$> rest.peelB sc.lift sm.wkC onNext
  | .destructure (us := us) e sel rest => do
    let e' ← e.substMut sc sm
    (.destructure e' sel ·) <$> rest.peelB (sc.liftAll us) (sm.wkAll us) onNext
  | .assign x e rest => do
    let e' ← e.substMut sc sm
    if e'.isAtom then rest.peelB sc (sm.set x e') onNext
    else (.const "x" e' ·) <$> rest.peelB sc.wkC (JsMutSub.set (JsMutSub.wkC sm) x (.cvar .zero)) onNext
  | .ite c t e => return .ite (← c.substMut sc sm) (← t.peelB sc sm onNext) (← e.peelB sc sm onNext)
  | .enumCases e arms => return .enumCases (← e.substMut sc sm) (← arms.peelB sc sm onNext)
  | .unionCases e arms => return .unionCases (← e.substMut sc sm) (← arms.peelB sc sm onNext)
  | .tick nt j b rest => do
    let v := sm j
    return .natCase "j" nt v (← b.peelB sc sm onNext)
      (← rest.peelB sc.wkC (JsMutSub.set (JsMutSub.wkC sm) j (.cvar .zero)) onNext)
  | _ => none
/-- `peelB` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.peelB {C M C' : List JsTy} {R : JsTy} {n : Nat} (sc : JsMutSub S C C')
    (sm : JsMutSub S M C')
    (onNext : {C'' : List JsTy} → JsMutSub S M C'' → Option (JsBlock S C'' [] [] (.ret R))) :
    JsEnumArms S C M [R] .loop n → Option (JsEnumArms S C' [] [] (.ret R) n)
  | .nil => some .nil
  | .cons b rest => return .cons (← b.peelB sc sm onNext) (← rest.peelB sc sm onNext)
/-- `peelB` in the arms of a case analysis on a union. -/
partial def JsUnionArms.peelB {C M C' : List JsTy} {R : JsTy} {cs : List (List JsTy)}
    (sc : JsMutSub S C C') (sm : JsMutSub S M C')
    (onNext : {C'' : List JsTy} → JsMutSub S M C'' → Option (JsBlock S C'' [] [] (.ret R))) :
    JsUnionArms S C M [R] .loop cs → Option (JsUnionArms S C' [] [] (.ret R) cs)
  | .nil => some .nil
  | .cons (us := us) sel b rest =>
    return .cons sel (← b.peelB (sc.liftAll us) (sm.wkAll us) onNext)
      (← rest.peelB sc sm onNext)
end

/-- Are the fields all leaves (numbers, booleans, strings, enums)? -/
def scalarFields (ts : List JsTy) : Bool :=
  ts.all fun | .terminal _ => true | .enum _ _ => true | _ => false

/-- A record literal of the fields of a record taken wholly apart (`eta`: the level of the
    constant holding the record, and the levels of the constants holding its fields, in order)
    is that record (its fields are leaves: sharing it is not seen). -/
def etaRecord {C' M' : List JsTy} {τ : JsTy} (eta : List (Nat × List Nat)) (e : JsExpr S C' M' τ) :
    JsExpr S C' M' τ :=
  (go e).getD e
where
  /-- The record, if the expression is a literal of its fields. -/
  go {τ : JsTy} : JsExpr S C' M' τ → Option (JsExpr S C' M' τ)
    | .record_mk fs => do
      let ls ← (fs.toList.map fun ⟨_, a⟩ => match a with
        | .cvar v => some (C'.length - 1 - v.index)
        | _ => none).mapM id
      let (src, _) ← eta.find? (·.2 == ls)
      let x ← JsMem.ofIndex? C' (C'.length - 1 - src) _
      some (.cvar x)
    | _ => none

/-- The body of a function whose loop over a `Bool` tag (the first mutable variable, of initial
    value `cg`) is run for one iteration only, outside any loop, the end of that iteration
    being `mkCall` of the values of the variables of the loop then (the counter innermost, the
    tag outermost).  `eta`: the records taken wholly apart (`etaRecord`), by levels. -/
partial def JsBlock.peelTop {C M C' : List JsTy} {R : JsTy} (cg : Bool)
    (mkCall : {C'' M' : List JsTy} → JsMutSub S M' C'' → Option (JsBlock S C'' [] [] (.ret R)))
    (eta : List (Nat × List Nat)) (sc : JsMutSub S C C') (sm : JsMutSub S M C') :
    JsBlock S C M [] (.ret R) → Option (JsBlock S C' [] [] (.ret R))
  | .const x e rest => do
    let e' ← e.substMut sc sm
    bindAtom x e' fun _ r v =>
      rest.peelTop cg mkCall eta (JsMutSub.push (JsMutSub.ren r sc) v) (JsMutSub.ren r sm)
  | .destructure (id := id) (args := args) (us := us) e sel rest => do
    let e' ← e.substMut sc sm
    let fs := S.fieldsOf id args
    let n := sel.binds.length
    let eta' := match e' with
      | .cvar v =>
        if n == fs.length && n > 0 && scalarFields fs then
          (C'.length - 1 - v.index, (List.range n).map (C'.length + ·)) :: eta
        else eta
      | _ => eta
    (.destructure e' sel ·) <$> rest.peelTop cg mkCall eta' (sc.liftAll us) (sm.wkAll us)
  | .letMut x e rest => do
    let e' ← e.substMut sc sm
    bindAtom x e' fun _ r v =>
      rest.peelTop cg mkCall eta (JsMutSub.ren r sc) (JsMutSub.push (JsMutSub.ren r sm) v)
  | .countdown x nt n base step rest => do
    let ⟨h⟩ ← rest.retC0Eq?
    -- the tag is the outermost mutable variable, under the counter
    let (a, b) ← step.tagArms? M.length
    let arm := if cg then a else b
    let n' ← n.substMut sc sm
    bindAtom "n" n' fun _ r n2 => do
      let sc' : JsMutSub S C _ := JsMutSub.ren r sc
      let sm' : JsMutSub S M _ := JsMutSub.ren r sm
      let zero ← (h ▸ base).peelB sc' (JsMutSub.push sm' n2) fun _ => none
      let zero := match zero with
        | .ret e => .ret (etaRecord eta e)
        | z => z
      let succ ← (h ▸ arm).peelB (JsMutSub.wkC sc') (JsMutSub.push (JsMutSub.wkC sm') (.cvar .zero)) mkCall
      some (.natCase x nt n2 zero succ)
  | _ => none

/-! ## Rebuilding the arguments of a function from the variables of its loop -/

/-- Where the argument of a parameter of a function whose body is a loop comes from, given
    the variables of the loop (`TagInv`): the counter, a variable of the loop (by its level:
    its position from the outermost, `0` the tag), the record of the fields of some variables
    of the loop, or the parameter itself (a parameter the loop never changes). -/
inductive ParamSrc where
  | counter
  | loopVar (lvl : Nat)
  | record (lvls : List Nat)
  | same (lvl : Nat)
  deriving Inhabited, Repr

/-- What the statements in front of the loop of a function do with its parameters. -/
structure TagInv where
  /-- The constants (by level) holding a field of a parameter: the parameter's level, the
      field's position, how many times the constant is read. -/
  fieldOf : List (Nat × Nat × Nat × Nat) := []
  /-- The parameters taken apart (by level). -/
  destructured : List Nat := []
  /-- The variables of the loop (by level) initialised with a constant (by level). -/
  inits : List (Nat × Nat) := []
  /-- The constant (by level) the counter starts from. -/
  counter : Option Nat := none

/-- How many times the block reads the constant of index `i`. -/
def JsBlock.cReads {C M J : List JsTy} {k : JsEnd} (b : JsBlock S C M J k) (i : Nat) : Nat :=
  (b.occs.filter fun o => !o.isMut && o.idx == i).size

/-- Walk the statements in front of the loop of a function (patterns taking a parameter wholly
    apart, the tag, variables initialised with a constant, the loop counting down from a
    constant). -/
partial def JsBlock.tagInv {C M J : List JsTy} {k : JsEnd} (acc : TagInv) :
    JsBlock S C M J k → Option TagInv
  | .destructure (id := id) (args := args) e sel rest => do
    let .cvar v := e | none
    let n := sel.binds.length
    unless n == (S.fieldsOf id args).length do none
    let lv := C.length - 1 - v.index
    let fs := (List.range n).map fun j => (C.length + j, lv, j, rest.cReads (n - 1 - j))
    rest.tagInv { acc with fieldOf := acc.fieldOf ++ fs, destructured := lv :: acc.destructured }
  | .letMut _ e rest =>
    if M.length == 0 then do
      let _ ← e.boolLit?
      rest.tagInv acc
    else do
      let .cvar v := e | none
      rest.tagInv { acc with inits := acc.inits ++ [(M.length, C.length - 1 - v.index)] }
  | .countdown _ _ n _ _ _ => do
    let .cvar v := n | none
    some { acc with counter := some (C.length - 1 - v.index) }
  | _ => none

/-- Where the argument of each parameter of a function (of `np` parameters, whose body is
    `body`) comes from, so that calling it on these arguments starts its loop from the values
    the variables of the loop have (`none` when the parameters are not given to the variables of
    the loop as they are, or when the loop reads such a parameter otherwise). -/
def paramSources {C M J : List JsTy} {k : JsEnd} (np : Nat) (body : JsBlock S C M J k) :
    Option (List ParamSrc) := do
  let inv ← body.tagInv {}
  let reads (p : Nat) : Nat := body.cReads (C.length - 1 - p)
  let initOf (c : Nat) : Option Nat := (inv.inits.find? (·.2 == c)).map (·.1)
  (List.range np).mapM fun p => do
    if inv.counter == some p then
      if reads p == 1 then some .counter else none
    else if let some m := initOf p then
      if reads p == 1 then some (.loopVar m) else none
    else if inv.destructured.contains p then
      let fs := inv.fieldOf.filter (·.2.1 == p)
      let ms := fs.map fun (c, _, _, _) => initOf c
      if ms.all (·.isNone) then some (.same p)
      else do
        unless reads p == 1 && fs.all (·.2.2.2 == 1) do none
        let ms ← ms.mapM id
        some (.record ms)
    else some (.same p)

mutual
/-- The arguments of the parameters of types `ts`, from their sources (`paramSources`) and the
    values `sm` of the variables of the loop (the counter innermost), over constants whose
    outermost are the parameters. -/
partial def buildArgs {C'' M' : List JsTy} (sm : JsMutSub S M' C'') :
    List ParamSrc → (ts : List JsTy) → Option (JsArgs S C'' [] ts)
  | [], [] => some .nil
  | src :: srcs, t :: ts => do
    let a ← buildArg sm src t
    return .cons a (← buildArgs sm srcs ts)
  | _, _ => none
/-- One argument of `buildArgs`. -/
partial def buildArg {C'' M' : List JsTy} (sm : JsMutSub S M' C'') :
    ParamSrc → (t : JsTy) → Option (JsExpr S C'' [] t)
  | .counter, t => do
    let x ← JsMem.ofIndex? M' 0 t
    some (sm x)
  | .loopVar l, t => do
    let x ← JsMem.ofIndex? M' (M'.length - 1 - l) t
    some (sm x)
  | .same l, t => do
    let x ← JsMem.ofIndex? C'' (C''.length - 1 - l) t
    some (.cvar x)
  | .record ls, .obj id args => do
    let fs ← buildArgs sm (ls.map .loopVar) (S.fieldsOf id args)
    some (.record_mk fs)
  | .record _, _ => none
end

/-- A function whose body is a loop over a `Bool` tag, with the loop unrolled (`none` when it
    has no such loop, or it cannot be unrolled). -/
def JsFun.unrollTag? (f : JsFun) : Option JsFun := do
  let body ← f.body.unrollTags?
  return { f with body }

/-- The function `g`, whose body is a loop over a `Bool` tag of initial value `cg`, as one
    iteration of its loop followed by a call of the function `f` (the same loop, starting with
    the tag `cf`), when every iteration of `g`'s first state ends the loop or goes on in the
    state `cf`, and the arguments of `f` can be rebuilt from the variables of the loop. -/
def JsFun.peelInto? (g f : JsFun) (cg cf : Bool) : Option JsFun := do
  unless g.params == f.params && g.ret == f.ret do none
  let ts := f.params.map (·.2)
  let srcs ← paramSources ts.length f.body
  let mkCall : {C'' M' : List JsTy} → JsMutSub g.sig M' C'' →
      Option (JsBlock g.sig C'' [] [] (.ret g.ret)) := fun {_ M'} sm => do
    -- the tag, the outermost variable of the loop, must then be `cf`
    let tagX ← JsMem.ofIndex? M' (M'.length - 1) (.terminal .bool)
    unless (sm tagX).boolLit? == some cf do none
    let args ← buildArgs sm srcs ts
    some (.ret (.app (.global (τ := .fn ts g.ret) f.name) args))
  let body ← g.body.peelTop cg mkCall [] JsMutSub.ident JsMutSub.empty
  return { g with body }

end MoreJs

end
