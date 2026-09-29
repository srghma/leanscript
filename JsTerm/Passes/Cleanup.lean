module

public import JsTerm.Passes.Simplify

@[expose] public section

set_option autoImplicit false

/-!
# Copies and self-assignments

Two more clean-ups of `JsTerm`, type-preserving like the ones of `JsTerm.Passes.Simplify`,
applied bottom-up by `JsBlock.mapBU`:

* **copy propagation** (`copyPropNode`): `const y = e; rest` where `e` is a copy — a constant,
  a module constant (`const k$1 = $k1;`, left by hoisting), an enum, a boolean, `number` or
  `BigInt` literal — is `rest` with `e` for `y`.  A string literal is propagated only into a
  single use, not inside a loop or a closure (so that it is never written twice).  A copy of a
  *mutable* variable, `const y = acc;`, is propagated only when `rest` never assigns `acc` and
  does not read `y` inside a closure (a closure can be called after `acc` is reassigned outside
  of `rest`: `const a = acc; acc = (x) => a(x);` must keep `a`);
* **self-assignments** (`selfAssignNode`): `x = x;` is dropped.

Each rewrite only replaces a read of a variable by an equal value, or drops a statement with no
effect, so the printed JavaScript computes the same results.
-/

namespace MoreJs

/-- Is the literal cheap to write more than once (a boolean, a `number`, a `BigInt`)? -/
def JsLit.isSmall {t : JsTerminalTy} (l : JsLit t) : Bool :=
  match l.shape with
  | .bool _ | .number _ | .bigint _ => true
  | _ => false

/-- Is the literal a string? -/
def JsLit.isString {t : JsTerminalTy} (l : JsLit t) : Bool :=
  match l.shape with
  | .str _ => true
  | _ => false

/-- May `const y = e; rest` be replaced by `rest` with `e` for `y`? (see above) -/
def copyPropagates {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    (e : JsExpr C M τ) (rest : JsBlock (τ :: C) M J k) : Bool :=
  match e with
  | .cvar _ | .global .. | .enum_mk .. => true
  | .lit l =>
    l.isSmall ||
      (l.isString &&
        (let uses := rest.occs.filter (·.is ⟨false, 0⟩)
         uses.size ≤ 1 && !uses.any (·.again)))
  | .mvar m =>
    let occs := rest.occs
    !occs.any (fun o => o.write && o.is ⟨true, m.index⟩) &&
      !occs.any (fun o => o.inClosure && o.is ⟨false, 0⟩)
  | _ => false

/-- Copy propagation, on one block (see above). -/
def copyPropNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if copyPropagates e rest then rest.subst (JsSubst.inst e) else b
  | b => b

/-- `x = x;` dropped. -/
def selfAssignNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.assign x (.mvar y) rest) => if x.index == y.index then rest else b
  | b => b

/-! ## Rebuilt unions -/

/-- The renaming that skips the variables of a pattern. -/
def JsRen.skipAll {Γ : List JsTy} : (us : List JsTy) → JsRenM Id Γ (pushAll us Γ)
  | [] => fun x => x
  | _ :: us => fun x => JsRen.skipAll us (JsMem.succ x)

/-- Does the pattern keep every field? -/
def JsSel.keepsAll {ts us : List JsTy} : JsSel ts us → Bool
  | .nil => true
  | .keep _ s => s.keepsAll
  | .skip _ => false

/-- Are the arguments the `n` fields a pattern keeping every field binds, in order (from the
    `j`-th)? -/
def JsArgs.areFields {C M σs : List JsTy} (n j : Nat) : JsArgs C M σs → Bool
  | .nil => j == n
  | .cons (.cvar x) as => x.index + 1 + j == n && as.areFields n (j + 1)
  | .cons _ _ => false

/-- `e` is the constructor `i` of the fields `0 … n-1` (as a pattern keeping every field binds
    them): the value `s` it takes apart, when it has the same type. -/
def rebuiltAs {C M : List JsTy} {σ τ : JsTy} (s : JsExpr C M σ) (i n : Nat) (e : JsExpr C M τ) :
    JsExpr C M τ :=
  let isRebuild : Bool := match e with
    | .union_mk ix args => ix.index == i && args.areFields n 0
    | _ => false
  if isRebuild then (if h : σ = τ then h ▸ s else e) else e

/-- `rebuiltAs` in the first statement of a block. -/
def rebuildHead {C M J : List JsTy} {σ : JsTy} {k : JsEnd} (s : JsExpr C M σ) (i n : Nat) :
    JsBlock C M J k → JsBlock C M J k
  | .ret e => .ret (rebuiltAs s i n e)
  | .jump j e => .jump j (rebuiltAs s i n e)
  | .assign x e rest => .assign x (rebuiltAs s i n e) rest
  | .const x e rest => .const x (rebuiltAs s i n e) rest
  | b => b

/-- `rebuildHead` in each arm of a case analysis on `s` (the arms from the `i`-th). -/
def JsUnionArms.rebuild {C M J : List JsTy} {σ : JsTy} {k : JsEnd} (s : JsExpr C M σ) (i : Nat) :
    {cs : List (List JsTy)} → JsUnionArms C M J k cs → JsUnionArms C M J k cs
  | _, .nil => .nil
  | _, .cons (us := us) sel b rest =>
    let b := if sel.keepsAll then
      rebuildHead (Id.run (s.renameM (JsRen.skipAll us) JsRen.id)) i us.length b else b
    .cons sel b (rest.rebuild s (i + 1))

/-- In a case analysis on a variable, an arm that starts by rebuilding the value it takes
    apart (`if (x.tag === 0) { const { _1: f } = x; return { tag: 0, _1: f }; }`) uses the
    variable instead (`return x;`).  The variable is not reassigned in between. -/
def rebuildNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.unionCases e arms) => if e.isAtom then .unionCases e (arms.rebuild e 0) else b
  | b => b

/-! ## Unused fields -/

/-- The renaming that drops the innermost variable (which must not occur). -/
def JsRen.strengthen {Γ : List JsTy} {σ : JsTy} : JsRenM Option (σ :: Γ) Γ := fun x =>
  match x with
  | .zero => none
  | .succ x => some x

/-- A pattern keeping only the fields `used` says (by their positions `j, j+1, …` among the
    fields it keeps, the constants of index `n - 1 - j, …` after it), and the renaming of
    the constants after it. -/
def JsSel.narrow (used : Nat → Bool) (n : Nat) :
    {ts us : List JsTy} → JsSel ts us → (j : Nat) →
      (us' : List JsTy) × JsSel ts us' × (∀ {C : List JsTy}, JsRenM Option (pushAll us C) (pushAll us' C))
  | _, _, .nil, _ => ⟨[], .nil, fun x => some x⟩
  | _, _, .skip s, j =>
    let ⟨us', s', r⟩ := s.narrow used n j
    ⟨us', .skip s', r⟩
  | _, _, .keep (t := t) h s, j =>
    let ⟨us', s', r⟩ := s.narrow used n (j + 1)
    if used (n - 1 - j) then
      ⟨t :: us', .keep h s', fun {C} {_} x => r (C := t :: C) x⟩
    else
      ⟨us', .skip s', fun {C} {_} x => r (C := t :: C) x >>= JsRenM.liftAll us' JsRen.strengthen⟩

/-- The constants of index below `n` a block reads. -/
def readFields {C M J : List JsTy} {k : JsEnd} (n : Nat) (b : JsBlock C M J k) : Array Nat :=
  (b.occs.filter fun o => !o.isMut && o.idx < n).map (·.idx)

/-- A pattern and the block after it, without the fields the block does not read. -/
def narrowPattern {C M J ts us : List JsTy} {k : JsEnd} (sel : JsSel ts us)
    (b : JsBlock (pushAll us C) M J k) :
    (us' : List JsTy) × JsSel ts us' × JsBlock (pushAll us' C) M J k :=
  let n := us.length
  let used := readFields n b
  if used.size == 0 && n == 0 then ⟨us, sel, b⟩ else
  let ⟨us', sel', r⟩ := sel.narrow (fun i => used.contains i) n 0
  if us'.length == n then ⟨us, sel, b⟩ else
  match b.renameM r (fun x => some x) with
  | some b' => ⟨us', sel', b'⟩
  | none => ⟨us, sel, b⟩

/-- `narrowPattern` in the arms of a case analysis on a union. -/
def JsUnionArms.narrow {C M J : List JsTy} {k : JsEnd} :
    {cs : List (List JsTy)} → JsUnionArms C M J k cs → JsUnionArms C M J k cs
  | _, .nil => .nil
  | _, .cons sel b rest =>
    let ⟨_, sel', b'⟩ := narrowPattern sel b
    .cons sel' b' rest.narrow

/-- The fields a pattern binds but the rest of the block does not read are left out of the
    pattern (`const { _1: a, _2: b } = x;` is `const { _2: b } = x;` when `a` is not read,
    and nothing when no field is). -/
def narrowNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | .destructure e sel rest =>
    let ⟨_, sel', rest'⟩ := narrowPattern sel rest
    .destructure e sel' rest'
  | .unionCases e arms => .unionCases e arms.narrow
  | b => b

/-! ## All the clean-ups -/

/-- One step of the clean-ups, on a block whose parts are clean already. -/
def cleanupNode {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  narrowNode (selfAssignNode (copyPropNode (rebuildNode b)))

/-- The clean-ups of this file, everywhere. -/
def cleanup {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  b.mapBU .id ⟨fun _ _ _ _ b => cleanupNode b⟩

/-- The clean-ups of this file, in an expression (the bodies of its closures). -/
def cleanupExpr {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : JsExpr C M τ :=
  e.mapBU .id ⟨fun _ _ _ _ b => cleanupNode b⟩

/-! ## Constants used once, right away -/

mutual
/-- Does a closure of the expression assign a mutable variable it captures? -/
partial def JsExpr.closureWrites {C M : List JsTy} {τ : JsTy} : JsExpr C M τ → Bool
  | .cvar _ | .mvar _ | .global .. | .lit _ | .enum_mk .. | .unreachable _ => false
  | .imported _ as | .inlined _ as => as.closureWrites
  | .app f as => f.closureWrites || as.closureWrites
  | e@(.lam _ b) => e.occs.any (·.write) || b.closureWrites
  | .record_mk fs => fs.closureWrites
  | .union_mk _ as => as.closureWrites
  | .array_mk _ ps | .list_mk ps => ps.closureWrites
  | .cond c a b => c.closureWrites || a.closureWrites || b.closureWrites
/-- `closureWrites` of arguments. -/
partial def JsArgs.closureWrites {C M σs : List JsTy} : JsArgs C M σs → Bool
  | .nil => false
  | .cons a as => a.closureWrites || as.closureWrites
/-- `closureWrites` of the parts of an array literal. -/
partial def JsParts.closureWrites {C M : List JsTy} {A E : JsTy} : JsParts C M A E → Bool
  | .nil => false
  | .elem e rest | .spread e rest => e.closureWrites || rest.closureWrites
/-- `closureWrites` of a block. -/
partial def JsBlock.closureWrites {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → Bool
  | .ret e | .jump _ e => e.closureWrites
  | .next | .throw _ => false
  | .const _ e rest | .letMut _ e rest | .assign _ e rest | .destructure e _ rest =>
    e.closureWrites || rest.closureWrites
  | .ite c t e => c.closureWrites || t.closureWrites || e.closureWrites
  | .enumCases e arms => e.closureWrites || arms.closureWrites
  | .unionCases e arms => e.closureWrites || arms.closureWrites
  | .join _ b rest => b.closureWrites || rest.closureWrites
  | .forRange _ _ n b rest | .lastIter _ _ n b rest =>
    n.closureWrites || b.closureWrites || rest.closureWrites
  | .forOf _ _ xs b rest => xs.closureWrites || b.closureWrites || rest.closureWrites
/-- `closureWrites` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.closureWrites {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms C M J k n → Bool
  | .nil => false
  | .cons b rest => b.closureWrites || rest.closureWrites
/-- `closureWrites` of the arms of a case analysis on a union. -/
partial def JsUnionArms.closureWrites {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms C M J k cs → Bool
  | .nil => false
  | .cons _ b rest => b.closureWrites || rest.closureWrites
end

/-- What evaluating an expression does before it reads a given constant: nothing that could
    have an effect or fail (`clean`, and the constant is not read), reads it first (`found`:
    everything evaluated before it has no effect), or something else (`dirty`). -/
inductive FirstRead where
  | clean
  | found
  | dirty
  deriving BEq, Inhabited

/-- `a`, then (if nothing happened yet) `b`. -/
def FirstRead.andThen (a : FirstRead) (b : Unit → FirstRead) : FirstRead :=
  match a with
  | .clean => b ()
  | r => r

/-- The parts, and then an operation that could have an effect or fail. -/
def FirstRead.thenCall : FirstRead → FirstRead
  | .found => .found
  | _ => .dirty

mutual
/-- `FirstRead` of the constant of index `d` in an expression (JavaScript evaluates the
    callee, then the arguments, the fields and the parts of literals, left to right; an
    inlined operation may evaluate its arguments in any order, so they must all be
    effect-free but the one that reads the constant). -/
partial def JsExpr.firstRead {C M : List JsTy} {τ : JsTy} (d : Nat) : JsExpr C M τ → FirstRead
  | .cvar x => if x.index == d then .found else .clean
  | .global .. | .lit _ | .enum_mk .. | .unreachable _ => .clean
  -- the value of a mutable variable only changes by assignments (see `inlineOnce`)
  | .mvar _ => .clean
  | .imported _ as => (as.firstRead d).thenCall
  | .inlined _ as => (as.firstReadAny d).thenCall
  | .app f as => ((f.firstRead d).andThen fun _ => as.firstRead d).thenCall
  | e@(.lam ..) => if e.occs.any (·.is ⟨false, d⟩) then .dirty else .clean
  | .record_mk fs => fs.firstRead d
  | .union_mk _ as => as.firstRead d
  | .array_mk _ ps => ps.firstRead d
  | .list_mk ps => ps.firstRead d
  | .cond c a b =>
    match c.firstRead d with
    | .found => .found
    | .clean => if a.firstRead d == .clean && b.firstRead d == .clean then .clean else .dirty
    | .dirty => .dirty
/-- `FirstRead` of arguments, left to right. -/
partial def JsArgs.firstRead {C M σs : List JsTy} (d : Nat) : JsArgs C M σs → FirstRead
  | .nil => .clean
  | .cons a as => (a.firstRead d).andThen fun _ => as.firstRead d
/-- `FirstRead` of arguments evaluated in any order. -/
partial def JsArgs.firstReadAny {C M σs : List JsTy} (d : Nat) : JsArgs C M σs → FirstRead
  | .nil => .clean
  | .cons a as =>
    match a.firstRead d, as.firstReadAny d with
    | .clean, r => r
    | .found, .clean => .found
    | _, _ => .dirty
/-- `FirstRead` of the parts of an array literal, left to right. -/
partial def JsParts.firstRead {C M : List JsTy} {A E : JsTy} (d : Nat) : JsParts C M A E → FirstRead
  | .nil => .clean
  | .elem e rest => (e.firstRead d).andThen fun _ => rest.firstRead d
  | .spread a rest => (a.firstRead d).andThen fun _ => rest.firstRead d
end

/-- `FirstRead` of the innermost constant in the first statement of a block. -/
def JsBlock.headRead {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → FirstRead
  | .ret e | .jump _ e => e.firstRead 0
  | .const _ e _ | .letMut _ e _ | .assign _ e _ | .destructure e _ _ => e.firstRead 0
  | .ite c _ _ => c.firstRead 0
  | _ => .dirty

/-- `const x = e; S` where the first statement of `S` reads `x` before doing anything that
    could have an effect or fail, and nothing else reads `x`: `S` with `e` for `x`
    (`const x = f(y); return g(x);` is `return g(f(y));`).  `e` is still evaluated exactly
    once, and before everything it was evaluated before. -/
def inlineOnceNode {C M J : List JsTy} {k : JsEnd} : JsBlock C M J k → JsBlock C M J k
  | b@(.const _ e rest) =>
    if rest.headRead != .found then b else
    let uses := rest.occs.filter (·.is ⟨false, 0⟩)
    if uses.size == 1 then rest.subst (JsSubst.inst e) else b
  | b => b

/-- `inlineOnceNode` everywhere (once arrays are updated in place: it is run last).  Moving
    `e` past reads of mutable variables is only safe when no closure assigns a mutable
    variable (calling it could change them): the backend never writes such a closure, and the
    pass does nothing otherwise. -/
def inlineOnce {C M J : List JsTy} {k : JsEnd} (b : JsBlock C M J k) : JsBlock C M J k :=
  if b.closureWrites then b else
  b.mapBU .id ⟨fun _ _ _ _ b => inlineOnceNode b⟩

/-- `inlineOnce` in an expression (the bodies of its closures). -/
def inlineOnceExpr {C M : List JsTy} {τ : JsTy} (e : JsExpr C M τ) : JsExpr C M τ :=
  if e.closureWrites then e else
  e.mapBU .id ⟨fun _ _ _ _ b => inlineOnceNode b⟩

end MoreJs

end
