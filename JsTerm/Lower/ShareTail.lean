module

public import JsTerm.Lower.Sink
public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Tails shared by the branches of a decision tree, written once after a labelled block

A `match` of several columns (`CaseHeuristics.lean`) is compiled to a decision tree whose
leaves repeat the same fall-through: the last pattern `_, _ => …` is copied into every branch
where a test of the earlier patterns fails.

```js
if (a.tag === 1) {                       L: {
  if (a._1 === 1) {                        if (a.tag === 1) {
    if (a1.tag === 0) { return 3; }          if (a._1 === 1 && a1.tag === 1) {
    if (a1.tag === 1) {                        …
      …                                      }
    }                               ⟶      } else if (…) { … }
    return 4;                              }
  }                                        return a1.tag === 0 ? 3 : 4;
  return a1.tag === 0 ? 3 : 4;
}
…
return a1.tag === 0 ? 3 : 4;
```

`JsBlock.shareTails` finds, at a test (`if`, a case analysis), a block `D` that ends two of
its branches or more (the *tail*), and writes it once, after a join point whose block is the
test with each copy of `D` replaced by a jump to it (`join t { … jump … } D`): the labelled
block `L: { … }` of the printer, a jump being `break L;`, or nothing at its end.  A jump
passes no value (`undefined`, which the printer does not write).

A branch is a copy of `D` when it is the same statements as `D` (the same dump,
`JsBlock.pretty`, once moved to the context of the test: it reads no variable bound in
between, `JsBlock.renameM` into `Option`), or when it is what `D` computes where the branch
is: the branches of `D` that the tests around the branch already decided are taken
(`JsBlock.assume`; `if (a1.tag === 0) { return 3; }` inside `a1.tag === 0` is `D`), and
`return c ? a : b` is `if (c) { return a; } D` when `return b` is `D` there.  The tests
remembered are those whose subject never changes (a constant, or a condition without effect
that reads no mutable variable: `JsExpr.stable`), so they still hold at the branch.

`D` is chosen, among the largest blocks in tail position under the test whose copies end two
different branches of the test (a block ending only branches inside one branch is shared there
instead, `shareTails` going down the tree), as the one whose JavaScript is the shortest (the
printer's measure, `JsTerm.Print.Share.blockCost`: a jump at the end of the labelled block is
nothing, one elsewhere a `break`), and only when it is shorter than the test as it is; a jump,
a `continue` or a `throw` is never shared.

A jump from a copy of `D` specialised by the tests around it runs those tests of `D` again at
run time, so each of them adds `retestCost` to the measure (`JsBlock.assumeSkipped`).  In
`CaseMulti.lean` sharing `if (y === 4) { return "_.4"; } return y === 5 ? …` with the leaf
`return "_.4"` of the other branch (under `y === 4`) would test `y === 4` twice on that path;
the leaf `return "_.4"` itself is shared instead, and no path makes more comparisons than
purescript-backend-optimizer's decision tree.

**Why the value is the same.**  A jump replaces a copy of `D` that is in tail position (the
last thing the block does before it returns, ends its iteration, or jumps out): the join
point's block ends there, and `D`, right after it, runs in the same state, on the same
variables (every variable `D` reads is bound outside the join point and is the same one).
The tests remembered hold there (their subjects never change), so `D` takes the branches the
copy was specialised to.
-/

namespace MoreJs

variable {S : JsSig}

/-- The type of the value a jump to a shared tail passes: nothing reads it (it is
    `undefined`). -/
abbrev tailTy : JsTy := .terminal .bool

/-! ## Renamings -/

/-- A renaming into the root that forgets a new innermost variable (`none` for it). -/
def JsRenM.forget {Γ R : List JsTy} {σ : JsTy} (r : JsRenM Option Γ R) :
    JsRenM Option (σ :: Γ) R := fun x =>
  match x with
  | .zero => none
  | .succ y => r y

/-- A renaming into the root that forgets the variables of a pattern. -/
def JsRenM.forgetAll {R : List JsTy} : {Γ : List JsTy} → (us : List JsTy) →
    JsRenM Option Γ R → JsRenM Option (pushAll us Γ) R
  | _, [], r => r
  | _, _ :: us, r => JsRenM.forgetAll us (JsRenM.forget r)

/-- The identity, into `Option`. -/
def JsRenM.someId {Γ : List JsTy} : JsRenM Option Γ Γ := fun x => some x

mutual
/-- The block with the jumps to enclosing join points renamed (the blocks of loops and
    closures, which start with join points of their own, are kept). -/
partial def JsBlock.renJ {C M J J' : List JsTy} {k : JsEnd} (rj : JsRenM Id J J') :
    JsBlock S C M J k → JsBlock S C M J' k
  | .ret e => .ret e
  | .next => .next
  | .jump j e => .jump (rj j) e
  | .throw m => .throw m
  | .raise e => .raise e
  | .const x e rest => .const x e (rest.renJ rj)
  | .letMut x e rest => .letMut x e (rest.renJ rj)
  | .assign x e rest => .assign x e (rest.renJ rj)
  | .destructure e sel rest => .destructure e sel (rest.renJ rj)
  | .ite c t e => .ite c (t.renJ rj) (e.renJ rj)
  | .enumCases e arms => .enumCases e (arms.renJ rj)
  | .unionCases e arms => .unionCases e (arms.renJ rj)
  | .join x b rest => .join x (b.renJ (JsRenM.lift rj)) (rest.renJ rj)
  | .forRange x nt n body rest => .forRange x nt n body (rest.renJ rj)
  | .forOf x l xs body rest => .forOf x l xs body (rest.renJ rj)
  | .countdown x nt n base step rest => .countdown x nt n base step (rest.renJ rj)
  | .tick nt j base rest => .tick nt j (base.renJ rj) (rest.renJ rj)
  | .natCase x nt n z s => .natCase x nt n (z.renJ rj) (s.renJ rj)
  | .funs hints defs rest => .funs hints defs (rest.renJ rj)
/-- `renJ` of the arms of an enum's case analysis. -/
partial def JsEnumArms.renJ {C M J J' : List JsTy} {k : JsEnd} {n : Nat} (rj : JsRenM Id J J') :
    JsEnumArms S C M J k n → JsEnumArms S C M J' k n
  | .nil => .nil
  | .cons b rest => .cons (b.renJ rj) (rest.renJ rj)
/-- `renJ` of the arms of a union's case analysis. -/
partial def JsUnionArms.renJ {C M J J' : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (rj : JsRenM Id J J') : JsUnionArms S C M J k cs → JsUnionArms S C M J' k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.renJ rj) (rest.renJ rj)
end

/-! ## Tests that still hold further down -/

/-- Does the expression always have the same value where it is in scope: a constant (or one
    layer of a datatype in or out of one), or a condition without effect that cannot throw
    and reads no mutable variable (`JsExpr.sinkable`)? -/
def JsExpr.stable {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ => true
  | .fold _ e | .unfold _ e => e.stable
  | e => e.sinkable && e.occs.all (!·.isMut)

/-- The tests the branches are under: the dump of the subject of the test in the root
    context (prefixed by the kind of test) and the branch taken (`1`/`0` for the two branches
    of an `if`). -/
abbrev Facts := List (String × Nat)

/-- The key of a test on the subject `e`, when it is stable and reads no variable bound since
    the root. -/
def testKey {C M R MR : List JsTy} {τ : JsTy} (kind : String) (rc : JsRenM Option C R)
    (rm : JsRenM Option M MR) (e : JsExpr S C M τ) : Option String :=
  if !e.stable then none else
  (e.renameM rc rm).map fun (e' : JsExpr S R MR τ) => kind ++ e'.pretty ""

/-- The tests with one more, when it has a key. -/
def Facts.add (fs : Facts) : Option String → Nat → Facts
  | some key, i => (key, i) :: fs
  | none, _ => fs

/-- The arm of index `i` of a case analysis on an enum. -/
def JsEnumArms.arm? {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    Nat → JsEnumArms S C M J k n → Option (JsBlock S C M J k)
  | _, .nil => none
  | 0, .cons b _ => some b
  | i + 1, .cons _ rest => rest.arm? i

/-- The arm of index `i` of a case analysis on a union, when it reads none of the fields of
    its pattern (then moved out of the pattern). -/
def JsUnionArms.arm? {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    Nat → JsUnionArms S C M J k cs → Option (JsBlock S C M J k)
  | _, .nil => none
  | 0, .cons (us := us) _ b _ => b.renameM (JsRenM.forgetAll us JsRenM.someId) JsRenM.someId
  | i + 1, .cons _ _ rest => rest.arm? i

/-- The block where the tests `facts` hold: the branches of its tests that they decide are
    taken, as long as they are. -/
partial def JsBlock.assume {C M J : List JsTy} {k : JsEnd} (facts : Facts) :
    JsBlock S C M J k → JsBlock S C M J k
  | .ite c t e =>
    match facts.lookup ("c:" ++ c.pretty "") with
    | some 1 => t.assume facts
    | some _ => e.assume facts
    | none => .ite c t e
  | .unionCases e arms =>
    match (facts.lookup ("u:" ++ e.pretty "")).bind (arms.arm? ·) with
    | some b => b.assume facts
    | none => .unionCases e arms
  | .enumCases e arms =>
    match (facts.lookup ("e:" ++ e.pretty "")).bind (arms.arm? ·) with
    | some b => b.assume facts
    | none => .enumCases e arms
  | b => b

/-- What a test run again by a jump to a shared tail costs, measured as text (`BlockCost`):
    about the length of the `if (…) { … }` it would take to write the test once more, so a
    tail is shared from a specialised copy only when that saves more text than writing the
    tests again would. -/
def retestCost : Nat := 20

/-- The tests `JsBlock.assume facts` decides in the block, each by the length of the dump of
    its subject (a jump to a shared tail specialised there runs them again). -/
partial def JsBlock.assumeSkipped {C M J : List JsTy} {k : JsEnd} (facts : Facts) :
    JsBlock S C M J k → Nat
  | .ite c t e =>
    let key := "c:" ++ c.pretty ""
    match facts.lookup key with
    | some 1 => retestCost + t.assumeSkipped facts
    | some _ => retestCost + e.assumeSkipped facts
    | none => 0
  | .unionCases e arms =>
    let key := "u:" ++ e.pretty ""
    match (facts.lookup key).bind (arms.arm? ·) with
    | some b => retestCost + b.assumeSkipped facts
    | none => 0
  | .enumCases e arms =>
    let key := "e:" ++ e.pretty ""
    match (facts.lookup key).bind (arms.arm? ·) with
    | some b => retestCost + b.assumeSkipped facts
    | none => 0
  | _ => 0

/-! ## Finding the tails -/

/-- Does the block only leave (a jump, the end of an iteration, a `throw`)? -/
def JsBlock.isExit {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Bool
  | .jump .. | .next | .throw _ => true
  | _ => false

mutual
/-- The candidates for a shared tail: the blocks in tail position in the block (`root`: the
    test itself, not a candidate) that read no variable bound since the test, moved to its
    context, with their dumps (the blocks of join points, loops and closures are not looked
    into). -/
partial def JsBlock.tails {R MR C M J : List JsTy} {k : JsEnd} (rc : JsRenM Option C R)
    (rm : JsRenM Option M MR) (root : Bool) (acc : Array (String × JsBlock S R MR J k))
    (b : JsBlock S C M J k) : Array (String × JsBlock S R MR J k) :=
  let acc := if root || b.isExit then acc else
    match b.renameM rc rm with
    | some b' => acc.push (b'.pretty "", b')
    | none => acc
  b.tailsBelow rc rm acc
/-- `tails` of the blocks in tail position right below the block. -/
partial def JsBlock.tailsBelow {R MR C M J : List JsTy} {k : JsEnd} (rc : JsRenM Option C R)
    (rm : JsRenM Option M MR) (acc : Array (String × JsBlock S R MR J k)) :
    JsBlock S C M J k → Array (String × JsBlock S R MR J k)
  | .const _ _ rest => rest.tails (JsRenM.forget rc) rm false acc
  | .letMut _ _ rest => rest.tails rc (JsRenM.forget rm) false acc
  | .assign _ _ rest => rest.tails rc rm false acc
  | .destructure (us := us) _ _ rest => rest.tails (JsRenM.forgetAll us rc) rm false acc
  | .ite _ t e => e.tails rc rm false (t.tails rc rm false acc)
  | .enumCases _ arms => arms.tails rc rm acc
  | .unionCases _ arms => arms.tails rc rm acc
  | .join _ _ rest => rest.tails (JsRenM.forget rc) rm false acc
  | .forRange _ _ _ _ rest | .forOf _ _ _ _ rest | .tick _ _ _ rest =>
    rest.tails rc rm false acc
  | .countdown _ _ _ _ _ rest => rest.tails (JsRenM.forget rc) rm false acc
  | .natCase _ _ _ z s => s.tails (JsRenM.forget rc) rm false (z.tails rc rm false acc)
  | .funs (τs := τs) _ _ rest => rest.tails (JsRenM.forgetAll τs rc) rm false acc
  | .ret _ | .next | .jump .. | .throw _ | .raise _ => acc
/-- `tails` of the arms of an enum's case analysis. -/
partial def JsEnumArms.tails {R MR C M J : List JsTy} {k : JsEnd} {n : Nat}
    (rc : JsRenM Option C R) (rm : JsRenM Option M MR) (acc : Array (String × JsBlock S R MR J k)) :
    JsEnumArms S C M J k n → Array (String × JsBlock S R MR J k)
  | .nil => acc
  | .cons b rest => rest.tails rc rm (b.tails rc rm false acc)
/-- `tails` of the arms of a union's case analysis. -/
partial def JsUnionArms.tails {R MR C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (rc : JsRenM Option C R) (rm : JsRenM Option M MR) (acc : Array (String × JsBlock S R MR J k)) :
    JsUnionArms S C M J k cs → Array (String × JsBlock S R MR J k)
  | .nil => acc
  | .cons (us := us) _ b rest => rest.tails rc rm (b.tails (JsRenM.forgetAll us rc) rm false acc)
end

/-! ## Replacing the copies by jumps -/

/-- Where the walk replacing the copies of a tail `D` is. -/
structure ShareAt (R MR : List JsTy) (C M : List JsTy) where
  /-- The variables moved to the context of the test. -/
  rc : JsRenM Option C R
  rm : JsRenM Option M MR
  /-- The tests the block is under. -/
  facts : Facts
  /-- The branch of the test the block is in (`none`: the test itself). -/
  child : Option Nat
  /-- What a jump from where the tests `facts` hold costs at run time: the tests of `D`
      decided there, run again (`JsBlock.assumeSkipped`). -/
  penalty : Facts → Nat := fun _ => 0

/-- Is the block, moved to the context of the test, the dump `dump facts` (`D` where the tests
    `facts` hold)? -/
def JsBlock.isTail {R MR C M J : List JsTy} {k : JsEnd} (dump : Facts → String)
    (at_ : ShareAt R MR C M) (b : JsBlock S C M J k) : Bool :=
  at_.child.isSome && !b.isExit && match b.renameM at_.rc at_.rm with
    | some b' => b'.pretty "" == dump at_.facts
    | none => false

/-- The walk replacing copies of `D`: the copies it replaced, each by the branch of the test it
    is in and the tests of `D` a jump from there runs again (`ShareAt.penalty`). -/
abbrev ShareM := StateM (Array (Nat × Nat))

/-- Record a copy of `D` replaced: the branch of the test it is in, and the tests of `D` a jump
    from there runs again. -/
def ShareAt.hit {R MR C M : List JsTy} (at_ : ShareAt R MR C M) : ShareM Unit :=
  modify (·.push (at_.child.getD 0, at_.penalty at_.facts))

mutual
/-- The block under the test with the copies of `D` (`dump`: the dump of `D` where tests hold)
    replaced by jumps to the join point `tgt` (the jumps to the join points around renamed by
    `rj`). -/
partial def JsBlock.shareGo {R MR C M J J' : List JsTy} {k : JsEnd} (dump : Facts → String)
    (tgt : JsMem J' tailTy) (rj : JsRenM Id J J') (at_ : ShareAt R MR C M) :
    JsBlock S C M J k → ShareM (JsBlock S C M J' k)
  | b => do
    if b.isTail dump at_ then
      at_.hit
      return .jump tgt (.unreachable tailTy)
    b.shareStep dump tgt rj at_
/-- `shareGo` of a block that is not a copy of `D`: its blocks in tail position. -/
partial def JsBlock.shareStep {R MR C M J J' : List JsTy} {k : JsEnd} (dump : Facts → String)
    (tgt : JsMem J' tailTy) (rj : JsRenM Id J J') (at_ : ShareAt R MR C M) :
    JsBlock S C M J k → ShareM (JsBlock S C M J' k)
  | .ret (.cond c a e) => do
    if (JsBlock.ret (J := J) e).isTail dump at_ then
      at_.hit
      return .ite c (.ret a) (.jump tgt (.unreachable tailTy))
    if (JsBlock.ret (J := J) a).isTail dump at_ then
      at_.hit
      return .ite c (.jump tgt (.unreachable tailTy)) (.ret e)
    return .ret (.cond c a e)
  | .ret e => return .ret e
  | .next => return .next
  | .jump j e => return .jump (rj j) e
  | .throw m => return .throw m
  | .raise e => return .raise e
  | .const x e rest =>
    return .const x e (← rest.shareGo dump tgt rj { at_ with rc := JsRenM.forget at_.rc })
  | .letMut x e rest =>
    return .letMut x e (← rest.shareGo dump tgt rj { at_ with rm := JsRenM.forget at_.rm })
  | .assign x e rest => return .assign x e (← rest.shareGo dump tgt rj at_)
  | .destructure (us := us) e sel rest =>
    return .destructure e sel
      (← rest.shareGo dump tgt rj { at_ with rc := JsRenM.forgetAll us at_.rc })
  | .ite c t e => do
    let key := testKey "c:" at_.rc at_.rm c
    let t' ← t.shareGo dump tgt rj { at_ with facts := at_.facts.add key 1, child := at_.child.orElse fun _ => some 0 }
    let e' ← e.shareGo dump tgt rj { at_ with facts := at_.facts.add key 0, child := at_.child.orElse fun _ => some 1 }
    return .ite c t' e'
  | .enumCases e arms =>
    return .enumCases e (← arms.shareGo dump tgt rj at_ (testKey "e:" at_.rc at_.rm e) 0)
  | .unionCases e arms =>
    return .unionCases e (← arms.shareGo dump tgt rj at_ (testKey "u:" at_.rc at_.rm e) 0)
  | .join x blk rest =>
    return .join x (blk.renJ (JsRenM.lift rj))
      (← rest.shareGo dump tgt rj { at_ with rc := JsRenM.forget at_.rc })
  | .forRange x nt n body rest => return .forRange x nt n body (← rest.shareGo dump tgt rj at_)
  | .forOf x l xs body rest => return .forOf x l xs body (← rest.shareGo dump tgt rj at_)
  | .countdown x nt n base step rest =>
    return .countdown x nt n base step
      (← rest.shareGo dump tgt rj { at_ with rc := JsRenM.forget at_.rc })
  | .tick nt j base rest =>
    return .tick nt j (← base.shareGo dump tgt rj at_) (← rest.shareGo dump tgt rj at_)
  | .natCase x nt n z s => do
    let z' ← z.shareGo dump tgt rj { at_ with child := at_.child.orElse fun _ => some 0 }
    let s' ← s.shareGo dump tgt rj { at_ with rc := JsRenM.forget at_.rc, child := at_.child.orElse fun _ => some 1 }
    return .natCase x nt n z' s'
  | .funs (τs := τs) hints defs rest =>
    return .funs hints defs
      (← rest.shareGo dump tgt rj { at_ with rc := JsRenM.forgetAll τs at_.rc })
/-- `shareGo` of the arms of an enum's case analysis (`key`: the key of its test, `i`: the index
    of the first arm). -/
partial def JsEnumArms.shareGo {R MR C M J J' : List JsTy} {k : JsEnd} {n : Nat}
    (dump : Facts → String) (tgt : JsMem J' tailTy) (rj : JsRenM Id J J') (at_ : ShareAt R MR C M)
    (key : Option String) (i : Nat) : JsEnumArms S C M J k n → ShareM (JsEnumArms S C M J' k n)
  | .nil => return .nil
  | .cons b rest => do
    let b' ← b.shareGo dump tgt rj
      { at_ with facts := at_.facts.add key i, child := at_.child.orElse fun _ => some i }
    return .cons b' (← rest.shareGo dump tgt rj at_ key (i + 1))
/-- `shareGo` of the arms of a union's case analysis. -/
partial def JsUnionArms.shareGo {R MR C M J J' : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (dump : Facts → String) (tgt : JsMem J' tailTy) (rj : JsRenM Id J J') (at_ : ShareAt R MR C M)
    (key : Option String) (i : Nat) :
    JsUnionArms S C M J k cs → ShareM (JsUnionArms S C M J' k cs)
  | .nil => return .nil
  | .cons (us := us) sel b rest => do
    let b' ← b.shareGo dump tgt rj
      { rc := JsRenM.forgetAll us at_.rc, rm := at_.rm, facts := at_.facts.add key i,
        child := at_.child.orElse fun _ => some i, penalty := at_.penalty }
    return .cons sel b' (← rest.shareGo dump tgt rj at_ key (i + 1))
end

/-! ## The rewrite -/

/-- Is the block a test with several branches? -/
def JsBlock.isTest {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Bool
  | .ite .. | .enumCases .. | .unionCases .. | .natCase .. => true
  | _ => false

/-- The largest candidates tried at a test. -/
def maxTailCandidates : Nat := 24

/-- A measure of the text a block is printed as (`JsTerm.Print.Share` passes the length of its
    JavaScript). -/
abbrev BlockCost (S : JsSig) := ∀ {C M J : List JsTy} {k : JsEnd}, JsBlock S C M J k → Nat

/-- The test with a tail shared by two of its branches or more replaced by jumps to a new join
    point, and the tail (under the value of the join point, which it does not read): of the
    candidates, the one printed the shortest (`cost`), when it is shorter than the test as it
    is. -/
def JsBlock.hoistTail? {C M J : List JsTy} {k : JsEnd} (cost : BlockCost S)
    (b : JsBlock S C M J k) :
    Option (JsBlock S C M (tailTy :: J) k × JsBlock S (tailTy :: C) M J k) := Id.run do
  if !b.isTest then return none
  let found := b.tails JsRenM.someId JsRenM.someId true #[]
  -- one candidate per dump, the largest first
  let mut seen : Std.HashSet String := {}
  let mut cands : Array (String × JsBlock S C M J k) := #[]
  for (key, d) in found do
    if seen.contains key then continue
    seen := seen.insert key
    cands := cands.push (key, d)
  let best := (cands.qsort fun a b => a.1.length > b.1.length).toList.take maxTailCandidates
  let mut chosen : Option (Nat × JsBlock S C M (tailTy :: J) k × JsBlock S (tailTy :: C) M J k) :=
    none
  let base := cost b
  for (_, d) in best do
    let dump : Facts → String := fun facts => (d.assume facts).pretty ""
    let (b', hits) := (b.shareGo dump .zero (fun j => JsMem.succ j)
      { rc := JsRenM.someId, rm := JsRenM.someId, facts := [], child := none,
        penalty := fun facts => d.assumeSkipped facts }).run #[]
    let branches := hits.foldl (fun acc (i, _) => if acc.contains i then acc else acc.push i) #[]
    if hits.size ≥ 2 && branches.size ≥ 2 then
      let d' := Id.run (d.renameM JsRen.succ JsRen.id)
      let c := cost (JsBlock.join "t" b' d') + hits.foldl (fun acc (_, p) => acc + p) 0
      if c < base && chosen.all (c < ·.1) then chosen := some (c, b', d')
  return chosen.map fun (_, b', d') => (b', d')

mutual
/-- `hoistTail?` everywhere in the block, from the top down (a tail is shared at the test
    closest to its copies whose branches it ends, then the rest looked into again). -/
partial def JsBlock.shareTails {C M J : List JsTy} {k : JsEnd} (cost : BlockCost S) :
    JsBlock S C M J k → JsBlock S C M J k
  | b =>
    match b.hoistTail? cost with
    | some (b', d) => .join "t" (b'.shareTails cost) (d.shareTails cost)
    | none =>
      match b with
      | .ret e => .ret e
      | .next => .next
      | .jump j e => .jump j e
      | .throw m => .throw m
      | .raise e => .raise e
      | .const x e rest => .const x e (rest.shareTails cost)
      | .letMut x e rest => .letMut x e (rest.shareTails cost)
      | .assign x e rest => .assign x e (rest.shareTails cost)
      | .destructure e sel rest => .destructure e sel (rest.shareTails cost)
      | .ite c t e => .ite c (t.shareTails cost) (e.shareTails cost)
      | .enumCases e arms => .enumCases e (arms.shareTails cost)
      | .unionCases e arms => .unionCases e (arms.shareTails cost)
      | .join x blk rest => .join x (blk.shareTails cost) (rest.shareTails cost)
      | .forRange x nt n body rest =>
        .forRange x nt n (body.shareTails cost) (rest.shareTails cost)
      | .forOf x l xs body rest => .forOf x l xs (body.shareTails cost) (rest.shareTails cost)
      | .countdown x nt n base step rest =>
        .countdown x nt n (base.shareTails cost) (step.shareTails cost) (rest.shareTails cost)
      | .tick nt j base rest => .tick nt j (base.shareTails cost) (rest.shareTails cost)
      | .natCase x nt n z s => .natCase x nt n (z.shareTails cost) (s.shareTails cost)
      | .funs hints defs rest => .funs hints defs (rest.shareTails cost)
/-- `shareTails` in the arms of an enum's case analysis. -/
partial def JsEnumArms.shareTails {C M J : List JsTy} {k : JsEnd} {n : Nat} (cost : BlockCost S) :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons (b.shareTails cost) (rest.shareTails cost)
/-- `shareTails` in the arms of a union's case analysis. -/
partial def JsUnionArms.shareTails {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (cost : BlockCost S) : JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.shareTails cost) (rest.shareTails cost)
end

/-- The function with the tails shared by the branches of its tests written once (where that
    makes it shorter, as `cost` measures). -/
def JsFun.shareTails (cost : ∀ (S : JsSig), BlockCost S) (f : JsFun) : JsFun :=
  { f with body := f.body.shareTails (cost f.sig) }

end MoreJs

end
