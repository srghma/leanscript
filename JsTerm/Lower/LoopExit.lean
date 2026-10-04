module

public import JsTerm.Lower.Tail
public import JsTerm.Syntax.Vars.Occs

@[expose] public section

set_option autoImplicit false

/-!
# Leaving a counting loop at the first iteration after which nothing changes

A `for` loop of Lean with `break` or `return` (`for i in [0:n] do … break …`) is a fold whose
state is a union (`ForInStep`, or Lean's `MProd`/`Option` for `return`): once the state is
`done`, every later iteration hands it on unchanged.  The conversion (`JsTerm.Lower.FromTerm`)
writes such a fold as a loop over all the iterations, each testing the state first:

```js
let acc = { tag: 1, _1: n };
for (let i = 0; i < n; i++) {
  if (acc.tag === 1) {                         // `yield`: the step runs
    …
    if (…) { acc = { tag: 0, _1: i }; }        // `done`: no later iteration does anything
  }                                            // (no `else`: a `done` state is kept)
}
return acc._1;
```

The rewrite here (`JsBlock.loopExit`) leaves the loop at the iteration that makes the state
`done`: `acc = { tag: 0, _1: i }; break L;` with the loop labelled `L` (`JsBlock.forExit`).  It
applies to a loop whose body is a case analysis on a mutable variable (the state) in which the
arms of some constructors (the *idle* ones) only end the iteration (`next`), and to each
assignment of a literal of an idle constructor to the state that ends the iteration (directly,
or in an arm of a conditional `acc = c ? … : …;`, which becomes an `if`).  Every iteration
after such an assignment would run an idle arm, which changes nothing (the counter of the loop
is not seen after it), so leaving the loop there computes the same.

`Term` has no statement that leaves a loop (a fold always runs all its iterations), and the
conversion writes the body of a loop and the code after it separately, so the rewrite is made
on the JavaScript grammar.
-/

namespace MoreJs

variable {S : JsSig}

/-- Is the block the end of an iteration? -/
def JsBlock.isNext {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Bool
  | .next => true
  | _ => false

/-- The positions (from `i`) of the arms of a case analysis on a union that only end the
    iteration. -/
def JsUnionArms.idleAt {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (i : Nat) :
    JsUnionArms S C M J k cs → List Nat
  | .nil => []
  | .cons _ b rest => (if b.isNext then [i] else []) ++ rest.idleAt (i + 1)

/-- Is the expression, on some path, a literal of one of the constructors at the positions
    `idle`? -/
def JsExpr.idleLeaf {C M : List JsTy} {τ : JsTy} (idle : List Nat) : JsExpr S C M τ → Bool
  | .union_mk ix _ => idle.contains ix.index
  | .cond _ a b => a.idleLeaf idle || b.idleLeaf idle
  | _ => false

/-- `x = e;` and the end of the iteration, where an assignment of a literal of an idle
    constructor leaves the loop instead (the join point `ex`), and a conditional with such a
    literal in an arm is an `if`. -/
def JsBlock.exitAssign {C M J : List JsTy} {σ τ : JsTy} (idle : List Nat) (x : JsMem M σ)
    (ex : JsMem J τ) : JsExpr S C M σ → JsBlock S C M J .loop
  | .cond c a b =>
    if a.idleLeaf idle || b.idleLeaf idle then
      .ite c (JsBlock.exitAssign idle x ex a) (JsBlock.exitAssign idle x ex b)
    else .assign x (.cond c a b) .next
  | .union_mk ix as =>
    if idle.contains ix.index then .assign x (.union_mk ix as) (.jump ex (.unreachable τ))
    else .assign x (.union_mk ix as) .next
  | e => .assign x e .next

mutual
/-- The body of a loop over one more join point (the exit, below the others), each assignment
    of a literal of an idle constructor to the mutable variable at position `acc` followed by
    the end of the iteration leaving the loop instead; and whether there was one.  The bodies
    of inner loops (whose iterations end on their own) and closures are kept. -/
partial def JsBlock.exits {C M J : List JsTy} {τ : JsTy} (idle : List Nat) (acc : Nat) :
    JsBlock S C M J .loop → JsBlock S C M (J ++ [τ]) .loop × Bool
  | .next => (.next, false)
  | .jump j e => (.jump (j.appendR [τ]) e, false)
  | .throw m => (.throw m, false)
  | .raise e => (.raise e, false)
  | .const x e rest => let (r, f) := rest.exits idle acc; (.const x e r, f)
  | .letMut x e rest => let (r, f) := rest.exits idle (acc + 1); (.letMut x e r, f)
  | .assign x e .next =>
    if x.index == acc && e.idleLeaf idle then (JsBlock.exitAssign idle x (JsMem.last J) e, true)
    else (.assign x e .next, false)
  | .assign x e rest => let (r, f) := rest.exits idle acc; (.assign x e r, f)
  | .destructure e sel rest => let (r, f) := rest.exits idle acc; (.destructure e sel r, f)
  | .ite c t e =>
    let (t', f₁) := t.exits idle acc
    let (e', f₂) := e.exits idle acc
    (.ite c t' e', f₁ || f₂)
  | .enumCases e arms => let (a, f) := arms.exits idle acc; (.enumCases e a, f)
  | .unionCases e arms => let (a, f) := arms.exits idle acc; (.unionCases e a, f)
  | .join x b rest =>
    let (b', f₁) := b.exits idle acc
    let (r, f₂) := rest.exits idle acc
    (.join x b' r, f₁ || f₂)
  | .forRange x nt n body rest => let (r, f) := rest.exits idle acc; (.forRange x nt n body r, f)
  | .forOf x l xs body rest => let (r, f) := rest.exits idle acc; (.forOf x l xs body r, f)
  | .forExit x nt n body done rest =>
    let (r, f) := rest.exits idle acc; (.forExit x nt n body done r, f)
  | .countdown x nt n base step rest =>
    let (r, f) := rest.exits idle acc; (.countdown x nt n base step r, f)
  | .tick nt j base rest =>
    let (b', f₁) := base.exits idle acc
    let (r, f₂) := rest.exits idle acc
    (.tick nt j b' r, f₁ || f₂)
  | .natCase x nt n z s =>
    let (z', f₁) := z.exits idle acc
    let (s', f₂) := s.exits idle acc
    (.natCase x nt n z' s', f₁ || f₂)
  | .funs hints defs rest => let (r, f) := rest.exits idle acc; (.funs hints defs r, f)
/-- `exits` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.exits {C M J : List JsTy} {τ : JsTy} {n : Nat} (idle : List Nat)
    (acc : Nat) : JsEnumArms S C M J .loop n → JsEnumArms S C M (J ++ [τ]) .loop n × Bool
  | .nil => (.nil, false)
  | .cons b rest =>
    let (b', f₁) := b.exits idle acc
    let (r, f₂) := rest.exits idle acc
    (.cons b' r, f₁ || f₂)
/-- `exits` in the arms of a case analysis on a union. -/
partial def JsUnionArms.exits {C M J : List JsTy} {τ : JsTy} {cs : List (List JsTy)}
    (idle : List Nat) (acc : Nat) :
    JsUnionArms S C M J .loop cs → JsUnionArms S C M (J ++ [τ]) .loop cs × Bool
  | .nil => (.nil, false)
  | .cons sel b rest =>
    let (b', f₁) := b.exits idle acc
    let (r, f₂) := rest.exits idle acc
    (.cons sel b' r, f₁ || f₂)
end

/-- A block under one more constant. -/
def JsBlock.wkC {C M J : List JsTy} {σ : JsTy} {k : JsEnd} (b : JsBlock S C M J k) :
    JsBlock S (σ :: C) M J k :=
  Id.run (b.renameM JsRen.succ JsRen.id)

/-- A counting loop (body and rest already rewritten), left at the first iteration after which
    nothing changes when its body is a case analysis on its state with idle arms (see the
    module documentation). -/
def JsBlock.mkForExit {C M J : List JsTy} {N : JsTy} {k : JsEnd} (x : String) (nt : JsNatTy N)
    (n : JsExpr S C M N) (body : JsBlock S (N :: C) M [] .loop) (rest : JsBlock S C M J k) :
    JsBlock S C M J k :=
  match body with
  | .unionCases (.mvar m) arms =>
    let idle := arms.idleAt 0
    if idle.isEmpty then .forRange x nt n body rest else
    let (body', found) := JsBlock.exits (τ := .terminal .bool) idle m.index body
    if !found then .forRange x nt n body rest else
    .forExit x nt n body' (.jump .zero (.unreachable _)) rest.wkC
  | _ => .forRange x nt n body rest

/-! ## The idle arms, once they are dead -/

/-- The position of the constructor of a literal of a union. -/
def JsExpr.ctorIndex? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option Nat
  | .union_mk ix _ => some ix.index
  | _ => none

/-- Is the expression, on every path, a literal of a constructor not in `idle`, or the mutable
    variable at position `acc` itself (an assignment that changes nothing)? -/
def JsExpr.activeLeaves {C M : List JsTy} {τ : JsTy} (idle : List Nat) (acc : Nat) :
    JsExpr S C M τ → Bool
  | .union_mk ix _ => !idle.contains ix.index
  | .mvar y => y.index == acc
  | .cond _ a b => a.activeLeaves idle acc && b.activeLeaves idle acc
  | _ => false

mutual
/-- Is every assignment of the mutable variable at position `acc` in the block one of a literal
    of a constructor not in `idle` (or of the variable itself), or one of a literal of a
    constructor in `idle` followed by the exit of the loop (the jump to the join point at
    `exit`, in the loop's own body)? -/
partial def JsBlock.stateKept {C M J : List JsTy} {k : JsEnd} (idle : List Nat) (acc : Nat)
    (exit : Option Nat) : JsBlock S C M J k → Bool
  | .assign x e rest =>
    if x.index != acc then rest.stateKept idle acc exit else
    match e with
    | .union_mk ix _ =>
      if idle.contains ix.index then
        match rest with
        | .jump j _ => exit == some j.index
        | _ => false
      else rest.stateKept idle acc exit
    | e => e.activeLeaves idle acc && rest.stateKept idle acc exit
  | .next | .ret _ | .jump .. | .throw _ | .raise _ => true
  | .const _ _ rest => rest.stateKept idle acc exit
  | .destructure _ _ rest => rest.stateKept idle acc exit
  | .funs _ _ rest => rest.stateKept idle acc exit
  | .letMut _ _ rest => rest.stateKept idle (acc + 1) exit
  | .ite _ t e => t.stateKept idle acc exit && e.stateKept idle acc exit
  | .enumCases _ arms => arms.stateKept idle acc exit
  | .unionCases _ arms => arms.stateKept idle acc exit
  | .join _ b rest => b.stateKept idle acc (exit.map (· + 1)) && rest.stateKept idle acc exit
  | .forRange _ _ _ body rest => body.stateKept idle acc none && rest.stateKept idle acc exit
  | .forOf _ _ _ body rest => body.stateKept idle acc none && rest.stateKept idle acc exit
  | .forExit _ _ _ body done rest =>
    body.stateKept idle acc none && done.stateKept idle acc none && rest.stateKept idle acc exit
  | .countdown _ _ _ base step rest =>
    base.stateKept idle (acc + 1) none && step.stateKept idle (acc + 1) none &&
      rest.stateKept idle acc exit
  | .tick _ _ base rest => base.stateKept idle acc exit && rest.stateKept idle acc exit
  | .natCase _ _ _ z s => z.stateKept idle acc exit && s.stateKept idle acc exit
/-- `stateKept` of the arms of a case analysis on an enum. -/
partial def JsEnumArms.stateKept {C M J : List JsTy} {k : JsEnd} {n : Nat} (idle : List Nat)
    (acc : Nat) (exit : Option Nat) : JsEnumArms S C M J k n → Bool
  | .nil => true
  | .cons b rest => b.stateKept idle acc exit && rest.stateKept idle acc exit
/-- `stateKept` of the arms of a case analysis on a union. -/
partial def JsUnionArms.stateKept {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (idle : List Nat) (acc : Nat) (exit : Option Nat) : JsUnionArms S C M J k cs → Bool
  | .nil => true
  | .cons _ b rest => b.stateKept idle acc exit && rest.stateKept idle acc exit
end

/-- The number of arms. -/
def JsUnionArms.count {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → Nat
  | .nil => 0
  | .cons _ _ rest => rest.count + 1

/-- An arm of a case analysis on a union: the fields of its constructor, the ones it binds, and
    its statements. -/
abbrev UnionArm (S : JsSig) (C M J : List JsTy) (k : JsEnd) : Type :=
  (fs : List JsTy) × (us : List JsTy) × JsSel fs us × JsBlock S (pushAll us C) M J k

/-- The arm at position `i` (from `j`). -/
def JsUnionArms.armAt? {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} (i j : Nat) :
    JsUnionArms S C M J k cs → Option (UnionArm S C M J k)
  | .nil => none
  | .cons (fs := fs) (us := us) sel b rest =>
    if i == j then some ⟨fs, us, sel, b⟩ else rest.armAt? i (j + 1)

/-- The arms at the positions `idle` (from `i`) replaced by the arm `a`, where their
    constructors have the fields of its constructor. -/
def JsUnionArms.fillIdle {C M J : List JsTy} {k : JsEnd} (idle : List Nat)
    (a : UnionArm S C M J k) (i : Nat) : {cs : List (List JsTy)} →
    JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | _, .nil => .nil
  | _, .cons (fs := fs) sel b rest =>
    let rest' := rest.fillIdle idle a (i + 1)
    if idle.contains i then
      if h : a.1 = fs then .cons (h ▸ a.2.2.1) a.2.2.2 rest' else .cons sel b rest'
    else .cons sel b rest'

/-- `let acc = lit; for (…) { case acc of … }` after `mkForExit`: when the state starts at a
    constructor that is not idle and every assignment of it is a literal of such a constructor,
    or a literal of an idle one right before the exit, the state is never idle at the start of
    an iteration, so the idle arms never run.  They are replaced by the arm of the one other
    constructor (when the fields are the same), so that the printer writes the arms once,
    without testing the tag (`sameUnionArms`). -/
def JsBlock.mkLetMut {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (x : String)
    (e : JsExpr S C M τ) (rest : JsBlock S C (τ :: M) J k) : JsBlock S C M J k :=
  let keep := JsBlock.letMut x e rest
  match e.ctorIndex?, rest with
  | some ix, .forExit y nt n body done r =>
    match body with
    | .unionCases (.mvar m) arms =>
      if m.index != 0 then keep else
      let idle := arms.idleAt 0
      if idle.contains ix then keep else
      let active := (List.range arms.count).filter (!idle.contains ·)
      match active with
      | [g] =>
        let closureWrites := body.occs.any fun o =>
          o.isMut && o.idx == 0 && o.write && o.inClosure
        if closureWrites || !body.stateKept idle 0 (some 0) then keep else
        match arms.armAt? g 0 with
        | some a =>
          .letMut x e (.forExit y nt n (.unionCases (.mvar m) (arms.fillIdle idle a 0)) done r)
        | none => keep
      | _ => keep
    | _ => keep
  | _, _ => keep

/-! ## The walk -/

mutual
/-- `JsBlock.loopExit` in the closures of an expression. -/
partial def JsExpr.loopExit {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => .imported op as.loopExit
  | .inlined op as => .inlined op as.loopExit
  | .app f as => .app f.loopExit as.loopExit
  | .lam hints body => .lam hints body.loopExit
  | .record_mk fs => .record_mk fs.loopExit
  | .union_mk ix as => .union_mk ix as.loopExit
  | .enumIndex nt e => .enumIndex nt e.loopExit
  | .enumEq a b => .enumEq a.loopExit b.loopExit
  | .boolCmp op a b => .boolCmp op a.loopExit b.loopExit
  | .index l nt a i => .index l nt a.loopExit i.loopExit
  | .indexOr l nt a i d => .indexOr l nt a.loopExit i.loopExit d.loopExit
  | .array_mk l ps => .array_mk l ps.loopExit
  | .list_mk ps => .list_mk ps.loopExit
  | .cond c a b => .cond c.loopExit a.loopExit b.loopExit
  | .listOp op as => .listOp op as.loopExit
  | .fold i e => .fold i e.loopExit
  | .unfold i e => .unfold i e.loopExit
  | e => e
/-- `loopExit` of arguments. -/
partial def JsArgs.loopExit {C M : List JsTy} {σs : List JsTy} : JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons a.loopExit as.loopExit
/-- `loopExit` of the parts of an array literal. -/
partial def JsParts.loopExit {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem e.loopExit rest.loopExit
  | .spread a rest => .spread a.loopExit rest.loopExit
/-- The counting loops of a block left at the first iteration after which nothing changes (see
    the module documentation), bottom-up. -/
partial def JsBlock.loopExit {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret e.loopExit
  | .next => .next
  | .jump j e => .jump j e.loopExit
  | .throw m => .throw m
  | .raise e => .raise e.loopExit
  | .const x e rest => .const x e.loopExit rest.loopExit
  | .letMut x e rest => JsBlock.mkLetMut x e.loopExit rest.loopExit
  | .assign x e rest => .assign x e.loopExit rest.loopExit
  | .destructure e sel rest => .destructure e.loopExit sel rest.loopExit
  | .ite c t e => .ite c.loopExit t.loopExit e.loopExit
  | .enumCases e arms => .enumCases e.loopExit arms.loopExit
  | .unionCases e arms => .unionCases e.loopExit arms.loopExit
  | .join x block rest => .join x block.loopExit rest.loopExit
  | .forRange x nt n body rest => JsBlock.mkForExit x nt n.loopExit body.loopExit rest.loopExit
  | .forOf x l xs body rest => .forOf x l xs.loopExit body.loopExit rest.loopExit
  | .forExit x nt n body done rest =>
    .forExit x nt n.loopExit body.loopExit done.loopExit rest.loopExit
  | .countdown x nt n base step rest =>
    .countdown x nt n.loopExit base.loopExit step.loopExit rest.loopExit
  | .tick nt j base rest => .tick nt j base.loopExit rest.loopExit
  | .natCase x nt n zero succ => .natCase x nt n.loopExit zero.loopExit succ.loopExit
  | .funs hints defs rest => .funs hints defs.loopExit rest.loopExit
/-- `loopExit` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.loopExit {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons b.loopExit rest.loopExit
/-- `loopExit` in the arms of a case analysis on a union. -/
partial def JsUnionArms.loopExit {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.loopExit rest.loopExit
end

/-- The function with its counting loops left early where nothing changes any more
    (`JsBlock.loopExit`). -/
def JsFun.loopExit (f : JsFun) : JsFun := { f with body := f.body.loopExit }

end MoreJs

end
