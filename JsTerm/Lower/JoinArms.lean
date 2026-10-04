module

public import JsTerm.Syntax.Pretty
public import JsTerm.Syntax.Vars.Occs

@[expose] public section

set_option autoImplicit false

/-!
# Join points written into the arms that jump to them, or into the variable they feed

Two rewrites of a join point `join x { block } rest` (`let x; L: { block } rest`), everywhere in
a block (in closures too), bottom-up (`JsBlock.joinArms`):

**Every arm passes the same field.**  When `block` is a case analysis on a union each of whose
arms takes exactly one field apart, the field at the same position in every arm, and only
jumps to the join point with it, the rest is written in each arm instead, reading the field:

```js
let x;                                       // every arm is the same now: the printer writes
if (a.tag === 0) { x = a._1; }        ⟶      // it once, without a test (`sameUnionArms`)
else { x = a._1; }                           return f(a._1) + 1;
return f(x) + 1;
```

The arms are the same statements (the same field position, the same `rest`), so the printer
writes them once, without the test, and the field is read where it is used: `Term` has no
expression for "the field at position `i`, whatever the constructor", so the join point of
`match a with | .error b => b | .ok c => c` followed by `f v + 1` can only go once the arms
print the same.  Nothing is duplicated in the output, and no call is: each arm still runs
`rest` once, on the same value.

**The value goes straight into a variable.**  When `rest` starts by assigning the value to a
mutable variable (`m = x;`) and reads `x` nowhere else, every jump to the join point assigns
the variable itself:

```js
let x;                                       if (p.tag === 0) {
if (p.tag === 0) {                             p = { tag: 1, _1: p._1 + 1 };
  x = { tag: 1, _1: p._1 + 1 };       ⟶      } else {
} else {                                       p = { tag: 0, _1: p._1 - 1 };
  x = { tag: 0, _1: p._1 - 1 };              }
}
p = x;
```

**Why the value is the same.**  A jump ends the block: its value is computed, assigned, and
nothing of the block runs after it, so assigning `m` there instead of right after the block
changes nothing that is read (the value is computed before `m` is assigned, as before).  The
jumps out of a loop body (`for`, the counting-down loop) or a closure are to their own join
points, never to this one, so the rewrite never moves an assignment into a loop.
-/

namespace MoreJs

variable {S : JsSig}

/-! ## Every arm passes the same field -/

/-- Is the block `jump j x` where `j` is the innermost join point and `x` the innermost
    constant? -/
def JsBlock.isJumpHeadOfHead {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → Bool
  | .jump j (.cvar x) => j.index == 0 && x.index == 0
  | _ => false

/-- The arms of a case analysis on a union, inside the block of a join point (of type `τ`),
    each with `rest` in place of the arm, when every arm takes exactly one field (of type `τ`)
    apart and only jumps to the join point with it; with the position of the field each arm
    takes. -/
def JsUnionArms.jumpField? {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    (rest : JsBlock S (τ :: C) M J k) :
    {cs : List (List JsTy)} → JsUnionArms S C M (τ :: J) k cs →
      Option (List (List Nat) × JsUnionArms S C M J k cs)
  | [], .nil => some ([], .nil)
  | _ :: _, .cons (us := us) sel b more =>
    if !b.isJumpHeadOfHead then none else
    match us, sel with
    | [u], sel =>
      if h : u = τ then
        match JsUnionArms.jumpField? rest more with
        | some (ps, more') =>
          some ((sel.binds.map (·.1)) :: ps, .cons sel (by subst h; exact rest) more')
        | none => none
      else none
    | _, _ => none

/-- `join x { block } rest` with `rest` written in the arms of `block` (see the module
    documentation), when they all take the field at the same position apart. -/
def JsBlock.joinIntoArms? {C M J : List JsTy} {τ : JsTy} {k : JsEnd}
    (block : JsBlock S C M (τ :: J) k) (rest : JsBlock S (τ :: C) M J k) :
    Option (JsBlock S C M J k) :=
  match block with
  | .unionCases e arms =>
    match arms.jumpField? rest with
    | some (p :: ps, arms') => if ps.all (· == p) then some (.unionCases e arms') else none
    | _ => none
  | _ => none

/-! ## The value goes straight into a variable -/

mutual
/-- The block with every jump to the join point `jv` (of type `σ`) passing `e` replaced by
    `m = e;` and a jump passing no value; `none` when a jump passes no value already. -/
partial def JsBlock.assignJumps {C M J : List JsTy} {σ : JsTy} {k : JsEnd} (jv : JsMem J σ)
    (m : JsMem M σ) : JsBlock S C M J k → Option (JsBlock S C M J k)
  | .jump (τ := τ') j e =>
    if j.index != jv.index then some (.jump j e) else
    match e with
    | .unreachable _ => none
    | e => if h : τ' = σ then some (.assign m (h ▸ e) (.jump j (.unreachable τ'))) else none
  | .ret e => some (.ret e)
  | .next => some .next
  | .throw msg => some (.throw msg)
  | .raise e => some (.raise e)
  | .const x e rest => (.const x e) <$> rest.assignJumps jv m
  | .letMut x e rest => (.letMut x e) <$> rest.assignJumps jv (.succ m)
  | .assign x e rest => (.assign x e) <$> rest.assignJumps jv m
  | .destructure e sel rest => (.destructure e sel) <$> rest.assignJumps jv m
  | .ite c t e => do return .ite c (← t.assignJumps jv m) (← e.assignJumps jv m)
  | .enumCases e arms => (.enumCases e) <$> arms.assignJumps jv m
  | .unionCases e arms => (.unionCases e) <$> arms.assignJumps jv m
  | .join x block rest => do
    return .join x (← block.assignJumps (.succ jv) m) (← rest.assignJumps jv m)
  | .forRange x nt n body rest => (.forRange x nt n body) <$> rest.assignJumps jv m
  | .forOf x l xs body rest => (.forOf x l xs body) <$> rest.assignJumps jv m
  | .countdown x nt n base step rest => (.countdown x nt n base step) <$> rest.assignJumps jv m
  | .forExit x nt n body done rest => (.forExit x nt n body done) <$> rest.assignJumps jv m
  | .tick nt j base rest => do
    return .tick nt j (← base.assignJumps jv m) (← rest.assignJumps jv m)
  | .natCase x nt n zero succ => do
    return .natCase x nt n (← zero.assignJumps jv m) (← succ.assignJumps jv m)
  | .funs hints defs rest => (.funs hints defs) <$> rest.assignJumps jv m
/-- `assignJumps` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.assignJumps {C M J : List JsTy} {σ : JsTy} {k : JsEnd} {n : Nat}
    (jv : JsMem J σ) (m : JsMem M σ) : JsEnumArms S C M J k n → Option (JsEnumArms S C M J k n)
  | .nil => some .nil
  | .cons b rest => do return .cons (← b.assignJumps jv m) (← rest.assignJumps jv m)
/-- `assignJumps` in the arms of a case analysis on a union. -/
partial def JsUnionArms.assignJumps {C M J : List JsTy} {σ : JsTy} {k : JsEnd}
    {cs : List (List JsTy)} (jv : JsMem J σ) (m : JsMem M σ) :
    JsUnionArms S C M J k cs → Option (JsUnionArms S C M J k cs)
  | .nil => some .nil
  | .cons sel b rest => do return .cons sel (← b.assignJumps jv m) (← rest.assignJumps jv m)
end

/-- `join x { block } m = x; rest` (`rest` not reading `x`), with every jump of `block`
    assigning `m` itself (see the module documentation). -/
def JsBlock.joinIntoAssign? {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String)
    (block : JsBlock S C M (τ :: J) k) (rest : JsBlock S (τ :: C) M J k) :
    Option (JsBlock S C M J k) :=
  match rest with
  | .assign (τ := σ) m (.cvar x) rest' =>
    if x.index != 0 || rest'.mentions ⟨false, 0⟩ then none else
    if h : σ = τ then
      (fun b => .join hint b rest') <$> block.assignJumps .zero (h ▸ m)
    else none
  | _ => none

/-- A join point, rewritten when one of the two rewrites applies (block and rest already
    walked). -/
def JsBlock.mkJoin {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (hint : String)
    (block : JsBlock S C M (τ :: J) k) (rest : JsBlock S (τ :: C) M J k) : JsBlock S C M J k :=
  match JsBlock.joinIntoArms? block rest with
  | some b => b
  | none => (JsBlock.joinIntoAssign? hint block rest).getD (.join hint block rest)

/-! ## The walk -/

mutual
/-- `JsBlock.joinArms` in the closures of an expression. -/
partial def JsExpr.joinArms {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => .imported op as.joinArms
  | .inlined op as => .inlined op as.joinArms
  | .app f as => .app f.joinArms as.joinArms
  | .lam hints body => .lam hints body.joinArms
  | .record_mk fs => .record_mk fs.joinArms
  | .union_mk ix as => .union_mk ix as.joinArms
  | .enumIndex nt e => .enumIndex nt e.joinArms
  | .enumEq a b => .enumEq a.joinArms b.joinArms
  | .boolCmp op a b => .boolCmp op a.joinArms b.joinArms
  | .index l nt a i => .index l nt a.joinArms i.joinArms
  | .indexOr l nt a i d => .indexOr l nt a.joinArms i.joinArms d.joinArms
  | .array_mk l ps => .array_mk l ps.joinArms
  | .list_mk ps => .list_mk ps.joinArms
  | .cond c a b => .cond c.joinArms a.joinArms b.joinArms
  | .listOp op as => .listOp op as.joinArms
  | .fold i e => .fold i e.joinArms
  | .unfold i e => .unfold i e.joinArms
  | e => e
/-- `joinArms` of arguments. -/
partial def JsArgs.joinArms {C M : List JsTy} {σs : List JsTy} : JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons a.joinArms as.joinArms
/-- `joinArms` of the parts of an array literal. -/
partial def JsParts.joinArms {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem e.joinArms rest.joinArms
  | .spread a rest => .spread a.joinArms rest.joinArms
/-- The join points of a block rewritten (see the module documentation), bottom-up. -/
partial def JsBlock.joinArms {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret e.joinArms
  | .next => .next
  | .jump j e => .jump j e.joinArms
  | .throw m => .throw m
  | .raise e => .raise e.joinArms
  | .const x e rest => .const x e.joinArms rest.joinArms
  | .letMut x e rest => .letMut x e.joinArms rest.joinArms
  | .assign x e rest => .assign x e.joinArms rest.joinArms
  | .destructure e sel rest => .destructure e.joinArms sel rest.joinArms
  | .ite c t e => .ite c.joinArms t.joinArms e.joinArms
  | .enumCases e arms => .enumCases e.joinArms arms.joinArms
  | .unionCases e arms => .unionCases e.joinArms arms.joinArms
  | .join x block rest => JsBlock.mkJoin x block.joinArms rest.joinArms
  | .forRange x nt n body rest => .forRange x nt n.joinArms body.joinArms rest.joinArms
  | .forOf x l xs body rest => .forOf x l xs.joinArms body.joinArms rest.joinArms
  | .countdown x nt n base step rest =>
    .countdown x nt n.joinArms base.joinArms step.joinArms rest.joinArms
  | .forExit x nt n body done rest =>
    .forExit x nt n.joinArms body.joinArms done.joinArms rest.joinArms
  | .tick nt j base rest => .tick nt j base.joinArms rest.joinArms
  | .natCase x nt n zero succ => .natCase x nt n.joinArms zero.joinArms succ.joinArms
  | .funs hints defs rest => .funs hints defs.joinArms rest.joinArms
/-- `joinArms` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.joinArms {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons b.joinArms rest.joinArms
/-- `joinArms` in the arms of a case analysis on a union. -/
partial def JsUnionArms.joinArms {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.joinArms rest.joinArms
end

/-- The function with its join points rewritten (`JsBlock.joinArms`). -/
def JsFun.joinArms (f : JsFun) : JsFun := { f with body := f.body.joinArms }

end MoreJs

end
