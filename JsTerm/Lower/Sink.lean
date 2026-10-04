module

public import JsTerm.Syntax.Vars.Occs
public import JsTerm.Syntax.Vars.Rename

@[expose] public section

set_option autoImplicit false

/-!
# Constants computed only on the path that reads them

A constant read only in one branch that comes right after it is computed in that branch:

```js
const x = p + 1n;                          if (j === 0n) {
if (j === 0n) { return { _1: x }; }   ⟶      return { _1: p + 1n };
j--;                                       }
…  (x not read)                            j--; …
```

(`JsBlock.sink`: `const x = e;` followed by a test of a loop counter, `if (j === 0) { base }
j--; rest`, or by `if (c) { t } else { f }`, and read by only one of the two ways on.)  The
constant, now read once right where it is computed, is then written at its use by the printer.
The loop step saves the computation on every iteration that does not end the loop.

**When.**  Skipping the computation on the other path, and doing it after the test instead of
before, must not change anything: `e` has no effect, cannot throw, and reads only variables and
numbers, booleans or strings (`JsExpr.sinkable`: operations that are pure and never throw, on
leaf types only, so no array or record that an update in place could change); and the test in
between (`c`; the test of the counter reads it only) has no effect either, so it assigns no
mutable variable that `e` reads.
-/

namespace MoreJs

variable {S : JsSig}

/-- Is the type a leaf (a number, a boolean, a string…)? -/
def JsTy.isLeaf : JsTy → Bool
  | .terminal _ => true
  | _ => false

mutual
/-- Can the expression be computed later, or not at all: variables, literals and operations
    that are pure and never throw, on leaf types. -/
def JsExpr.sinkable {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .mvar _ | .lit _ | .enum_mk .. => true
  | .inlined (σs := σs) (e := .pure) (t := .doesntThrow) _ as =>
    τ.isLeaf && σs.all JsTy.isLeaf && as.sinkable
  | .imported (σs := σs) (e := .pure) (t := .doesntThrow) _ as =>
    τ.isLeaf && σs.all JsTy.isLeaf && as.sinkable
  | _ => false
/-- `sinkable` of arguments. -/
def JsArgs.sinkable {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => true
  | .cons a as => a.sinkable && as.sinkable
end

/-- The renaming dropping the innermost constant (`none` for it). -/
def dropC0 {C : List JsTy} {τ : JsTy} : JsRenM Option (τ :: C) C := fun x =>
  match x with
  | .zero => none
  | .succ y => some y

/-- `const x = e;` then `rest` (already rewritten), the constant moved into the only branch
    that reads it, when `rest` starts with a test and `e` can wait (`JsExpr.sinkable`). -/
partial def JsBlock.sinkConst {C M J : List JsTy} {τ : JsTy} {k : JsEnd} (x : String)
    (e : JsExpr S C M τ) (rest : JsBlock S (τ :: C) M J k) : JsBlock S C M J k :=
  let keep := JsBlock.const x e rest
  if !e.sinkable then keep else
  match rest with
  | .tick nt j base r =>
    match r.renameM dropC0 (fun y => some y) with
    | some r' => .tick nt j (JsBlock.sinkConst x e base) r'
    | none => keep
  | .ite c t f =>
    match c.renameM dropC0 (fun y => some y) with
    | some c' =>
      if !c'.noEffect then keep else
      match f.renameM dropC0 (fun y => some y), t.renameM dropC0 (fun y => some y) with
      | some f', _ => .ite c' (JsBlock.sinkConst x e t) f'
      | none, some t' => .ite c' t' (JsBlock.sinkConst x e f)
      | none, none => keep
    | none => keep
  | _ => keep

mutual
/-- `sinkConst` everywhere in the expression (in the bodies of its closures). -/
partial def JsExpr.sink {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => .imported op as.sink
  | .inlined op as => .inlined op as.sink
  | .app f as => .app f.sink as.sink
  | .lam hints body => .lam hints body.sink
  | .record_mk fs => .record_mk fs.sink
  | .union_mk ix as => .union_mk ix as.sink
  | .enumIndex nt e => .enumIndex nt e.sink
  | .enumEq a b => .enumEq a.sink b.sink
  | .index l nt a i => .index l nt a.sink i.sink
  | .indexOr l nt a i d => .indexOr l nt a.sink i.sink d.sink
  | .array_mk l ps => .array_mk l ps.sink
  | .list_mk ps => .list_mk ps.sink
  | .cond c a b => .cond c.sink a.sink b.sink
  | .listOp op as => .listOp op as.sink
  | .fold i e => .fold i e.sink
  | .unfold i e => .unfold i e.sink
  | e => e
/-- `sink` of arguments. -/
partial def JsArgs.sink {C M σs : List JsTy} : JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons a.sink as.sink
/-- `sink` of the parts of an array literal. -/
partial def JsParts.sink {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem e.sink rest.sink
  | .spread a rest => .spread a.sink rest.sink
/-- `sinkConst` everywhere in the block, bottom-up. -/
partial def JsBlock.sink {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret e.sink
  | .next => .next
  | .jump j e => .jump j e.sink
  | .throw m => .throw m
  | .raise e => .raise e.sink
  | .const x e rest => JsBlock.sinkConst x e.sink rest.sink
  | .letMut x e rest => .letMut x e.sink rest.sink
  | .assign x e rest => .assign x e.sink rest.sink
  | .destructure e sel rest => .destructure e.sink sel rest.sink
  | .ite c t e => .ite c.sink t.sink e.sink
  | .enumCases e arms => .enumCases e.sink arms.sink
  | .unionCases e arms => .unionCases e.sink arms.sink
  | .join x block rest => .join x block.sink rest.sink
  | .forRange x nt n body rest => .forRange x nt n.sink body.sink rest.sink
  | .forOf x l xs body rest => .forOf x l xs.sink body.sink rest.sink
  | .countdown x nt n base step rest => .countdown x nt n.sink base.sink step.sink rest.sink
  | .forExit x nt n body done rest => .forExit x nt n.sink body.sink done.sink rest.sink
  | .tick nt j base rest => .tick nt j base.sink rest.sink
  | .natCase x nt n zero succ => .natCase x nt n.sink zero.sink succ.sink
  | .funs hints defs rest => .funs hints defs.sink rest.sink
/-- `sink` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.sink {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons b.sink rest.sink
/-- `sink` in the arms of a case analysis on a union. -/
partial def JsUnionArms.sink {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.sink rest.sink
end

/-- The function with its constants computed only on the paths that read them. -/
def JsFun.sink (f : JsFun) : JsFun := { f with body := f.body.sink }

end MoreJs

end
