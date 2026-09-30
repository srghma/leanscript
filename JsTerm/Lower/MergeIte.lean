module

public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Tests that end in the same statements, merged

A decision tree translated from a `match` (or from nested `if`s) often ends two tests in the
same statements: the fall-through of a test inside a branch is also the fall-through of the
test around it.

```js
if (a) {                               if (a && b) {
  if (b) { T }                   ⟶       T
  E                                    }
}                                      E
E
```

`JsBlock.mergeIte` rewrites, bottom-up, everywhere in a block (in closures too):

* `if (a) { if (b) { T } else { E } } else { E' }` to `if (a && b) { T } else { E }`, and
* `if (a) { E } else { if (b) { E' } else { T } }` to `if (a || b) { E } else { T }`,

when `E` and `E'` are the same statements (the same dump, `JsBlock.pretty`: the variables are
de Bruijn indices, and both are in the same scope, so the same dump is the same statements).
`a && b` is `a ? b : false` and `a || b` is `a ? true : b` (`JsExpr.cond`, which the printer
writes with the operators); a chain is grouped to the left (`a && b && c`).

**Why the value is the same.**  JavaScript evaluates `b` in `a && b` (resp. `a || b`) exactly
when the original evaluated the inner test: after `a`, when `a` is true (resp. false).  The
two tests are evaluated in the same order in both programs, so `E` then runs in the same state
as `E` or `E'` did.  Nothing is duplicated: a test and one copy of `E` are dropped.
-/

namespace MoreJs

variable {S : JsSig}

/-- `a && b` (`a ? b : false`), grouped to the left: `a && (b₁ && b₂)` is `(a && b₁) && b₂`. -/
partial def JsExpr.mkAnd {C M : List JsTy} (a b : JsExpr S C M (.terminal .bool)) :
    JsExpr S C M (.terminal .bool) :=
  match b with
  | .cond b₁ b₂ (.lit (.bool false)) => .cond (JsExpr.mkAnd a b₁) b₂ (.lit (.bool false))
  | b => .cond a b (.lit (.bool false))

/-- `a || b` (`a ? true : b`), grouped to the left: `a || (b₁ || b₂)` is `(a || b₁) || b₂`. -/
partial def JsExpr.mkOr {C M : List JsTy} (a b : JsExpr S C M (.terminal .bool)) :
    JsExpr S C M (.terminal .bool) :=
  match b with
  | .cond b₁ (.lit (.bool true)) b₂ => .cond (JsExpr.mkOr a b₁) (.lit (.bool true)) b₂
  | b => .cond a (.lit (.bool true)) b

/-- `if (c) { t } else { e }`, with the tests that end in the same statements merged (see the
    module documentation). -/
def JsBlock.mkIte {C M J : List JsTy} {k : JsEnd} (c : JsExpr S C M (.terminal .bool))
    (t e : JsBlock S C M J k) : JsBlock S C M J k :=
  let viaAnd? : Option (JsBlock S C M J k) := match t with
    | .ite b t' e' =>
      if e'.pretty "" == e.pretty "" then some (.ite (JsExpr.mkAnd c b) t' e') else none
    | _ => none
  match viaAnd? with
  | some r => r
  | none =>
    match e with
    | .ite b e' t' =>
      if t.pretty "" == e'.pretty "" then .ite (JsExpr.mkOr c b) t t' else .ite c t e
    | _ => .ite c t e

mutual
/-- `JsBlock.mkIte` in the closures of an expression. -/
partial def JsExpr.mergeIte {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → JsExpr S C M τ
  | .imported op as => .imported op as.mergeIte
  | .inlined op as => .inlined op as.mergeIte
  | .app f as => .app f.mergeIte as.mergeIte
  | .lam hints body => .lam hints body.mergeIte
  | .record_mk fs => .record_mk fs.mergeIte
  | .union_mk ix as => .union_mk ix as.mergeIte
  | .enumIndex nt e => .enumIndex nt e.mergeIte
  | .enumEq a b => .enumEq a.mergeIte b.mergeIte
  | .index l nt a i => .index l nt a.mergeIte i.mergeIte
  | .array_mk l ps => .array_mk l ps.mergeIte
  | .list_mk ps => .list_mk ps.mergeIte
  | .cond c a b => .cond c.mergeIte a.mergeIte b.mergeIte
  | .listOp op as => .listOp op as.mergeIte
  | .fold i e => .fold i e.mergeIte
  | .unfold i e => .unfold i e.mergeIte
  | e => e
/-- `mergeIte` of arguments. -/
partial def JsArgs.mergeIte {C M : List JsTy} {σs : List JsTy} : JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons a.mergeIte as.mergeIte
/-- `mergeIte` of the parts of an array literal. -/
partial def JsParts.mergeIte {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem e.mergeIte rest.mergeIte
  | .spread a rest => .spread a.mergeIte rest.mergeIte
/-- `JsBlock.mkIte` everywhere in a block, bottom-up. -/
partial def JsBlock.mergeIte {C M J : List JsTy} {k : JsEnd} : JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret e.mergeIte
  | .next => .next
  | .jump j e => .jump j e.mergeIte
  | .throw m => .throw m
  | .const x e rest => .const x e.mergeIte rest.mergeIte
  | .letMut x e rest => .letMut x e.mergeIte rest.mergeIte
  | .assign x e rest => .assign x e.mergeIte rest.mergeIte
  | .destructure e sel rest => .destructure e.mergeIte sel rest.mergeIte
  | .ite c t e => JsBlock.mkIte c.mergeIte t.mergeIte e.mergeIte
  | .enumCases e arms => .enumCases e.mergeIte arms.mergeIte
  | .unionCases e arms => .unionCases e.mergeIte arms.mergeIte
  | .join x block rest => .join x block.mergeIte rest.mergeIte
  | .forRange x nt n body rest => .forRange x nt n.mergeIte body.mergeIte rest.mergeIte
  | .forOf x l xs body rest => .forOf x l xs.mergeIte body.mergeIte rest.mergeIte
  | .countdown x nt n base step rest =>
    .countdown x nt n.mergeIte base.mergeIte step.mergeIte rest.mergeIte
  | .tick nt j base rest => .tick nt j base.mergeIte rest.mergeIte
  | .natCase x nt n zero succ => .natCase x nt n.mergeIte zero.mergeIte succ.mergeIte
  | .funs hints defs rest => .funs hints defs.mergeIte rest.mergeIte
/-- `mergeIte` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.mergeIte {C M J : List JsTy} {k : JsEnd} {n : Nat} :
    JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons b.mergeIte rest.mergeIte
/-- `mergeIte` in the arms of a case analysis on a union. -/
partial def JsUnionArms.mergeIte {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)} :
    JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel b.mergeIte rest.mergeIte
end

/-- The function with its tests that end in the same statements merged. -/
def JsFun.mergeIte (f : JsFun) : JsFun := { f with body := f.body.mergeIte }

end MoreJs

end
