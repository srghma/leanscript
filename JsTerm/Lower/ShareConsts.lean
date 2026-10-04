module

public import JsTerm.Syntax.Pretty

@[expose] public section

set_option autoImplicit false

/-!
# Constants of the module sharing the values of the constants before them

`Term` has no global definitions: a definition reading a constant of the module has its value
inlined, so the module writes that value again in each of them:

```js
export const extern1 = [1, 2, 0];                    export const extern1 = [1, 2, 0];
export const extern2 = [[1, 2, 0], [3], [0]];   ⟶   export const extern2 = [extern1, [3], [0]];
export const test3 = [1, 2, 0];                      export const test3 = extern1;
export const test4 = [[1, 2, 0], [3], [0]];          export const test4 = extern2;
```

`shareConstValues` reads, in the value of each constant (`JsFun.isConst`, a body `return e;`),
each value built of arrays, lists, records and constructors (`JsExpr.isShareable`) that is
written exactly as the whole value of a constant before it (the same dump, `JsExpr.pretty`,
which writes literals, constructors and typed arrays as they are printed) as that constant, by
its name (`JsExpr.global`), outermost first, as purescript-backend-optimizer refers to
`extern1` instead of writing its value again.

This keeps what the module computes: the values of the translated programs are never updated
in place once shared (a constant is shared by every reader, `JsFun.isConst`), so reading the
value of the constant is reading the same value; the constant comes before, so it is computed
when it is read (its value was computed without throwing, since the module got there).
Only the values of constants are rewritten, never the body of a function: a function returns
a fresh array, which a version owning it may update in place (`LeanScript.Term.Ownership`).
-/

namespace MoreJs

variable {S : JsSig}

/-- Are there no parts? -/
def JsParts.isNil {C M : List JsTy} {A E : JsTy} : JsParts S C M A E → Bool
  | .nil => true
  | _ => false

/-- Are there no arguments? -/
def JsArgs.isNil {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => true
  | _ => false

/-- Is the expression a value built of arrays, lists, records and constructors with at least one
    part (not `[]` nor `{ tag: 0 }`, which are as short as a name)? -/
def JsExpr.isShareable {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .array_mk _ ps | .list_mk ps => !ps.isNil
  | .record_mk fs => !fs.isNil
  | .union_mk _ as => !as.isNil
  | .fold _ e => e.isShareable
  | _ => false

mutual
/-- Each part of the expression that is the value of a constant of `tbl` (its dump, the name of
    the constant) read as that constant, outermost first. -/
partial def JsExpr.shareConsts {C M : List JsTy} {τ : JsTy} (tbl : List (String × String))
    (e : JsExpr S C M τ) : JsExpr S C M τ :=
  match (if e.isShareable then tbl.lookup (e.pretty "") else none) with
  | some g => .global g
  | none =>
    match e with
    | .array_mk l ps => .array_mk l (ps.shareConsts tbl)
    | .list_mk ps => .list_mk (ps.shareConsts tbl)
    | .record_mk fs => .record_mk (fs.shareConsts tbl)
    | .union_mk ix as => .union_mk ix (as.shareConsts tbl)
    | .fold i e => .fold i (e.shareConsts tbl)
    | e => e
/-- `shareConsts` of each argument. -/
partial def JsArgs.shareConsts {C M σs : List JsTy} (tbl : List (String × String)) :
    JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons (a.shareConsts tbl) (as.shareConsts tbl)
/-- `shareConsts` of each part of an array literal. -/
partial def JsParts.shareConsts {C M : List JsTy} {A E : JsTy} (tbl : List (String × String)) :
    JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem (e.shareConsts tbl) (rest.shareConsts tbl)
  | .spread a rest => .spread (a.shareConsts tbl) (rest.shareConsts tbl)
end

/-- The dump of the value of a block `return e;` when `e` is shareable (`JsExpr.isShareable`). -/
def JsBlock.shareableRet? {C M J : List JsTy} {τ : JsTy} :
    JsBlock S C M J (.ret τ) → Option String
  | .ret e => if e.isShareable then some (e.pretty "") else none
  | _ => none

/-- `shareConsts` of the value of a block `return e;`. -/
def JsBlock.shareConstsRet {C M J : List JsTy} {τ : JsTy} (tbl : List (String × String)) :
    JsBlock S C M J (.ret τ) → JsBlock S C M J (.ret τ)
  | .ret e => .ret (e.shareConsts tbl)
  | b => b

/-! ## Inside functions: frozen values only -/

mutual
/-- Is the expression a value no program ever updates in place: literals, constructors of enums,
    records and constructors of unions holding such values (no array, no list: an array a
    function returns may be updated in place by a version owning it,
    `LeanScript.Term.Ownership`; records and constructors are never updated in place)? -/
partial def JsExpr.isFrozen {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .lit _ => true
  | .enum_mk _ _ _ => true
  | .record_mk fs => fs.isFrozen
  | .union_mk _ as => as.isFrozen
  | .fold _ e => e.isFrozen
  | _ => false
/-- `JsExpr.isFrozen` of each argument. -/
partial def JsArgs.isFrozen {C M σs : List JsTy} : JsArgs S C M σs → Bool
  | .nil => true
  | .cons a as => a.isFrozen && as.isFrozen
end

mutual
/-- Each frozen value (`JsExpr.isFrozen`) of the expression that is the value of a constant of
    `tbl` read as that constant, outermost first, in closures too. -/
partial def JsExpr.shareFrozen {C M : List JsTy} {τ : JsTy} (tbl : List (String × String))
    (e : JsExpr S C M τ) : JsExpr S C M τ :=
  match (if e.isShareable && e.isFrozen then tbl.lookup (e.pretty "") else none) with
  | some g => .global g
  | none =>
    match e with
    | .imported op as => .imported op (as.shareFrozen tbl)
    | .inlined op as => .inlined op (as.shareFrozen tbl)
    | .app f as => .app (f.shareFrozen tbl) (as.shareFrozen tbl)
    | .lam hints body => .lam hints (body.shareFrozen tbl)
    | .record_mk fs => .record_mk (fs.shareFrozen tbl)
    | .union_mk ix as => .union_mk ix (as.shareFrozen tbl)
    | .enumIndex nt e => .enumIndex nt (e.shareFrozen tbl)
    | .enumEq a b => .enumEq (a.shareFrozen tbl) (b.shareFrozen tbl)
    | .index l nt a i => .index l nt (a.shareFrozen tbl) (i.shareFrozen tbl)
    | .indexOr l nt a i d =>
      .indexOr l nt (a.shareFrozen tbl) (i.shareFrozen tbl) (d.shareFrozen tbl)
    | .array_mk l ps => .array_mk l (ps.shareFrozen tbl)
    | .list_mk ps => .list_mk (ps.shareFrozen tbl)
    | .cond c a b => .cond (c.shareFrozen tbl) (a.shareFrozen tbl) (b.shareFrozen tbl)
    | .listOp op as => .listOp op (as.shareFrozen tbl)
    | .fold i e => .fold i (e.shareFrozen tbl)
    | .unfold i e => .unfold i (e.shareFrozen tbl)
    | e => e
/-- `shareFrozen` of each argument. -/
partial def JsArgs.shareFrozen {C M σs : List JsTy} (tbl : List (String × String)) :
    JsArgs S C M σs → JsArgs S C M σs
  | .nil => .nil
  | .cons a as => .cons (a.shareFrozen tbl) (as.shareFrozen tbl)
/-- `shareFrozen` of each part of an array literal. -/
partial def JsParts.shareFrozen {C M : List JsTy} {A E : JsTy} (tbl : List (String × String)) :
    JsParts S C M A E → JsParts S C M A E
  | .nil => .nil
  | .elem e rest => .elem (e.shareFrozen tbl) (rest.shareFrozen tbl)
  | .spread a rest => .spread (a.shareFrozen tbl) (rest.shareFrozen tbl)
/-- `shareFrozen` everywhere in a block. -/
partial def JsBlock.shareFrozen {C M J : List JsTy} {k : JsEnd} (tbl : List (String × String)) :
    JsBlock S C M J k → JsBlock S C M J k
  | .ret e => .ret (e.shareFrozen tbl)
  | .next => .next
  | .jump j e => .jump j (e.shareFrozen tbl)
  | .throw m => .throw m
  | .raise e => .raise (e.shareFrozen tbl)
  | .const x e rest => .const x (e.shareFrozen tbl) (rest.shareFrozen tbl)
  | .letMut x e rest => .letMut x (e.shareFrozen tbl) (rest.shareFrozen tbl)
  | .assign x e rest => .assign x (e.shareFrozen tbl) (rest.shareFrozen tbl)
  | .destructure e sel rest => .destructure (e.shareFrozen tbl) sel (rest.shareFrozen tbl)
  | .ite c t e => .ite (c.shareFrozen tbl) (t.shareFrozen tbl) (e.shareFrozen tbl)
  | .enumCases e arms => .enumCases (e.shareFrozen tbl) (arms.shareFrozen tbl)
  | .unionCases e arms => .unionCases (e.shareFrozen tbl) (arms.shareFrozen tbl)
  | .join x block rest => .join x (block.shareFrozen tbl) (rest.shareFrozen tbl)
  | .forRange x nt n body rest =>
    .forRange x nt (n.shareFrozen tbl) (body.shareFrozen tbl) (rest.shareFrozen tbl)
  | .forOf x l xs body rest =>
    .forOf x l (xs.shareFrozen tbl) (body.shareFrozen tbl) (rest.shareFrozen tbl)
  | .countdown x nt n base step rest =>
    .countdown x nt (n.shareFrozen tbl) (base.shareFrozen tbl) (step.shareFrozen tbl)
      (rest.shareFrozen tbl)
  | .forExit x nt n body done rest =>
    .forExit x nt (n.shareFrozen tbl) (body.shareFrozen tbl) (done.shareFrozen tbl)
      (rest.shareFrozen tbl)
  | .tick nt j base rest => .tick nt j (base.shareFrozen tbl) (rest.shareFrozen tbl)
  | .natCase x nt n zero succ =>
    .natCase x nt (n.shareFrozen tbl) (zero.shareFrozen tbl) (succ.shareFrozen tbl)
  | .funs hints defs rest => .funs hints (defs.shareFrozen tbl) (rest.shareFrozen tbl)
/-- `shareFrozen` in the arms of a case analysis on an enum. -/
partial def JsEnumArms.shareFrozen {C M J : List JsTy} {k : JsEnd} {n : Nat}
    (tbl : List (String × String)) : JsEnumArms S C M J k n → JsEnumArms S C M J k n
  | .nil => .nil
  | .cons b rest => .cons (b.shareFrozen tbl) (rest.shareFrozen tbl)
/-- `shareFrozen` in the arms of a case analysis on a union. -/
partial def JsUnionArms.shareFrozen {C M J : List JsTy} {k : JsEnd} {cs : List (List JsTy)}
    (tbl : List (String × String)) : JsUnionArms S C M J k cs → JsUnionArms S C M J k cs
  | .nil => .nil
  | .cons sel b rest => .cons sel (b.shareFrozen tbl) (rest.shareFrozen tbl)
end

/-- The functions `funs`, the value of each constant reading the values of the constants before
    it by their names (see the module documentation), and each frozen value
    (`JsExpr.isFrozen`) written in the body of a function that is the value of a constant before
    it read as that constant: `f({ _1: 99, _2: 0, _3: 11 })` is `f(extern)`, as
    purescript-backend-optimizer writes it.  Only the constants *before* the function are read:
    a constant after it may not be computed yet when a constant between the two calls it. -/
def shareConstValues (funs : List JsFun) : List JsFun := Id.run do
  let mut tbl : List (String × String) := []
  let mut out : Array JsFun := #[]
  for f in funs do
    if f.isConst && f.alias?.isNone && f.delegate?.isNone then
      let key? := f.body.shareableRet?
      let f' := if tbl.isEmpty then f else { f with body := f.body.shareConstsRet tbl }
      if let some key := key? then
        if (tbl.lookup key).isNone then tbl := tbl ++ [(key, f.name)]
      out := out.push f'
    else if !f.isConst && !tbl.isEmpty then
      out := out.push { f with body := f.body.shareFrozen tbl }
    else
      out := out.push f
  return out.toList

end MoreJs

end
