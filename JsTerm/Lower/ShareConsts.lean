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

/-- The functions `funs`, the value of each constant reading the values of the constants before
    it by their names (see the module documentation). -/
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
    else
      out := out.push f
  return out.toList

end MoreJs

end
