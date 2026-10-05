module

public import JsTerm.Lower.BoolCmp

@[expose] public section

set_option autoImplicit false

/-!
# Comparisons of a totally ordered type, written with the operator that reads best

A rewrite of the conversion from `Term` (`JsTerm.Lower.FromTerm`), local to the comparison
being converted.  Lean's externs only compare with `<` and `≤` (`lean_nat_dec_lt`,
`lean_string_dec_lt`, …): `a > b` reaches the conversion as `b < a`, `a ≥ b` on `String` (and on
`Char`, whose comparisons are those of one-character strings) as `!(a < b)`, …

| Lean | extern call | before | now |
|---|---|---|---|
| `a > b` | `lt(b, a)` | `b < a` | `a > b` |
| `a ≥ b` (`Nat`) | `le(b, a)` | `b <= a` | `a >= b` |
| `a ≤ b` (`String`) | `!lt(b, a)` | `!(b < a)` | `a <= b` |
| `a ≥ b` (`String`) | `!lt(a, b)` | `!(a < b)` | `a >= b` |
| `'a' ≤ c && c ≤ 'z'` (`Char`) | `lt(c, "a") ? false : !lt("z", c)` | `(c < "a" ? false : !("z" < c))` | `c >= "a" && c <= "z"` |

**When.**  Only for an inlined operation written `x < y` or `x <= y` on two values of a terminal
type that JavaScript orders totally (`JsTerminalTy.totalOrd`: booleans, integers as `number`s or
`BigInt`s, strings), never on a float: `!(x < y)` is not `x >= y` when one of them is `NaN`.

* `!(x op y)` is `x op' y` (`JsBoolCmp.neg`), with the same operands in the same order, whatever
  they are;
* `c ? false : y` and `c ? y : true`, on such a comparison `c`, are `c' && y` and `c' || y` with
  the opposite comparison `c'`: `c` is still computed first, and `y` for the same values;
* `x op y` is written `y op'' x` (`>` for `<`, …; also on floats, as this needs no totality)
  only when `x` and `y` are two constants with `y` bound first (a parameter to the left of
  `x`), or when `x` is a literal and `y` is not (`"z" >= c` is `c <= "z"`): reading a constant or
  a literal has no effect and cannot throw, so the order in which the operands are computed
  does not matter.  Other comparisons (`i < a.length`, `y < 64`, `b + 1 < a`) are left as they
  are, so the rewrites that recognise them later still do.

**Why it is right** (`JsOrd`, below).  JavaScript defines the relational operators from one
comparison, *IsLessThan*, which answers `undefined` only for `NaN`: `a > b` is `b < a`,
`a <= b` is `!(b < a)` and `a >= b` is `!(a < b)` (with `false` for `undefined`).  When
*IsLessThan* never answers `undefined`, the identities used here follow.

`Term` has no `>` nor `>=` to rewrite to (its externs are Lean's), so this cannot be done on
`Term`; it is done here rather than on `JsTerm`, where the comparison is built once from its
parts.
-/

namespace MoreJs

variable {S : JsSig}

/-! ## A model of JavaScript's relational operators -/

/-- JavaScript's relational operators on a type whose *IsLessThan* is `lt` (`none` for
    `undefined`, the answer when a `NaN` is compared). -/
structure JsOrd (α : Type) where
  /-- *IsLessThan*. -/
  lt : α → α → Option Bool

namespace JsOrd

variable {α : Type} (o : JsOrd α)

/-- `a op b`, as the ECMAScript specification defines it from *IsLessThan* (`undefined` reads
    as `false`).  Equality is not defined from *IsLessThan* and is not modelled here. -/
def eval : JsBoolCmp → α → α → Bool
  | .lt, a, b => (o.lt a b).getD false
  | .gt, a, b => (o.lt b a).getD false
  | .le, a, b => ((o.lt b a).map (!·)).getD false
  | .ge, a, b => ((o.lt a b).map (!·)).getD false
  | .eq, _, _ => false
  | .ne, _, _ => false

/-- *IsLessThan* never answers `undefined` (no `NaN`). -/
def Total : Prop := ∀ a b, (o.lt a b).isSome

/-- The comparison with its operands swapped: `x op y` is `y op.flip x`. -/
def _root_.MoreJs.JsBoolCmp.flip : JsBoolCmp → JsBoolCmp
  | .lt => .gt | .gt => .lt | .le => .ge | .ge => .le | .eq => .eq | .ne => .ne

/-- `y > x` is `x < y`, `y >= x` is `x <= y`, … (for any *IsLessThan*). -/
theorem eval_flip (op : JsBoolCmp) (x y : α) : o.eval op.flip y x = o.eval op x y := by
  cases op <;> rfl

/-- With no `NaN`, `!(x op y)` is `x op.neg y`, for the relational operators. -/
theorem eval_neg (ht : o.Total) (op : JsBoolCmp) (x y : α) (h : op ≠ .eq ∧ op ≠ .ne) :
    o.eval op.neg x y = !o.eval op x y := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (ht x y)
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (ht y x)
  cases op <;> simp_all [eval, JsBoolCmp.neg]

/-- Without the totality, `!(x < y)` and `x >= y` differ: with `NaN`, both `x < y` and `x >= y`
    are `false`. -/
theorem eval_neg_needs_total :
    let o : JsOrd Unit := ⟨fun _ _ => none⟩
    o.eval JsBoolCmp.lt.neg () () ≠ !o.eval .lt () () := by
  decide

end JsOrd

/-! ## The rewrite -/

/-- Does JavaScript order the values of this terminal type totally with `<` (*IsLessThan* never
    `undefined`)?  Booleans, integers (`number`s that are integers, `BigInt`s) and strings do;
    floats do not (`NaN`), and the string slices are arrays. -/
def JsTerminalTy.totalOrd : JsTerminalTy → Bool
  | .float | .float32 | .substring | .stringSlice => false
  | _ => true

/-- The comparison an inlined operation is, when its JavaScript is `x < y` or `x <= y` of its
    two arguments in order. -/
def JsOpInlinable.ordCmp? {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpInlinable e t σs τ) : Option JsBoolCmp :=
  match op.template with
  | .bin "<" (.arg 0) (.arg 1) => some .lt
  | .bin "<=" (.arg 0) (.arg 1) => some .le
  | _ => none

/-- `x op y` (`op` one of `<`, `<=`, …) of two values of a terminal type, by its parts: an
    inlined comparison (`JsOpInlinable.ordCmp?`) or a comparison already rewritten.  With
    `total`, only on a totally ordered terminal type (`JsTerminalTy.totalOrd`); without it, also
    on floats (enough to swap the operands, `JsOrd.eval_flip`, not to negate). -/
def JsExpr.ordCmpParts? {C M : List JsTy} (total : Bool := true) : JsExpr S C M (.terminal .bool) →
    Option ((t : JsTerminalTy) × JsBoolCmp × JsExpr S C M (.terminal t) × JsExpr S C M (.terminal t))
  | .inlined (σs := σs) op args =>
    match op.ordCmp?, σs, args with
    | some c, [.terminal t, .terminal t'], .cons x (.cons y .nil) =>
      if h : t = t' then
        if t.totalOrd || (!total && (t == .float || t == .float32)) then some ⟨t, c, x, h ▸ y⟩
        else none
      else none
    | _, _, _ => none
  | .boolCmp (t := t) op x y =>
    if (t.totalOrd || (!total && (t == .float || t == .float32))) && (op != .eq && op != .ne) then
      some ⟨t, op, x, y⟩
    else none
  | _ => none

/-- Is the expression a literal? -/
def JsExpr.isLiteral {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .lit _ => true
  | _ => false

/-- The level of a constant (its position counting from the outside, as `Ref.c`). -/
def JsExpr.cLvl? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option Nat
  | .cvar x => some (C.length - 1 - x.index)
  | _ => none

/-- Should `x op y` be written `y op.flip x`?  When the result reads better and computing the
    operands in the other order makes no difference, because one of them is a constant or a
    literal (reading one has no effect and cannot throw, and a constant never changes):
    * `5 < x` is `x > 5`, `"z" >= c` is `c <= "z"`: a literal on the left, anything else on the
      right;
    * `b < a` is `a > b`: two parameters of the innermost enclosing function (their levels are
      `params`), the one to the left on the left.  Not any two constants: `i < n`, a counter
      bound after the bound `n`, stays as it is. -/
def JsExpr.swapOperands {C M : List JsTy} {τ : JsTy} (params : List Nat)
    (x y : JsExpr S C M τ) : Bool :=
  (x.isLiteral && !y.isLiteral) ||
    match x.cLvl?, y.cLvl? with
    | some lx, some ly => params.contains lx && params.contains ly && ly < lx
    | _, _ => false

/-- `x op y`, its operands swapped when `JsExpr.swapOperands` says so. -/
def JsExpr.ordCmpNice {C M : List JsTy} {t : JsTerminalTy} (params : List Nat) (op : JsBoolCmp)
    (x y : JsExpr S C M (.terminal t)) : JsExpr S C M (.terminal .bool) :=
  if x.swapOperands params y then .boolCmp op.flip y x else .boolCmp op x y

/-- A comparison (of a totally ordered type, or of floats) whose operands read better the other
    way round (`JsExpr.swapOperands`), so written: `b < a` is `a > b` (see the module docstring).
    `none` for any other expression, which is then kept as it is. -/
def JsExpr.ordFlip? {C M : List JsTy} {τ : JsTy} (e : JsExpr S C M τ) (params : List Nat) :
    Option (JsExpr S C M τ) :=
  match τ, e with
  | .terminal .bool, e => do
    let ⟨_, op, x, y⟩ ← e.ordCmpParts? (total := false)
    if x.swapOperands params y then some (.boolCmp op.flip y x) else none
  | _, _ => none

/-- Is the inlined operation `x === y` or `x !== y` of its two arguments in order? -/
def JsOpInlinable.isEqCmp {e : Effectfulness} {t : MayThrow} {σs : List JsTy} {τ : JsTy}
    (op : JsOpInlinable e t σs τ) : Bool :=
  match op.template with
  | .bin "===" (.arg 0) (.arg 1) => true
  | .bin "!==" (.arg 0) (.arg 1) => true
  | _ => false

/-- An equality `x === y` (or `x !== y`) whose operands read better the other way round
    (`JsExpr.swapOperands`: `"a" === c` is `c === "a"`), so written.  `===` is symmetric for
    every pair of values (`NaN` included), and reading a literal or a constant has no effect, so
    the order the operands are computed in does not matter.  The operation stays the same
    inlined operation, so the rewrites that recognise it later still do. -/
def JsExpr.eqFlip? {C M : List JsTy} {τ : JsTy} (params : List Nat) :
    JsExpr S C M τ → Option (JsExpr S C M τ)
  | .inlined (σs := [σ, σ']) op (.cons x (.cons y .nil)) =>
    if h : σ' = σ then
      match σ', h, op, y with
      | _, rfl, op, y =>
        if op.isEqCmp && x.swapOperands params y then some (.inlined op (.cons y (.cons x .nil)))
        else none
    else none
  | _ => none

/-- The negation `!(x op y)` of a comparison of a totally ordered type, as the opposite
    comparison `x op.neg y` (then with its operands swapped if they read better so). -/
def JsExpr.negOrdCmp? {C M : List JsTy} (params : List Nat) (e : JsExpr S C M (.terminal .bool)) :
    Option (JsExpr S C M (.terminal .bool)) := do
  let ⟨_, op, x, y⟩ ← e.ordCmpParts?
  some (JsExpr.ordCmpNice params op.neg x y)

/-- A conditional of booleans on a comparison `c` of a totally ordered type, whose arms make it
    a negation, with the opposite comparison `c'` (`JsExpr.negOrdCmp?`):
    * `c ? false : true` (`!c`) is `c'`;
    * `c ? false : y` is `c' ? y : false`, written `c' && y`;
    * `c ? y : true` is `c' ? true : y`, written `c' || y`.
    The condition is still computed first, and `y` only for the same values of the operands. -/
def JsExpr.condNegOrd? {C M : List JsTy} {τ : JsTy} (params : List Nat)
    (c : JsExpr S C M (.terminal .bool))
    (a b : JsExpr S C M τ) : Option (JsExpr S C M τ) :=
  match τ, a, b with
  | .terminal .bool, .lit (.bool false), .lit (.bool true) => c.negOrdCmp? params
  | .terminal .bool, .lit (.bool false), y => do
    let c' ← c.negOrdCmp? params
    some (.cond c' y (.lit (.bool false)))
  | .terminal .bool, y, .lit (.bool true) => do
    let c' ← c.negOrdCmp? params
    some (.cond c' (.lit (.bool true)) y)
  | _, _, _ => none

end MoreJs

end
