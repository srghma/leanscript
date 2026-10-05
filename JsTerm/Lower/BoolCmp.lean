module

public import JsTerm.Lower.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Conditionals of booleans written as comparisons of booleans

A rewrite of the conversion from `Term` (`JsTerm.Lower.FromTerm`), local to the conditional
being converted.  `Term` has no operation comparing two booleans: Lean's `==`, `!=`, `<`, `≤`
on `Bool` are case analyses (`Bool.decEq`, `Bool.decLt`, …, are not externs), which reach the
conversion as conditionals of booleans:

| Lean | `Term` | before | now |
|---|---|---|---|
| `a == b` | `cond(a, b, cond(b, false, true))` | `a ? b : !b` | `a === b` |
| `a != b` | `cond(cond(a, b, …), false, true)` | `!(a ? b : !b)` | `a !== b` |
| `a < b` | `cond(a, false, b)` | `a ? false : b` | `a < b` |
| `a > b` | `cond(b, false, a)` | `b ? false : a` | `a > b` |
| `a ≤ b` | `cond(a, b, true)` | `a ? b : true` | `a <= b` |
| `a ≥ b` | `cond(b, a, true)` | `b ? a : true` | `a >= b` |

JavaScript compares two booleans as the numbers `0` and `1`, so `a < b` is `!a && b`, `a <= b`
is `!a || b`, … (`JsBoolCmp.eval`; the theorems below are the identities each rewrite relies on).

**Evaluation order.**  A comparison always computes both operands, left first; a conditional
computes its condition first, then one arm.  So:

* `c ? y : !y` (and `c ? !y : y`) computes `c` then `y` either way: it is `c === y` (`c !== y`)
  for any condition `c`, when both copies of `y` are the same variable;
* `c ? false : y` and `c ? y : true` compute `y` only for one value of `c`: they are `c < y` and
  `c <= y` only when `c` and `y` are both variables (reading a variable has no effect).  A
  condition that is not a variable keeps its conditional, which also avoids `x < 5 < y`.  As
  both are variables, the one bound first (the parameter to the left) is written on the left:
  `b ? false : a` is `a > b` rather than `b < a` (`JsExpr.varCmp`);
* the negation `!(x op y)` of a comparison is the opposite comparison (`JsBoolCmp.neg`:
  `x !== y` for `x === y`, `x >= y` for `x < y`, …), with the same operands in the same order.

This cannot be done on `Term`, which has no comparison of booleans to rewrite to (its externs are
those of Lean, and Lean's comparisons of `Bool` are not externs), and it is done here rather than
on `JsTerm` because here the conditional is built once from its parts.
-/

namespace MoreJs

variable {S : JsSig}

/-! ## The identities -/

/-- `c ? y : !y` is `c === y`. -/
theorem JsBoolCmp.eval_eq (c y : Bool) : (if c then y else !y) = JsBoolCmp.eval .eq c y := by
  cases c <;> cases y <;> rfl

/-- `c ? !y : y` is `c !== y`. -/
theorem JsBoolCmp.eval_ne (c y : Bool) : (if c then !y else y) = JsBoolCmp.eval .ne c y := by
  cases c <;> cases y <;> rfl

/-- `c ? false : y` is `c < y`, and `y > c`. -/
theorem JsBoolCmp.eval_lt (c y : Bool) :
    (if c then false else y) = JsBoolCmp.eval .lt c y ∧
      (if c then false else y) = JsBoolCmp.eval .gt y c := by
  cases c <;> cases y <;> decide

/-- `c ? y : true` is `c <= y`, and `y >= c`. -/
theorem JsBoolCmp.eval_le (c y : Bool) :
    (if c then y else true) = JsBoolCmp.eval .le c y ∧
      (if c then y else true) = JsBoolCmp.eval .ge y c := by
  cases c <;> cases y <;> decide

/-- `!x` (`x ? false : true`) of a comparison is the opposite comparison. -/
theorem JsBoolCmp.cond_neg (op : JsBoolCmp) (x y : Bool) :
    (if op.eval x y then false else true) = op.neg.eval x y := by
  rw [JsBoolCmp.eval_neg]; cases op.eval x y <;> rfl

/-! ## The rewrite -/

/-- Is the expression a variable (a constant or a mutable variable)?  Reading one has no
    effect. -/
def JsExpr.isVar {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Bool
  | .cvar _ | .mvar _ => true
  | _ => false

/-- Are the two expressions the same variable? -/
def JsExpr.sameVar {C M : List JsTy} {τ σ : JsTy} : JsExpr S C M τ → JsExpr S C M σ → Bool
  | .cvar x, .cvar y => x.index == y.index
  | .mvar x, .mvar y => x.index == y.index
  | _, _ => false

/-- Is the first expression a constant bound before the second one (a parameter to the left of
    it, …)?  Only decides on which side of a comparison of two variables each one is written. -/
def JsExpr.boundBefore {C M : List JsTy} {τ σ : JsTy} : JsExpr S C M τ → JsExpr S C M σ → Bool
  | .cvar x, .cvar y => x.index > y.index
  | _, _ => false

/-- The boolean `y` of `!y` (`y ? false : true`). -/
def JsExpr.notOf? {C M : List JsTy} : JsExpr S C M (.terminal .bool) →
    Option (JsExpr S C M (.terminal .bool))
  | .cond y (.lit (.bool false)) (.lit (.bool true)) => some y
  | _ => none

/-- The negation of a comparison of booleans, as the opposite comparison (`JsBoolCmp.neg`).
    Only of booleans: a comparison of floats (`JsTerm.Lower.OrdCmp`) is not negated so
    (`NaN`). -/
def JsExpr.negBoolCmp? {C M : List JsTy} : JsExpr S C M (.terminal .bool) →
    Option (JsExpr S C M (.terminal .bool))
  | .boolCmp (t := t) op x y => if t == .bool then some (.boolCmp op.neg x y) else none
  | _ => none

/-- `x op y` of two variables, written with the one bound first on the left: `y > x` rather than
    `x < y` when `y` is a parameter to the left of `x` (`flip` is the comparison with its operands
    swapped).  Reading a variable has no effect, so the order of the operands does not matter. -/
def JsExpr.varCmp {C M : List JsTy} (op flip : JsBoolCmp) (x y : JsExpr S C M (.terminal .bool)) :
    JsExpr S C M (.terminal .bool) :=
  if y.boundBefore x then .boolCmp flip y x else .boolCmp op x y

/-- `c ? a : b` on booleans as a comparison of booleans (see the module docstring). -/
def JsExpr.boolCondB {C M : List JsTy} (c : JsExpr S C M (.terminal .bool)) :
    JsExpr S C M (.terminal .bool) → JsExpr S C M (.terminal .bool) →
      Option (JsExpr S C M (.terminal .bool))
  | .lit (.bool false), .lit (.bool true) => c.negBoolCmp?
  | .lit (.bool false), y => if c.isVar && y.isVar then some (JsExpr.varCmp .lt .gt c y) else none
  | y, .lit (.bool true) => if c.isVar && y.isVar then some (JsExpr.varCmp .le .ge c y) else none
  | a, b =>
    match b.notOf? with
    | some y => if a.isVar && a.sameVar y then some (.boolCmp .eq c a) else none
    | none =>
      match a.notOf? with
      | some y => if b.isVar && b.sameVar y then some (.boolCmp .ne c b) else none
      | none => none

/-- `c ? a : b` as a comparison of booleans, when it is a conditional of booleans of one of the
    shapes of the module docstring. -/
def JsExpr.boolCond? {C M : List JsTy} {τ : JsTy} (c : JsExpr S C M (.terminal .bool))
    (a b : JsExpr S C M τ) : Option (JsExpr S C M τ) :=
  match τ, a, b with
  | .terminal .bool, a, b => JsExpr.boolCondB c a b
  | _, _, _ => none

end MoreJs

end
