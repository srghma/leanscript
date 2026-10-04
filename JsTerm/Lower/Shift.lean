module

public import JsTerm.Lower.Basic

@[expose] public section

set_option autoImplicit false

/-!
# Shifts of 64-bit bit vectors under the test of their count

A shift of `BitVec 64` by a bit vector (`x <<< y`, `x >>> y`) answers `0` once the count reaches
`64`, while the shift of `UInt64` takes its count modulo `64`.  The translator reads it
(`bitvecShiftCall?`, `LeanScript/TermElab/ToTerm/Expr/Calls.lean`) as the shift of `UInt64`
under the test of the count:

```
y < 64 ? (x <<< y) : 0        -- `x <<< y` the shift of `UInt64`, count modulo 64
```

At the `BigInt` representation of `UInt64` the shift of `UInt64` is
`BigInt.asUintN(64, a << (b & 63n))` (left) and `a >> (b & 63n)` (right), and at the `number`
representation the right shift is `Math.floor(a / 2 ** (b % 64))`.  Under the test the count is
below `64`, so the mask is the identity, and the right shift needs no test at all: a right shift
of a value below `2 ^ 64` by `64` or more is `0` already (`a >> b`, `Math.floor(a / 2 ** b)`;
`2 ** b` is `Infinity` from `b = 1024` on, and `a / Infinity` is `0`).  So the conversion
(`JsExpr.condShift?`, at a conditional of `JsTerm.Lower.FromTerm`) writes

| shift | `BigInt` | `number` |
| --- | --- | --- |
| left | `b < 64n ? BigInt.asUintN(64, a << b) : 0n` | (unchanged: the runtime checks the result) |
| right | `a >> b` | `Math.floor(a / 2 ** b)` |

A shift of `UInt64` by a literal count below `64` drops the mask the same way
(`JsExpr.litShift?`: `BigInt.asUintN(64, a << 3n)`, `a >> 60n`, `Math.floor(a / 2 ** 60)`).

These reuse the operations of `Nat.shiftLeft`, `Nat.shiftRight` and `UInt64.ofNat` at the same
representation (a `UInt64` and a `Nat` are both a `BigInt`, or both a `number`).  The rewrite is
only done when the count and the shifted value are constants (seen through operations that are
the identity in JavaScript, like `UInt64.ofBitVec`): reading them without the test, or reading
the count once more, computes nothing.  The equalities are proved in `RuntimeSpec/InlineShift.lean`
(`uint64_shift_right_guarded`, `uint64_shift_left_guarded`, …).

The rewrite cannot be done on `Term`: the language's shift of `UInt64` takes its count modulo
`64` (it is Lean's), and its naturals have no representation to share with `UInt64`.
-/

namespace MoreJs

variable {S : JsSig}

/-- The constant an expression is, seen through operations that are the identity in JavaScript
    (`UInt64.ofBitVec`, `UInt64.toBitVec`, …: their template is their argument), by its
    de Bruijn index. -/
def JsExpr.idConst? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option Nat
  | .cvar x => some x.index
  | .inlined op (.cons a .nil) =>
    match op.template with
    | .arg 0 => match a with
      | .cvar x => some x.index
      | .inlined op' (.cons a' .nil) =>
        match op'.template, a' with
        | .arg 0, .cvar x => some x.index
        | _, _ => none
      | _ => none
    | _ => none
  | _ => none

/-- The natural number a literal is (of any representation), seen through operations that are
    the identity in JavaScript. -/
def JsExpr.anyNatLit? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option Nat
  | .lit (.bigint_nat k) => some k
  | .lit (.uint53 k _) => some k
  | .lit (.bitvec_small v) => some v
  | .lit (.bigint_bitvec_big v) => some v
  | .lit (.int53_bitvec_big v _) => some v
  | .inlined op (.cons a .nil) =>
    match op.template, a with
    | .arg 0, .lit (.bigint_nat k) => some k
    | .arg 0, .lit (.uint53 k _) => some k
    | .arg 0, .lit (.bitvec_small v) => some v
    | .arg 0, .lit (.bigint_bitvec_big v) => some v
    | .arg 0, .lit (.int53_bitvec_big v _) => some v
    | _, _ => none
  | _ => none

/-- The shift of `UInt64` by the constant `v` in `x` (seen through operations that are the
    identity), written for a count below `64`: the expression, and whether it still needs the
    test of the count (`true` for the left shift, whose result is masked). -/
def JsExpr.shiftUnderTest? {C M : List JsTy} {τ : JsTy} (v : Nat) :
    JsExpr S C M τ → Option (JsExpr S C M τ × Bool)
  | .inlined .bigint_nat__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
    if b.idConst? == some v && a.idConst?.isSome then
      some (.inlined .bigint_nat__lean_nat_shiftr (.cons a (.cons b .nil)), false)
    else none
  | .inlined .uint53__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
    if b.idConst? == some v && a.idConst?.isSome then
      some (.inlined .uint53__lean_nat_shiftr (.cons a (.cons b .nil)), false)
    else none
  | .inlined .bigint_nat__lean_uint64_shift_left (.cons a (.cons b .nil)) =>
    if b.idConst? == some v then
      some (.inlined .bigint_nat__lean_uint64_of_nat__UInt64_ofNat
        (.cons (.inlined .bigint_nat__lean_nat_shiftl (.cons a (.cons b .nil))) .nil), true)
    else none
  | .inlined op (.cons s .nil) =>
    match op.template with
    | .arg 0 =>
      match s with
      | .inlined .bigint_nat__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
        if b.idConst? == some v && a.idConst?.isSome then
          some (.inlined op (.cons (.inlined .bigint_nat__lean_nat_shiftr
            (.cons a (.cons b .nil))) .nil), false)
        else none
      | .inlined .uint53__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
        if b.idConst? == some v && a.idConst?.isSome then
          some (.inlined op (.cons (.inlined .uint53__lean_nat_shiftr
            (.cons a (.cons b .nil))) .nil), false)
        else none
      | .inlined .bigint_nat__lean_uint64_shift_left (.cons a (.cons b .nil)) =>
        if b.idConst? == some v then
          some (.inlined op (.cons (.inlined .bigint_nat__lean_uint64_of_nat__UInt64_ofNat
            (.cons (.inlined .bigint_nat__lean_nat_shiftl (.cons a (.cons b .nil))) .nil)) .nil),
            true)
        else none
      | _ => none
    | _ => none
  | _ => none

/-- `b < 64 ? (a <<< b) : 0` (a shift of `UInt64`, count modulo `64`, under the test of the
    count; the shape of a shift of `BitVec 64` by a bit vector) without the mask of the count,
    and, for a right shift, without the test (`JsTerm.Lower.Shift`). -/
def JsExpr.condShift? {C M : List JsTy} {τ : JsTy} (c : JsExpr S C M (.terminal .bool))
    (x d : JsExpr S C M τ) : Option (JsExpr S C M τ) :=
  if d.anyNatLit? != some 0 then none else
  let count? : Option Nat := match c with
    | .inlined .bigint_nat__lean_uint64_dec_lt (.cons b (.cons k .nil)) =>
      if k.anyNatLit? == some 64 then b.idConst? else none
    | .inlined .uint53__lean_uint64_dec_lt (.cons b (.cons k .nil)) =>
      if k.anyNatLit? == some 64 then b.idConst? else none
    | _ => none
  match count? with
  | none => none
  | some v =>
    match x.shiftUnderTest? v with
    | some (x', true) => some (.cond c x' d)
    | some (x', false) => some x'
    | none => none

/-- A shift of `UInt64` by a literal count below `64` without the mask of its count:
    `BigInt.asUintN(64, a << 3n)`, `a >> 60n`, `Math.floor(a / 2 ** 60)`. -/
def JsExpr.litShift? {C M : List JsTy} {τ : JsTy} : JsExpr S C M τ → Option (JsExpr S C M τ)
  | .inlined .bigint_nat__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
    if (b.anyNatLit?.map (decide <| · < 64)) == some true then
      some (.inlined .bigint_nat__lean_nat_shiftr (.cons a (.cons b .nil)))
    else none
  | .inlined .uint53__lean_uint64_shift_right (.cons a (.cons b .nil)) =>
    if (b.anyNatLit?.map (decide <| · < 64)) == some true then
      some (.inlined .uint53__lean_nat_shiftr (.cons a (.cons b .nil)))
    else none
  | .inlined .bigint_nat__lean_uint64_shift_left (.cons a (.cons b .nil)) =>
    if (b.anyNatLit?.map (decide <| · < 64)) == some true then
      some (.inlined .bigint_nat__lean_uint64_of_nat__UInt64_ofNat
        (.cons (.inlined .bigint_nat__lean_nat_shiftl (.cons a (.cons b .nil))) .nil))
    else none
  | _ => none

end MoreJs

end
