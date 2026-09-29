module

public import LanguageJavascriptCommon.Types

@[expose] public section

set_option autoImplicit false

/-!
# `number` literals

How a JavaScript `number` (an IEEE double) is written in the source the backend prints: a
small integer as itself (`12`, `-3`), the special values as `NaN`, `Infinity`, `-Infinity` and
`-0`, and every other value as the **shortest** decimal that reads back as the same double
(`0.1`, `1e-7`, `5e-324`).

A double is kept as the core library's model of IEEE floats, `Float.Model.UnpackedFloat`
(`f.toModel.unpack`): not a number, a signed infinity, a signed zero, or `± m * 2 ^ e` with
`m > 0`.  A `Float32` unpacks to the same shape (`Float32.toModel`), and its value is a double
too, so the two share `NumberForm.finiteDecimal`: the decimal printed for a `Float32` reads
back as that double exactly (a `number` holding a `Float32` is always one `Math.fround` has
rounded, so the literal must not be a shorter decimal that only rounds to the same `Float32`).
The decimal is a `Language.JavaScript.JSNumber`, the literal type of the JavaScript trees, and
is spelled with its `render`.
-/

namespace MoreJs

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)
open Language.JavaScript (JSNumber)

/-- The shortest decimal `(digits, exponent)` with `digits * 10 ^ exponent` reading back as
    the double `m * 2 ^ e` (`m > 0`). -/
def shortestDecimal (m : Nat) (e : Int) : Nat × Int :=
  -- the exact value as `D * 10 ^ (-K)`
  let (D, K) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat, 0) else (m * 5 ^ e.natAbs, e.natAbs)
  let exact : Float := Float.ofScientific D true K
  let L := (toString D).length
  let rec go (fuel k : Nat) : Nat × Int :=
    match fuel with
    | 0 => (D, -(K : Int))
    | fuel + 1 =>
      if k ≥ L then (D, -(K : Int)) else
      let drop := L - k
      let q := D / 10 ^ drop
      let r := D % 10 ^ drop
      let q := if 2 * r ≥ 10 ^ drop then q + 1 else q
      let ex : Int := (drop : Int) - K
      let f : Float := if ex ≥ 0 then Float.ofScientific q false ex.toNat
        else Float.ofScientific q true ex.natAbs
      if f.toBits == exact.toBits then (q, ex) else go fuel (k + 1)
  go 20 1

/-- A `number` literal: an integer, or a double taken apart by the core library's model
    (`Float.Model.UnpackedFloat`: not a number, a signed infinity, a signed zero, or
    `± m * 2 ^ e`).  The decimal digits of a double are only worked out when it is written
    (`finiteDecimal`), and written with the literal type of the JavaScript trees
    (`Language.JavaScript.JSNumber`). -/
inductive NumberForm where
  /-- An integer, written as itself. -/
  | int (n : Int)
  /-- A double. -/
  | float (u : UnpackedFloat)
  deriving Inhabited, Repr, BEq

namespace NumberForm

/-- The value `m * 2 ^ e` as a natural number, when it is an integer of at most `2 ^ 53`. -/
def smallNat? (m : Nat) (e : Int) : Option Nat :=
  let v? : Option Nat :=
    if e ≥ 0 then some (m * 2 ^ e.toNat)
    else if m % 2 ^ e.natAbs == 0 then some (m / 2 ^ e.natAbs) else none
  match v? with
  | some v => if v ≤ 2 ^ 53 then some v else none
  | none => none

/-- The positive double `m * 2 ^ e` (`m > 0`) as a base ten literal: the integer itself when
    it is one of at most `2 ^ 53`, the shortest decimal that reads back as it otherwise. -/
def finiteDecimal (m : Nat) (e : Int) : JSNumber :=
  match smallNat? m e with
  | some v => .decimal v 0
  | none => let (d, ex) := shortestDecimal m e; JSNumber.normalize (.decimal d ex)

/-- The form of a double. -/
def ofFloat (f : Float) : NumberForm := .float f.toModel.unpack

/-- The form of a `Float32`, as the double that holds it. -/
def ofFloat32 (f : Float32) : NumberForm := .float f.toModel.unpack

/-- `JSNumber.render` writes a positive exponent without a sign (`1e21`, as `prettier` does);
    `Number.prototype.toString` writes it with one (`1e+21`). -/
def withExponentSign (s : String) : String := String.ofList (go s.toList)
where
  /-- A `+` after the first `e`, unless a `-` follows it. -/
  go : List Char → List Char
    | [] => []
    | c :: cs =>
      if c = 'e' then (if cs.head? = some '-' then c :: cs else c :: '+' :: cs)
      else c :: go cs

/-- `"-"` for a negative sign. -/
def signPrefix : Sign → String
  | .negative => "-"
  | .positive => ""

/-- The form as JavaScript source, spelled as `String(x)` spells the number in JavaScript. -/
def source : NumberForm → String
  | .int n => toString n
  | .float .notANumber => "NaN"
  | .float (.infinity s) => signPrefix s ++ "Infinity"
  | .float (.zero s) => signPrefix s ++ "0"
  | .float (.finite s m e _) => signPrefix s ++ withExponentSign (finiteDecimal m e).render

end NumberForm

/-- A `number`, as JavaScript source. -/
def numberSource (f : Float) : String := (NumberForm.ofFloat f).source

/-- A `Float32` (a `number` rounded by `Math.fround`), as JavaScript source. -/
def float32Source (f : Float32) : String := (NumberForm.ofFloat32 f).source

end MoreJs

end
