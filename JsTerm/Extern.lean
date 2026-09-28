module

public import JsTerm.Syntax
public import LeanScript.Term.Extern.Name

@[expose] public section

set_option autoImplicit false

/-!
# Externs in JavaScript

A call of an extern of the catalogue (`LeanScript.Neu.extern`) becomes, in JavaScript,

* an **operator**, for the handful of externs whose meaning is a JavaScript operator at the
  chosen representation (`Nat.add` on `BigInt`s is `a + b`, `Nat.decLt` is `a < b` on
  numbers and on `BigInt`s, `String.append` is `a + b`, …), or
* a call of a **runtime helper**: a small JavaScript function emitted at the top of the
  generated module, once, only if the module calls it.  Its name is the name of the extern,
  followed, when the representation of a configurable type matters, by one letter per
  argument and for the result (`b`: a `BigInt`, `n`: a `number` standing for an unbounded or
  64-bit integer, `_`: anything else): `lean_nat_sub$bbb`, `lean_nat_sub$nnn`.

Every helper is written in the JavaScript grammar of `JsTerm.Syntax` (a `JsHelper`: its
parameters and a body of `JsStmt`s), not as JavaScript text: the prelude of a module is
printed by the same printer as the exported functions.  The small combinators of `Js` below
(`Js.v`, `Js.op`, `Js.meth`, …) only make those terms shorter to write.

The helpers are faithful to Lean's semantics at the chosen representation: `Nat.sub`
truncates at `0`, division by `0` answers `0`, fixed-width arithmetic wraps, `Int.ediv` is
Euclidean.  With a `number` representation of an unbounded type, a result that is not a safe
integer throws a `RangeError` (`$chk53`) instead of losing precision.

An extern that has no JavaScript implementation yet becomes a helper that throws when it is
called (`stubHelper`), so the rest of the module still loads and runs.
-/

namespace MoreJs

open LeanScript

/-! ## Building terms of the grammar -/

/-- The operator on `number`s of the same name as an operator on `BigInt`s. -/
def JsBigIntBinOp.toNum : JsBigIntBinOp → JsNumBinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div | .mod => .mod
  | .lt => .lt | .le => .le | .gt => .gt | .ge => .ge
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor | .shl => .shl | .shr => .shr

namespace Js

/-- A variable. -/
def v (x : String) : JsExpr := .var x
/-- A `number` literal of an integer. -/
def num (n : Int) : JsExpr := .lit (.int n)
/-- A `BigInt` literal. -/
def big (n : Int) : JsExpr := .lit (.bigint n)
/-- An integer literal at the layout `t` (a `BigInt` or a `number`). -/
def intAt (t : JsTerm) (n : Int) : JsExpr := if t.isBigInt then big n else num n
/-- A string literal. -/
def str (s : String) : JsExpr := .lit (.str s)
/-- A boolean literal. -/
def bool (b : Bool) : JsExpr := .lit (.bool b)
/-- `undefined`. -/
def undef : JsExpr := .var "undefined"
/-- `Infinity`. -/
def inf : JsExpr := .var "Infinity"
/-- `f(args)`, for a global function `f` (`BigInt`, `Number`, …). -/
def call (f : String) (args : List JsExpr) : JsExpr := .call (.var f) args
/-- `o.m(args)`. -/
def meth (o : JsExpr) (m : String) (args : List JsExpr) : JsExpr := .call (.member o m) args
/-- `G.m(args)`, for a global object `G` (`Math`, `Number`, …). -/
def glob (g m : String) (args : List JsExpr) : JsExpr := meth (.var g) m args
/-- `a op b` on `number`s. -/
def nop (op : JsNumBinOp) (a b : JsExpr) : JsExpr := .bin (.num op) a b
/-- `a op b` on `BigInt`s. -/
def bop (op : JsBigIntBinOp) (a b : JsExpr) : JsExpr := .bin (.bigint op) a b
/-- `a op b` on `BigInt`s when `isBig`, on `number`s otherwise. -/
def op (isBig : Bool) (o : JsBigIntBinOp) (a b : JsExpr) : JsExpr :=
  if isBig then bop o a b else nop o.toNum a b
/-- `-a` on `BigInt`s when `isBig`, on `number`s otherwise. -/
def neg (isBig : Bool) (a : JsExpr) : JsExpr := .un (if isBig then .bigint .neg else .num .neg) a
/-- `a === b`. -/
def eq (a b : JsExpr) : JsExpr := .bin .strictEq a b
/-- `a && b`. -/
def jand (a b : JsExpr) : JsExpr := .bin (.bool .and) a b
/-- `a || b`. -/
def jor (a b : JsExpr) : JsExpr := .bin (.bool .or) a b
/-- `!a`. -/
def jnot (a : JsExpr) : JsExpr := .un (.bool .not) a
/-- `a + b` on strings. -/
def concat (a b : JsExpr) : JsExpr := .bin (.str .concat) a b
/-- `c ? a : b`. -/
def cond (c a b : JsExpr) : JsExpr := .cond c a b
/-- `e.length`. -/
def len (e : JsExpr) : JsExpr := .member e "length"
/-- `if (c) { t }`. -/
def when (c : JsExpr) (t : List JsStmt) : JsStmt := .ite c t []

/-- The parameters of a helper, `a`, `b`, `c`. -/
def a : JsExpr := v "a"
@[inherit_doc a] def b : JsExpr := v "b"
@[inherit_doc a] def c : JsExpr := v "c"

end Js

open Js

/-- The code of a layout in the name of a helper: `b` for a `BigInt`, `n` for a `number`
    standing for an unbounded or 64-bit integer, `_` otherwise. -/
def sigCode (t : JsTerm) : Char :=
  if t.isBigInt then 'b'
  else match t with
    | .uint53 | .int53 => 'n'
    | _ => '_'

/-- The suffix of a helper's name: the codes of its arguments and result, when one of them is
    configurable. -/
def sigSuffix (tys : List JsTerm) : String :=
  let cs := tys.map sigCode
  if cs.any (· != '_') then "$" ++ String.ofList cs else ""

/-- The parameters of a helper of `n` arguments: `a`, `b`, `c`, …. -/
def helperParams (n : Nat) : List String :=
  (List.range n).map fun i =>
    if i < 26 then String.singleton (Char.ofNat ('a'.toNat + i)) else s!"p{i}"

/-! ## The base helpers -/

/-- The largest safe integer of a `number`, `2^53 - 1`. -/
def safeMax : Int := 2 ^ 53 - 1

/-- The message of the `RangeError` thrown when a result does not fit in a `number`. -/
def overflowMsg : String :=
  "LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)"

/-- A result that must be a safe integer (a `number` standing for an unbounded integer). -/
def chk53 : JsHelper :=
  { name := "$chk53", params := ["x"], body := [
      when (jnot (glob "Number" "isSafeInteger" [v "x"])) [.throw "RangeError" overflowMsg],
      .ret (v "x")] }

/-- A `BigInt` that must fit in a safe integer `number`. -/
def toNum53 : JsHelper :=
  { name := "$toNum53", params := ["x"], body := [
      when (jor (bop .gt (v "x") (big safeMax)) (bop .lt (v "x") (big (-safeMax))))
        [.throw "RangeError" overflowMsg],
      .ret (call "Number" [v "x"])] }

/-- A memoised delay: `{ f, v: undefined, done: false }`. -/
def thunkHelper : JsHelper :=
  { name := "$thunk", params := ["f"], body := [
      .ret (.object [("f", v "f"), ("v", undef), ("done", bool false)])] }

/-- A memoised delay that is already computed: `{ f: undefined, v, done: true }`. -/
def thunkPureHelper : JsHelper :=
  { name := "$thunkPure", params := ["v"], body := [
      .ret (.object [("f", undef), ("v", v "v"), ("done", bool true)])] }

/-- The value of a memoised delay (computed the first time, then remembered). -/
def forceHelper : JsHelper :=
  let t := v "t"
  { name := "$force", params := ["t"], body := [
      when (jnot (.member t "done")) [
        .setMember t "v" (.call (.member t "f") []),
        .setMember t "done" (bool true),
        .setMember t "f" undef],
      .ret (.member t "v")] }

/-- The UTF-8 bytes of a string (positions of Lean strings are UTF-8 byte offsets). -/
def utf8Helper : JsHelper :=
  { name := "$utf8", params := ["s"], body := [
      .ret (meth (.new (v "TextEncoder") []) "encode" [v "s"])] }

/-- The number of UTF-8 bytes of the code point `cp`. -/
def utf8Len (cp : JsExpr) : JsExpr :=
  cond (nop .lt cp (num 0x80)) (num 1)
    (cond (nop .lt cp (num 0x800)) (num 2) (cond (nop .lt cp (num 0x10000)) (num 3) (num 4)))

/-- The code point of the one-code-point string `ch`. -/
def codePoint (ch : JsExpr) : JsExpr := meth ch "codePointAt" [num 0]

/-- The code point starting at UTF-8 byte offset `p` of `s`, and its length in bytes
    (`[ch, n]`), or `undefined` when `p` is not the start of a character. -/
def utf8AtHelper : JsHelper :=
  let (s, p, off, ch, n) := (v "s", v "p", v "off", v "ch", v "n")
  { name := "$utf8At", params := ["s", "p"], body := [
      .letMut "off" (some (num 0)),
      .forOf "ch" s [
        .const "cp" (codePoint ch),
        .const "n" (utf8Len (v "cp")),
        when (eq off p) [.ret (.array [ch, n])],
        when (nop .gt off p) [.ret undef],
        .assign "off" (nop .add off n)],
      .ret undef] }

/-- `String.Pos.Raw.set`: replace the character that starts at the UTF-8 offset `p`
    (`Pos.Raw.utf8SetAux`); the string is unchanged when no character starts there. -/
def utf8SetHelper : JsHelper :=
  let (s, p, c, off, i, ch) := (v "s", v "p", v "c", v "off", v "i", v "ch")
  { name := "$utf8Set", params := ["s", "p", "c"], body := [
      .letMut "off" (some (num 0)),
      .letMut "i" (some (num 0)),
      .forOf "ch" s [
        when (eq off p)
          [.ret (concat (concat (meth s "slice" [num 0, i]) c)
            (meth s "slice" [nop .add i (len ch)]))],
        .const "cp" (codePoint ch),
        .assign "off" (nop .add off (utf8Len (v "cp"))),
        .assign "i" (nop .add i (len ch))],
      .ret s] }

/-- `String.Pos.Raw.extract`: the characters from the one starting at the UTF-8 offset `b`
    up to (not including) the one starting at `e` (`Pos.Raw.extract.go₁`/`go₂`). -/
def utf8ExtractHelper : JsHelper :=
  let (s, b, e, off, out, started, ch) :=
    (v "s", v "b", v "e", v "off", v "out", v "started", v "ch")
  { name := "$utf8Extract", params := ["s", "b", "e"], body := [
      when (nop .ge b e) [.ret (str "")],
      .letMut "off" (some (num 0)),
      .letMut "out" (some (str "")),
      .letMut "started" (some (bool false)),
      .forOf "ch" s [
        when (jand (jnot started) (eq off b)) [.assign "started" (bool true)],
        when started [
          when (eq off e) [.ret out],
          .assign "out" (concat out ch)],
        .const "cp" (codePoint ch),
        .assign "off" (nop .add off (utf8Len (v "cp")))],
      .ret out] }

/-- A copy of an array (generic or typed) with one more element. -/
def arrayPushHelper : JsHelper :=
  let (a, x, r) := (v "a", v "x", v "r")
  { name := "$arrayPush", params := ["a", "x"], body := [
      when (glob "Array" "isArray" [a]) [.ret (.array [.spread a, x])],
      .const "r" (.new (.member a "constructor") [nop .add (len a) (num 1)]),
      .expr (meth r "set" [a]),
      .setAt r (len a) x,
      .ret r] }

/-- A copy of an array (generic or typed) with one element replaced (the array itself when
    the index is out of bounds). -/
def arraySetHelper : JsHelper :=
  let (a, i, x, r) := (v "a", v "i", v "x", v "r")
  { name := "$arraySet", params := ["a", "i", "x"], body := [
      when (nop .ge i (len a)) [.ret a],
      .const "r" (meth a "slice" []),
      .setAt r i x,
      .ret r] }

/-- A copy of an array (generic or typed) with two elements swapped (the array itself when
    an index is out of bounds). -/
def arraySwapHelper : JsHelper :=
  let (a, i, j, r, t) := (v "a", v "i", v "j", v "r", v "t")
  { name := "$arraySwap", params := ["a", "i", "j"], body := [
      when (jor (nop .ge i (len a)) (nop .ge j (len a))) [.ret a],
      .const "r" (meth a "slice" []),
      .const "t" (.at r i),
      .setAt r i (.at r j),
      .setAt r j t,
      .ret r] }

/-- `a ** b` on `BigInt`s (`b ≥ 0`), by repeated squaring. -/
def bigPowHelper : JsHelper :=
  let (r, x, e) := (v "r", v "x", v "e")
  { name := "$bigPow", params := ["a", "b"], body := [
      .letMut "r" (some (big 1)),
      .letMut "x" (some a),
      .letMut "e" (some b),
      .while (bop .gt e (big 0)) [
        when (eq (bop .bitAnd e (big 1)) (big 1)) [.assign "r" (bop .mul r x)],
        .assign "e" (bop .shr e (big 1)),
        when (bop .gt e (big 0)) [.assign "x" (bop .mul x x)]],
      .ret r] }

/-- A helper that throws: the extern has no JavaScript implementation yet. -/
def stubHelper (name : String) : JsHelper :=
  { name, params := [], body := [
      .throw "Error" s!"LeanScript: the extern {name} has no JavaScript implementation yet"] }

/-! ## Numeric conversions -/

/-- Convert the integer `e` from the layout `src` to the layout `dst` (both integers). -/
def convInt (e : JsExpr) (src dst : JsTerm) : JsExpr × List JsHelper :=
  if src.isBigInt == dst.isBigInt then (e, [])
  else if src.isBigInt then (.helper "$toNum53" [e], [toNum53])
  else (call "BigInt" [e], [])

/-- An array index as a `number`: a `BigInt` index too large for a number becomes
    `Infinity`, which is out of bounds of every array (so the bounds checks answer as Lean
    does instead of throwing). -/
def idxHelper : JsHelper :=
  { name := "$idx", params := ["x"], body := [
      .ret (cond (bop .gt (v "x") (big safeMax)) inf (call "Number" [v "x"]))] }

/-- Convert the index `e` from the integer layout `src` to a `number`. -/
def convIdx (e : JsExpr) (src : JsTerm) : JsExpr × List JsHelper :=
  if src.isBigInt then (.helper "$idx" [e], [idxHelper]) else (e, [])

/-- Check that an integer result at layout `t` is exact (a safe integer when it is a
    `number` standing for an unbounded integer). -/
def chkInt (e : JsExpr) (t : JsTerm) : JsExpr × List JsHelper :=
  match t with
  | .uint53 | .int53 => (.helper "$chk53" [e], [chk53])
  | _ => (e, [])

/-- A JavaScript typed array constructor for a layout, if it is a typed array. -/
def typedCtor? : JsTerm → Option String
  | .uint8Array => some "Uint8Array" | .uint16Array => some "Uint16Array"
  | .uint32Array => some "Uint32Array" | .int8Array => some "Int8Array"
  | .int16Array => some "Int16Array" | .int32Array => some "Int32Array"
  | .float32Array => some "Float32Array" | .float64Array => some "Float64Array"
  | .bigUint64Array => some "BigUint64Array" | .bigInt64Array => some "BigInt64Array"
  | _ => none

/-! ## Fixed-width integers -/

/-- Wrap a JavaScript integer (a `number` computed from 32-bit or smaller operands) to an
    unsigned `bits`-bit value. -/
def wrapU (bits : Nat) (e : JsExpr) : JsExpr :=
  if bits == 32 then nop .ushr e (num 0) else nop .bitAnd e (num (2 ^ bits - 1))

/-- Wrap a JavaScript integer to a signed `bits`-bit value. -/
def wrapS (bits : Nat) (e : JsExpr) : JsExpr :=
  if bits == 32 then nop .bitOr e (num 0)
  else nop .shr (nop .shl e (num (32 - bits))) (num (32 - bits))

/-- `BigInt.asIntN(bits, e)` (`signed`) or `BigInt.asUintN(bits, e)`. -/
def asN (signed : Bool) (bits : Nat) (e : JsExpr) : JsExpr :=
  glob "BigInt" (if signed then "asIntN" else "asUintN") [num bits, e]

/-- The implementation of an operation `op` of `UIntN`/`IntN` for `N ≤ 32` (a `number`),
    as the expression returned over the parameters `a`, `b`. -/
def smallFixedImpl (signed : Bool) (bits : Nat) (op : String) (argTys : List JsTerm)
    (resTy : JsTerm) : Option (JsExpr × List JsHelper) :=
  let w := if signed then wrapS bits else wrapU bits
  let arg0 := argTys.headD .bool
  let n (e : JsExpr) : Option (JsExpr × List JsHelper) := some (e, [])
  let bmod := nop .mod (nop .add (nop .mod b (num bits)) (num bits)) (num bits)
  match op with
  | "add" => n (w (nop .add a b))
  | "sub" => n (w (nop .sub a b))
  | "mul" => n (if bits == 32 then w (glob "Math" "imul" [a, b]) else w (nop .mul a b))
  | "neg" => n (w (.un (.num .neg) a))
  | "div" => n (if signed then cond (eq b (num 0)) (num 0) (w (glob "Math" "trunc" [nop .div a b]))
                else cond (eq b (num 0)) (num 0) (glob "Math" "floor" [nop .div a b]))
  | "mod" => n (cond (eq b (num 0)) a (nop .mod a b))
  | "land" => n (w (nop .bitAnd a b))
  | "lor" => n (w (nop .bitOr a b))
  | "xor" => n (w (nop .bitXor a b))
  | "complement" => n (w (.un (.num .bitNot) a))
  | "shift_left" => n (w (nop .shl a bmod))
  | "shift_right" =>
    n (if signed then nop .shr a bmod else nop .ushr a (nop .mod b (num bits)))
  | "abs" => n (w (glob "Math" "abs" [a]))
  | "dec_eq" => n (eq a b)
  | "dec_lt" => n (nop .lt a b)
  | "dec_le" => n (nop .le a b)
  | "log2" => n (cond (eq a (num 0)) (num 0) (nop .sub (num 31) (glob "Math" "clz32" [a])))
  | "to_nat" | "to_int" => some (convInt a .uint53 resTy)
  | "of_nat" | "of_int" =>
    if arg0.isBigInt then n (call "Number" [asN signed bits a])
    else if signed then n (w a)
    else n (nop .mod (nop .add (nop .mod a (num (2 ^ bits))) (num (2 ^ bits))) (num (2 ^ bits)))
  | "of_nat_mk" | "to_bitvec" => n a
  | "to_float" | "to_float32" => n a
  | _ => none

/-- The implementation of an operation of `UInt64`/`Int64` on `BigInt`s. -/
def bigFixedImpl (signed : Bool) (op : String) (argTys : List JsTerm) (resTy : JsTerm) :
    Option (JsExpr × List JsHelper) :=
  let w := asN signed 64
  let arg0 := argTys.headD .bool
  let n (e : JsExpr) : Option (JsExpr × List JsHelper) := some (e, [])
  let bmod := bop .mod (bop .add (bop .mod b (big 64)) (big 64)) (big 64)
  match op with
  | "add" => n (w (bop .add a b))
  | "sub" => n (w (bop .sub a b))
  | "mul" => n (w (bop .mul a b))
  | "neg" => n (w (.un (.bigint .neg) a))
  | "div" => n (cond (eq b (big 0)) (big 0) (w (bop .div a b)))
  | "mod" => n (cond (eq b (big 0)) a (bop .mod a b))
  | "land" => n (w (bop .bitAnd a b))
  | "lor" => n (w (bop .bitOr a b))
  | "xor" => n (w (bop .bitXor a b))
  | "complement" => n (w (.un (.bigint .bitNot) a))
  | "shift_left" => n (w (bop .shl a bmod))
  | "shift_right" => n (bop .shr a bmod)
  | "abs" => n (w (cond (bop .lt a (big 0)) (.un (.bigint .neg) a) a))
  | "dec_eq" => n (eq a b)
  | "dec_lt" => n (bop .lt a b)
  | "dec_le" => n (bop .le a b)
  | "log2" =>
    n (cond (eq a (big 0)) (big 0)
      (call "BigInt" [nop .sub (len (meth a "toString" [num 2])) (num 1)]))
  | "to_nat" | "to_int" | "to_int_sint" => some (convInt a .nat resTy)
  | "of_nat" | "of_int" => let (e, hs) := convInt a arg0 .nat; some (w e, hs)
  | "of_nat_mk" | "to_bitvec" => n a
  | "to_float" | "to_float32" => n (call "Number" [a])
  | _ => none

/-- The operations of `UInt64`/`Int64` whose result is the 64-bit type itself. -/
def fixedResultIsSelf (op : String) : Bool :=
  ["add", "sub", "mul", "neg", "div", "mod", "land", "lor", "xor", "complement",
   "shift_left", "shift_right", "abs", "log2", "of_nat", "of_int", "of_nat_mk"].contains op

/-- Parse `lean_uint8_add` into `(false, 8, "add")`, `lean_int64_to_int_sint` into
    `(true, 64, "to_int_sint")`. -/
def parseFixed? (sym : String) : Option (Bool × Nat × String) := do
  let rest ← sym.dropPrefix? "lean_" |>.map (·.toString)
  let (signed, rest) ← if rest.startsWith "uint" then some (false, rest.drop 4 |>.toString)
    else if rest.startsWith "int" then some (true, rest.drop 3 |>.toString) else none
  let digits := rest.takeWhile Char.isDigit |>.toString
  let bits ← digits.toNat?
  unless [8, 16, 32, 64].contains bits do none
  let op := (rest.drop (digits.length + 1)).toString
  return (signed, bits, op)

/-- Conversions between fixed widths: `lean_uint32_to_uint8`, `lean_int8_to_int64`. -/
def fixedConvImpl (signed : Bool) (fromBits : Nat) (op : String) (resTy : JsTerm) :
    Option (JsExpr × List JsHelper) := do
  let pre := if signed then "to_int" else "to_uint"
  let toBits ← (op.dropPrefix? pre).bind (·.toString.toNat?)
  unless [8, 16, 32, 64].contains toBits do none
  if fromBits == 64 then
    if toBits == 64 then return (a, []) else
    if resTy.isBigInt then return (a, []) else
    -- from a `BigInt` (or a `number` standing for one) to a small width
    return (call "Number" [asN signed toBits (call "BigInt" [a])], [])
  else if toBits == 64 then
    return (if resTy.isBigInt then call "BigInt" [a] else a, [])
  else if toBits ≥ fromBits then return (a, [])
  else return ((if signed then wrapS toBits else wrapU toBits) a, [])

/-! ## The implementations -/

/-- The conversions between a float and its model (`Float.toModel`, `Float.ofModel`, and the
    same for `Float32`): a model is laid out as the float it models, so they are the identity. -/
def floatModelIds : List String :=
  ["lean_float_to_bits__Float_toModel", "lean_float_of_bits__Float_ofModel",
   "lean_float32_to_bits__Float32_toModel", "lean_float32_of_bits__Float32_ofModel"]

/-- The expression a helper returns, over its parameters `a`, `b`, `c`, …, and the helpers
    it calls; `none` when the extern has no implementation yet (or its helper needs more than
    a `return`, `externImpl?`). -/
def externExpr? (name : String) (argTys : List JsTerm) (resTy : JsTerm) :
    Option (JsExpr × List JsHelper) :=
  let sym := externSymbol name
  let t0 := argTys.headD .bool
  let isBig := t0.isBigInt
  let z := intAt t0 0
  let n (e : JsExpr) : Option (JsExpr × List JsHelper) := some (e, [])
  -- `(a op b)` computed on `BigInt`s, for `a`, `b` at the layout of the first argument
  let viaBig (o : JsBigIntBinOp) : JsExpr :=
    if isBig then bop o a b else call "Number" [bop o (call "BigInt" [a]) (call "BigInt" [b])]
  let fround (e : JsExpr) : JsExpr := glob "Math" "fround" [e]
  let f32 := sym.startsWith "lean_float32"
  let flt (e : JsExpr) : Option (JsExpr × List JsHelper) := n (if f32 then fround e else e)
  match name with
  | "lean_uint32_of_nat__Char_ofNatAux" =>
    n (glob "String" "fromCodePoint" [call "Number" [a]])
  | _ =>
  match sym with
  -- Nat
  | "lean_nat_add" => some (chkInt (op isBig .add a b) resTy)
  | "lean_nat_sub" => n (cond (op isBig .gt a b) (op isBig .sub a b) z)
  | "lean_nat_mul" => some (chkInt (op isBig .mul a b) resTy)
  | "lean_nat_div" | "lean_nat_div_exact" =>
    n (if isBig then cond (eq b (big 0)) (big 0) (bop .div a b)
       else cond (eq b (num 0)) (num 0) (glob "Math" "floor" [nop .div a b]))
  | "lean_nat_mod" => n (cond (eq b z) a (op isBig .mod a b))
  | "lean_nat_pow" =>
    if isBig then some (.helper "$bigPow" [a, b], [bigPowHelper])
    else some (chkInt (nop .pow a b) resTy)
  | "lean_nat_dec_eq" => n (eq a b)
  | "lean_nat_dec_lt" => n (op isBig .lt a b)
  | "lean_nat_dec_le" => n (op isBig .le a b)
  | "lean_nat_pred" => n (cond (op isBig .gt a z) (op isBig .sub a (intAt t0 1)) z)
  | "lean_nat_land" => n (viaBig .bitAnd)
  | "lean_nat_lor" => n (viaBig .bitOr)
  | "lean_nat_lxor" => n (viaBig .bitXor)
  | "lean_nat_shiftl" =>
    if isBig then n (bop .shl a b) else some (chkInt (nop .mul a (nop .pow (num 2) b)) resTy)
  | "lean_nat_shiftr" =>
    n (if isBig then bop .shr a b else glob "Math" "floor" [nop .div a (nop .pow (num 2) b)])
  | "lean_nat_log2" =>
    let bits := nop .sub (len (meth a "toString" [num 2])) (num 1)
    n (if isBig then cond (eq a (big 0)) (big 0) (call "BigInt" [bits])
       else cond (eq a (num 0)) (num 0) bits)
  | "lean_nat_to_int" => some (convInt a t0 resTy)
  | "lean_nat_abs" => some (convInt (cond (op isBig .lt a z) (neg isBig a) a) t0 resTy)
  -- Int
  | "lean_int_add" => some (chkInt (op isBig .add a b) resTy)
  | "lean_int_sub" => some (chkInt (op isBig .sub a b) resTy)
  | "lean_int_mul" => some (chkInt (op isBig .mul a b) resTy)
  | "lean_int_neg" => n (if isBig then neg true a else nop .sub (num 0) a)
  | "lean_int_neg_succ_of_nat" =>
    let (e, hs) := convInt a t0 resTy
    some (op resTy.isBigInt .sub (neg resTy.isBigInt e) (intAt resTy 1), hs)
  | "lean_int_dec_eq" => n (eq a b)
  | "lean_int_dec_lt" => n (op isBig .lt a b)
  | "lean_int_dec_le" => n (op isBig .le a b)
  | "lean_int_dec_nonneg" => n (op isBig .ge a z)
  | "lean_int_div" =>
    n (if isBig then cond (eq b (big 0)) (big 0) (bop .div a b)
       else cond (eq b (num 0)) (num 0) (glob "Math" "trunc" [nop .div a b]))
  | "lean_int_mod" => n (cond (eq b z) a (op isBig .mod a b))
  | "lean_int_ediv" | "lean_int_div_exact" =>
    -- the truncated quotient, moved one step towards `-∞` (`b > 0`) or `+∞` (`b < 0`) when
    -- the remainder is negative
    let q := if isBig then bop .div a b else glob "Math" "trunc" [nop .div a b]
    let one := intAt t0 1
    n (cond (eq b z) z
      (cond (op isBig .lt (op isBig .mod a b) z)
        (cond (op isBig .gt b z) (op isBig .sub q one) (op isBig .add q one)) q))
  | "lean_int_emod" =>
    let absB := if isBig then cond (bop .lt b (big 0)) (neg true b) b else glob "Math" "abs" [b]
    n (cond (eq b z) a (op isBig .mod (op isBig .add (op isBig .mod a b) absB) absB))
  -- Bool
  | "lean_strict_and" => n (jand a b)
  | "lean_strict_or" => n (jor a b)
  | "lean_bool_to_uint8" | "lean_bool_to_uint16" | "lean_bool_to_uint32" | "lean_bool_to_int8"
  | "lean_bool_to_int16" | "lean_bool_to_int32" => n (cond a (num 1) (num 0))
  | "lean_bool_to_uint64" | "lean_bool_to_int64" => n (cond a (intAt resTy 1) (intAt resTy 0))
  -- Thunks
  | "lean_thunk_pure" => some (.helper "$thunkPure" [a], [thunkPureHelper])
  | "lean_mk_thunk" => some (.helper "$thunk" [a], [thunkHelper])
  | "lean_thunk_get_own" => some (.helper "$force" [a], [forceHelper])
  -- Arrays (generic or typed; never mutated in place)
  | "lean_array_mk" =>
    match typedCtor? resTy with
    | some k => n (glob k "from" [a])
    | none => n a
  | "lean_array_to_list" => n (cond (glob "Array" "isArray" [a]) a (glob "Array" "from" [a]))
  | "lean_array_get_size" => some (convInt (len a) .uint53 resTy)
  | "lean_array_get" | "lean_array_get_borrowed" =>
    let (i, hs) := convIdx c (argTys.getD 2 .uint53)
    some (cond (nop .lt i (len b)) (.at b i) a, hs)
  | "lean_array_push" => some (.helper "$arrayPush" [a, b], [arrayPushHelper])
  | "lean_array_set" | "lean_array_fset" =>
    let (i, hs) := convIdx b (argTys.getD 1 .uint53)
    some (.helper "$arraySet" [a, i, c], arraySetHelper :: hs)
  | "lean_array_swap" | "lean_array_fswap" =>
    let (i, hs) := convIdx b (argTys.getD 1 .uint53)
    let (j, hs') := convIdx c (argTys.getD 2 .uint53)
    some (.helper "$arraySwap" [a, i, j], arraySwapHelper :: hs ++ hs')
  | "lean_array_pop" =>
    n (meth a "slice" [num 0, glob "Math" "max" [nop .sub (len a) (num 1), num 0]])
  | "lean_mk_empty_array_with_capacity" =>
    match typedCtor? resTy with
    | some k => n (.new (v k) [num 0])
    | none => n (.array [])
  | "lean_mk_array" =>
    let (cnt, hs) := convInt a t0 .uint53
    let k := (typedCtor? resTy).getD "Array"
    some (meth (.new (v k) [cnt]) "fill" [b], hs)
  -- Strings (positions are UTF-8 byte offsets)
  | "lean_string_append" => n (concat a b)
  | "lean_string_push" => n (concat a b)
  | "lean_string_dec_eq" => n (eq a b)
  | "lean_string_dec_lt" => n (.bin (.str .lt) a b)
  | "lean_string_compare" =>
    n (cond (.bin (.str .lt) a b) (num (-1)) (cond (eq a b) (num 0) (num 1)))
  | "lean_string_isempty" => n (eq (len a) (num 0))
  | "lean_string_length" => some (convInt (len (.array [.spread a])) .uint53 resTy)
  | "lean_string_utf8_byte_size" =>
    let (e, hs) := convInt (len (.helper "$utf8" [a])) .uint53 resTy
    some (e, utf8Helper :: hs)
  | "lean_string_mk" => n (meth a "join" [str ""])
  | "lean_string_data" => n (.array [.spread a])
  | "lean_string_pushn" =>
    let (cnt, hs) := convInt c (argTys.getD 2 .uint53) .uint53
    some (concat a (meth b "repeat" [cnt]), hs)
  | "lean_string_utf8_at_end" => some (nop .ge b (len (.helper "$utf8" [a])), [utf8Helper])
  | "lean_string_utf8_set" => some (.helper "$utf8Set" [a, b, c], [utf8SetHelper])
  | "lean_string_utf8_extract" => some (.helper "$utf8Extract" [a, b, c], [utf8ExtractHelper])
  -- Floats
  | "lean_float_add" | "lean_float32_add" => flt (nop .add a b)
  | "lean_float_sub" | "lean_float32_sub" => flt (nop .sub a b)
  | "lean_float_mul" | "lean_float32_mul" => flt (nop .mul a b)
  | "lean_float_div" | "lean_float32_div" => flt (nop .div a b)
  | "lean_float_negate" | "lean_float32_negate" => n (.un (.num .neg) a)
  | "lean_float_beq" | "lean_float32_beq" => n (eq a b)
  | "lean_float_decLt" | "lean_float32_decLt" => n (nop .lt a b)
  | "lean_float_decLe" | "lean_float32_decLe" => n (nop .le a b)
  | "lean_float_isnan" | "lean_float32_isnan" => n (glob "Number" "isNaN" [a])
  | "lean_float_isfinite" | "lean_float32_isfinite" => n (glob "Number" "isFinite" [a])
  | "lean_float_isinf" | "lean_float32_isinf" => n (jor (eq a inf) (eq a (.un (.num .neg) inf)))
  | "lean_float_to_float32" => n (fround a)
  | "lean_float32_to_float" => n a
  | _ =>
    -- `UIntN`/`IntN` families
    match parseFixed? sym with
    | some (signed, bits, fop) =>
      if fop.startsWith "to_uint" || (fop.startsWith "to_int" && fop != "to_int" && fop != "to_int_sint") then
        fixedConvImpl signed bits fop resTy
      else if fop == "to_float" then
        n (if t0.isBigInt then call "Number" [a] else a)
      else if bits < 64 then smallFixedImpl signed bits fop argTys resTy
      else if t0.isBigInt || resTy.isBigInt || argTys.any JsTerm.isBigInt then
        bigFixedImpl signed fop argTys resTy
      else none
    | none => none

/-- The body of the helper of an extern, over its parameters `a`, `b`, `c`, …, and the helpers
    it calls; `none` when the extern has no implementation yet. -/
def externImpl? (name : String) (argTys : List JsTerm) (resTy : JsTerm) :
    Option (List JsStmt × List JsHelper) :=
  let sym := externSymbol name
  let r := v "r"
  match sym with
  | "lean_string_utf8_get" =>
    -- `default` (`'A'`) when no character starts at the position
    some ([.const "r" (.helper "$utf8At" [a, b]), .ret (cond (eq r undef) (str "A") (.index r 0))],
      [utf8AtHelper])
  | "lean_string_utf8_next" =>
    some ([.const "r" (.helper "$utf8At" [a, b]),
        .ret (cond (eq r undef) (nop .add b (num 1)) (nop .add b (.index r 1)))],
      [utf8AtHelper])
  | _ =>
  match externExpr? name argTys resTy with
  | some (e, hs) => some ([.ret e], hs)
  | none =>
    -- a 64-bit type represented by a `number`: computed on `BigInt`s (the parameters are
    -- converted first), and the result checked to be a safe integer
    match parseFixed? sym with
    | some (signed, 64, fop) =>
      let big? (t : JsTerm) : JsTerm := match t with
        | .uint53 => .nat | .int53 => .int | t => t
      let bigRes := big? resTy
      match bigFixedImpl signed fop (argTys.map big?) bigRes with
      | some (e, hs) =>
        let conv := (helperParams argTys.length).zip argTys |>.filterMap fun (p, t) =>
          match t with
          | .uint53 | .int53 => some (JsStmt.assign p (call "BigInt" [v p]))
          | _ => none
        if bigRes.isBigInt then some (conv ++ [.ret (.helper "$toNum53" [e])], toNum53 :: hs)
        else some (conv ++ [.ret e], hs)
      | none => none
    | _ => none

/-- The call of an extern: an operator when its meaning is one at this representation,
    otherwise a call of its helper; with the helpers the call needs (each after the helpers
    it calls). -/
def lowerExtern (name : String) (argTys : List JsTerm) (resTy : JsTerm)
    (args : List JsExpr) : JsExpr × List JsHelper :=
  let sym := externSymbol name
  let t0 := argTys.headD .bool
  let bin (o : JsBinOp) : JsExpr := match args with
    | [x, y] => .bin o x y
    | _ => .helper name args
  let isBig := t0.isBigInt
  -- an arithmetic operator on the representation of the first argument
  let arith (nop : JsNumBinOp) (bop : JsBigIntBinOp) : JsExpr :=
    bin (if isBig then .bigint bop else .num nop)
  let inline? : Option JsExpr :=
    -- a `Float.Model` (`Float32.Model`) is laid out as the `Float` (`Float32`) it models
    if floatModelIds.contains name then args.head? else
    match sym with
    | "lean_nat_add" | "lean_int_add" => if isBig then some (bin (.bigint .add)) else none
    | "lean_nat_mul" | "lean_int_mul" => if isBig then some (bin (.bigint .mul)) else none
    | "lean_int_sub" => if isBig then some (bin (.bigint .sub)) else none
    | "lean_nat_dec_eq" | "lean_int_dec_eq" | "lean_string_dec_eq" | "lean_float_beq" =>
      some (bin .strictEq)
    | "lean_nat_dec_lt" | "lean_int_dec_lt" | "lean_float_decLt" => some (arith .lt .lt)
    | "lean_nat_dec_le" | "lean_int_dec_le" | "lean_float_decLe" => some (arith .le .le)
    | "lean_strict_and" => some (bin (.bool .and))
    | "lean_strict_or" => some (bin (.bool .or))
    -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one
    -- code point), how `a = b` on `Char` is translated
    | "lean_string_push" => match args with
      | [.lit (.str ""), ch] => some ch
      | _ => some (bin (.str .concat))
    | "lean_string_append" => some (bin (.str .concat))
    -- a list and a generic array are both JavaScript arrays
    | "lean_array_mk" => match typedCtor? resTy, args with
      | none, [a] => some a
      | _, _ => none
    | "lean_array_to_list" => match t0, args with
      | .genericArray _, [a] => some a
      | _, _ => none
    | "lean_float_add" => some (bin (.num .add))
    | "lean_float_sub" => some (bin (.num .sub))
    | "lean_float_mul" => some (bin (.num .mul))
    | "lean_float_div" => some (bin (.num .div))
    | _ =>
      match parseFixed? sym with
      | some (_, _, "dec_eq") => some (bin .strictEq)
      | some (_, _, "dec_lt") => some (arith .lt .lt)
      | some (_, _, "dec_le") => some (arith .le .le)
      | _ => none
  match inline? with
  | some e => (e, [])
  | none =>
    let hname := name ++ sigSuffix (argTys ++ [resTy])
    match externImpl? name argTys resTy with
    | some (body, deps) =>
      (.helper hname args, deps ++ [{ name := hname, params := helperParams argTys.length, body }])
    | none => (.helper hname args, [stubHelper hname])

end MoreJs

end
