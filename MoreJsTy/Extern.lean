module

public import MoreJsTy.Syntax
public import LeanScript.Term.ExternName

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

The helpers are faithful to Lean's semantics at the chosen representation: `Nat.sub`
truncates at `0`, division by `0` answers `0`, fixed-width arithmetic wraps, `Int.ediv` is
Euclidean.  With a `number` representation of an unbounded type, a result that is not a safe
integer throws a `RangeError` (`$chk53`) instead of losing precision.

An extern that has no JavaScript implementation yet becomes a helper that throws when it is
called (`stubHelper`), so the rest of the module still loads and runs.
-/

namespace MoreJs

open LeanScript

/-- The code of a layout in the name of a helper: `b` for a `BigInt`, `n` for a `number`
    standing for an unbounded or 64-bit integer, `_` otherwise. -/
def sigCode (t : MoreJsTy) : Char :=
  if t.isBigInt then 'b'
  else match t with
    | .uint53 | .int53 => 'n'
    | _ => '_'

/-- The suffix of a helper's name: the codes of its arguments and result, when one of them is
    configurable. -/
def sigSuffix (tys : List MoreJsTy) : String :=
  let cs := tys.map sigCode
  if cs.any (· != '_') then "$" ++ String.ofList cs else ""

/-- The parameters of a helper of `n` arguments: `a`, `b`, `c`, …. -/
def helperParams (n : Nat) : List String :=
  (List.range n).map fun i =>
    if i < 26 then String.singleton (Char.ofNat ('a'.toNat + i)) else s!"p{i}"

/-! ## The base helpers -/

/-- A result that must be a safe integer (a `number` standing for an unbounded integer). -/
def chk53 : JsHelper :=
  ⟨"$chk53", "function $chk53(x) {\n  if (!Number.isSafeInteger(x)) throw new RangeError(\"LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)\");\n  return x;\n}"⟩

/-- A `BigInt` that must fit in a safe integer `number`. -/
def toNum53 : JsHelper :=
  ⟨"$toNum53", "function $toNum53(x) {\n  if (x > 9007199254740991n || x < -9007199254740991n) throw new RangeError(\"LeanScript: integer overflow: the result does not fit in a number (use the bigint representation)\");\n  return Number(x);\n}"⟩

/-- A memoised delay. -/
def thunkHelper : JsHelper :=
  ⟨"$thunk", "function $thunk(f) {\n  return { f, v: undefined, done: false };\n}"⟩

/-- A memoised delay that is already computed. -/
def thunkPureHelper : JsHelper :=
  ⟨"$thunkPure", "function $thunkPure(v) {\n  return { f: undefined, v, done: true };\n}"⟩

/-- The value of a memoised delay. -/
def forceHelper : JsHelper :=
  ⟨"$force", "function $force(t) {\n  if (!t.done) {\n    t.v = t.f();\n    t.done = true;\n    t.f = undefined;\n  }\n  return t.v;\n}"⟩

/-- The UTF-8 bytes of a string (positions of Lean strings are UTF-8 byte offsets). -/
def utf8Helper : JsHelper :=
  ⟨"$utf8", "const $utf8Enc = new TextEncoder();\nfunction $utf8(s) {\n  return $utf8Enc.encode(s);\n}"⟩

/-- The code point starting at UTF-8 byte offset `p` of `s`, and its length in bytes, or
    `undefined` when `p` is not the start of a character. -/
def utf8AtHelper : JsHelper :=
  ⟨"$utf8At", "function $utf8At(s, p) {\n  let off = 0;\n  for (const ch of s) {\n    const cp = ch.codePointAt(0);\n    const n = cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;\n    if (off === p) return [ch, n];\n    if (off > p) return undefined;\n    off += n;\n  }\n  return undefined;\n}"⟩

/-- `String.Pos.Raw.set`: replace the character that starts at the UTF-8 offset `p`
    (`Pos.Raw.utf8SetAux`); the string is unchanged when no character starts there. -/
def utf8SetHelper : JsHelper :=
  ⟨"$utf8Set", "function $utf8Set(s, p, c) {\n  let off = 0, i = 0;\n  for (const ch of s) {\n    if (off === p) return s.slice(0, i) + c + s.slice(i + ch.length);\n    const cp = ch.codePointAt(0);\n    off += cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;\n    i += ch.length;\n  }\n  return s;\n}"⟩

/-- `String.Pos.Raw.extract`: the characters from the one starting at the UTF-8 offset `b`
    up to (not including) the one starting at `e` (`Pos.Raw.extract.go₁`/`go₂`). -/
def utf8ExtractHelper : JsHelper :=
  ⟨"$utf8Extract", "function $utf8Extract(s, b, e) {\n  if (b >= e) return \"\";\n  let off = 0, out = \"\", started = false;\n  for (const ch of s) {\n    if (!started && off === b) started = true;\n    if (started) {\n      if (off === e) return out;\n      out += ch;\n    }\n    const cp = ch.codePointAt(0);\n    off += cp < 0x80 ? 1 : cp < 0x800 ? 2 : cp < 0x10000 ? 3 : 4;\n  }\n  return out;\n}"⟩

/-- A copy of an array (generic or typed) with one more element. -/
def arrayPushHelper : JsHelper :=
  ⟨"$arrayPush", "function $arrayPush(a, x) {\n  if (Array.isArray(a)) return [...a, x];\n  const r = new a.constructor(a.length + 1);\n  r.set(a);\n  r[a.length] = x;\n  return r;\n}"⟩

/-- A copy of an array (generic or typed) with one element replaced. -/
def arraySetHelper : JsHelper :=
  ⟨"$arraySet", "function $arraySet(a, i, x) {\n  if (i >= a.length) return a;\n  const r = a.slice();\n  r[i] = x;\n  return r;\n}"⟩

/-- A copy of an array (generic or typed) with two elements swapped. -/
def arraySwapHelper : JsHelper :=
  ⟨"$arraySwap", "function $arraySwap(a, i, j) {\n  if (i >= a.length || j >= a.length) return a;\n  const r = a.slice();\n  const t = r[i];\n  r[i] = r[j];\n  r[j] = t;\n  return r;\n}"⟩

/-- A helper that throws: the extern has no JavaScript implementation yet. -/
def stubHelper (name : String) : JsHelper :=
  ⟨name, s!"function {name}(...args) \{\n  throw new Error(\"LeanScript: the extern {name} has no JavaScript implementation yet\");\n}"⟩

/-! ## Numeric conversions -/

/-- The source of the integer literal `n` at layout `t`. -/
def numLit (t : MoreJsTy) (n : Int) : String :=
  if t.isBigInt then s!"{n}n" else toString n

/-- Convert the integer `e` from the layout `src` to the layout `dst` (both integers). -/
def convInt (e : String) (src dst : MoreJsTy) : String × List JsHelper :=
  if src.isBigInt == dst.isBigInt then (e, [])
  else if src.isBigInt then (s!"$toNum53({e})", [toNum53])
  else (s!"BigInt({e})", [])

/-- An array index as a `number`: a `BigInt` index too large for a number becomes
    `Infinity`, which is out of bounds of every array (so the bounds checks answer as Lean
    does instead of throwing). -/
def idxHelper : JsHelper :=
  ⟨"$idx", "function $idx(x) {\n  return x > 9007199254740991n ? Infinity : Number(x);\n}"⟩

/-- Convert the index `e` from the integer layout `src` to a `number`. -/
def convIdx (e : String) (src : MoreJsTy) : String × List JsHelper :=
  if src.isBigInt then (s!"$idx({e})", [idxHelper]) else (e, [])

/-- Check that an integer result at layout `t` is exact (a safe integer when it is a
    `number` standing for an unbounded integer). -/
def chkInt (e : String) (t : MoreJsTy) : String × List JsHelper :=
  match t with
  | .uint53 | .int53 => (s!"$chk53({e})", [chk53])
  | _ => (e, [])

/-- A JavaScript typed array constructor for a layout, if it is a typed array. -/
def typedCtor? : MoreJsTy → Option String
  | .uint8Array => some "Uint8Array" | .uint16Array => some "Uint16Array"
  | .uint32Array => some "Uint32Array" | .int8Array => some "Int8Array"
  | .int16Array => some "Int16Array" | .int32Array => some "Int32Array"
  | .float32Array => some "Float32Array" | .float64Array => some "Float64Array"
  | .bigUint64Array => some "BigUint64Array" | .bigInt64Array => some "BigInt64Array"
  | _ => none

/-! ## Fixed-width integers -/

/-- Wrap a JavaScript integer (a `number` computed from 32-bit or smaller operands) to an
    unsigned `bits`-bit value. -/
def wrapU (bits : Nat) (e : String) : String :=
  if bits == 32 then s!"(({e}) >>> 0)" else s!"(({e}) & {2 ^ bits - 1})"

/-- Wrap a JavaScript integer to a signed `bits`-bit value. -/
def wrapS (bits : Nat) (e : String) : String :=
  if bits == 32 then s!"(({e}) | 0)" else s!"((({e}) << {32 - bits}) >> {32 - bits})"

/-- The implementation of an operation `op` of `UIntN`/`IntN` for `N ≤ 32` (a `number`),
    as the source of the returned expression over the parameters `a`, `b`. -/
def smallFixedImpl (signed : Bool) (bits : Nat) (op : String) (argTys : List MoreJsTy)
    (resTy : MoreJsTy) : Option (String × List JsHelper) :=
  let w := if signed then wrapS bits else wrapU bits
  let arg0 := argTys.headD .bool
  match op with
  | "add" => some (w "a + b", [])
  | "sub" => some (w "a - b", [])
  | "mul" => some (if bits == 32 then w "Math.imul(a, b)" else w "a * b", [])
  | "neg" => some (w "-a", [])
  | "div" => some (if signed then s!"(b === 0 ? 0 : {w "Math.trunc(a / b)"})"
                   else "(b === 0 ? 0 : Math.floor(a / b))", [])
  | "mod" => some ("(b === 0 ? a : a % b)", [])
  | "land" => some (w "a & b", [])
  | "lor" => some (w "a | b", [])
  | "xor" => some (w "a ^ b", [])
  | "complement" => some (w "~a", [])
  | "shift_left" => some (w s!"a << (((b % {bits}) + {bits}) % {bits})", [])
  | "shift_right" =>
    some (if signed then s!"(a >> (((b % {bits}) + {bits}) % {bits}))"
          else s!"(a >>> (b % {bits}))", [])
  | "abs" => some (w "Math.abs(a)", [])
  | "dec_eq" => some ("a === b", [])
  | "dec_lt" => some ("a < b", [])
  | "dec_le" => some ("a <= b", [])
  | "log2" => some ("(a === 0 ? 0 : 31 - Math.clz32(a))", [])
  | "to_nat" | "to_int" =>
    let (e, hs) := convInt "a" .uint53 resTy
    some (e, hs)
  | "of_nat" | "of_int" =>
    if arg0.isBigInt then
      some (s!"Number(BigInt.as{if signed then "Int" else "Uint"}N({bits}, a))", [])
    else if signed then some (w "a", [])
    else some (s!"(((a % {2 ^ bits}) + {2 ^ bits}) % {2 ^ bits})", [])
  | "of_nat_mk" | "to_bitvec" => some ("a", [])
  | "to_float" | "to_float32" => some ("a", [])
  | _ => none

/-- The implementation of an operation of `UInt64`/`Int64` on `BigInt`s. -/
def bigFixedImpl (signed : Bool) (op : String) (argTys : List MoreJsTy) (resTy : MoreJsTy) :
    Option (String × List JsHelper) :=
  let w (e : String) := s!"BigInt.as{if signed then "Int" else "Uint"}N(64, {e})"
  let arg0 := argTys.headD .bool
  match op with
  | "add" => some (w "a + b", [])
  | "sub" => some (w "a - b", [])
  | "mul" => some (w "a * b", [])
  | "neg" => some (w "-a", [])
  | "div" => some (s!"(b === 0n ? 0n : {w "a / b"})", [])
  | "mod" => some ("(b === 0n ? a : a % b)", [])
  | "land" => some (w "a & b", [])
  | "lor" => some (w "a | b", [])
  | "xor" => some (w "a ^ b", [])
  | "complement" => some (w "~a", [])
  | "shift_left" => some (w "a << (((b % 64n) + 64n) % 64n)", [])
  | "shift_right" => some ("(a >> (((b % 64n) + 64n) % 64n))", [])
  | "abs" => some (w "(a < 0n ? -a : a)", [])
  | "dec_eq" => some ("a === b", [])
  | "dec_lt" => some ("a < b", [])
  | "dec_le" => some ("a <= b", [])
  | "log2" => some ("(a === 0n ? 0n : BigInt(a.toString(2).length - 1))", [])
  | "to_nat" | "to_int" | "to_int_sint" => some (convInt "a" .nat resTy)
  | "of_nat" | "of_int" => some (w (convInt "a" arg0 .nat).1, (convInt "a" arg0 .nat).2)
  | "of_nat_mk" | "to_bitvec" => some ("a", [])
  | "to_float" | "to_float32" => some ("Number(a)", [])
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
def fixedConvImpl (signed : Bool) (fromBits : Nat) (op : String) (resTy : MoreJsTy) :
    Option (String × List JsHelper) := do
  let pre := if signed then "to_int" else "to_uint"
  let toBits ← (op.dropPrefix? pre).bind (·.toString.toNat?)
  unless [8, 16, 32, 64].contains toBits do none
  if fromBits == 64 then
    if toBits == 64 then return ("a", []) else
    if resTy.isBigInt then return ("a", []) else
    -- from a `BigInt` (or a `number` standing for one) to a small width
    let e := s!"Number(BigInt.as{if signed then "Int" else "Uint"}N({toBits}, BigInt(a)))"
    return (e, [])
  else if toBits == 64 then
    return (if resTy.isBigInt then "BigInt(a)" else "a", [])
  else if toBits ≥ fromBits then return ("a", [])
  else return ((if signed then wrapS toBits else wrapU toBits) "a", [])

/-! ## The implementations -/

/-- The source of the expression a helper returns, over its parameters `a`, `b`, `c`, …, and
    the helpers it calls; `none` when the extern has no implementation yet. -/
def externImpl? (name : String) (argTys : List MoreJsTy) (resTy : MoreJsTy) :
    Option (String × List JsHelper) :=
  let sym := externSymbol name
  let t0 := argTys.headD .bool
  let big := t0.isBigInt
  let z := numLit t0 0
  match name with
  | "lean_uint32_of_nat__Char_ofNatAux" =>
    some (s!"String.fromCodePoint(Number({if big then "a" else "a"}))", [])
  | _ =>
  match sym with
  -- Nat
  | "lean_nat_add" => some (chkInt "a + b" resTy)
  | "lean_nat_sub" => some (s!"(a > b ? a - b : {z})", [])
  | "lean_nat_mul" => some (chkInt "a * b" resTy)
  | "lean_nat_div" | "lean_nat_div_exact" =>
    some (if big then "(b === 0n ? 0n : a / b)" else "(b === 0 ? 0 : Math.floor(a / b))", [])
  | "lean_nat_mod" => some (s!"(b === {z} ? a : a % b)", [])
  | "lean_nat_pow" => some (chkInt "a ** b" resTy)
  | "lean_nat_dec_eq" => some ("a === b", [])
  | "lean_nat_dec_lt" => some ("a < b", [])
  | "lean_nat_dec_le" => some ("a <= b", [])
  | "lean_nat_pred" => some (s!"(a > {z} ? a - {numLit t0 1} : {z})", [])
  | "lean_nat_land" => some (if big then "a & b" else "Number(BigInt(a) & BigInt(b))", [])
  | "lean_nat_lor" => some (if big then "a | b" else "Number(BigInt(a) | BigInt(b))", [])
  | "lean_nat_lxor" => some (if big then "a ^ b" else "Number(BigInt(a) ^ BigInt(b))", [])
  | "lean_nat_shiftl" => some (if big then ("a << b", []) else chkInt "a * 2 ** b" resTy)
  | "lean_nat_shiftr" => some (if big then "a >> b" else "Math.floor(a / 2 ** b)", [])
  | "lean_nat_log2" =>
    some (if big then "(a === 0n ? 0n : BigInt(a.toString(2).length - 1))"
          else "(a === 0 ? 0 : a.toString(2).length - 1)", [])
  | "lean_nat_to_int" => some (convInt "a" t0 resTy)
  | "lean_nat_abs" =>
    let (e, hs) := convInt s!"(a < {z} ? -a : a)" t0 resTy
    some (e, hs)
  -- Int
  | "lean_int_add" => some (chkInt "a + b" resTy)
  | "lean_int_sub" => some (chkInt "a - b" resTy)
  | "lean_int_mul" => some (chkInt "a * b" resTy)
  | "lean_int_neg" => some (if big then "-a" else "0 - a", [])
  | "lean_int_neg_succ_of_nat" =>
    let (e, hs) := convInt "a" t0 resTy
    some (s!"-{e} - {numLit resTy 1}", hs)
  | "lean_int_dec_eq" => some ("a === b", [])
  | "lean_int_dec_lt" => some ("a < b", [])
  | "lean_int_dec_le" => some ("a <= b", [])
  | "lean_int_dec_nonneg" => some (s!"a >= {z}", [])
  | "lean_int_div" =>
    some (if big then "(b === 0n ? 0n : a / b)" else "(b === 0 ? 0 : Math.trunc(a / b))", [])
  | "lean_int_mod" => some (s!"(b === {z} ? a : a % b)", [])
  | "lean_int_ediv" | "lean_int_div_exact" =>
    if big then
      some ("(b === 0n ? 0n : (a % b < 0n ? (b > 0n ? a / b - 1n : a / b + 1n) : a / b))", [])
    else
      some ("(b === 0 ? 0 : (a % b < 0 ? (b > 0 ? Math.trunc(a / b) - 1 : Math.trunc(a / b) + 1) : Math.trunc(a / b)))", [])
  | "lean_int_emod" =>
    if big then some ("(b === 0n ? a : ((a % b) + (b < 0n ? -b : b)) % (b < 0n ? -b : b))", [])
    else some ("(b === 0 ? a : ((a % b) + Math.abs(b)) % Math.abs(b))", [])
  -- Bool
  | "lean_strict_and" => some ("a && b", [])
  | "lean_strict_or" => some ("a || b", [])
  | "lean_bool_to_uint8" | "lean_bool_to_uint16" | "lean_bool_to_uint32" | "lean_bool_to_int8"
  | "lean_bool_to_int16" | "lean_bool_to_int32" => some ("(a ? 1 : 0)", [])
  | "lean_bool_to_uint64" | "lean_bool_to_int64" =>
    some (if resTy.isBigInt then "(a ? 1n : 0n)" else "(a ? 1 : 0)", [])
  -- Thunks
  | "lean_thunk_pure" => some ("$thunkPure(a)", [thunkPureHelper])
  | "lean_mk_thunk" => some ("$thunk(a)", [thunkHelper])
  | "lean_thunk_get_own" => some ("$force(a)", [forceHelper])
  -- Arrays (generic or typed; never mutated in place)
  | "lean_array_mk" =>
    match typedCtor? resTy with
    | some c => some (s!"{c}.from(a)", [])
    | none => some ("a", [])
  | "lean_array_to_list" => some ("(Array.isArray(a) ? a : Array.from(a))", [])
  | "lean_array_get_size" => some (convInt "a.length" .uint53 resTy)
  | "lean_array_get" | "lean_array_get_borrowed" =>
    let (i, hs) := convIdx "c" (argTys.getD 2 .uint53)
    some (s!"({i} < b.length ? b[{i}] : a)", hs)
  | "lean_array_push" => some ("$arrayPush(a, b)", [arrayPushHelper])
  | "lean_array_set" | "lean_array_fset" =>
    let (i, hs) := convIdx "b" (argTys.getD 1 .uint53)
    some (s!"$arraySet(a, {i}, c)", arraySetHelper :: hs)
  | "lean_array_swap" | "lean_array_fswap" =>
    let (i, hs) := convIdx "b" (argTys.getD 1 .uint53)
    let (j, hs') := convIdx "c" (argTys.getD 2 .uint53)
    some (s!"$arraySwap(a, {i}, {j})", arraySwapHelper :: hs ++ hs')
  | "lean_array_pop" => some ("a.slice(0, Math.max(a.length - 1, 0))", [])
  | "lean_mk_empty_array_with_capacity" =>
    match typedCtor? resTy with
    | some c => some (s!"new {c}(0)", [])
    | none => some ("[]", [])
  | "lean_mk_array" =>
    let (n, hs) := convInt "a" t0 .uint53
    match typedCtor? resTy with
    | some c => some (s!"new {c}({n}).fill(b)", hs)
    | none => some (s!"new Array({n}).fill(b)", hs)
  -- Strings (positions are UTF-8 byte offsets)
  | "lean_string_append" => some ("a + b", [])
  | "lean_string_push" => some ("a + b", [])
  | "lean_string_dec_eq" => some ("a === b", [])
  | "lean_string_dec_lt" => some ("a < b", [])
  | "lean_string_compare" => some ("(a < b ? -1 : a === b ? 0 : 1)", [])
  | "lean_string_isempty" => some ("a.length === 0", [])
  | "lean_string_length" => some (convInt "[...a].length" .uint53 resTy)
  | "lean_string_utf8_byte_size" =>
    let (e, hs) := convInt "$utf8(a).length" .uint53 resTy
    some (e, utf8Helper :: hs)
  | "lean_string_mk" => some ("a.join(\"\")", [])
  | "lean_string_data" => some ("[...a]", [])
  | "lean_string_pushn" =>
    let (n, hs) := convInt "c" (argTys.getD 2 .uint53) .uint53
    some (s!"a + b.repeat({n})", hs)
  | "lean_string_utf8_get" => some ("($utf8At(a, b) ?? [\"A\"])[0]", [utf8AtHelper])
  | "lean_string_utf8_next" =>
    some ("(($r) => $r === undefined ? b + 1 : b + $r[1])($utf8At(a, b))", [utf8AtHelper])
  | "lean_string_utf8_at_end" => some ("b >= $utf8(a).length", [utf8Helper])
  | "lean_string_utf8_set" => some ("$utf8Set(a, b, c)", [utf8SetHelper])
  | "lean_string_utf8_extract" => some ("$utf8Extract(a, b, c)", [utf8ExtractHelper])
  -- Floats
  | "lean_float_add" | "lean_float32_add" =>
    some (if sym == "lean_float32_add" then "Math.fround(a + b)" else "a + b", [])
  | "lean_float_sub" | "lean_float32_sub" =>
    some (if sym == "lean_float32_sub" then "Math.fround(a - b)" else "a - b", [])
  | "lean_float_mul" | "lean_float32_mul" =>
    some (if sym == "lean_float32_mul" then "Math.fround(a * b)" else "a * b", [])
  | "lean_float_div" | "lean_float32_div" =>
    some (if sym == "lean_float32_div" then "Math.fround(a / b)" else "a / b", [])
  | "lean_float_negate" | "lean_float32_negate" => some ("-a", [])
  | "lean_float_beq" | "lean_float32_beq" => some ("a === b", [])
  | "lean_float_decLt" | "lean_float32_decLt" => some ("a < b", [])
  | "lean_float_decLe" | "lean_float32_decLe" => some ("a <= b", [])
  | "lean_float_isnan" | "lean_float32_isnan" => some ("Number.isNaN(a)", [])
  | "lean_float_isfinite" | "lean_float32_isfinite" => some ("Number.isFinite(a)", [])
  | "lean_float_isinf" | "lean_float32_isinf" =>
    some ("(a === Infinity || a === -Infinity)", [])
  | "lean_float_to_float32" => some ("Math.fround(a)", [])
  | "lean_float32_to_float" => some ("a", [])
  | _ =>
    -- `UIntN`/`IntN` families
    match parseFixed? sym with
    | some (signed, bits, op) =>
      if op.startsWith "to_uint" || (op.startsWith "to_int" && op != "to_int" && op != "to_int_sint") then
        fixedConvImpl signed bits op resTy
      else if op == "to_float" then
        some (if t0.isBigInt then "Number(a)" else "a", [])
      else if bits < 64 then smallFixedImpl signed bits op argTys resTy
      else if t0.isBigInt || resTy.isBigInt || argTys.any MoreJsTy.isBigInt then
        bigFixedImpl signed op argTys resTy
      else
        -- a 64-bit type represented by a `number`: computed on `BigInt`s, and the result
        -- checked to be a safe integer
        let bigArgs := argTys.map fun t => match t with
          | .uint53 => MoreJsTy.nat | .int53 => MoreJsTy.int | t => t
        let bigRes := match resTy with
          | .uint53 => MoreJsTy.nat | .int53 => MoreJsTy.int | t => t
        match bigFixedImpl signed op bigArgs bigRes with
        | some (e, hs) =>
          let ps := helperParams argTys.length
          let callArgs := ps.zip argTys |>.map fun (p, t) => match t with
            | .uint53 | .int53 => s!"BigInt({p})"
            | _ => p
          let body := s!"(({", ".intercalate ps}) => {e})({", ".intercalate callArgs})"
          if bigRes.isBigInt then some (s!"$toNum53({body})", toNum53 :: hs)
          else some (body, hs)
        | none => none
    | none => none

/-- The call of an extern: an operator when its meaning is one at this representation,
    otherwise a call of its helper; with the helpers the call needs (each after the helpers
    it calls). -/
def lowerExtern (name : String) (argTys : List MoreJsTy) (resTy : MoreJsTy)
    (args : List JsExpr) : JsExpr × List JsHelper :=
  let sym := externSymbol name
  let t0 := argTys.headD .bool
  let bin (op : JsBinOp) : JsExpr := match args with
    | [a, b] => .bin op a b
    | _ => .helper name args
  let inline? : Option JsExpr :=
    match sym with
    | "lean_nat_add" | "lean_int_add" => if t0.isBigInt then some (bin .add) else none
    | "lean_nat_mul" | "lean_int_mul" => if t0.isBigInt then some (bin .mul) else none
    | "lean_int_sub" => if t0.isBigInt then some (bin .sub) else none
    | "lean_nat_dec_eq" | "lean_int_dec_eq" | "lean_string_dec_eq" | "lean_float_beq" =>
      some (bin .strictEq)
    | "lean_nat_dec_lt" | "lean_int_dec_lt" | "lean_float_decLt" => some (bin .lt)
    | "lean_nat_dec_le" | "lean_int_dec_le" | "lean_float_decLe" => some (bin .le)
    | "lean_strict_and" => some (bin .and)
    | "lean_strict_or" => some (bin .or)
    -- `"".push c` is the one-character string `c` itself (a `Char` is a string of one
    -- code point), how `a = b` on `Char` is translated
    | "lean_string_push" => match args with
      | [.lit (.str ""), c] => some c
      | _ => some (bin .add)
    | "lean_string_append" => some (bin .add)
    | "lean_float_add" => some (bin .add)
    | "lean_float_sub" => some (bin .sub)
    | "lean_float_mul" => some (bin .mul)
    | "lean_float_div" => some (bin .div)
    | _ =>
      match parseFixed? sym with
      | some (_, _, "dec_eq") => some (bin .strictEq)
      | some (_, _, "dec_lt") => some (bin .lt)
      | some (_, _, "dec_le") => some (bin .le)
      | _ => none
  match inline? with
  | some e => (e, [])
  | none =>
    let hname := name ++ sigSuffix (argTys ++ [resTy])
    match externImpl? name argTys resTy with
    | some (body, deps) =>
      let ps := helperParams argTys.length
      let src := s!"function {hname}({", ".intercalate ps}) \{\n  return {body};\n}"
      (.helper hname args, deps ++ [⟨hname, src⟩])
    | none => (.helper hname args, [stubHelper hname])

end MoreJs

end
