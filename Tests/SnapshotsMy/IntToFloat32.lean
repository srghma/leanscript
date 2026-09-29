set_option trace.Compiler.saveMono true   -- mono LCNF phase
set_option trace.Compiler.result true     -- final LCNF result
-- Integer → `Float32` conversions round to single precision: `16777217 = 2^24 + 1` is not a
-- `Float32`, so it becomes `16777216`.  An integer `number` must go through `Math.fround`
-- (`Number(x)` of a number is `x` itself, unrounded).

def u32ToF32 (n : Nat) : Float := (n.toUInt32 + 16777216).toFloat32.toFloat

def i32ToF32 (i : Int) : Float := (Int32.ofInt i + 16777216).toFloat32.toFloat

def u64ToF32 (n : Nat) : Float := (n.toUInt64 + 16777216).toFloat32.toFloat

def i64ToF32 (i : Int) : Float := (Int64.ofInt i + 16777216).toFloat32.toFloat

-- Beyond `2^53` (the `BigInt` representation) the conversions are the runtime's
-- `bigint_nat__lean_uint64_to_float32` / `bigint_int__lean_int64_to_float32`, checked in
-- `Tests/Main.lean` (a literal that large cannot be written in the `pbo` preset).
