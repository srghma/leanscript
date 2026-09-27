-- import Lean

-- open Lean Elab Command

-- /-- Executes both `bigint.js` and `num.js` via Bun and displays both outputs. -/
-- def assertBothJsModes
--     (jsFnName : String)
--     (leanVal : String)
--     (args : List String)
--     (projectRoot : String := "/home/srghma/projects/lean-js-backend")
--     (bigintRelPath : String := "./SnapshotsPBOPure/PrimOpIntBit01Configurable-bigint.js")
--     (numRelPath : String := "./SnapshotsPBOPure/PrimOpIntBit01Configurable-num.js") : IO Unit := do
--   let argsJson := "[" ++ String.intercalate ", " (args.map (fun a => "\"" ++ a ++ "\"")) ++ "]"
--   let script :=
--     "import path from 'node:path';\n" ++
--     "const root = '" ++ projectRoot ++ "';\n" ++
--     "const modBI = await import(path.resolve(root, '" ++ bigintRelPath ++ "'));\n" ++
--     "const modNum = await import(path.resolve(root, '" ++ numRelPath ++ "'));\n" ++
--     "const fnName = '" ++ jsFnName ++ "';\n" ++
--     "const leanExpected = '" ++ leanVal ++ "';\n" ++
--     "const rawArgs = " ++ argsJson ++ ";\n" ++
--     "\n" ++
--     "// 1. Always evaluate BigInt mode\n" ++
--     "const fnBI = modBI[fnName];\n" ++
--     "if (typeof fnBI !== 'function') {\n" ++
--     "  console.error('Export ' + fnName + ' not found in bigint file');\n" ++
--     "  process.exit(1);\n" ++
--     "}\n" ++
--     "let resBI = fnBI;\n" ++
--     "for (const a of rawArgs) {\n" ++
--     "  if (typeof resBI !== 'function') break;\n" ++
--     "  resBI = resBI(BigInt(a));\n" ++
--     "}\n" ++
--     "const biStr = resBI.toString();\n" ++
--     "\n" ++
--     "// 2. Always evaluate Num mode (no skipping!)\n" ++
--     "const fnNum = modNum[fnName];\n" ++
--     "let numStatus = 'N/A';\n" ++
--     "if (typeof fnNum === 'function') {\n" ++
--     "  try {\n" ++
--     "    let resNum = fnNum;\n" ++
--     "    for (const a of rawArgs) {\n" ++
--     "      if (typeof resNum !== 'function') break;\n" ++
--     "      resNum = resNum(Number(a));\n" ++
--     "    }\n" ++
--     "    const numStr = resNum.toString();\n" ++
--     "    if (numStr === leanExpected) {\n" ++
--     "      numStatus = 'PASS';\n" ++
--     "    } else {\n" ++
--     "      numStatus = 'MISMATCH (got ' + numStr + ')';\n" ++
--     "    }\n" ++
--     "  } catch (e) {\n" ++
--     "    numStatus = 'ERROR (' + e.message + ')';\n" ++
--     "  }\n" ++
--     "}\n" ++
--     "console.log(biStr + '\\n' + numStatus);\n"

--   let out ← IO.Process.output {
--     cmd := "bun",
--     args := #["-e", script],
--     cwd := some projectRoot
--   }

--   if out.exitCode != 0 then
--     throw <| IO.userError s!"[JS Error for {jsFnName}]:\n{out.stderr.trimAscii.toString}"

--   let stdoutStr : String := out.stdout.trimAscii.toString
--   let lines : List String := stdoutStr.splitOn "\n"
--   let biVal : String := lines.getD 0 ""
--   let numStatus : String := lines.getD 1 ""
--   let argsStr := String.intercalate ", " args

--   -- BigInt mode is required to be exact
--   if biVal != leanVal then
--     throw <| IO.userError
--       s!"BigInt assertion failed for {jsFnName}({argsStr})!\n  Lean:   {leanVal}\n  BigInt: {biVal}"

--   let tag := if numStatus == "PASS" then "✓ PASS" else "⚠ DIFF"
--   IO.println s!"{tag} | {jsFnName}({argsStr}) | Lean: {leanVal} | bigint: PASS | num: {numStatus}"

-- /-- Syntax: `#def name : Type := expr` -/
-- syntax (name := testDefCmd) "#def " ident " : " term " := " term : command

-- elab_rules : command
--   | `(#def $id:ident : $ty:term := $rhs:term) => do
--     elabCommand (← `(def $id : $ty := $rhs))
--     let currNs ← getCurrNamespace
--     match rhs with
--     | `($a:term &&& $b:term) =>
--       let jsName := (currNs ++ `land).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term ||| $b:term) =>
--       let jsName := (currNs ++ `lor).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term <<< $b:term) =>
--       let jsName := (currNs ++ `shiftLeft).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term >>> $b:term) =>
--       let jsName := (currNs ++ `shiftRight).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term ^^^ $b:term) =>
--       let jsName := (currNs ++ `xor).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `(~~~$a:term) =>
--       let jsName := (currNs ++ `complement).toString.replace "." "$"
--       elabCommand (← `(#eval! assertBothJsModes $(quote jsName) (toString $id) [toString (($a : $ty))]))
--     | _ =>
--       throwErrorAt rhs s!"#def expects a bitwise expression (&&&, |||, <<<, >>>, ^^^, ~~~), but got: {rhs}"

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

namespace TestUInt64

def land : UInt64 := 1023 &&& 8
def lor  : UInt64 := 16 ||| 15
def shiftLeft : UInt64 := (1023 : UInt64) <<< 2
def shiftRight : UInt64 := (-1023 : UInt64) >>> 2
def xor : UInt64 := 15 ^^^ 12
def complement : UInt64 := ~~~(-3)

end TestUInt64

namespace TestUSize

def land : USize := 1023 &&& 8
def lor  : USize := 16 ||| 15
def shiftLeft : USize := (1023 : USize) <<< 2
def shiftRight : USize := (-1023 : USize) >>> 2
def xor : USize := 15 ^^^ 12
def complement : USize := ~~~(-3)

end TestUSize

namespace TestNat

def land : Nat := 1023 &&& 8
def lor  : Nat := 16 ||| 15
def shiftLeft : Nat := 1023 <<< 2
def shiftRight : Nat := (1023 : Nat) >>> 2
def xor : Nat := 15 ^^^ 12

-- -- (2^60 + 1) has bit 0 set.
-- -- In Lean: (2^60 + 1) &&& 1 = 1
-- #def largeLand : Nat := (2^60 + 1) &&& 1

-- -- 2^60 has bit 0 as 0. Adding 1 loses the 1 in JS double!
-- -- In Lean: (2^60 + 1) - 2^60 = 1
-- #def largeShift : Nat := (1 <<< 60) + 1


end TestNat

-------------------------------------------

namespace TestInt64

def land : Int64 := 1023 &&& 8
def lor  : Int64 := 16 ||| 15
def shiftLeft : Int64 := (1023 : Int64) <<< 2
def shiftRight : Int64 := (-1023 : Int64) >>> 2
def xor : Int64 := 15 ^^^ 12
def complement : Int64 := ~~~(-3)

end TestInt64

namespace TestISize

def land : ISize := 1023 &&& 8
def lor  : ISize := 16 ||| 15
def shiftLeft : ISize := (1023 : ISize) <<< 2
def shiftRight : ISize := (-1023 : ISize) >>> 2
def xor : ISize := 15 ^^^ 12
def complement : ISize := ~~~(-3)

end TestISize

namespace TestInt

def complement : Int := ~~~(-3)

end TestInt
