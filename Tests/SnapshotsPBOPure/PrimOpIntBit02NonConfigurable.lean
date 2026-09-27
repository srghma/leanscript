-- import Lean

-- open Lean Elab Command

-- /-- Executes the non-configurable JS function via Bun and verifies it matches Lean. -/
-- def assertNonConfigurableJs
--     (jsFnName : String)
--     (leanVal : String)
--     (args : List String)
--     (projectRoot : String := "/home/srghma/projects/lean-js-backend")
--     (jsRelPath : String := "./SnapshotsPBOPure/PrimOpIntBit01NonConfigurable.js") : IO Unit := do
--   let argsJson := "[" ++ String.intercalate ", " (args.map (fun a => "\"" ++ a ++ "\"")) ++ "]"
--   let script :=
--     "import fs from 'node:fs';\n" ++
--     "import path from 'node:path';\n" ++
--     "const root = '" ++ projectRoot ++ "';\n" ++
--     "let resolvedPath = path.resolve(root, '" ++ jsRelPath ++ "');\n" ++
--     "if (!fs.existsSync(resolvedPath)) {\n" ++
--     "  resolvedPath = path.resolve(root, './SnapshotsPBOPure/PrimOpIntBit02NonConfigurable.js');\n" ++
--     "}\n" ++
--     "const mod = await import(resolvedPath);\n" ++
--     "const fnName = '" ++ jsFnName ++ "';\n" ++
--     "const fn = mod[fnName];\n" ++
--     "if (typeof fn !== 'function') {\n" ++
--     "  console.error('Export ' + fnName + ' not found in ' + resolvedPath);\n" ++
--     "  process.exit(1);\n" ++
--     "}\n" ++
--     "const rawArgs = " ++ argsJson ++ ";\n" ++
--     "let res = fn;\n" ++
--     "for (const a of rawArgs) {\n" ++
--     "  if (typeof res !== 'function') break;\n" ++
--     "  res = res(Number(a));\n" ++
--     "}\n" ++
--     "console.log(res.toString());\n"

--   let out ← IO.Process.output {
--     cmd := "bun",
--     args := #["-e", script],
--     cwd := some projectRoot
--   }

--   if out.exitCode != 0 then
--     throw <| IO.userError s!"[JS Error for {jsFnName}]:\n{out.stderr.trimAscii.toString}"

--   let jsVal := out.stdout.trimAscii.toString
--   let argsStr := String.intercalate ", " args

--   if jsVal != leanVal then
--     throw <| IO.userError
--       s!"Assertion failed for {jsFnName}({argsStr})!\n  Lean: {leanVal}\n  JS:   {jsVal}"

--   IO.println s!"✓ PASS | {jsFnName}({argsStr}) | Lean: {leanVal} == JS: {jsVal}"

-- /-- Syntax: `#def name : Type := expr` -/
-- syntax (name := testDefNonConfigCmd) "#def " ident " : " term " := " term : command

-- elab_rules : command
--   | `(#def $id:ident : $ty:term := $rhs:term) => do
--     -- 1. Elaborate regular Lean definition
--     elabCommand (← `(def $id : $ty := $rhs))

--     -- 2. Namespace prefix (e.g. TestUInt8)
--     let currNs ← getCurrNamespace

--     -- 3. Map operator to JS export name
--     match rhs with
--     | `($a:term &&& $b:term) =>
--       let jsName := (currNs ++ `land).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term ||| $b:term) =>
--       let jsName := (currNs ++ `lor).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term <<< $b:term) =>
--       let jsName := (currNs ++ `shiftLeft).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term >>> $b:term) =>
--       let jsName := (currNs ++ `shiftRight).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `($a:term ^^^ $b:term) =>
--       let jsName := (currNs ++ `xor).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty)), toString $b]))
--     | `(~~~$a:term) =>
--       let jsName := (currNs ++ `complement).toString.replace "." "$"
--       elabCommand (← `(#eval! assertNonConfigurableJs $(quote jsName) (toString $id) [toString (($a : $ty))]))
--     | _ =>
--       throwErrorAt rhs s!"#def expects a bitwise expression (&&&, |||, <<<, >>>, ^^^, ~~~), but got: {rhs}"

--------------------------------------------------------------------------------
-- Tests
--------------------------------------------------------------------------------

namespace TestUInt8

def land : UInt8 := 1023 &&& 8
def lor  : UInt8 := 16 ||| 15
def shiftLeft : UInt8 := (1023 : UInt8) <<< 2
def shiftRight : UInt8 := (-1023 : UInt8) >>> 2
def xor : UInt8 := 15 ^^^ 12
def complement : UInt8 := ~~~(-3)

end TestUInt8

namespace TestUInt16

def land : UInt16 := 1023 &&& 8
def lor  : UInt16 := 16 ||| 15
def shiftLeft : UInt16 := (1023 : UInt16) <<< 2
def shiftRight : UInt16 := (-1023 : UInt16) >>> 2
def xor : UInt16 := 15 ^^^ 12
def complement : UInt16 := ~~~(-3)

end TestUInt16

namespace TestUInt32

def land : UInt32 := 1023 &&& 8
def lor  : UInt32 := 16 ||| 15
def shiftLeft : UInt32 := (1023 : UInt32) <<< 2
def shiftRight : UInt32 := (-1023 : UInt32) >>> 2
def xor : UInt32 := 15 ^^^ 12
def complement : UInt32 := ~~~(-3)

end TestUInt32

-------------------------------------------

namespace TestInt8

def land : Int8 := 1023 &&& 8
def lor  : Int8 := 16 ||| 15
def shiftLeft : Int8 := (1023 : Int8) <<< 2
def shiftRight : Int8 := (-1023 : Int8) >>> 2
def xor : Int8 := 15 ^^^ 12
def complement : Int8 := ~~~(-3)

end TestInt8

namespace TestInt16

def land : Int16 := 1023 &&& 8
def lor  : Int16 := 16 ||| 15
def shiftLeft : Int16 := (1023 : Int16) <<< 2
def shiftRight : Int16 := (-1023 : Int16) >>> 2
def xor : Int16 := 15 ^^^ 12
def complement : Int16 := ~~~(-3)

end TestInt16

namespace TestInt32

def land : Int32 := 1023 &&& 8
def lor  : Int32 := 16 ||| 15
def shiftLeft : Int32 := (1023 : Int32) <<< 2
def shiftRight : Int32 := (-1023 : Int32) >>> 2
def xor : Int32 := 15 ^^^ 12
def complement : Int32 := ~~~(-3)

end TestInt32
