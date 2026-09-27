/-
The operations of `BitVec w` for the widths a knob decides.

`bitvecRepr` (`LeanScript/Config.lean`) says how a bit vector of at least 32 bits is held:
as a JavaScript number under `--config=pbo`, as a `BigInt` under `--config=faithful`.
Both widths here are at least 32, so every value of this module follows that knob and
the two presets print different JavaScript — which is what the name
`…Configurable` claims and what `lake test` checks.

A bit vector narrower than 32 bits is a JavaScript number whatever the configuration
says, but the *width* a runtime operation is called with is a `Nat`, so even a module
of narrow bit vectors prints differently at the two presets; there is therefore no
`PrimOpBitVec01NonConfigurable` beside this file.
-/

namespace TestBitVec32

def add (a b : BitVec 32) : BitVec 32 := a + b
def sub (a b : BitVec 32) : BitVec 32 := a - b
def eq  (a b : BitVec 32) : Bool := a == b
def ne  (a b : BitVec 32) : Bool := a != b
def lt  (a b : BitVec 32) : Bool := a < b
def gt  (a b : BitVec 32) : Bool := a > b
def le  (a b : BitVec 32) : Bool := a <= b
def ge  (a b : BitVec 32) : Bool := a >= b
def mul (a b : BitVec 32) : BitVec 32 := a * b
def div (a b : BitVec 32) : BitVec 32 := a / b
def neg (a : BitVec 32) : BitVec 32 := -a

end TestBitVec32

namespace TestBitVec64

def add (a b : BitVec 64) : BitVec 64 := a + b
def sub (a b : BitVec 64) : BitVec 64 := a - b
def eq  (a b : BitVec 64) : Bool := a == b
def ne  (a b : BitVec 64) : Bool := a != b
def lt  (a b : BitVec 64) : Bool := a < b
def gt  (a b : BitVec 64) : Bool := a > b
def le  (a b : BitVec 64) : Bool := a <= b
def ge  (a b : BitVec 64) : Bool := a >= b
def mul (a b : BitVec 64) : BitVec 64 := a * b
def div (a b : BitVec 64) : BitVec 64 := a / b
def neg (a : BitVec 64) : BitVec 64 := -a

end TestBitVec64
