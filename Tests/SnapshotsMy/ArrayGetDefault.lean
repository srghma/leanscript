/-! `a[i]!` out of bounds reads the default of `Inhabited`: `a[i] ?? d` in JavaScript, at every
element type (no value of the language is `undefined` or `null`), with a literal or a variable
index and a literal, constructed or parameter default; and `i < a.size ? a[i] : d` (`getD`,
`if h : i < a.size`) as the same `a[i] ?? d`. -/

def boolAt (a : Array Bool) (i : Nat) : Bool := a[i]!

def optAt (a : Array (Option Nat)) (i : Nat) : Option Nat := a[i]!

def strAt (a : Array String) : String := a[1]!

def floatAt (a : Array Float) (i : Nat) : Float := a[i]!

def intAt (a : Array Int) (i : Nat) : Int := a[i]! + 1

def pairAt (a : Array (Nat × String)) (i : Nat) : Nat × String := a[i]!

def byteAt (a : ByteArray) (i : Nat) : UInt8 := a.get! i

def u8At (a : Array UInt8) (i : Nat) : UInt8 := a[i]!

def sumFirstTwo (a : Array Nat) : Nat := a[0]! + a[1]!

def getDAt (a : Array Nat) (i : Nat) : Nat := a.getD i 7

def diteAt (a : Array String) (i : Nat) (d : String) : String :=
  if h : i < a.size then a[i] else d

def getDCtor (a : Array (Option Nat)) (i : Nat) : Option Nat := a.getD i (some 3)
