/-! Variations of `Tests/SnapshotsPBOPure/PrimOpChar02.lean`: the comparisons of `charValues`
applied to an unknown character `c`, so that they are not folded to literals.  A comparison of
`c` with itself (`c == c`, `c < c`, `c ≤ c`) is a literal, and a literal on the left of `==` is
written on the right (`"a" === c` is `c === "a"`). -/

/-- `charValues` of `PrimOpChar02` without `@[inline]`: still inlined and folded. -/
def charValuesNI (op : Char → Char → Bool) : Array Bool :=
  #[ op 'a' 'a', op 'a' 'b', op 'b' 'a' ]

def u1 := charValuesNI (fun a b => a == b)
def u3 := charValuesNI (fun a b => decide (a < b))
def u4 := charValuesNI (fun a b => a > b)

@[inline] def charValuesAt (op : Char → Char → Bool) (c : Char) : Array Bool :=
  #[ op c 'a', op 'a' c, op c c ]

def v1 (c : Char) := charValuesAt (fun a b => a == b) c
def v2 (c : Char) := charValuesAt (fun a b => a != b) c
def v3 (c : Char) := charValuesAt (fun a b => decide (a < b)) c
def v4 (c : Char) := charValuesAt (fun a b => a > b) c
def v5 (c : Char) := charValuesAt (fun a b => decide (a <= b)) c
def v6 (c : Char) := charValuesAt (fun a b => decide (a >= b)) c

/-- The same on the other leaf types with an order. -/
def selfNat (n : Nat) : Array Bool := #[n == n, n < n, n ≤ n, n != n]
def selfInt (i : Int) : Array Bool := #[i == i, i < i, i ≤ i, i > i, i ≥ i]
def selfString (s : String) : Array Bool := #[s == s, s < s, s ≤ s, "x" == s, "x" != s]
def selfUInt8 (x : UInt8) : Array Bool := #[x == x, x < x, x ≤ x]
def selfUInt64 (x : UInt64) : Array Bool := #[x == x, x < x, x ≤ x]
def selfInt32 (x : Int32) : Array Bool := #[x == x, x < x, x ≤ x]

/-- Not folded: `x == x` on floats is `false` for `NaN`. -/
def selfFloat (x : Float) : Array Bool := #[x == x, x < x, x ≤ x]

/-- A comparison with itself used as a condition. -/
def selfCond (c : Char) (n : Nat) : Nat := if c ≤ c && n == n then n + 1 else 0

def isSpace (c : Char) : Bool := c.isWhitespace
def ofNatChar (n : Nat) : Char := Char.ofNat n
def astral : Array Bool := #['😀' < 'a', '\uE000' < '😀']

/-- Several parameters, each compared with itself only. -/
def selfMixed (s : String) (n : Nat) (i : Int) (x : UInt8) : Array Bool :=
  #[s == s, s < s, n == n, n < n, n ≤ n, i < i, i ≤ i, x == x, x < x]
