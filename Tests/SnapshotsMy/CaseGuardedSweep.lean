/-!
`test1` and `test4` of `Tests/SnapshotsPBOPure/CaseGuarded.lean`, run by `sweep1`/`sweep4` on
every input that reaches a different branch (`n` from `lo` to `lo + 109`; every combination
of `a`, `b`, `d`, `f`, `c`, `e` around the literals of the patterns), so that the differential
checks cover every branch of the generated code: `toString` of an `Int` (`"n: " + n`), the
`&&` of two tests, and the two tests of `test4` that end in the same `return`, merged.
-/

def test1 (n : Int) : String :=
  if n < 1 then "n: " ++ toString n
  else if n > 1 && n < 100 then "1 < x < 100: " ++ toString n
  else "catch"

structure Rec1 where
  a : Int
  b : Int
  c : Int

structure Rec2 where
  d : Int
  e : Int
  f : Int

def test4 : Rec1 → Rec2 → Int
  | { a := 1, .. }, { d := 1, .. } => 1
  | _,              { d := 2, .. } => 2
  | _,              { d := 3, .. } => 3
  | { a := 1, .. }, { d := 4, .. } => 4
  | { a := 1, .. }, { d := 5, .. } => 5
  | { a := 2, .. }, { d := 1, .. } => 6
  | { c, .. },      { d := 4, e, .. } =>
    if c == e then 7
    else if c < e then 8
    else 9
  | { b := 2, .. }, { d := 1, f := 10, .. } => 10
  | { c, .. },      { f, .. } => 11 + c + f

def sweep1 (lo : Int) : String := Id.run do
  let mut s := ""
  for i in [0:110] do
    s := s ++ test1 (lo + i) ++ ";"
  return s

def sweep4 (lo : Int) : Int := Id.run do
  let mut acc : Int := 0
  for a in [0:4] do
    for b in [0:3] do
      for d in [0:7] do
        for f in [9:11] do
          for c in [0:3] do
            for e in [0:3] do
              let r := test4 ⟨lo + a, lo + b, lo + c⟩ ⟨lo + d, lo + e, lo + f⟩
              acc := acc * 31 % 1000000007 + r
  return acc
