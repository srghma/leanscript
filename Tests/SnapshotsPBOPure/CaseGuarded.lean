def test1 (n : Int) : String :=
  if n < 1 then "n: " ++ toString n
  else if n > 1 && n < 100 then "1 < x < 100: " ++ toString n
  else "catch"

inductive NInt where
  | mk : Int → NInt

def test2 : NInt -> Int
  | .mk i =>
    if i < 1 then i
    else if i > 1 then i
    else if i == 1 then 1
    else 0

inductive Product3 (α β γ : Type) where
  | mk : α → β → γ → Product3 α β γ

def test3 : Product3 Int Int Int -> Int
  | .mk a b c =>
    if a == b then a
    else if c == b then a
    else if a == c then c
    else b

structure Rec1 where
  a : Int
  b : Int
  c : Int
deriving Repr

structure Rec2 where
  d : Int
  e : Int
  f : Int
deriving Repr

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

def test5 (x? : Option (Except Int Int)) : Int :=
  match x? with
  | some (.ok y) => y
  | some (.error 2) => 4
  | _ => 5
