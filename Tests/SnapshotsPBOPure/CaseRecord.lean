structure ABC where
  a : Int
  b : Int
  c : Int

def test1 (x : ABC) : String :=
  match x with
  | { a := 1, .. } => "0"
  | { b := 1, .. } => "1"
  | { c := 1, .. } => "2"
  | { a := 2, b := 2, .. } => "3"
  | _ => "catch"

namespace Test2

structure InnerBC where
  b : Int
  c : Int

structure InnerEF where
  e : Int
  f : Int

structure Outer where
  a : InnerBC
  d : InnerEF

def test2 (x : Outer) : Int :=
  match x with
  | { a := { b := 1, c := 2 }, d := { e := 1, f := 2 } } => 1
  | { a := { b := _, c := 2 }, d := { e := 1, f := 2 } } => 2
  | { a := { b := 1, c := 2 }, d := _ } => 3
  | _ => 4

end Test2

/- Tests 3–6 -/

structure AB where
  a : Int
  b : Int

-- PureScript: { a } | a > 0 -> a; { a: _, b } | b > 1 -> b; _ -> 3
def test3 (x : AB) : Int :=
  match x with
  | { a, .. } =>
    if a > 0 then a
    else
      match x with
      | { a := _, b } =>
        if b > 1 then b
        else 3

-- PureScript: { a, b: _ } | a > 0 -> a; { b } | b > 1 -> b; _ -> 3
def test4 (x : AB) : Int :=
  match x with
  | { a, b := _ } =>
    if a > 0 then a
    else
      match x with
      | { b, .. } =>
        if b > 1 then b
        else 3

-- PureScript: { a, b: _ } | a > 0 -> a; { a: _, b } | b > 0 -> b; _ -> 0
def test5 (x : AB) : Int :=
  match x with
  | { a, b := _ } =>
    if a > 0 then a
    else
      match x with
      | { a := _, b } =>
        if b > 0 then b
        else 0

-- PureScript: { a, b } | a > 0 -> a | b > 0 -> b; _ -> 0
def test6 (x : AB) : Int :=
  match x with
  | { a, b } =>
    if a > 0 then a
    else if b > 0 then b
    else 0
