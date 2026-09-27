def known1 : String :=
  (some "c").map (fun _ => "b") |>.getD "a"

def test1 (a : Sum Int Int) : Int :=
  match some a with
  | some (Sum.inl b) => b
  | some (Sum.inr c) => c
  | none => 42

def test2 (x : Int) : String :=
  let a := if x > 42 then some "Hello" else none
  match a with
  | some str => str ++ ", World!"
  | none => ""

def test3 (x : Int) : Array String :=
  let a := if x > 42 then some "Hello" else some "Default"
  match a with
  | some s => #[ s ++ ", World", s ++ ", Universe" ]
  | none => #[]

def test4 (f : String → String → String) (x : Int) : String :=
  let a := if x > 42 then some "Hello" else some "Default"
  match a with
  | some s => f (s ++ ", World") (s ++ ", Universe")
  | none => ""

def test5 (x : Int) : Bool :=
  let a := if x > 42 then some true else some false
  match a with
  | some b => b && !b
  | none => false

inductive TestEnum where | Foo | Bar | Baz | Qux

def fromString (s : String) : Option TestEnum :=
  match s with
  | "foo" => some .Foo
  | "bar" => some .Bar
  | "baz" => some .Baz
  | "qux" => some .Qux
  | _ => none

def test6 (a : String) : Int :=
  match fromString a with
  | some .Foo => 1
  | some .Bar => 2
  | some .Baz => 3
  | some .Qux => 4
  | none => 0
