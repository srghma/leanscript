import Std.Data.HashMap

def test1 (a : Std.HashMap String Int) : Int :=
  a.get! "foo"

def test2 (a : Std.HashMap String Int) : Int :=
  a.get! "foo.bar"

def test3 (a : Std.HashMap String Int) (b : String) : Int :=
  a.get! b

def test4 (a : Std.HashMap String Int) : Array String :=
  a.keys.toArray

def test5 (a : Std.HashMap String Int) : Bool :=
  a["wat"]?.isSome
