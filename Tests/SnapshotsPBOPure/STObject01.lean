-- @js_export: test1, test2, test3, test4, test5, test6
private def poke (k : String) (v : Int) (m : List (String × Int)) : List (String × Int) :=
  (k, v) :: m.filter (fun p => p.1 != k)

private def deleteKey (k : String) (m : List (String × Int)) : List (String × Int) :=
  m.filter (fun p => p.1 != k)

def test1 : List (String × Int) := []

def test3 : List (String × Int) :=
  let m := []
  let m := poke "a" 1 m
  let m := poke "b" 2 m
  let m := poke "c" 3 m
  m

def test5 : List (String × Int) :=
  let m := []
  let m := poke "a" 1 m
  let m := poke "b" 2 m
  let m := deleteKey "a" m
  let m := deleteKey "b" m
  m
