/-!
# Branches that begin with the same computation, and a string position of `0`

Two things the backend does with this file:

* `test1` and `test2` are matches whose clauses differ only in what they *append* to a
  common message. Each compiles to one `if` whose branches begin with the same
  computation, and that value is computed once, in front of the test.
* `test3`, `test4` and `test5` address a string at byte position `0`. A Lean string
  position is a byte offset into the UTF-8 encoding, but at the beginning of a string
  it is a character position, so these are ordinary JavaScript string operations and
  the general implementations (which build the UTF-8 view of the string) are not
  emitted at all.
-/

def test1 (file : Option String) (code : Nat) (msg : String) : String :=
  match file with
  | none => msg ++ " (error code: " ++ toString code ++ ")"
  | some f => msg ++ " (error code: " ++ toString code ++ ")\n  file: " ++ f

def test2 (xs : List String) (n : Nat) : String :=
  match xs with
  | [] => "[" ++ toString (n * n + 1) ++ "]"
  | x :: _ => "[" ++ toString (n * n + 1) ++ ", " ++ x ++ "]"

def test3 (s : String) : Char := String.Pos.Raw.get s ⟨0⟩

def test4 (s : String) (c : Char) : String := String.Pos.Raw.set s ⟨0⟩ c

def test5 (s : String) : Bool := String.Pos.Raw.atEnd s ⟨0⟩
