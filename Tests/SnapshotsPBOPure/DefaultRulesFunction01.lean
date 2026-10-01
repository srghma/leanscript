def F := ∀ {α β γ : Type}, α → β → γ

-- test1: annotate that (g "foo" a) produces Nat
-- (a result of `Unit` would be one point: in a pure language such a function does nothing,
-- and `leanscript` skips it)
def test1 (f : F) (g : F) (a : Nat) : Nat :=
  f 1 <| (g "foo" a : Nat)

-- test2: annotate intermediate pipeline step
def test2 (f : F) (g : F) (a : Nat) : Nat :=
  (a |> g "foo" : Nat) |> f 1

-- test3: annotate intermediate flip result (say, Int)
def test3 (f : F) (g : F) : Nat → Nat :=
  fun _ => flip f 3 $ (flip g 2 1 : Int)

-- test4: works as-is
def test4 (f : F) : F :=
  fun b a => flip f a b

-- test5: works as-is
def test5 (α β : Type) (a : α) : β → α :=
  Function.const β a

-- test6: works as-is (and remains fully polymorphic!)
def test6 {α : Type} : α → α :=
  flip (Function.const Nat) 42
