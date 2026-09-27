-- @js_export: TestEnum, instBEqTestEnum, test1, test2
inductive TestEnum where
  | foo
  | bar
  | baz
  | qux
deriving BEq

-- #print instBEqTestEnum
def test1 (a : TestEnum) : Bool := .baz == a
def test2 (a : TestEnum) : Bool := a == .baz
