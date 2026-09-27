-- @js_export: test1, test2, test3
inductive Variant where
  | foo : Int → Variant
  | bar : Bool → Variant
  | baz : String → Variant

def test1 : Variant → String
  | Variant.foo i => toString i
  | Variant.bar b => toString b
  | Variant.baz s => s
