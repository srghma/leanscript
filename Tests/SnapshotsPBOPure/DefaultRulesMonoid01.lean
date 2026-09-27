-- Scoped to `Monoid` to avoid clashing with Lean's built-in Alternative `guard`
namespace Monoid
  private def guard {M : Type} [EmptyCollection M] (b : Bool) (a : M) : M :=
    if b then a else ∅
end Monoid

-- type F = forall a. a -> a
private def F := ∀ {α : Type}, α → α

-- test1 :: Boolean -> Array Int
-- test1 = flip guard [ 1, 2, 3 ]
def test1 : Bool → Array Int :=
  flip Monoid.guard #[1, 2, 3]

-- test2 :: F -> Boolean -> Array Int
-- test2 f = flip guard (f [ 1, 2, 3 ])
def test2 (f : F) : Bool → Array Int :=
  flip Monoid.guard (f #[1, 2, 3])

-- Verification:
-- #eval test1 true   -- #[1, 2, 3]
-- #eval test1 false  -- #[]
