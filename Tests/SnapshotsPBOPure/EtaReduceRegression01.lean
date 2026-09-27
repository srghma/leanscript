prelude
import Init.Prelude
import Init.Data.String

-- 1. Identity function (exported standalone)
def identity (x : α) : α := x

-- 2. Monoid typeclass & String instance
class Monoid (α : Type u) where
  empty : α
  append : α → α → α

instance : Monoid String where
  empty := ""
  append := String.append

-- 3. Foldable typeclass & Option instance
class Foldable (f : Type u → Type v) where
  foldMap : {α : Type u} → {m : Type w} → [Monoid m] → (α → m) → f α → m

instance : Foldable Option where
  foldMap f
    | none   => Monoid.empty
    | some x => f x

-- 4. Point-free `fold` with explicit dictionary names
-- Notice there is no explicit `(x : f α)` argument!
def fold {f : Type u → Type v} {α : Type u}
    [dictFoldable : Foldable f] [dictMonoid : Monoid α] : f α → α :=
  Foldable.foldMap identity

-- 5. Point-free `test`
-- Notice there is no explicit `(v : Option String)` argument!
def test : Option String → String :=
  fold
