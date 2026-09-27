-- @js_export: ExprF, Add, Lit, Mul, functorExprF, test1, test2
inductive ExprF (α : Type) where
  | Lit : Int → ExprF α
  | Add : α → α → ExprF α
  | Mul : α → α → ExprF α

def mapExprF {α β : Type} (f : α → β) : ExprF α → ExprF β
  | .Lit n   => .Lit n
  | .Add a b => .Add (f a) (f b)
  | .Mul a b => .Mul (f a) (f b)

instance : Functor ExprF where
  map := mapExprF

structure FixExpr where
  unFix : ExprF FixExpr

-- Total, non-partial cata using mutual recursion
mutual
  def cata {α : Type} (alg : ExprF α → α) : FixExpr → α
    | ⟨f⟩ => alg (cataMap alg f)

  def cataMap {α : Type} (alg : ExprF α → α) : ExprF FixExpr → ExprF α
    | .Lit n   => .Lit n
    | .Add a b => .Add (cata alg a) (cata alg b)
    | .Mul a b => .Mul (cata alg a) (cata alg b)
end

def eval : ExprF Int → Int
  | .Lit n   => n
  | .Add a b => a + b
  | .Mul a b => a * b

def bump : ExprF Int → ExprF Int
  | .Lit n => .Lit (n + 1)
  | other  => other

def test1 (e : FixExpr) : Int :=
  cata eval e

def test2 (e : FixExpr) : Int :=
  cata (eval ∘ bump) e
