-- mutual
--   partial def f (a b : Int) : Int := g (a + b)
--   partial def g (a : Int) : Int := f a (a + 1)
-- end

mutual
  def f (fuel : Nat) (a b : Int) : Int :=
    match fuel with
    | 0 => a + b
    | fuel + 1 => g fuel (a + b)

  def g (fuel : Nat) (a : Int) : Int :=
    match fuel with
    | 0 => a
    | fuel + 1 => f fuel a (a + 1)
end
