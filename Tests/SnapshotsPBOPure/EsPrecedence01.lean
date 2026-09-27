-- since `f a` is pure function - it will be cached by optimizer, so `f a` calls will be optimized to single call
--
-- TODO:
-- since `f a` is the only found optimization - function will be rendered as
-- ```
-- const test1 = (f, a) => {
--   let $0 = f(a);
--   return (b) => ...
-- ```
-- ???
def test1 (f : Unit → Bool) (a b : Unit) : Bool :=
  let x := if f a then f b else false
  let y := if x then f a else true
  if y then f a else f ()
