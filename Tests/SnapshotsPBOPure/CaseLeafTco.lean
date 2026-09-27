-- partial def test1 (b : Bool) (arr : Array Int) : Array Int :=
--   let head? : Option Int := arr[0]?
--   let last? : Option Int := arr.back?
--   match head?, last? with
--   | some 1, some 2 => arr
--   | none, some y => arr.push y
--   | none, none => arr
--   | some x, none => arr.push x
--   | some x, some y =>
--     if b then
--       #[]
--     else
--       test1 b (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)

def test1Fuel : Nat → Bool → Array Int → Array Int
  | 0,     _, arr => arr
  | n + 1, b, arr =>
    match (arr[0]? : Option Int), arr.back? with
    | some 1, some 2 => arr
    | none,   some y => arr.push y
    | none,   none   => arr
    | some x, none   => arr.push x
    | some x, some y =>
      if b then
        #[]
      else
        test1Fuel n b
          (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)

def test1FuelCalled (b : Bool) (arr : Array Int) : Array Int :=
  test1Fuel 1000000 b arr

-- this approach doesnt work
--
-- def test1 (b : Bool) (arr : Array Int) (h : arr = #[]) : Array Int :=
--   let head? : Option Int := arr[0]?
--   let last? : Option Int := arr.back?
--   match head?, last? with
--   | some 1, some 2 => arr
--   | none, some y => arr.push y
--   | none, none => arr
--   | some x, none => arr.push x
--   | some x, some y =>
--     if b then
--       #[]
--     else
--       test1 b (#[ y, x, 3, y, 5, 6, 7, 8, 9, 10, x, 12, 13, 14, 15, 16, 17 ] ++ arr)
