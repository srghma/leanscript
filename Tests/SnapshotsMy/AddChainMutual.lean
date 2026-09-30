/-!
Additions of literals folded across the two iterations of an unrolled `mutual` loop.

`swap`: `evenS`/`oddS` swap the fields, so after unrolling each variable only depends on
itself (`p = p + 5`).  `keep`: `evenK`/`oddK` keep the fields, so after unrolling the new first
field depends on the old second one and conversely — the second assignment must not read the
variable the first one just assigned.  `mixed`: literals of both signs (on `Int`), which may
only be combined when they cannot hide an overflow.
-/

mutual
  def evenS (n : Nat) (x y : Int) : Int × Int :=
    match n with
    | 0 => (x, y)
    | n + 1 => oddS n (y + 1) (x + 2)
  def oddS (n : Nat) (x y : Int) : Int × Int :=
    match n with
    | 0 => (x, y)
    | n + 1 => evenS n (y + 3) (x + 4)
end

mutual
  def evenK (n : Nat) (x y : Int) : Int × Int :=
    match n with
    | 0 => (x, y)
    | n + 1 => oddK n (y + 1) (x + 2)
  def oddK (n : Nat) (x y : Int) : Int × Int :=
    match n with
    | 0 => (x, y)
    | n + 1 => evenK n (x + 3) (y + 4)
end

mutual
  def evenM (n : Nat) (x : Int) (y : Nat) : Int × Nat :=
    match n with
    | 0 => (x, y)
    | n + 1 => oddM n (x - 7) (y + 1)
  def oddM (n : Nat) (x : Int) (y : Nat) : Int × Nat :=
    match n with
    | 0 => (x, y)
    | n + 1 => evenM n (x + 3) (y + 2)
end
