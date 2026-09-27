def test1 : Int32 := Int32.maxValue - 1
def test2 : Int32 := Int32.minValue + 1
def test3 : Char :=
  ⟨UInt32.ofNatLT
    -- Max 16-bit BMP char
    -- (PureScript's `top :: Char` / JS UTF-16 code unit)
    -- Not Lean's max Unicode char (0x10FFFF)
    0xFFFF
    (of_decide_eq_true rfl),
    Or.inr
    ⟨of_decide_eq_true rfl,
    of_decide_eq_true rfl
    ⟩
  ⟩
def test4 : Char := Char.ofNat 0
