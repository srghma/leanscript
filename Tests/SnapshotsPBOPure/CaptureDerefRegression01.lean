prelude
import Init.Data.Int.Basic

-- Should be optimized out, bc its newtype
private inductive Box (α : Type) where
  | mk : α → Box α

-- all non-recursive types should be passed as just fields to functions
def test1 (v : Int × Int) (b : Int) : Int :=
  v.1 + b

def test2 (v : Int × Int) : Int → Int :=
  fun b => v.1 + b

def test3 (v : Int × Int) : Box (Int → Int) :=
  .mk (fun b => v.1 + b)

-------------------------------------
private inductive Box2 (α : Type) where
  | mk : α → α → Box2 α

-- in both test4 and test5 arguments will be unboxed and then reboxed on return.
-- Why? Bc we assume user will use actually

-- TODO: Detect The "Re-Boxing" Trap (Where Unboxing Hurts)
-- ```
-- Caller (has Boxed { _1, _2 })
--   ↳ Unpacks to call f(v_1, v_2)
--       ↳ f needs to store v in an Array or pass to a generic function
--           ↳ f must RE-BOX: const v = { _1: v_1, _2: v_2 };
-- ```

def test4 (v : Int × Int) : Box2 (Int → Int) :=
  .mk (fun b => v.1 + b) (fun b => v.2 + b)

def test5 (v : Box2 Int) : Box2 (Int → Int) :=
  .mk (fun b => v.1 + b) (fun b => v.2 + b)

-- set_option trace.compiler.ir.result true

-- Mutual Tail-Recursion Passing and Unpacking Box2
-- NOTE: even lean doesnt perform TCO for these two, so can overflow
mutual
  def testEven (n : Nat) (b : Box2 Int) : Box2 Int :=
    match n with
    | 0 => b
    | n + 1 =>
      match b with
      | .mk x y => testOdd n (.mk (y + 1) (x + 2))

  def testOdd (n : Nat) (b : Box2 Int) : Box2 Int :=
    match n with
    | 0 => b
    | n + 1 =>
      match b with
      | .mk x y => testEven n (.mk (y + 3) (x + 4))
end
