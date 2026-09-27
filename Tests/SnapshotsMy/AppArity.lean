set_option trace.Compiler.saveMono true   -- mono LCNF phase
set_option trace.Compiler.result true     -- final LCNF result
-- Applying a value that is a closure this program built: every argument at once.
@[inline] def mkAdd (n : Nat) : Nat → Nat → Nat := fun a b => a + b + n

@[inline] private def applyTwice (f : Nat → Nat → Nat) (x y : Nat) : Nat := f x y + f y x

def test1 (n x y : Nat) : Nat := applyTwice (mkAdd n) x y

-- A second closure reaching the same parameter changes nothing: it is a closure too.
@[noinline] def mkMul (n : Nat) : Nat → Nat → Nat := fun a b => a * b * n

def test2 (n x y : Nat) : Nat := applyTwice (mkMul n) x y

-- Three arguments at once.
@[noinline] def mkSum3 (n : Nat) : Nat → Nat → Nat → Nat := fun a b c => a + b + c + n

@[noinline] private def applyThree (f : Nat → Nat → Nat → Nat) (x y : Nat) : Nat := f x y x

def test3 (n x y : Nat) : Nat := applyThree (mkSum3 n) x y

-- A function value the caller of the generated file supplies is applied one argument
-- at a time: nothing is known about what it is.
def test4 (f : Nat → Nat → Nat) (x y : Nat) : Nat := f x y + f y x
