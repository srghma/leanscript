/-!
# What the backend's inliner does

`LeanScript.Inline` rewrites a saturated call of a top-level declaration into that
declaration's body, with the arguments of the call in place of its parameters.  The
four groups below are the four answers it can give.
-/

/-- Lean marks this `@[inline]`, so a call of it is inlined whatever its size. -/
@[inline] def foo (a b : Nat) : Nat := a * b + a

/-- `foo 1 2`: a call of an `@[inline]` declaration with literal arguments. -/
def bar : Nat := foo 1 2

/-- Small, and Lean says nothing about it, so a call of it is inlined too.  Nothing
    exports it once its call sites have their own copy, and the emitted module does not
    bind it. -/
private def scale (a : Nat) : Nat := a * 2

/-- Two calls of `scale`, each of which becomes `a * 2`. -/
def useScale (n : Nat) : Nat := scale n + scale (n + 1)

/-- `@[noinline]` is a prohibition the backend keeps: a call of this stays a call. -/
@[noinline] def triple (a : Nat) : Nat := a * 3

/-- Two calls of `triple`, both of which are still calls in the emitted module. -/
def useTriple (n : Nat) : Nat := triple n + triple (n + 1)
