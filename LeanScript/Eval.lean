module

public import LeanScript.Expr

@[expose] public section

set_option autoImplicit false

/-!
TODO:

```
Term.evalClosed (t : Term Sg [] [] τ) : τ.den
```

* it takes **no fuel**;
* it answers in `τ.den`, not in `Option` or an error monad — it never gets stuck, so
  there is no progress theorem to prove and no neutral term to characterise;
* it is neither `partial` nor `unsafe`, and it uses no `sorry` and no extra axiom.
-/
