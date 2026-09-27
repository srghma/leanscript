module

public import LeanScript.Term.PExpr
public meta import LeanScript.ExternElab.TermShorthands

@[expose] public section

set_option autoImplicit false

/-!
# The calls of the externs, one term former per entry

For every entry `c` of the catalogue of externs (`LeanInitPureExtern`), the term formers
`PExpr.c` and `Neu.c`: the call of `c` on pure expressions of the types of its arguments
(`derive_extern_term_shorthands`, `LeanScript.ExternElab.TermShorthands`).  So

```
PExpr.lean_string_any (.lit .string "12345") f
  = .neu (.extern .lean_string_any (.cons (.lit .string "12345") (.cons f .nil)))
PExpr.lean_array_push .nat a x
  = .neu (.extern (.lean_array_push .nat) (.cons a (.cons x .nil)))
```

An entry with type arguments (`lean_array_push`) takes them first, explicitly.  The term
formers are reducible and usable in patterns.
-/

namespace LeanScript

derive_extern_term_shorthands PExpr
derive_extern_term_shorthands Neu

end LeanScript

end
