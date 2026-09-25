module

public import Lean.Data.Options

/-!
# How deep the translation searches for a fold

`#leanscript_to_term` reads the depth `k` of a fold (`nat_rec k`, `array_rec k`,
`recTaggedUnion_rec k`, `recObject_rec k`, `recAlias_rec k`,
`mutualRecursiveFamily_rec k`) off the compiled recursion by trying `k = 0, 1, 2, …` in
turn and keeping the first depth at which every read of the history is served.  The
options below bound that search; a recursion deeper than the bound is refused, naming the
option to raise.

```lean
set_option leanscript.toTerm.maxRecUnionRecDepth 20 in
def deep_term := #leanscript_to_term deep
```
-/

public section

/-- How deep a `nat_rec k` (and an `array_rec k`) the translation searches for. -/
register_option leanscript.toTerm.maxNatRecDepth : Nat := {
  defValue := 64
  descr := "`#leanscript_to_term`: the largest depth `k` of a `nat_rec k` or `array_rec k` \
    that the translation searches for"
}

/-- How deep a `recObject_rec k` or `recAlias_rec k` the translation searches for. -/
register_option leanscript.toTerm.maxRecObjectRecDepth : Nat := {
  defValue := 24
  descr := "`#leanscript_to_term`: the largest depth `k` of a `recObject_rec k` or \
    `recAlias_rec k` that the translation searches for"
}

/-- How deep a `recTaggedUnion_rec k` the translation searches for. -/
register_option leanscript.toTerm.maxRecUnionRecDepth : Nat := {
  defValue := 16
  descr := "`#leanscript_to_term`: the largest depth `k` of a `recTaggedUnion_rec k` that \
    the translation searches for"
}

/-- How deep a `mutualRecursiveFamily_rec k` the translation searches for. -/
register_option leanscript.toTerm.maxRecFamilyRecDepth : Nat := {
  defValue := 16
  descr := "`#leanscript_to_term`: the largest depth `k` of a `mutualRecursiveFamily_rec k` \
    that the translation searches for"
}

end
