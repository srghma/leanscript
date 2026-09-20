module

public import Init
public import LeanScript.ExternEval

@[expose] public section

set_option autoImplicit false

/-!
# The meaning of the remaining terminal externs

The three-argument and five-argument families, and the *constants* of the runtime.

Both are **total**, one row per entry.

The constants (`LeanInitPureExternLazy`) are a family with no entries left: what
`lean_version_get_major`, `lean_system_platform_windows` or
`lean_internal_get_hardware_concurrency` answer is a fact about the machine the compiled
program will run on, not a function of any value, and reading it off *this* host would
bake the wrong answer into the semantics.  Rather than let them make the evaluator stick,
they are commented out of `LeanScript.LeanInitPureExterns` (marked `(‡)`) until the backend
has a target description to read them from, and `LeanInitPureExternLazy.eval` is total
because there is nothing to evaluate.
-/

namespace LeanScript

/-- The function a three-argument terminal extern denotes -/
def LeanInitPureExtern3OnlyPrim.eval : ∀ {a b c d : LeanPrimTy},
    LeanInitPureExtern3OnlyPrim a b c d → a.denote → b.denote → c.denote → d.denote
  | _, _, _, _, .lean_substring_extract, s, i, j => (Substring.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_pushn, s, c, n => (String.pushn s c n)
  | _, _, _, _, .lean_string_utf8_extract, s, i, j => (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_utf8_extract_fast, s, i, j =>
      (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_utf8_extract_basic, s, i, j =>
      (String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩)
  | _, _, _, _, .lean_string_pos_raw_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)
  | _, _, _, _, .lean_string_pos_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)
  | _, _, _, _, .lean_string_set, s, i, c => (String.Pos.Raw.set s ⟨i⟩ c)

/-- The function a five-argument terminal extern denotes: `lean_string_memcmp` compares
    `len` bytes of two strings, each from its own byte position. -/
def LeanInitPureExtern5.eval : ∀ {a b c d e f : LeanPrimTy},
    LeanInitPureExtern5 a b c d e f →
      a.denote → b.denote → c.denote → d.denote → e.denote → f.denote
  | _, _, _, _, _, _, .lean_string_memcmp, s1, s2, p1, p2, len =>
      (strBytes s1 p1 (p1 + len) == strBytes s2 p2 (p2 + len))

/-- What a constant of the runtime answers with.  Total for the vacuous reason: every
    constant of the catalogue is a fact about the *target* machine, so all of them are
    commented out of `LeanInitPureExternLazy`, which is therefore empty.  See this
    module's header, and `(‡)` in `LeanScript.LeanInitPureExterns`. -/
def LeanInitPureExternLazy.eval : ∀ {p : LeanPrimTy},
    LeanInitPureExternLazy p → p.denote
  | _, e => nomatch e

end LeanScript

end
