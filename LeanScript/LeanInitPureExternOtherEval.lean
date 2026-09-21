module

public import Init
public import LeanScript.ExternEval

@[expose] public section

set_option autoImplicit false

/-!
# The meaning of the remaining terminal externs

The three-argument and five-argument families, and the *constants* of the runtime.

Both are **total**, one row per entry.

The constants (`LeanInitPureExtern_U_T`) are a family with no entries left: what
`lean_version_get_major`, `lean_system_platform_windows` or
`lean_internal_get_hardware_concurrency` answer is a fact about the machine the compiled
program will run on, not a function of any value, and reading it off *this* host would
bake the wrong answer into the semantics.  Rather than let them make the evaluator stick,
they are commented out of `LeanScript.LeanInitPureExterns` (marked `(‡)`) until the backend
has a target description to read them from, and `LeanInitPureExtern_U_T.eval` is total
because there is nothing to evaluate.
-/

namespace LeanScript

def LeanInitPureExtern_U_T.eval : ∀ {p : LeanPrimTy},
    LeanInitPureExtern_U_T p → p.denote
  | _, lean_version_get_special_desc          : LeanInitPureExtern_U_T .string -- always "leanscript"
  | _, lean_version_get_is_release            : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_version_get_major                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_version_get_patch                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_internal_is_stage0                : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_version_get_minor                 : LeanInitPureExtern_U_T .nat -- always 0
  | _, lean_get_githash                       : LeanInitPureExtern_U_T .string -- always "leanscript"
  | _, lean_internal_has_llvm_backend         : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_system_platform_emscripten        : LeanInitPureExtern_U_T .bool -- always false
  | _, lean_system_platform_target            : LeanInitPureExtern_U_T .string -- always "nodeorbrowser"

/-- The function a three-argument terminal extern denotes -/
def LeanInitPureExtern_T_T_T_T.eval : ∀ {a b c d : LeanPrimTy},
    LeanInitPureExtern_T_T_T_T a b c d → a.denote → b.denote → c.denote → d.denote
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
def LeanInitPureExtern_T_T_T_T_T.eval : ∀ {a b c d e f : LeanPrimTy},
    LeanInitPureExtern_T_T_T_T_T a b c d e f →
      a.denote → b.denote → c.denote → d.denote → e.denote → f.denote
  | _, _, _, _, _, _, .lean_string_memcmp, s1, s2, p1, p2, len =>
    String.Slice.Pattern.Internal.memcmpStr --TODO should use

end LeanScript

end
