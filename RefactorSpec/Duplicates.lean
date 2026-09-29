module

public import LanguageJavascriptCommon.Types
public import JsTerm.Syntax.Basic
public import LeanScript.WFTerm.Syntax

@[expose] public section

set_option autoImplicit false

/-!
# The other duplications, stated and proved

* `Legacy.NEList` is the removed non-empty list of `LanguageJavascriptCommon/Types.lean`;
  `neList_equiv_nonEmptyList` shows it is the `NonEmptyList` of the `NonEmpty` library under
  another name (inverse maps that keep the elements).
* `LeanScript.WFFnVar` (the index of a global function) and `MoreJs.JsMem` (a typed position in
  a list) are the same type family: `wfFnVarToJsMem` and `jsMemToWFFnVar` are inverse.
* `lookup_eq_find?_map`: the key lookup written by hand in `JsTerm/Passes/Hoist.lean`
  (`(l.find? (·.1 == n)).map (·.2)`) is core's `List.lookup` on a list.
* `JSNumber.repeatChar` and `JSNumber.powNat` are `String.pushn` and `^` under other names.

(That `JSNumber.digitChar` is `Nat.digitChar` below 16 was already proved in the project:
`Language.JavaScript.LiteralPrintSpec.JSNumber.digitChar_eq`.)
-/

namespace MoreJs.RefactorSpec

open NonEmpty.ListCorrectByConstruction (NonEmptyList)

/-- The removed `NEList` of `LanguageJavascriptCommon/Types.lean`. -/
structure Legacy.NEList (α : Type) where
  hd : α
  tl : List α

/-- The removed `NEList.toList`. -/
def Legacy.NEList.toList {α : Type} (l : Legacy.NEList α) : List α := l.hd :: l.tl

/-- A removed `NEList` as a `NonEmptyList`. -/
def Legacy.NEList.toNonEmptyList {α : Type} (l : Legacy.NEList α) : NonEmptyList α :=
  ⟨l.hd, l.tl⟩

/-- A `NonEmptyList` as a removed `NEList`. -/
def Legacy.NEList.ofNonEmptyList {α : Type} (l : NonEmptyList α) : Legacy.NEList α :=
  ⟨l.head, l.tail⟩

/-- The removed `NEList` is `NonEmptyList`: the two maps are inverse and keep the elements. -/
theorem neList_equiv_nonEmptyList {α : Type} :
    (∀ l : Legacy.NEList α, Legacy.NEList.ofNonEmptyList l.toNonEmptyList = l) ∧
    (∀ l : NonEmptyList α, (Legacy.NEList.ofNonEmptyList l).toNonEmptyList = l) ∧
    (∀ l : Legacy.NEList α, l.toNonEmptyList.toList = l.toList) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

section Mem

variable {ks : List Nat} {Δ : LeanScript.DSig ks}

/-- An index of a global function is a position in the list of functions. -/
def wfFnVarToJsMem : {fs : List (LeanScript.WFFn Δ)} → {f : LeanScript.WFFn Δ} →
    LeanScript.WFFnVar fs f → JsMem fs f
  | _, _, .here => .zero
  | _, _, .there v => .succ (wfFnVarToJsMem v)

/-- A position in the list of functions is an index of a global function. -/
def jsMemToWFFnVar : {fs : List (LeanScript.WFFn Δ)} → {f : LeanScript.WFFn Δ} →
    JsMem fs f → LeanScript.WFFnVar fs f
  | _, _, .zero => .here
  | _, _, .succ v => .there (jsMemToWFFnVar v)

theorem jsMemToWFFnVar_wfFnVarToJsMem : ∀ {fs : List (LeanScript.WFFn Δ)}
    {f : LeanScript.WFFn Δ} (v : LeanScript.WFFnVar fs f), jsMemToWFFnVar (wfFnVarToJsMem v) = v
  | _, _, .here => rfl
  | _, _, .there v => by
    simp only [wfFnVarToJsMem, jsMemToWFFnVar, jsMemToWFFnVar_wfFnVarToJsMem v]

theorem wfFnVarToJsMem_jsMemToWFFnVar : ∀ {fs : List (LeanScript.WFFn Δ)}
    {f : LeanScript.WFFn Δ} (v : JsMem fs f), wfFnVarToJsMem (jsMemToWFFnVar v) = v
  | _, _, .zero => rfl
  | _, _, .succ v => by
    simp only [wfFnVarToJsMem, jsMemToWFFnVar, wfFnVarToJsMem_jsMemToWFFnVar v]

end Mem

/-- Looking up a key by `find?` and taking the value is `List.lookup`. -/
theorem lookup_eq_find?_map {β : Type} (n : String) :
    ∀ l : List (String × β), (l.find? (·.1 == n)).map (·.2) = l.lookup n
  | [] => rfl
  | (k, b) :: l => by
    by_cases h : k = n
    · subst h; simp [List.lookup]
    · have h' : (n == k) = false := by simp; exact fun e => h e.symm
      have h'' : (k == n) = false := by simp; exact h
      simp only [List.find?, List.lookup, h', h'']
      exact lookup_eq_find?_map n l

/-- `repeatChar` is `String.pushn`. -/
theorem repeatChar_eq (c : Char) (n : Nat) :
    Language.JavaScript.JSNumber.repeatChar c n = "".pushn c n := rfl

/-- `powNat` is `^`. -/
theorem powNat_eq (b e : Nat) : Language.JavaScript.JSNumber.powNat b e = b ^ e := rfl

end MoreJs.RefactorSpec

end
