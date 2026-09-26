module

public import LeanScript.Ty.Instances

@[expose] public section

/-!
# Why the translations of the `List` library functions are sound

`#leanscript_to_term` translates a few functions of Lean's library by a rule rather than
by reading their definition (see `LeanScript/ToTerm/Overview.lean` and
`TermTests/ToTermTest/ListLibrary.lean`).  Each rule replaces a Lean expression by
another one, which is then translated as usual.  This file proves, for every input, that
each replacement is an equation of Lean's logic:

* `panic! msg` becomes the `default` of its `Inhabited` instance (`panic_eq_default`,
  and the same for the variants `l[i]!` and `a[i]!` reach);
* `l[i]!` becomes `l.getD i default` (`getElem!_eq_getD`);
* `l[i]` on a list, with its proof, becomes `l.getD i d`, for any default `d`
  (`getElem_eq_getD`);
* `l.getD i d` is `l[i]?.getD d` (`getD_eq_getElem?_getD`), and `l[i]?` is the recursion
  `nth?` with a catch-all pattern (`getElem?_eq_nth?`);
* `l.attach` and `l.attachWith P h` become `l`: a subtype has the tree of its values
  (`tyWfOf_subtype`), and reading the values of the attached list gives back `l`
  (`attach_unattach`, `attachWith_unattach`), so any `map` or `foldl` that reads only
  the values is the same function of `l` (`map_attach_val`, `foldl_attach_val`, …).
-/

namespace LeanScript.ListLibrary

/-! ## `panic!` is `default` -/

/-- `panic msg` is, in Lean's logic, the `default` of the instance it is handed. -/
theorem panic_eq_default {α : Sort u} [Inhabited α] (msg : String) :
    (panic msg : α) = default := rfl

/-- The same for `panicWithPos`, which `panic!` expands to. -/
theorem panicWithPos_eq_default {α : Sort u} [Inhabited α] (modName : String)
    (line col : Nat) (msg : String) :
    (panicWithPos modName line col msg : α) = default := rfl

/-- The same for `panicWithPosWithDecl`, which `panic!` inside a definition expands to
    (`List.get!Internal`'s out-of-range branch is one). -/
theorem panicWithPosWithDecl_eq_default {α : Sort u} [Inhabited α]
    (modName declName : String) (line col : Nat) (msg : String) :
    (panicWithPosWithDecl modName declName line col msg : α) = default := rfl

/-- The same for `outOfBounds`, which `a[i]!` on an array reaches. -/
theorem outOfBounds_eq_default {α : Sort u} [Inhabited α] :
    (outOfBounds : α) = default := rfl

/-! ## Indexing a list -/

/-- `l[i]!` is `l.getD i default`: in range the element, out of range `default`. -/
theorem getElem!_eq_getD {α : Type u} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = l.getD i default := by
  rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

/-- `l[i]` with its proof is `l.getD i d`, whatever the default `d`: the default is never
    reached when the index is in range. -/
theorem getElem_eq_getD {α : Type u} (l : List α) (i : Nat) (h : i < l.length) (d : α) :
    l[i] = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `l.getD i d` is `l[i]?.getD d`, by definition. -/
theorem getD_eq_getElem?_getD {α : Type u} (l : List α) (i : Nat) (d : α) :
    l.getD i d = l[i]?.getD d := rfl

/-- `l[i]?` written by hand as a recursion whose `match` has a catch-all pattern — the
    shape of `List.get?Internal`, which `l[i]?` is. -/
def nth? {α : Type u} : List α → Nat → Option α
  | a :: _, 0 => some a
  | _ :: as, n + 1 => nth? as n
  | _, _ => none

/-- `l[i]?` is `nth? l i`, for every list and index. -/
theorem getElem?_eq_nth? {α : Type u} (l : List α) (i : Nat) : l[i]? = nth? l i := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a t ih =>
      cases i with
      | zero => rfl
      | succ n => simp only [List.getElem?_cons_succ, ih, nth?]

/-! ## `List.attach` is the list itself -/

/-- A subtype `{x // p x}` has the tree of `α`: its proof is erased. -/
theorem tyWfOf_subtype {α : Type u} (p : α → Prop) [LeanScriptTyWf α] :
    tyWfOf (Subtype p) = tyWfOf α := rfl

/-- So `List {x // p x}` has the tree of `List α`. -/
theorem tyWfOf_list_subtype {α : Type u} (p : α → Prop) [LeanScriptTyWf α] :
    tyWfOf (List (Subtype p)) = tyWfOf (List α) := rfl

/-- The values of `l.attach` are `l`. -/
theorem attach_unattach {α : Type u} (l : List α) : l.attach.map Subtype.val = l :=
  List.attach_map_subtype_val l

/-- The values of `l.attachWith P h` are `l`. -/
theorem attachWith_unattach {α : Type u} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) : (l.attachWith P h).map Subtype.val = l :=
  List.attachWith_map_subtype_val h

/-- A `map` over `l.attach` that reads only the values is a `map` over `l`. -/
theorem map_attach_val {α : Type u} {β : Type v} (l : List α) (g : α → β) :
    l.attach.map (fun x => g x.1) = l.map g := by
  have h := congrArg (List.map g) (attach_unattach l)
  rwa [List.map_map] at h

/-- The same over `l.attachWith P h`. -/
theorem map_attachWith_val {α : Type u} {β : Type v} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) (g : α → β) :
    (l.attachWith P h).map (fun x => g x.1) = l.map g := by
  have h' := congrArg (List.map g) (attachWith_unattach l P h)
  rwa [List.map_map] at h'

/-- A `foldl` over `l.attach` that reads only the values is a `foldl` over `l`. -/
theorem foldl_attach_val {α : Type u} {β : Type v} (l : List α) (f : β → α → β) (b : β) :
    l.attach.foldl (fun acc x => f acc x.1) b = l.foldl f b := by
  rw [← List.foldl_map (f := Subtype.val) (g := f), attach_unattach]

/-- The same over `l.attachWith P h`. -/
theorem foldl_attachWith_val {α : Type u} {β : Type v} (l : List α) (P : α → Prop)
    (h : ∀ x ∈ l, P x) (f : β → α → β) (b : β) :
    (l.attachWith P h).foldl (fun acc x => f acc x.1) b = l.foldl f b := by
  rw [← List.foldl_map (f := Subtype.val) (g := f), attachWith_unattach]

/-- The pattern `(List.range n).attach.map fun ⟨i, h⟩ => l[i]'…`: indexing with the proof
    that membership in `List.range l.length` gives is `l.getD i d` at every `i`, so the
    whole map is a map of `getD` over `List.range l.length`, which is `l` mapped. -/
theorem map_range_attach_getElem {α : Type u} {β : Type v} (l : List α) (g : α → β)
    (d : α) :
    (List.range l.length).attach.map (fun x => g (l[x.1]'(List.mem_range.mp x.2))) =
      (List.range l.length).map (fun i => g (l.getD i d)) := by
  have h : ∀ x ∈ (List.range l.length).attach,
      g (l[x.1]'(List.mem_range.mp x.2)) = g (l.getD x.1 d) := fun x _ => by
    rw [getElem_eq_getD l x.1 _ d]
  rw [List.map_congr_left h]
  exact map_attach_val _ (fun i => g (l.getD i d))

end LeanScript.ListLibrary

end
