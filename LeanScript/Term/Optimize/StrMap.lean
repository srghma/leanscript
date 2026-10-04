module

public import LeanScript.Term.Semantics.Eval
public import LeanScript.Term.Extern.Eval
public import LeanScript.Term.Optimize.Fold
public import LeanScript.Term.Optimize.Count

@[expose] public section

set_option autoImplicit false

/-!
# Hash maps with string keys

Two rewrites of the operations on hash maps with string keys (`StrMapExtern`,
`LeanScript.LeanInitPureExterns.StrMap`), each proved to preserve the value:

* `(m.keys).toArray` is `m.keysArray` (`Std.HashMap.toArray_keys`) and `(m.toList).toArray` is
  `m.toArray` (`Std.HashMap.toArray_toList`): the array is built at once, without the list in
  between (`Neu.normStrMapArray`, applied by `Term.appendWalk` at every extern call);
* a case analysis of `m[k]?` whose two arms answer Boolean literals, as `Option.isSome` unfolds
  to, `match m[k]? with | none => a | some _ => b`, is `m.contains k ? b : a`
  (`Std.HashMap.isSome_getElem?_eq_contains`), and so `m.contains k` itself when `a` is `false`
  and `b` is `true` (`Term.ofBranchStrMap`, applied by `Term.condWalk` at every branch).
-/

namespace LeanScript

variable {ks : List Nat} {Δ : DSig ks}

/-! ## Arrays of the keys, of the pairs -/

/-- `m.keysArray` or `m.toArray` for the operand of `List.toArray` when it is `m.keys` or
    `m.toList`, with the fact that it is the array of the operand's elements. -/
def PExpr.strMapListToArray? {Φ : KCtx ks} {Γ : UCtx ks} : {t : Ty ks} → {o : Lvl} →
    (e : PExpr Δ Φ Γ (.list t) o) →
    Option {n : Neu Δ Φ Γ (.array t) (o.getD 0) //
      ∀ κ ρ, (n.eval κ ρ : Array (Ty.Den Δ t)) = List.toArray (e.eval κ ρ)}
  | _, _, .neu (.extern (.strMapExtern (.lean_str_map_keys v)) args h) =>
      some ⟨.extern (.strMapExtern (.lean_str_map_keys_array v)) args h, fun κ ρ => by
        simp only [PExpr.eval, Neu.eval, Extern.eval, StrMapExtern.eval]
        exact Std.HashMap.toArray_keys.symm⟩
  | _, _, .neu (.extern (.strMapExtern (.lean_str_map_to_list v)) args h) =>
      some ⟨.extern (.strMapExtern (.lean_str_map_to_array v)) args h, fun κ ρ => by
        simp only [PExpr.eval, Neu.eval, Extern.eval, StrMapExtern.eval]
        exact Std.HashMap.toArray_toList.symm⟩
  | _, _, _ => none

/-- The neutral expression `m.keysArray` or `m.toArray` when `n` is `Array.mk m.keys` or
    `Array.mk m.toList`, with the fact that they have the same value. -/
def Neu.strMapArray? {Φ : KCtx ks} {Γ : UCtx ks} : {τ : Ty ks} → {ℓ : Nat} →
    (n : Neu Δ Φ Γ τ ℓ) → Option {n' : Neu Δ Φ Γ τ ℓ // ∀ κ ρ, n'.eval κ ρ = n.eval κ ρ}
  | _, ℓ, .extern (.preludeExtern (.lean_array_mk _)) (.cons (o₁ := o₁) a .nil) h =>
    match a.strMapListToArray? with
    | some m =>
      have hl : o₁.getD 0 = ℓ := by rw [Lvl.meet_none] at h; subst h; rfl
      some ⟨hl ▸ m.1, fun κ ρ => by
        revert h; subst hl; intro h
        simp only [Neu.eval, Args.eval, Extern.eval, PreludeExtern.eval]
        exact m.2 κ ρ⟩
    | none => none
  | _, _, _ => none

/-- **`List.toArray` of the keys or of the pairs of a map**, `Array.mk m.keys` or
    `Array.mk m.toList`, as `m.keysArray` or `m.toArray` (otherwise the expression is kept). -/
def Neu.normStrMapArray {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (n : Neu Δ Φ Γ τ ℓ) : Neu Δ Φ Γ τ ℓ :=
  match n.strMapArray? with
  | some m => m.1
  | none => n

theorem Neu.normStrMapArray_eval {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {ℓ : Nat}
    (n : Neu Δ Φ Γ τ ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    n.normStrMapArray.eval κ ρ = n.eval κ ρ := by
  unfold Neu.normStrMapArray
  split
  · rename_i m _; exact m.2 κ ρ
  · rfl

/-! ## Tests of a key -/

/-- `c ? b : a` on Boolean literals, `c` itself when `b` is `true` and `a` is `false`. -/
def Neu.strMapCond {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ) :
    Bool → Bool → Neu Δ Φ Γ .bool ℓ
  | true, false => c
  | b, a => (Neu.cond c (.lit .bool b) (.lit .bool a) : Neu Δ Φ Γ .bool (Lvl.meetL ℓ none))

theorem Neu.strMapCond_eval {Φ : KCtx ks} {Γ : UCtx ks} {ℓ : Nat} (c : Neu Δ Φ Γ .bool ℓ)
    (b a : Bool) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ) :
    ((c.strMapCond b a).eval κ ρ : Bool) = _root_.cond (c.eval κ ρ : Bool) b a := by
  have key : ∀ (x y : Bool), ((Neu.cond c (.lit .bool x) (.lit .bool y) :
      Neu Δ Φ Γ .bool (Lvl.meetL ℓ (Lvl.meet none none))).eval κ ρ : Bool) =
      _root_.cond (c.eval κ ρ : Bool) x y := by
    intro x y
    simp only [Neu.eval]
    split <;> rename_i h <;> simp only [h, PExpr.eval] <;> rfl
  cases b <;> cases a
  · exact key false false
  · exact key false true
  · show (c.eval κ ρ : Bool) = _root_.cond (c.eval κ ρ : Bool) true false
    cases (c.eval κ ρ : Bool) <;> rfl
  · exact key true true

/-- `m.contains k ? b : a` is the case analysis of `m[k]?` whose arms answer `a` (`none`) and
    `b` (`some _`) (`Std.HashMap.isSome_getElem?_eq_contains`). -/
theorem Extern.eval_strMap_contains_cond (E : Ref ks → Type) (v : Ty ks)
    (p : DenList E [.strMap v, .prim .string]) (a b : Bool) :
    _root_.cond (Extern.eval E (.strMapExtern (.lean_str_map_contains v)) p : Bool) b a =
      Ctor.twoCase (E := E) .nullary (.fields (.one v))
        (Extern.eval E (.strMapExtern (.lean_str_map_get_opt v)) p) (fun _ => a) (fun _ => b) := by
  obtain ⟨m, k⟩ := p
  change Std.HashMap String (Ty.den E v) at m
  change String at k
  show _root_.cond (m.contains k) b a =
    Ctor.twoCase (E := E) .nullary (.fields (.one v)) (m.get? k) (fun _ => a) (fun _ => b)
  rw [← Std.HashMap.isSome_getElem?_eq_contains, ← Std.HashMap.get?_eq_getElem?]
  generalize m.get? k = o
  cases o <;> rfl

/-- The answer `m.contains k ? b : a` when the branch is the case analysis of `m[k]?` whose arms
    answer the Boolean literals `a` (`none`) and `b` (`some _`), with the fact that it has the
    same value and no more calls. -/
def Branch.strMapTest? {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {js : JCtx ks} :
    {τ : Ty ks} → {ℓ : Nat} → (br : Branch Δ d Φ Γ τ js ℓ) →
    Option {t : Term Δ d Φ Γ τ js (some ℓ) //
      (∀ κ ρ jκ, t.eval κ ρ jκ = br.eval κ ρ jκ) ∧ t.numCalls = br.numCalls}
  | _, _, .union_casesOn (.extern (.strMapExtern (.lean_str_map_get_opt v)) args h)
      (.two _ _ t₁ t₂) =>
    match t₁, t₂ with
    | .ret (.lit .bool a), .ret (.lit .bool b) =>
      some ⟨.ret (.neu ((Neu.extern (.strMapExtern (.lean_str_map_contains v)) args h).strMapCond
          b a)), fun κ ρ jκ => by
        simp only [Term.eval, PExpr.eval, Branch.eval, Branches.eval]
        refine (Neu.strMapCond_eval _ b a κ ρ).trans ?_
        simp only [Neu.eval]
        exact Extern.eval_strMap_contains_cond _ v (args.eval κ ρ) a b, rfl⟩
    | _, _ => none
  | _, _, _ => none

/-- **A test of a key** (`Branch.strMapTest?`) as the answer `m.contains k ? b : a`; any other
    branch is kept. -/
def Term.ofBranchStrMap {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks} {js : JCtx ks}
    {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) : Term Δ d Φ Γ τ js (some ℓ) :=
  match br.strMapTest? with
  | some t => t.1
  | none => .branch br

theorem Term.ofBranchStrMap_eval {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) (κ : KEnv Δ Φ) (ρ : UEnv Δ Γ)
    (jκ : JEnv Δ τ js) : (Term.ofBranchStrMap br).eval κ ρ jκ = br.eval κ ρ jκ := by
  unfold Term.ofBranchStrMap
  split
  · rename_i t _; exact t.2.1 κ ρ jκ
  · rfl

theorem Term.numCalls_ofBranchStrMap {d : Nat} {Φ : KCtx ks} {Γ : UCtx ks} {τ : Ty ks}
    {js : JCtx ks} {ℓ : Nat} (br : Branch Δ d Φ Γ τ js ℓ) :
    (Term.ofBranchStrMap br).numCalls = br.numCalls := by
  unfold Term.ofBranchStrMap
  split
  · rename_i t _; exact t.2.2
  · rfl

end LeanScript

end
