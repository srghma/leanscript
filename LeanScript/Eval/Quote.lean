module

public import Lean.ToExpr
public import LeanScript.Expr.Term
public import LeanScript.Eval.Extern

@[expose] public section

set_option autoImplicit false

/-!
# Writing a computed value back as a term

An extern called on values is a redex when its result type is `LeanScript.TyWf.quotable`
(`LeanScript.Expr.Quotable`): the translation computes the value where the term is
written and writes the value instead of the call.  `Ty.quote` is the half of that which
reads a value of the language: it describes the term that denotes the value as a
`LeanScript.Quoted`, a small tree whose leaves are the payloads of literals as
`Lean.Expr`s.  The translation runs it (compiled) on the value of the call and builds the
term from the tree.

`Ty.quote` answers with a tree for every value of a quotable type
(`LeanScript.Extern.quote_isSome`, proved below), so the translation can always write the
value the grammar asks for.
-/

namespace LeanScript

open Lean

/-- The term that denotes a computed value, as a tree whose leaves are the payloads of
    literals. -/
inductive Quoted where
  /-- The literal constructor `ctor` of the grammar (`Term.nat_mk`, …) applied to the
      payload. -/
  | lit (ctor : Name) (payload : Expr)
  /-- A bit-vector literal of width `w` (`Term.bitvec_mk`). -/
  | bitvec (w : Nat) (payload : Expr)
  /-- The constructor number `i` of an enum (`Term.enum_mk`). -/
  | enum (i : Nat)
  /-- An array of these elements (`Term.array_mk`). -/
  | array (elems : List Quoted)
  /-- A delay of this value: a lazy value (`Term.lazy_mk`) if `lazy`, a thunk
      (`Term.thunk_mk`) otherwise. -/
  | delay (lazy : Bool) (value : Quoted)
  deriving Inhabited

/-- A byte position, as an expression. -/
def quotePosRaw (p : String.Pos.Raw) : Expr :=
  mkApp (mkConst ``String.Pos.Raw.mk) (toExpr p.byteIdx)

/-- The literal of a value of a primitive type, when the type has one that can be written
    from the value alone (`LeanPrimTy.quotable`). -/
def LeanPrimTy.quote : (p : LeanPrimTy) → p.denote → Option Quoted
  | .bool, v => some (.lit ``Term.bool_mk (toExpr v))
  | .nat, v => some (.lit ``Term.nat_mk (toExpr v))
  | .int, v => some (.lit ``Term.int_mk (toExpr v))
  | .bitvec w _, v => some (.bitvec w (toExpr v))
  | .uint8, v => some (.lit ``Term.uint8_mk (toExpr v))
  | .uint16, v => some (.lit ``Term.uint16_mk (toExpr v))
  | .uint32, v => some (.lit ``Term.uint32_mk (toExpr v))
  | .uint64, v => some (.lit ``Term.uint64_mk (toExpr v))
  | .int8, v => some (.lit ``Term.int8_mk (toExpr v))
  | .int16, v => some (.lit ``Term.int16_mk (toExpr v))
  | .int32, v => some (.lit ``Term.int32_mk (toExpr v))
  | .int64, v => some (.lit ``Term.int64_mk (toExpr v))
  | .char, v => some (.lit ``Term.char_mk (toExpr v))
  | .string, v => some (.lit ``Term.string_mk (toExpr v))
  | .stringPosRaw, v => some (.lit ``Term.stringPosRaw_mk (quotePosRaw v))
  | .substringRaw, v => some (.lit ``Term.substringRaw_mk
      (mkApp3 (mkConst ``Substring.Raw.mk) (toExpr v.str) (quotePosRaw v.startPos)
        (quotePosRaw v.stopPos)))
  -- a float is written by its bits, which is exact (a `NaN` keeps its payload)
  | .float, v => some (.lit ``Term.float_mk (mkApp (mkConst ``Float.ofBits) (toExpr v.toBits)))
  | .float32, v =>
      some (.lit ``Term.float32_mk (mkApp (mkConst ``Float32.ofBits) (toExpr v.toBits)))
  | .stringPos _, _ | .stringSlice, _ | .floatModel, _ | .float32Model, _ => none

mutual

/-- The term that denotes a value of type `t`, when `t` is quotable (`Ty.quotable`). -/
def Ty.quote : (t : Ty) → Ty.Den t → Option Quoted
  | .shape s, v => Ty.quoteShape s v
  | _, _ => none

/-- `Ty.quote`, on a node. -/
def Ty.quoteShape : (s : TyShape Ty) → Ty.DenShape s → Option Quoted
  | .prim p, v => p.quote v
  | .enum _, v => some (.enum v.val)
  | .primCovariant c, v => Ty.quoteCov c v
  | _, _ => none

/-- `Ty.quote`, on an array, a thunk or a lazy value. -/
def Ty.quoteCov : (c : LeanPrimTyCovariant Ty) → Ty.DenCov c → Option Quoted
  | .array a, v => (v.toList.mapM (Ty.quote a)).map Quoted.array
  | .thunk a, v => (Ty.quote a v).map (Quoted.delay false)
  | .lazy a, v => (Ty.quote a v).map (Quoted.delay true)

end

/-- The term that denotes a value of type `τ`, when `τ` is quotable (`TyWf.quotable`). -/
def TyWf.quote (τ : TyWf) (v : τ.Den) : Option Quoted := Ty.quote τ.toTy v

/-- The term that denotes the value of an extern called on values, when its result type
    is quotable. -/
def Extern.quote {τ : TyWf} (e : Extern τ) : Option Quoted :=
  TyWf.quote τ (Extern.eval e)

/-- The same, for an extern that takes a proof and whose call decides it: nothing where
    the proposition does not hold, and otherwise the term that denotes the value, if
    the result type is quotable. -/
def Extern.quoteChecked {τ : TyWf} (e : Option (Extern τ)) : Option (Option Quoted) :=
  e.map Extern.quote

/-! ## Every value of a quotable type can be written

The translation relies on this: when the grammar asks for the value of an extern on
values (its result type is `TyWf.quotable`), `Ty.quote` always has a term for it. -/

theorem LeanPrimTy.quote_isSome : ∀ (p : LeanPrimTy), p.quotable = true →
    ∀ v : p.denote, (p.quote v).isSome := by
  intro p hp v
  cases p <;> first | rfl | exact absurd hp (by simp [LeanPrimTy.quotable])

theorem List.mapM_option_isSome {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ x ∈ l, (f x).isSome) → (l.mapM f).isSome
  | [], _ => rfl
  | a :: l, h => by
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (List.mem_cons_self ..))
      obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
        (List.mapM_option_isSome f l fun x hx => h x (List.mem_cons_of_mem _ hx))
      simp [List.mapM_cons, hb, hbs]

mutual

theorem Ty.quote_isSome : ∀ (t : Ty), t.quotable = true → ∀ v : Ty.Den t, (Ty.quote t v).isSome
  | .shape s, h, v => Ty.quoteShape_isSome s h v
  | .self, h, _ | .familyMember _, h, _ | .recTaggedUnion _, h, _ | .recObject _, h, _
  | .recAlias _, h, _ | .mutualRecursiveFamily _, h, _ => absurd h (by simp [Ty.quotable])

theorem Ty.quoteShape_isSome : ∀ (s : TyShape Ty), Ty.quotableShape s = true →
    ∀ v : Ty.DenShape s, (Ty.quoteShape s v).isSome
  | .prim p, h, v => LeanPrimTy.quote_isSome p h v
  | .enum _, _, _ => rfl
  | .primCovariant c, h, v => Ty.quoteCov_isSome c h v
  | .fn _ _, h, _ | .record _, h, _ | .taggedUnion _, h, _ =>
      absurd h (by simp [Ty.quotableShape])

theorem Ty.quoteCov_isSome : ∀ (c : LeanPrimTyCovariant Ty), Ty.quotableCov c = true →
    ∀ v : Ty.DenCov c, (Ty.quoteCov c v).isSome
  | .array a, h, v => by
      simp only [Ty.quoteCov, Option.isSome_map]
      exact List.mapM_option_isSome _ _ fun x _ => Ty.quote_isSome a h x
  | .thunk a, h, v => by
      simp only [Ty.quoteCov, Option.isSome_map]; exact Ty.quote_isSome a h v
  | .lazy a, h, v => by
      simp only [Ty.quoteCov, Option.isSome_map]; exact Ty.quote_isSome a h v

end

/-- **The translation can always write the value the grammar asks for**: an extern on
    values whose result type is quotable has a term for its value. -/
theorem Extern.quote_isSome {τ : TyWf} (e : Extern τ) (h : TyWf.quotable τ = true) :
    (Extern.quote e).isSome :=
  Ty.quote_isSome τ.toTy h _

end LeanScript

end
