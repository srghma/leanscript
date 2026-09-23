module

public import LeanScript.Ty.Class
meta import LeanScript.Ty.WfTactic

@[expose] public section

namespace LeanScript

/-!
# The instances the language comes with

The Lean types the language knows about have their model written here, once: the terminal
types, the type formers it has a shape for (`Array`, `Thunk`, `→`), and the handful of
library types whose model is a *decision* rather than a mechanical translation.

Everything else gets its instance from `deriving LeanScriptTyWf`
(`LeanScript.Ty.Deriving`), which builds a type's tree out of the trees of these.

## Why some of these are written by hand

`Ordering` is the example.  Mechanically it is a field-less sum of three constructors, so
a translation would give it `Ty.enum ⟨0, 0⟩` — the constructors numbered `0`, `1`, `2`.
What it should be is the enum numbered from `-1`, so that `lt`, `eq` and `gt` are `-1`,
`0` and `1` and comparison is a subtraction.  Because the answer lives in an instance,
that decision is made **once** and everything that mentions an `Ordering` — every record
with an `Ordering` field, in any module — uses it; there is no second model of `Ordering`
anywhere, and nothing has to know that the model is unusual.
-/

/-! ## Terminal types -/

instance : LeanScriptTyWf Nat := ⟨.prim .nat, by ty_wf⟩
instance : LeanScriptTyWf Int := ⟨.prim .int, by ty_wf⟩
instance : LeanScriptTyWf Bool := ⟨.prim .bool, by ty_wf⟩
instance : LeanScriptTyWf Char := ⟨.prim .char, by ty_wf⟩
instance : LeanScriptTyWf String := ⟨.prim .string, by ty_wf⟩
instance : LeanScriptTyWf UInt8 := ⟨.prim .uint8, by ty_wf⟩
instance : LeanScriptTyWf UInt16 := ⟨.prim .uint16, by ty_wf⟩
instance : LeanScriptTyWf UInt32 := ⟨.prim .uint32, by ty_wf⟩
instance : LeanScriptTyWf UInt64 := ⟨.prim .uint64, by ty_wf⟩
instance : LeanScriptTyWf Int8 := ⟨.prim .int8, by ty_wf⟩
instance : LeanScriptTyWf Int16 := ⟨.prim .int16, by ty_wf⟩
instance : LeanScriptTyWf Int32 := ⟨.prim .int32, by ty_wf⟩
instance : LeanScriptTyWf Int64 := ⟨.prim .int64, by ty_wf⟩
instance : LeanScriptTyWf Float := ⟨.prim .float, by ty_wf⟩
instance : LeanScriptTyWf Float32 := ⟨.prim .float32, by ty_wf⟩
instance : LeanScriptTyWf String.Pos.Raw := ⟨.prim .stringPosRaw, by ty_wf⟩
instance : LeanScriptTyWf Substring.Raw := ⟨.prim .substringRaw, by ty_wf⟩
instance : LeanScriptTyWf String.Slice := ⟨.prim .stringSlice, by ty_wf⟩

/-- `BitVec 0` has one value, so it carries no information and the language erases it;
    the instance is therefore stated at `n + 1`, which is also where the positivity
    condition of `LeanPrimTy.bitvec` is discharged. -/
instance (n : Nat) : LeanScriptTyWf (BitVec (n + 1)) :=
  ⟨.prim (.bitvec (n + 1) (Nat.succ_pos n)), by ty_wf⟩

/-! ## The type formers the language has a shape for -/

instance [LeanScriptTyWf α] : LeanScriptTyWf (Array α) := ⟨.array (tyWfOf α), by ty_wf⟩
instance [LeanScriptTyWf α] : LeanScriptTyWf (Thunk α) := ⟨.thunk (tyWfOf α), by ty_wf⟩

/-- Every function of the language is curried, so `α → β` is one parameter and one
    result. -/
instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α → β) :=
  ⟨.fn (tyWfOf α) (tyWfOf β), by ty_wf⟩

/-! ## Library types

Each of these is the tree `deriving LeanScriptTyWf` would give it, written out here because
the declaration belongs to the core library and cannot carry a `deriving` clause — except
`Ordering`, whose model is a decision (see the header). -/

/-- Constructor `0` (`none`) carries nothing; constructor `1` (`some`) carries the
    value. -/
instance [LeanScriptTyWf α] : LeanScriptTyWf (Option α) :=
  ⟨.taggedUnion (.skip (.here ⟨tyWfOf α, []⟩ [])), by ty_wf⟩

/-- One constructor with two fields. -/
instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α × β) :=
  ⟨.record ⟨tyWfOf α, tyWfOf β, []⟩, by ty_wf⟩

/-- Two constructors, each with one field. -/
instance [LeanScriptTyWf α] [LeanScriptTyWf β] : LeanScriptTyWf (α ⊕ β) :=
  ⟨.taggedUnion (.payloadFirst ⟨tyWfOf α, []⟩ [tyWfOf β] []), by ty_wf⟩

/-- A list is the recursive sum `nil | cons (_ : α) (_ : self)`. -/
instance [LeanScriptTyWf α] : LeanScriptTyWf (List α) :=
  ⟨.recTaggedUnion (.skip (.here ⟨tyWfOf α, [.self]⟩ [])), by ty_wf⟩

/-- `lt`, `eq` and `gt` are `-1`, `0` and `1`: the enum is shifted, which a mechanical
    translation of the declaration would not have done. -/
instance : LeanScriptTyWf Ordering := ⟨.enum ⟨0, -1⟩, by ty_wf⟩

end LeanScript

end
