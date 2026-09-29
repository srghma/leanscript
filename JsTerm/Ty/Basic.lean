module

public import JsTerm.Ty.Defs
public import JsTerm.Ty.DecEq

@[expose] public section

set_option autoImplicit false

/-!
# The types of `JsTerm`: names, renderings and array layouts

The types themselves (`JsTerminalTy`, `JsTy`, the typed arrays) are in `JsTerm.Ty.Defs`, their
decidable equality in `JsTerm.Ty.DecEq`.  This module adds the names of the leaves (as the
names of the operations spell them), the renderings of the `-JsTerm-*.txt` dump, and the two
layouts of the operations' signatures: `JsNatTy` (the loop counters) and `JsArrayLayout`
(generic or typed arrays).
-/

namespace MoreJs

open LeanScript

instance : Coe JsTerminalTy JsTy := ⟨JsTy.terminal⟩

namespace JsTerminalTy

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTerminalTy → Bool
  | .bigint_nat | .bigint_int | .bigint_bitvec_big .. => true
  | _ => false

/-- The name of the leaf, as the names of the operations spell it (`bigint_nat`,
    `uint53`, `bitvec32`, …). -/
def name : JsTerminalTy → String
  | .bool => "bool" | .bigint_nat => "bigint_nat" | .uint53 => "uint53"
  | .bigint_int => "bigint_int" | .int53 => "int53"
  | .bitvec_small n _ _ => s!"bitvec{n}"
  | .bigint_bitvec_big n _ => s!"bigint_bitvec{n}"
  | .int53_bitvec_big n _ => s!"int53_bitvec{n}"
  | .uint8 => "uint8" | .uint16 => "uint16" | .uint32 => "uint32"
  | .int8 => "int8" | .int16 => "int16" | .int32 => "int32"
  | .float => "float" | .float32 => "float32"
  | .string => "string" | .substring => "substring" | .stringSlice => "stringSlice"

/-- A rendering for the `-JsTerm.txt` dump. -/
def pretty : JsTerminalTy → String
  | .bool => "boolean"
  | .bigint_nat => "nat(bigint)"
  | .uint53 => "uint53(number)"
  | .bigint_int => "int(bigint)"
  | .int53 => "int53(number)"
  | .bitvec_small n _ _ => s!"bitvec{n}(number)"
  | .bigint_bitvec_big n _ => s!"bitvec{n}(bigint)"
  | .int53_bitvec_big n _ => s!"bitvec{n}(number)"
  | t => t.name

end JsTerminalTy

namespace JsTypedArray

/-- The JavaScript constructor of the typed array. -/
def ctorName : JsTypedArray → String
  | .uint8Array => "Uint8Array" | .uint16Array => "Uint16Array"
  | .uint32Array => "Uint32Array" | .int8Array => "Int8Array" | .int16Array => "Int16Array"
  | .int32Array => "Int32Array" | .float32Array => "Float32Array"
  | .float64Array => "Float64Array" | .bigUint64Array => "BigUint64Array"
  | .bigInt64Array => "BigInt64Array"

end JsTypedArray

/-- The two representations of a natural number that count the iterations of a loop. -/
inductive JsNatTy : JsTy → Type where
  | bigint_nat : JsNatTy (.terminal .bigint_nat)
  | uint53 : JsNatTy (.terminal .uint53)
  deriving Repr

/-- The natural-number representation of a type, if it is one. -/
def JsNatTy.of? : (t : JsTy) → Option (JsNatTy t)
  | .terminal .bigint_nat => some .bigint_nat
  | .terminal .uint53 => some .uint53
  | _ => none

/-- How an array type is laid out: a generic array of elements `α`, or a typed array whose
    elements are read as the leaf of `t`. -/
inductive JsArrayLayout : JsTy → JsTy → Type where
  | generic (α : JsTy) : JsArrayLayout (.array α) α
  | typed (t : JsTypedElem) : JsArrayLayout (.typedArray t) (.terminal t.leaf)
  deriving Repr

/-- The layout of an array type, if it is one. -/
def JsArrayLayout.of? : (a : JsTy) → Option (Σ e, JsArrayLayout a e)
  | .array α => some ⟨α, .generic α⟩
  | .typedArray t => some ⟨.terminal t.leaf, .typed t⟩
  | _ => none

/-- The element type of an array layout is determined by the array type. -/
theorem JsArrayLayout.elem_unique {a e₁ e₂ : JsTy} :
    JsArrayLayout a e₁ → JsArrayLayout a e₂ → e₁ = e₂
  | .generic _, .generic _ => rfl
  | .typed _, .typed _ => rfl

namespace JsTy

/-- Is a value of this type a `BigInt` at run time? -/
def isBigInt : JsTy → Bool
  | .terminal t => t.isBigInt
  | _ => false

/-- The name of declaration `i` of a signature, as a JavaScript type name. -/
def declName (i : Nat) : String := s!"D{i}"

/-- A rendering for the `-JsTerm-*.txt` dump and the JSDoc comments. -/
partial def pretty : JsTy → String
  | .terminal t => t.pretty
  | .array t => s!"Array<{t.pretty}>"
  | .typedArray t => s!"{t.kind.ctorName}<{t.leaf.pretty}>"
  | .list t => s!"List<{t.pretty}>"
  | .fn ds c => "(" ++ ", ".intercalate (ds.map pretty) ++ s!") => {c.pretty}"
  | .enum n shift => s!"enum{n}@{shift}"
  | .thunk t => s!"Thunk<{t.pretty}>"
  | .obj (.record _) ts => "{ " ++ ", ".intercalate
      ((List.range ts.length).zip ts |>.map fun (i, t) => s!"_{i + 1}: {t.pretty}") ++ " }"
  | .obj (.union ar r) args => let cs := splitArities ar args; "(" ++ " | ".intercalate
      ((List.range cs.length).zip cs |>.map fun (i, fs) =>
        if r == .smallIntNullary && fs.isEmpty then toString i else
        "{ " ++ ", ".intercalate (s!"tag: {i}" ::
          ((List.range fs.length).zip fs |>.map fun (j, t) => s!"_{j + 1}: {t.pretty}")) ++ " }") ++ ")"
  | .obj .consList [t] => s!"ConsList<{t.pretty}>"
  | .obj .consList ts => "ConsList<" ++ ", ".intercalate (ts.map pretty) ++ ">"
  | .obj (.decl i) [] => declName i
  | .obj (.decl i) ts => declName i ++ "<" ++ ", ".intercalate (ts.map pretty) ++ ">"

instance : ToString JsTy := ⟨pretty⟩

end JsTy

end MoreJs

end
