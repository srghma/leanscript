module

public import LeanScript.Term.Extern.Catalogue
import LeanScript.Term.Extern.NameElab

@[expose] public section

set_option autoImplicit false

/-!
# The name of an extern

`externName e` is the name of the entry `e` of the catalogue of externs
(`LeanScript.LeanInitPureExtern`), as written in the catalogue: `lean_nat_add`,
`lean_nat_mod__Nat_mod`, ….  The JavaScript backend chooses the implementation of a call by
this name (`MoreJsTy.Extern`).
-/

namespace LeanScript



/-- The name of an entry of the catalogue of externs. -/
def externName {ks : List Nat} {σs : List (Ty ks)} {τ : Ty ks} : Extern ks σs τ → String
  | .preludeExtern e => (ctor_names% PreludeExtern)[e.ctorIdx]!
  | .coreExtern e => (ctor_names% CoreExtern)[e.ctorIdx]!
  | .intBasicExtern e => (ctor_names% IntBasicExtern)[e.ctorIdx]!
  | .natDivExtern e => (ctor_names% NatDivExtern)[e.ctorIdx]!
  | .natBitwiseExtern e => (ctor_names% NatBitwiseExtern)[e.ctorIdx]!
  | .uintBasicAuxExtern e => (ctor_names% UIntBasicAuxExtern)[e.ctorIdx]!
  | .stringBootstrapExtern e => (ctor_names% StringBootstrapExtern)[e.ctorIdx]!
  | .utilExtern e => (ctor_names% UtilExtern)[e.ctorIdx]!
  | .arraySetExtern e => (ctor_names% ArraySetExtern)[e.ctorIdx]!
  | .arrayBasicExtern e => (ctor_names% ArrayBasicExtern)[e.ctorIdx]!
  | .metaDefsExtern e => (ctor_names% MetaDefsExtern)[e.ctorIdx]!
  | .natLog2Extern e => (ctor_names% NatLog2Extern)[e.ctorIdx]!
  | .intDivModExtern e => (ctor_names% IntDivModExtern)[e.ctorIdx]!
  | .uint8BasicExtern e => (ctor_names% UInt8BasicExtern)[e.ctorIdx]!
  | .uint16BasicExtern e => (ctor_names% UInt16BasicExtern)[e.ctorIdx]!
  | .uint32BasicExtern e => (ctor_names% UInt32BasicExtern)[e.ctorIdx]!
  | .uint64BasicExtern e => (ctor_names% UInt64BasicExtern)[e.ctorIdx]!
  | .stringPosRawExtern e => (ctor_names% StringPosRawExtern)[e.ctorIdx]!
  | .stringDefsExtern e => (ctor_names% StringDefsExtern)[e.ctorIdx]!
  | .platformExtern e => (ctor_names% PlatformExtern)[e.ctorIdx]!
  | .stringBasicExtern e => (ctor_names% StringBasicExtern)[e.ctorIdx]!
  | .stringLengthExtern e => (ctor_names% StringLengthExtern)[e.ctorIdx]!
  | .int8BasicExtern e => (ctor_names% Int8BasicExtern)[e.ctorIdx]!
  | .int16BasicExtern e => (ctor_names% Int16BasicExtern)[e.ctorIdx]!
  | .int32BasicExtern e => (ctor_names% Int32BasicExtern)[e.ctorIdx]!
  | .int64BasicExtern e => (ctor_names% Int64BasicExtern)[e.ctorIdx]!
  | .stringPatternExtern e => (ctor_names% StringPatternExtern)[e.ctorIdx]!
  | .stringSliceExtern e => (ctor_names% StringSliceExtern)[e.ctorIdx]!
  | .stringModifyExtern e => (ctor_names% StringModifyExtern)[e.ctorIdx]!
  | .floatExtern e => (ctor_names% FloatExtern)[e.ctorIdx]!
  | .uintLog2Extern e => (ctor_names% UIntLog2Extern)[e.ctorIdx]!
  | .sIntFloatExtern e => (ctor_names% SIntFloatExtern)[e.ctorIdx]!
  | .float32Extern e => (ctor_names% Float32Extern)[e.ctorIdx]!
  | .sIntFloat32Extern e => (ctor_names% SIntFloat32Extern)[e.ctorIdx]!
  | .ordStringExtern e => (ctor_names% OrdStringExtern)[e.ctorIdx]!

/-- The C symbol of an extern: its name up to the `__` that disambiguates the Lean functions
    sharing one symbol (`lean_nat_mod__Nat_mod` is `lean_nat_mod`). -/
def externSymbol (name : String) : String :=
  (name.splitOn "__").headD name


end LeanScript

end
