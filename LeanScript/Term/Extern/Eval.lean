module

public import LeanScript.Term.Extern.Eval.Core
public import LeanScript.Term.Extern.Eval.UInt
public import LeanScript.Term.Extern.Eval.SInt
public import LeanScript.Term.Extern.Eval.String
public import LeanScript.Term.Extern.Eval.Float
public import LeanScript.Term.Extern.Eval.ArrayStd

@[expose] public section

set_option autoImplicit false

/-!
# The evaluator of the externs

`Extern.eval e v`: the value of the extern `e` (an entry of the catalogue
`LeanInitPureExtern` over the types of the language, `LeanScript.Extern`) on the values `v`
of its arguments — the Lean function the entry stands for.  It takes the family of the
entry apart and hands the entry to the evaluator of its family
(`LeanScript.Term.Extern.Eval.Core`, `.UInt`, `.SInt`, `.String`, `.Float`, `.ArrayStd`).
-/

namespace LeanScript

/-- The value of an extern on the values of its arguments. -/
def Extern.eval {ks : List Nat} (E : Ref ks → Type) {σs : List (Ty ks)} {τ : Ty ks} :
    Extern ks σs τ → DenList E σs → Ty.den E τ
  | .preludeExtern e => PreludeExtern.eval E e
  | .coreExtern e => CoreExtern.eval E e
  | .intBasicExtern e => IntBasicExtern.eval E e
  | .natDivExtern e => NatDivExtern.eval E e
  | .natBitwiseExtern e => NatBitwiseExtern.eval E e
  | .uintBasicAuxExtern e => UIntBasicAuxExtern.eval E e
  | .stringBootstrapExtern e => StringBootstrapExtern.eval E e
  | .utilExtern e => UtilExtern.eval E e
  | .arraySetExtern e => ArraySetExtern.eval E e
  | .arrayBasicExtern e => ArrayBasicExtern.eval E e
  | .metaDefsExtern e => MetaDefsExtern.eval E e
  | .natLog2Extern e => NatLog2Extern.eval E e
  | .intDivModExtern e => IntDivModExtern.eval E e
  | .uint8BasicExtern e => UInt8BasicExtern.eval E e
  | .uint16BasicExtern e => UInt16BasicExtern.eval E e
  | .uint32BasicExtern e => UInt32BasicExtern.eval E e
  | .uint64BasicExtern e => UInt64BasicExtern.eval E e
  | .stringPosRawExtern e => StringPosRawExtern.eval E e
  | .stringDefsExtern e => StringDefsExtern.eval E e
  | .platformExtern e => PlatformExtern.eval E e
  | .stringBasicExtern e => StringBasicExtern.eval E e
  | .stringLengthExtern e => StringLengthExtern.eval E e
  | .int8BasicExtern e => Int8BasicExtern.eval E e
  | .int16BasicExtern e => Int16BasicExtern.eval E e
  | .int32BasicExtern e => Int32BasicExtern.eval E e
  | .int64BasicExtern e => Int64BasicExtern.eval E e
  | .stringPatternExtern e => StringPatternExtern.eval E e
  | .stringSliceExtern e => StringSliceExtern.eval E e
  | .stringModifyExtern e => StringModifyExtern.eval E e
  | .floatExtern e => FloatExtern.eval E e
  | .uintLog2Extern e => UIntLog2Extern.eval E e
  | .sIntFloatExtern e => SIntFloatExtern.eval E e
  | .float32Extern e => Float32Extern.eval E e
  | .sIntFloat32Extern e => SIntFloat32Extern.eval E e
  | .ordStringExtern e => OrdStringExtern.eval E e
  | .arrayStdExtern e => ArrayStdExtern.eval E e

end LeanScript

end
