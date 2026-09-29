import RefactorSpec.NumberStrip
import JsTerm.Print.Mini.Basic

/-!
# The JavaScript a `number` literal prints to did not change

`Legacy.numberExpr` is the printer of the removed `NumberForm`.  `numberExpr_eq_legacy` proves
that for every unpacked float whose mantissa is below `2 ^ 53`, the new printer (which matches on
`UnpackedFloat` and spells decimals as a normalised `JSNumber`) builds exactly the syntax tree
the old one built; `numberExpr_ofFloat_eq_legacy` and `numberExpr_ofFloat32_eq_legacy` drop the
hypothesis for the values that actually occur, those of a `Float` or a `Float32`.

(This file is not a `module`: the printer, `JsTerm.Print.Mini.Basic`, is not one.)
-/

namespace MoreJs

open Language.JavaScript.MiniAST (MiniExpr)
open Language.JavaScript (JSNumber)
open Float.Model (UnpackedFloat)

/-- The removed printer of a `number` literal. -/
def Legacy.numberExpr : Legacy.NumberForm → MiniExpr
  | .nan => ident "NaN"
  | .infinity neg => if neg then .unary .minus (ident "Infinity") else ident "Infinity"
  | .negZero => .unary .minus (natNum 0)
  | .int n => intNum n
  | .decimal neg d ex =>
    let num : MiniExpr := .number (.decimal d ex)
    if neg then .unary .minus num else num

namespace RefactorSpec

/-- The printers agree on every unpacked float with a mantissa below `2 ^ 53`. -/
theorem numberExpr_eq_legacy (u : UnpackedFloat)
    (hu : ∀ s m e h, u = .finite s m e h → m < 2 ^ 53) :
    numberExpr (.float u) = Legacy.numberExpr (Legacy.ofUnpacked u) := by
  cases u with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | finite s m e hm =>
    have hlt := hu s m e hm rfl
    simp only [numberExpr, Legacy.ofUnpacked, NumberForm.finiteDecimal]
    cases hv : NumberForm.smallNat? m e with
    | some v =>
      have hv0 := smallNat?_pos hm hv
      cases s
      · simp [Legacy.numberExpr, Legacy.signIsNeg, withSign, intNum, natNum]; omega
      · simp [Legacy.numberExpr, Legacy.signIsNeg, withSign, intNum, natNum]
    | none =>
      obtain ⟨h1, h2⟩ := shortestDecimal_digits_ok m e hm hlt
      have := Legacy.stripZeros_eq _ (shortestDecimal m e).2 h1 h2
      cases s <;> simp [Legacy.numberExpr, Legacy.signIsNeg, withSign, JSNumber.normalize, this]

/-- The printers agree on every double. -/
theorem numberExpr_ofFloat_eq_legacy (f : Float) :
    numberExpr (NumberForm.ofFloat f) = Legacy.numberExpr (Legacy.ofFloat f) :=
  numberExpr_eq_legacy _ fun _ _ _ _ hu => float_mantissa_lt f hu

/-- The printers agree on every `Float32`. -/
theorem numberExpr_ofFloat32_eq_legacy (f : Float32) :
    numberExpr (NumberForm.ofFloat32 f) = Legacy.numberExpr (Legacy.ofFloat32 f) :=
  numberExpr_eq_legacy _ fun _ _ _ _ hu => float32_mantissa_lt f hu

end RefactorSpec

end MoreJs
