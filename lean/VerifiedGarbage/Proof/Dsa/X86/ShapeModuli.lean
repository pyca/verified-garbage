module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Impl.Dsa.X86.Shape
public import VerifiedGarbage.Proof.Dsa.Accepted
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86.Shape

/-! # Successful public shape validation establishes the arithmetic invariants -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shapeModuli_ok {s : State} {base : Addr} {size pLen qLen p q : Nat}
    (hs : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen) (Q : CallerBuffer s base size (.input .q) qLen)
    (hp : operandValue s base (.input .p) pLen = p) (hq : operandValue s base (.input .q) qLen = q) :
    WP isa (Shape.check pLen qLen) s fun t =>
      flagW base (Layout.field .mask) t = mask32 (shapeValid p q) ∧
      t.zf = some (!decide (shapeValid p q)) ∧
      (shapeValid p q → Moduli base size pLen qLen p q t ∧
        (pointerValue base t (.input .digestPrefixLen)).toNat =
          min (pointerValue base s (.input .digestLen)).toNat (Spec.Dsa.bitLength q / 8)) ∧
      Keeps shapeClob s t ∧ Outs base shapeRanges s.mem t.mem := by
  have L : 128 ≤ pLen ∧ pLen ≤ 384 ∧ 20 ≤ qLen ∧ qLen ≤ 32 := by
    unfold Spec.Dsa.lengthsValid at widths
    omega
  have sz : 15712 ≤ size := extent
  have ctx : contextBytes 48 ≤ size := by change 7048 ≤ size; omega
  have A : pLen % 4 = 0 ∧ qLen % 4 = 0 := by
    unfold Spec.Dsa.lengthsValid at widths
    omega
  refine WP.mono (shape_ok hs (by change 8256 ≤ size; omega)
    (by omega) (by omega) (by omega) (by omega) A.1 A.2 (P.ready ctx) (Q.ready ctx) hp hq)
    fun t ⟨F, Z, D, K, O⟩ => ?_
  refine ⟨F, Z, ?_, K, O⟩
  intro valid
  have B := VG.Proof.Dsa.supported_bounds valid.1
  refine ⟨⟨hs.of_keeps K (by decide), extent, widths,
    P.keep_shape O K (by decide) (by decide), Q.keep_shape O K (by decide) (by decide),
    (P.value_keep_shape O K (by decide) (by decide) (by omega)).trans hp,
    (Q.value_keep_shape O K (by decide) (by decide) (by omega)).trans hq,
    B.1, B.2.1, valid.2.2, valid.2.1⟩, D valid⟩

end VG.Proof.Dsa.X86
