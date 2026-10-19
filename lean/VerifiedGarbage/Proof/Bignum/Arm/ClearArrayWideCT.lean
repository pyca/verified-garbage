module
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.ClearOperandBuffer
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.ClearOperandBufferCT
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # Clearing an extended result array leaks only its public layout -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt)

theorem clearArrayWide_ct {base : BitVec 32} {len w o : Nat} (ho : o < 8) (fit : 128 ≤ 8 * len) :
    RelCT isa (fun s t => ArithmeticReady base len w s ∧ ArithmeticReady base len w t ∧ s.sp = t.sp)
      (clearOperandBuffer (64 + 8 * o)) (fun _ _ => True) := by
  have input (s : State) (h : ArithmeticReady base len w s) :
      ClearOperandBufferInput base (base + BitVec.ofNat 32 (arrAt w o)) (8 * len) (64 + 8 * o) w s := by
    have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
    rw [h.width] at header
    exact ⟨h.workspace, h.ptr, header.count, header.array o ho⟩
  exact (clearOperandBuffer_ct (base := base) (dst := base + BitVec.ofNat 32 (arrAt w o))
    (size := 8 * len) (slot := 64 + 8 * o) (w := w) (by omega) (by omega) (by omega)).mono
    (fun s t h => ⟨input s h.1, input t h.2.1, h.2.2⟩) (fun _ _ _ => trivial)

end VG.Proof.Bignum.Arm
