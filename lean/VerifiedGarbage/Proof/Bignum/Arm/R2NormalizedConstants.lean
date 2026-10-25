module

public import VerifiedGarbage.Impl.Bignum.Arm.R2Normalized
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.R2TopBit
import VerifiedGarbage.Proof.Bignum.Arm.TopBitMemory
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! The normalized initializer sets R/2 and two without reading scratch contents. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem r2TopBitReady_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (zero : numAt s.mem (State.addr base) w 4 = 0) :
    WP isa (.block r2TopBit) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have arrayFits := Nat.le_trans (array_end_le (w := w) (by decide : 4 < 8)) fits
  have size : 100 ≤ 8 * len := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  refine WP.mono (r2TopBit_ok s h.workspace size (by omega) (by omega) h.ptr header.count
    (header.array 4 (by decide))) ?_
  rintro t ⟨mem, rest⟩
  have outside := writeW32_outside s.mem (State.addr base)
    (d := arrAt w 4 + 8 * w - 4) (0x80000000 : BitVec 32) (by have := h.workspace.nowrap; omega)
  rw [← mem] at outside
  have arrayOutside := outside.mono (show arrAt w 4 ≤ arrAt w 4 + 8 * w - 4 by omega)
    (show arrAt w 4 + 8 * w - 4 + 4 ≤ arrAt w 4 + 8 * w by omega)
  have keeps := outside_array_keeps arrayOutside (len := len) (by have := h.workspace.nowrap; omega)
  have frame := outside_workspace arrayOutside (size := 8 * len) (by omega)
  have fullRest : Rest roundClobbers s t := rest.mono (by decide)
  have ready := h.after_array (by decide : 4 ≠ 0) keeps frame fullRest
    ((rest.gpr .r0 (by decide)).trans h.ptr)
  refine ⟨ready.1, ?_, ready.2, frame, fullRest⟩
  rw [numAt_native, mem]
  exact val32_write_top_bit s.mem (State.addr base) (by omega) (by have := h.workspace.nowrap; omega)
    (by rw [← numAt_native]; exact zero)

theorem r2NormalizedConstants_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa r2NormalizedConstants s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (64 * w - 1) ∧
      w32 t.mem (State.addr base) (arrAt w 7) = 2 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2NormalizedConstants, WP.seq_iff]
  refine WP.mono (smallConst_ok s (o := 4) 0 h (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨ready, zero, _, keeps1, frame1, rest1⟩
  rw [WP.seq_iff]
  refine WP.mono (r2TopBitReady_ok u ready zero) ?_
  rintro v ⟨readyV, top, modV, frameV, restV⟩
  refine WP.mono (smallConst_ok v (o := 7) 2 readyV (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨next, _, two, keeps2, frame2, rest2⟩
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have op0 : Operand 0 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp]
  exact ⟨next, (keeps_array_num keeps2 fits op4 (by decide)).trans top, two,
    (keeps_array_num keeps2 fits op0 (by decide)).trans
      (modV.trans (keeps_array_num keeps1 fits op0 (by decide))),
    frame1.trans (frameV.trans frame2), rest1.trans (restV.trans rest2)⟩

end VG.Proof.Bignum.Arm
