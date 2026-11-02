module

public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.SanitizeModulusCT
import VerifiedGarbage.Proof.Bignum.Arm.ArrayCompare
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! FFDH comparison/copy adapters preserve the prepared RSA modulus. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt arrAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

 theorem layoutReady {s : State} {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) : LayoutFrameReady base len w s :=
  ⟨⟨h.workspace, h.layout, h.width, h.ptr⟩, h.stackRead, h.stackSep, h.saved⟩

theorem compare_ok (s : State) {base : BitVec 32} {len w a b : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8) (hb : b < 8) (na : a ≠ 3) (nb : b ≠ 3) :
    WP isa (VG.Impl.Bignum.Arm.arrayCompare a b) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w b then 1 else 0) ∧
      Keeps (State.addr base) len w 3 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (arrayCompare_ok s (layoutReady h) ha hb na nb) ?_
  rintro t ⟨ready, result, keeps, frame, rest⟩
  exact ⟨(h.after_array (by decide : 3 ≠ 0) keeps frame rest ready.ptr).1, result, keeps, frame, rest⟩

theorem copy_ok (s : State) {base : BitVec 32} {len w o a : Nat}
    (h : ArithmeticReady base len w s) (ho : o < 8) (ha : a < 8) (ho0 : o ≠ 0) :
    WP isa (VG.Impl.Ffdh.Arm.copy o a) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = numAt s.mem (State.addr base) w a ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.copy, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun u moved => WP.block_nil ?_
  have restU : Rest [.r11] s u := moved.rest (by simp)
  have readyU := h.of_mem moved.mem restU ((restU.gpr .r0 (by simp)).trans h.ptr)
  refine WP.mono (selectArray_ok u readyU.workspace readyU.layout readyU.width readyU.ptr
    ho ha ha (by rw [moved.gpr]; decide) readyU.stackRead readyU.stackSep readyU.saved) ?_
  rintro t ⟨_, _, value, outside, frame, restT, ptr⟩
  rw [moved.mem] at value outside frame
  simp only [ite_self] at value
  have keeps := outside_array_keeps outside (len := len) (by have := h.workspace.nowrap; omega)
  have rest : Rest roundClobbers s t := (restU.mono (by simp [roundClobbers])).trans restT
  exact ⟨(h.after_array ho0 keeps frame rest ptr).1, value, keeps, frame, rest⟩

theorem greaterOne_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8) (na3 : a ≠ 3) (na7 : a ≠ 7) (oa : Operand a) :
    WP isa (VG.Impl.Ffdh.Arm.greaterOne a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if 1 < numAt s.mem (State.addr base) w a then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.greaterOne, WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, oneU, _, keepsU, frameU, restU⟩
  have bound : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have inputU := keeps_array_num keepsU bound oa na7
  refine WP.mono (compare_ok u readyU (by decide : 7 < 8) ha (by decide) na3) ?_
  rintro t ⟨ready, result, keepsT, frameT, restT⟩
  rw [oneU, inputU] at result
  exact ⟨ready, result, fun q hq nq =>
    (keeps_array_num keepsT bound hq hq.2.2).trans (keeps_array_num keepsU bound hq nq),
    frameU.trans frameT, restU.trans restT⟩

end VG.Proof.Ffdh.Arm
