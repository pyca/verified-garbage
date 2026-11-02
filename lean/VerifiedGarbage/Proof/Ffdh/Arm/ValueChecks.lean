module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Equal
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Constant-width tests of an operand against zero and one. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem isOne_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (na7 : a ≠ 7) :
    WP isa (VG.Impl.Ffdh.Arm.isOne a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a = 1 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.isOne, WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, one, _, keepsU, frameU, restU⟩
  refine WP.mono (equal_ok u readyU ha (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])) ?_
  rintro t ⟨ready, flag, arraysT, frameT, restT⟩
  rw [one, keeps_array_num keepsU fits ha na7] at flag
  exact ⟨ready, flag, fun q hq nq => (arraysT q hq).trans (keeps_array_num keepsU fits hq nq),
    frameU.trans frameT, restU.trans restT⟩

theorem negateFlag_ok (s : State) :
    WP isa (.block [.dp .eor .r11 .r11 (.imm 1)]) s fun t =>
      (t.gpr .r11 = s.gpr .r11 ^^^ 1 ∧ t.mem = s.mem) ∧ Rest [.r11] s t := by
  refine withRest_all [.r11] ?_ (by rfl) (by rfl)
  ffrun []

theorem nonzero_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (na7 : a ≠ 7) :
    WP isa (VG.Impl.Ffdh.Arm.nonzero a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if 0 < numAt s.mem (State.addr base) w a then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  rw [VG.Impl.Ffdh.Arm.nonzero, WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 h (by decide : 7 < 8) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, one, _, keepsU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (compare_ok u readyU ha.1 (by decide : 7 < 8) ha.2.2 (by decide)) ?_
  rintro v ⟨readyV, less, keepsV, frameV, restV⟩
  refine WP.mono (negateFlag_ok v) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  refine ⟨readyV.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyV.ptr), ?_, ?_, ?_, ?_⟩
  · rw [flag, less, one, keeps_array_num keepsU fits ha na7]
    by_cases hz : numAt s.mem (State.addr base) w a = 0
    · simp [hz]
    · have pos : 0 < numAt s.mem (State.addr base) w a := by omega
      simp [show ¬ numAt s.mem (State.addr base) w a < 1 by omega, pos]
  · intro q hq nq
    rw [memT, keeps_array_num keepsV fits hq hq.2.2, keeps_array_num keepsU fits hq nq]
  · rw [memT]; exact frameU.trans frameV
  · exact restU.trans (restV.trans (restT.mono (by simp [roundClobbers])))

end VG.Proof.Ffdh.Arm
