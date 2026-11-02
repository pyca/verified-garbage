module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.SetLowBit
import VerifiedGarbage.Proof.Ffdh.Arm.LowBit
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.Checks

/-! Compare against p-1 using full-width, fixed-schedule native operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem belowP_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : a < 8)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.belowP a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0 - 1 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      t.mem.readW (off (State.addr base) 136) 32 = s.mem.readW (off (State.addr base) 136) 32 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  rw [VG.Impl.Ffdh.Arm.belowP, WP.seq_iff]
  refine WP.mono (copy_ok s h (by decide : 7 < 8) ha (by decide)) ?_
  rintro u ⟨readyU, valueU, keepsU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (setLowBit_ok u readyU) ?_
  rintro v ⟨readyV, valueV, keepsV, frameV, restV⟩
  have arraysUV (q : Nat) (hq : Operand q) (nq : q ≠ 7) :=
    (keeps_array_num keepsV fits hq nq).trans (keeps_array_num keepsU fits hq nq)
  refine WP.mono (compare_ok v readyV (by decide : 7 < 8) (by decide : 0 < 8) (by decide) (by decide)) ?_
  rintro t ⟨ready, flag, keepsT, frameT, restT⟩
  refine ⟨ready, ?_, ?_, ?_, frameU.trans (frameV.trans frameT), restU.trans (restV.trans restT)⟩
  · rw [valueV, valueU, arraysUV 0 (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)] at flag
    simp only [belowOdd _ _ odd] at flag
    exact flag
  · intro q hq nq
    exact (keeps_array_num keepsT fits hq hq.2.2).trans (arraysUV q hq nq)
  · exact (keeps_header_readW keepsT size (d := 136) (bits := 32) (by decide)).trans
      ((keeps_header_readW keepsV size (d := 136) (bits := 32) (by decide)).trans
        (keeps_header_readW keepsU size (d := 136) (bits := 32) (by decide)))

end VG.Proof.Ffdh.Arm
