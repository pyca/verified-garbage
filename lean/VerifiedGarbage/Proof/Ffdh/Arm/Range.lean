module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.BelowP
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! All FFDH value ranges are checked without secret-dependent iteration. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem andFlag_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.andFlag) s fun t =>
      (t.gpr .r11 = s.gpr .r11 &&& s.mem.readW (off (State.addr base) 136) 32 ∧ t.mem = s.mem) ∧
      Rest [.r3, .r11] s t := by
  have size : 256 ≤ 8 * len := by
    have := h.layout.2.2.1
    simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at this
    omega
  have addr : State.addr (base + BitVec.ofNat 32 136) = off (State.addr base) 136 :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  have read := h.workspace.read (off := 136) (by omega)
  refine withRest_all [.r3, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.andFlag
  ffrun [h.ptr, addr, read, off]

theorem andFlags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0) : BitVec 32) &&& (if q then 1 else 0) =
      (if p ∧ q then 1 else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem inRange_ok (s : State) {base : BitVec 32} {len w a : Nat}
    (h : ArithmeticReady base len w s) (ha : Operand a) (na7 : a ≠ 7)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.inRange a) s fun t => ArithmeticReady base len w t ∧
      t.gpr .r11 = (if 1 < numAt s.mem (State.addr base) w a ∧
        numAt s.mem (State.addr base) w a < numAt s.mem (State.addr base) w 0 - 1 then 1 else 0) ∧
      (∀ q, Operand q → q ≠ 7 → numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.inRange, WP.seq_iff]
  refine WP.mono (greaterOne_ok s h ha.1 ha.2.2 na7 ha) ?_
  rintro u ⟨readyU, lower, arraysU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok u readyU) ?_
  rintro v ⟨readyV, saved, arraysV, frameV, restV⟩
  have arraysUV (q : Nat) (hq : Operand q) (nq : q ≠ 7) :=
    (arraysV q hq.1).trans (arraysU q hq nq)
  have oddV : numAt v.mem (State.addr base) w 0 % 2 = 1 := by
    rw [arraysUV 0 op0 (by decide)]; exact odd
  rw [WP.seq_iff]
  refine WP.mono (belowP_ok v readyV ha.1 oddV) ?_
  rintro z ⟨readyZ, upper, arraysZ, headerZ, frameZ, restZ⟩
  refine WP.mono (andFlag_ok z readyZ) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  refine ⟨readyZ.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyZ.ptr), ?_, ?_, ?_, ?_⟩
  · rw [flag, upper, headerZ, saved, lower, arraysUV a ha na7, arraysUV 0 op0 (by decide), andFlags]
    simp only [and_comm]
  · intro q hq nq
    rw [memT, arraysZ q hq nq, arraysUV q hq nq]
  · rw [memT]; exact frameU.trans (frameV.trans frameZ)
  · exact restU.trans ((restV.mono (by simp [roundClobbers])).trans
      (restZ.trans (restT.mono (by simp [roundClobbers]))))

end VG.Proof.Ffdh.Arm
