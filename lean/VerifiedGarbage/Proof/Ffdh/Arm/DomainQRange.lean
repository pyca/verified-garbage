module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Odd
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag

/-! The subgroup order must be odd and strictly inside the modulus range. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand arrAt)

def qRangeFlag (p : Inputs) : BitVec 32 := if 2 < p.Q ∧ p.Q < p.P - 1 ∧ p.Q % 2 = 1 then 1 else 0

theorem qRange_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true) (h60 : 60 ∈ slots) (h32 : 32 ∈ slots)
    (hasQ : p.hasQ = true) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧ t.gpr .r11 = qRangeFlag p ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have qLength := p.qLength hasQ
  rw [VG.Impl.Ffdh.Arm.Domain.CheckDomain.qRange, WP.seq_iff]
  refine WP.mono (importAt_ok s 1 60 32 h stable h60 h32 ready (by decide) (by decide) (h.qBytes hasQ)
    (by rw [qLength]; have := p.minLength; omega) (by rw [qLength]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.k = _; rw [qLength])) ?_
  rintro u ⟨_, readyU, q, keepsU, frameU, restU⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := readyU.width ▸ readyU.layout.2.2.1
  have modU := (keeps_array_num keepsU fits op0 (by decide)).trans modulus
  have r2U := (keeps_array_num keepsU fits op4 (by decide)).trans r2
  rw [WP.seq_iff]
  refine WP.mono (inRange_ok u readyU op1 (by decide) (by rw [modU]; exact odd)) ?_
  rintro v ⟨readyV, range, arraysV, frameV, restV⟩
  rw [q, modU] at range
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok v readyV) ?_
  rintro w ⟨readyW, saved, arraysW, frameW, restW⟩
  rw [WP.seq_iff]
  refine WP.mono (odd_ok w readyW (by decide : 1 < 8)) ?_
  rintro x ⟨readyX, parity, memX, restX⟩
  rw [arraysW 1 (by decide), arraysV 1 op1 (by decide), q] at parity
  refine WP.mono (andFlag_ok x readyX) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  have readyT := readyX.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyX.ptr)
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by
    rw [memT, memX]; exact (frameU.trans frameV).trans frameW
  have rest : VG.Proof.X25519.Arm.Rest roundClobbers s t :=
    (((restU.trans restV).trans (restW.mono (by simp [roundClobbers]))).trans
      (restX.mono (by simp [roundClobbers]))).trans (restT.mono (by simp [roundClobbers]))
  refine ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT, ?_, ?_, ?_, frame, rest⟩
  · rw [flag, parity, memX, saved, range]
    change BitVec.ofNat 32 (p.Q % 2) &&& (if 1 < p.Q ∧ p.Q < p.P - 1 then 1 else 0) = qRangeFlag p
    have small : p.Q % 2 = 0 ∨ p.Q % 2 = 1 := by omega
    rcases small with even | oddQ
    · simp [even, qRangeFlag]
    · rw [oddQ]
      by_cases lower : 1 < p.Q <;> by_cases upper : p.Q < p.P - 1 <;>
        simp [qRangeFlag, lower, upper, oddQ, show (2 < p.Q ↔ 1 < p.Q) by omega]
  · rw [memT, memX, arraysW 0 (by decide), arraysV 0 op0 (by decide)]
    exact modU
  · rw [memT, memX, arraysW 4 (by decide), arraysV 4 op4 (by decide)]
    exact r2U

end VG.Proof.Ffdh.Arm
