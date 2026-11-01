module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarUpper
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

/-! Native scalar validity combines nonzero and the public domain's upper bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt Operand)

def scalarValidFlag (p : Inputs) (x : Nat) : BitVec 32 := if 0 < x ∧ x < scalarBound p then 1 else 0

theorem scalarRange_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s fun t => Context p slots t ∧
      ArithmeticReady p.base p.len p.w t ∧
      t.gpr .r11 = scalarValidFlag p (numAt s.mem (State.addr p.base) p.w 1) ∧
      (∀ a ∈ [0, 1, 4], numAt t.mem (State.addr p.base) p.w a = numAt s.mem (State.addr p.base) p.w a) ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  rw [VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange, WP.seq_iff]
  refine WP.mono (nonzero_ok s ready op1 (by decide)) ?_
  rintro u ⟨readyU, nonzero, arraysU, frameU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_ok u readyU) ?_
  rintro v ⟨readyV, saved, arraysV, frameV, restV⟩
  have restUV := restU.trans (restV.mono (by simp [roundClobbers]))
  have frameUV := frameU.trans frameV
  have contextV := h.after_workspace frameUV restUV readyV.ptr (fun d hd => (stableSlots_at stable hd).1)
  have modV := ((arraysV 0 (by decide)).trans (arraysU 0 op0 (by decide))).trans modulus
  rw [WP.seq_iff]
  refine WP.mono (scalarUpper_ok v contextV stable h28 h32 h60 readyV modV odd) ?_
  rintro w ⟨_, readyW, upper, arraysW, header, frameW, restW⟩
  rw [arraysV 1 (by decide), arraysU 1 op1 (by decide)] at upper
  refine WP.mono (andFlag_ok w readyW) ?_
  rintro t ⟨⟨flag, memT⟩, restT⟩
  have readyT := readyW.of_mem memT restT ((restT.gpr .r0 (by simp)).trans readyW.ptr)
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [memT]; exact frameUV.trans frameW
  have rest := (restUV.trans restW).trans (restT.mono (by simp [roundClobbers]))
  refine ⟨h.after_workspace frame rest readyT.ptr (fun d hd => (stableSlots_at stable hd).1), readyT, ?_, ?_, frame, rest⟩
  · rw [flag, upper, header, saved, nonzero, andFlags]
    simp only [scalarValidFlag, and_comm]
  · intro a ha
    rw [memT, arraysW a ha, arraysV a (by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl | rfl <;> decide)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact arraysU 0 op0 (by decide)
    · exact arraysU 1 op1 (by decide)
    · exact arraysU 4 op4 (by decide)

end VG.Proof.Ffdh.Arm
