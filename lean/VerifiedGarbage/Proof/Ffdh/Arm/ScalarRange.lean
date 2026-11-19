module

import VerifiedGarbage.Proof.Ffdh.Arm.CheckFlag
public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.ValueChecks
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Ffdh.Arm.QTest
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! ### `Ffdh.Arm.ScalarUpper`, which this module and modules that import it used -/

section

/-! Compare an imported scalar with q when supplied, or with p-1 otherwise. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)

def scalarBound (p : Inputs) : Nat := if p.hasQ = true then p.Q else p.P - 1

theorem scalarUpper_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : Context p slots s) (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.withQ
      (.seq (VG.Impl.Ffdh.Arm.Domain.importAt 6 60 32) (VG.Impl.Bignum.Arm.arrayCompare 1 6))
      (VG.Impl.Ffdh.Arm.belowP 1)) s fun t => Context p slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      t.gpr .r11 = (if numAt s.mem (State.addr p.base) p.w 1 < scalarBound p then 1 else 0) ∧
      (∀ a ∈ [0, 1, 4], numAt t.mem (State.addr p.base) p.w a = numAt s.mem (State.addr p.base) p.w a) ∧
      t.mem.readW (off (State.addr p.base) 136) 32 = s.mem.readW (off (State.addr p.base) 136) 32 ∧
      Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem ∧ VG.Proof.X25519.Arm.Rest roundClobbers s t := by
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op1 : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have size : 256 ≤ 8 * p.len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  rw [VG.Impl.Ffdh.Arm.Domain.withQ, WP.seq_iff]
  refine WP.mono (qTest_ok s h h28 h32) ?_
  rintro u ⟨⟨zero, memU⟩, restU⟩
  have ptrU := (restU.gpr .r0 (by simp)).trans h.ptr
  have contextU := h.of_mem memU restU ptrU
  have readyU := ready.of_mem memU restU ptrU
  refine WP.ite p.hasQ (by simp only [eval, zero, Bool.not_not]) ?_ ?_
  · intro hasQ
    rw [WP.seq_iff]
    refine WP.mono (importAt_ok u 6 60 32 contextU stable h60 h32 readyU (by decide) (by decide)
      (contextU.qBytes hasQ) (by rw [p.qLength hasQ]; have := p.minLength; omega_using [this])
      (by rw [p.qLength hasQ]; exact p.width.2.2.2.1)
      (by change BitVec.ofNat 32 p.k = _; rw [p.qLength hasQ])) ?_
    rintro v ⟨_, readyV, q, keepsV, frameV, restV⟩
    refine WP.mono (compare_ok v readyV (by decide : 1 < 8) (by decide : 6 < 8) (by decide) (by decide)) ?_
    rintro t ⟨readyT, flag, keepsT, frameT, restT⟩
    have frame := frameV.trans frameT
    have rest := restV.trans restT
    have arrays (a : Nat) (ha : a ∈ [0, 1, 4]) :
        numAt t.mem (State.addr p.base) p.w a = numAt u.mem (State.addr p.base) p.w a := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact (keeps_array_num keepsT fits op0 (by decide)).trans (keeps_array_num keepsV fits op0 (by decide))
      · exact (keeps_array_num keepsT fits op1 (by decide)).trans (keeps_array_num keepsV fits op1 (by decide))
      · exact (keeps_array_num keepsT fits op4 (by decide)).trans (keeps_array_num keepsV fits op4 (by decide))
    rw [keeps_array_num keepsV fits op1 (by decide), q, memU] at flag
    rw [memU] at arrays frame
    have header := (keeps_header_readW keepsT size (d := 136) (bits := 32) (by decide)).trans
      (keeps_header_readW keepsV size (d := 136) (bits := 32) (by decide))
    rw [memU] at header
    exact ⟨contextU.after_workspace (by rw [memU]; exact frame) rest readyT.ptr
      (fun d hd => (stableSlots_at stable hd).1), readyT,
      by rw [scalarBound, ite_eq_left hasQ]; exact flag, arrays, header, frame,
      (restU.mono (by simp [roundClobbers])).trans rest⟩
  · intro hasQ
    refine WP.mono (belowP_ok u readyU (by decide : 1 < 8)
      (by rw [memU, modulus]; exact odd)) ?_
    rintro t ⟨readyT, flag, arrays, header, frame, rest⟩
    rw [memU, modulus] at flag
    rw [memU] at header frame arrays
    refine ⟨contextU.after_workspace (by rw [memU]; exact frame) rest readyT.ptr
      (fun d hd => (stableSlots_at stable hd).1), readyT, ?_, ?_, header, frame,
      (restU.mono (by simp [roundClobbers])).trans rest⟩
    · have absent : ¬p.hasQ = true := by rw [hasQ]; decide
      rw [scalarBound, ite_eq_right absent]; exact flag
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact arrays 0 op0 (by decide)
      · exact arrays 1 op1 (by decide)
      · exact arrays 4 op4 (by decide)

end VG.Proof.Ffdh.Arm

end

end

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
