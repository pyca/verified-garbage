module
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block

/-! # One iteration of repeated modular doubling -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem doubleLoopMultiply_ok (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) :
    WP isa doubleLoopMultiply s fun t => DoubleLoopReady base len w c t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [doubleLoopMultiply, WP.seq_iff]
  refine WP.mono (doubleIndices_ok s) ?_
  rintro u ⟨out, scalar, operand, mem, rest⟩
  have ready : DoubleFnReady base len w 4 7 4 u := by
    refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, ?_, out, scalar, operand, ?_, ?_⟩, ?_⟩
    · rw [mem]; exact h.layout
    · rw [mem]; exact h.width
    · exact (rest.gpr .r0 (by decide)).trans h.ptr
    · rw [mem]; exact h.inverse
    · rw [mem]; exact h.operand
    · rw [mem]; exact h.two
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono (doubleFnRestore_ok u ready op4 op7 op4
    (by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead)
    (by rw [rest.sp]; exact h.stackSep)
    (by rw [mem, rest.sp]; exact h.saved)) ?_
  rintro t ⟨bound, value, keeps, frame, keep, ptr⟩
  rw [mem] at bound value keeps frame
  have fullRest := (rest.mono (by decide)).trans keep
  have state := h.after_double bound keeps frame fullRest ptr
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have oldM := keeps_array_num keeps fits
    (show Operand 0 by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
  exact ⟨state, value, oldM, frame, fullRest⟩

theorem doubleLoopBody_ok (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa doubleLoopBody s fun t => DoubleLoopReady base len w (c - 1) t ∧
      numAt t.mem (State.addr base) w 4 =
        (2 * numAt s.mem (State.addr base) w 4) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      t.z = decide (c = 1) ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [doubleLoopBody, WP.seq_iff]
  refine WP.mono (doubleLoopMultiply_ok s h) ?_
  rintro u ⟨ready, value, modulus, frame, rest⟩
  have fits := ready.layout.2.2.1
  have size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  refine WP.mono (doubleCount_ok u ready.workspace size ready.ptr hc hc' ready.counter) ?_
  rintro t ⟨mem, zero, keep⟩
  obtain ⟨state, frameT, number, modT⟩ := ready.after_count mem keep
  exact ⟨state, number.trans value, modT.trans modulus, zero, frame.trans frameT,
    rest.trans (keep.mono (by decide))⟩

end VG.Proof.Bignum.Arm
