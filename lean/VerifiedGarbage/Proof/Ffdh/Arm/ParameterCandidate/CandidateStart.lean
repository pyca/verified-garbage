module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Buffer permissions and separation before the candidate argument snapshot. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

structure CandidateStart (p : CandidateParams) (s : State) : Prop where
  locals : Workspace s s.sp 72
  workspace : Workspace s p.base (8 * p.capacity)
  outputWrite : InRegions s.wr (State.addr p.out) p.length
  usedWrite : InRegions s.wr (State.addr p.usedPtr) 8
  tapeRead : InRegions (s.rd ++ s.wr) (State.addr p.tape) p.bytes.length
  tapeBytes : Spec.Rsa.bytesAt s.mem (State.addr p.tape) p.bytes.length = p.bytes
  stackBelow : 56 ≤ s.sp.toNat
  stackOutput : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.out, p.length⟩
  stackUsed : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.usedPtr, 8⟩
  stackScratch : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  stackTape : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr p.tape, p.bytes.length⟩
  belowOutput : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.out, p.length⟩
  belowUsed : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.usedPtr, 8⟩
  belowScratch : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.base, 8 * p.capacity⟩
  belowTape : (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr p.tape, p.bytes.length⟩

theorem CandidateStart.after_entry {s t : State} {p : CandidateParams} {rs : List Reg}
    (h : CandidateStart p s) (saved : SavedFrame (candidateValues p 0) candidateSlots t)
    (changed : Frame [⟨State.addr s.sp, 72⟩] s.mem t.mem) (rest : Rest rs s t) : CandidateContext p 0 t := by
  refine ⟨saved, h.workspace.congr rest.wr, ?_, ?_, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rest.wr]; exact h.outputWrite
  · rw [rest.wr]; exact h.usedWrite
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · refine (rsa_bytes_frame changed (by have := p.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.stackTape.symm
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.stackOutput
  · rw [rest.sp]; exact h.stackUsed
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackTape
  · rw [rest.sp]; exact h.belowOutput
  · rw [rest.sp]; exact h.belowUsed
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.sp]; exact h.belowTape

end VG.Proof.Ffdh.Arm.ParameterCandidate
