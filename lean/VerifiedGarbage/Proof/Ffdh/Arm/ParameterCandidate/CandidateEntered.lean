module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateStart
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.EntryContext
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateGuard
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat

/-! Complete candidate execution after reserving the common AAPCS frame. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def candidateEnteredRegions (p : CandidateParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.out, p.length⟩, ⟨State.addr p.usedPtr, 8⟩, ⟨State.addr p.base, 8 * p.capacity⟩,
    ⟨State.addr sp, 72⟩, FrameStack.belowA sp 56]

def candidatePost (p : CandidateParams) (m : Mem) (r : BitVec 32) : Prop :=
  r = BitVec.ofNat 32 (witnessResultStatus (candidateAnswer p)) ∧
  Spec.Rsa.wordsAt m (State.addr p.usedPtr) 1 =
    [BitVec.ofNat 64 (match candidateAnswer p with | none => 0 | some (_, rest) => p.bytes.length - rest.length)] ∧
  Spec.Rsa.bytesAt m (State.addr p.out) p.length =
    (match candidateAnswer p with | some (true, _) => Spec.Rsa.i2osp p.candidate p.length | _ => List.replicate p.length 0)

theorem candidateEntered_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateStart p s) (incoming : CandidateIncoming p s)
    (out : s.gpr .r0 = p.out) (width : s.gpr .r1 = BitVec.ofNat 32 p.length)
    (used : s.gpr .r2 = p.usedPtr) (bits : s.gpr .r3 = BitVec.ofNat 32 p.bits) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.entry,
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)]) s
      (fun t => Frame (candidateEnteredRegions p s.sp) s.mem t.mem ∧ candidatePost p t.mem (t.gpr .r0)) := by
  change WP isa (.seq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) _) s _
  rw [WP.seq_iff]
  refine WP.mono (candidateEntry_ok h.locals incoming out width used bits) ?_
  rintro u ⟨saved, changed, rest⟩
  refine WP.mono (candidateGuard_ok v (h.after_entry saved changed rest)) ?_
  rintro t ⟨status, count, bytes, frame, _⟩
  rw [rest.sp] at frame
  have bodyFrame : Frame (candidateEnteredRegions p s.sp) u.mem t.mem := by
    refine frame.sub ?_
    intro r hr
    simp only [candidateReturnRegions, candidateRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · exact ⟨_, by simp [candidateEnteredRegions], fun _ h => h⟩
    · refine ⟨⟨State.addr s.sp, 72⟩, by simp [candidateEnteredRegions], ?_⟩
      rw [VG.Arm.addr_add (by have := h.locals.nowrap; omega)]
      exact Offset.sub_base _ (by decide : 40 + 28 ≤ 72)
  exact ⟨(changed.mono (by simp [candidateEnteredRegions])).trans bodyFrame, status, count, bytes⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
