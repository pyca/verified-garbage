module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateStart
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.EntryContext
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Nat
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateReturn
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePairMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ScreenedTests
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateLocalFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateQOdd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCount
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
/-! Complete candidate execution after reserving the common AAPCS frame. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateScreenPair.lean`, which only this module imported.
section

/-! Initialize the RSA table once and screen both moduli at each prime. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenPair_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length ≤ p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate)
    (oddQ : ((p.candidate-1)/2)%2=1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateTable_ok h) ?_)
  rintro u ⟨ctx, table, changed, rest⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytes]
    exact number
  refine WP.seq (WP.mono (candidatePair_ok ctx table numberU oddQ) ?_)
  rintro w ⟨ctxW, tableW, flag, bytesW, changedW, restW⟩
  change w.z=candidateShapes p at flag
  have numberW : Spec.Rsa.os2ip (Spec.Rsa.bytesAt w.mem (State.addr p.out) p.length) = p.candidate := by
    rw [bytesW]
    exact numberU
  by_cases prime : candidateShapes p = true
  · refine WP.seq (WP.ite true (by change some w.z = some true; rw [flag, prime]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (screenedTests_ok v ctxW enough oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, prime]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)
  · have composite : candidateShapes p = false := Bool.eq_false_iff.mpr prime
    refine WP.seq (WP.ite false (by change some w.z = some false; rw [flag, composite]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxW) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_shapes, composite]
    exact (returned.trans_pre (candidate_local_frame ctx (by decide) (by decide) changedW) restW (fun _ h => h)).trans_pre
      (changed.mono (by simp [candidateRegions])) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateScreenP.lean`, which only this module imported.
section

/-! Reject even q before the paired RSA sieve and witness controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateScreenP_ok (v : RoundImpl) {s : State} {p : CandidateParams}
    (h : CandidateContext p p.length s) (enough : p.length≤p.bytes.length)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code) s
      (CandidateReturn p (candidateScreenP p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.screenP VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateQOdd_ok h number) ?_)
  rintro u ⟨ctx,flag,memory,rest⟩
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length)=p.candidate := by
    rw [memory]
    exact number
  by_cases oddQ : ((p.candidate-1)/2)%2=1
  · refine WP.seq (WP.ite true (by change some u.z=some true; rw [flag,decide_eq_true oddQ]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenPair_ok v ctx enough numberU oddQ) ?_
    intro t returned
    refine WP.block_nil ?_
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)
  · refine WP.seq (WP.ite false (by change some u.z=some false; rw [flag,decide_eq_false oddQ]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreenP_even p (by omega)]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateMain.lean`, which only this module imported.
section

/-! The entire candidate body: shape, residue, two sieves, and q/p Miller–Rabin. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateMain_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (enough : p.length ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code) s (CandidateReturn p (candidateScreen p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.main VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (candidateCount_ok h enough) ?_)
  rintro u ⟨ctxU, changedU, restU⟩
  refine WP.seq (WP.mono (candidateShape_ok ctxU enough) ?_)
  rintro w ⟨ctxW, _, numberW, changedW, restW⟩
  refine WP.seq (WP.mono (candidateResidue_ok ctxW numberW) ?_)
  rintro a ⟨ctxA, flag, memoryA, restA⟩
  have numberA : Spec.Rsa.os2ip (Spec.Rsa.bytesAt a.mem (State.addr p.out) p.length) = p.candidate := by
    rw [memoryA]
    exact numberW
  by_cases shape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · refine WP.seq (WP.ite true (by change some a.z = some true; rw [flag, shape]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateScreenP_ok v ctxA enough numberA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, shape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)
  · have badShape : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr shape
    refine WP.seq (WP.ite false (by change some a.z = some false; rw [flag, badShape]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateRejected_ok ctxA) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateScreen, badShape]
    exact ((returned.trans_pre (by rw [memoryA]; exact Frame.refl _ _) restA (fun _ h => h)).trans_pre
      (changedW.mono (by simp [candidateRegions])) restW (fun _ h => h)).trans_pre
      (candidate_local_frame h (by decide) (by decide) changedU) restU (fun _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateGuard.lean`, which only this module imported.
section

/-! Complete candidate control flow, including the short initial entropy tape. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateGuard_ok (v : RoundImpl) {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)]) s
      (CandidateReturn p (candidateAnswer p) s) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (initialRoom_ok h.saved.space p.tapeCount
    (by have := p.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases enough : p.length ≤ p.bytes.length
  · refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false (by omega)]) (by intro h; cases h) ?_)
    intro _
    refine WP.mono (candidateMain_ok v ctx enough) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_left enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])
  · refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true (by omega)]) ?_ (by intro h; cases h))
    intro _
    refine WP.mono (candidateNone_ok ctx) ?_
    intro t returned
    refine WP.block_nil ?_
    rw [candidateAnswer, ite_eq_right enough]
    exact returned.trans_pre (by rw [memory]; exact Frame.refl _ _) rest (by simp [roundClobbers])

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

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
