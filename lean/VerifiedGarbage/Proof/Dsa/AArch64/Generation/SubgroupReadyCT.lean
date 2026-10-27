module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SubgroupCTState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SourceFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate

/-! # Hash and shape the subgroup candidate before the native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Proof.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem subgroup_candidate_ready (H : GenerationHashes)
    {p : SubgroupPublic} {s : State} (h : SubgroupBefore p s) :
    WP isa (qCandidate H.sha1 H.sha256) s fun t =>
      PrimeTestBefore (8 * p.plan.prime.len) p.primeCall t := by
  obtain ⟨W, hw, hs⟩ := h
  let q := p.plan.withWords W hw
  have plen : p.plan.prime.len ≤ 32 := by rcases p.plan.width with h | h <;> omega
  obtain ⟨V, R⟩ := hs.rep
  have candidate := qBuild_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
    H.width1 H.width256 p.plan.width hs.layout R hs.label q.outputSlot hs.outputWrite
    p.plan.outputFrame.symm p.plan.outputScratch
  dsimp only [q, SubgroupPlan.withWords] at candidate
  refine WP.mono candidate fun t ⟨tq, step, ff, L, V', R'⟩ => ?_
  have bt : Spec.Rsa.bytesAt t.mem p.plan.output p.plan.prime.len =
      Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N := by
    have se : Spec.Rsa.bytesAt s.mem p.plan.seedPtr p.plan.prime.len = p.plan.seed := hs.seed
    rw [tq, se]
    exact congrArg (Spec.Dsa.encodeBE p.plan.prime.len) p.plan.modulus.symm
  have hc : Impl.Dsa.AArch64.ProbablePrime.candidate (8 * p.plan.prime.len) = Impl.Dsa.Generation.Layout.q := by
    unfold Impl.Dsa.AArch64.ProbablePrime.candidate
    rcases p.plan.width with hh | hh <;> rw [hh] <;> decide
  have h5 := hw 5 (by simp)
  exact ⟨W, V', {
    layout := L
    rep := R'
    arena := h5
    arenaWrite := by have := hs.arena.congr step.wr; rwa [show q.W 5 = p.plan.W 5 from h5] at this
    tapePtr := q.tapePtr
    tapeLength := q.tapeLength
    usedSlot := hs.usedSlot
    usedBound := hs.usedBound
    tapeSize := p.plan.prime.randMax
    tapeCover := by rw [step.rd, step.wr]; exact hs.tapeCover
    tapeBytes := bytes_of_src (source_of_frame hs.tape ff p.plan.tapeHash p.plan.prime.randMax step.rd step.wr)
    candidate := by
      rw [hc, Nat.mul_div_cancel_left _ (by decide)]
      change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem
        (p.plan.W 5 + BitVec.ofNat 64 Impl.Dsa.Generation.Layout.q) p.plan.prime.len) = p.plan.prime.N
      rw [p.plan.outputPtr, bt, VG.Proof.Dsa.decodeBE_os2ip]
      exact p.plan.encoding
    odd := by
      change p.plan.prime.N % 2 = 1
      rw [p.plan.modulus]
      exact (VG.Proof.Dsa.Generation.qCandidate_shape
        (show 2 ≤ 8 * p.plan.prime.len by rcases p.plan.width with hh | hh <;> omega) p.plan.seed).1
    bitLen := p.plan.bits }⟩

end VG.Proof.Dsa.AArch64.Generation
