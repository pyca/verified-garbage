module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SubgroupCTState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QBuild
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SourceFrame
import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Subgroup

/-! # Hash and shape the subgroup candidate before the native primality call -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem subgroup_candidate_ready (H : GenerationHashes) {n : Nat}
    {p : SubgroupPublic} {s : State} (h : SubgroupBefore n p s) :
    WP isa (qCandidate H.sha1 H.sha256) s fun t =>
      PrimeFrameInputs p.call t ∧ Scr t p.plan.prime.B p.plan.prime.Z := by
  obtain ⟨W, hw, hs, _, hwr⟩ := h
  let q := p.plan.withWords W hw
  have plen : p.plan.prime.len ≤ 32 := by rcases p.plan.width with h | h <;> omega
  obtain ⟨V, R⟩ := hs.rep
  have candidate := qCandidate_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
    H.width1 H.width256 p.plan.width hs.layout R hs.label q.outputSlot hs.outputWrite
    (fun i hi j hj => ?_) p.plan.outputHash
  case refine_1 =>
    have he := p.plan.outputHash.scratch j hj (oDig + i) (by unfold oDig oRsa; omega)
    simpa only [off_off, SubgroupPlan.withWords, q] using Ne.symm he
  dsimp only [q, SubgroupPlan.withWords] at candidate
  refine WP.mono candidate fun t ⟨tq, rd, wr, _, ff, L, V', R'⟩ => ?_
  have bt : Spec.Rsa.bytesAt t.mem p.plan.output p.plan.prime.len =
      Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N := by
    have se : Spec.Rsa.bytesAt s.mem p.plan.seedPtr p.plan.prime.len = p.plan.seed := hs.seed
    rw [tq, se]
    exact congrArg (Spec.Dsa.encodeBE p.plan.prime.len) p.plan.modulus.symm
  refine ⟨?_, hs.scratch.congr wr⟩
  refine ⟨L.rsp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wr.trans hwr, hs.usedBound⟩
  · intro k hk
    exact L.ld (by unfold frameBytes; omega)
  · exact (R'.fr 5 (by decide)).trans (hw 5 (by simp))
  · exact (R'.fr 13 (by decide)).trans q.tapePtr
  · exact (R'.fr 15 (by decide)).trans q.tapeLength
  · exact (R'.fr 16 (by decide)).trans hs.usedSlot
  · exact source_of_frame hs.tape ff p.plan.tapeHash p.plan.prime.randMax rd wr
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < p.plan.prime.len := by
        simpa only [SubgroupPublic.call, VG.Proof.Dsa.encodeBE_length] using hi
      have w : InRegions t.wr (off p.plan.output i) 1 := by rw [wr]; exact hs.outputWrite i hi'
      obtain ⟨r, hr, hc⟩ := w
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · intro i hi
      simp only [SubgroupPublic.call] at hi ⊢
      change t.mem (off p.plan.output i) = (Spec.Dsa.encodeBE p.plan.prime.len p.plan.prime.N)[i]
      rw [List.getElem_eq_getD (0 : Byte), ← bt]
      have hi' : i < p.plan.prime.len := by
        simpa only [SubgroupPublic.call, VG.Proof.Dsa.encodeBE_length] using hi
      simp [Spec.Rsa.bytesAt, off, List.getD_eq_getElem?_getD, hi']
    · intro i hi
      exact p.plan.outputOutside i (by
        simpa only [SubgroupPublic.call, VG.Proof.Dsa.encodeBE_length] using hi)
  · intro i hi; rw [wr]; exact hs.witnessWrite i hi

end VG.Proof.Dsa.X86_64.Generation
