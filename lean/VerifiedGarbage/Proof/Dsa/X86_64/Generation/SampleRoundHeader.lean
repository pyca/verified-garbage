module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SampleRound
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RoundHeader

/-! # Header slots retained by a complete DSA witness iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum

/-- These slots carry the draw buffer, tape, and check count through an
entire iteration. Counters and the result status are intentionally omitted. -/
theorem sampleRound_header_ranges {w k : Nat}
    (hk : k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 23 ∨ k = 24 ∨ k = 25) :
    ∀ r ∈ sampleRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have hsmall : k < 32 := by omega
  have hne : k ≠ 22 ∧ k ≠ 26 ∧ k ≠ 27 ∧ k ≠ 28 ∧ k ≠ 31 := by omega
  intro r hr
  simp only [sampleRoundRanges, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · left; simp only [slot, hdrBytes]; omega
    · left; simp only [slot, hdrBytes]; omega
    · left; change 8 * k + 8 ≤ 240; omega
  · exact round_header_ranges hsmall hne r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      dsimp only [VG.Impl.RsaKeyGen.X86_64.Candidate.kI, VG.Impl.RsaKeyGen.X86_64.Candidate.kElen,
        VG.Impl.RsaKeyGen.X86_64.Candidate.kUni, VG.Impl.RsaKeyGen.X86_64.Candidate.kP,
        VG.Impl.RsaKeyGen.X86_64.Candidate.kStat, sFn] <;> omega

open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.MillerRabin VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem sampleRoundRanges_le (w : Nat) : ∀ r ∈ sampleRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  simp only [sampleRoundRanges, testRanges, witnessRoundRanges, Caller.callRanges,
    mutRanges, Proof.MillerRabin.Round.extended, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Caller.pad, slot, hdrBytes, aR1, aAcc, aTmp, aXm, kU, kI, kUni, kStat,
    kElen, kP, sFn, Proof.Rsa.Mont.arrAt, Proof.Rsa.Mont.hdrBytes]
  and_intros <;> omega

end VG.Proof.Dsa.X86_64.Generation
