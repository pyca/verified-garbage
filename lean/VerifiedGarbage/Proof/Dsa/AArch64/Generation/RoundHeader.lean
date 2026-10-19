module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.WitnessRound
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
import VerifiedGarbage.Proof.Framework.Omega

/-! The shared round preserves the caller's entropy and policy header words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem round_header_ranges (w j : Nat) (hj : j ∈ [0, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27]) :
    ∀ r ∈ witnessRoundRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  intro r hr
  rcases List.mem_append.mp hr with hm | hk
  · simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    have hj32 : j < 32 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      omega
    rcases hm with rfl | rfl | rfl <;> left <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aXm] <;> omega_arith
  · exact sharedKernel_hdr w j hj r hk

theorem witnessRoundRanges_lt (w : Nat) : ∀ r ∈ witnessRoundRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  rcases List.mem_append.mp hr with hm | hk
  · simp only [witnessMontRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, aAcc, aTmp, aXm, aE] <;> omega_arith
  · apply sharedRoundRanges_lt w r
    simp only [sharedRoundRanges, sharedMidRanges, List.mem_append]
    exact Or.inl (Or.inr hk)

end VG.Proof.Dsa.AArch64.Generation
