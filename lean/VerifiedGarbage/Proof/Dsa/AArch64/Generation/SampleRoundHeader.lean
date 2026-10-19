module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SampleRound
import VerifiedGarbage.Proof.Framework.Omega

/-! A complete witness iteration retains its immutable generation arguments. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64

theorem sampleRound_header_ranges {w j : Nat} (hj : j ∈ [16, 17, 18, 19, 24, 25, 27]) :
    ∀ r ∈ sampleRoundRanges w, 8 * j + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * j := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      have hj32 : j < 32 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      have hj1 : 1 ≤ j := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega
      rcases htest with rfl | rfl
      · left; simp only [slot, hdrBytes, aX]; omega_arith
      · right; simp only [kU]; omega
    · apply round_header_ranges w j ?_ r hrnd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ht
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases ht with rfl | rfl | rfl <;> decide

theorem sampleRoundRanges_le (w : Nat) : ∀ r ∈ sampleRoundRanges w, r.1 + r.2 ≤ slot w 28 := by
  intro r hr
  rcases List.mem_append.mp hr with hm | ht
  · rcases List.mem_append.mp hm with htest | hrnd
    · simp only [testRanges, List.mem_cons, List.not_mem_nil, or_false] at htest
      rcases htest with rfl | rfl <;> simp only [slot, hdrBytes, aX, kU] <;> omega_arith
    · have hh := witnessRoundRanges_lt w r hrnd
      simp only [slot, hdrBytes, aE] at hh ⊢
      omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;>
      simp only [slot, hdrBytes, kI, kElen, kUni, kP, kStat, sFn] <;> omega_arith

end VG.Proof.Dsa.AArch64.Generation
