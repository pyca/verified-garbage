module

public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.AArch64.VerifyingPublic
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Buffer and stack resources for a complete verification call -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem VerifyingABI.pre {s : State} (h : VerifyingABI s) : VerifyingPre h.input s := by
  have hs : Scr s (stackArg s 0) ((stackArg s 1).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 16⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · simpa only [Nat.mul_zero, off_zero] using stackWord_read (count := 2) (j := 0) hargs (by decide) (by decide)
  · exact (ofNat_toNat64 _).symm
  · change s.gpr .x7 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x1).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x5).isLt) h.signatureScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x6) (by rw [h.rd]; simp)
      (Nat.le_of_lt (s.gpr .x7).isLt) h.digestScratch) h.used

def VerifyingABI.call {s : State} (h : VerifyingABI s) : VerifyingCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64
