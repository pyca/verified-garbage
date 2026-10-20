module

public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingABI
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingPublic
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Buffer and stack resources for a complete verification call -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem VerifyingABI.pre {s : State} (h : VerifyingABI s) : VerifyingPre h.input s := by
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj hb
    exact stackWord_read (count := 4) hargs hj (by omega) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans h.used (stackWord_separate (count := 4) h.scratchArgs hj (by omega) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 1 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rsi).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .r9).isLt) h.signatureScratch) h.used
  · exact source_shrink (src_of_region (p := stackArg s 0) (by rw [h.rd]; simp)
      (Nat.le_of_lt (stackArg s 1).isLt) h.digestScratch) h.used

def VerifyingABI.call {s : State} (h : VerifyingABI s) : VerifyingCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.X86_64
