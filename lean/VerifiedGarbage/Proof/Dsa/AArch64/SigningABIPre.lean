module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningABI
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningPublic
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared signing precondition supplies every machine-level resource -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningABI.pre {s : State} (h : SigningABI s) : SigningPre h.input s := by
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 24⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj
    exact stackWord_read (count := 3) hargs (by omega) (by decide)
  · intro i hi
    simpa only [Nat.mul_zero, off_zero, SigningABI.input] using Nat.le_trans h.used (stackWord_separate (count := 3) (j := 0) h.scratchArgs (by decide) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 0 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x3).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x6).isLt) h.nonceScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x7) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.digestScratch) h.used
  · intro i hi
    exact ⟨_, by rw [h.wr]; simp, contains_byte _ (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi)
      (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro i hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _
      (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi) (Nat.le_of_lt (s.gpr .x1).isLt)))

def SigningABI.call {s : State} (h : SigningABI s) : SigningCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64
