module

public import VerifiedGarbage.Proof.Dsa.X86_64.SigningABI
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningPublic
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The shared signing precondition supplies every machine-level resource -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem SigningABI.pre {s : State} (h : SigningABI s) : SigningPre h.input s := by
  have hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 40⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj hb
    exact stackWord_read (count := 5) hargs hj (by omega) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans h.used (stackWord_separate (count := 5) h.scratchArgs hj (by omega) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 2 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.nonceScratch) h.used
  · exact source_shrink (src_of_region (p := stackArg s 1) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.digestScratch) h.used
  · intro i hi
    exact ⟨_, by rw [h.wr]; simp, contains_byte _ (by change i < 2 * (stackArg s 0).toNat at hi; rw [h.outLength]; exact hi)
      (Nat.le_of_lt (s.gpr .rsi).isLt)⟩
  · intro i hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _
      (by change i < 2 * (stackArg s 0).toNat at hi; rw [h.outLength]; exact hi) (Nat.le_of_lt (s.gpr .rsi).isLt)))

def SigningABI.call {s : State} (h : SigningABI s) : SigningCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.X86_64
