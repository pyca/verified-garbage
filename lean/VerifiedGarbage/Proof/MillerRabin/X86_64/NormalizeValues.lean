module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize

/-! # Normalized bookkeeping depends only on the public limb count -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.Proof.Bignum VG.Impl.Bignum
open VG.Impl.MillerRabin.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate

theorem normalized_values (m : Mem) (B : Addr) (w : Nat) :
    ∀ j ∈ bookkeeping.map (·.1),
      word (normalizedMem m B w) B (8 * j) =
        if j = kLen ∨ j = kUsed then BitVec.ofNat 64 (8 * w) else 0#64 := by
  simp only [bookkeeping, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  rintro j (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals
    simp only [normalizedMem, zeroWords, List.foldl_cons, List.foldl_nil]
    repeat first
      | rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
      | rw [word_writeW_self]
    simp [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kE, kI, kElen, kUsed, sFn]

end VG.Proof.MillerRabin.X86_64
