module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # Bytewise hash-buffer separation from region separation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Impl.RsaOaep.X86_64

theorem bufferSeparate_of_regions {F S ptr : Addr} {len : Nat} (hl : len < 2 ^ 64)
    (hF : (⟨ptr, len⟩ : Region).Disjoint ⟨F, frameBytes⟩)
    (hS : (⟨ptr, len⟩ : Region).Disjoint ⟨S, oRsa⟩) : HashBufferSeparate F S ptr len where
  frame i hi j hj he := hF (off ptr i)
    (Offset.contains_base _ (by omega) (by omega)) (by rw [he]; exact Offset.contains_base _ (by omega) (by unfold frameBytes at hj; omega))
  scratch i hi j hj he := hS (off ptr i)
    (Offset.contains_base _ (by omega) (by omega)) (by rw [he]; exact Offset.contains_base _ (by omega) (by unfold oRsa at hj; omega))

end VG.Proof.Dsa.X86_64.Generation
