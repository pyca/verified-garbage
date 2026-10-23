module

public import VerifiedGarbage.Proof.AesCbc.AArch64.Encrypt.State
import VerifiedGarbage.Proof.Aes.AArch64.Ecb

/-! Final indexed memory agrees with all ciphertext blocks of CBC. -/

@[expose] public section
namespace VG.Proof.AesCbc.AArch64.Encrypt
open VG VG.AArch64 VG.Proof.Aes.AArch64 VG.Proof.Aes.AArch64.Aese

theorem data_done {s₀ : State} {m : Mem}
    (hI : EcbInv s₀.mem m (Dp s₀) (N s₀) (N s₀) (output s₀)) :
    Spec.Cbc.blocksAt m (Dp s₀) (N s₀)=
      Spec.Cbc.encrypt (Spec.Cbc.aesWith (R s₀) (wK s₀)) (iv0 s₀) (blks s₀) := by
  have hs := statesAt_of_ecbInv hI
  have he : Spec.Cbc.blocksAt m (Dp s₀) (N s₀)=
      (Spec.Aes.statesAt m (Dp s₀) (N s₀)).map Vector.toList := by
    simp only [Spec.Cbc.blocksAt,Spec.Aes.statesAt,List.map_map,Function.comp_def]
    exact List.map_congr_left fun _ _ => bytesAt_toList _ _
  rw [he,hs,List.map_map]
  have hp := (chain_blocks s₀ (N s₀) (Nat.le_refl _)).1
  rw [outK,List.take_of_length_le (by rw [length_blocksAt])] at hp
  exact hp.symm
end VG.Proof.AesCbc.AArch64.Encrypt
