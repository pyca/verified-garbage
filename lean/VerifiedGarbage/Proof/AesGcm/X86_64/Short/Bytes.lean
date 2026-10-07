import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small
import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Aes.Blocks

/-!
# AES-GCM's short path on x86-64: the bytes

Untrusted: everything here is checked by Lean. What the short path's buffers
hold, as the specification's lists: the text XORed with the keystream blocks
at `K` is counter mode (`xb_gctr`), and the buffer `G` (zero blocks, the
additional data and the text each padded, the lengths block) has the blocks
`GHASH` absorbs (`gBlocks`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.WriteBytes
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt blocks inc32 gctr zeros padLen ghashInput ofBytes toBytes)
open VG.Proof.Gcm (xorKs ksByte padded lensBlock)

theorem repeat_inc32_succ (b : Nat) (J : Block) : Nat.repeat inc32 (b + 1) J = Nat.repeat inc32 b (inc32 J) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [Nat.repeat] at ih ⊢; rw [ih]

/-- The `n` bytes at `D` XORed with the keystream at `K`, whose block `b` is
`CIPH(inc₃₂ᵇ⁺¹(J₀))` (`K` is after `K[0]`): counter mode from `inc₃₂(J₀)`. -/
theorem xb_gctr {m : Mem} {D K : Addr} {n : Nat} {ciph : Block → Block} {J : Block}
    (hK : ∀ b, 16 * b < n → blockAt m (K + BitVec.ofNat 64 (16 * b)) = ciph (Nat.repeat inc32 (b + 1) J)) :
    xb m D K n = gctr ciph (inc32 J) (bytesAt m D n) := by
  rw [Proof.Gcm.gctr_eq]
  refine Proof.Gcm.list_ext (by simp [xb, Proof.Gcm.length_xorKs, length_bytesAt]) fun i hi => ?_
  have hin : i < n := by simpa [xb, length_bytesAt] using hi
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [length_bytesAt]; exact hin), Nat.zero_add]
  simp only [xb, List.getD_eq_getElem?_getD, List.getElem?_zipWith, bytesAt, List.getElem?_map,
    List.getElem?_range hin, Option.map_some, Option.getD_some]
  congr 1
  simp only [ksByte]
  rw [← repeat_inc32_succ, ← hK (i / 16) (by omega), Proof.Aes.toBytes_blockAt _ _ (by omega : i % 16 < 16),
    add_ofNat_ofNat, show 16 * (i / 16) + i % 16 = i by omega]

theorem padLen_eq (x : Nat) : padLen x = 16 * nb16 x - x := by simp only [padLen, nb16]; omega

/-- The additional data and the text, each padded to whole blocks, are
`ghashInput` padded. -/
theorem padded_layout (a c : List Byte) :
    a ++ zeros (16 * nb16 a.length - a.length) ++ c ++ zeros (16 * nb16 c.length - c.length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    simp [padded, ghashInput, padLen_eq, zeros, nb16]
  · rw [padded, Proof.Gcm.ghashInput_of_ne hc, padLen_eq, padLen_eq]
    simp only [List.length_append, Proof.Gcm.length_zeros]
    congr 2
    simp only [nb16]; omega

theorem ofBytes_zeros16 : ofBytes (zeros 16) = 0 := by decide

theorem blocks_zeros (k : Nat) : blocks (zeros (16 * k)) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show zeros (16 * (k + 1)) = zeros (16 * k) ++ zeros 16 by
        rw [zeros, zeros, zeros, List.replicate_append_replicate, Nat.mul_succ],
      Proof.Gcm.blocks_append (by simp [Proof.Gcm.length_zeros]), ih,
      Proof.Gcm.blocks_single (Proof.Gcm.length_zeros 16), ofBytes_zeros16, List.replicate_succ']

/-- The blocks of `G`: the zero blocks, those of the additional data and the
text padded, and the lengths block. -/
theorem gBlocks (lead : Nat) (a c : List Byte) :
    blocks (zeros (16 * lead) ++ padded a c ++ lensBlock a.length c.length) =
      List.replicate lead 0 ++ blocks (padded a c) ++ [ofBytes (lensBlock a.length c.length)] := by
  rw [List.append_assoc, Proof.Gcm.blocks_append (by simp [Proof.Gcm.length_zeros]), blocks_zeros,
    Proof.Gcm.blocks_append (Proof.Gcm.length_padded a c),
    Proof.Gcm.blocks_single (Proof.Gcm.length_lensBlock _ _), List.append_assoc]

end VG.Proof.AesGcm.X86_64.Short
