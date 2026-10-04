import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Bytes

/-!
# AES-CCM on ARMv7: words as bytes

Untrusted: everything here is checked by Lean. The bytes (`le4`, least
significant first) of the words the pieces store: a byte-reversed integer
is its big-endian bytes (`le4_rev_ofNat`), and shifts by 16 move two bytes
(`le4_shr16`, `le4_shl16`), which `header` uses for the encodings of the
length of the associated data.
-/

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.Cmac (le4)

theorem le4_eq (a : BitVec 32) :
    le4 a = [a.extractLsb' 0 8, a.extractLsb' 8 8, a.extractLsb' 16 8, a.extractLsb' 24 8] := rfl

theorem le4_rev (a : BitVec 32) : le4 (rev a) = (le4 a).reverse := by
  have e : ∀ k < 4, (rev a).extractLsb' (8 * k) 8 = a.extractLsb' (8 * (3 - k)) 8 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    exact rev_bit _ hk hj
  rw [le4_eq, le4_eq, e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide)]
  rfl

theorem extract_ofNat {i k : Nat} :
    (BitVec.ofNat 32 i).extractLsb' k 8 = BitVec.ofNat 8 (i % 2 ^ 32 / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]

theorem le4_ofNat {i : Nat} (hi : i < 2 ^ 32) : le4 (BitVec.ofNat 32 i) = (Spec.Ccm.be 4 i).reverse := by
  rw [le4_eq, extract_ofNat, extract_ofNat, extract_ofNat,
    extract_ofNat, Nat.mod_eq_of_lt hi]
  simp [Spec.Ccm.be, List.range_succ]

/-- A byte-reversed integer is its big-endian bytes. -/
theorem le4_rev_ofNat {i : Nat} (hi : i < 2 ^ 32) : le4 (rev (BitVec.ofNat 32 i)) = Spec.Ccm.be 4 i := by
  rw [le4_rev, le4_ofNat hi, List.reverse_reverse]

theorem le4_shr16 (a : BitVec 32) : le4 (a >>> 16) = (le4 a).drop 2 ++ Spec.Ccm.zeros 2 := by
  have e : ∀ k < 4, (a >>> 16).extractLsb' (8 * k) 8 =
      if k < 2 then a.extractLsb' (8 * (k + 2)) 8 else 0 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [BitVec.getLsbD_ushiftRight] <;>
      first | rfl | (apply BitVec.getLsbD_of_ge; omega) | (congr 1; omega)
  rw [le4_eq (a >>> 16), e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), le4_eq]
  rfl

theorem le4_shl16 (a : BitVec 32) : le4 (a <<< 16) = Spec.Ccm.zeros 2 ++ (le4 a).take 2 := by
  have e : ∀ k < 4, (a <<< 16).extractLsb' (8 * k) 8 =
      if k < 2 then 0 else a.extractLsb' (8 * (k - 2)) 8 := fun k hk => by
    ext j hj
    simp only [BitVec.getElem_extractLsb']
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp [BitVec.getLsbD_shiftLeft] <;>
      first | rfl | (intro; omega) |
        (rw [decide_eq_true (by omega : 24 + j < 32), decide_eq_false (by omega : ¬ 24 + j < 16)]
         simp only [Bool.true_and, Bool.not_false]; congr 1; omega)
  rw [le4_eq (a <<< 16), e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), le4_eq]
  rfl

end VG.Proof.AesCcm.Arm
