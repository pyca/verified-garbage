module
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Scrypt.Contract

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Transfer
open VG VG.Spec.Scrypt
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt.Memory
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)

theorem writeW_xor (w : Nat) (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a (8*w) ^^^ m'.readW b (8*w)) =
      writeBytes m d (xorBytes (bytesAt m' a w) (bytesAt m' b w)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8*w / 8 = w by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

theorem xor_mem (w : Nat) (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : w * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, w * n⟩ ⟨x, w * n⟩) (hdy : Region.Disjoint ⟨d, w * n⟩ ⟨y, w * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k)))).writeW
      (d + BitVec.ofNat 64 (w * k))
      ((writeBytes m d (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k)))).readW
          (x + BitVec.ofNat 64 (w * k)) (8*w) ^^^
        (writeBytes m d (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k)))).readW
          (y + BitVec.ofNat 64 (w * k)) (8*w)) =
      writeBytes m d (xorBytes (bytesAt m x (w * (k + 1))) (bytesAt m y (w * (k + 1)))) := by
  have hwk : w*k+w ≤ w*n := by
    simpa only [Nat.mul_succ] using Nat.mul_le_mul_left w (by omega : k+1 ≤ n)
  have hl : (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k))).length = w * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (w * k), w⟩
      ⟨d, (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (w * k), w⟩
      ⟨d, (xorBytes (bytesAt m x (w * k)) (bytesAt m y (w * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor w, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (w * k)) w)
    (bytesAt m (y + BitVec.ofNat 64 (w * k)) w))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.AArch64.Transfer
