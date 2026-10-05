import VerifiedGarbage.Proof.Scrypt.Memory

/-! Byte-level correctness of 128-bit XOR stores used by the SSE2 loops. -/
namespace VG.Proof.Scrypt.Memory
open VG VG.Spec.Scrypt VG.Spec.Pbkdf2
open VG.Proof.Sha256.Stream
theorem writeW_xor128 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 128 ^^^ m'.readW b 128) =
      writeBytes m d (xorBytes (bytesAt m' a 16) (bytesAt m' b 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (128 : Nat) / 8 = 16 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem128 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 16 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩) :
    (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).writeW
      (d + BitVec.ofNat 64 (16 * k))
      ((writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (x + BitVec.ofNat 64 (16 * k)) 128 ^^^
        (writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (y + BitVec.ofNat 64 (16 * k)) 128) =
      writeBytes m d (xorBytes (bytesAt m x (16 * (k + 1))) (bytesAt m y (16 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length = 16 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  -- The words of `x` and `y` are not in the part of `d` written so far.
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [writeW_xor128, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (16 * k)) 16)
    (bytesAt m (y + BitVec.ofNat 64 (16 * k)) 16))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]


end VG.Proof.Scrypt.Memory
