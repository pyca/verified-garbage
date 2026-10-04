import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448 scalar arithmetic: little-endian bytes as words

Untrusted and target-independent. A buffer of `len` bytes read from word `k`
up is that word and `2^64` times the bytes above it (`words_step`), which is
how the reductions consume their input from the top.
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- The input from word `k` up: that word, and `2^64` times the bytes above
it. -/
theorem words_step (m : Mem) (p : Addr) (len k : Nat) (hk : 8 * (k + 1) ≤ len) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (len - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (len - 8 * (k + 1))) := by
  have e : len - 8 * k = 8 + (len - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (len - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (len - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  rw [e, hs, decodeLE_append, bytesAt_length, hw, ha]

/-- The 57 bytes at `p`: seven words and a byte. -/
theorem decode57 (m : Mem) (p : Addr) :
    decodeLE (bytesAt m p 57) =
      (m.readW (p + BitVec.ofNat 64 0) 64).toNat + 2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 16) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 24) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 32) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 40) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 48) 64).toNat + 2 ^ 64 *
      (m (p + BitVec.ofNat 64 56)).toNat)))))) := by
  have e0 := words_step m p 57 0 (by omega)
  have e1 := words_step m p 57 1 (by omega)
  have e2 := words_step m p 57 2 (by omega)
  have e3 := words_step m p 57 3 (by omega)
  have e4 := words_step m p 57 4 (by omega)
  have e5 := words_step m p 57 5 (by omega)
  have e6 := words_step m p 57 6 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.sub_zero] at e0 e1 e2 e3 e4 e5 e6
  rw [show p = p + BitVec.ofNat 64 0 from (BitVec.add_zero p).symm, e0, e1, e2, e3, e4, e5, e6]
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, decodeLE, BitVec.add_zero,
    Nat.mul_zero, Nat.add_zero]

end VG.Proof.Ed448
