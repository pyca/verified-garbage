import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop

/-!
# Ed448 on x86-64: 57-byte strings as words

The number of 57 bytes in memory as seven words and a byte (`decode57`), as
the code that prunes a hash into a scalar reads it.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64

/-- The 57 bytes at `p`: seven words and a byte. -/
theorem decode57 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 57) =
      (m.readW p 64).toNat + 2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 8) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 16) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 24) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 32) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 40) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 48) 64).toNat + 2 ^ 64 *
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 56) 1))))))) := by
  have e0 := words_step m p 57 0 (by omega)
  have e1 := words_step m p 57 1 (by omega)
  have e2 := words_step m p 57 2 (by omega)
  have e3 := words_step m p 57 3 (by omega)
  have e4 := words_step m p 57 4 (by omega)
  have e5 := words_step m p 57 5 (by omega)
  have e6 := words_step m p 57 6 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.sub_zero] at e0 e1 e2 e3 e4 e5 e6
  rw [BitVec.add_zero] at e0
  rw [e0, e1, e2, e3, e4, e5, e6]

/-- The byte below a word that is zero. -/
theorem byte_of_zero (m : Mem) (p : Addr) (h : m.readW p 64 = 0) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) = 0 := by
  have hs : Spec.Ed448.bytesAt m p (1 + 7) =
      Spec.Ed448.bytesAt m p 1 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 1) 7 :=
    Proof.X25519.bytesAt_add m p 1 7
  have hw : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 8) = 0 := by
    rw [Proof.Ed448.decodeLE_eq, Proof.Ed448.bytesAt_eq, Proof.X25519.leNum_bytesAt_64, h]; rfl
  rw [show (8 : Nat) = 1 + 7 from rfl, hs, Proof.Ed448.decodeLE_append] at hw
  omega

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem decodeLE_byte_lt (m : Mem) (p : Addr) : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) < 256 := by
  simp only [Spec.Ed448.bytesAt, List.range_one, List.map_cons, List.map_nil, Spec.Ed448.decodeLE]
  have := (m (p + BitVec.ofNat 64 0)).isLt
  omega

end VG.Proof.Ed448.X86_64
