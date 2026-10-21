module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Ed25519.Contract

/-! # Facts about the seed's SHA-512 digest, for the expanded-key entry points

Signing and the public key depend on the seed only through its digest
(`sign_of_sha512_eq`, `publicKey_of_sha512_eq`), and a digest is 64 bytes. Copies of it
are read back by words (`bytesAt_of_words`). -/

@[expose] public section

namespace VG.Proof.Ed25519

/-- A signature depends on the seed only through its SHA-512 digest. -/
theorem sign_of_sha512_eq {a b : List Byte} (h : Spec.Sha512.sha512 a = Spec.Sha512.sha512 b)
    (m : List Byte) : Spec.Ed25519.sign a m = Spec.Ed25519.sign b m := by
  simp only [Spec.Ed25519.sign, Spec.Ed25519.expandSecret, h]

/-- The public key depends on the seed only through its SHA-512 digest. -/
theorem publicKey_of_sha512_eq {a b : List Byte} (h : Spec.Sha512.sha512 a = Spec.Sha512.sha512 b) :
    Spec.Ed25519.publicKey a = Spec.Ed25519.publicKey b := by
  simp only [Spec.Ed25519.publicKey, Spec.Ed25519.expandSecret, h]

theorem sha512_length (m : List Byte) : (Spec.Sha512.sha512 m).length = 64 := by
  simp [Spec.Sha512.sha512, Spec.Sha512.finalHash, Spec.Sha512.wordBytes, List.map_const']

/-- Byte `i` of a little-endian 64-bit word. -/
theorem readW_byte64 (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    m (a + BitVec.ofNat 64 i) = (m.readW a 64).extractLsb' (8 * i) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi]
  simp only [Mem.readW]
  rfl

/-- 64 bytes from their eight little-endian words. -/
theorem bytesAt_of_words {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 8, m'.readW (p' + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64) :
    Spec.Sha512.bytesAt m' p' 64 = Spec.Ed25519.bytesAt m p 64 := by
  simp only [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ∀ q : Addr, q + BitVec.ofNat 64 i = q + BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
    intro q
    have e : BitVec.ofNat 64 i = BitVec.ofNat 64 (8 * (i / 8)) + BitVec.ofNat 64 (i % 8) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1; omega
    rw [e, BitVec.add_assoc]
  have hk : i / 8 < 8 := by omega
  have hj : i % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [ha p', ha p, readW_byte64 m' _ hj, readW_byte64 m _ hj, h _ hk]

end VG.Proof.Ed25519
