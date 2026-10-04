import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Spec.GcmSiv

/-!
# AES-GCM-SIV: lemmas on the specification

Untrusted: everything here is checked by Lean. RFC 8452's cipher on byte
strings is CMAC's (`aesWith_eq`), whose relation to GCM's on blocks, as
`vg_aes_ctr32` computes it, is `Proof.Cmac.aesWith_bytes`; the four bytes of
a counter (`le4_le32`); and the message keys of `derive_keys` as the first
8 bytes of each block, one after the other (`halves`, `deriveKeys_eq`).
-/

namespace VG.Proof.GcmSiv

open VG

theorem aesWith_eq (nr : Nat) (w : List Byte) : Spec.GcmSiv.aesWith nr w = Spec.Cmac.aesWith nr w := rfl

theorem aesWith_length (nr : Nat) (w x : List Byte) : (Spec.GcmSiv.aesWith nr w x).length = 16 :=
  Proof.Cmac.aesWith_length nr w x

theorem ctxCiph_length (m : Mem) (K : Addr) (R : Nat) (x : List Byte) :
    (Spec.GcmSiv.ctxCiph m K R x).length = 16 :=
  aesWith_length _ _ _

/-- The four bytes of the counter `i`, as `little_endian_uint32`. -/
theorem le4_le32 (i : Nat) : Proof.Cmac.le4 ((BitVec.ofNat 64 i).setWidth 32) = Spec.GcmSiv.le32 i := by
  apply List.ext_getElem (by simp [Proof.Cmac.le4, Spec.GcmSiv.le32])
  intro j h₁ _
  have hj : j < 4 := by simpa [Proof.Cmac.le4] using h₁
  simp only [Proof.Cmac.le4, Spec.GcmSiv.le32, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- The first 8 bytes of `CIPH(little_endian_uint32(i) ‖ nonce)`, for `i < k`,
one after the other. -/
def halves (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) : List Byte :=
  (List.range k).flatMap fun i => (ciph (Spec.GcmSiv.le32 i ++ nonce)).take 8

theorem halves_succ (ciph : Spec.GcmSiv.Cipher) (nonce : List Byte) (k : Nat) :
    halves ciph nonce (k + 1) = halves ciph nonce k ++ (ciph (Spec.GcmSiv.le32 k ++ nonce)).take 8 := by
  simp [halves, List.range_succ, List.flatMap_append]

theorem length_halves {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (nonce : List Byte) (k : Nat) :
    (halves ciph nonce k).length = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [halves_succ, List.length_append, ih, List.length_take, h]; omega

/-- `derive_keys`: the first 16 bytes of the halves, and the rest. -/
theorem deriveKeys_eq {ciph : Spec.GcmSiv.Cipher} (h : ∀ x, (ciph x).length = 16) (keyLen : Nat)
    (nonce : List Byte) :
    Spec.GcmSiv.deriveKeys ciph keyLen nonce =
      ((halves ciph nonce (keyLen / 8 + 2)).take 16, (halves ciph nonce (keyLen / 8 + 2)).drop 16) := by
  have e : halves ciph nonce (keyLen / 8 + 2) =
      ((ciph (Spec.GcmSiv.le32 0 ++ nonce)).take 8 ++ (ciph (Spec.GcmSiv.le32 1 ++ nonce)).take 8) ++
        (List.range (keyLen / 8)).flatMap fun i => (ciph (Spec.GcmSiv.le32 (i + 2) ++ nonce)).take 8 := by
    simp only [halves, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.append_assoc]
  have hl : ((ciph (Spec.GcmSiv.le32 0 ++ nonce)).take 8 ++ (ciph (Spec.GcmSiv.le32 1 ++ nonce)).take 8).length =
      16 := by simp [h]
  rw [e, List.take_left' hl, List.drop_left' hl]
  rfl

end VG.Proof.GcmSiv
