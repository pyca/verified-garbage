import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-CCM: the bytes of a buffer after writes

Untrusted: everything here is checked by Lean, and depends on no target. A
write of a byte, a 32-bit word or bytes into a buffer replaces those of its
bytes (`bytesAt_writeBytes_at`, `bytesAt_writeW8_at`, `bytesAt_writeW32_at`),
so that the pieces of the 32-bit implementations build their blocks
(`Ctr₀`, `B₀`, the first block of the associated data, a last block padded)
as lists; and `[v]₈ₖ` split into zeros and `[v]₈q` (`be_split`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW32_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (le4 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le4]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le4 _ h]
    simp
  · rfl

theorem bytesAt_writeW32_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 32) (h : o + 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le4 v ++ (bytesAt m p n).drop (o + 4) := by
  rw [writeW32_eq, bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le4]; exact h) hn, Proof.Cmac.length_le4]

theorem bytesAt_writeW32_base (m : Mem) (p : Addr) {n : Nat} (v : BitVec 32) (h : 4 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p v) p n = le4 v ++ (bytesAt m p n).drop 4 := by
  have := bytesAt_writeW32_at m p (o := 0) v h hn
  simpa using this

/-! ## Big-endian strings -/

/-- The last `k` bytes of `[v]₈q`, for `k ≤ q` and `v < 2^(8k)`, are `[v]₈ₖ`. -/
theorem be_drop {q k v : Nat} (hkq : k ≤ q) (hv : v < 256 ^ k) :
    (Spec.Ccm.be q v).drop (q - k) = Spec.Ccm.be k v := by
  rw [be_split hkq hv, List.drop_left' (by simp [Spec.Ccm.zeros])]

theorem le4_or (a b : BitVec 32) : le4 (a ||| b) = List.zipWith (· ||| ·) (le4 a) (le4 b) := by
  apply List.ext_getElem (by simp [le4])
  intro k h₁ h₂
  simp only [le4, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

/-- The last 4 bytes of `Ctrᵢ`: those of the nonce after its first 11, then
the last `min q 4` bytes of `[i]₈q`. -/
theorem ctrBlock_drop12 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ min (15 - nonce.length) 4) :
    (Spec.Ccm.ctrBlock nonce i).drop 12 =
      nonce.drop 11 ++ Spec.Ccm.be (min (15 - nonce.length) 4) i := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.drop_succ_cons]
  by_cases h11 : 11 ≤ nonce.length
  · rw [List.drop_append_of_le_length h11, Nat.min_eq_left (by omega)]
  · rw [List.drop_append, List.drop_eq_nil_of_le (show nonce.length ≤ 11 by omega), List.nil_append,
      show 11 - nonce.length = (15 - nonce.length) - min (15 - nonce.length) 4 by omega,
      be_drop (by omega) hi, List.nil_append]

theorem length_ctrBlock' {nonce : List Byte} (h13 : nonce.length ≤ 13) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).length = 16 := by
  simp only [Spec.Ccm.ctrBlock, List.length_cons, List.length_append, length_be]; omega

/-- `Ctrᵢ`, for `i < 2³²` (and `i < 2^(8q)`), from `Ctr₀`: its first 12 bytes, and
its last 4 ORed with `[i]₃₂`. -/
theorem ctrBlock_split {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ min (15 - nonce.length) 4) :
    Spec.Ccm.ctrBlock nonce i = (Spec.Ccm.ctrBlock nonce 0).take 12 ++
      List.zipWith (· ||| ·) ((Spec.Ccm.ctrBlock nonce 0).drop 12) (Spec.Ccm.be 4 i) := by
  have hi4 : i < 256 ^ 4 := Nat.lt_of_lt_of_le hi (Nat.pow_le_pow_right (by decide) (by omega))
  have k0 : (0 : Nat) < 256 ^ min (15 - nonce.length) 4 := Nat.pow_pos (by decide)
  conv => lhs; rw [← List.take_append_drop 12 (Spec.Ccm.ctrBlock nonce i)]
  congr 1
  · simp only [Spec.Ccm.ctrBlock, List.cons_append, List.take_succ_cons]
    congr 1
    by_cases h11 : 11 ≤ nonce.length
    · rw [List.take_append_of_le_length h11, List.take_append_of_le_length h11]
    · rw [List.take_append, List.take_append, be_split (q := 4) (by omega) hi4,
        be_split (q := 4) (by omega) (show 0 < 256 ^ 4 by decide)]
      congr 1
      rw [List.take_left' (by simp [Spec.Ccm.zeros]; omega), List.take_left' (by simp [Spec.Ccm.zeros]; omega)]
  · rw [ctrBlock_drop12 h7 h13 hi, ctrBlock_drop12 h7 h13 k0, be_zero,
      be_split (k := 4) (q := min (15 - nonce.length) 4) (by omega) hi,
      List.zipWith_append (by simp [Spec.Ccm.zeros]; omega), zipWith_or_zeros_right _ (by simp; omega),
      zipWith_or_zeros_left _ (length_be _ _)]

/-- The cipher of a key schedule that a write misses. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, (⟨K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega)]

end VG.Proof.AesCcm
