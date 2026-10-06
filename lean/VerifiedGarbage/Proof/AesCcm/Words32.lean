import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesCcm.Bytes
import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Cmac.Frame

/-!
# AES-CCM: blocks built of 32-bit words

Untrusted: everything here is checked by Lean. Target-independent facts for
code that builds AES-CCM's blocks from 32-bit words, as the x86 code does: a
word written into a buffer replaces four of its bytes
(`bytesAt_writeW32_at`); a byte-reversed number is its big-endian bytes
(`le4_byteRev32_ofNat`); the last word of `Ctrᵢ` (A.3) is that of `Ctr₀`
ORed with `[i]₃₂` (`ctr_or32`); and the encodings of the lengths of the
associated data less than 2³² (A.2.2), and the flags of `B₀` (A.2.1), as
the 32-bit code computes them.
-/

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le4)

/-- The bytes of a buffer after a write that misses it. -/
theorem bytesAt_writeW_sep (m : Mem) {q a : Addr} {w n : Nat} (v : BitVec w)
    (h : (⟨q, n⟩ : Region).Disjoint ⟨a, w / 8⟩) (hn : n ≤ 2 ^ 64) : bytesAt (m.writeW a v) q n = bytesAt m q n :=
  Proof.Cmac.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h) hn

/-- The four bytes of a word just written. -/
theorem bytesAt_writeW32_self (m : Mem) (p : Addr) (v : BitVec 32) : bytesAt (m.writeW p v) p 4 = le4 v := by
  rw [bytesAt_writeW32_base _ _ _ (by decide) (by decide), List.drop_eq_nil_of_le (by rw [length_bytesAt]),
    List.append_nil]

/-- `B₀` as the x86 code builds it: the first three words of `Ctr₀`, the
flags over its first byte, then the last word. -/
theorem b0_bytes (m : Mem) (p : Addr) (w₀ w₁ w₂ x : BitVec 32) (f : Byte) :
    bytesAt (((((m.writeW p w₀).writeW (p + BitVec.ofNat 64 4) w₁).writeW (p + BitVec.ofNat 64 8) w₂).writeW p f).writeW
      (p + BitVec.ofNat 64 12) x) p 16 = (f :: (le4 w₀).drop 1) ++ le4 w₁ ++ le4 w₂ ++ le4 x := by
  have dj : ∀ a n d k, a + n ≤ d ∨ d + k ≤ a → a + n ≤ 16 → d + k ≤ 16 →
      (⟨p + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 d, k⟩ :=
    fun a n d k h ha hd => Offset.disjoint p h (by omega) (by omega)
  have d0 : ∀ d k, 4 ≤ d → d + k ≤ 16 → (⟨p, 4⟩ : Region).Disjoint ⟨p + BitVec.ofNat 64 d, k⟩ := fun d k h hd => by
    simpa using dj 0 4 d k (.inl h) (by decide) hd
  have d0' : ∀ a n, 1 ≤ a → a + n ≤ 16 → (⟨p + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨p, 8 / 8⟩ := fun a n h ha => by
    simpa using dj a n 0 1 (.inr h) ha (by decide)
  rw [Cmac.bytesAt_split4]
  rw [bytesAt_writeW_sep _ _ (d0 12 4 (by decide) (by decide)) (by decide), bytesAt_writeW8_base _ _ _ (by decide)
      (by decide), bytesAt_writeW_sep _ _ (d0 8 4 (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0 4 4 (by decide) (by decide)) (by decide), bytesAt_writeW32_self,
    bytesAt_writeW_sep _ _ (dj 4 4 12 4 (.inl (by decide)) (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0' 4 4 (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (dj 4 4 8 4 (.inl (by decide)) (by decide) (by decide)) (by decide), bytesAt_writeW32_self,
    bytesAt_writeW_sep _ _ (dj 8 4 12 4 (.inl (by decide)) (by decide) (by decide)) (by decide),
    bytesAt_writeW_sep _ _ (d0' 8 4 (by decide) (by decide)) (by decide), bytesAt_writeW32_self, bytesAt_writeW32_self]

/-- The bytes of `[v]₃₂`, the most significant first. -/
theorem le4_byteRev32_ofNat {v : Nat} (hv : v < 2 ^ 32) : le4 (byteRev32 (BitVec.ofNat 32 v)) = Spec.Ccm.be 4 v := by
  rw [le4, byteRev32_extract, Spec.Ccm.be, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hv]

/-- The last 4 bytes of `Ctrᵢ`, for `i < 2³²`: `[i]₃₂`, ORed with those of
`Ctr₀` (the nonce's last bytes, when `q < 4`). -/
theorem ctrBlock_drop12_or {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi : i < 256 ^ (15 - nonce.length)) (hi32 : i < 2 ^ 32) :
    (Spec.Ccm.ctrBlock nonce i).drop 12 =
      List.zipWith (· ||| ·) (Spec.Ccm.be 4 i) ((Spec.Ccm.ctrBlock nonce 0).drop 12) := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.drop_succ_cons]
  rcases Nat.lt_or_ge nonce.length 11 with h | h
  · -- `q > 4`: the last 4 bytes are those of `[i]₈q`.
    simp only [List.drop_append, List.drop_eq_nil_of_le (show nonce.length ≤ 11 by omega),
      List.nil_append, be_zero]
    rw [be_split (q := 4) (k := 15 - nonce.length) (by omega) (by omega), Spec.Ccm.zeros, Spec.Ccm.zeros,
      List.drop_append, List.drop_replicate, List.length_replicate, List.drop_replicate,
      show 15 - nonce.length - 4 - (11 - nonce.length) = 0 by omega, List.replicate_zero, List.nil_append,
      show 11 - nonce.length - (15 - nonce.length - 4) = 0 by omega, List.drop_zero,
      show 15 - nonce.length - (11 - nonce.length) = 4 by omega]
    exact (zipWith_or_zeros_right _ (length_be 4 i)).symm
  · -- `q ≤ 4`: the nonce's last bytes, then `[i]₈q`.
    rw [List.drop_append_of_le_length h, List.drop_append_of_le_length h, be_zero,
      be_split (q := 15 - nonce.length) (k := 4) (by omega) hi]
    have hd : (nonce.drop 11).length = 4 - (15 - nonce.length) := by rw [List.length_drop]; omega
    rw [List.zipWith_append (by rw [hd]; simp [Spec.Ccm.zeros]), zipWith_or_zeros_left _ hd,
      zipWith_or_zeros_right _ (length_be _ _)]

/-- The first 12 bytes of `Ctrᵢ`, for `i < 2³²`, are those of `Ctr₀`. -/
theorem ctrBlock_take12 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {i : Nat}
    (hi32 : i < 2 ^ 32) : (Spec.Ccm.ctrBlock nonce i).take 12 = (Spec.Ccm.ctrBlock nonce 0).take 12 := by
  simp only [Spec.Ccm.ctrBlock, List.cons_append, List.take_succ_cons, List.cons.injEq, true_and]
  rcases Nat.lt_or_ge nonce.length 11 with h | h
  · simp only [List.take_append, List.take_of_length_le (show nonce.length ≤ 11 by omega)]
    congr 1
    rw [be_zero, be_split (q := 4) (k := 15 - nonce.length) (by omega) (by omega), Spec.Ccm.zeros, Spec.Ccm.zeros,
      List.take_append, List.take_replicate, List.take_replicate, List.length_replicate,
      show 11 - nonce.length - (15 - nonce.length - 4) = 0 by omega, List.take_zero, List.append_nil,
      Nat.min_eq_left (show 11 - nonce.length ≤ 15 - nonce.length - 4 by omega),
      Nat.min_eq_left (show 11 - nonce.length ≤ 15 - nonce.length by omega)]
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]

/-- `Ctrᵢ`'s last word, from `Ctr₀`'s and `[i]₃₂`. -/
theorem ctr_or32 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w : BitVec 32}
    (hw : le4 w = (Spec.Ccm.ctrBlock nonce 0).drop 12) {i : Nat} (hi : i < 256 ^ (15 - nonce.length))
    (hi32 : i < 2 ^ 32) :
    le4 (byteRev32 (BitVec.ofNat 32 i) ||| w) = (Spec.Ccm.ctrBlock nonce i).drop 12 := by
  rw [le4_or, le4_byteRev32_ofNat hi32, hw, ctrBlock_drop12_or h7 h13 hi hi32]

/-! ## The encoding of the length of the associated data (A.2.2) -/

theorem le4_feff : le4 (BitVec.ofNat 32 0xfeff) = [0xff, 0xfe] ++ Spec.Ccm.zeros 2 := by decide

/-- A right shift by whole bytes drops the low bytes. -/
theorem le4_ushiftRight (x : BitVec 32) {k : Nat} (hk : k ≤ 4) :
    le4 (x >>> (8 * k)) = (le4 x).drop k ++ Spec.Ccm.zeros k := by
  have hl : ((le4 x).drop k).length = 4 - k := by rw [List.length_drop, Proof.Cmac.length_le4]
  have hlen : (le4 (x >>> (8 * k))).length = ((le4 x).drop k ++ Spec.Ccm.zeros k).length := by
    rw [Proof.Cmac.length_le4, List.length_append, hl, Spec.Ccm.zeros, List.length_replicate]
    omega
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hi : i < 4 := by rwa [Proof.Cmac.length_le4] at h₁
  by_cases h : i < 4 - k
  · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_drop]
    simp only [le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [show 8 * k + 8 * i = 8 * (k + i) by omega]
  · rw [List.getElem_append_right (by rw [hl]; omega)]
    simp only [Spec.Ccm.zeros, List.getElem_replicate, le4, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))]
    rfl

/-- `[a]₁₆`, from `[a]₃₂` shifted right by 16, followed by zeros. -/
theorem enc_lo32 {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) :
    le4 (byteRev32 (BitVec.ofNat 32 a) >>> 16) ++ Spec.Ccm.zeros 12 =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  rw [show byteRev32 (BitVec.ofNat 32 a) >>> 16 = byteRev32 (BitVec.ofNat 32 a) >>> (8 * 2) from rfl,
    le4_ushiftRight _ (by decide), le4_byteRev32_ofNat (by omega), be_split (q := 2) (by decide) (by omega),
    encodeLen_lo h, hdrLen_lo h]
  simp [Spec.Ccm.zeros]

/-- `0xff ‖ 0xfe ‖ [a]₃₂`, written over zeros. -/
theorem enc_mid32 {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    (le4 (BitVec.ofNat 32 0xfeff) ++ Spec.Ccm.zeros 12).take 2 ++ le4 (byteRev32 (BitVec.ofNat 32 a)) ++
        (le4 (BitVec.ofNat 32 0xfeff) ++ Spec.Ccm.zeros 12).drop (2 + 4) =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  rw [le4_feff, le4_byteRev32_ofNat h₂, encodeLen_mid h₁ h₂, hdrLen_mid h₁ h₂]
  simp [Spec.Ccm.zeros, List.replicate]

/-! ## The flags of `B₀` (A.2.1) -/

theorem flags_val32 {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 32 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega, ite_false, Nat.zero_add]; omega
  · simp only [h, ite_false, show al > 0 by omega, ite_true]; omega

/-- The first byte of `Ctr₀`, `q − 1 = 14 − n`. -/
theorem sub_low_byte32 {nl : Nat} (h : nl ≤ 14) :
    ((BitVec.ofNat 32 14 - BitVec.ofNat 32 nl).setWidth 8 : Byte) = BitVec.ofNat 8 (15 - nl - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

end VG.Proof.AesCcm
