import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-SIV: CTR with `vg_aes_ctr32`

`vg_aes_ctr32` increments only the last 32 bits of its counter block
(`inc₃₂`), as a big-endian integer. The counter `Q` (§2.6) clears their most
significant bit (`counter_low`), so from `Q`, fewer than `2³¹` increments
never wrap around: they add to `Q` as a 128-bit integer
(`repeat_inc32`), and `vg_aes_ctr32` from `Q` over `k` whole blocks gives
CTR's output on them (`ctr32_ctrPart`), with the counter `Q + k` it leaves
for the next block. Nothing here depends on a target.
-/

namespace VG.Proof.AesSiv

open VG VG.Spec
open VG.Proof.AesCcm (beVal beVal_append beVal_cons beVal_lt toNat_inc32 ctr32_bytes)

theorem beNat_eq_beVal (q : List Byte) : Siv.beNat q = beVal q := rfl

theorem length_be128 (x : Nat) : (Siv.be128 x).length = 16 := by simp [Siv.be128]

/-- The block of `be128 x` is `x mod 2¹²⁸`. -/
theorem ofBytes_be128 (x : Nat) : Gcm.ofBytes (Siv.be128 x) = BitVec.ofNat 128 x := by
  rw [← toBytes_be128, Proof.Cmac.ofBytes_toBytes]

/-- `inc₃₂` adds 1 unless the last 32 bits wrap around. -/
theorem inc32_ofNat {x : Nat} (hx : x % 2 ^ 32 + 1 < 2 ^ 32) (h128 : x < 2 ^ 128) :
    Gcm.inc32 (BitVec.ofNat 128 x) = BitVec.ofNat 128 (x + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_inc32, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h128,
    Nat.mod_eq_of_lt (a := x % 2 ^ 32 + 1) hx]
  have : x + 1 < 2 ^ 128 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

/-- From a counter block `q` whose last 32 bits do not wrap around in `k`
increments, the `i`-th counter block, `i < k`, is `q + i`. -/
theorem repeat_inc32 {q : List Byte} (hq : q.length = 16) {k : Nat} (hk : Siv.beNat q % 2 ^ 32 + k ≤ 2 ^ 32) :
    ∀ i < k, Nat.repeat Gcm.inc32 i (Gcm.ofBytes q) = Gcm.ofBytes (Siv.be128 (Siv.beNat q + i)) := by
  have hb : Siv.beNat q < 2 ^ 128 := by
    have := beVal_lt q; rw [hq] at this; rw [beNat_eq_beVal]; simpa using this
  intro i hi
  rw [ofBytes_be128]
  induction i with
  | zero => rw [beNat_eq]; rfl
  | succ i ih =>
    rw [Nat.repeat, ih (by omega), inc32_ofNat (by omega) (by omega), Nat.add_assoc]

/-- `vg_aes_ctr32`'s keystream from `q`, over `k` blocks whose counter blocks
are `q + i`, XORed into `k` blocks: CTR's output on them. -/
theorem xorKs_ctrPart {G : Gcm.Block → Gcm.Block} {ciph : Cmac.Cipher}
    (hG : ∀ c : List Byte, c.length = 16 → Gcm.toBytes (G (Gcm.ofBytes c)) = ciph c) {q : List Byte}
    {icb : Gcm.Block} {k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i icb = Gcm.ofBytes (Siv.be128 (Siv.beNat q + i)))
    {d : List Byte} (hd : d.length = 16 * k) :
    Proof.Gcm.xorKs G icb 0 d = ctrPart ciph q d (16 * k) := by
  refine ext_getD (by rw [Proof.Gcm.length_xorKs, length_ctrPart]) fun p hp => ?_
  rw [Proof.Gcm.length_xorKs] at hp
  rw [Proof.Gcm.getD_xorKs _ _ _ _ hp, getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), Nat.zero_add,
    Proof.Gcm.ksByte, hinc (p / 16) (by omega), hG _ (length_be128 _)]

/-- `vg_aes_ctr32` from `q` over `k` blocks at `D` whose counter blocks are
`q + i`: CTR's output, with the first `16 k` bytes done, on the data. -/
theorem ctr32_ctrPart {m m' : Mem} {K C D : Addr} {R : Nat} {q : List Byte} {k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i (Gcm.blockAt m C) = Gcm.ofBytes (Siv.be128 (Siv.beNat q + i)))
    (hd : Gcm.blocksAt m' D k =
      Gcm.ctr32 (Gcm.aesWith R (Aes.bytesAt m K (16 * (R + 1)))) (Gcm.blockAt m C) (Gcm.blocksAt m D k)) :
    Aes.bytesAt m' D (16 * k) = ctrPart (Siv.schedCiph m K R) q (Aes.bytesAt m D (16 * k)) (16 * k) := by
  rw [ctr32_bytes hd]
  exact xorKs_ctrPart (fun c hc => Proof.Cmac.aesWith_bytes _ _ hc) hinc (Proof.Cmac.bytesAt_length _ _ _)

/-- CTR's output with the first `a` bytes done, on the first `a` bytes of
`a + b`: those of CTR's output on all of them. -/
theorem ctrPart_take (ciph : Cmac.Cipher) (q : List Byte) {x : List Byte} {a : Nat} (ha : a ≤ x.length) :
    ctrPart ciph q (x.take a) a = (ctrPart ciph q x a).take a := by
  refine ext_getD (by simp only [length_ctrPart, List.length_take]) fun p hp => ?_
  simp only [length_ctrPart, List.length_take] at hp
  rw [getD_ctrPart _ _ _ _ (by simp only [List.length_take]; omega), getD_take (by omega), getD_take (by omega),
    getD_ctrPart _ _ _ _ (by omega)]

/-- The counter `Q`'s last 32 bits, as a big-endian integer, are below `2³¹`. -/
theorem counter_low (v : List Byte) : Siv.beNat (Siv.counter v) % 2 ^ 32 < 2 ^ 31 := by
  have e : Siv.counter v = ((List.range 12).map fun i => if i = 8 then v.getD i 0 &&& 0x7f else v.getD i 0) ++
      [v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0, v.getD 15 0] := by
    simp [Siv.counter, List.range_succ]
  rw [e, beNat_eq_beVal, beVal_append, beVal_cons, beVal_cons, beVal_cons, beVal_cons]
  simp only [List.length_cons, List.length_nil]
  have h0 : (v.getD 12 0 &&& 0x7f).toNat < 128 := by
    rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h1 := (v.getD 13 0).isLt
  have h2 := (v.getD 14 0).isLt
  have h3 := (v.getD 15 0).isLt
  have hn : beVal [] = 0 := rfl
  rw [hn]
  simp only [Nat.reducePow, Nat.reduceAdd] at h1 h2 h3 ⊢
  omega

/-- The counter `Q` is a block. -/
theorem length_counter (v : List Byte) : (Siv.counter v).length = 16 := by simp [Siv.counter]

/-! ## More of CTR's output -/

/-- CTR's output with the first `a.length` bytes done, on `a` followed by
more: on `a`, then the rest as it is. -/
theorem ctrPart_append (ciph : Cmac.Cipher) (q a b : List Byte) :
    ctrPart ciph q (a ++ b) a.length = ctrPart ciph q a a.length ++ b := by
  refine ext_getD (by simp [length_ctrPart]) fun p hp => ?_
  simp only [length_ctrPart, List.length_append] at hp
  rw [getD_ctrPart _ _ _ _ (by simp; omega)]
  by_cases h : p < a.length
  · rw [ite_eq_left h]
    have e1 : (a ++ b).getD p 0 = a.getD p 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have e2 : (ctrPart ciph q a a.length ++ b).getD p 0 = (ctrPart ciph q a a.length).getD p 0 := by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show p < (ctrPart ciph q a a.length).length by rw [length_ctrPart]; exact h)]
    rw [e1, e2, getD_ctrPart _ _ _ _ h, ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : (a ++ b).getD p 0 = b.getD (p - a.length) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show a.length ≤ p by omega)]
    have e2 : (ctrPart ciph q a a.length ++ b).getD p 0 = b.getD (p - a.length) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right
        (show (ctrPart ciph q a a.length).length ≤ p by rw [length_ctrPart]; omega), length_ctrPart]
    rw [e1, e2]

/-- `vg_aes_ctr32` on a zero block: the keystream block of its counter. -/
theorem xorKs_zeros {G : Gcm.Block → Gcm.Block} (icb : Gcm.Block) :
    Proof.Gcm.xorKs G icb 0 (Cmac.zeros 16) = Gcm.toBytes (G icb) := by
  have hl : (Gcm.toBytes (G icb)).length = 16 := by simp [Gcm.toBytes]
  refine ext_getD (by rw [Proof.Gcm.length_xorKs, hl]; rfl) fun p hp => ?_
  rw [Proof.Gcm.length_xorKs] at hp
  simp only [Cmac.zeros, List.length_replicate] at hp
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by simp [Cmac.zeros, hp]), Nat.zero_add, Proof.Gcm.ksByte,
    show (Cmac.zeros 16).getD p 0 = 0 by
      rw [Cmac.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hp],
    Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
  simp [Nat.repeat]

/-! ## The counter `Q`, a 32-bit word at a time -/

/-- The mask of the IV's third and fourth words: bit 7 of their first bytes
(the IV's bytes 8 and 12) cleared. -/
def qm4 : BitVec 32 := 0xffffff7f

/-- Setting bit 7 and flipping it clears it. -/
theorem orr_eor_80 (x : BitVec 32) : (x ||| 0x80#32) ^^^ 0x80#32 = x &&& qm4 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have h80 : ∀ j < 32, (0x80#32).getLsbD j = decide (j = 7) := by decide
  have hq : ∀ j < 32, qm4.getLsbD j = !decide (j = 7) := by decide
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or, BitVec.getLsbD_and, h80 j hj, hq j hj]
  cases x.getLsbD j <;> by_cases h : j = 7 <;> simp [h]

theorem extractLsb'_and32 (a b : BitVec 32) (k : Nat) :
    (a &&& b).extractLsb' (8 * k) 8 = a.extractLsb' (8 * k) 8 &&& b.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem qm4_byte : ∀ k < 4, qm4.extractLsb' (8 * k) 8 = if k = 0 then 0x7f else 0xff := by decide

/-- The IV's words, the last two ANDed with `qm4`, are the bytes of the
counter `Q`. -/
theorem counter_words4 (a b c d : BitVec 32) :
    Proof.Cmac.le4 a ++ Proof.Cmac.le4 b ++ Proof.Cmac.le4 (c &&& qm4) ++ Proof.Cmac.le4 (d &&& qm4) =
      Siv.counter (Proof.Cmac.le4 a ++ Proof.Cmac.le4 b ++ Proof.Cmac.le4 c ++ Proof.Cmac.le4 d) := by
  refine Proof.Cmac.ext16 (by simp [Proof.Cmac.length_le4]) (by simp [Siv.counter]) fun k hk => ?_
  simp only [Siv.counter, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, Proof.Cmac.getD_le4_append4 _ _ _ _ hk,
    Proof.Cmac.getD_le4_append4 _ _ _ _ hk]
  rcases (by omega : k < 8 ∨ (8 ≤ k ∧ k < 12) ∨ 12 ≤ k) with h | h | h
  · have : ¬ (k = 8 ∨ k = 12) := by omega
    simp only [this, ite_false]
    by_cases h4 : k < 4 <;> simp [h4, h]
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, ite_false, ite_true, extractLsb'_and32,
      qm4_byte (k % 4) (by omega)]
    by_cases h8 : k = 8
    · subst h8; simp
    · simp only [show ¬ (k = 8 ∨ k = 12) by omega, show k % 4 ≠ 0 by omega, ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ite_false,
      extractLsb'_and32, qm4_byte (k % 4) (by omega)]
    by_cases h12 : k = 12
    · subst h12; simp
    · simp only [show ¬ (k = 8 ∨ k = 12) by omega, show k % 4 ≠ 0 by omega, ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]

end VG.Proof.AesSiv
