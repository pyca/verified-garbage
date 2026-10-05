import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.AesCcm.Ctr

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.CtrPart`. -/
section

/-!
# AES-SIV: CTR a block at a time

`ctrPart ciph q x k` is CTR's output with only its first `k` bytes done
(the rest of `x` as it is): `x` itself for `k = 0` and `ctr ciph q x` for
`k ≥ len(x)`. Writing the next `n` bytes of the keystream block `i`, XORed
into the data at `P + 16 i`, gives the next one (`ctrPart_step`), as an
implementation that XORs a keystream block into the data a byte at a time
does. Nothing here depends on a target.
-/

namespace VG.Proof.AesSiv

open VG VG.WriteBytes

/-- The first `a` bytes of `a + b` bytes. -/
theorem take_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).take a = Spec.Aes.bytesAt m p a := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]

/-- The last `b` bytes of `a + b` bytes. -/
theorem drop_bytesAt (m : Mem) (p : Addr) {a b : Nat} :
    (Spec.Aes.bytesAt m p (a + b)).drop a = Spec.Aes.bytesAt m (p + BitVec.ofNat 64 a) b := by
  rw [Proof.Cmac.Stream.bytesAt_append, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]

theorem writeBytes_at' (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

/-- CTR with the first `k` bytes done. -/
def ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) : List Byte :=
  (List.range x.length).map fun p =>
    if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0

theorem length_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) :
    (VG.Proof.AesSiv.ctrPart ciph q x k).length = x.length := by
  simp [VG.Proof.AesSiv.ctrPart]

theorem getD_ctrPart (ciph : Spec.Cmac.Cipher) (q x : List Byte) (k : Nat) {p : Nat} (hp : p < x.length) :
    (VG.Proof.AesSiv.ctrPart ciph q x k).getD p 0 =
      if p < k then x.getD p 0 ^^^ (Siv.ksBlock ciph q (p / 16)).getD (p % 16) 0 else x.getD p 0 := by
  simp [VG.Proof.AesSiv.ctrPart, List.getD_eq_getElem?_getD, hp]

theorem ext_getD {a b : List Byte} (hl : a.length = b.length) (h : ∀ p < a.length, a.getD p 0 = b.getD p 0) :
    a = b := by
  apply List.ext_getElem hl
  intro p h₁ h₂
  have := h p h₁
  simpa [List.getD_eq_getElem?_getD, h₁, h₂] using this

theorem ctrPart_zero (ciph : Spec.Cmac.Cipher) (q x : List Byte) : VG.Proof.AesSiv.ctrPart ciph q x 0 = x :=
  VG.Proof.AesSiv.ext_getD (VG.Proof.AesSiv.length_ctrPart _ _ _ _) fun p hp => by
    rw [VG.Proof.AesSiv.length_ctrPart] at hp; rw [VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp]; simp

theorem ctrPart_all (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) {k : Nat}
    (hk : x.length ≤ k) : VG.Proof.AesSiv.ctrPart ciph q x k = Spec.Siv.ctr ciph q x :=
  VG.Proof.AesSiv.ext_getD (by rw [VG.Proof.AesSiv.length_ctrPart, Siv.length_ctr ciph hc]) fun p hp => by
    rw [VG.Proof.AesSiv.length_ctrPart] at hp
    rw [VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), Siv.ctr_getD ciph hc q x hp]

theorem getD_xor {a b : List Byte} {k : Nat} (ha : k < a.length) (hb : k < b.length) :
    (Spec.Cmac.xor a b).getD k 0 = a.getD k 0 ^^^ b.getD k 0 := by
  simp [Spec.Cmac.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, ha, hb]

theorem getD_take {a : List Byte} {n k : Nat} (h : k < n) : (a.take n).getD k 0 = a.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- One block of CTR, `n` bytes of it, XORed into the data at `P + 16 i`. -/
theorem ctrPart_step (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) (m : Mem)
    (P : Addr) {i n : Nat} (hx : x.length < 2 ^ 64) (hn : n ≤ 16) (hin : 16 * i + n ≤ x.length)
    (hd : Spec.Aes.bytesAt m P x.length = VG.Proof.AesSiv.ctrPart ciph q x (16 * i)) :
    Spec.Aes.bytesAt (writeBytes m (P + BitVec.ofNat 64 (16 * i))
        (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n) ((Siv.ksBlock ciph q i).take n)))
        P x.length =
      VG.Proof.AesSiv.ctrPart ciph q x (16 * i + n) := by
  have hlk : (Siv.ksBlock ciph q i).length = 16 := hc _
  have hlb : (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt m (P + BitVec.ofNat 64 (16 * i)) n)
      ((Siv.ksBlock ciph q i).take n)).length = n := by
    rw [Proof.Cmac.length_xor, hlb, List.length_take, hlk]; omega
  have hdk : ∀ p < x.length, m (P + BitVec.ofNat 64 p) = (VG.Proof.AesSiv.ctrPart ciph q x (16 * i)).getD p 0 := fun p hp => by
    rw [← hd, Proof.Cmac.getD_bytesAt _ _ hp]
  refine VG.Proof.AesSiv.ext_getD (by rw [Proof.Cmac.bytesAt_length, VG.Proof.AesSiv.length_ctrPart]) fun p hp => ?_
  rw [Proof.Cmac.bytesAt_length] at hp
  rw [Proof.Cmac.getD_bytesAt _ _ hp, VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp]
  by_cases h₁ : p < 16 * i
  · rw [writeBytes_before _ _ _ h₁ (by rw [hlx]; omega), hdk p hp, VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp,
      ite_eq_left h₁, ite_eq_left (by omega)]
  · have e : P + BitVec.ofNat 64 p = P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i) := by
      rw [Offset.add_add, show 16 * i + (p - 16 * i) = p by omega]
    have hm : m (P + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 (p - 16 * i)) = x.getD p 0 := by
      rw [← e, hdk p hp, VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp, ite_eq_right h₁]
    rw [e, VG.Proof.AesSiv.writeBytes_at' _ _ _ (by omega), hlx]
    by_cases h₂ : p < 16 * i + n
    · rw [ite_eq_left (by omega), ite_eq_left h₂, VG.Proof.AesSiv.getD_xor (by rw [hlb]; omega) (by rw [List.length_take, hlk]; omega),
        Proof.Cmac.getD_bytesAt _ _ (by omega), hm, VG.Proof.AesSiv.getD_take (by omega),
        show p / 16 = i by omega, show p % 16 = p - 16 * i by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h₂, hm]

end VG.Proof.AesSiv

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Words`. -/
section

/-!
# AES-SIV: words and bits

Facts about 64-bit words that implementations on any target use:

* The counter `Q + i` is stored as a 128-bit block (big-endian, as
  `Spec.Gcm.toBytes`), which is the RFC's `be128` of the number
  (`toBytes_be128`, `be128_add`).
* The counter `Q`: the IV's second word with bits 7 and 39 cleared (`qmask`)
  clears bit 7 of its bytes 8 and 12 (`counter_words`).
* The comparison of the IVs: the OR of the XORs of the halves is 0 exactly if
  the IVs are equal (`or_xor_eq_zero`, `le8_append_eq`).
-/

namespace VG.Proof.AesSiv

open VG Proof.Cmac

theorem getD_le8_append (a b : BitVec 64) {k : Nat} (hk : k < 16) :
    (le8 a ++ le8 b).getD k 0 = if k < 8 then a.extractLsb' (8 * k) 8 else b.extractLsb' (8 * (k - 8)) 8 := by
  rw [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by rw [length_le8]; omega), ← List.getD_eq_getElem?_getD, getD_le8 _ ‹_›]
  · rw [List.getElem?_append_right (by rw [length_le8]; omega), length_le8, ← List.getD_eq_getElem?_getD,
      getD_le8 _ (by omega)]

/-! ## The counter as a block -/

theorem toBytes_be128 (x : Nat) : Spec.Gcm.toBytes (BitVec.ofNat 128 x) = Spec.Siv.be128 x := by
  simp only [Spec.Gcm.toBytes, Spec.Siv.be128]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : 2 ^ 128 = 2 ^ (8 * (15 - i)) * 2 ^ (128 - 8 * (15 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    show 256 ^ (15 - i) = 2 ^ (8 * (15 - i)) by rw [Nat.pow_mul]]

theorem beNat_eq (q : List Byte) : Spec.Gcm.ofBytes q = BitVec.ofNat 128 (Spec.Siv.beNat q) := rfl

/-- The counter block of CTR for block `i`: `be128 (beNat q + i)` is the
block of `q` plus `i`, as bytes. -/
theorem be128_add (q : List Byte) (i : Nat) :
    Spec.Siv.be128 (Spec.Siv.beNat q + i) = Spec.Gcm.toBytes (Spec.Gcm.ofBytes q + BitVec.ofNat 128 i) := by
  rw [← VG.Proof.AesSiv.toBytes_be128, VG.Proof.AesSiv.beNat_eq, BitVec.ofNat_add]

/-! ## The counter `Q` -/

/-- The mask of the IV's second word: bit 7 of its bytes 0 and 4 (the IV's
bytes 8 and 12) cleared. -/
def qmask : BitVec 64 := 0xffffff7fffffff7f

theorem extractLsb'_and (a b : BitVec 64) (k : Nat) :
    (a &&& b).extractLsb' (8 * k) 8 = a.extractLsb' (8 * k) 8 &&& b.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem qmask_byte : ∀ k < 8, qmask.extractLsb' (8 * k) 8 = if k = 0 ∨ k = 4 then 0x7f else 0xff := by
  decide

/-- The two words of the IV, the second ANDed with `qmask`, are the bytes of
the counter `Q`. -/
theorem counter_words (w₀ w₁ : BitVec 64) :
    le8 w₀ ++ le8 (w₁ &&& VG.Proof.AesSiv.qmask) = Spec.Siv.counter (le8 w₀ ++ le8 w₁) := by
  refine ext16 (by simp [length_le8]) (by simp [Spec.Siv.counter]) fun k hk => ?_
  simp only [Spec.Siv.counter, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [VG.Proof.AesSiv.getD_le8_append _ _ hk, VG.Proof.AesSiv.getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    split
    · omega
    · rfl
  · rw [VG.Proof.AesSiv.getD_le8_append _ _ hk, VG.Proof.AesSiv.getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [VG.Proof.AesSiv.extractLsb'_and, VG.Proof.AesSiv.qmask_byte (k - 8) (by omega)]
    by_cases hk' : k = 8 ∨ k = 12
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = True from eq_true (by omega), hk', ite_true]
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = False from eq_false (by omega), hk', ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]

/-! ## Comparing the IVs -/

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun l => (l.getD (j / 8) 0).getLsbD (j % 8)) h
  simp only [getD_le8 _ (show j / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show j % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem or_xor_eq_zero (v₀ t₀ v₁ t₁ : BitVec 64) :
    ((v₀ ^^^ t₀) ||| (v₁ ^^^ t₁)) = 0 ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have hb : ∀ j < 64, v₀.getLsbD j = t₀.getLsbD j ∧ v₁.getLsbD j = t₁.getLsbD j := by
      intro j _
      have := congrArg (fun x : BitVec 64 => x.getLsbD j) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor] at this
      have z : (0 : BitVec 64).getLsbD j = false := by simp
      rw [z] at this
      revert this
      cases v₀.getLsbD j <;> cases t₀.getLsbD j <;> cases v₁.getLsbD j <;> cases t₁.getLsbD j <;> simp
    exact ⟨BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).1, BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).2⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- Two 16-byte blocks, as two words each, are equal exactly if their words are. -/
theorem le8_append_eq (v₀ t₀ v₁ t₁ : BitVec 64) :
    le8 v₀ ++ le8 v₁ = le8 t₀ ++ le8 t₁ ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have := List.append_inj h (by simp [length_le8])
    exact ⟨VG.Proof.AesSiv.le8_inj this.1, VG.Proof.AesSiv.le8_inj this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- `((a − 1) ∧ ¬a) >> 63`: 1 if `a` is 0, else 0. -/
theorem eqz (a : BitVec 64) : ((a - 1) &&& ~~~a) >>> 63 = if a = 0 then 1 else 0 := by
  split
  · subst_vars; decide
  · rename_i h
    have h0 : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and, BitVec.toNat_not,
      BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
    have ha := a.isLt
    apply Nat.div_eq_of_lt
    by_cases hm : a.toNat < 2 ^ 63
    · calc _ ≤ (2 ^ 64 - 1 + a.toNat) % 2 ^ 64 := Nat.and_le_left
        _ < 2 ^ 63 := by rw [show 2 ^ 64 - 1 + a.toNat = (a.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]; omega
    · calc _ ≤ 2 ^ 64 - 1 - a.toNat := Nat.and_le_right
        _ < 2 ^ 63 := by omega

/-! ## Blocks -/

theorem xor_zeros {x : List Byte} (h : x.length = 16) : Spec.Cmac.xor x (Spec.Cmac.zeros 16) = x := by
  apply List.ext_getElem (by simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h])
  intro i h₁ h₂
  simp only [Spec.Cmac.xor, Spec.Cmac.zeros, List.getElem_zipWith, List.getElem_replicate]
  exact BitVec.xor_zero ..

theorem chain_blocks_nil (c : Spec.Cmac.Cipher) (z : List Byte) :
    Spec.Cmac.chain c z (Spec.Cmac.blocks 16 []) = z := rfl

/-- The last block of CMAC (§6.2 step 4) is a block. -/
theorem length_lastBlock {k1 k2 t : List Byte} (h1 : k1.length = 16) (h2 : k2.length = 16) (ht : t.length ≤ 16) :
    (Spec.Cmac.lastBlock 16 k1 k2 t).length = 16 := by
  unfold Spec.Cmac.lastBlock
  split
  · simp [Proof.Cmac.length_xor, *]
  · simp [Proof.Cmac.length_xor, Proof.Cmac.length_zeros, h2]; omega

end VG.Proof.AesSiv

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Ctr32`. -/
section

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
  rw [← VG.Proof.AesSiv.toBytes_be128, Proof.Cmac.ofBytes_toBytes]

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
    have := beVal_lt q; rw [hq] at this; rw [VG.Proof.AesSiv.beNat_eq_beVal]; simpa using this
  intro i hi
  rw [VG.Proof.AesSiv.ofBytes_be128]
  induction i with
  | zero => rw [VG.Proof.AesSiv.beNat_eq]; rfl
  | succ i ih =>
    rw [Nat.repeat, ih (by omega), VG.Proof.AesSiv.inc32_ofNat (by omega) (by omega), Nat.add_assoc]

/-- `vg_aes_ctr32`'s keystream from `q`, over `k` blocks whose counter blocks
are `q + i`, XORed into `k` blocks: CTR's output on them. -/
theorem xorKs_ctrPart {G : Gcm.Block → Gcm.Block} {ciph : Cmac.Cipher}
    (hG : ∀ c : List Byte, c.length = 16 → Gcm.toBytes (G (Gcm.ofBytes c)) = ciph c) {q : List Byte}
    {icb : Gcm.Block} {k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i icb = Gcm.ofBytes (Siv.be128 (Siv.beNat q + i)))
    {d : List Byte} (hd : d.length = 16 * k) :
    Proof.Gcm.xorKs G icb 0 d = VG.Proof.AesSiv.ctrPart ciph q d (16 * k) := by
  refine VG.Proof.AesSiv.ext_getD (by rw [Proof.Gcm.length_xorKs, VG.Proof.AesSiv.length_ctrPart]) fun p hp => ?_
  rw [Proof.Gcm.length_xorKs] at hp
  rw [Proof.Gcm.getD_xorKs _ _ _ _ hp, VG.Proof.AesSiv.getD_ctrPart _ _ _ _ hp, ite_eq_left (by omega), Nat.zero_add,
    Proof.Gcm.ksByte, hinc (p / 16) (by omega), hG _ (VG.Proof.AesSiv.length_be128 _)]

/-- `vg_aes_ctr32` from `q` over `k` blocks at `D` whose counter blocks are
`q + i`: CTR's output, with the first `16 k` bytes done, on the data. -/
theorem ctr32_ctrPart {m m' : Mem} {K C D : Addr} {R : Nat} {q : List Byte} {k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i (Gcm.blockAt m C) = Gcm.ofBytes (Siv.be128 (Siv.beNat q + i)))
    (hd : Gcm.blocksAt m' D k =
      Gcm.ctr32 (Gcm.aesWith R (Aes.bytesAt m K (16 * (R + 1)))) (Gcm.blockAt m C) (Gcm.blocksAt m D k)) :
    Aes.bytesAt m' D (16 * k) = VG.Proof.AesSiv.ctrPart (Siv.schedCiph m K R) q (Aes.bytesAt m D (16 * k)) (16 * k) := by
  rw [ctr32_bytes hd]
  exact VG.Proof.AesSiv.xorKs_ctrPart (fun c hc => Proof.Cmac.aesWith_bytes _ _ hc) hinc (Proof.Cmac.bytesAt_length _ _ _)

/-- CTR's output with the first `a` bytes done, on the first `a` bytes of
`a + b`: those of CTR's output on all of them. -/
theorem ctrPart_take (ciph : Cmac.Cipher) (q : List Byte) {x : List Byte} {a : Nat} (ha : a ≤ x.length) :
    VG.Proof.AesSiv.ctrPart ciph q (x.take a) a = (VG.Proof.AesSiv.ctrPart ciph q x a).take a := by
  refine VG.Proof.AesSiv.ext_getD (by simp only [VG.Proof.AesSiv.length_ctrPart, List.length_take]) fun p hp => ?_
  simp only [VG.Proof.AesSiv.length_ctrPart, List.length_take] at hp
  rw [VG.Proof.AesSiv.getD_ctrPart _ _ _ _ (by simp only [List.length_take]; omega), VG.Proof.AesSiv.getD_take (by omega), VG.Proof.AesSiv.getD_take (by omega),
    VG.Proof.AesSiv.getD_ctrPart _ _ _ _ (by omega)]

/-- The counter `Q`'s last 32 bits, as a big-endian integer, are below `2³¹`. -/
theorem counter_low (v : List Byte) : Siv.beNat (Siv.counter v) % 2 ^ 32 < 2 ^ 31 := by
  have e : Siv.counter v = ((List.range 12).map fun i => if i = 8 then v.getD i 0 &&& 0x7f else v.getD i 0) ++
      [v.getD 12 0 &&& 0x7f, v.getD 13 0, v.getD 14 0, v.getD 15 0] := by
    simp [Siv.counter, List.range_succ]
  rw [e, VG.Proof.AesSiv.beNat_eq_beVal, beVal_append, beVal_cons, beVal_cons, beVal_cons, beVal_cons]
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
    VG.Proof.AesSiv.ctrPart ciph q (a ++ b) a.length = VG.Proof.AesSiv.ctrPart ciph q a a.length ++ b := by
  refine VG.Proof.AesSiv.ext_getD (by simp [VG.Proof.AesSiv.length_ctrPart]) fun p hp => ?_
  simp only [VG.Proof.AesSiv.length_ctrPart, List.length_append] at hp
  rw [VG.Proof.AesSiv.getD_ctrPart _ _ _ _ (by simp; omega)]
  by_cases h : p < a.length
  · rw [ite_eq_left h]
    have e1 : (a ++ b).getD p 0 = a.getD p 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have e2 : (VG.Proof.AesSiv.ctrPart ciph q a a.length ++ b).getD p 0 = (VG.Proof.AesSiv.ctrPart ciph q a a.length).getD p 0 := by
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show p < (VG.Proof.AesSiv.ctrPart ciph q a a.length).length by rw [VG.Proof.AesSiv.length_ctrPart]; exact h)]
    rw [e1, e2, VG.Proof.AesSiv.getD_ctrPart _ _ _ _ h, ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : (a ++ b).getD p 0 = b.getD (p - a.length) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show a.length ≤ p by omega)]
    have e2 : (VG.Proof.AesSiv.ctrPart ciph q a a.length ++ b).getD p 0 = b.getD (p - a.length) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right
        (show (VG.Proof.AesSiv.ctrPart ciph q a a.length).length ≤ p by rw [VG.Proof.AesSiv.length_ctrPart]; omega), VG.Proof.AesSiv.length_ctrPart]
    rw [e1, e2]

/-- `vg_aes_ctr32` on a zero block: the keystream block of its counter. -/
theorem xorKs_zeros {G : Gcm.Block → Gcm.Block} (icb : Gcm.Block) :
    Proof.Gcm.xorKs G icb 0 (Cmac.zeros 16) = Gcm.toBytes (G icb) := by
  have hl : (Gcm.toBytes (G icb)).length = 16 := by simp [Gcm.toBytes]
  refine VG.Proof.AesSiv.ext_getD (by rw [Proof.Gcm.length_xorKs, hl]; rfl) fun p hp => ?_
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
theorem orr_eor_80 (x : BitVec 32) : (x ||| 0x80#32) ^^^ 0x80#32 = x &&& VG.Proof.AesSiv.qm4 := by
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
    Proof.Cmac.le4 a ++ Proof.Cmac.le4 b ++ Proof.Cmac.le4 (c &&& VG.Proof.AesSiv.qm4) ++ Proof.Cmac.le4 (d &&& VG.Proof.AesSiv.qm4) =
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
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, h.2, ite_false, ite_true, VG.Proof.AesSiv.extractLsb'_and32,
      VG.Proof.AesSiv.qm4_byte (k % 4) (by omega)]
    by_cases h8 : k = 8
    · subst h8; simp
    · simp only [show ¬ (k = 8 ∨ k = 12) by omega, show k % 4 ≠ 0 by omega, ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]
  · simp only [show ¬ k < 4 by omega, show ¬ k < 8 by omega, show ¬ k < 12 by omega, ite_false,
      VG.Proof.AesSiv.extractLsb'_and32, VG.Proof.AesSiv.qm4_byte (k % 4) (by omega)]
    by_cases h12 : k = 12
    · subst h12; simp
    · simp only [show ¬ (k = 8 ∨ k = 12) by omega, show k % 4 ≠ 0 by omega, ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]

end VG.Proof.AesSiv

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Key`. -/
section

/-!
# AES-SIV: the key context

The context `vg_aes_siv_init` leaves is that of the key (`Spec.Siv.KeyRepr`)
when its three parts are where the calls of `vg_aes_expand_key_scratch` and
`vg_cmac_aes_subkeys` left them (`keyRepr_of`), on any target.
-/

namespace VG.Proof.AesSiv

open VG

/-- The context `init` leaves is that of the key: the schedule of `K1`, its
subkeys and the schedule of `K2`, each where the calls left it. -/
theorem keyRepr_of {m m₀ : Mem} {Ct Kp : Addr} {KL : Nat} (hl : KL = 32 ∨ KL = 48 ∨ KL = 64)
    (h1 : Spec.Aes.bytesAt m Ct (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2)))
    (hs : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))))
        16).2)
    (h2 : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 272) (16 * (Spec.Aes.rounds (KL / 2 / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2))) :
    Spec.Siv.KeyRepr m Ct (Spec.Aes.bytesAt m₀ Kp KL) := by
  have hKL : KL = KL / 2 + KL / 2 := by omega
  have hlen := Proof.Cmac.bytesAt_length m₀ Kp KL
  have e8 : KL / 8 = KL / 2 / 4 := by omega
  have k1 : (Spec.Aes.bytesAt m₀ Kp KL).take (KL / 2) = Spec.Aes.bytesAt m₀ Kp (KL / 2) := by
    have := VG.Proof.AesSiv.take_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have k2 : (Spec.Aes.bytesAt m₀ Kp KL).drop (KL / 2) =
      Spec.Aes.bytesAt m₀ (Kp + BitVec.ofNat 64 (KL / 2)) (KL / 2) := by
    have := VG.Proof.AesSiv.drop_bytesAt m₀ Kp (a := KL / 2) (b := KL / 2)
    rwa [← hKL] at this
  have hs' : Spec.Aes.bytesAt m (Ct + BitVec.ofNat 64 240) 32 =
      Spec.Aes.bytesAt m (Ct + 240) 16 ++ Spec.Aes.bytesAt m (Ct + 256) 16 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, Proof.Cmac.Stream.bytesAt_append, Offset.add_add]; rfl
  have ka : Spec.Cmac.aes (Spec.Aes.bytesAt m₀ Kp (KL / 2)) =
      Spec.Cmac.aesWith (KL / 8 + 6) (Spec.Aes.expandKey (Spec.Aes.bytesAt m₀ Kp (KL / 2))) := by
    rw [Spec.Cmac.aes, Proof.Cmac.bytesAt_length, Spec.Aes.rounds, e8]
  rw [hs', ← ka] at hs
  obtain ⟨hs1, hs2⟩ := List.append_inj hs (by
    rw [Proof.Cmac.bytesAt_length, Spec.Cmac.aes]; exact (Proof.Cmac.subkeys_aes_length _ _).symm)
  refine ⟨by rw [hlen]; exact hl, ?_, ?_, ?_, ?_⟩
  · rw [hlen, k1, e8]; exact h1
  · rw [hlen, k1]; exact hs1
  · rw [hlen, k1]; exact hs2
  · rw [hlen, k2, e8]; exact h2

end VG.Proof.AesSiv

end

/- Proofs formerly in `VerifiedGarbage.Proof.AesSiv.Long`. -/
section

/-!
# AES-SIV: finishing S2V with a string of a block or more

For a last string `P` of `L ≥ 16` bytes, with `nb = ⌊(L − 1) / 16⌋` whole
blocks before its last 1 to 16 bytes, `k = max(nb, 1) − 1` (`kOf`) and
`j = min(nb, 1)` (`jOf`), an implementation copies the last `T = L − 16 k`
bytes of `P` (17 to 32 of them, or 16 if `L = 16`) to a tail and XORs `D`
into its last 16 bytes (`xorend_mem`), so the tail is `P[16k..] xorend D`;
then it chains the `k` blocks of `P`, then the first `j` blocks of the tail,
and finalizes the rest of the tail (`long_spec`). Nothing here depends on a
target.
-/

namespace VG.Proof.AesSiv

open VG

/-- The whole blocks of `P` chained before the tail. -/
def kOf (L : Nat) : Nat := if L < 17 then 0 else (L - 1) / 16 - 1

/-- The whole blocks of the tail chained before its last bytes. -/
def jOf (L : Nat) : Nat := if L < 17 then 0 else 1

theorem kOf_lt {L : Nat} (h : L < 17) : VG.Proof.AesSiv.kOf L = 0 := by simp [VG.Proof.AesSiv.kOf, h]

theorem kOf_ge {L : Nat} (h : ¬ L < 17) : VG.Proof.AesSiv.kOf L = (L - 1) / 16 - 1 := by simp [VG.Proof.AesSiv.kOf, h]

theorem kOf_tail {L : Nat} (h : 16 ≤ L) : 16 ≤ L - 16 * VG.Proof.AesSiv.kOf L ∧ L - 16 * VG.Proof.AesSiv.kOf L ≤ 32 := by
  unfold VG.Proof.AesSiv.kOf; split <;> omega

theorem jOf_rest {L : Nat} (h : 16 ≤ L) :
    16 * VG.Proof.AesSiv.jOf L ≤ L - 16 * VG.Proof.AesSiv.kOf L ∧ 0 < L - 16 * VG.Proof.AesSiv.kOf L - 16 * VG.Proof.AesSiv.jOf L ∧ L - 16 * VG.Proof.AesSiv.kOf L - 16 * VG.Proof.AesSiv.jOf L ≤ 16 := by
  unfold VG.Proof.AesSiv.kOf VG.Proof.AesSiv.jOf; split <;> omega

theorem jOf_le (L : Nat) : VG.Proof.AesSiv.jOf L ≤ 1 := by unfold VG.Proof.AesSiv.jOf; split <;> omega

/-- XORing `D` into the last 16 of `T` bytes. -/
theorem xorend_mem (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    Spec.Aes.bytesAt (Proof.Cmac.xor2Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (Spec.Aes.bytesAt m B T) (Spec.Aes.bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (Proof.Cmac.xor2Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := VG.Proof.AesSiv.take_bytesAt m B (a := T - 16) (b := 16)
  have dr := VG.Proof.AesSiv.drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor2Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Proof.Cmac.xor2Mem_bytes _ ?_ ?_, Siv.xor_eq]
  · rw [Offset.add_add]; exact Offset.disjoint B (by omega) (by omega) (by omega)
  · exact (hd.sub_left (fun a ha => hc a (Region.sub_prefix (base := B + BitVec.ofNat 64 (T - 16)) (len := 8)
      (len' := 16) (by decide) a ha))).sub_right (Offset.sub_base Q (d := 8) (n := 8) (k := 16) (by decide))

/-- S2V's end for a string of a block or more, as the implementations
compute it. -/
theorem long_spec (ciph : Spec.Cmac.Cipher) (k1 k2 d p : List Byte) (hd : d.length = 16) (hL16 : 16 ≤ p.length) :
    ciph (Spec.Cmac.xor (Spec.Cmac.lastBlock 16 k1 k2
          ((Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.kOf p.length)) d).drop (16 * VG.Proof.AesSiv.jOf p.length)))
        (Spec.Cmac.chain ciph (Spec.Cmac.chain ciph (Spec.Cmac.zeros 16)
            (Spec.Cmac.blocks 16 (p.take (16 * VG.Proof.AesSiv.kOf p.length))))
          (Spec.Cmac.blocks 16 ((Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.kOf p.length)) d).take (16 * VG.Proof.AesSiv.jOf p.length))))) =
      Spec.Siv.s2vFinish (Spec.Siv.cmacWith ciph k1 k2) d p := by
  have hT := VG.Proof.AesSiv.kOf_tail hL16
  have hJ := VG.Proof.AesSiv.jOf_rest hL16
  have hlT : (Spec.Siv.xorend (p.drop (16 * VG.Proof.AesSiv.kOf p.length)) d).length = p.length - 16 * VG.Proof.AesSiv.kOf p.length := by
    rw [Siv.length_xorend (by rw [List.length_drop, hd]; omega), List.length_drop]
  rw [Siv.s2vFinish_long _ hd (a := 16 * VG.Proof.AesSiv.kOf p.length) (by omega)]
  generalize Spec.Siv.xorend (List.drop (16 * VG.Proof.AesSiv.kOf p.length) p) d = tl at hlT ⊢
  conv => rhs; rw [← List.take_append_drop (16 * VG.Proof.AesSiv.jOf p.length) tl]
  rw [← List.append_assoc, Siv.cmacWith_split₂ _ _ _ (by rw [List.length_take]; omega)
      (by rw [List.length_take, hlT]; omega) (by rw [List.length_drop, hlT]; omega)
      (Or.inr (by rw [List.length_drop, hlT]; omega)), Proof.Cmac.xor_comm]

end VG.Proof.AesSiv

end
