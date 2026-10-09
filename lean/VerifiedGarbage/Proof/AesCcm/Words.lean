import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Gcm.Be64

/-!
# AES-CCM: blocks built from words and bytes

Untrusted: everything here is checked by Lean, and nothing depends on a
target. A write of a byte, a word or bytes into a buffer replaces those of
its bytes (`bytesAt_writeBytes_at`, `bytesAt_writeW8_at`,
`bytesAt_writeW64_at`): an implementation builds its blocks (`Ctr₀`, `B₀`,
the first block of the associated data, a last block padded) as lists. A
byte-reversed word (`byteRev64`, x86's `bswap` and Arm's `rev`) stored
little-endian is the big-endian `[v]₆₄` (`le8_byteRev64_ofNat`), from which
the last 8 bytes of a counter block (`ctr_or`) and the encodings of the
length of the associated data (`encodeLen_lo`, …) follow; and the flags of
`B₀` (`flags_val`).
-/

namespace VG.Proof.AesCcm

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac (le8)

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem getElem_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n)[i]'(by rw [length_bytesAt]; exact hi) = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt]

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## Writes into a buffer -/

/-- `xs` written at `p + o`, inside the `n` bytes at `p`. -/
theorem bytesAt_writeBytes_at (m : Mem) (p : Addr) {o n : Nat} (xs : List Byte) (h : o + xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 o) xs) p n =
      (bytesAt m p n).take o ++ xs ++ (bytesAt m p n).drop (o + xs.length) := by
  apply List.ext_getElem (by simp [length_bytesAt]; omega_arith)
  intro i h₁ h₂
  rw [getElem_bytesAt _ _ (by rw [length_bytesAt] at h₁; exact h₁)]
  simp only [writeBytes]
  have hi : i < n := by rw [length_bytesAt] at h₁; exact h₁
  have e : (p + BitVec.ofNat 64 i - (p + BitVec.ofNat 64 o)).toNat = (i + (2 ^ 64 - o)) % 2 ^ 64 := by
    rw [Offset.add_sub_add_left, BitVec.toNat_sub, toNat_ofNat64 (by omega_arith), toNat_ofNat64 (by omega_arith)]
    omega_arith
  rw [e]
  have hl := length_bytesAt m p n
  by_cases hlo : i < o
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = 2 ^ 64 - o + i by omega_arith]
    simp only [show ¬ (2 ^ 64 - o + i < xs.length) by omega_arith, ite_false]
    rw [List.getElem_append_left (by simp [hl]; omega_arith), List.getElem_append_left (by simp [hl]; omega_arith),
      List.getElem_take, getElem_bytesAt _ _ hi]
  · rw [show (i + (2 ^ 64 - o)) % 2 ^ 64 = i - o by omega_arith]
    by_cases hhi : i < o + xs.length
    · simp only [show i - o < xs.length by omega_arith, ite_true]
      rw [List.getElem_append_left (by simp [hl]; omega_arith), List.getElem_append_right (by simp [hl]; omega_arith)]
      simp only [List.length_take, hl, List.getD_eq_getElem?_getD, Nat.min_eq_left (show o ≤ n by omega_arith),
        List.getElem?_eq_getElem (show i - o < xs.length by omega_arith), Option.getD_some]
    · simp only [show ¬ (i - o < xs.length) by omega_arith, ite_false]
      rw [List.getElem_append_right (by simp [hl]; omega_arith), List.getElem_drop]
      simp only [List.length_append, List.length_take, hl, Nat.min_eq_left (show o ≤ n by omega_arith)]
      rw [getElem_bytesAt _ _ (by omega_arith), show o + xs.length + (i - (o + xs.length)) = i by omega_arith]

/-- A byte write is a write of one byte. -/
theorem writeW8_eq (m : Mem) (a : Addr) (b : Byte) : m.writeW a b = writeBytes m a [b] := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, List.length_cons, List.length_nil, Nat.zero_add]
  split
  · rename_i h
    simp only [show (x - a).toNat = 0 by omega_arith, List.getD_cons_zero]
    simp
  · rfl

/-- A word write is a write of its bytes, least significant first. -/
theorem writeW64_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (le8 v) := by
  funext x
  simp only [Mem.writeW, Mem.write, writeBytes, Proof.Cmac.length_le8]
  split
  · rename_i h
    rw [Proof.Cmac.getD_le8 _ h]
    simp
  · rfl

theorem bytesAt_writeW8_at (m : Mem) (p : Addr) {o n : Nat} (b : Byte) (h : o + 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) b) p n = (bytesAt m p n).take o ++ [b] ++ (bytesAt m p n).drop (o + 1) := by
  rw [writeW8_eq, bytesAt_writeBytes_at _ _ _ h hn]; rfl

theorem bytesAt_writeW64_at (m : Mem) (p : Addr) {o n : Nat} (v : BitVec 64) (h : o + 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW (p + BitVec.ofNat 64 o) v) p n = (bytesAt m p n).take o ++ le8 v ++ (bytesAt m p n).drop (o + 8) := by
  rw [writeW64_eq, bytesAt_writeBytes_at _ _ _ (by rw [Proof.Cmac.length_le8]; exact h) hn, Proof.Cmac.length_le8]

/-- At offset 0. -/
theorem bytesAt_writeBytes_base (m : Mem) (p : Addr) {n : Nat} (xs : List Byte) (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) : bytesAt (writeBytes m p xs) p n = xs ++ (bytesAt m p n).drop xs.length := by
  have := bytesAt_writeBytes_at m p (o := 0) xs (by omega_arith) hn
  simpa using this

theorem bytesAt_writeW64_base (m : Mem) (p : Addr) {n : Nat} (v : BitVec 64) (h : 8 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p v) p n = le8 v ++ (bytesAt m p n).drop 8 := by
  have := bytesAt_writeW64_at m p (o := 0) v h hn
  simpa using this

theorem bytesAt_writeW8_base (m : Mem) (p : Addr) {n : Nat} (b : Byte) (h : 1 ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (m.writeW p b) p n = b :: (bytesAt m p n).drop 1 := by
  have := bytesAt_writeW8_at m p (o := 0) b h hn
  simpa using this

theorem bytesAt_prefix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m p a = (bytesAt m p n).take a := by
  rw [show n = a + (n - a) by omega_arith, Proof.Cmac.Stream.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

theorem bytesAt_suffix (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    bytesAt m (p + BitVec.ofNat 64 a) (n - a) = (bytesAt m p n).drop a := by
  conv => rhs; rw [show n = a + (n - a) by omega_arith, Proof.Cmac.Stream.bytesAt_append]
  rw [List.drop_left' (length_bytesAt _ _ _)]

/-! ## Words as bytes -/

theorem le8_or (a b : BitVec 64) : le8 (a ||| b) = List.zipWith (· ||| ·) (le8 a) (le8 b) := by
  apply List.ext_getElem (by simp [le8])
  intro k h₁ h₂
  simp only [le8, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  ext j hj
  simp

/-- The bytes of `[v]₆₄`, the most significant first. -/
theorem le8_byteRev64_ofNat {v : Nat} (hv : v < 2 ^ 64) : le8 (byteRev64 (BitVec.ofNat 64 v)) = Spec.Ccm.be 8 v := by
  rw [Proof.Gcm.le8_byteRev64, toNat_ofNat64 hv]
  rfl

theorem be_zero (k : Nat) : Spec.Ccm.be k 0 = Spec.Ccm.zeros k := by
  simp [Spec.Ccm.be, Spec.Ccm.zeros, List.map_const']

/-- `[v]₈ₖ` for `v < 2^(8q)` and `k ≥ q`: zeros, then `[v]₈q`. -/
theorem be_split {q k v : Nat} (hqk : q ≤ k) (hv : v < 256 ^ q) :
    Spec.Ccm.be k v = Spec.Ccm.zeros (k - q) ++ Spec.Ccm.be q v := by
  induction k with
  | zero => rw [show q = 0 by omega_arith]; simp [Spec.Ccm.zeros, Spec.Ccm.be]
  | succ k ih =>
    rcases Nat.lt_or_ge k q with h | h
    · rw [show q = k + 1 by omega_arith]; simp [Spec.Ccm.zeros]
    · rw [be_succ, ih h, show k + 1 - q = (k - q) + 1 by omega_arith, Spec.Ccm.zeros, Spec.Ccm.zeros,
        List.replicate_succ, List.cons_append]
      congr 1
      rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) h))]
      rfl

/-- The last 8 bytes of `Ctrᵢ`: the nonce's bytes after its first 7, then `[i]₈q`. -/
theorem ctrBlock_drop8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).drop 8 = nonce.drop 7 ++ Spec.Ccm.be (15 - nonce.length) i := by
  simp [Spec.Ccm.ctrBlock, List.drop_append_of_le_length (show 7 ≤ nonce.length from h7)]

theorem ctrBlock_take8 {nonce : List Byte} (h7 : 7 ≤ nonce.length) (i : Nat) :
    (Spec.Ccm.ctrBlock nonce i).take 8 = BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce.take 7 := by
  simp [Spec.Ccm.ctrBlock, List.take_append_of_le_length (show 7 ≤ nonce.length from h7)]

theorem zipWith_or_zeros_right (xs : List Byte) {n : Nat} (h : xs.length = n) :
    List.zipWith (· ||| ·) xs (Spec.Ccm.zeros n) = xs := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

theorem zipWith_or_zeros_left (ys : List Byte) {n : Nat} (h : ys.length = n) :
    List.zipWith (· ||| ·) (Spec.Ccm.zeros n) ys = ys := by
  subst h
  apply List.ext_getElem (by simp [Spec.Ccm.zeros])
  intro k h₁ h₂
  simp [Spec.Ccm.zeros]

/-- `Ctrᵢ`'s last 8 bytes, from `Ctr₀`'s and `[i]₆₄`. -/
theorem ctr_or {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13) {w : BitVec 64}
    (hw : le8 w = (Spec.Ccm.ctrBlock nonce 0).drop 8) {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) :
    le8 (w ||| byteRev64 (BitVec.ofNat 64 i)) = (Spec.Ccm.ctrBlock nonce i).drop 8 := by
  have hi64 : i < 2 ^ 64 := Nat.lt_of_lt_of_le hi (by
    rw [show 2 ^ 64 = 256 ^ 8 from rfl]; exact Nat.pow_le_pow_right (by decide) (by omega_arith))
  rw [le8_or, le8_byteRev64_ofNat hi64, hw, ctrBlock_drop8 h7, ctrBlock_drop8 h7, be_zero,
    be_split (q := 15 - nonce.length) (by omega_arith) hi]
  have hd : (nonce.drop 7).length = 8 - (15 - nonce.length) := by rw [List.length_drop]; omega_arith
  rw [List.zipWith_append (by rw [hd]; simp [Spec.Ccm.zeros]), zipWith_or_zeros_right _ hd,
    zipWith_or_zeros_left _ (length_be _ _)]

/-- A right shift by whole bytes drops the low bytes. -/
theorem le8_ushiftRight (x : BitVec 64) {k : Nat} (hk : k ≤ 8) :
    le8 (x >>> (8 * k)) = (le8 x).drop k ++ Spec.Ccm.zeros k := by
  have hl : ((le8 x).drop k).length = 8 - k := by rw [List.length_drop, Proof.Cmac.length_le8]
  have hlen : (le8 (x >>> (8 * k))).length = ((le8 x).drop k ++ Spec.Ccm.zeros k).length := by
    rw [Proof.Cmac.length_le8, List.length_append, hl, Spec.Ccm.zeros, List.length_replicate]
    omega_arith
  apply List.ext_getElem hlen
  intro i h₁ h₂
  have hi : i < 8 := by rwa [Proof.Cmac.length_le8] at h₁
  by_cases h : i < 8 - k
  · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_drop]
    simp only [le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [show 8 * k + 8 * i = 8 * (k + i) by omega_arith]
  · rw [List.getElem_append_right (by rw [hl]; omega_arith)]
    simp only [Spec.Ccm.zeros, List.getElem_replicate, le8, List.getElem_map, List.getElem_range]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      ← Nat.pow_add]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega_arith)))]
    rfl

theorem le8_ffff : le8 (BitVec.ofNat 64 0xffff) = [0xff, 0xff] ++ Spec.Ccm.zeros 6 := by decide
theorem le8_feff : le8 (BitVec.ofNat 64 0xfeff) = [0xff, 0xfe] ++ Spec.Ccm.zeros 6 := by decide

/-! ## The encoding of the length of the associated data (A.2.2) -/

theorem encodeLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : Spec.Ccm.encodeLen a = Spec.Ccm.be 2 a := by
  simp [Spec.Ccm.encodeLen, h]

theorem encodeLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xfe] ++ Spec.Ccm.be 4 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem encodeLen_hi {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : ¬ a < 2 ^ 32) :
    Spec.Ccm.encodeLen a = [0xff, 0xff] ++ Spec.Ccm.be 8 a := by
  simp [Spec.Ccm.encodeLen, h₁, h₂]

theorem hdrLen_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) : hdrLen a = 2 := by simp [hdrLen, h]

theorem hdrLen_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) : hdrLen a = 6 := by
  simp [hdrLen, h₁, h₂]

theorem hdrLen_hi {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : ¬ a < 2 ^ 32) : hdrLen a = 10 := by
  simp [hdrLen, h₁, h₂]

/-- `[a]₁₆` written over zeros: the encoding of a short length. -/
theorem enc_lo {a : Nat} (h : a < 2 ^ 16 - 2 ^ 8) (z : List Byte) (hz : z = Spec.Ccm.zeros 8) :
    le8 (byteRev64 (BitVec.ofNat 64 a) >>> 48) ++ z = Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  subst hz
  rw [show (48 : Nat) = 8 * 6 from rfl, le8_ushiftRight _ (by decide), le8_byteRev64_ofNat (by omega_arith),
    be_split (q := 2) (by decide) (by omega_arith), encodeLen_lo h, hdrLen_lo h]
  simp [Spec.Ccm.zeros]

/-- `0xff ‖ 0xfe ‖ [a]₃₂` written over zeros. -/
theorem enc_mid {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : a < 2 ^ 32) (z : List Byte)
    (hz : z = Spec.Ccm.zeros 8) :
    le8 (byteRev64 (BitVec.ofNat 64 a) >>> 16 ||| BitVec.ofNat 64 0xfeff) ++ z =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  subst hz
  rw [le8_or, show byteRev64 (BitVec.ofNat 64 a) >>> 16 = byteRev64 (BitVec.ofNat 64 a) >>> (8 * 2) from rfl,
    le8_ushiftRight _ (by decide), le8_byteRev64_ofNat (by omega_arith), be_split (q := 4) (by decide) (by omega_arith),
    encodeLen_mid h₁ h₂, le8_feff, hdrLen_mid h₁ h₂]
  have hl4 := length_be 4 a
  rcases hb : Spec.Ccm.be 4 a with _ | ⟨b₀, _ | ⟨b₁, _ | ⟨b₂, _ | ⟨b₃, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    rw [hb] at hl4 <;> simp at hl4
  simp [Spec.Ccm.zeros, List.replicate]

/-- `0xff ‖ 0xff`, then `[a]₆₄` at offset 2, written over zeros. -/
theorem enc_hi {a : Nat} (h₁ : ¬ a < 2 ^ 16 - 2 ^ 8) (h₂ : ¬ a < 2 ^ 32) (ha : a < 2 ^ 64) :
    (le8 (BitVec.ofNat 64 0xffff) ++ Spec.Ccm.zeros 8).take 2 ++ le8 (byteRev64 (BitVec.ofNat 64 a)) ++
        (le8 (BitVec.ofNat 64 0xffff) ++ Spec.Ccm.zeros 8).drop (2 + 8) =
      Spec.Ccm.encodeLen a ++ Spec.Ccm.zeros (16 - hdrLen a) := by
  rw [le8_ffff, le8_byteRev64_ofNat ha, encodeLen_hi h₁ h₂, hdrLen_hi h₁ h₂]
  simp [Spec.Ccm.zeros, List.replicate]

/-! ## The flags of `B₀` (A.2.1) -/

theorem flags_val {tl nl al : Nat} (ht4 : 4 ≤ tl) (ht16 : tl ≤ 16) (hte : tl % 2 = 0) (h7 : 7 ≤ nl) (h13 : nl ≤ 13) :
    ((BitVec.ofNat 64 (4 * (tl - 2) + (14 - nl) + if al = 0 then 0 else 64)).setWidth 8 : Byte) =
      Spec.Ccm.flags tl (15 - nl) al := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Spec.Ccm.flags]
  by_cases h : al = 0
  · subst h; simp only [ite_true, Nat.add_zero, show ¬ (0 > 0) by omega_arith, ite_false, Nat.zero_add]; omega_arith
  · simp only [h, ite_false, show al > 0 by omega_arith, ite_true]; omega_arith

/-- The first byte of `Ctr₀`, `q − 1 = 14 − n`. -/
theorem sub_low_byte {nl : Nat} (h : nl ≤ 14) :
    ((BitVec.ofNat 64 14 - BitVec.ofNat 64 nl).setWidth 8 : Byte) = BitVec.ofNat 8 (15 - nl - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

end VG.Proof.AesCcm
