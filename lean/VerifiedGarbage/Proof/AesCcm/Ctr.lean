import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Gcm.Be64
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# AES-CCM: counter mode in pieces

Untrusted: everything here is checked by Lean. CCM's encryption (§6.1 steps
5–8) XORs byte `i` of the text with byte `i mod 16` of `CIPH_K(Ctrⱼ₊ᵢ/16)`
for `j = 1` (`crypt_eq`, `xorFrom`), so a text of whole blocks followed by
more is encrypted in two pieces, the second from the counter after the first
(`xorFrom_append`).

`vg_aes_ctr32` increments only the low 32 bits of its counter block
(`inc₃₂`). As a 128-bit big-endian integer, `Ctrᵢ` is `A · 2^(8q) + i` for
`i < 2^(8q)` (`beVal_ctrBlock`), and `inc₃₂` adds 1 to it unless the low 32
bits of `i + 1` are zero (`inc32_ctrBlock`; when `q < 4` they never are), so
`vg_aes_ctr32` from `Ctrⱼ` gives `Ctrⱼ, …, Ctrⱼ₊ₖ₋₁` as long as
`j mod 2³² + k ≤ 2³²` (`repeat_inc32_ctrBlock`), and its keystream is CCM's
(`xorKs_eq`).
-/

namespace VG.Proof.AesCcm

open VG.Spec

/-! ## Big-endian values -/

/-- The big-endian value of a byte string. -/
def beVal (bs : List Byte) : Nat := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

theorem beVal_foldl (bs : List Byte) (a : Nat) :
    bs.foldl (fun acc b => 256 * acc + b.toNat) a = a * 256 ^ bs.length + beVal bs := by
  induction bs generalizing a with
  | nil => simp [beVal]
  | cons b bs ih =>
    simp only [List.foldl_cons, beVal, List.length_cons] at ih ⊢
    rw [ih, ih (256 * 0 + b.toNat), Nat.pow_succ]
    simp only [Nat.mul_zero, Nat.zero_add]
    grind

theorem beVal_append (xs ys : List Byte) : beVal (xs ++ ys) = beVal xs * 256 ^ ys.length + beVal ys := by
  rw [beVal, List.foldl_append, beVal_foldl]; rfl

theorem beVal_cons (b : Byte) (bs : List Byte) : beVal (b :: bs) = b.toNat * 256 ^ bs.length + beVal bs := by
  rw [show b :: bs = [b] ++ bs from rfl, beVal_append]; simp [beVal]

theorem beVal_lt : ∀ bs : List Byte, beVal bs < 256 ^ bs.length
  | [] => by simp [beVal]
  | b :: bs => by
    rw [beVal_cons, List.length_cons, Nat.pow_succ]
    have := beVal_lt bs
    have := b.isLt
    have : b.toNat * 256 ^ bs.length + 256 ^ bs.length ≤ 256 ^ bs.length * 256 := by
      rw [← Nat.succ_mul, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    omega

theorem be_succ (k x : Nat) : Ccm.be (k + 1) x = BitVec.ofNat 8 (x / 256 ^ k) :: Ccm.be k x := by
  simp only [Ccm.be, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.sub_zero, Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro a ha
  simp only [Function.comp, List.mem_range] at ha ⊢
  rw [show k - (a + 1) = k - 1 - a by omega]

theorem beVal_be (k x : Nat) : beVal (Ccm.be k x) = x % 256 ^ k := by
  induction k with
  | zero => simp [Ccm.be, beVal, Nat.mod_one]
  | succ k ih =>
    rw [be_succ, beVal_cons, length_be, ih, BitVec.toNat_ofNat, Nat.mod_pow_succ (b := 256) (k := k)]
    show x / 256 ^ k % 256 * 256 ^ k + x % 256 ^ k = x % 256 ^ k + 256 ^ k * (x / 256 ^ k % 256)
    rw [Nat.add_comm, Nat.mul_comm]

theorem ofBytes_eq (bs : List Byte) : Gcm.ofBytes bs = BitVec.ofNat 128 (beVal bs) := rfl

/-! ## Counter blocks -/

theorem length_ctrBlock {nonce : List Byte} (hn : nonce.length ≤ 15) (i : Nat) :
    (Ccm.ctrBlock nonce i).length = 16 := by
  simp only [Ccm.ctrBlock, List.cons_append, List.length_cons, List.length_append, length_be]; omega

/-- `Ctrᵢ` as a big-endian integer. -/
theorem beVal_ctrBlock (nonce : List Byte) {i : Nat} (hi : i < 256 ^ (15 - nonce.length)) :
    beVal (Ccm.ctrBlock nonce i) =
      beVal (BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce) * 256 ^ (15 - nonce.length) + i := by
  simp only [Ccm.ctrBlock]
  rw [beVal_append, length_be, beVal_be, Nat.mod_eq_of_lt hi]

theorem toNat_ofBytes {bs : List Byte} (h : bs.length = 16) : (Gcm.ofBytes bs).toNat = beVal bs := by
  rw [ofBytes_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := beVal_lt bs; rw [h] at this; exact this

theorem toNat_inc32 (x : Gcm.Block) :
    (Gcm.inc32 x).toNat = x.toNat / 2 ^ 32 * 2 ^ 32 + (x.toNat % 2 ^ 32 + 1) % 2 ^ 32 := by
  simp only [Gcm.inc32, BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)), Nat.shiftLeft_eq, Nat.pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt (a := x.toNat / 2 ^ 32) (by omega)]
  rfl

/-- `inc₃₂` adds 1 to `Ctrᵢ` unless the low 32 bits of `i + 1` are zero. -/
theorem inc32_ctrBlock {nonce : List Byte} (hn₁ : 7 ≤ nonce.length) (hn₂ : nonce.length ≤ 13) {i : Nat}
    (hi : i + 1 < 256 ^ (15 - nonce.length)) (hw : (i + 1) % 2 ^ 32 ≠ 0) :
    Gcm.inc32 (Gcm.ofBytes (Ccm.ctrBlock nonce i)) = Gcm.ofBytes (Ccm.ctrBlock nonce (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_inc32, toNat_ofBytes (length_ctrBlock (by omega) _), toNat_ofBytes (length_ctrBlock (by omega) _),
    beVal_ctrBlock nonce (by omega), beVal_ctrBlock nonce hi]
  generalize beVal (BitVec.ofNat 8 (15 - nonce.length - 1) :: nonce) = A
  generalize hq : 15 - nonce.length = q at hi
  have : q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 ∨ q = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow] at hi ⊢ <;> omega

/-- `vg_aes_ctr32`'s counter blocks from `Ctrⱼ`, `k` of them, are
`Ctrⱼ, …, Ctrⱼ₊ₖ₋₁` if the low 32 bits do not wrap around. -/
theorem repeat_inc32_ctrBlock {nonce : List Byte} (hn₁ : 7 ≤ nonce.length) (hn₂ : nonce.length ≤ 13)
    {j k : Nat} (hk : j % 2 ^ 32 + k ≤ 2 ^ 32) (hj : j + k ≤ 256 ^ (15 - nonce.length)) :
    ∀ i < k, Nat.repeat Gcm.inc32 i (Gcm.ofBytes (Ccm.ctrBlock nonce j)) =
      Gcm.ofBytes (Ccm.ctrBlock nonce (j + i)) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Nat.repeat, ih (by omega), ← Nat.add_assoc]
    exact inc32_ctrBlock hn₁ hn₂ (by omega) (by omega)

/-! ## The keystream, byte by byte -/

/-- Byte `i` of CCM's keystream from `Ctrⱼ`: byte `i mod 16` of
`CIPH_K(Ctrⱼ₊ᵢ/16)`. -/
def ksb (ciph : Ccm.Cipher) (nonce : List Byte) (j i : Nat) : Byte :=
  (ciph (Ccm.ctrBlock nonce (j + i / 16))).getD (i % 16) 0

/-- `d` XORed with CCM's keystream from `Ctrⱼ`. -/
def xorFrom (ciph : Ccm.Cipher) (nonce : List Byte) (j : Nat) (d : List Byte) : List Byte :=
  (List.range d.length).map fun i => d.getD i 0 ^^^ ksb ciph nonce j i

theorem length_xorFrom (ciph : Ccm.Cipher) (nonce : List Byte) (j : Nat) (d : List Byte) :
    (xorFrom ciph nonce j d).length = d.length := by simp [xorFrom]

theorem getD_xorFrom (ciph : Ccm.Cipher) (nonce : List Byte) (j : Nat) (d : List Byte) {i : Nat}
    (hi : i < d.length) : (xorFrom ciph nonce j d).getD i 0 = d.getD i 0 ^^^ ksb ciph nonce j i := by
  simp [xorFrom, List.getD_eq_getElem?_getD, hi]

theorem xorFrom_nil (ciph : Ccm.Cipher) (nonce : List Byte) (j : Nat) : xorFrom ciph nonce j [] = [] := rfl

/-- A text of `a` whole blocks followed by more: the rest from `Ctrⱼ₊ₐ`. -/
theorem xorFrom_append (ciph : Ccm.Cipher) (nonce : List Byte) (j : Nat) {d e : List Byte} {a : Nat}
    (hd : d.length = 16 * a) :
    xorFrom ciph nonce j (d ++ e) = xorFrom ciph nonce j d ++ xorFrom ciph nonce (j + a) e := by
  simp only [xorFrom, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, List.getD_eq_getElem?_getD, ksb]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, hd,
      show (16 * a + i) / 16 = a + i / 16 by omega, show (16 * a + i) % 16 = i % 16 by omega, Nat.add_assoc]

/-- `CIPH_K` gives blocks. -/
def BlockCipher (ciph : Ccm.Cipher) : Prop := ∀ x, (ciph x).length = 16

theorem keystream_succ (ciph : Ccm.Cipher) (nonce : List Byte) (m : Nat) :
    Ccm.keystream ciph nonce (m + 1) = Ccm.keystream ciph nonce m ++ ciph (Ccm.ctrBlock nonce (m + 1)) := by
  simp [Ccm.keystream, List.range_succ, List.flatMap_append]

theorem length_keystream {ciph : Ccm.Cipher} (hc : BlockCipher ciph) (nonce : List Byte) (m : Nat) :
    (Ccm.keystream ciph nonce m).length = 16 * m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [keystream_succ, List.length_append, ih, hc]; omega

/-- §6.1 steps 5–8: CCM's encryption is the XOR with the keystream from
`Ctr₁`. -/
theorem crypt_eq {ciph : Ccm.Cipher} (hc : BlockCipher ciph) (nonce x : List Byte) :
    Ccm.crypt ciph nonce x = xorFrom ciph nonce 1 x := by
  have hl := length_keystream hc nonce ((x.length + 15) / 16)
  refine Gcm.list_ext (by simp [Ccm.crypt, Ccm.xor, length_xorFrom, hl]; omega) fun i hi => ?_
  simp only [Ccm.crypt, Ccm.xor, List.length_zipWith, hl] at hi
  have hix : i < x.length := by omega
  rw [getD_xorFrom _ _ _ _ hix, Ccm.crypt, Ccm.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hix, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some]
  congr 1
  · simp [List.getD_eq_getElem?_getD, hix]
  · -- Byte `i` of the keystream.
    have key : ∀ (m : Nat), ∀ i < 16 * m, (Ccm.keystream ciph nonce m).getD i 0 =
        (ciph (Ccm.ctrBlock nonce (i / 16 + 1))).getD (i % 16) 0 := by
      intro m
      induction m with
      | zero => intro i hi; simp at hi
      | succ m ih =>
        intro i hi
        have hlm := length_keystream hc nonce m
        rw [keystream_succ, List.getD_eq_getElem?_getD]
        by_cases h : i < 16 * m
        · rw [List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, ih i h]
        · rw [List.getElem?_append_right (by omega), hlm, ← List.getD_eq_getElem?_getD,
            show i / 16 = m by omega, show i - 16 * m = i % 16 by omega]
    have := key ((x.length + 15) / 16) i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [this, ksb, Nat.add_comm 1]

/-- What `vg_aes_ctr32` XORs in, from a counter block whose `k` blocks are
`Ctrⱼ, …, Ctrⱼ₊ₖ₋₁`, is CCM's keystream from `Ctrⱼ`. -/
theorem xorKs_eq {G : Gcm.Block → Gcm.Block} {ciph : Ccm.Cipher}
    (hG : ∀ c : List Byte, c.length = 16 → Gcm.toBytes (G (Gcm.ofBytes c)) = ciph c)
    {nonce : List Byte} (hn : nonce.length ≤ 15) {icb : Gcm.Block} {j k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i icb = Gcm.ofBytes (Ccm.ctrBlock nonce (j + i)))
    {d : List Byte} (hd : d.length ≤ 16 * k) :
    Gcm.xorKs G icb 0 d = xorFrom ciph nonce j d := by
  refine Gcm.list_ext (by simp [Gcm.length_xorKs, length_xorFrom]) fun i hi => ?_
  simp only [Gcm.length_xorKs] at hi
  rw [Gcm.getD_xorKs _ _ _ _ hi, getD_xorFrom _ _ _ _ hi, Nat.zero_add, Gcm.ksByte, ksb,
    hinc (i / 16) (by omega), hG _ (length_ctrBlock hn _)]

/-- The last bytes, XORed with the first bytes of `CIPH_K(Ctrⱼ)`. -/
theorem xorFrom_tail {ciph : Ccm.Cipher} (nonce : List Byte) (j : Nat) {d : List Byte} (hd : d.length ≤ 16) :
    List.zipWith (· ^^^ ·) d ((ciph (Ccm.ctrBlock nonce j)).take d.length) = xorFrom ciph nonce j d ∨
      (ciph (Ccm.ctrBlock nonce j)).length < d.length := by
  by_cases hl : d.length ≤ (ciph (Ccm.ctrBlock nonce j)).length
  · left
    refine Gcm.list_ext (by simp [length_xorFrom]; omega) fun i hi => ?_
    simp only [List.length_zipWith, List.length_take] at hi
    rw [getD_xorFrom _ _ _ _ (by omega), ksb, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < d.length by omega),
      List.getElem?_eq_getElem (show i < (ciph (Ccm.ctrBlock nonce j)).length by omega)]
  · exact .inr (by omega)

/-- The first `t` bytes of a block XORed with CCM's keystream from `Ctr₀`:
the first `t` bytes of the block encrypted as a MAC (§6.1 step 8). -/
theorem take_xorFrom_zero {ciph : Ccm.Cipher} (hc : BlockCipher ciph) (nonce : List Byte) {Y : List Byte}
    (hY : Y.length = 16) {t : Nat} (ht : t ≤ 16) :
    (xorFrom ciph nonce 0 Y).take t = Ccm.cryptTag ciph t nonce (Y.take t) := by
  have hl := hc (Ccm.ctrBlock nonce 0)
  refine Gcm.list_ext (by simp [length_xorFrom, Ccm.cryptTag, Ccm.xor, hY, hl]) fun i hi => ?_
  simp only [List.length_take, length_xorFrom, hY] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD,
    getD_xorFrom _ _ _ _ (by omega), ksb, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_zero]
  simp only [Ccm.cryptTag, Ccm.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_take_of_lt
    (show i < t by omega), List.getElem?_eq_getElem (show i < Y.length by omega),
    List.getElem?_eq_getElem (show i < (ciph (Ccm.ctrBlock nonce 0)).length by omega), Option.getD_some]

/-! ## `vg_aes_ctr32` on memory -/

/-- What `vg_aes_ctr32` writes over the `nb` blocks at `D`, as bytes: the
keystream from its counter block XORed in. -/
theorem ctr32_bytes {m m' : Mem} {C D : Addr} {G : Gcm.Block → Gcm.Block} {nb : Nat}
    (hd : Gcm.blocksAt m' D nb = Gcm.ctr32 G (Gcm.blockAt m C) (Gcm.blocksAt m D nb)) :
    Aes.bytesAt m' D (16 * nb) = Gcm.xorKs G (Gcm.blockAt m C) 0 (Aes.bytesAt m D (16 * nb)) := by
  refine Gcm.list_ext (by simp [Gcm.length_xorKs, Cmac.bytesAt_length]) fun k hk => ?_
  simp only [Cmac.bytesAt_length] at hk
  rw [Gcm.getD_xorKs _ _ _ _ (by rw [Cmac.bytesAt_length]; exact hk), Gcm.getD_bytesAt' _ _ hk,
    Gcm.getD_bytesAt' _ _ hk]
  have hq : k / 16 < nb := by omega
  have e₁ := congrArg (fun L => L.getD (k / 16) 0) hd
  rw [Gcm.ctr32_getD _ _ _ (by rw [Gcm.length_blocksAt]; exact hq), Gcm.blocksAt_getD _ _ _ hq,
    Gcm.blocksAt_getD _ _ _ hq] at e₁
  have ea : D + BitVec.ofNat 64 k = D + BitVec.ofNat 64 (16 * (k / 16)) + BitVec.ofNat 64 (k % 16) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [ea, Gcm.bytes_toBytes_blockAt m' _ (by omega), Gcm.bytes_toBytes_blockAt m _ (by omega), e₁,
    Proof.Aes.toBytes_xor _ _ (by omega), Gcm.ksByte, Nat.zero_add]

/-- `vg_aes_ctr32` from `Ctrⱼ` over `k` blocks whose counters do not wrap
around: CCM's keystream from `Ctrⱼ`. -/
theorem ctr32_ccm {m m' : Mem} {K C D : Addr} {R : Nat} {nonce : List Byte} (hn : nonce.length ≤ 15) {j k : Nat}
    (hinc : ∀ i < k, Nat.repeat Gcm.inc32 i (Gcm.blockAt m C) = Gcm.ofBytes (Ccm.ctrBlock nonce (j + i)))
    (hd : Gcm.blocksAt m' D k =
      Gcm.ctr32 (Gcm.aesWith R (Aes.bytesAt m K (16 * (R + 1)))) (Gcm.blockAt m C) (Gcm.blocksAt m D k)) :
    Aes.bytesAt m' D (16 * k) = xorFrom (Ccm.ctxCiph m K R) nonce j (Aes.bytesAt m D (16 * k)) := by
  rw [ctr32_bytes hd]
  exact xorKs_eq (fun c hc => Cmac.aesWith_bytes _ _ hc) hn hinc (by rw [Cmac.bytesAt_length])

/-- A zero block XORed with CCM's keystream from `Ctrⱼ`: `CIPH_K(Ctrⱼ)`. -/
theorem xorFrom_zeros {ciph : Ccm.Cipher} (hc : BlockCipher ciph) (nonce : List Byte) (j : Nat) :
    xorFrom ciph nonce j (Ccm.zeros 16) = ciph (Ccm.ctrBlock nonce j) := by
  refine Gcm.list_ext (by rw [length_xorFrom, hc]; rfl) fun i hi => ?_
  simp only [length_xorFrom, Ccm.zeros, List.length_replicate] at hi
  rw [getD_xorFrom _ _ _ _ (by simp [Ccm.zeros, hi]), ksb, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi, Nat.add_zero,
    show (Ccm.zeros 16).getD i 0 = 0 by
      simp only [Ccm.zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, hi, ↓reduceIte, Option.getD_some]]
  exact BitVec.zero_xor

/-- Encrypting a MAC twice gives it back. -/
theorem cryptTag_cryptTag {ciph : Ccm.Cipher} (hc : BlockCipher ciph) {t : Nat} (ht : t ≤ 16) (nonce : List Byte)
    {x : List Byte} (hx : x.length = t) : Ccm.cryptTag ciph t nonce (Ccm.cryptTag ciph t nonce x) = x := by
  have hl := hc (Ccm.ctrBlock nonce 0)
  apply List.ext_getElem (by simp [Ccm.cryptTag, Ccm.xor, hx, hl]; omega)
  intro i h₁ h₂
  simp only [Ccm.cryptTag, Ccm.xor, List.getElem_zipWith, List.getElem_take]
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem cryptTag_eq_iff {ciph : Ccm.Cipher} (hc : BlockCipher ciph) {t : Nat} (ht : t ≤ 16) (nonce : List Byte)
    {x y : List Byte} (hx : x.length = t) (hy : y.length = t) :
    Ccm.cryptTag ciph t nonce x = y ↔ x = Ccm.cryptTag ciph t nonce y :=
  ⟨fun h => by rw [← h, cryptTag_cryptTag hc ht nonce hx], fun h => by rw [h, cryptTag_cryptTag hc ht nonce hy]⟩

end VG.Proof.AesCcm
